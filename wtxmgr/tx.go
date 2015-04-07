/*
 * Copyright (c) 2013-2015 Conformal Systems LLC <info@conformal.com>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */

package wtxmgr

import (
	"bytes"
	"fmt"
	"sort"
	"time"

	"github.com/btcsuite/btcd/blockchain"
	"github.com/btcsuite/btcd/chaincfg"
	"github.com/btcsuite/btcd/wire"
	"github.com/btcsuite/btcutil"
	"github.com/btcsuite/btcwallet/walletdb"
)

// Block contains the minimum amount of data to uniquely identify any block on
// either the best or side chain.
type Block struct {
	Hash   wire.ShaHash
	Height int32
}

// BlockMeta contains the unique identification for a block and any metadata
// pertaining to the block.  At the moment, this additional metadata only
// includes the block time from the block header.
type BlockMeta struct {
	Block
	Time time.Time
}

// blockRecord is an in-memory representation of the block record saved in the
// database.
type blockRecord struct {
	Block
	Time         time.Time
	transactions []wire.ShaHash
}

// Incidence records the block hash and blockchain height of a mined transaction.
// Since a transaction hash alone is not enough to uniquely identify a mined
// transaction (duplicate transaction hashes are allowed), the incidence is used
// instead.
type Incidence struct {
	TxHash wire.ShaHash
	Block
}

// IndexedIncidence records the transaction incidence and an input or output
// index.
type IndexedIncidence struct {
	Incidence
	Index uint32
}

// debit records the debits a transaction record makes from previous wallet
// transaction credits.
type debit struct {
	txHash wire.ShaHash
	index  uint32
	amount btcutil.Amount
	spends IndexedIncidence
}

// credit describes a transaction output which was or is spendable by wallet.
type credit struct {
	outPoint wire.OutPoint
	block    Block
	amount   btcutil.Amount
	change   bool
	spentBy  IndexedIncidence // Index == ^uint32(0) if unspent
}

// TxRecord represents a transaction managed by the Store.
type TxRecord struct {
	MsgTx        wire.MsgTx
	Hash         wire.ShaHash
	Received     time.Time
	SerializedTx []byte // Optional: may be nil
}

// NewTxRecord creates a new transaction record that may be inserted into the
// store.  It uses memoization to save the transaction hash and the serialized
// transaction.
func NewTxRecord(serializedTx []byte, received time.Time) (*TxRecord, error) {
	rec := &TxRecord{
		Received:     received,
		SerializedTx: serializedTx,
	}
	err := rec.MsgTx.Deserialize(bytes.NewReader(serializedTx))
	if err != nil {
		str := "failed to deserialize transaction"
		return nil, storeError(ErrInput, str, err)
	}
	copy(rec.Hash[:], wire.DoubleSha256(serializedTx))
	return rec, nil
}

// NewTxRecordFromMsgTx creates a new transaction record that may be inserted
// into the store.
func NewTxRecordFromMsgTx(msgTx *wire.MsgTx, received time.Time) (*TxRecord, error) {
	buf := bytes.NewBuffer(make([]byte, 0, msgTx.SerializeSize()))
	err := msgTx.Serialize(buf)
	if err != nil {
		str := "failed to serialize transaction"
		return nil, storeError(ErrInput, str, err)
	}
	rec := &TxRecord{
		MsgTx:        *msgTx,
		Received:     received,
		SerializedTx: buf.Bytes(),
	}
	copy(rec.Hash[:], wire.DoubleSha256(rec.SerializedTx))
	return rec, nil
}

// Credit is the type representing a transaction output which was spent or
// is still spendable by wallet.  A UTXO is an unspent Credit, but not all
// Credits are UTXOs.
type Credit struct {
	wire.OutPoint
	BlockMeta
	Amount       btcutil.Amount
	PkScript     []byte
	Received     time.Time
	FromCoinBase bool
}

// Store implements a transaction store for storing and managing wallet
// transactions.
type Store struct {
	namespace walletdb.Namespace
}

// Open opens a persistent transaction store from the walletdb namespace, or
// creates a new store in the namespace if one does not already exist.
func Open(namespace walletdb.Namespace, net *chaincfg.Params) (*Store, error) {
	// Upgrade the manager to the latest version as needed.  This includes
	// the initial creation.
	if err := upgradeStore(namespace); err != nil {
		return nil, err
	}

	return &Store{
		namespace: namespace,
	}, nil
}

// moveMinedTx moves a transaction record from the unmined buckets to block
// buckets.
func (s *Store) moveMinedTx(ns walletdb.Bucket, rec *TxRecord, recKey, recVal []byte, block *BlockMeta) error {
	log.Infof("Marking unconfirmed transaction %v mined in block %d",
		&rec.Hash, block.Height)

	// Insert block record as needed.
	blockKey, blockVal := existsBlockRecord(ns, block.Height)
	var err error
	if blockVal == nil {
		blockVal = valueBlockRecord(block, &rec.Hash)
	} else {
		blockVal, err = appendRawBlockRecord(blockVal, &rec.Hash)
		if err != nil {
			return err
		}
	}
	err = putRawBlockRecord(ns, blockKey, blockVal)
	if err != nil {
		return err
	}

	err = putRawTxRecord(ns, recKey, recVal)
	if err != nil {
		return err
	}
	minedBalance, err := fetchMinedBalance(ns)
	if err != nil {
		return err
	}

	// For all mined transactions with unspent credits spent by this
	// transaction, mark each spent, remove from the unspents map, and
	// insert a debit record for the spent credit.
	debitIncidence := IndexedIncidence{
		Incidence: Incidence{TxHash: rec.Hash, Block: block.Block},
		// Index set for each rec input below.
	}
	for i, input := range rec.MsgTx.TxIn {
		unspentKey, credKey := existsUnspent(ns, &input.PreviousOutPoint)
		if credKey == nil {
			continue
		}
		debitIncidence.Index = uint32(i)
		amt, err := spendCredit(ns, credKey, &debitIncidence)
		if err != nil {
			return err
		}
		minedBalance -= amt
		err = deleteRawUnspent(ns, unspentKey)
		if err != nil {
			return err
		}

		err = putDebit(ns, &rec.Hash, uint32(i), amt, &block.Block, credKey)
		if err != nil {
			return err
		}

		err = deleteRawUnminedInput(ns, unspentKey)
		if err != nil {
			return err
		}
	}

	// For each output of the record that is marked as a credit, if the
	// output is marked as a credit by the unconfirmed store, remove the
	// marker and mark the output as a credit in the db.
	//
	// Moved credits are added as unspents, even if there is another
	// unconfirmed transaction which spends them.
	cred := credit{
		outPoint: wire.OutPoint{Hash: rec.Hash},
		block:    block.Block,
		spentBy:  IndexedIncidence{Index: ^uint32(0)},
	}
	it := makeUnminedCreditIterator(ns, &rec.Hash)
	for it.next() {
		// TODO: This should use the raw apis.  The credit value (it.cv)
		// can be moved from unmined directly to the credits bucket.
		// The key needs a modification to include the block
		// height/hash.
		index, err := fetchRawUnminedCreditIndex(it.ck)
		if err != nil {
			return err
		}
		amount, change, err := fetchRawUnminedCreditAmountChange(it.cv)
		if err != nil {
			return err
		}
		cred.outPoint.Index = index
		cred.amount = amount
		cred.change = change

		err = it.delete()
		if err != nil {
			return err
		}
		err = putCredit(ns, &cred)
		if err != nil {
			return err
		}
		err = putUnspent(ns, &cred.outPoint, &block.Block)
		if err != nil {
			return err
		}
		minedBalance += amount
	}
	if it.err != nil {
		return it.err
	}

	err = putMinedBalance(ns, minedBalance)
	if err != nil {
		return err
	}

	return deleteRawUnmined(ns, rec.Hash[:])
}

// InsertTx records a transaction as belonging to a wallet's transaction
// history.  If block is nil, the transaction is considered unspent, and the
// transaction's index must be unset.
func (s *Store) InsertTx(rec *TxRecord, block *BlockMeta) error {
	return scopedUpdate(s.namespace, func(ns walletdb.Bucket) error {
		if block == nil {
			return s.insertMemPoolTx(ns, rec)
		}
		return s.insertMinedTx(ns, rec, block)
	})
}

// insertMinedTx inserts a new transaction record for a mined transaction into
// the database.  It is expected that the exact transation does not already
// exist in the unmined buckets, but unmined double spends (including mutations)
// are removed.
func (s *Store) insertMinedTx(ns walletdb.Bucket, rec *TxRecord, block *BlockMeta) error {
	// If a transaction record for this tx hash and block already exist,
	// there is nothing left to do.
	k, v := existsTxRecord(ns, &rec.Hash, &block.Block)
	if v != nil {
		return nil
	}

	// If the exact tx (not a double spend) is already included but
	// unconfirmed, move it to a block.
	v = existsRawUnmined(ns, rec.Hash[:])
	if v != nil {
		return s.moveMinedTx(ns, rec, k, v, block)
	}

	// As there may be unconfirmed transactions that are invalidated by this
	// transaction (either being duplicates, or double spends), remove them
	// from the unconfirmed set.  This also handles removing unconfirmed
	// transaction spend chains if any other unconfirmed transactions spend
	// outputs of the removed double spend.
	err := s.removeDoubleSpends(ns, rec)
	if err != nil {
		return err
	}

	// If a block record does not yet exist for any transactions from this
	// block, insert the record.  Otherwise, update it by adding the
	// transaction hash to the set of transactions from this block.
	blockKey, blockValue := existsBlockRecord(ns, block.Height)
	if blockValue == nil {
		err = putBlockRecord(ns, block, &rec.Hash)
	} else {
		blockValue, err = appendRawBlockRecord(blockValue, &rec.Hash)
		if err == nil {
			return err
		}
		err = putRawBlockRecord(ns, blockKey, blockValue)
	}
	if err != nil {
		return err
	}

	err = putTxRecord(ns, rec, &block.Block)
	if err != nil {
		return err
	}

	minedBalance, err := fetchMinedBalance(ns)
	if err != nil {
		return err
	}

	// Add a debit record for each unspent credit spent by this tx.
	spender := IndexedIncidence{
		Incidence: Incidence{
			TxHash: rec.Hash,
			Block:  block.Block,
		},
		// Index set for each iteration below
	}
	for i, input := range rec.MsgTx.TxIn {
		unspentKey, credKey := existsUnspent(ns, &input.PreviousOutPoint)
		if credKey == nil {
			// Debits for unmined transactions are not explicitly
			// tracked.  Instead, all previous outputs spent by any
			// unmined transaction are added to a map for quick
			// lookups when it must be checked whether a mined
			// output is unspent or not.
			//
			// Tracking individual debits for unmined transactions
			// could be added later to simplify (and increase
			// performance of) determining some details that need
			// the previous outputs (e.g. determining a fee), but at
			// the moment that is not done (and a db lookup is used
			// for those cases instead).  There is also a good
			// chance that all unmined transaction handling will
			// move entirely to the db rather than being handled in
			// memory for atomicity reasons, so the simplist
			// implementation is currently used.
			continue
		}
		spender.Index = uint32(i)
		amt, err := spendCredit(ns, credKey, &spender)
		if err != nil {
			return err
		}
		err = putDebit(ns, &rec.Hash, uint32(i), amt, &block.Block,
			credKey)
		if err != nil {
			return err
		}

		minedBalance -= amt

		err = deleteRawUnspent(ns, unspentKey)
		if err != nil {
			return err
		}
	}

	return putMinedBalance(ns, minedBalance)
}

// AddCredit marks a transaction record as containing a transaction output
// spendable by wallet.  The output is added unspent, and is marked spent
// when a new transaction spending the output is inserted into the store.
//
// TODO(jrick): This should not be necessary.  Instead, pass the indexes
// that are known to contain credits when a transaction or merkleblock is
// inserted into the store.
func (s *Store) AddCredit(rec *TxRecord, block *BlockMeta, index uint32, change bool) error {
	if len(rec.MsgTx.TxOut) <= int(index) {
		str := "transaction output does not exist"
		return storeError(ErrInput, str, nil)
	}

	return scopedUpdate(s.namespace, func(ns walletdb.Bucket) error {
		return s.addCredit(ns, rec, block, index, change)
	})
}

func (s *Store) addCredit(ns walletdb.Bucket, rec *TxRecord, block *BlockMeta, index uint32, change bool) error {
	if block == nil {
		k := canonicalOutPoint(&rec.Hash, index)
		v := valueUnminedCredit(btcutil.Amount(rec.MsgTx.TxOut[index].Value), change)
		return putRawUnminedCredit(ns, k, v)
	}

	k, v := existsCredit(ns, &rec.Hash, index, &block.Block)
	if v != nil {
		return nil
	}

	txOutAmt := btcutil.Amount(rec.MsgTx.TxOut[index].Value)
	log.Debugf("Marking transaction %v output %d (%v) spendable",
		rec.Hash, index, txOutAmt)

	cred := credit{
		outPoint: wire.OutPoint{
			Hash:  rec.Hash,
			Index: index,
		},
		block:   block.Block,
		amount:  txOutAmt,
		change:  change,
		spentBy: IndexedIncidence{Index: ^uint32(0)},
	}
	v = valueCredit(&cred)
	err := putRawCredit(ns, k, v)
	if err != nil {
		return err
	}

	minedBalance, err := fetchMinedBalance(ns)
	if err != nil {
		return err
	}
	err = putMinedBalance(ns, minedBalance+txOutAmt)
	if err != nil {
		return err
	}

	return putUnspent(ns, &cred.outPoint, &block.Block)
}

// Rollback removes all blocks at height onwards, moving any transactions within
// each block to the unconfirmed pool.
func (s *Store) Rollback(height int32) error {
	return scopedUpdate(s.namespace, func(ns walletdb.Bucket) error {
		return s.rollback(ns, height)
	})
}

func (s *Store) rollback(ns walletdb.Bucket, height int32) error {
	minedBalance, err := fetchMinedBalance(ns)
	if err != nil {
		return err
	}

	it := makeBlockIterator(ns, height)
	for it.next() {
		b := &it.elem

		log.Infof("Rolling back %d transactions from block %v height %d",
			len(b.transactions), b.Hash, b.Height)

		for i := range b.transactions {
			txHash := &b.transactions[i]

			recKey := keyTxRecord(txHash, &b.Block)
			recVal := existsRawTxRecord(ns, recKey)
			if recVal == nil {
				str := fmt.Sprintf("missing transaction %v for "+
					"block %v", txHash, b.Height)
				return storeError(ErrData, str, nil)
			}
			var rec TxRecord
			err = readRawTxRecord(txHash, recVal, &rec)
			if err != nil {
				return err
			}

			err = deleteTxRecord(ns, txHash, &b.Block)
			if err != nil {
				return err
			}
			err = putRawUnmined(ns, txHash[:], recVal)
			if err != nil {
				return err
			}

			// Handle coinbase transactions specially since they are
			// not moved to the unconfirmed store.  A coinbase cannot
			// contain any debits, but all credits should be removed
			// and the mined balance decremented.
			if blockchain.IsCoinBaseTx(&rec.MsgTx) {
				op := wire.OutPoint{Hash: rec.Hash}
				for i, output := range rec.MsgTx.TxOut {
					k, v := existsCredit(ns, &rec.Hash,
						uint32(i), &b.Block)
					if v == nil {
						continue
					}
					op.Index = uint32(i)
					unspentKey, credKey := existsUnspent(ns, &op)
					if credKey != nil {
						minedBalance -= btcutil.Amount(output.Value)
						err = deleteRawUnspent(ns, unspentKey)
						if err != nil {
							return err
						}
					}
					err = deleteRawCredit(ns, k)
					if err != nil {
						return err
					}
				}

				continue
			}

			// For each debit recorded for this transaction, mark
			// the credit it spends as unspent (as long as it still
			// exists) and delete the debit.  The previous output is
			// recorded in the unconfirmed store for every previous
			// output, not just debits.
			for i, input := range rec.MsgTx.TxIn {
				prevOut := &input.PreviousOutPoint
				prevOutKey := canonicalOutPoint(&prevOut.Hash,
					prevOut.Index)
				err = putRawUnminedInput(ns, prevOutKey, rec.Hash[:])
				if err != nil {
					return err
				}

				// If this input is a debit, remove the debit
				// record and mark the credit that it spent as
				// unspent, incrementing the mined balance.
				debKey, credKey, err := existsDebit(ns,
					&rec.Hash, uint32(i), &b.Block)
				if err != nil {
					return err
				}
				if debKey == nil {
					continue
				}

				// unspendRawCredit does not error in case the
				// no credit exists for this key, but this
				// behavior is correct.  Since blocks are
				// removed in increasing order, this credit
				// may have already been removed from a
				// previously removed transaction record in
				// this rollback.
				var amt btcutil.Amount
				amt, err = unspendRawCredit(ns, credKey)
				if err != nil {
					return err
				}
				err = deleteRawDebit(ns, debKey)
				if err != nil {
					return err
				}

				// If the credit was previously removed in the
				// rollback, the credit amount is zero.  Only
				// mark the previously spent credit as unspent
				// if it still exists.
				if amt == 0 {
					continue
				}
				unspentVal, err := fetchRawCreditUnspentValue(credKey)
				if err != nil {
					return err
				}
				minedBalance += amt
				err = putRawUnspent(ns, prevOutKey, unspentVal)
				if err != nil {
					return err
				}
			}

			// For each detached non-coinbase credit, move the
			// credit output to unmined.  If the credit is marked
			// unspent, it is removed from the utxo set and the
			// mined balance is decremented.
			//
			// TODO: use a credit iterator
			for i, output := range rec.MsgTx.TxOut {
				k, v := existsCredit(ns, &rec.Hash, uint32(i),
					&b.Block)
				if v == nil {
					continue
				}

				amt, change, err := fetchRawCreditAmountChange(v)
				if err != nil {
					return err
				}
				outPointKey := canonicalOutPoint(&rec.Hash, uint32(i))
				unminedCredVal := valueUnminedCredit(amt, change)
				err = putRawUnminedCredit(ns, outPointKey, unminedCredVal)
				if err != nil {
					return err
				}

				err = deleteRawCredit(ns, k)
				if err != nil {
					return err
				}

				credKey := existsRawUnspent(ns, outPointKey)
				if credKey != nil {
					minedBalance -= btcutil.Amount(output.Value)
					err = deleteRawUnspent(ns, outPointKey)
					if err != nil {
						return err
					}
				}
			}
		}

		err = it.delete()
		if err != nil {
			return err
		}
	}
	if it.err != nil {
		return it.err
	}

	return putMinedBalance(ns, minedBalance)
}

// UnspentOutputs returns all unspent received transaction outputs.
// The order is undefined.
func (s *Store) UnspentOutputs() ([]Credit, error) {
	var credits []Credit
	err := scopedView(s.namespace, func(ns walletdb.Bucket) error {
		var err error
		credits, err = s.unspentOutputs(ns)
		return err
	})
	return credits, err
}

func (s *Store) unspentOutputs(ns walletdb.Bucket) ([]Credit, error) {
	var unspent []Credit

	var op wire.OutPoint
	var block Block
	err := ns.Bucket(bucketUnspent).ForEach(func(k, v []byte) error {
		err := readCanonicalOutPoint(k, &op)
		if err != nil {
			return err
		}
		if existsRawUnminedInput(ns, k) != nil {
			// Output is spent by an unmined transaction.
			// Skip this k/v pair.
			return nil
		}
		err = readUnspentBlock(v, &block)
		if err != nil {
			return err
		}

		blockTime, err := fetchBlockTime(ns, block.Height)
		if err != nil {
			return err
		}
		// TODO(jrick): reading the entire transaction should
		// be avoidable.  Creating the credit only requires the
		// output amount and pkScript.
		rec, err := fetchTxRecord(ns, &op.Hash, &block)
		if err != nil {
			return err
		}
		txOut := rec.MsgTx.TxOut[op.Index]
		cred := Credit{
			OutPoint: op,
			BlockMeta: BlockMeta{
				Block: block,
				Time:  blockTime,
			},
			Amount:       btcutil.Amount(txOut.Value),
			PkScript:     txOut.PkScript,
			Received:     rec.Received,
			FromCoinBase: blockchain.IsCoinBaseTx(&rec.MsgTx),
		}
		unspent = append(unspent, cred)
		return nil
	})
	if err != nil {
		if _, ok := err.(StoreError); ok {
			return nil, err
		}
		str := "failed iterating unspent bucket"
		return nil, storeError(ErrDatabase, str, err)
	}

	err = ns.Bucket(bucketUnminedCredits).ForEach(func(k, v []byte) error {
		if existsRawUnminedInput(ns, k) != nil {
			// Output is spent by an unmined transaction.
			// Skip to next unmined credit.
			return nil
		}

		err := readCanonicalOutPoint(k, &op)
		if err != nil {
			return err
		}

		// TODO(jrick): Reading/parsing the entire transaction record
		// just for the output amount and script can be avoided.
		recVal := existsRawUnmined(ns, op.Hash[:])
		if recVal == nil {
			str := "missing unmined transaction record"
			return storeError(ErrData, str, nil)
		}
		var rec TxRecord
		err = readRawTxRecord(&op.Hash, recVal, &rec)
		if err != nil {
			return err
		}

		txOut := rec.MsgTx.TxOut[op.Index]
		cred := Credit{
			OutPoint: op,
			BlockMeta: BlockMeta{
				Block: Block{Height: -1},
			},
			Amount:       btcutil.Amount(txOut.Value),
			PkScript:     txOut.PkScript,
			Received:     rec.Received,
			FromCoinBase: blockchain.IsCoinBaseTx(&rec.MsgTx),
		}
		unspent = append(unspent, cred)
		return nil
	})
	if err != nil {
		if _, ok := err.(StoreError); ok {
			return nil, err
		}
		str := "failed iterating unmined credits bucket"
		return nil, storeError(ErrDatabase, str, err)
	}

	return unspent, nil
}

type creditSlice []Credit

func (s creditSlice) Len() int {
	return len(s)
}

func (s creditSlice) Less(i, j int) bool {
	switch {
	// If both credits are from the same tx, sort by output index.
	case s[i].OutPoint.Hash == s[j].OutPoint.Hash:
		return s[i].OutPoint.Index < s[j].OutPoint.Index

	// If both transactions are unmined, sort by their received date.
	case s[i].Height == -1 && s[j].Height == -1:
		return s[i].Received.Before(s[j].Received)

	// Unmined (newer) txs always come last.
	case s[i].Height == -1:
		return false
	case s[j].Height == -1:
		return true

	// If both txs are mined in different blocks, sort by block height.
	default:
		return s[i].Height < s[j].Height
	}
}

func (s creditSlice) Swap(i, j int) {
	s[i], s[j] = s[j], s[i]
}

// SortedUnspentOutputs returns all unspent recevied transaction outputs.
// The order is first unmined transactions (sorted by receive date), then
// mined transactions in increasing number of confirmations.  Transactions
// in the same block (same number of confirmations) are sorted by block
// index in increasing order.  Credits (outputs) from the same transaction
// are sorted by output index in increasing order.
func (s *Store) SortedUnspentOutputs() ([]Credit, error) {
	unspent, err := s.UnspentOutputs()
	if err != nil {
		return nil, err
	}
	sort.Sort(sort.Reverse(creditSlice(unspent)))
	return unspent, nil
}

// confirmed checks whether a transaction at height txHeight has met
// minconf confirmations for a blockchain at height curHeight.
func confirmed(minconf, txHeight, curHeight int32) bool {
	return confirms(txHeight, curHeight) >= minconf
}

// confirms returns the number of confirmations for a transaction in a
// block at height txHeight (or -1 for an unconfirmed tx) given the chain
// height curHeight.
func confirms(txHeight, curHeight int32) int32 {
	switch {
	case txHeight == -1, txHeight > curHeight:
		return 0
	default:
		return curHeight - txHeight + 1
	}
}

// Balance returns the spendable wallet balance (total value of all unspent
// transaction outputs) given a minimum of minConf confirmations, calculated
// at a current chain height of curHeight.  Coinbase outputs are only included
// in the balance if maturity has been reached.
func (s *Store) Balance(minConf, chainHeight int32) (btcutil.Amount, error) {
	var amt btcutil.Amount
	err := scopedView(s.namespace, func(ns walletdb.Bucket) error {
		var err error
		amt, err = s.balance(ns, minConf, chainHeight)
		return err
	})
	return amt, err
}

func (s *Store) balance(ns walletdb.Bucket, minConf int32, chainHeight int32) (btcutil.Amount, error) {
	bal, err := fetchMinedBalance(ns)
	if err != nil {
		return 0, err
	}

	// Shadow this to avoid repeating arguments unnecesarily.
	confirms := func(height int32) int32 {
		return confirms(height, chainHeight)
	}

	// Subtract the balance for each credit that is spent by an unmined
	// transaction.
	var op wire.OutPoint
	var block Block
	err = ns.Bucket(bucketUnspent).ForEach(func(k, v []byte) error {
		err := readCanonicalOutPoint(k, &op)
		if err != nil {
			return err
		}
		err = readUnspentBlock(v, &block)
		if err != nil {
			return err
		}
		if existsRawUnminedInput(ns, k) != nil {
			_, v := existsCredit(ns, &op.Hash, op.Index, &block)
			amt, err := fetchRawCreditAmount(v)
			if err != nil {
				return err
			}
			bal -= amt
		}
		return nil
	})
	if err != nil {
		if _, ok := err.(StoreError); ok {
			return 0, err
		}
		str := "failed iterating unspent outputs"
		return 0, storeError(ErrDatabase, str, err)
	}

	// Decrement the balance for any unspent credit with less than
	// minConf confirmations and any (unspent) immature coinbase credit.
	stopConf := minConf
	if blockchain.CoinbaseMaturity > stopConf {
		stopConf = blockchain.CoinbaseMaturity
	}
	lastHeight := chainHeight - stopConf
	blockIt := makeReverseBlockIterator(ns)
	for blockIt.prev() {
		block := &blockIt.elem

		if block.Height < lastHeight {
			break
		}

		for i := range block.transactions {
			txHash := &block.transactions[i]
			rec, err := fetchTxRecord(ns, txHash, &block.Block)
			if err != nil {
				return 0, err
			}
			numOuts := uint32(len(rec.MsgTx.TxOut))
			for i := uint32(0); i < numOuts; i++ {
				// Avoid double decrementing the credit amount
				// if it was already removed for being spent by
				// an unmined tx.
				opKey := canonicalOutPoint(txHash, i)
				if existsRawUnminedInput(ns, opKey) != nil {
					continue
				}

				_, v := existsCredit(ns, txHash, i, &block.Block)
				if v == nil {
					continue
				}
				amt, spent, err := fetchRawCreditAmountSpent(v)
				if err != nil {
					return 0, err
				}
				if spent {
					continue
				}
				if confirms(block.Height) < minConf || blockchain.IsCoinBaseTx(&rec.MsgTx) {
					bal -= amt
				}
			}
		}
	}
	if blockIt.err != nil {
		return 0, blockIt.err
	}

	// If unmined outputs are included, increment the balance for each
	// output that is unspent.
	if minConf == 0 {
		err = ns.Bucket(bucketUnminedCredits).ForEach(func(k, v []byte) error {
			if existsRawUnminedInput(ns, k) != nil {
				// Output is spent by an unmined transaction.
				// Skip to next unmined credit.
				return nil
			}

			amount, err := fetchRawUnminedCreditAmount(v)
			if err != nil {
				return err
			}
			bal += amount
			return nil
		})
		if err != nil {
			if _, ok := err.(StoreError); ok {
				return 0, err
			}
			str := "failed to iterate over unmined credits bucket"
			return 0, storeError(ErrDatabase, str, err)
		}
	}

	return bal, nil
}

// CreditRecord contains metadata regarding a transaction credit for a known
// transaction.  Further details may be looked up by indexing a wire.MsgTx.TxOut
// with the Index field.
type CreditRecord struct {
	Index  uint32
	Amount btcutil.Amount
	Spent  bool
	Change bool
}

// DebitRecord contains metadata regarding a transaction debit for a known
// transaction.  Further details may be looked up by indexing a wire.MsgTx.TxIn
// with the Index field.
type DebitRecord struct {
	Amount btcutil.Amount
	Index  uint32
}

// TxDetails is intended to provide callers with access to rich details
// regarding a relevant transaction and which inputs and outputs are credit or
// debits.
type TxDetails struct {
	TxRecord
	Block   BlockMeta
	Credits []CreditRecord
	Debits  []DebitRecord
}

// TxDetails looks up all recorded details regarding a transaction with some
// hash.  In case of a hash collision, the most recent transaction with a
// matching hash is returned.
//
// Not finding a transaction with this hash is not an error.  In this case,
// a nil TxDetails is returned.
func (s *Store) TxDetails(txHash *wire.ShaHash) (*TxDetails, error) {
	var details *TxDetails
	err := scopedView(s.namespace, func(ns walletdb.Bucket) error {
		var err error

		// First, check whether there exists an unmined transaction with this
		// hash.  Use it if found.
		v := existsRawUnmined(ns, txHash[:])
		if v != nil {
			details, err = s.unminedTxDetails(ns, txHash, v)
			return err
		}

		// Otherwise, if there exists a mined transaction with this matching
		// hash, skip over to the newest and begin fetching all details.
		k, v := latestTxRecord(ns, txHash)
		if v == nil {
			// not found
			return nil
		}

		details, err = s.txDetails(ns, txHash, k, v)
		return err
	})
	return details, err
}

// UniqueTxDetails looks up all recorded details for a transaction recorded
// mined in some particular block, or an unmined transaction if block is nil.
//
// Not finding a transaction with this hash from this block is not an error.  In
// this case, a nil TxDetails is returned.
func (s *Store) UniqueTxDetails(txHash *wire.ShaHash, block *Block) (*TxDetails, error) {
	var details *TxDetails
	err := scopedView(s.namespace, func(ns walletdb.Bucket) error {
		var err error
		if block == nil {
			v := existsRawUnmined(ns, txHash[:])
			if v == nil {
				return nil
			}
			details, err = s.unminedTxDetails(ns, txHash, v)
			return err
		}

		k, v := existsTxRecord(ns, txHash, block)
		if v == nil {
			return nil
		}
		details, err = s.txDetails(ns, txHash, k, v)
		return err
	})
	return details, err
}

func (s *Store) txDetails(ns walletdb.Bucket, txHash *wire.ShaHash, recKey, recVal []byte) (*TxDetails, error) {
	var details TxDetails

	// Parse transaction record k/v, lookup the full block record for the
	// block time, and read all matching credits, debits.
	err := readRawTxRecord(txHash, recVal, &details.TxRecord)
	if err != nil {
		return nil, err
	}
	err = readRawTxRecordBlock(recKey, &details.Block.Block)
	if err != nil {
		return nil, err
	}
	details.Block.Time, err = fetchBlockTime(ns, details.Block.Height)
	if err != nil {
		return nil, err
	}

	credIter := makeCreditIterator(ns, recKey)
	for credIter.next() {
		if int(credIter.elem.Index) >= len(details.MsgTx.TxOut) {
			str := "saved credit index exceeds number of outputs"
			return nil, storeError(ErrData, str, nil)
		}

		details.Credits = append(details.Credits, credIter.elem)
	}
	if credIter.err != nil {
		return nil, credIter.err
	}

	debIter := makeDebitIterator(ns, recKey)
	for debIter.next() {
		if int(debIter.elem.Index) >= len(details.MsgTx.TxIn) {
			str := "saved debit index exceeds number of inputs"
			return nil, storeError(ErrData, str, nil)
		}

		details.Debits = append(details.Debits, debIter.elem)
	}
	return &details, debIter.err
}

func (s *Store) unminedTxDetails(ns walletdb.Bucket, txHash *wire.ShaHash, v []byte) (*TxDetails, error) {
	var details TxDetails
	err := readRawTxRecord(txHash, v, &details.TxRecord)
	if err != nil {
		return nil, err
	}

	it := makeUnminedCreditIterator(ns, txHash)
	for it.next() {
		if int(it.elem.Index) >= len(details.MsgTx.TxOut) {
			str := "saved credit index exceeds number of outputs"
			return nil, storeError(ErrData, str, nil)
		}

		// Set the Spent field since this is not done by the iterator.
		it.elem.Spent = existsRawUnminedInput(ns, it.ck) != nil
		details.Credits = append(details.Credits, it.elem)
	}
	if it.err != nil {
		return nil, it.err
	}

	// Debit records are not saved for unmined transactions.  Instead, they
	// must be looked up for each transaction input manually.  There are two
	// kinds of previous credits that may be debited by an unmined
	// transaction: mined unspent outputs (which remain marked unspent even
	// when spent by an unmined transaction), and credits from other unmined
	// transactions.  Both situations must be considered.
	for i, output := range details.MsgTx.TxIn {
		opKey := canonicalOutPoint(&output.PreviousOutPoint.Hash,
			output.PreviousOutPoint.Index)
		credKey := existsRawUnspent(ns, opKey)
		if credKey != nil {
			v := existsRawCredit(ns, credKey)
			amount, err := fetchRawCreditAmount(v)
			if err != nil {
				return nil, err
			}

			details.Debits = append(details.Debits, DebitRecord{
				Amount: amount,
				Index:  uint32(i),
			})
			continue
		}

		v := existsRawUnminedCredit(ns, opKey)
		if v == nil {
			continue
		}

		amount, err := fetchRawCreditAmount(v)
		if err != nil {
			return nil, err
		}
		details.Debits = append(details.Debits, DebitRecord{
			Amount: amount,
			Index:  uint32(i),
		})
	}

	return &details, nil
}

// RangeTransactions runs the function f on all transaction details between
// blocks on the best chain over the height range [begin,end].  The special
// height -1 may be used to also include unmined transactions.  If the end
// height comes before the begin height, blocks are iterated in reverse order
// and unmined transactions (if any) are processed first.
//
// The function f may return an error which, if non-nil, is propigated to the
// caller.  Additionally, a boolean return value allows exiting the function
// early without reading any additional transactions early when true.
//
// All calls to f are guaranteed to be passed a slice with more than zero
// elements.  The slice may be reused for multiple blocks, so it is not safe to
// use it after the loop iteration it was acquired.
func (s *Store) RangeTransactions(begin, end int32, f func([]TxDetails) (bool, error)) error {
	return scopedView(s.namespace, func(ns walletdb.Bucket) error {
		var addedUnmined bool
		if begin < 0 {
			brk, err := s.rangeUnminedTransactions(ns, f)
			if err != nil || brk {
				return err
			}
			addedUnmined = true
		}

		brk, err := s.rangeBlockTransactions(ns, begin, end, f)
		if err == nil && !brk && !addedUnmined && end < 0 {
			_, err = s.rangeUnminedTransactions(ns, f)
		}
		return err
	})
}

func (s *Store) rangeUnminedTransactions(ns walletdb.Bucket, f func([]TxDetails) (bool, error)) (brk bool, err error) {
	var details []TxDetails
	err = ns.Bucket(bucketUnmined).ForEach(func(k, v []byte) error {
		if len(k) < 32 {
			str := fmt.Sprintf("%s: short key (expected %d "+
				"bytes, read %d)", bucketUnmined, 32, len(k))
			return storeError(ErrData, str, nil)
		}

		var txHash wire.ShaHash
		copy(txHash[:], k)
		detail, err := s.unminedTxDetails(ns, &txHash, v)
		if err != nil {
			return err
		}

		// Because the key was created while foreach-ing over the
		// bucket, it should be impossible for unminedTxDetails to ever
		// successfully return a nil details struct.
		details = append(details, *detail)
		return nil
	})
	if err == nil && len(details) > 0 {
		return f(details)
	}
	return false, err
}

func (s *Store) rangeBlockTransactions(ns walletdb.Bucket, begin, end int32, f func([]TxDetails) (bool, error)) (brk bool, err error) {
	// Mempool height is considered a high bound.
	if begin < 0 {
		begin = int32(^uint32(0) >> 1)
	}
	if end < 0 {
		end = int32(^uint32(0) >> 1)
	}

	var blockIter blockIterator
	var advance func(*blockIterator) bool
	if begin < end {
		// Iterate in forwards order
		blockIter = makeBlockIterator(ns, begin)
		advance = func(it *blockIterator) bool {
			if !it.next() {
				return false
			}
			return it.elem.Height <= end
		}
	} else {
		// Iterate in backwards order, from begin -> end.
		blockIter = makeBlockIterator(ns, begin)
		advance = func(it *blockIterator) bool {
			if !it.prev() {
				return false
			}
			return end <= it.elem.Height
		}
	}

	var details []TxDetails
	for advance(&blockIter) {
		block := &blockIter.elem

		if cap(details) < len(block.transactions) {
			details = make([]TxDetails, 0, len(block.transactions))
		} else {
			details = details[:0]
		}

		for _, txHash := range block.transactions {
			k := keyTxRecord(&txHash, &block.Block)
			v := existsRawTxRecord(ns, k)
			if v == nil {
				str := fmt.Sprintf("missing transaction %v for "+
					"block %v", txHash, block.Height)
				return false, storeError(ErrData, str, nil)
			}
			detail := TxDetails{
				Block: BlockMeta{
					Block: block.Block,
					Time:  block.Time,
				},
			}
			err := readRawTxRecord(&txHash, v, &detail.TxRecord)
			if err != nil {
				return false, err
			}

			credIter := makeCreditIterator(ns, k)
			for credIter.next() {
				if int(credIter.elem.Index) >= len(detail.MsgTx.TxOut) {
					str := "saved credit index exceeds number of outputs"
					return false, storeError(ErrData, str, nil)
				}

				detail.Credits = append(detail.Credits, credIter.elem)
			}
			if credIter.err != nil {
				return false, credIter.err
			}

			debIter := makeDebitIterator(ns, k)
			for debIter.next() {
				if int(debIter.elem.Index) >= len(detail.MsgTx.TxIn) {
					str := "saved debit index exceeds number of inputs"
					return false, storeError(ErrData, str, nil)
				}

				detail.Debits = append(detail.Debits, debIter.elem)
			}
			if debIter.err != nil {
				return false, debIter.err
			}

			details = append(details, detail)
		}

		// Every block record must have at least one transaction, so it
		// is safe to call f.
		brk, err := f(details)
		if err != nil || brk {
			return brk, err
		}
	}
	return false, blockIter.err
}

// PreviousPkScripts returns a slice of previous output scripts for each output
// this transaction record debits from.
func (s *Store) PreviousPkScripts(rec *TxRecord, block *Block) ([][]byte, error) {
	var pkScripts [][]byte
	err := scopedView(s.namespace, func(ns walletdb.Bucket) error {
		if block == nil {
			for _, input := range rec.MsgTx.TxIn {
				prevOut := &input.PreviousOutPoint

				// Input may spend a previous unmined output, a
				// mined output (which would still be marked
				// unspent), or neither.

				v := existsRawUnmined(ns, prevOut.Hash[:])
				if v != nil {
					pkScript, err := fetchRawTxRecordPkScript(
						prevOut.Hash[:], v, prevOut.Index)
					if err != nil {
						return err
					}
					pkScripts = append(pkScripts, pkScript)
					continue
				}

				_, credKey := existsUnspent(ns, prevOut)
				if credKey != nil {
					k := extractRawCreditTxRecordKey(credKey)
					v = existsRawTxRecord(ns, k)
					pkScript, err := fetchRawTxRecordPkScript(k, v,
						prevOut.Index)
					if err != nil {
						return err
					}
					pkScripts = append(pkScripts, pkScript)
				}
			}
		}

		recKey := keyTxRecord(&rec.Hash, block)
		it := makeDebitIterator(ns, recKey)
		for it.next() {
			credKey := extractRawDebitCreditKey(it.cv)
			index := extractRawCreditIndex(credKey)
			k := extractRawCreditTxRecordKey(credKey)
			v := existsRawTxRecord(ns, k)
			pkScript, err := fetchRawTxRecordPkScript(k, v, index)
			if err != nil {
				return err
			}
			pkScripts = append(pkScripts, pkScript)
		}
		return it.err
	})
	return pkScripts, err
}
