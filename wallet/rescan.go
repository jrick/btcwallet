// Copyright (c) 2013-2014 The btcsuite developers
// Copyright (c) 2015-2016 The Decred developers
// Use of this source code is governed by an ISC
// license that can be found in the LICENSE file.

package wallet

import (
	"context"
	"time"

	"github.com/decred/dcrd/chaincfg/chainhash"
	"github.com/decred/dcrd/dcrutil"
	"github.com/decred/dcrd/wire"
	"github.com/decred/dcrwallet/errors"
	"github.com/decred/dcrwallet/wallet/udb"
	"github.com/decred/dcrwallet/walletdb"
	"golang.org/x/crypto/ripemd160"
)

const maxBlocksPerRescan = 2000

// RescanFilter implements a precise filter intended to hold all watched wallet
// data in memory such as addresses and unspent outputs.  The zero value is not
// valid, and filters must be created using NewRescanFilter.  RescanFilter is
// not safe for concurrent access.
type RescanFilter struct {
	// Implemented fast paths for address lookup.
	pubKeyHashes        map[[ripemd160.Size]byte]struct{}
	scriptHashes        map[[ripemd160.Size]byte]struct{}
	compressedPubKeys   map[[33]byte]struct{}
	uncompressedPubKeys map[[65]byte]struct{}

	// A fallback address lookup map in case a fast path doesn't exist.
	// Only exists for completeness.  If using this shows up in a profile,
	// there's a good chance a fast path should be added.
	otherAddresses map[string]struct{}

	// Outpoints of unspent outputs.
	unspent map[wire.OutPoint]struct{}
}

// NewRescanFilter creates and initializes a RescanFilter containing each passed
// address and outpoint.
func NewRescanFilter(addresses []dcrutil.Address, unspentOutPoints []*wire.OutPoint) *RescanFilter {
	filter := &RescanFilter{
		pubKeyHashes:        map[[ripemd160.Size]byte]struct{}{},
		scriptHashes:        map[[ripemd160.Size]byte]struct{}{},
		compressedPubKeys:   map[[33]byte]struct{}{},
		uncompressedPubKeys: map[[65]byte]struct{}{},
		otherAddresses:      map[string]struct{}{},
		unspent:             make(map[wire.OutPoint]struct{}, len(unspentOutPoints)),
	}

	for _, s := range addresses {
		filter.AddAddress(s)
	}
	for _, op := range unspentOutPoints {
		filter.AddUnspentOutPoint(op)
	}

	return filter
}

// AddAddress adds an address to the filter if it does not already exist.
func (f *RescanFilter) AddAddress(a dcrutil.Address) {
	switch a := a.(type) {
	case *dcrutil.AddressPubKeyHash:
		f.pubKeyHashes[*a.Hash160()] = struct{}{}
	case *dcrutil.AddressScriptHash:
		f.scriptHashes[*a.Hash160()] = struct{}{}
	case *dcrutil.AddressSecpPubKey:
		serializedPubKey := a.ScriptAddress()
		switch len(serializedPubKey) {
		case 33: // compressed
			var compressedPubKey [33]byte
			copy(compressedPubKey[:], serializedPubKey)
			f.compressedPubKeys[compressedPubKey] = struct{}{}
		case 65: // uncompressed
			var uncompressedPubKey [65]byte
			copy(uncompressedPubKey[:], serializedPubKey)
			f.uncompressedPubKeys[uncompressedPubKey] = struct{}{}
		}
	default:
		f.otherAddresses[a.EncodeAddress()] = struct{}{}
	}
}

// ExistsAddress returns whether an address is contained in the filter.
func (f *RescanFilter) ExistsAddress(a dcrutil.Address) (ok bool) {
	switch a := a.(type) {
	case *dcrutil.AddressPubKeyHash:
		_, ok = f.pubKeyHashes[*a.Hash160()]
	case *dcrutil.AddressScriptHash:
		_, ok = f.scriptHashes[*a.Hash160()]
	case *dcrutil.AddressSecpPubKey:
		serializedPubKey := a.ScriptAddress()
		switch len(serializedPubKey) {
		case 33: // compressed
			var compressedPubKey [33]byte
			copy(compressedPubKey[:], serializedPubKey)
			_, ok = f.compressedPubKeys[compressedPubKey]
			if !ok {
				_, ok = f.pubKeyHashes[*a.AddressPubKeyHash().Hash160()]
			}
		case 65: // uncompressed
			var uncompressedPubKey [65]byte
			copy(uncompressedPubKey[:], serializedPubKey)
			_, ok = f.uncompressedPubKeys[uncompressedPubKey]
			if !ok {
				_, ok = f.pubKeyHashes[*a.AddressPubKeyHash().Hash160()]
			}
		}
	default:
		_, ok = f.otherAddresses[a.EncodeAddress()]
	}
	return
}

// RemoveAddress removes an address from the filter if it exists.
func (f *RescanFilter) RemoveAddress(a dcrutil.Address) {
	switch a := a.(type) {
	case *dcrutil.AddressPubKeyHash:
		delete(f.pubKeyHashes, *a.Hash160())
	case *dcrutil.AddressScriptHash:
		delete(f.scriptHashes, *a.Hash160())
	case *dcrutil.AddressSecpPubKey:
		serializedPubKey := a.ScriptAddress()
		switch len(serializedPubKey) {
		case 33: // compressed
			var compressedPubKey [33]byte
			copy(compressedPubKey[:], serializedPubKey)
			delete(f.compressedPubKeys, compressedPubKey)
		case 65: // uncompressed
			var uncompressedPubKey [65]byte
			copy(uncompressedPubKey[:], serializedPubKey)
			delete(f.uncompressedPubKeys, uncompressedPubKey)
		}
	default:
		delete(f.otherAddresses, a.EncodeAddress())
	}
}

// AddUnspentOutPoint adds an outpoint to the filter if it does not already
// exist.
func (f *RescanFilter) AddUnspentOutPoint(op *wire.OutPoint) {
	f.unspent[*op] = struct{}{}
}

// ExistsUnspentOutPoint returns whether an outpoint is contained in the filter.
func (f *RescanFilter) ExistsUnspentOutPoint(op *wire.OutPoint) bool {
	_, ok := f.unspent[*op]
	return ok
}

// RemoveUnspentOutPoint removes an outpoint from the filter if it exists.
func (f *RescanFilter) RemoveUnspentOutPoint(op *wire.OutPoint) {
	delete(f.unspent, *op)
}

// RescannedBlock models the relevant data returned during a rescan from a
// single block.
type RescannedBlock struct {
	BlockHash    chainhash.Hash
	Transactions []*wire.MsgTx
}

// rescan synchronously scans over all blocks on the main chain starting at
// startHash and height up through the recorded main chain tip block.  The
// progress channel, if non-nil, is sent non-error progress notifications with
// the heights the rescan has completed through, starting with the start height.
func (w *Wallet) rescan(ctx context.Context, n NetworkBackend,
	startHash *chainhash.Hash, height int32, p chan<- RescanProgress) error {

	blockHashStorage := make([]chainhash.Hash, maxBlocksPerRescan)
	rescanFrom := *startHash
	inclusive := true
	for {
		select {
		case <-ctx.Done():
			return ctx.Err()
		default:
		}

		var rescanBlocks []chainhash.Hash
		err := walletdb.View(w.db, func(dbtx walletdb.ReadTx) error {
			txmgrNs := dbtx.ReadBucket(wtxmgrNamespaceKey)
			var err error
			rescanBlocks, err = w.TxStore.GetMainChainBlockHashes(txmgrNs,
				&rescanFrom, inclusive, blockHashStorage)
			return err
		})
		if err != nil {
			return err
		}
		if len(rescanBlocks) == 0 {
			return nil
		}

		scanningThrough := height + int32(len(rescanBlocks)) - 1
		log.Infof("Rescanning blocks %v-%v...", height,
			scanningThrough)
		rescanResults, err := n.Rescan(ctx, rescanBlocks)
		if err != nil {
			return err
		}
		err = walletdb.Update(w.db, func(dbtx walletdb.ReadWriteTx) error {
			txmgrNs := dbtx.ReadWriteBucket(wtxmgrNamespaceKey)
			for _, r := range rescanResults {
				blockMeta, err := w.TxStore.GetBlockMetaForHash(txmgrNs, &r.BlockHash)
				if err != nil {
					return err
				}
				header, err := w.TxStore.GetBlockHeader(dbtx, &r.BlockHash)
				if err != nil {
					return err
				}

				for _, tx := range r.Transactions {
					rec, err := udb.NewTxRecordFromMsgTx(tx, time.Now())
					if err != nil {
						return err
					}
					err = w.processTransactionRecord(dbtx, rec, header, &blockMeta)
					if err != nil {
						return err
					}
				}
			}
			return nil
		})
		if err != nil {
			return err
		}
		if p != nil {
			p <- RescanProgress{ScannedThrough: scanningThrough}
		}
		rescanFrom = rescanBlocks[len(rescanBlocks)-1]
		height += int32(len(rescanBlocks))
		inclusive = false
	}
}

// Rescan starts a rescan of the wallet for all blocks on the main chain
// beginning at startHash.  This function blocks until the rescan completes.
func (w *Wallet) Rescan(ctx context.Context, n NetworkBackend, startHash *chainhash.Hash) error {
	const op errors.Op = "wallet.Rescan"

	var startHeight int32
	err := walletdb.View(w.db, func(tx walletdb.ReadTx) error {
		txmgrNs := tx.ReadBucket(wtxmgrNamespaceKey)
		header, err := w.TxStore.GetSerializedBlockHeader(txmgrNs, startHash)
		if err != nil {
			return err
		}
		startHeight = udb.ExtractBlockHeaderHeight(header)
		return nil
	})
	if err != nil {
		return errors.E(op, err)
	}

	err = w.rescan(ctx, n, startHash, startHeight, nil)
	if err != nil {
		return errors.E(op, err)
	}
	return nil
}

// RescanFromHeight is an alternative to Rescan that takes a block height
// instead of a hash.  See Rescan for more details.
func (w *Wallet) RescanFromHeight(ctx context.Context, n NetworkBackend, startHeight int32) error {
	const op errors.Op = "wallet.RescanFromHeight"

	var startHash chainhash.Hash
	err := walletdb.View(w.db, func(tx walletdb.ReadTx) error {
		txmgrNs := tx.ReadBucket(wtxmgrNamespaceKey)
		var err error
		startHash, err = w.TxStore.GetMainChainBlockHashForHeight(
			txmgrNs, startHeight)
		return err
	})
	if err != nil {
		return errors.E(op, err)
	}

	err = w.rescan(ctx, n, &startHash, startHeight, nil)
	if err != nil {
		return errors.E(op, err)
	}
	return nil
}

// RescanProgress records the height the rescan has completed through and any
// errors during processing of the rescan.
type RescanProgress struct {
	Err            error
	ScannedThrough int32
}

// RescanProgressFromHeight rescans for relevant transactions in all blocks in
// the main chain starting at startHeight.  Progress notifications and any
// errors are sent to the channel p.  This function blocks until the rescan
// completes or ends in an error.  p is closed before returning.
func (w *Wallet) RescanProgressFromHeight(ctx context.Context, n NetworkBackend,
	startHeight int32, p chan<- RescanProgress) {

	const op errors.Op = "wallet.RescanProgressFromHeight"

	defer close(p)

	var startHash chainhash.Hash
	err := walletdb.View(w.db, func(tx walletdb.ReadTx) error {
		txmgrNs := tx.ReadBucket(wtxmgrNamespaceKey)
		var err error
		startHash, err = w.TxStore.GetMainChainBlockHashForHeight(
			txmgrNs, startHeight)
		return err
	})
	if err != nil {
		p <- RescanProgress{Err: errors.E(op, err)}
		return
	}

	err = w.rescan(ctx, n, &startHash, startHeight, p)
	if err != nil {
		p <- RescanProgress{Err: errors.E(op, err)}
	}
}
