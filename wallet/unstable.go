// Copyright (c) 2016 The Decred developers
// Use of this source code is governed by an ISC
// license that can be found in the LICENSE file.

package wallet

import (
	"github.com/decred/dcrd/chaincfg/chainhash"
	"github.com/decred/dcrutil"
	"github.com/decred/dcrwallet/walletdb"
	"github.com/decred/dcrwallet/wtxmgr"
)

// UnstableAPI exposes additional unstable public APIs for a Wallet.  These APIs
// may be changed or removed at any time.  Currently this type exists to ease
// the transation (particularly for the legacy JSON-RPC server) from using
// exported manager packages to a unified wallet package that exposes all
// functionality by itself.  New code should not be written using this API.
type UnstableAPI struct {
	w *Wallet
}

// NewUnstableAPI allows access to unstable APIs for a wallet.
func NewUnstableAPI(w *Wallet) UnstableAPI { return UnstableAPI{w} }

// TxDetails calls wtxmgr.Store.TxDetails under a single database view transaction.
func (u UnstableAPI) TxDetails(txHash *chainhash.Hash) (*wtxmgr.TxDetails, error) {
	var details *wtxmgr.TxDetails
	err := walletdb.View(u.w.db, func(dbtx walletdb.ReadTx) error {
		txmgrNs := dbtx.ReadBucket(wtxmgrNamespaceKey)
		var err error
		details, err = u.w.TxStore.TxDetails(txmgrNs, txHash)
		return err
	})
	return details, err
}

// RangeTransactions calls wtxmgr.Store.RangeTransactions under a single
// database view tranasction.
func (u UnstableAPI) RangeTransactions(begin, end int32, f func([]wtxmgr.TxDetails) (bool, error)) error {
	return walletdb.View(u.w.db, func(dbtx walletdb.ReadTx) error {
		txmgrNs := dbtx.ReadBucket(wtxmgrNamespaceKey)
		return u.w.TxStore.RangeTransactions(txmgrNs, begin, end, f)
	})
}

// UnspentMultisigCreditsForAddress calls
// wtxmgr.Store.UnspentMultisigCreditsForAddress under a single database view
// transaction.
func (u UnstableAPI) UnspentMultisigCreditsForAddress(p2shAddr *dcrutil.AddressScriptHash) ([]*wtxmgr.MultisigCredit, error) {
	var multisigCredits []*wtxmgr.MultisigCredit
	err := walletdb.View(u.w.db, func(tx walletdb.ReadTx) error {
		txmgrNs := tx.ReadBucket(wtxmgrNamespaceKey)
		var err error
		multisigCredits, err = u.w.TxStore.UnspentMultisigCreditsForAddress(
			txmgrNs, p2shAddr)
		return err
	})
	return multisigCredits, err
}