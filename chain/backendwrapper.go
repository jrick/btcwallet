// Copyright (c) 2017 The Decred developers
// Use of this source code is governed by an ISC
// license that can be found in the LICENSE file.

package chain

import (
	"context"
	"encoding/hex"
	"io"

	"github.com/decred/dcrd/chaincfg/chainhash"
	"github.com/decred/dcrd/dcrutil"
	"github.com/decred/dcrd/gcs"
	"github.com/decred/dcrd/rpcclient"
	"github.com/decred/dcrd/wire"
	"github.com/decred/dcrwallet/errors"
	"github.com/decred/dcrwallet/wallet"
	"golang.org/x/sync/errgroup"
)

type rpcBackend struct {
	rpcClient *rpcclient.Client
}

var _ wallet.NetworkBackend = (*rpcBackend)(nil)

// BackendFromRPCClient creates a wallet network backend from an RPC client.
func BackendFromRPCClient(rpcClient *rpcclient.Client) wallet.NetworkBackend {
	return &rpcBackend{rpcClient}
}

// RPCClientFromBackend returns the RPC client used to create a wallet network
// backend.  This errors if the backend was not created using
// BackendFromRPCClient.
func RPCClientFromBackend(n wallet.NetworkBackend) (*rpcclient.Client, error) {
	const op errors.Op = "chain.RPCClientFromBackend"

	b, ok := n.(*rpcBackend)
	if !ok {
		return nil, errors.E(op, errors.Invalid, "this operation requires "+
			"the network backend to be the consensus RPC server")
	}
	return b.rpcClient, nil
}

func (b *rpcBackend) GetBlocks(ctx context.Context, blockHashes []*chainhash.Hash) ([]*wire.MsgBlock, error) {
	const op errors.Op = "dcrd.jsonrpc.getblock"

	blocks := make([]*wire.MsgBlock, len(blockHashes))
	var g errgroup.Group
	for i := range blockHashes {
		i := i
		g.Go(func() error {
			block, err := b.rpcClient.GetBlock(blockHashes[i])
			blocks[i] = block
			return err
		})
	}
	err := g.Wait()
	if err != nil {
		return nil, errors.E(op, err)
	}
	return blocks, nil
}

func (b *rpcBackend) GetCFilters(ctx context.Context, blockHashes []*chainhash.Hash) ([]*gcs.Filter, error) {
	const op errors.Op = "dcrd.jsonrpc.getcfilter"

	// TODO: this is spammy and would be better implemented with a single RPC.
	filters := make([]*gcs.Filter, len(blockHashes))
	var g errgroup.Group
	for i := range blockHashes {
		i := i
		g.Go(func() error {
			f, err := b.rpcClient.GetCFilter(blockHashes[i], wire.GCSFilterRegular)
			filters[i] = f
			return err
		})
	}
	err := g.Wait()
	if err != nil {
		return nil, errors.E(op, err)
	}
	return filters, nil
}

func (b *rpcBackend) GetHeaders(ctx context.Context, blockLocators []*chainhash.Hash, hashStop *chainhash.Hash) ([]*wire.BlockHeader, error) {
	const op errors.Op = "dcrd.jsonrpc.getheaders"

	r, err := b.rpcClient.GetHeaders(blockLocators, hashStop)
	if err != nil {
		return nil, errors.E(op, err)
	}
	headers := make([]*wire.BlockHeader, 0, len(r.Headers))
	for _, hexHeader := range r.Headers {
		header := new(wire.BlockHeader)
		err := header.Deserialize(newHexReader(hexHeader))
		if err != nil {
			return nil, errors.E(op, errors.Encoding, err)
		}
		headers = append(headers, header)
	}
	return headers, nil
}

func (b *rpcBackend) LoadTxFilter(ctx context.Context, reload bool, addrs []dcrutil.Address, outpoints []wire.OutPoint) error {
	const op errors.Op = "dcrd.jsonrpc.loadtxfilter"

	err := b.rpcClient.LoadTxFilter(reload, addrs, outpoints)
	if err != nil {
		return errors.E(op, err)
	}
	return nil
}

func (b *rpcBackend) PublishTransaction(ctx context.Context, tx *wire.MsgTx) error {
	const op errors.Op = "dcrd.jsonrpc.sendrawtransaction"

	// High fees are hardcoded and allowed here since transactions created by
	// the wallet perform their own high fee check if high fees are disabled.
	// This matches the lack of any high fee checking when publishing
	// transactions over the wire protocol.
	_, err := b.rpcClient.SendRawTransaction(tx, true)
	if err != nil {
		return errors.E(op, err)
	}
	return nil
}

func (b *rpcBackend) Rescan(ctx context.Context, blocks []chainhash.Hash) ([]*wallet.RescannedBlock, error) {
	const op errors.Op = "dcrd.jsonrpc.rescan"

	r, err := b.rpcClient.Rescan(blocks)
	if err != nil {
		return nil, errors.E(op, err)
	}
	discoveredData := make([]*wallet.RescannedBlock, 0, len(r.DiscoveredData))
	for _, d := range r.DiscoveredData {
		blockHash, err := chainhash.NewHashFromStr(d.Hash)
		if err != nil {
			return nil, errors.E(op, errors.Encoding, err)
		}
		txs := make([]*wire.MsgTx, 0, len(d.Transactions))
		for _, txHex := range d.Transactions {
			tx := new(wire.MsgTx)
			err := tx.Deserialize(newHexReader(txHex))
			if err != nil {
				return nil, errors.E(op, errors.Encoding, err)
			}
			txs = append(txs, tx)
		}
		rescannedBlock := &wallet.RescannedBlock{
			BlockHash:    *blockHash,
			Transactions: txs,
		}
		discoveredData = append(discoveredData, rescannedBlock)
	}
	return discoveredData, nil
}

func (b *rpcBackend) StakeDifficulty(ctx context.Context) (dcrutil.Amount, error) {
	const op errors.Op = "dcrd.jsonrpc.getstakedifficulty"

	r, err := b.rpcClient.GetStakeDifficulty()
	if err != nil {
		return 0, errors.E(op, err)
	}
	amount, err := dcrutil.NewAmount(r.NextStakeDifficulty)
	if err != nil {
		return 0, errors.E(op, err)
	}
	return amount, nil
}

// hexReader implements io.Reader to read bytes from a hexadecimal string.
// TODO: Replace with hex.NewDecoder (available since Go 1.10)
type hexReader struct {
	hex   string
	index int
}

func newHexReader(s string) *hexReader {
	return &hexReader{hex: s}
}

func (r *hexReader) Read(b []byte) (n int, err error) {
	end := r.index + 2*len(b)
	if end > len(r.hex) {
		end = len(r.hex)
	}
	src := r.hex[r.index:end]
	n, err = hex.Decode(b, []byte(src))
	r.index += 2 * n
	if err == nil && n == 0 {
		return 0, io.EOF
	}
	return n, err
}
