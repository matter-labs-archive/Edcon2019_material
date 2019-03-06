# Edcon2019 material

Code in this repo was made for Edcon2019 zkSNARKs workshop to explain how to make zk circuits (statements) using bellman + sapling-crypto gadget library.

## Structure

Repo is essentially a single file `src/circuit.rs` (a `demo.rs` was just copy-pasted over the webcast from the `circuit.rs`). It demonstrates how to use primitives like `Boolean`, `AllocatedNum`, `sha256` inside of the circuit, properly declare witnesses and generate parameters and proofs for circuits. Comments are by author and are for rough guidance, but most likely are not sufficient for complete understanding.
