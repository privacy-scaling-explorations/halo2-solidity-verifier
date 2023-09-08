# Halo2 Solidity Verifier

Solidity verifier generator for [`halo2`](http://github.com/privacy-scaling-explorations/halo2) proof with KZG polynomial commitment scheme on BN254

## Usage

### Generate verifier and verifying key separately as 2 solidity contracts

```rust
let generator = SolidityGenerator::new(&params, &vk, Bdfg21, num_instances);
let (verifier_solidity, vk_solidity) = generator.render_separately().unwrap();
```

Check [`examples/separately.rs`](./examples/separately.rs) for more details.

### Generate verifier and verifying key in a single solidity contract

```rust
let generator = SolidityGenerator::new(&params, &vk, Bdfg21, num_instances);
let verifier_solidity = generator.render().unwrap();
```

### Encode proof into calldata to invoke `verifyProof`

```rust
let calldata = encode_calldata(vk_address, &proof, &instances);
```

Note that function selector is already included.

## Limitation

- It only allows circuit with **exact 1 instance column** and **no rotated query to this instance column**.
- Option `--via-ir` seems necessary when compiling the generated contract, otherwise it'd cause stack too deep error. However, `--via-ir` is not allowed to be used with `--standard-json`, not sure how to work around this yet.
- Even the `configure` is same, the [selector compression](https://github.com/privacy-scaling-explorations/halo2/blob/7a2165617195d8baa422ca7b2b364cef02380390/halo2_proofs/src/plonk/circuit/compress_selectors.rs#L51) might lead to different configuration when selector assignments are different. To avoid this we might need to update halo2 to support disabling selector compression.
- Now it only supports BDFG21 batch open scheme (aka SHPLONK), GWC19 is not yet implemented.

## Compatibility

The [`Keccak256Transcript`](./src/transcript.rs#L19) behaves exactly same as the `EvmTranscript` in `snark-verifier`.

## Acknowledgement

The template is heavily inspired by Aztec's [`BaseUltraVerifier.sol`](https://github.com/AztecProtocol/barretenberg/blob/4c456a2b196282160fd69bead6a1cea85289af37/sol/src/ultra/BaseUltraVerifier.sol).
