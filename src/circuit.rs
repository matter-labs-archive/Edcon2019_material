extern crate ff;
extern crate pairing;
extern crate bellman;
extern crate sapling_crypto;
extern crate crypto;
extern crate rand;

use ff::{
    PrimeField,
    PrimeFieldRepr,
    Field,
};

use pairing::{
    Engine
};

use bellman::{
    SynthesisError,
    ConstraintSystem,
    Circuit
};

use sapling_crypto::circuit::{
    Assignment,
    boolean,
    ecc,
    sha256,
    num,
    multipack,
};

use sapling_crypto::jubjub::{
    JubjubEngine,
    FixedGenerators,
    Unknown,
    edwards,
    JubjubParams
};

#[derive(Clone)]
pub struct AccountWitness {
    pub old_blinding_bits: Vec<Option<bool>>,
    pub new_blinding_bits: Vec<Option<bool>>,
    pub value_bits: Vec<Option<bool>>,
}

#[derive(Clone)]
pub struct UTXOWitness<E: JubjubEngine> {
    pub value: Option<E::Fs>,
    pub blinding: Option<E::Fs>,
}

pub struct ConfidentialAccount<'a, E: JubjubEngine> {
    pub params: &'a E::Params,

    // supply the current account state
    pub current_state: Option<E::Fr>,

    // Witnesses
    pub witness: AccountWitness,

    // UTXO witness
    pub utxo: UTXOWitness<E>
}

impl<'a, E:JubjubEngine + 'a> Clone for ConfidentialAccount<'a, E> {
    fn clone(&self) -> Self {
        ConfidentialAccount {
            params: self.params,
            current_state: self.current_state.clone(),
            witness: self.witness.clone(),
            utxo: self.utxo.clone()
        }
    }
}

const NUM_VALUE_BITS: usize = 128;
const NUM_BLINDING_BITS: usize = 128;

impl<'a, E: JubjubEngine> Circuit<E> for ConfidentialAccount<'a, E> {
    fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError>
    {
        assert_eq!(self.witness.old_blinding_bits.len(), NUM_BLINDING_BITS);
        assert_eq!(self.witness.new_blinding_bits.len(), NUM_BLINDING_BITS);
        assert_eq!(self.witness.value_bits.len(), NUM_VALUE_BITS);

        // Expose the current truncated hash as the input
        let current = num::AllocatedNum::alloc(
            cs.namespace(|| "current account state"),
            || {
                let value = self.current_state;
                Ok(*value.get()?)
            }
        )?;
        current.inputize(cs.namespace(|| "current state input"))?;

        let mut blinding_bits = Vec::<boolean::Boolean>::with_capacity(NUM_BLINDING_BITS);
        // allocate bits for use of sha256 
        for i in 0..NUM_BLINDING_BITS {
            let bit = boolean::Boolean::from(boolean::AllocatedBit::alloc(
                cs.namespace(|| format!("allocating blinding bit {}", i)),
                self.witness.old_blinding_bits[i]
                )?
            );
            blinding_bits.push(bit);
        }

        let mut value_bits = Vec::<boolean::Boolean>::with_capacity(NUM_VALUE_BITS);

        for i in 0..NUM_VALUE_BITS {
            let bit = boolean::Boolean::from(boolean::AllocatedBit::alloc(
                cs.namespace(|| format!("allocating value bit {}", i)),
                self.witness.value_bits[i]
                )?
            );
            value_bits.push(bit);
        }
        // use bit in to calculate a value

        // make a linear combination from bit decomposition
        let mut coeff = E::Fr::one();
        let mut num_lc = num::Num::<E>::zero();
        for bit in value_bits.iter() {
            num_lc = num_lc.add_bool_with_coeff(CS::one(), bit, coeff);
            coeff.double();
        }

        // allocate some number that should be equal to this combination
        let value = num::AllocatedNum::alloc(
            cs.namespace(|| "current value"), 
            || {
                let value = num_lc.get_value();

                Ok(*value.get()?)
            }
        )?;

        // enforce!

        cs.enforce(
            || "enforce current value allocation",
            |lc| lc + value.get_variable(),
            |lc| lc + CS::one(),
            // `lc` function returns `lc` scaled by the specified constant. In our case the constant is one
            |_| num_lc.lc(E::Fr::one())
        );

        // calculate the hash value

        // merge vectors

        blinding_bits.extend(value_bits);

        let mut hash = sha256::sha256(
            cs.namespace(|| "calculate old state hash"),
            &blinding_bits
        )?;

        // hash is not is just an array of 256 bits. Our field is limited
        // in number of bits that input can represent, so we need to truncate some of the bits

        // for convenience we reverse the array, trucrate it and interpret the rest as LE decomposition
        // of the field element

        hash.reverse();
        hash.truncate(E::Fr::CAPACITY as usize);

        let mut packed_hash_lc = num::Num::<E>::zero();
        let mut coeff = E::Fr::one();
        for bit in hash {
            packed_hash_lc = packed_hash_lc.add_bool_with_coeff(CS::one(), &bit, coeff);
            coeff.double();
        }

        cs.enforce(
            || "enforce state equality to external input",
            |lc| lc + current.get_variable(),
            |lc| lc + CS::one(),
            |_| packed_hash_lc.lc(E::Fr::one())
        );

        Ok(())
    }
}

fn be_bit_vector_into_bytes
    (bits: &Vec<bool>) -> Vec<u8>
{
    let mut bytes: Vec<u8> = vec![];
    for byte_chunk in bits.chunks(8)
    {
        let mut byte = 0u8;
        // pack just in order
        for (i, bit) in byte_chunk.iter().enumerate()
        {
            if *bit {
                byte |= 1 << (7 - i);
            }
        }
        bytes.push(byte);
    }

    bytes
}

fn u128_into_be_bits(value: u128) -> Vec<bool>
{
    let mut v = value;
    let mut bits: Vec<bool> = vec![];
    for _ in 0..128 {
        if v & 1 > 0 {
            bits.push(true);
        } else {
            bits.push(false);
        }
        v >>= 1;
    }
    bits.reverse();

    bits
}


#[test]
fn test_the_circuit() {
    use pairing::bn256::*;
    use rand::{SeedableRng, Rng, XorShiftRng, Rand};
    use sapling_crypto::circuit::test::*;
    use sapling_crypto::alt_babyjubjub::{AltJubjubBn256, fs, edwards, PrimeOrder};
    use bellman::groth16::{generate_random_parameters, create_random_proof, verify_proof, prepare_verifying_key};
    use crypto::sha2::Sha256;
    use crypto::digest::Digest;

    let params = &AltJubjubBn256::new();

    let mut rng = XorShiftRng::from_seed([0x3dbe6258, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    let (public_input, circuit) = {
        let value: u64 = rng.gen(); // Rand is not implemented for u128, so we can away with it
        let value = value as u128;
        let value_bits = u128_into_be_bits(value);

        let old_blinding_bits: Vec<bool> = (0..NUM_BLINDING_BITS).map(|_| rng.gen()).collect();

        let witness = AccountWitness {
            old_blinding_bits: old_blinding_bits.iter().map(|el| Some(*el)).collect(),
            new_blinding_bits: vec![Some(true); NUM_BLINDING_BITS],
            value_bits: value_bits.iter().map(|el| Some(*el)).collect(),
        };

        let mut current_state_bits = old_blinding_bits.clone();
        current_state_bits.extend(value_bits.clone());
        let bytes_to_hash: Vec<u8> = be_bit_vector_into_bytes(&current_state_bits);

        let mut hash_result = [0u8; 32];
        // calculate a hash and repack it as field element for witness
        let mut h = Sha256::new();
        h.input(&bytes_to_hash);
        h.result(&mut hash_result[..]);

        let bits_to_trim = 256 - Fr::CAPACITY;
        let trimming_mask = (1u8 << (8 - bits_to_trim)) - 1u8;

        assert_eq!(trimming_mask, 0x1f);

        // truncate the top bits if this hash to later use it as BE representation of a field element
        hash_result[0] &= trimming_mask; // trim top 3 bits for BN256 case.

        let mut repr = Fr::zero().into_repr();
        repr.read_be(&hash_result[..]).expect("pack hash as field element");
        let current_account_state = Fr::from_repr(repr).expect("must be a valud representation");

        let utxo = UTXOWitness::<Bn256> {
            value: None,
            blinding: None,
        };

        let circuit = ConfidentialAccount::<Bn256> {
            params: &params,
            current_state: Some(current_account_state),
            witness: witness,
            utxo: utxo,
        };

        (current_account_state, circuit)
    };

    // TestConstraintSystem is a special constraint system implementation that does not reduce R1CS
    // and eagerly calculates all closures
    {
        let mut cs = TestConstraintSystem::<Bn256>::new();

        let circuit = circuit.clone();

        circuit.synthesize(&mut cs).expect("circuit must synthesize");
        // we can use internal tools to check for some variables being unconstrained (e.g. declared, but not used)
        let unconstrained = cs.find_unconstrained();
        println!("{}", unconstrained);
        assert!(unconstrained == "");

        // let's check that our constraints are satisfied with a current assignment
        let unsatisfied = cs.which_is_unsatisfied();
        if unsatisfied.is_some() {
            panic!("{}", unsatisfied.unwrap());
        }
        println!("Constraint system is satisfied");
    };

    // we can generate parameters on an empty circuit actually!
    // closures compute the witness, but constraints do not depend on them
    let parameters = {
            let witness = AccountWitness {
                old_blinding_bits: vec![None; NUM_BLINDING_BITS],
                new_blinding_bits: vec![None; NUM_BLINDING_BITS],
                value_bits: vec![None; NUM_VALUE_BITS],
            };

            let utxo = UTXOWitness::<Bn256> {
                value: None,
                blinding: None,
            };

            let circuit = ConfidentialAccount::<Bn256> {
                params: &params,
                current_state: None,
                witness: witness,
                utxo: utxo,
            };

        generate_random_parameters(circuit, &mut rng).expect("must generate parameters")
    };

    let prepared_vk = prepare_verifying_key(&parameters.vk);

    // now let's make a proof
    let proof = {
        create_random_proof(circuit, &parameters, &mut rng).expect("must create a proof")
    };

    let is_valid = verify_proof(&prepared_vk, &proof, &vec![public_input]).expect("must verify a proof");

    assert!(is_valid);
    println!("Test is complete");
}