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
    BitIterator
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
    PrimeOrder,
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
    pub value: Option<E::Fr>,
    pub blinding: Option<E::Fr>,
    // pub commitment: Option<edwards::Point<E, PrimeOrder>>
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

        // if time permits we can now also make an UTXO design

        let utxo_value = num::AllocatedNum::alloc(
            cs.namespace(|| "utxo value"),
            || {
                let value = self.utxo.value;
                Ok(*value.get()?)
            }
        )?;

        utxo_value.limit_number_of_bits(
            cs.namespace(|| "limit number of bits for value"),
            NUM_VALUE_BITS
        )?;

        let utxo_bits = utxo_value.into_bits_le(
            cs.namespace(|| "get utxo value bits")
        )?;

        let utxo_blinding = num::AllocatedNum::alloc(
            cs.namespace(|| "utxo blinding"),
            || {
                let value = self.utxo.blinding;
                Ok(*value.get()?)
            }
        )?;

        let blinding_bits = utxo_blinding.into_bits_le(
            cs.namespace(|| "get blinding bits")
        )?;


        let value_point = ecc::fixed_base_multiplication(
            cs.namespace(|| "value * G"), 
            FixedGenerators::ValueCommitmentValue, 
            &utxo_bits, 
            self.params
        )?;

        let blinding_point = ecc::fixed_base_multiplication(
            cs.namespace(|| "blinding * H"), 
            FixedGenerators::ValueCommitmentRandomness, 
            &blinding_bits, 
            self.params
        )?;

        let commitment_point = value_point.add(
            cs.namespace(|| "calculate commitment"),
            &blinding_point, 
            self.params
        )?;

        commitment_point.inputize(
            cs.namespace(|| "make commitment as input")
        )?;

        // let supplied_commitment = ecc::EdwardsPoint::witness(
        //     cs.namespace(|| "externally supplied commitment"),
        //     self.utxo.commitment,
        //     self.params
        // )?;

        let remaining_value = num::AllocatedNum::alloc(
            cs.namespace(|| "remaining_value"), 
            || {
                let mut v1 = *value.get_value().get()?;
                let v2 = *utxo_value.get_value().get()?;

                v1.sub_assign(&v2);

                Ok(v1)
            }
        )?;

        remaining_value.limit_number_of_bits(
            cs.namespace(|| "limit number of bits in remaining value"),
            NUM_VALUE_BITS
        )?;

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

pub fn le_bit_vector_into_field_element<P: PrimeField>
    (bits: &Vec<bool>) -> P
{
    // double and add
    let mut fe = P::zero();
    let mut base = P::one();

    for bit in bits {
        if *bit {
            fe.add_assign(&base);
        }
        base.double();
    }

    fe
}

pub fn encode_fs_into_fr<E: JubjubEngine>(input: E::Fs)
    -> E::Fr 
{
    let mut fs_le_bits: Vec<bool> = BitIterator::new(input.into_repr()).collect();
    fs_le_bits.reverse();

    let converted = le_bit_vector_into_field_element::<E::Fr>(&fs_le_bits);

    converted
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

    let (public_inputs, circuit) = {
        let value: u64 = rng.gen(); // Rand is not implemented for u128, so we can away with it
        let value = value as u128;
        let value_bits = u128_into_be_bits(value);

        let utxo_value = value / 100;
        let utxo_value = fs::Fs::from_str(&utxo_value.to_string()).expect("must make utxo value");
        let blinding: fs::Fs = rng.gen();

        let value_generator = params.generator(FixedGenerators::ValueCommitmentValue);
        let blinding_generator = params.generator(FixedGenerators::ValueCommitmentRandomness);

        let commitment = value_generator.mul(utxo_value, &params)
            .add(&blinding_generator.mul(blinding, &params), 
            &params
        );

        let (x,y) = commitment.into_xy();

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
            value: Some(encode_fs_into_fr::<Bn256>(utxo_value)),
            blinding: Some(encode_fs_into_fr::<Bn256>(blinding)),
            // commitment: None
        };

        let circuit = ConfidentialAccount::<Bn256> {
            params: &params,
            current_state: Some(current_account_state),
            witness: witness,
            utxo: utxo,
        };

        (vec![current_account_state, x, y], circuit)
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

    let is_valid = verify_proof(&prepared_vk, &proof, &public_inputs).expect("must verify a proof");

    assert!(is_valid, "proof was invalid");
    println!("Test is complete");
}