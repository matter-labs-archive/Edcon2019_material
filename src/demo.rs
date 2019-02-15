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

const NUM_VALUE_BITS: usize = 128;
const NUM_BLINDING_BITS: usize = 128;

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
            let bit = boolean::Boolean::from(
                boolean::AllocatedBit::alloc(
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

        // hash is now is just an array of 256 bits. Our field is limited
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

        let remaining_value = num::AllocatedNum::alloc(
            cs.namespace(|| "remaining value"), 
            || {
                let mut v1 = *value.get_value().get()?;
                let v2 = *utxo_value.get_value().get()?;

                v1.sub_assign(&v2);

                Ok(v1)
            }
        )?;

        cs.enforce(
            || "enforce value reduction",
            |lc| lc + remaining_value.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + value.get_variable() - utxo_value.get_variable()
        );

        remaining_value.limit_number_of_bits(
            cs.namespace(|| "limit number of bits in remaining value"),
            NUM_VALUE_BITS
        )?;

        Ok(())
    }
}