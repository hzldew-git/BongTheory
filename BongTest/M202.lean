import Bong.Lattice.DVRFactorization

/-! Smoke checks for milestone M202. -/

open Bong
open Bong.Dyadic

#check uniformizerInteger
#check coe_uniformizerInteger
#check uniformizerInteger_ne_zero
#check exists_eq_uniformizerInteger_pow_mul_unit

#print axioms exists_eq_uniformizerInteger_pow_mul_unit
