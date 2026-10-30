import HeckeGeneral.Arithmetic.SIntegerOrbits
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Tactic

/-!
Power saturation of the actual valuation-defined S-unit group in K^x.
This is valid for every set S: neither finiteness of S nor a class-number
assumption is needed. The ordered valuation group has no nontrivial torsion.
No Kummer character or faithfulness hypothesis is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeGeneral.Arithmetic.RowFaithfulnessDraft

open NumberField IsDedekindDomain

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K)))

/-- A positive power of a field unit is an S-unit only if the unit itself is. -/
theorem mem_sUnit_of_pow_mem (b : Kˣ) (n : ℕ) (hn : 0 < n)
    (hb : b ^ n ∈ S.unit K) : b ∈ S.unit K := by
  intro p hp
  have hv : p.valuation K ((b ^ n : Kˣ) : K) = 1 := hb p hp
  have hvpow : (p.valuation K (b : K)) ^ n = 1 := by
    simpa only [Units.val_pow_eq_pow_val, map_pow] using hv
  exact (pow_eq_one_iff_of_nonneg (by exact bot_le) hn.ne').mp hvpow

/-- A field root of an S-unit is an actual S-unit root in the original S.
The conclusion is equality in the S-unit group, not only a valuation bound. -/
theorem exists_sUnit_root_of_field_power
    (u : S.unit K) (b : K) (n : ℕ) (hn : 0 < n)
    (hpow : b ^ n = ((u : Kˣ) : K)) :
    ∃ v : S.unit K, v ^ n = u := by
  have hb : b ≠ 0 := by
    intro hz
    rw [hz, zero_pow hn.ne'] at hpow
    exact (u.val.ne_zero) hpow.symm
  let bU : Kˣ := Units.mk0 b hb
  have hmem : bU ^ n ∈ S.unit K := by
    intro p hp
    change p.valuation K (b ^ n) = 1
    rw [hpow]
    exact u.property p hp
  let v : S.unit K := ⟨bU, mem_sUnit_of_pow_mem K S bU n hn hmem⟩
  refine ⟨v, ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact hpow

end HeckeGeneral.Arithmetic.RowFaithfulnessDraft
