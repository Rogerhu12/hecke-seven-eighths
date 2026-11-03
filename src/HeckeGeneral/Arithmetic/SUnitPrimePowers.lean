import HeckeGeneral.Arithmetic.PrincipalIdealPowers
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DedekindDomain.SelmerGroup

/-!
# Actual S-units supported at one finite prime

The class number supplies a generator of the corresponding prime ideal power.
Its valuations are computed at every finite prime, so membership in the actual
Mathlib S-unit group follows without a principal-ideal-domain assumption.
These are the coordinate elements for the S-unit valuation lattice.

The native build and all-origin declaration audit are recorded in
`.cache/lattice-mask-audit.log` (138 declarations across six modules).
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

def primePowerGenerator (v : HeightOneSpectrum (𝓞 K)) : 𝓞 K :=
  (exists_nonzero_generator_classNumber_power K v.asIdeal v.ne_bot).choose

theorem primePowerGenerator_ne_zero (v : HeightOneSpectrum (𝓞 K)) :
    primePowerGenerator K v ≠ 0 :=
  (exists_nonzero_generator_classNumber_power K v.asIdeal v.ne_bot).choose_spec.1

theorem span_primePowerGenerator (v : HeightOneSpectrum (𝓞 K)) :
    Ideal.span {primePowerGenerator K v} = v.asIdeal ^ classNumber K :=
  (exists_nonzero_generator_classNumber_power K v.asIdeal v.ne_bot).choose_spec.2

/-- At its own prime the valuation exponent is exactly minus the class number. -/
theorem intValuation_primePowerGenerator_self (v : HeightOneSpectrum (𝓞 K)) :
    v.intValuation (primePowerGenerator K v) = WithZero.exp (-(classNumber K : ℤ)) := by
  rw [v.intValuation_eq_exp_neg_multiplicity (primePowerGenerator_ne_zero K v),
    span_primePowerGenerator, multiplicity_pow_self_of_prime v.prime]

/-- At every other prime its valuation is exactly one. -/
theorem intValuation_primePowerGenerator_ne (v w : HeightOneSpectrum (𝓞 K))
    (hw : w ≠ v) : w.intValuation (primePowerGenerator K v) = 1 := by
  have hnot : ¬w.asIdeal ∣ v.asIdeal := by
    intro h
    have heq : v.asIdeal = w.asIdeal :=
      (isMaximal v).eq_of_le w.isPrime.ne_top (Ideal.dvd_iff_le.mp h)
    exact hw (HeightOneSpectrum.ext_iff.mpr heq.symm)
  have hnotpow : ¬w.asIdeal ∣ v.asIdeal ^ classNumber K :=
    fun h => hnot (w.prime.dvd_of_dvd_pow h)
  rw [w.intValuation_eq_exp_neg_multiplicity (primePowerGenerator_ne_zero K v),
    span_primePowerGenerator, multiplicity_eq_zero_of_not_dvd hnotpow]
  simp

def primePowerUnit (v : HeightOneSpectrum (𝓞 K)) : Kˣ :=
  Units.mk0 (algebraMap (𝓞 K) K (primePowerGenerator K v))
    (by
      intro h
      apply primePowerGenerator_ne_zero K v
      apply IsFractionRing.injective (𝓞 K) K
      simpa only [map_zero] using h)

theorem valuation_primePowerUnit_self (v : HeightOneSpectrum (𝓞 K)) :
    v.valuation K (primePowerUnit K v : K) = WithZero.exp (-(classNumber K : ℤ)) := by
  change v.valuation K (algebraMap (𝓞 K) K (primePowerGenerator K v)) = _
  rw [valuation_of_algebraMap]
  exact intValuation_primePowerGenerator_self K v

theorem valuation_primePowerUnit_ne (v w : HeightOneSpectrum (𝓞 K))
    (hw : w ≠ v) : w.valuation K (primePowerUnit K v : K) = 1 := by
  change w.valuation K (algebraMap (𝓞 K) K (primePowerGenerator K v)) = _
  rw [valuation_of_algebraMap]
  exact intValuation_primePowerGenerator_ne K v w hw

/-- This is an element of Mathlib's existing S-unit subgroup. -/
def sUnitPrimePower (S : Set (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) : S.unit K :=
  ⟨primePowerUnit K v, fun w hw => valuation_primePowerUnit_ne K v w
    (fun h => hw (h.symm ▸ hv))⟩

/-- The actual multiplicative valuation map, with no quotient or real relaxation. -/
def sUnitValuations (S : Set (HeightOneSpectrum (𝓞 K))) :
    S.unit K →* (S → Multiplicative ℤ) where
  toFun u v := v.val.valuationOfNeZero (u : Kˣ)
  map_one' := by funext v; exact map_one _
  map_mul' u w := by funext v; exact map_mul _ _ _

theorem sUnitValuations_primePower (S : Set (HeightOneSpectrum (𝓞 K))) (v w : S) :
    sUnitValuations K S (sUnitPrimePower K S v.val v.property) w =
      if w = v then Multiplicative.ofAdd (-(classNumber K : ℤ)) else 1 := by
  apply WithZero.coe_injective
  change (w.val.valuationOfNeZero (primePowerUnit K v.val) :
    WithZero (Multiplicative ℤ)) = _
  rw [valuationOfNeZero_eq]
  by_cases h : w = v
  · subst w
    simpa only [ite_true, WithZero.exp_eq_coe_ofAdd] using
      valuation_primePowerUnit_self K v.val
  · have hvw : w.val ≠ v.val := fun h' => h (Subtype.ext h')
    simpa [h] using valuation_primePowerUnit_ne K v.val w.val hvw

end HeckeGeneral.Arithmetic
