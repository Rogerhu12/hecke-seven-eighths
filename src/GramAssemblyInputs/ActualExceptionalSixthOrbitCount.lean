import ActualExceptionalSixthIdealCount
import HeckeGeneral.Analysis.SIntegerSixthPowerDecomposition

/-!
UNCOMPILED candidate. Transfer the exceptional-ideal count to the existing
actual nonzero S-integer quotient, retaining every sixth-unit sector.
The verified exterior-ideal/sector equivalence gives an actual injection;
neither an orbit parametrization nor a frequency-count bound is assumed.
The norm is the existing product norm, identified with the actual ideal
contraction by its proved theorem. This is a counting endpoint, not a
Poisson or weighted Gram estimate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Analysis.ActualGramExceptionalCountDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.ActualSIntegerMoments
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Original orbits and their original product norm; exceptional status
uses their genuine contraction, including all sixth-power descendants. -/
def ActualExceptionalOrbitCutoff (C : NonzeroIdeal K) (X : ℝ) :=
  {q : ActualSIntegerOrbit K S // actualSIntegerOrbitNorm K S q ≤ X ∧
    ExceptionalSixthIdeal K C (actualSIntegerOrbitIdeal K S q)}

/-- The existing arithmetic equivalence identifies the actual contracted
ideal, not just its norm or class. -/
theorem actualOrbitCoordinates_ideal (P : ProbeData K S) (q : ActualSIntegerOrbit K S) :
    ((exteriorIdealSectorsEquivActualOrbits K S P).symm q).1.val =
      actualSIntegerOrbitIdeal K S q := by
  let e := exteriorIdealSectorsEquivActualOrbits K S P
  have he : decomposedIdealSectorOrbit K S P (e.symm q) = q := e.apply_symm_apply q
  have h := decomposedIdealSectorOrbit_ideal K S P (e.symm q)
  rw [he] at h
  exact h.symm

theorem actualOrbitCoordinates_norm (P : ProbeData K S) (q : ActualSIntegerOrbit K S) :
    idealNorm K ((exteriorIdealSectorsEquivActualOrbits K S P).symm q).1.val =
      actualSIntegerOrbitNorm K S q := by
  rw [actualOrbitCoordinates_ideal K S P, actualSIntegerOrbitNorm_eq_absNorm_contraction]
  rfl

/-- The injection keeps the literal complete ideal and the full finite
unit-sector coordinate of each actual quotient orbit. -/
def actualExceptionalOrbitEmbedding (P : ProbeData K S) (C : NonzeroIdeal K)
    {X : ℝ} (hX : 0 ≤ X) :
    ActualExceptionalOrbitCutoff K S C X ↪
      ({J : NonzeroIdeal K // J ∈ exceptionalIdealCutoff K C X} × SixthUnitClasses K S) where
  toFun q :=
    (⟨((exteriorIdealSectorsEquivActualOrbits K S P).symm q.val).1.val, by
      apply (mem_exceptionalIdealCutoff K hX).mpr
      constructor
      · rw [actualOrbitCoordinates_norm K S P]
        exact q.property.1
      · rw [actualOrbitCoordinates_ideal K S P]
        exact q.property.2⟩,
      ((exteriorIdealSectorsEquivActualOrbits K S P).symm q.val).2)
  inj' q r h := by
    apply Subtype.ext
    apply (exteriorIdealSectorsEquivActualOrbits K S P).symm.injective
    have h1 := congrArg (fun x :
        {J : NonzeroIdeal K // J ∈ exceptionalIdealCutoff K C X} × SixthUnitClasses K S =>
          x.1.val) h
    have h2 := congrArg Prod.snd h
    exact Prod.ext (Subtype.ext h1) h2

theorem finite_actualExceptionalOrbitCutoff (P : ProbeData K S) (C : NonzeroIdeal K)
    {X : ℝ} (hX : 0 ≤ X) : Finite (ActualExceptionalOrbitCutoff K S C X) :=
  Finite.of_injective (actualExceptionalOrbitEmbedding K S P C hX)
    (actualExceptionalOrbitEmbedding K S P C hX).injective

theorem actualExceptionalOrbitCutoff_card_le (P : ProbeData K S) (C : NonzeroIdeal K)
    {X : ℝ} (hX : 0 ≤ X) :
    Nat.card (ActualExceptionalOrbitCutoff K S C X) ≤
      Nat.card (SixthUnitClasses K S) * (exceptionalIdealCutoff K C X).card := by
  have h := Nat.card_le_card_of_injective (actualExceptionalOrbitEmbedding K S P C hX)
    (actualExceptionalOrbitEmbedding K S P C hX).injective
  simpa only [Nat.card_prod, Nat.card_eq_finsetCard, Nat.mul_comm] using h

/-- All actual exceptional frequency orbits are counted. The constant
depends only on K, S and epsilon, and precedes even the probe data P. -/
theorem actualExceptionalOrbitCutoff_small_power_count {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ (P : ProbeData K S) (C : NonzeroIdeal K) (X : ℝ), 1 ≤ X →
      (Nat.card (ActualExceptionalOrbitCutoff K S C X) : ℝ) ≤
        A * idealNorm K C ^ ε * X ^ (1 / 6 : ℝ) := by
  obtain ⟨B, hB, hcount⟩ := exceptionalIdealCutoff_small_power_count K hε
  have hM : (0 : ℝ) < Nat.card (SixthUnitClasses K S) := by
    exact_mod_cast Nat.card_pos (α := SixthUnitClasses K S)
  refine ⟨(Nat.card (SixthUnitClasses K S) : ℝ) * B, mul_pos hM hB,
    fun P C X hX => ?_⟩
  have hc : (Nat.card (ActualExceptionalOrbitCutoff K S C X) : ℝ) ≤
      (Nat.card (SixthUnitClasses K S) : ℝ) * ((exceptionalIdealCutoff K C X).card : ℝ) := by
    exact_mod_cast actualExceptionalOrbitCutoff_card_le K S P C (zero_le_one.trans hX)
  apply hc.trans
  calc
    _ ≤ (Nat.card (SixthUnitClasses K S) : ℝ) *
        (B * idealNorm K C ^ ε * X ^ (1 / 6 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hcount C X hX) hM.le
    _ = _ := by ring

end HeckeGeneral.Analysis.ActualGramExceptionalCountDraft
