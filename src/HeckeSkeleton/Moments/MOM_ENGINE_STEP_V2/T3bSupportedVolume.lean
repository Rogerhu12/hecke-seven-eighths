import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ArithmeticData
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ActualAnnularVolume
import HeckeSkeleton.Moments.MOM_PRIME.ExceptionalNormReduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalSupportedVolume

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# T3b: fixed exceptional characters and actual supported volume

The catalogue is selected from the original target before the call.
It contains every permitted plain background times either orientation
of the original finite theta character.  Its supported single-series
estimates come from the actual annular contour theorem.  The resulting
source bounds preserve the same allocated source and all four scales;
the nonpositive lower-length case retains the absolute alternative.

This file supplies the analytic primitive.  It does not assert the
raw-leaf dictionary or the final exceptional summation task.
-/

noncomputable section
open scoped Classical NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open EngineStep EngineInduction MOM_PRIME

variable {K : Type} [Field K] [NumberField K]

abbrev CharacterIndex (c : TargetContext K) :=
  Fin 3 × Bool ×
    {theta : HeckeCharacter K //
      theta ∈ Expansion.Project.canonicalDetectorTheta K (targetCharacter K c)}

def background (c : TargetContext K) (j : Fin 3) : HeckeCharacter K :=
  if j = 0 then 1 else if j = 1 then targetCharacter K c else (targetCharacter K c)⁻¹

def character (c : TargetContext K) (j : CharacterIndex c) : HeckeCharacter K :=
  background c j.1 * (if j.2.1 then j.2.2.val⁻¹ else j.2.2.val)

theorem background_radial_zero (c : TargetContext K) (j : Fin 3) :
    heckeRadialParameter K (normNormalizationPlace K) (background c j) = 0 := by
  unfold background
  split_ifs
  · simp
  · exact targetCharacter_radial_zero K c
  · rw [heckeRadialParameter_inv, targetCharacter_radial_zero K c, neg_zero]

theorem character_normReduced (c : TargetContext K) (j : CharacterIndex c) :
    ExceptionalNormReduced K (character c j) := by
  have htheta : FiniteOrder j.2.2.val :=
    Expansion.Project.canonicalDetectorTheta_finiteOrder K (targetCharacter K c)
      j.2.2.val j.2.2.property
  have hfinite : FiniteOrder (if j.2.1 then j.2.2.val⁻¹ else j.2.2.val) := by
    cases j.2.1 <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
      first | exact htheta | exact htheta.inv
  exact exceptionalNormReduced_of_radial_zero K (normNormalizationPlace K) _
    (radial_zero_mul_finiteOrder K (normNormalizationPlace K) _ _
      (background_radial_zero c j.1) hfinite)

/-- The catalogue covers the original plain background, including the
conjugated theta orientation.  The theta itself is not replaced. -/
theorem character_covers (c : TargetContext K) (omega theta : HeckeCharacter K)
    (homega : omega = 1 ∨ omega = targetCharacter K c ∨ omega = (targetCharacter K c)⁻¹)
    (htheta : theta ∈ Expansion.Project.canonicalDetectorTheta K (targetCharacter K c))
    (conjugate : Bool) :
    ∃ j : CharacterIndex c,
      character c j = omega * (if conjugate then theta⁻¹ else theta) := by
  rcases homega with h | h | h
  · refine ⟨(0, conjugate, ⟨theta, htheta⟩), ?_⟩
    simp [character, background, h]
  · refine ⟨(1, conjugate, ⟨theta, htheta⟩), ?_⟩
    simp [character, background, h]
  · refine ⟨(2, conjugate, ⟨theta, htheta⟩), ?_⟩
    simp [character, background, h]

/-- Actual analytic remainder on the original positive support window.
The principal residue remains the actual Hecke residue in all sectors. -/
theorem exists_remainder (c : TargetContext K) (lower upper : ℝ)
    (hlower : 0 < lower) (hinterval : lower ≤ upper) :
    ∃ remainder : CharacterIndex c → Seminorm ℂ (SchwartzMap ℝ ℂ),
      (∀ j, Continuous (remainder j)) ∧
      ∀ j (phi : SchwartzMap ℝ ℂ) (X : ℝ), 0 < X →
        tsupport phi ⊆ Set.Icc lower upper →
        ‖(∑' I : Ideal (𝓞 K), CanonicalExceptionalVolume.coefficient (character c j) I *
            phi ((Ideal.absNorm I : ℝ) / X)) -
          (X : ℂ) * actualAnnularDensity (character c j) phi‖ ≤ remainder j phi := by
  have hchoice (j : CharacterIndex c) :=
    exists_actualAnnularVolumeSeminorm (isComplex_of_family K c)
      (character c j) (character_normReduced c j) lower upper hlower hinterval
  choose remainder hcontinuous hbound using hchoice
  refine ⟨remainder, hcontinuous, ?_⟩
  intro j phi X hX hsupport
  exact hbound j phi hsupport X hX

/-- Fixed orders and a fixed scalar for the whole allocated exceptional
source.  These choices precede every moving source, mask and scale. -/
theorem exists_source_bounds (c : TargetContext K)
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (lower upper : ℝ) (hlower : 0 < lower) (hinterval : lower ≤ upper)
    (loss maskExponent : ℝ) (hloss : 0 < loss) (hmask : 0 ≤ maskExponent) :
    ∃ orders : Finset (ℕ × ℕ), (0, 0) ∈ orders ∧
      ∃ degree : ℕ, ∃ coefficient : ℝ, 0 < coefficient ∧
      ∀ (j : CharacterIndex c) (phi₁ phi₂ : SchwartzMap ℝ ℂ),
        tsupport phi₁ ⊆ Set.Icc lower upper →
        tsupport phi₂ ⊆ Set.Icc lower upper →
        ∀ amplitude : ℝ, 0 ≤ amplitude →
        orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) phi₁ ≤ amplitude →
        orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) phi₂ ≤ amplitude →
        (∀ {g h : (Arithmetic.data c).R} {slots : ℕ}
          (source : AllocatedExceptionalSource (V := V) (σ := Arithmetic.embedding c)
            (CanonicalExceptionalVolume.coefficient (character c j)) phi₁ phi₂ g h slots),
          ‖source.ordinaryValue‖ ≤ coefficient * amplitude ^ 2 * source.rawMass ∧
          ‖source.value‖ ≤ coefficient * amplitude ^ 2 * source.rawMass) ∧
        (∀ base : ℝ, 1 ≤ base → ∀ {g h : (Arithmetic.data c).R} {slots : ℕ}
          (source : AllocatedExceptionalSource (V := V) (σ := Arithmetic.embedding c)
            (CanonicalExceptionalVolume.coefficient (character c j)) phi₁ phi₂ g h slots),
          source.mask ≠ ⊥ → (Ideal.absNorm source.mask : ℝ) ≤ base ^ maskExponent →
          ∀ lowerLength : ℝ, base ^ lowerLength ≤ source.lower →
          ‖source.value‖ ≤ coefficient * amplitude ^ 2 * base ^ loss *
            (1 + ‖source.time‖) ^ degree * source.rawMass * base ^ (-max lowerLength 0)) := by
  obtain ⟨remainder, hcontinuous, hvolume⟩ :=
    exists_remainder c lower upper hlower hinterval
  exact CanonicalExceptionalVolume.exists_original_source_bounds_supported
    (A := Arithmetic.data c) (V := V) (σ := Arithmetic.embedding c)
    (character c) (fun j => actualAnnularDensity (character c j)) remainder
    hcontinuous (Set.Icc lower upper) hvolume isCompact_Icc
    (fun x hx => hlower.trans_le hx.1) loss maskExponent hloss hmask

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.character_normReduced
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.exists_remainder
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.exists_source_bounds
