import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAllocatedData

/-!
# The complete moving recipe of the computed literal child

The recipe is built from exactly the same appended moving factors,
remaining first deletion and complete second sixth root as the actual
allocated data. The full joint budget is the literal allowed-row
predicate of these data. The preceding physical-row theorem proves
that the original rows satisfy it; this file does not assume a final
support or a source-energy bound.

Clipping the two plain scales preserves every arithmetic field and
the same full budget. The recipe can therefore be supplied directly
to the full-kappa prime estimate for the chosen calibration.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedData

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ω ψ : HeckeCharacter K} {k : ℕ}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
variable (leftMultiplicity rightMultiplicity : ι → ℕ) (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) (m q : ℝ)
variable (inverse : IdealTest K) (index : Fin k → Fin parent.geometry.slotCount)
variable (rectangle : Bool) (firstSign : ℝ) (negative : Bool)

/-- No new moving element, sector or deletion ideal is selected. -/
def recipe : CompleteMovingRowRecipe A P R
    (data P R W B F parent oldMoving correction hcorr C p leftMultiplicity rightMultiplicity
      pattern ν remaining extra m q inverse index rectangle firstSign negative) where
  moving := (F.moving P R oldMoving).appendSecondFactor C p leftMultiplicity
    rightMultiplicity pattern
  correction := correction
  correction_mem _ := Or.inr hcorr
  sector _ := ν
  exterior _ _ hu := hu.1
  character _ _ _ := rfl
  remaining := remainingMaskIdeal A (remaining * extra) *
    exteriorMomentIdeal (secondSixthRootIdeal p leftMultiplicity rightMultiplicity)
  mask _ _ _ := rfl

@[simp] theorem recipe_moving :
    (recipe P R W B F parent oldMoving correction hcorr C p leftMultiplicity rightMultiplicity
      pattern ν remaining extra m q inverse index rectangle firstSign negative).moving =
      (F.moving P R oldMoving).appendSecondFactor C p leftMultiplicity rightMultiplicity pattern := rfl

@[simp] theorem recipe_remaining :
    (recipe P R W B F parent oldMoving correction hcorr C p leftMultiplicity rightMultiplicity
      pattern ν remaining extra m q inverse index rectangle firstSign negative).remaining =
      remainingMaskIdeal A (remaining * extra) *
        exteriorMomentIdeal (secondSixthRootIdeal p leftMultiplicity rightMultiplicity) := rfl

theorem recipe_fullJointBudget :
    (recipe P R W B F parent oldMoving correction hcorr C p leftMultiplicity rightMultiplicity
      pattern ν remaining extra m q inverse index rectangle firstSign negative).FullJointBudget
        d.base (m + q) := by
  intro ξ u hu
  exact hu.2

/-- The exact same arithmetic recipe applies to the clipped profiles.
The width here is still the original complete-deletion width. -/
def clippedRecipe (κ : ℝ) : CompleteMovingRowRecipe A P R (fun ξ =>
    clipPlainData
      (data P R W B F parent oldMoving correction hcorr C p leftMultiplicity rightMultiplicity
        pattern ν remaining extra m q inverse index rectangle firstSign negative ξ)
      (parameters d B rectangle m q κ) d.base (zero_lt_one.trans d.base_gt_one)) :=
  (recipe P R W B F parent oldMoving correction hcorr C p leftMultiplicity rightMultiplicity
    pattern ν remaining extra m q inverse index rectangle firstSign negative).clipped
      (parameters d B rectangle m q κ) d.base (zero_lt_one.trans d.base_gt_one)

theorem clippedRecipe_fullJointBudget (κ : ℝ) :
    (clippedRecipe P R W B F parent oldMoving correction hcorr C p leftMultiplicity
      rightMultiplicity pattern ν remaining extra m q inverse index rectangle firstSign
      negative κ).FullJointBudget d.base (m + q) := by
  intro ξ u hu
  exact hu.2

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedData

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedData.recipe
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedData.recipe_fullJointBudget
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllocatedData.clippedRecipe_fullJointBudget
