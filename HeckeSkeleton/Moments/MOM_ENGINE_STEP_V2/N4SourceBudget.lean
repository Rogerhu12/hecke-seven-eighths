import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FullSecondDeletionSupport

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N4: support and joint budgets from the original numerical windows

The complete remaining mask and sixth root are retained. These two
unchanged generic constructors use only calibration data and merged
base arithmetic. The canonical source file separately proves their
row/product premises from the actual packet trace.

Paper: Section 4.8, lines 2883--2906 and 2927--2946.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

/-- The three original supports are charged together, before adjoining
the complete sixth root. No product of separate upper windows is used. -/
theorem fullMaskSupport_norm_of_original_product
    (moving : OriginalMovingFactors A P R)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (paid unit nonunit root : A.Exterior)
    (atoms : moving.SupportAtoms (ExteriorIdealEuler.mul paid root) unit nonunit remaining)
    (Z supportLength : ℝ) (hZ : 1 < Z)
    (hpaid : A.exteriorNorm paid * A.exteriorNorm unit * A.exteriorNorm nonunit ≤
      Z ^ supportLength) :
    idealNorm K (moving.fullMaskSupport remaining) ≤
      Z ^ (supportLength + idealLogLength Z root.val) := by
  have hroot : A.exteriorNorm root = Z ^ idealLogLength Z root.val :=
    (rpow_idealLogLength Z hZ root.val root.property.1).symm
  calc
    _ ≤ A.exteriorNorm (ExteriorIdealEuler.mul paid root) *
        A.exteriorNorm unit * A.exteriorNorm nonunit :=
      atoms.fullMaskSupport_norm_le
    _ = (A.exteriorNorm paid * A.exteriorNorm unit * A.exteriorNorm nonunit) *
        A.exteriorNorm root := by
      change ((Ideal.absNorm (paid.val * root.val) : ℝ) *
          (Ideal.absNorm unit.val : ℝ) * (Ideal.absNorm nonunit.val : ℝ)) =
        (((Ideal.absNorm paid.val : ℝ) * (Ideal.absNorm unit.val : ℝ) *
          (Ideal.absNorm nonunit.val : ℝ)) * (Ideal.absNorm root.val : ℝ))
      rw [map_mul, Nat.cast_mul]
      ring
    _ ≤ Z ^ supportLength * A.exteriorNorm root :=
      mul_le_mul_of_nonneg_right hpaid (Nat.cast_nonneg _)
    _ = _ := by
      rw [hroot, ← Real.rpow_add (zero_lt_one.trans hZ)]

variable {c : TargetContext K} {call : Call c} {H : Type} {k : ℕ}
variable {s : ActualAllocatedSource (Arithmetic.data c) EngineParameter H k}

/-- The only numerical inputs are the original row window and the
original product window. In particular neither completed budget is
assumed. The recipe, source, allowed rows, and profile predicates are
those of the same original calibration. -/
def sourceConditions_of_original_atoms
    (D : OriginalCalibration call s)
    (paid unit nonunit root : (Arithmetic.data c).Exterior)
    (atoms : D.recipe.moving.SupportAtoms
      (ExteriorIdealEuler.mul paid root) unit nonunit D.recipe.remaining)
    (rowLength supportLength : ℝ)
    (hm : D.calibration.parameters.m = rowLength)
    (hq : D.calibration.parameters.q =
      supportLength + idealLogLength s.base root.val)
    (hrow : ∀ h ∈ s.rows,
      idealNorm K (s.row h).momentIdeal ≤ s.base ^ rowLength)
    (hpaid : (Arithmetic.data c).exteriorNorm paid *
        (Arithmetic.data c).exteriorNorm unit * (Arithmetic.data c).exteriorNorm nonunit ≤
      s.base ^ supportLength)
    (allowed : ∀ ξ u, (D.calibration.data ξ).allowedRow u ↔
      ∃ h ∈ s.rows, (s.row h).momentIdeal = u)
    (timeIndependent : ∀ ξ, ProfileTimeIndependent (D.calibration.data ξ))
    (primeSupport : ∀ ξ, PrimeProfileSupport (D.calibration.data ξ)) :
    D.SourceConditions := by
  have hfull : idealNorm K (D.recipe.moving.fullMaskSupport D.recipe.remaining) ≤
      s.base ^ D.calibration.parameters.q := by
    rw [hq]
    exact fullMaskSupport_norm_of_original_product D.recipe.moving D.recipe.remaining
      paid unit nonunit root atoms s.base supportLength s.base_gt_one hpaid
  refine {
    allowed_exact := allowed
    support := ?_
    joint := ?_
    timeIndependent := timeIndependent
    primeSupport := primeSupport }
  · exact (D.recipe.moving.support_norm_le_fullMaskSupport D.recipe.remaining).trans hfull
  · intro ξ u hu
    obtain ⟨h, hh, rfl⟩ := (allowed ξ u).mp hu
    have hrow' : idealNorm K (s.row h).momentIdeal ≤ s.base ^ D.calibration.parameters.m := by
      rw [hm]
      exact hrow h hh
    exact (mul_le_mul hrow' hfull (idealNorm_pos K _).le
      (Real.rpow_nonneg (zero_lt_one.trans s.base_gt_one).le _)).trans_eq
        (Real.rpow_add (zero_lt_one.trans s.base_gt_one) _ _).symm

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.fullMaskSupport_norm_of_original_product
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.sourceConditions_of_original_atoms
