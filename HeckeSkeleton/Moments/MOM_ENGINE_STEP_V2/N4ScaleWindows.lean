import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceData

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N4: the original upper endpoints and their two explicit errors

The row and support cutoffs are fixed by the original nominal geometry.
They are not lower bounds on an individual row or on the support norm.
The complete second sixth root is charged in the support parameter, so
the original scale window is recorded at `q - rootLength`.

Paper: Section 4.8, lines 2883--2906 and 2927--2946.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]
variable {a : RealParameters} {Z step : ℝ}
variable (G : OriginalNominalGeometry (K := K) a Z step)

def rowParameter (rowError : ℝ) : ℝ :=
  G.skeleton.nominalRow + rowError

def supportParameter (supportError rootLength : ℝ) : ℝ :=
  G.skeleton.nominalSupport + supportError + rootLength

/-- The two original cutoff powers provide both endpoint inequalities.
The only hypotheses are the explicit nonnegative errors and their sum. -/
def endpointWindows (hZ : 1 < Z) (rowError supportError rootLength : ℝ)
    (hrow : 0 ≤ rowError) (hsupport : 0 ≤ supportError)
    (hsmall : 2 * (rowError + supportError) ≤ step) :
    G.ScaleWindows (rowParameter G rowError)
      (supportParameter G supportError rootLength - rootLength) where
  rowScale := Z ^ (G.frequencyCenter + rowError)
  supportScale := Z ^ (G.supportCenter + supportError)
  rowScale_pos := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  supportScale_pos := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  rowError := rowError
  supportError := supportError
  rowError_nonneg := hrow
  supportError_nonneg := hsupport
  error_small := hsmall
  row_lower := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  row_upper := le_rfl
  support_lower := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  support_upper := le_rfl
  row_parameter := by
    have hf : Z ^ (G.skeleton.g₂ + G.skeleton.V) =
        (Ideal.absNorm (gcd G.ideals.second.val G.ideals.secondOpposite.val) : ℝ) *
          (Ideal.absNorm G.ideals.nonunitPart.val : ℝ) := by
      change Z ^ (idealLogLength Z _ + idealLogLength Z _) = _
      rw [Real.rpow_add (zero_lt_one.trans hZ),
        rpow_idealLogLength Z hZ _
          (gcd_ne_zero_of_left (nonZeroDivisors.coe_ne_zero G.ideals.second)),
        rpow_idealLogLength Z hZ _
          (nonZeroDivisors.coe_ne_zero G.ideals.nonunitPart)]
    have he : rowParameter G rowError =
        (G.frequencyCenter + rowError) - (G.skeleton.g₂ + G.skeleton.V) := by
      dsimp only [rowParameter, OriginalNominalGeometry.frequencyCenter,
        NominalChildGeometry.nominalRow]
      ring
    rw [he, Real.rpow_sub (zero_lt_one.trans hZ), hf]
  support_parameter := by
    have hf : Z ^ (G.skeleton.t₂ + G.skeleton.V) =
        (Ideal.absNorm G.ideals.unitPart.val : ℝ) *
          (Ideal.absNorm G.ideals.nonunitPart.val : ℝ) := by
      change Z ^ (idealLogLength Z _ + idealLogLength Z _) = _
      rw [Real.rpow_add (zero_lt_one.trans hZ),
        rpow_idealLogLength Z hZ _ (nonZeroDivisors.coe_ne_zero G.ideals.unitPart),
        rpow_idealLogLength Z hZ _ (nonZeroDivisors.coe_ne_zero G.ideals.nonunitPart)]
    have he : supportParameter G supportError rootLength - rootLength =
        (G.supportCenter + supportError) + (G.skeleton.t₂ + G.skeleton.V) := by
      dsimp only [supportParameter, OriginalNominalGeometry.supportCenter,
        NominalChildGeometry.nominalSupport]
      ring
    rw [he, Real.rpow_add (zero_lt_one.trans hZ), hf]

theorem endpointWindows_error (hZ : 1 < Z) (rowError supportError rootLength : ℝ)
    (hrow : 0 ≤ rowError) (hsupport : 0 ≤ supportError)
    (hsmall : 2 * (rowError + supportError) ≤ step) :
    (endpointWindows G hZ rowError supportError rootLength hrow hsupport hsmall).error =
      rowError + supportError := by
  rfl

/-- Rewriting the two parameters changes only their equality proofs.
The actual cutoffs and errors remain literal fields of the same window. -/
def reparameterizeWindows {m q m' q' : ℝ} (W : G.ScaleWindows m q)
    (hm : m' = m) (hq : q' = q) : G.ScaleWindows m' q' where
  rowScale := W.rowScale
  supportScale := W.supportScale
  rowScale_pos := W.rowScale_pos
  supportScale_pos := W.supportScale_pos
  rowError := W.rowError
  supportError := W.supportError
  rowError_nonneg := W.rowError_nonneg
  supportError_nonneg := W.supportError_nonneg
  error_small := W.error_small
  row_lower := W.row_lower
  row_upper := W.row_upper
  support_lower := W.support_lower
  support_upper := W.support_upper
  row_parameter := by rw [hm]; exact W.row_parameter
  support_parameter := by rw [hq]; exact W.support_parameter

theorem parameter_width (rowError supportError rootLength : ℝ) :
    rowParameter G rowError + supportParameter G supportError rootLength =
      G.skeleton.nominalWidth + rootLength + (rowError + supportError) := by
  dsimp only [rowParameter, supportParameter, NominalChildGeometry.nominalWidth]
  ring

variable {c : TargetContext K} (p : SourceParameters c)

theorem source_errors_small :
    2 * (12 * p.loss + 4 * p.loss) ≤ recipeInductionSigma c := by
  linarith [p.loss_small, p.loss_pos]

theorem source_errors_le_half_step :
    12 * p.loss + 4 * p.loss ≤ recipeInductionSigma c / 2 := by
  linarith [source_errors_small p]

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.endpointWindows
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.parameter_width
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.source_errors_small
