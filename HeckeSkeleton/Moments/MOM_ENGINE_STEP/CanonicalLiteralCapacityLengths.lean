import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralCoveredScaleProduct
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalExceptionalPlainWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SixthDeletionCapacity

/-!+# The actual upper endpoints in the capacity length dictionary

The second source uses the upper endpoint of the proved physical row
window and the already paid original support majorant. Their two
parameters are computed here from the same original geometry and its
actual frequency radicals. There is no lower bound on an individual
row or an assumption that the support majorant is the support norm.

The cutoff is an explicit row error; the full sixth root is an explicit
support increment. The scale product derived from the two original
occurrence extractions is rewritten into the same raw-degree ledger.
The atom table, allocation and future capacity choice stay unchanged.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

/-- The original annulus charge is absorbed at one fixed threshold,
before either original atlas, scale, allocation or Fourier variable. -/
theorem literal_scale_product_threshold (cap : ℕ) (annulus error : ℝ)
    (herror : 0 < error) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z → annulus ^ (2 * cap) ≤ Z ^ error := by
  have hevent := (_root_.tendsto_rpow_atTop herror).eventually
    (Filter.eventually_ge_atTop (annulus ^ (2 * cap)))
  obtain ⟨Z₁, hZ₁⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨max Z₁ 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro Z hZ
  exact hZ₁ Z ((le_max_left _ _).trans hZ)

namespace OriginalNominalGeometry

variable {a : RealParameters} {Z step : ℝ}
variable (G : OriginalNominalGeometry (K := K) a Z step)

/-- The same original first ideal times the actual removed pool power.
For main and direct branches the latter is the unit ideal. -/
def literalFirstExtraction : HeckeGeneral.Analysis.NonzeroIdeal K :=
  G.ideals.first * G.tag.extractionIdeal

theorem literalFirstExtraction_length :
    idealLogLength Z G.literalFirstExtraction.val = G.skeleton.c + G.skeleton.w := by
  have h₁ : (Ideal.absNorm G.ideals.first.val : ℝ) ≠ 0 := by
    exact_mod_cast (fun h => nonZeroDivisors.coe_ne_zero G.ideals.first
      (Ideal.absNorm_eq_zero_iff.mp h))
  have h₂ : (Ideal.absNorm G.tag.extractionIdeal.val : ℝ) ≠ 0 := by
    exact_mod_cast (fun h => nonZeroDivisors.coe_ne_zero G.tag.extractionIdeal
      (Ideal.absNorm_eq_zero_iff.mp h))
  have he : idealLogLength Z G.literalFirstExtraction.val =
      idealLogLength Z G.ideals.first.val + idealLogLength Z G.tag.extractionIdeal.val := by
    change idealLogLength Z (G.ideals.first.val * G.tag.extractionIdeal.val) = _
    simp only [idealLogLength, map_mul, Nat.cast_mul, Real.log_mul h₁ h₂]
    ring
  rw [he, G.tag.extractionIdeal_length Z]
  rfl

theorem literalRawDegree :
    G.skeleton.rawDegree = a.n₁ + a.n₂ + a.z -
      idealLogLength Z G.literalFirstExtraction.val -
        idealLogLength Z G.ideals.second.val := by
  rw [G.literalFirstExtraction_length]
  change G.skeleton.A - G.skeleton.c - G.skeleton.w - G.skeleton.c₂ =
    G.skeleton.A - (G.skeleton.c + G.skeleton.w) - G.skeleton.c₂
  ring

/-- The raw row parameter of the chosen physical upper endpoint. -/
def literalRowParameter (cutoff : ℝ) : ℝ :=
  G.frequencyCenter + cutoff - (G.skeleton.g₂ + G.skeleton.V)

/-- The fixed support majorant includes the entire second sixth root. -/
def literalSupportParameter (rootLength : ℝ) : ℝ :=
  G.supportCenter + (G.skeleton.t₂ + G.skeleton.V) + rootLength

/-- All four endpoint inequalities and the exact norm extractions are
proved internally. Only the original cutoff size enters the error. -/
def literalEndpointWindows (hZ : 1 < Z) (cutoff rootLength : ℝ)
    (hcutoff : 0 ≤ cutoff) (hsmall : 2 * cutoff ≤ step) :
    G.ScaleWindows (G.literalRowParameter cutoff)
      (G.literalSupportParameter rootLength - rootLength) where
  rowScale := Z ^ (G.frequencyCenter + cutoff)
  supportScale := Z ^ G.supportCenter
  rowScale_pos := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  supportScale_pos := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  rowError := cutoff
  supportError := 0
  rowError_nonneg := hcutoff
  supportError_nonneg := le_rfl
  error_small := by simpa only [add_zero] using hsmall
  row_lower := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  row_upper := le_rfl
  support_lower := by simp only [sub_zero, le_refl]
  support_upper := by simp only [add_zero, le_refl]
  row_parameter := by
    have hf : Z ^ (G.skeleton.g₂ + G.skeleton.V) =
        (Ideal.absNorm (gcd G.ideals.second.val G.ideals.secondOpposite.val) : ℝ) *
          (Ideal.absNorm G.ideals.nonunitPart.val : ℝ) := by
      change Z ^ (idealLogLength Z _ + idealLogLength Z _) = _
      rw [Real.rpow_add (zero_lt_one.trans hZ), rpow_idealLogLength Z hZ _
        (gcd_ne_zero_of_left (nonZeroDivisors.coe_ne_zero G.ideals.second)),
        rpow_idealLogLength Z hZ _ (nonZeroDivisors.coe_ne_zero G.ideals.nonunitPart)]
    rw [literalRowParameter, Real.rpow_sub (zero_lt_one.trans hZ), hf]
  support_parameter := by
    have hf : Z ^ (G.skeleton.t₂ + G.skeleton.V) =
        (Ideal.absNorm G.ideals.unitPart.val : ℝ) *
          (Ideal.absNorm G.ideals.nonunitPart.val : ℝ) := by
      change Z ^ (idealLogLength Z _ + idealLogLength Z _) = _
      rw [Real.rpow_add (zero_lt_one.trans hZ),
        rpow_idealLogLength Z hZ _ (nonZeroDivisors.coe_ne_zero G.ideals.unitPart),
        rpow_idealLogLength Z hZ _ (nonZeroDivisors.coe_ne_zero G.ideals.nonunitPart)]
    simp only [literalSupportParameter, add_sub_cancel_right]
    rw [Real.rpow_add (zero_lt_one.trans hZ), hf]

@[simp] theorem literalEndpointWindows_error (hZ : 1 < Z) (cutoff rootLength : ℝ)
    (hcutoff : 0 ≤ cutoff) (hsmall : 2 * cutoff ≤ step) :
    (G.literalEndpointWindows hZ cutoff rootLength hcutoff hsmall).error = cutoff := by
  simp only [ScaleWindows.error, literalEndpointWindows, add_zero]

/-- The actual joint budget is the nominal width plus the two explicit
costs used by the physical-cutoff and full-deletion constructions. -/
theorem literalParameters_width (cutoff rootLength : ℝ) :
    G.literalRowParameter cutoff + G.literalSupportParameter rootLength =
      G.skeleton.nominalWidth + rootLength + cutoff := by
  dsimp only [literalRowParameter, literalSupportParameter, frequencyCenter,
    supportCenter, NominalChildGeometry.nominalWidth,
    NominalChildGeometry.nominalRow, NominalChildGeometry.nominalSupport]
  ring

end OriginalNominalGeometry

namespace CanonicalLiteralRectangles.Atoms

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable {a : RealParameters} {step : ℝ}
variable (G : OriginalNominalGeometry (K := K) a d.base step)

/-- The two actual norm factors calculated by the original-table and
covered-leaf theorems are precisely the raw-degree factors. -/
theorem scaleProduct_le_originalRawDegree
    (B : ℝ) (cap : ℕ) (error : ℝ) (rectangle : Bool)
    (hbound : d.scaleProduct rectangle *
      ((Ideal.absNorm G.literalFirstExtraction.val : ℝ) *
        (Ideal.absNorm G.ideals.second.val : ℝ)) ≤
      B ^ (2 * cap) * d.base ^ (a.n₁ + a.n₂ + a.z))
    (herror : B ^ (2 * cap) ≤ d.base ^ error) :
    d.scaleProduct rectangle ≤ d.base ^ (G.skeleton.rawDegree + error) := by
  rw [G.literalRawDegree]
  exact d.scaleProduct_le_power_of_two_norms G.literalFirstExtraction.val
    G.ideals.second.val (nonZeroDivisors.coe_ne_zero _) (nonZeroDivisors.coe_ne_zero _)
    B cap (a.n₁ + a.n₂ + a.z) error rectangle hbound herror

end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.literalFirstExtraction_length
#print axioms HeckeSkeleton.Moments.EngineStep.literal_scale_product_threshold
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.literalEndpointWindows
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.literalParameters_width
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.scaleProduct_le_originalRawDegree
