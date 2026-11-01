import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFrameLengths

/-!
# A capacity scale error computed for every original rectangle

All rectangles receive their actual side normalization before source
activity is tested. An absent ordinary comparison can have arbitrary
positive comparison scales. Its raw degree is still bounded by the
explicit logarithm of its actual scale product; this possibly large
error is retained in its unused capacity cost.

On a rectangle satisfying the original two-extraction norm window,
the computed error equals the original small error exactly. Thus the
same selected normalization and child use the established small-error
mass formula. No inactive source, radius, calibration or slot is
replaced.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralRectangles.Atoms

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)

/-- This is a value computed from the actual original scales, not an
assumed raw-degree or capacity estimate. -/
def computedRawError (degree error : ℝ) (r : Bool) : ℝ :=
  max error (Real.logb d.base (d.scaleProduct r) - degree)

theorem computedRawError_nonneg (degree error : ℝ) (r : Bool) (herr : 0 ≤ error) :
    0 ≤ d.computedRawError degree error r := herr.trans (le_max_left _ _)

theorem scaleProduct_le_computedRawError (degree error : ℝ) (r : Bool) :
    d.scaleProduct r ≤ d.base ^ (degree + d.computedRawError degree error r) := by
  have hl : Real.logb d.base (d.scaleProduct r) ≤
      degree + d.computedRawError degree error r := by
    have h := le_max_right error (Real.logb d.base (d.scaleProduct r) - degree)
    change _ ≤ degree + max error (Real.logb d.base (d.scaleProduct r) - degree)
    linarith
  calc
    _ = d.base ^ Real.logb d.base (d.scaleProduct r) :=
      (Real.rpow_logb (zero_lt_one.trans d.base_gt_one) d.base_gt_one.ne'
        (d.scaleProduct_pos r)).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le d.base_gt_one.le hl

theorem computedRawError_eq_of_scaleProduct_le (degree error : ℝ) (r : Bool)
    (hproduct : d.scaleProduct r ≤ d.base ^ (degree + error)) :
    d.computedRawError degree error r = error := by
  have hpow : d.base ^ Real.logb d.base (d.scaleProduct r) ≤
      d.base ^ (degree + error) := by
    rw [Real.rpow_logb (zero_lt_one.trans d.base_gt_one) d.base_gt_one.ne'
      (d.scaleProduct_pos r)]
    exact hproduct
  have hl := (Real.rpow_le_rpow_left_iff d.base_gt_one).mp hpow
  apply max_eq_left
  linarith

theorem computedRawError_eq_of_two_norms {a : RealParameters} {step : ℝ}
    (G : OriginalNominalGeometry (K := K) a d.base step)
    (annulus : ℝ) (cap : ℕ) (error : ℝ) (r : Bool)
    (hbound : d.scaleProduct r *
      ((Ideal.absNorm G.literalFirstExtraction.val : ℝ) *
        (Ideal.absNorm G.ideals.second.val : ℝ)) ≤
      annulus ^ (2 * cap) * d.base ^ (a.n₁ + a.n₂ + a.z))
    (hthreshold : annulus ^ (2 * cap) ≤ d.base ^ error) :
    d.computedRawError G.skeleton.rawDegree error r = error :=
  d.computedRawError_eq_of_scaleProduct_le G.skeleton.rawDegree error r
    (d.scaleProduct_le_originalRawDegree G annulus cap error r hbound hthreshold)

section Frame

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {H J : Type*} [Fintype J] [DecidableEq J]
variable {ω ψ : HeckeCharacter K}
variable (R : ActualSecondCorrelationRows A σ H J)
variable (side : SecondColumnSide) (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
variable (ideal : AllocationColumn K k → A.Exterior)
variable (hideal : ∀ i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots,
  (ideal i).val = allocationColumnIdeal i)
variable (firstSign : ℝ) (rectangle : Bool) (L : Ideal (𝓞 K))
variable (selection : primeSupport L → Finset (Fin (k + 2)))
variable (hne : (pairedAllocatedColumns L selection d.plain₁ d.plain₂ d.slots
  id id HeightOneSpectrum.asIdeal).Nonempty)

local notation "f" =>
  (d.factors R side χ ideal hideal firstSign rectangle).frame C L selection hne

variable (D : ((d.factors R side χ ideal hideal firstSign rectangle).frame C L selection hne).source.Calibration
  (σ := σ) ω ψ)
variable (parent : MomentData K ω ψ) (a : RealParameters) (step : ℝ)
variable (G : OriginalNominalGeometry (K := K) a
  ((d.factors R side χ ideal hideal firstSign rectangle).frame C L selection hne).source.base step)
variable {centered : Bool} {Y₁ Y₂ floor padding : ℝ}
variable (domain : PairedEngineDomain centered parent a
  ((d.factors R side χ ideal hideal firstSign rectangle).frame C L selection hne).source.base
  Y₁ Y₂ floor padding)
variable (slots : OriginalSlotDictionary parent d.length)
variable (direct : G.tag = .direct → parent.geometry.slotCount = 0)
variable (cutoff rootLength : ℝ) (hcutoff : 0 ≤ cutoff) (hsmall : 2 * cutoff ≤ step)
variable (hparameters : D.parameters = CanonicalLiteralAllocatedData.parameters d
  ((d.factors R side χ ideal hideal firstSign rectangle).frame C L selection hne).allocation
  rectangle (G.literalRowParameter cutoff) (G.literalSupportParameter rootLength) a.κ)
variable (error : ℝ) (herr : 0 ≤ error)

/-- The actual original slot and endpoint data construct this binding
on every rectangle, including one whose source is identically zero. -/
def factorsOriginalSixthLengthsAll :
    D.OriginalSixthLengthBinding parent a step G rootLength := by
  have hproduct : (f).source.scale₁ * (f).source.scale₂ * (f).source.base ^ (f).source.beforeLength ≤
      (f).source.base ^ (G.skeleton.rawDegree +
        d.computedRawError G.skeleton.rawDegree error rectangle) := by
    have he := d.factors_source_scaleProduct (C := C) R side χ ideal hideal firstSign rectangle
      L selection hne
    cases side <;>
      exact he.trans_le (d.scaleProduct_le_computedRawError G.skeleton.rawDegree error rectangle)
  have hκ : D.parameters.κ = a.κ := by
    rw [hparameters]
    rfl
  have hm : D.parameters.m = G.literalRowParameter cutoff := by
    rw [hparameters]
    rfl
  have hq : D.parameters.q = G.literalSupportParameter rootLength := by
    rw [hparameters]
    rfl
  refine
    { slots := d.factorsOriginalSlots (C := C) R side χ ideal hideal firstSign rectangle L selection hne
        parent slots
      parent_z := domain.total_length
      parent_region := ⟨domain.kappa_lower, domain.kappa_upper, domain.capacity⟩
      kappa := hκ
      direct_slots := ?_
      scales := (G.literalEndpointWindows (f).source.base_gt_one cutoff rootLength hcutoff hsmall)
        .reparameterize hm (congrArg (fun y : ℝ => y - rootLength) hq)
      rawScaleError := d.computedRawError G.skeleton.rawDegree error rectangle
      rawScaleError_nonneg := d.computedRawError_nonneg G.skeleton.rawDegree error rectangle herr
      original_scale_product := hproduct }
  intro hd
  have hc : k ≤ parent.geometry.slotCount := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective slots.index slots.index.injective
  rw [direct hd] at hc
  exact Nat.eq_zero_of_le_zero hc

@[simp] theorem factorsOriginalSixthLengthsAll_rawError :
    (d.factorsOriginalSixthLengthsAll R side χ ideal hideal firstSign rectangle L selection hne
      D parent a step G domain slots direct cutoff rootLength hcutoff hsmall hparameters error herr)
      .rawScaleError = d.computedRawError G.skeleton.rawDegree error rectangle := rfl

@[simp] theorem factorsOriginalSixthLengthsAll_error :
    (d.factorsOriginalSixthLengthsAll R side χ ideal hideal firstSign rectangle L selection hne
      D parent a step G domain slots direct cutoff rootLength hcutoff hsmall hparameters error herr)
      .scales.error = cutoff := by
  simp only [factorsOriginalSixthLengthsAll, OriginalNominalGeometry.ScaleWindows.error,
    OriginalNominalGeometry.ScaleWindows.reparameterize,
    OriginalNominalGeometry.literalEndpointWindows, add_zero]

/-- With the original norm windows, the whole binding is identical
to the earlier small-error binding, including its same scale endpoints
and slot embedding. The proof fields agree by proof irrelevance. -/
theorem factorsOriginalSixthLengthsAll_eq
    (annulus : ℝ) (cap : ℕ)
    (hbound : d.scaleProduct rectangle *
      ((Ideal.absNorm G.literalFirstExtraction.val : ℝ) *
        (Ideal.absNorm G.ideals.second.val : ℝ)) ≤
      annulus ^ (2 * cap) * (f).source.base ^ (a.n₁ + a.n₂ + a.z))
    (hthreshold : annulus ^ (2 * cap) ≤ (f).source.base ^ error) :
    d.factorsOriginalSixthLengthsAll R side χ ideal hideal firstSign rectangle L selection hne
      D parent a step G domain slots direct cutoff rootLength hcutoff hsmall hparameters error herr =
    d.factorsOriginalSixthLengths R side χ ideal hideal firstSign rectangle L selection hne
      D parent a step G domain slots direct cutoff rootLength hcutoff hsmall hparameters
      annulus cap error herr hbound hthreshold := by
  have he : d.computedRawError G.skeleton.rawDegree error rectangle = error := by
    cases side <;> exact d.computedRawError_eq_of_two_norms G annulus cap error rectangle
      hbound hthreshold
  simp only [factorsOriginalSixthLengthsAll, factorsOriginalSixthLengths, he]

end Frame
end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.scaleProduct_le_computedRawError
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.computedRawError_eq_of_two_norms
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.factorsOriginalSixthLengthsAll
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.factorsOriginalSixthLengthsAll_eq
