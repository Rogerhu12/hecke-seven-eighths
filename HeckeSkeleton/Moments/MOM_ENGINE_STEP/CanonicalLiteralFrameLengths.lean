import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralCapacityLengths
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAllocatedData

/-!
# Original length products construct the actual frame's capacity binding

The actual frame keeps its original allocation and slot dictionary.
The original two extraction calculations supply the two norm factors
in its scale product; the fixed annulus threshold converts their
already computed product bound into the raw degree. The calibration's
parameter identity is literal for the constructed Fourier data.

The chosen row endpoint pays the two appearances of the original
active-column loss and the physical cutoff. It is never asserted to
be a lower window for every individual frequency. All endpoints and
the complete sixth-root support increment are constructed internally.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

namespace OriginalNominalGeometry

variable {a : RealParameters} {Z step : ℝ}
variable (G : OriginalNominalGeometry (K := K) a Z step)

/-- The original active column upper window enters the dual frequency
twice. Its cost is an explicit row error of this same geometry. -/
theorem literalParameters_secondWidth (columnLoss cutoff rootLength : ℝ) :
    G.literalRowParameter (2 * columnLoss + cutoff) + G.literalSupportParameter rootLength =
      secondCommonChildWidth Z
        (G.skeleton.A - G.skeleton.c - G.skeleton.w + columnLoss)
        (G.skeleton.q + G.skeleton.R + G.skeleton.E) G.skeleton.wo
        G.skeleton.Krow G.skeleton.g G.ideals.second.val G.ideals.secondOpposite.val
        G.ideals.unitPart.val G.ideals.nonunitPart.val + rootLength + cutoff := by
  dsimp only [literalRowParameter, literalSupportParameter, frequencyCenter,
    supportCenter, secondCommonChildWidth, skeleton]
  ring

namespace ScaleWindows

variable {G}

/-- Parameter identities transport only the two defining equations.
The actual endpoint values and their explicit errors stay literal. -/
def reparameterize {m q m' q' : ℝ} (W : G.ScaleWindows m q)
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

@[simp] theorem reparameterize_error {m q m' q' : ℝ} (W : G.ScaleWindows m q)
    (hm : m' = m) (hq : q' = q) : (W.reparameterize hm hq).error = W.error := rfl

end ScaleWindows

end OriginalNominalGeometry

namespace CanonicalLiteralRectangles.Atoms

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {H J : Type*} [Fintype J] [DecidableEq J]
variable {ω ψ : HeckeCharacter K} {k : ℕ}
variable (d : CanonicalLiteralRectangles.Atoms (K := K) k)
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

/-- Neither the negative right phase nor the actual allocation changes
the original pre-allocation occurrence dictionary. -/
def factorsOriginalSlots (parent : MomentData K ω ψ)
    (slots : OriginalSlotDictionary parent d.length) :
    OriginalSlotDictionary parent f.source.length := by
  cases side <;> exact slots

/-- The full-kappa prime input uses the same original mesh bound on
the retained source slots, before any capacity deletion. -/
theorem factors_childLength_le (parent : MomentData K ω ψ)
    (slots : OriginalSlotDictionary parent d.length) (mesh : ℝ)
    (hfit : parent.geometry.fitsMesh mesh) (i : Fin f.source.allocation.keep.card) :
    f.source.childLength i ≤ mesh := by
  exact (d.factorsOriginalSlots (C := C) R side χ ideal hideal firstSign rectangle L selection hne
    parent slots).fitsMesh hfit (SlotRestriction.index f.source.allocation.keep i)

variable (D : ((d.factors R side χ ideal hideal firstSign rectangle).frame C L selection hne).source.Calibration
  (σ := σ) ω ψ)
variable (parent : MomentData K ω ψ) (a : RealParameters) (step : ℝ)
variable (G : OriginalNominalGeometry (K := K) a
  ((d.factors R side χ ideal hideal firstSign rectangle).frame C L selection hne).source.base step)

/-- This is the length input of the already constructed actual frame.
`hbound` is the exact two-extraction norm-product result, before taking
logarithms; it is produced by the original direct/main/pool scale
theorems and `literalLeftAtoms_secondScale`/its right counterpart.
No raw-degree, width, final-child or capacity bound is assumed. -/
def factorsOriginalSixthLengths
    {centered : Bool} {Y₁ Y₂ floor padding : ℝ}
    (domain : PairedEngineDomain centered parent a f.source.base Y₁ Y₂ floor padding)
    (slots : OriginalSlotDictionary parent d.length)
    (direct : G.tag = .direct → parent.geometry.slotCount = 0)
    (cutoff rootLength : ℝ) (hcutoff : 0 ≤ cutoff) (hsmall : 2 * cutoff ≤ step)
    (hparameters : D.parameters = CanonicalLiteralAllocatedData.parameters d f.allocation
      rectangle (G.literalRowParameter cutoff) (G.literalSupportParameter rootLength) a.κ)
    (annulus : ℝ) (cap : ℕ) (error : ℝ) (herr : 0 ≤ error)
    (hbound : d.scaleProduct rectangle *
      ((Ideal.absNorm G.literalFirstExtraction.val : ℝ) *
        (Ideal.absNorm G.ideals.second.val : ℝ)) ≤
      annulus ^ (2 * cap) * f.source.base ^ (a.n₁ + a.n₂ + a.z))
    (hthreshold : annulus ^ (2 * cap) ≤ f.source.base ^ error) :
    D.OriginalSixthLengthBinding parent a step G rootLength := by
  have hproduct : f.source.scale₁ * f.source.scale₂ * f.source.base ^ f.source.beforeLength ≤
      f.source.base ^ (G.skeleton.rawDegree + error) := by
    have he := d.factors_source_scaleProduct (C := C) R side χ ideal hideal firstSign rectangle
      L selection hne
    cases side <;>
      exact he.trans_le (d.scaleProduct_le_originalRawDegree G annulus cap error rectangle
        hbound hthreshold)
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
      scales := (G.literalEndpointWindows f.source.base_gt_one cutoff rootLength hcutoff hsmall)
        .reparameterize hm (congrArg (fun y : ℝ => y - rootLength) hq)
      rawScaleError := error
      rawScaleError_nonneg := herr
      original_scale_product := hproduct }
  · intro hd
    have hc : k ≤ parent.geometry.slotCount := by
      simpa only [Fintype.card_fin] using
        Fintype.card_le_of_injective slots.index slots.index.injective
    rw [direct hd] at hc
    exact Nat.eq_zero_of_le_zero hc

@[simp] theorem factorsOriginalSixthLengths_error
    {centered : Bool} {Y₁ Y₂ floor padding : ℝ}
    (domain : PairedEngineDomain centered parent a f.source.base Y₁ Y₂ floor padding)
    (slots : OriginalSlotDictionary parent d.length)
    (direct : G.tag = .direct → parent.geometry.slotCount = 0)
    (cutoff rootLength : ℝ) (hcutoff : 0 ≤ cutoff) (hsmall : 2 * cutoff ≤ step)
    (hparameters : D.parameters = CanonicalLiteralAllocatedData.parameters d f.allocation
      rectangle (G.literalRowParameter cutoff) (G.literalSupportParameter rootLength) a.κ)
    (annulus : ℝ) (cap : ℕ) (error : ℝ) (herr : 0 ≤ error)
    (hbound : d.scaleProduct rectangle *
      ((Ideal.absNorm G.literalFirstExtraction.val : ℝ) *
        (Ideal.absNorm G.ideals.second.val : ℝ)) ≤
      annulus ^ (2 * cap) * f.source.base ^ (a.n₁ + a.n₂ + a.z))
    (hthreshold : annulus ^ (2 * cap) ≤ f.source.base ^ error) :
    (d.factorsOriginalSixthLengths (C := C) R side χ ideal hideal firstSign rectangle L selection hne
      D parent a step G domain slots direct cutoff rootLength hcutoff hsmall hparameters
      annulus cap error herr hbound hthreshold).scales.error = cutoff := by
  simp only [factorsOriginalSixthLengths, OriginalNominalGeometry.ScaleWindows.error,
    OriginalNominalGeometry.ScaleWindows.reparameterize,
    OriginalNominalGeometry.literalEndpointWindows, add_zero]

end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.literalParameters_secondWidth
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.factors_childLength_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.factorsOriginalSixthLengths
