import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralChartCoefficients
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ConstantCommonLeaf

/-!
# Computed common-atom extraction of the literal two-stage leaf

The inputs are the individual original atom tables and the actual two
support-extraction branches. The complete coefficients, both ordinary
rectangles, the common scalars and their row reweighting are computed.
The source is the existing `fullCorrelationHybridLeaf`, on the original
allocation label and both unchanged Fourier kernels.

The two original logarithmic coordinates keep the pool prime power and
the second common ideal. Their constant row translations disappear
only inside the proved column norms. Neither Fourier variable changes.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralCommonLeaf

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support WholeAllocation

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable {k l : ℕ}
variable (R : ActualSecondCorrelationRows A σ H ι)
variable (left : CanonicalLiteralRectangles.Atoms (K := K) k)
variable (right : CanonicalLiteralRectangles.Atoms (K := K) l)
variable {support : Finset (Ideal (𝓞 K))}
variable (bL : SupportCartesianBranch left.plain₁ left.plain₂ left.slots support)
variable (bR : SupportCartesianBranch right.plain₁ right.plain₂ right.slots support)
variable (IL : AllocationColumn K bL.keep.card → A.Exterior)
variable (IR : AllocationColumn K bR.keep.card → A.Exterior)
variable (b : liveSecondAllocationBranches (Ray := PUnit.{1})
  (left.extract bL).plain₁ (left.extract bL).plain₂ (left.extract bL).slots
  (right.extract bR).plain₁ (right.extract bR).plain₂ (right.extract bR).slots IR)
variable (exceptional : H → Prop)
variable (F₁ F₂ : SchwartzMap ℝ ℂ)
variable (power : A.Exterior) (firstSign : ℝ) (rowLog : H → ℝ)

local instance canonicalLiteralCommonLeafCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

/-- This is the existing finite hybrid source with its computed whole
coefficients. Both fixed common atoms are still inside the columns. -/
def sourceLeaf : ActualHybridLeaf K H ℝ ℝ :=
  fullCorrelationHybridLeaf F₁ F₂ R.rows
    (left.extract bL).plain₁ (left.extract bL).plain₂ (left.extract bL).slots
    (right.extract bR).plain₁ (right.extract bR).plain₂ (right.extract bR).slots
    (fun j => (IR j).val) (fun h => R.weight h * R.correlation h)
    (fixedPhaseCoefficient PUnit.{1} (fun _ => (1 : Circle)))
    (fun χ h i => left.whole (bL.reconstruct i) *
      (fixedLeftPhase PUnit.{1} χ PUnit.unit : ℂ) *
        σ (A.sexticResidue (IL i) (R.frequency h)))
    (fun χ h j => right.whole (bR.reconstruct j) *
      (fixedRightPhase PUnit.{1} χ PUnit.unit : ℂ) *
        σ (A.sexticResidue (IR j) (-R.frequency h)))
    (fun _ i => -firstSign * Real.log
      (Ideal.absNorm (power.val * allocationColumnIdeal (bL.reconstruct i)) : ℝ))
    (fun h i => rowLog h - Real.log
      (Ideal.absNorm (allocationColumnIdeal (bL.reconstruct i)) : ℝ))
    (fun _ j => -firstSign * Real.log
      (Ideal.absNorm (power.val * allocationColumnIdeal (bR.reconstruct j)) : ℝ))
    (fun _ j => -Real.log
      (Ideal.absNorm (allocationColumnIdeal (bR.reconstruct j)) : ℝ))
    (fun _ _ _ _ => exceptional) b.val

private theorem left_mem_residual
    (i : AllocationColumn K bL.keep.card)
    (hi : i ∈ b.val.leftColumns
      (left.extract bL).plain₁ (left.extract bL).plain₂ (left.extract bL).slots) :
    i ∈ bL.residualColumns := by
  rw [SecondAllocationBranch.leftColumns, paired_allocated_columns_eq_filter] at hi
  exact (Finset.mem_filter.mp hi).1

private theorem right_mem_residual
    (j : AllocationColumn K bR.keep.card) (hj : j ∈ b.val.rightColumns) :
    j ∈ bR.residualColumns := by
  rw [SecondAllocationBranch.rightColumns, paired_allocated_columns_eq_filter] at hj
  exact (Finset.mem_filter.mp hj).1

/-- The same second common scalar is extracted from both centered
rectangles, by the individual occurrence product proved earlier. -/
def extraction :
    (sourceLeaf R left right bL bR IL IR b exceptional F₁ F₂ power firstSign rowLog)
      .ConstantAtomExtraction where
  leftScalar := left.commonScalar bL
  rightScalar := right.commonScalar bR
  leftResidual := secondAllocatedLeftCoefficient (σ := σ) PUnit.{1} IL R.frequency
    (fun _ => PUnit.unit) b.val.2.1 (left.extract bL).whole
  rightResidual := fun h j => star (secondAllocatedRightCoefficient (σ := σ) PUnit.{1}
    IR R.frequency (fun _ => PUnit.unit) b.val.2.1 (right.extract bR).whole h j)
  left h _ i hi := by
    change left.whole (bL.reconstruct i) * _ * _ = _
    rw [left.extract_whole bL i (left_mem_residual left right bL bR IR b i hi)]
    dsimp only [secondAllocatedLeftCoefficient]
    ring
  right h _ j hj := by
    change right.whole (bR.reconstruct j) * _ * _ = _
    rw [right.extract_whole bR j (right_mem_residual left right bL bR IR b j hj)]
    simp only [secondAllocatedRightCoefficient, star_star]
    ring

/-- The two constants are moved into the original row weight. Every
frequency, generator, classification and original ideal is unchanged. -/
def commonRows : ActualSecondCorrelationRows A σ H ι :=
  { R with weight := fun h =>
      R.weight h * left.commonScalar bL * star (right.commonScalar bR) }

variable (hIL : ∀ i ∈ childCartesianColumns
    (left.extract bL).plain₁ (left.extract bL).plain₂ (left.extract bL).slots,
  (IL i).val = allocationColumnIdeal i)
variable (hIR : ∀ j ∈ childCartesianColumns
    (right.extract bR).plain₁ (right.extract bR).plain₂ (right.extract bR).slots,
  (IR j).val = allocationColumnIdeal j)

/-- Actual two-rectangle factors of the reweighted source. The right
first coordinate has the sign imposed by its stored conjugate column. -/
def rectangles :=
  CanonicalLiteralRectangles.rectangles (commonRows R left right bL bR)
    (left.extract bL) (right.extract bR) IL IR hIL hIR b exceptional firstSign (-firstSign)

/-- Exact binding to the same source leaf. The translations are
calculated from the original pool power and common occurrence ideals. -/
def ordinaryBinding :
    (extraction R left right bL bR IL IR b exceptional F₁ F₂ power firstSign rowLog).leaf
      .OrdinaryBinding (rectangles R left right bL bR IL IR b exceptional firstSign hIL hIR) where
  rows := Finset.Subset.refl _
  rows_zero h hh hn := False.elim (hn hh)
  left := rfl
  right := rfl
  exceptional _ _ := Iff.rfl
  rowWeight h _ := by
    change (R.weight h * R.correlation h) * left.commonScalar bL *
        star (right.commonScalar bR) =
      (R.weight h * left.commonScalar bL * star (right.commonScalar bR)) * R.correlation h
    ring
  leftCoefficient _ _ _ _ := rfl
  rightCoefficient _ _ _ _ := by simp only [extraction,
    ActualHybridLeaf.ConstantAtomExtraction.leaf, ActualHybridLeaf.withConstantAtoms, star_star]
  leftPoint h _ := by
    refine ⟨WithLp.toLp 2
      (-firstSign * Real.log (Ideal.absNorm (power.val * bL.literalExtractedIdeal) : ℝ),
        rowLog h - Real.log (Ideal.absNorm bL.literalExtractedIdeal : ℝ)), ?_⟩
    intro i hi
    have hm := left_mem_residual left right bL bR IR b i hi
    have hp := Finset.mem_product.mp (Finset.mem_product.mp hm).1
    have h₁ := (left.extract bL).plain₁_nonzero i.1.1 hp.1
    have h₂ := (left.extract bL).plain₂_nonzero i.1.2 hp.2
    apply CanonicalLiteralLocations.actual_product_locations firstSign (rowLog h)
      i h₁ h₂
      (power.val * allocationColumnIdeal (bL.reconstruct i))
      (allocationColumnIdeal (bL.reconstruct i))
      (power.val * bL.literalExtractedIdeal) bL.literalExtractedIdeal
      (mul_ne_zero power.property.1 bL.literalExtractedIdeal_ne_zero)
      bL.literalExtractedIdeal_ne_zero
    · rw [bL.reconstruct_literalIdeal i hm, mul_assoc]
    · exact bL.reconstruct_literalIdeal i hm
  rightPoint h _ := by
    refine ⟨WithLp.toLp 2
      (firstSign * Real.log (Ideal.absNorm (power.val * bR.literalExtractedIdeal) : ℝ),
        -Real.log (Ideal.absNorm bR.literalExtractedIdeal : ℝ)), ?_⟩
    intro j hj
    have hm := right_mem_residual left right bL bR IR b j hj
    have hp := Finset.mem_product.mp (Finset.mem_product.mp hm).1
    have h₁ := (right.extract bR).plain₁_nonzero j.1.1 hp.1
    have h₂ := (right.extract bR).plain₂_nonzero j.1.2 hp.2
    have he := CanonicalLiteralLocations.actual_product_locations (-firstSign) 0
      j h₁ h₂
      (power.val * allocationColumnIdeal (bR.reconstruct j))
      (allocationColumnIdeal (bR.reconstruct j))
      (power.val * bR.literalExtractedIdeal) bR.literalExtractedIdeal
      (mul_ne_zero power.property.1 bR.literalExtractedIdeal_ne_zero)
      bR.literalExtractedIdeal_ne_zero
      (by rw [bR.reconstruct_literalIdeal j hm, mul_assoc])
      (bR.reconstruct_literalIdeal j hm)
    simpa only [neg_neg, zero_sub, neg_mul] using he

/-- Only genuinely nonzero complete correlations enter the arithmetic
row calibration. The literal finite source itself is not filtered. -/
def supportedRows : ActualSecondCorrelationRows A σ H ι :=
  (commonRows R left right bL bR).restrictRows (fun h => R.correlation h ≠ 0)

def supportedRectangles :=
  CanonicalLiteralRectangles.rectangles (supportedRows R left right bL bR)
    (left.extract bL) (right.extract bR) IL IR hIL hIR b exceptional firstSign (-firstSign)

/-- Correlation-zero rows are omitted by an exact zero-summand identity,
while both computed logarithmic translations remain unchanged. This is
the binding used by the same canonical row-mass and capacity records. -/
def supportedOrdinaryBinding :
    (extraction R left right bL bR IL IR b exceptional F₁ F₂ power firstSign rowLog).leaf
      .OrdinaryBinding (supportedRectangles R left right bL bR IL IR b exceptional
        firstSign hIL hIR) where
  rows h hh := (Finset.mem_filter.mp hh).1
  rows_zero h hh hn := by
    have hc : R.correlation h = 0 := by
      by_contra hc
      exact hn (Finset.mem_filter.mpr ⟨hh, hc⟩)
    change (R.weight h * R.correlation h) * left.commonScalar bL *
      star (right.commonScalar bR) = 0
    simp only [hc, mul_zero, zero_mul]
  left := rfl
  right := rfl
  exceptional _ _ := Iff.rfl
  rowWeight := (ordinaryBinding R left right bL bR IL IR b exceptional
    F₁ F₂ power firstSign rowLog hIL hIR).rowWeight
  leftCoefficient := (ordinaryBinding R left right bL bR IL IR b exceptional
    F₁ F₂ power firstSign rowLog hIL hIR).leftCoefficient
  rightCoefficient := (ordinaryBinding R left right bL bR IL IR b exceptional
    F₁ F₂ power firstSign rowLog hIL hIR).rightCoefficient
  leftPoint := (ordinaryBinding R left right bL bR IL IR b exceptional
    F₁ F₂ power firstSign rowLog hIL hIR).leftPoint
  rightPoint := (ordinaryBinding R left right bL bR IL IR b exceptional
    F₁ F₂ power firstSign rowLog hIL hIR).rightPoint

/-- The row record above is exactly the record consumed by the genuine
common-atom mass budget when its primitive single-atom windows are given. -/
theorem commonRows_eq_withCommonAtoms
    (BL : bL.CommonAtomBounds left.characters left.base left.length left.slotWeight)
    (BR : bR.CommonAtomBounds right.characters right.base right.length right.slotWeight)
    (CL CR : A.Exterior)
    (hCL : bL.literalExtractedIdeal = CL.val)
    (hCR : bR.literalExtractedIdeal = CR.val) :
    commonRows R left right bL bR =
      R.withCommonAtoms (BL.atoms R.rows) (BR.atoms R.rows) := by
  have hL : ∀ h, (BL.atoms (A := A) (σ := σ) R.rows).value h = left.commonScalar bL :=
    BL.atoms_value R.rows CL hCL
  have hR : ∀ h, (BR.atoms (A := A) (σ := σ) R.rows).value h = right.commonScalar bR :=
    BR.atoms_value R.rows CR hCR
  unfold commonRows ActualSecondCorrelationRows.withCommonAtoms
  congr 1
  funext h
  rw [hL, hR]

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralCommonLeaf

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralCommonLeaf.extraction
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralCommonLeaf.ordinaryBinding
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralCommonLeaf.supportedOrdinaryBinding
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralCommonLeaf.commonRows_eq_withCommonAtoms
