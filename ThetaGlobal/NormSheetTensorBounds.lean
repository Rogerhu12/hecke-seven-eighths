module

public import ThetaGlobal.FiniteSheetMellin
public import DedekindZetaZeroFree.Adeles.Quotients.NormSheets.RemainingCoordinateIntegrals

/-!
# Continuity and quadratic tails of actual tensor norm sheets

One complex coordinate carries the norm parameter.  Its weighted local
bound leaves an integrable function of the other coordinates.  The
pushforward of norm-one Haar to those coordinates is a scalar multiple
of their product Haar, with compact angular kernel.  This proves the
sheet majorant and the domination needed for continuity from local data.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.NormSheetTensorBounds

open NumberField MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.ThetaProfileHaarSheets
open DedekindZetaZeroFree.ThetaPositiveSheetMellin
open DedekindZetaZeroFree.NormSheetRemainingCoordinates
open ThetaGlobal.FiniteSheetMellin
open scoped Classical NumberField BigOperators Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)

local instance : MeasurableSpace R.A.G1 := borel _
local instance : BorelSpace R.A.G1 := ⟨rfl⟩

abbrev FiniteUnits := ∀ p : R.A.Sf, (p.val.adicCompletion F)ˣ

def weightedFinite (f : FiniteUnits R → ℂ) (s : ℂ) (z : FiniteUnits R) : ℂ :=
  f z * ∏ p, (‖(z p).val‖ : ℂ) ^ s

def tensor (W : ℂ) (a : ∀ w : InfinitePlace F, w.Completionˣ → ℂ)
    (f : FiniteUnits R → ℂ) (y : R.A.G) : ℂ :=
  W * f y.2 * ∏ w, a w (y.1 w)

def sheet (W : ℂ) (a : ∀ w : InfinitePlace F, w.Completionˣ → ℂ)
    (f : FiniteUnits R → ℂ) (v₀ : InfinitePlace F) (t : PositiveAxis) : ℂ :=
  ∫ z : R.A.G1, tensor R W a f (sheetEquiv R v₀ (t, z))
    ∂R.probe.domain.measure

theorem tensor_weight (W : ℂ) (a : ∀ w : InfinitePlace F, w.Completionˣ → ℂ)
    (f : FiniteUnits R → ℂ) (s : ℂ) (y : R.A.G) :
    (R.A.norm y : ℂ) ^ s * tensor R W a f y =
      W * (∏ w, archWeighted a s w (y.1 w)) * weightedFinite R f s y.2 := by
  rw [norm_cpow]
  simp only [tensor, weightedFinite, archWeighted, Finset.prod_mul_distrib]
  ring

private theorem prod_erase_eq (v₀ : InfinitePlace F) (g : InfinitePlace F → ℝ) :
    (∏ v ∈ Finset.univ.erase v₀, g v) =
      ∏ v : RemainingComplex ⟨v₀, R.A.complex_place v₀⟩, g v.val.val := by
  rw [Finset.prod_subtype (p := fun v => v ≠ v₀) (Finset.univ.erase v₀)
    (fun v => by simp) g]
  let e : {v : InfinitePlace F // v ≠ v₀} ≃
      RemainingComplex ⟨v₀, R.A.complex_place v₀⟩ :=
    { toFun := fun v => ⟨⟨v.val, R.A.complex_place v.val⟩,
        fun h => v.property (congrArg Subtype.val h)⟩
      invFun := fun v => ⟨v.val.val, fun h => v.property (Subtype.ext h)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

def remainingMajorant (a : ∀ w : InfinitePlace F, w.Completionˣ → ℂ)
    (f : FiniteUnits R → ℂ) (v₀ : InfinitePlace F) (z : R.A.G1) : ℝ :=
  (∏ w ∈ Finset.univ.erase v₀, ‖archWeighted a 2 w (z.val.1 w)‖) *
    ‖weightedFinite R f 2 z.val.2‖

theorem remainingMajorant_nonneg
    (a : ∀ w : InfinitePlace F, w.Completionˣ → ℂ)
    (f : FiniteUnits R → ℂ) (v₀ : InfinitePlace F) (z : R.A.G1) :
    0 ≤ remainingMajorant R a f v₀ z :=
  mul_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _) (norm_nonneg _)

theorem remainingMajorant_integrable
    (a : ∀ w : InfinitePlace F, w.Completionˣ → ℂ)
    (f : FiniteUnits R → ℂ) (v₀ : InfinitePlace F)
    (ha : ∀ w, Integrable (archWeighted a 2 w) (archHaar R.A w (N.angularHaar w)))
    (hf : Integrable (weightedFinite R f 2) (Measure.pi N.finiteMultHaar)) :
    Integrable (remainingMajorant R a f v₀) R.probe.domain.measure := by
  letI := N.angularHaar_isHaar
  letI := N.finiteMultHaar_isHaar
  letI := R.probe.domain.haar
  letI : SecondCountableTopology ℂˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  letI : BorelSpace ℂˣ := ⟨by
    change (borel ℂ).comap Units.val = borel _
    rw [← borel_comap, ← Units.isOpenEmbedding_val.isEmbedding.isInducing.eq_induced]⟩
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : ∀ p : R.A.Sf, TopologicalSpace.SeparableSpace (p.val.adicCompletion F) :=
    fun p => TopologicalSpace.SeparableSpace.of_denseRange _ (p.val.denseRange_algebraMap F)
  letI : ∀ p : R.A.Sf, SecondCountableTopology (p.val.adicCompletion F) :=
    fun p => inferInstance
  letI : ∀ p : R.A.Sf, SecondCountableTopology (p.val.adicCompletion F)ˣ :=
    fun p => Units.isEmbedding_val₀.secondCountableTopology
  let w : {v : InfinitePlace F // v.IsComplex} := ⟨v₀, R.A.complex_place v₀⟩
  let ν : RemainingComplex w → Measure ℂˣ := fun v =>
    Measure.map (completionUnitsEquiv R.A v.val.val).symm
      (archHaar R.A v.val.val (N.angularHaar v.val.val))
  have hν : ∀ v, (ν v).IsHaarMeasure := fun v =>
    (completionUnitsEquiv R.A v.val.val).symm.isHaarMeasure_map _
  letI : ∀ v, (ν v).IsHaarMeasure := hν
  let g : RemainingUnits R.A w → ℝ := fun y =>
    (∏ v : RemainingComplex w,
      ‖archWeighted a 2 v.val.val (completionUnitsEquiv R.A v.val.val (y.1 v))‖) *
      ‖weightedFinite R f 2 y.2‖
  have hlocal (v : RemainingComplex w) :
      Integrable (fun z : ℂˣ =>
        ‖archWeighted a 2 v.val.val (completionUnitsEquiv R.A v.val.val z)‖) (ν v) := by
    rw [(completionUnitsEquiv R.A v.val.val).symm.toHomeomorph.toMeasurableEquiv
      .measurableEmbedding.integrable_map_iff]
    simpa only [ContinuousMulEquiv.apply_symm_apply] using (ha v.val.val).norm
  let μ : Measure (RemainingUnits R.A w) :=
    (Measure.pi ν).prod (Measure.pi N.finiteMultHaar)
  have hg : Integrable g μ :=
    (Integrable.fintype_prod hlocal).mul_prod hf.norm
  -- The geometric theorem was elaborated with the comap measurable space
  -- on finite units.  Extract its topological conclusions in that space,
  -- then compare Haar measures in the actual product Borel space used by N.
  have hgeometry : Continuous (remainingProjection R.A w) ∧
      Function.Surjective (remainingProjection R.A w) ∧
      Filter.Tendsto (remainingProjection R.A w) (Filter.cocompact R.A.G1)
        (Filter.cocompact (RemainingUnits R.A w)) := by
    letI : ∀ p : R.A.Sf, MeasurableSpace (p.val.adicCompletion F)ˣ :=
      fun _ => MeasurableSpace.comap Units.val (borel _)
    letI : ∀ p : R.A.Sf, BorelSpace (p.val.adicCompletion F)ˣ := fun p => ⟨by
      change (borel (p.val.adicCompletion F)).comap Units.val = borel _
      rw [← borel_comap, ← Units.isEmbedding_val₀.isInducing.eq_induced]⟩
    obtain ⟨hp, hs, _, ht, _⟩ := raw_remaining_projection_haar R.A w
      R.probe.domain.measure R.probe.domain.haar ν hν
      (fun _ => Measure.haar) (fun _ => inferInstance)
    exact ⟨hp, hs, ht⟩
  obtain ⟨hp, hs, ht⟩ := hgeometry
  letI : μ.IsHaarMeasure := by
    dsimp only [μ]
    infer_instance
  letI : (Measure.map (remainingProjection R.A w)
      R.probe.domain.measure).IsHaarMeasure :=
    Measure.isHaarMeasure_map R.probe.domain.measure (remainingProjection R.A w) hp hs ht
  have hm : Measure.map (remainingProjection R.A w) R.probe.domain.measure =
      Measure.haarScalarFactor
        (Measure.map (remainingProjection R.A w) R.probe.domain.measure) μ • μ :=
    Measure.isMulLeftInvariant_eq_smul _ _
  have hmap : Integrable g (Measure.map (remainingProjection R.A w) R.probe.domain.measure) := by
    rw [hm]
    exact hg.smul_measure_nnreal
  apply (hmap.comp_measurable hp.measurable).congr
  exact Filter.Eventually.of_forall fun z => by
    dsimp only [Function.comp_apply, g, remainingMajorant]
    rw [prod_erase_eq R v₀]
    congr 1
    apply Finset.prod_congr rfl
    intro v _
    congr 2
    apply Units.ext
    change (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (R.A.complex_place v.val.val)).symm
        ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (R.A.complex_place v.val.val)) (z.val.1 v.val.val).val) = _
    exact (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (R.A.complex_place v.val.val)).symm_apply_apply _

theorem tensor_sheet_quadratic_bound
    (W : ℂ) (a : ∀ w : InfinitePlace F, w.Completionˣ → ℂ)
    (f : FiniteUnits R → ℂ) (v₀ : InfinitePlace F)
    (B : ℝ) (hB : ∀ z, ‖archWeighted a 2 v₀ z‖ ≤ B)
    (t : PositiveAxis) (z : R.A.G1) :
    ‖tensor R W a f (sheetEquiv R v₀ (t, z))‖ ≤
      (‖W‖ * B) * (t.val ^ 2)⁻¹ * remainingMajorant R a f v₀ z := by
  have hn : R.A.norm (sheetEquiv R v₀ (t, z)) = t.val :=
    congrArg Subtype.val (sheetEquiv_norm R v₀ (t, z))
  have hf : (sheetEquiv R v₀ (t, z)).2 = z.val.2 := by
    ext p
    simp [sheetEquiv, normSplit, normSection]
  have ha (w : InfinitePlace F) (hw : w ≠ v₀) :
      (sheetEquiv R v₀ (t, z)).1 w = z.val.1 w := by
    change (normSection R.A v₀ t).1 w * z.val.1 w = _
    rw [normSection_at_other_place R.A v₀ w hw, one_mul]
  have hrest : (∏ w ∈ Finset.univ.erase v₀,
      ‖archWeighted a 2 w ((sheetEquiv R v₀ (t, z)).1 w)‖) =
      ∏ w ∈ Finset.univ.erase v₀, ‖archWeighted a 2 w (z.val.1 w)‖ := by
    apply Finset.prod_congr rfl
    intro w hw
    rw [ha w (Finset.mem_erase.mp hw).1]
  have he := congrArg norm (tensor_weight R W a f 2 (sheetEquiv R v₀ (t, z)))
  rw [hn, norm_mul, Complex.cpow_ofNat, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg t.property.le,
    norm_mul, norm_mul, norm_prod, hf,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ v₀), hrest] at he
  have hmul : ‖tensor R W a f (sheetEquiv R v₀ (t, z))‖ * t.val ^ 2 ≤
      (‖W‖ * B) * remainingMajorant R a f v₀ z := by
    rw [mul_comm, he]
    calc
      _ = (‖W‖ * ‖archWeighted a 2 v₀ ((sheetEquiv R v₀ (t, z)).1 v₀)‖) *
          remainingMajorant R a f v₀ z := by dsimp [remainingMajorant]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hB _) (norm_nonneg W))
        (remainingMajorant_nonneg R a f v₀ z)
  have hd := (le_div_iff₀ (sq_pos_of_pos t.property)).mpr hmul
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hd

theorem sheet_continuous_and_bound
    (W : ℂ) (a : ∀ w : InfinitePlace F, w.Completionˣ → ℂ)
    (f : FiniteUnits R → ℂ) (v₀ : InfinitePlace F)
    (hac : ∀ w, Continuous (a w)) (hfc : Continuous f)
    (hai : ∀ w, Integrable (archWeighted a 2 w) (archHaar R.A w (N.angularHaar w)))
    (hfi : Integrable (weightedFinite R f 2) (Measure.pi N.finiteMultHaar))
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ z, ‖archWeighted a 2 v₀ z‖ ≤ B) :
    Continuous (sheet R W a f v₀) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t : PositiveAxis,
        ‖sheet R W a f v₀ t‖ ≤ C * (t.val ^ 2)⁻¹ := by
  let G := remainingMajorant R a f v₀
  have hG := remainingMajorant_integrable R N a f v₀ hai hfi
  have hG0 : ∀ z, 0 ≤ G z := remainingMajorant_nonneg R a f v₀
  have htc : Continuous (tensor R W a f) := by
    apply Continuous.mul
    · exact continuous_const.mul (hfc.comp continuous_snd)
    · exact continuous_finset_prod _ fun w _ =>
        (hac w).comp ((continuous_apply w).comp continuous_fst)
  have hbound := tensor_sheet_quadratic_bound R W a f v₀ B hB
  have hc : Continuous (fun t : PositiveAxis => (t.val ^ 2)⁻¹) :=
    (continuous_subtype_val.pow 2).inv₀ fun t => pow_ne_zero 2 t.property.ne'
  have hint (t : PositiveAxis) : Integrable
      (fun z : R.A.G1 => tensor R W a f (sheetEquiv R v₀ (t, z)))
        R.probe.domain.measure :=
    (hG.const_mul ((‖W‖ * B) * (t.val ^ 2)⁻¹)).mono'
      (htc.comp ((normSplit R.A v₀).continuous.comp
        (continuous_const.prodMk continuous_id))).aestronglyMeasurable
      (Filter.Eventually.of_forall (hbound t))
  constructor
  · apply continuous_iff_continuousAt.mpr
    intro t₀
    apply continuousAt_of_dominated
      (bound := fun z => (‖W‖ * B) * ((t₀.val ^ 2)⁻¹ + 1) * G z)
    · exact Filter.Eventually.of_forall fun t => (hint t).aestronglyMeasurable
    · have ht : ∀ᶠ t : PositiveAxis in 𝓝 t₀,
          (t.val ^ 2)⁻¹ < (t₀.val ^ 2)⁻¹ + 1 :=
        hc.continuousAt.eventually (Iio_mem_nhds (by linarith))
      filter_upwards [ht] with t ht
      exact Filter.Eventually.of_forall fun z => (hbound t z).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left ht.le (mul_nonneg (norm_nonneg _) hB0)) (hG0 z))
    · exact hG.const_mul _
    · exact Filter.Eventually.of_forall fun z =>
        (htc.comp ((normSplit R.A v₀).continuous.comp
          (continuous_id.prodMk continuous_const))).continuousAt
  · refine ⟨(‖W‖ * B) * (∫ z, G z ∂R.probe.domain.measure),
      mul_nonneg (mul_nonneg (norm_nonneg _) hB0) (integral_nonneg hG0), ?_⟩
    intro t
    calc
      ‖sheet R W a f v₀ t‖ ≤ ∫ z,
          (‖W‖ * B) * (t.val ^ 2)⁻¹ * G z ∂R.probe.domain.measure :=
        norm_integral_le_of_norm_le (hG.const_mul _)
          (Filter.Eventually.of_forall (hbound t))
      _ = _ := by rw [integral_const_mul]; ring

end ThetaGlobal.NormSheetTensorBounds

#print axioms ThetaGlobal.NormSheetTensorBounds.sheet_continuous_and_bound
