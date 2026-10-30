module

public import ThetaGlobal.FiniteSheetMellin

/-!
# Direct sheet Mellin transform and the actual finite Haar volume

The finite direct function is the characteristic function of the actual
target-kernel cutoff.  Compactness forces its local norms to equal one;
therefore its Mellin transform is precisely its Haar volume, with no
suppressed factor.  The archimedean factors are left local for the
explicit high K-type Mellin input.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.FiniteDirectMellin

open NumberField MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources DedekindZetaZeroFree.ThetaExpansion
open DedekindZetaZeroFree.ThetaProfileHaarSheets
open DedekindZetaZeroFree.ThetaPositiveSheetMellin
open ThetaGlobal.FiniteSheetMellin
open scoped Classical NumberField BigOperators

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (B : FirstRootCutoffs R)

local instance : MeasurableSpace R.A.G1 := borel _
local instance : BorelSpace R.A.G1 := ⟨rfl⟩

def cutoffProduct (z : ∀ p : R.A.Sf, (p.val.adicCompletion F)ˣ) : ℂ :=
  ∏ p, (B.cutoff p : Set _).indicator (fun _ => (1 : ℂ)) (z p)

theorem cutoffProduct_continuous : Continuous (cutoffProduct R B) := by
  apply continuous_finset_prod
  intro p _
  have hclopen : IsClopen (B.cutoff p : Set (p.val.adicCompletion F)ˣ) :=
    ⟨(B.cutoff p).isClosed_of_isOpen (B.open_cutoff p), B.open_cutoff p⟩
  exact (hclopen.continuous_indicator continuous_const).comp (continuous_apply p)

def cutoffVolume : ℝ :=
  ∏ p, (N.finiteMultHaar p (B.cutoff p : Set _)).toReal

theorem cutoffVolume_pos : 0 < cutoffVolume R N B := by
  letI := N.finiteMultHaar_isHaar
  apply Finset.prod_pos
  intro p _
  exact ENNReal.toReal_pos
    ((B.open_cutoff p).measure_ne_zero _ ⟨1, (B.cutoff p).one_mem⟩)
    (B.compact_cutoff p).measure_ne_top

theorem cutoffProduct_integral :
    (∫ z, cutoffProduct R B z ∂Measure.pi N.finiteMultHaar) =
      (cutoffVolume R N B : ℂ) := by
  letI := N.finiteMultHaar_isHaar
  unfold cutoffProduct cutoffVolume
  rw [integral_fintype_prod_eq_prod]
  simp_rw [integral_indicator_const (μ := N.finiteMultHaar _) (1 : ℂ)
    (B.open_cutoff _).measurableSet]
  simp only [measureReal_def, Complex.real_smul, mul_one, Complex.ofReal_prod]

theorem cutoffProduct_integrable :
    Integrable (cutoffProduct R B) (Measure.pi N.finiteMultHaar) := by
  letI := N.finiteMultHaar_isHaar
  apply Integrable.fintype_prod_dep
  intro p
  exact (integrable_indicator_iff (B.open_cutoff p).measurableSet).mpr
    (integrableOn_const (C := (1 : ℂ)) (μ := N.finiteMultHaar p)
      (B.compact_cutoff p).measure_ne_top)

theorem cutoffProduct_norm_power (s : ℂ)
    (z : ∀ p : R.A.Sf, (p.val.adicCompletion F)ˣ) :
    (∏ p, (‖(z p).val‖ : ℂ) ^ s) * cutoffProduct R B z = cutoffProduct R B z := by
  by_cases hz : ∀ p, z p ∈ B.cutoff p
  · have hn (p : R.A.Sf) : ‖(z p).val‖ = 1 :=
      GaussianSmoothing.compact_subgroup_norm_one (B.cutoff p) (B.compact_cutoff p)
        (z p) (hz p)
    simp only [hn, Complex.ofReal_one, Complex.one_cpow, Finset.prod_const_one, one_mul]
  · obtain ⟨p, hp⟩ := not_forall.mp hz
    have hzero : cutoffProduct R B z = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ p) (Set.indicator_of_notMem hp _)
    rw [hzero, mul_zero]

def directTensor (W : ℂ)
    (a : ∀ w : InfinitePlace F, w.Completionˣ → ℂ) (y : R.A.G) : ℂ :=
  W * cutoffProduct R B y.2 * ∏ w, a w (y.1 w)

theorem directTensor_weight (W : ℂ)
    (a : ∀ w : InfinitePlace F, w.Completionˣ → ℂ) (s : ℂ) (y : R.A.G) :
    (R.A.norm y : ℂ) ^ s * directTensor R B W a y =
      W * (∏ w, archWeighted a s w (y.1 w)) * cutoffProduct R B y.2 := by
  rw [norm_cpow]
  simp only [directTensor, archWeighted, Finset.prod_mul_distrib]
  calc
    _ = W * ((∏ w, a w (y.1 w)) *
        (∏ w, ((‖(y.1 w).val‖ ^ 2 : ℝ) : ℂ) ^ s)) *
        ((∏ p, (‖(y.2 p).val‖ : ℂ) ^ s) * cutoffProduct R B y.2) := by ring
    _ = _ := by rw [cutoffProduct_norm_power]

theorem direct_global_mellin (W : ℂ)
    (a : ∀ w : InfinitePlace F, w.Completionˣ → ℂ) (s : ℂ)
    (ha : ∀ w, Integrable (archWeighted a s w) (archHaar R.A w (N.angularHaar w))) :
    Integrable (fun y => (R.A.norm y : ℂ) ^ s * directTensor R B W a y) N.groupHaar ∧
    (∫ y, (R.A.norm y : ℂ) ^ s * directTensor R B W a y ∂N.groupHaar) =
      W * (cutoffVolume R N B : ℂ) *
        ∏ w : InfinitePlace F, ∫ z, archWeighted a s w z ∂archHaar R.A w (N.angularHaar w) := by
  letI := N.finiteMultHaar_isHaar
  letI := N.angularHaar_isHaar
  letI : ∀ w : InfinitePlace F, SecondCountableTopology w.Completion := fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (R.A.complex_place w)).toHomeomorph.secondCountableTopology
  letI : ∀ w : InfinitePlace F, SecondCountableTopology w.Completionˣ :=
    fun w => Units.isEmbedding_val₀.secondCountableTopology
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : ∀ p : R.A.Sf, TopologicalSpace.SeparableSpace (p.val.adicCompletion F) :=
    fun p => TopologicalSpace.SeparableSpace.of_denseRange _ (p.val.denseRange_algebraMap F)
  letI : ∀ p : R.A.Sf, SecondCountableTopology (p.val.adicCompletion F) := fun p => inferInstance
  letI : ∀ p : R.A.Sf, SecondCountableTopology (p.val.adicCompletion F)ˣ :=
    fun p => Units.isEmbedding_val₀.secondCountableTopology
  letI : ∀ w : InfinitePlace F, LocallyCompactSpace w.Completion := fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (R.A.complex_place w)).toHomeomorph.isOpenEmbedding.locallyCompactSpace
  have harch := Integrable.fintype_prod_dep ha
  have hfinite := cutoffProduct_integrable R N B
  rw [N.polar_transport]
  unfold productHaar
  rw [groupMeasurableSpace_eq_prod R.A, Measure.map_id']
  simp_rw [directTensor_weight]
  refine ⟨((harch.mul_prod hfinite).const_mul W).congr
    (Filter.Eventually.of_forall (fun _ => (mul_assoc _ _ _).symm)), ?_⟩
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_prod_mul, integral_fintype_prod_eq_prod,
    cutoffProduct_integral]
  ring

def directSheet (W : ℂ)
    (a : ∀ w : InfinitePlace F, w.Completionˣ → ℂ)
    (v₀ : InfinitePlace F) (t : PositiveAxis) : ℂ :=
  ∫ z : R.A.G1, directTensor R B W a (sheetEquiv R v₀ (t, z))
    ∂R.probe.domain.measure

theorem direct_sheet_mellin (W : ℂ)
    (a : ∀ w : InfinitePlace F, w.Completionˣ → ℂ)
    (v₀ : InfinitePlace F) (s : ℂ)
    (ha : ∀ w, Integrable (archWeighted a s w) (archHaar R.A w (N.angularHaar w))) :
    (∫ t : PositiveAxis, (t.val : ℂ) ^ s * directSheet R B W a v₀ t ∂positiveHaar) =
      W * (cutoffVolume R N B : ℂ) *
        ∏ w : InfinitePlace F, ∫ z, archWeighted a s w z ∂archHaar R.A w (N.angularHaar w) := by
  letI : LocallyCompactSpace R.A.G1 := (NormSheetsCoordinates.normOne_geometry R.A).1
  letI : SecondCountableTopology R.A.G1 := (NormSheetsCoordinates.normOne_geometry R.A).2
  letI := R.probe.domain.haar
  have h := direct_global_mellin R N B W a s ha
  exact (SheetMellin.sheet_transform_eq_global (sheetEquiv R v₀)
    (sheetEquiv_measurePreserving R N v₀) (normCoordinate R)
    (sheetEquiv_norm R v₀) (fun t : PositiveAxis => (t.val : ℂ) ^ s)
    (directTensor R B W a) h.1).trans h.2

end ThetaGlobal.FiniteDirectMellin

#print axioms ThetaGlobal.FiniteDirectMellin.cutoffVolume_pos
#print axioms ThetaGlobal.FiniteDirectMellin.direct_sheet_mellin
