import HeckeAxiom.ProbeTestChoice

/-! A fixed positive compact annular tensor. Its complex factor is one on
norm-square [1/4,7/4], while every finite factor is the actual unit-shell test. -/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.Profile

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open scoped Classical NumberField ContDiff

def positiveBump : ContDiffBump (1 : ℝ) := ⟨3 / 4, 7 / 8, by norm_num, by norm_num⟩

def positiveComplex (z : ℂ) : ℂ := (positiveBump (Complex.normSq z) : ℂ)

theorem positiveComplex_smooth : ContDiff ℝ (⊤ : ℕ∞) positiveComplex := by
  apply Complex.ofRealCLM.contDiff.comp
  apply positiveBump.contDiff.comp
  change ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => z.re * z.re + z.im * z.im)
  exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
    (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)

theorem positiveComplex_support :
    tsupport positiveComplex ⊆ {z : ℂ | 1 / 4 ≤ ‖z‖ ∧ ‖z‖ ≤ 2} := by
  apply closure_minimal
  · intro z hz
    have hb : positiveBump (Complex.normSq z) ≠ 0 := by
      simpa [Function.mem_support, positiveComplex] using hz
    have hb' := (positiveBump.support_eq ▸ hb :
      Complex.normSq z ∈ Metric.ball (1 : ℝ) (7 / 8))
    rw [Metric.mem_ball, Real.dist_eq, abs_lt, Complex.normSq_eq_norm_sq] at hb'
    dsimp [positiveBump] at hb'
    have hn := norm_nonneg z
    constructor <;> nlinarith
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)

theorem positiveComplex_annular : IsComplexAnnular positiveComplex := by
  refine ⟨positiveComplex_smooth, ?_, 1 / 4, 2, by norm_num, by norm_num,
    positiveComplex_support⟩
  apply IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) 2) isClosed_closure
  intro z hz
  simpa using (positiveComplex_support hz).2

theorem positiveComplex_radial (z w : ℂ) (h : ‖z‖ = ‖w‖) :
    positiveComplex z = positiveComplex w := by
  simp [positiveComplex, Complex.normSq_eq_norm_sq, h]

theorem positiveComplex_one (z : ℂ)
    (hl : 1 / 4 ≤ Complex.normSq z) (hu : Complex.normSq z ≤ 7 / 4) :
    positiveComplex z = 1 := by
  have hb : positiveBump (Complex.normSq z) = 1 := by
    apply positiveBump.one_of_mem_closedBall
    change |Complex.normSq z - 1| ≤ 3 / 4
    rw [abs_le]
    constructor <;> linarith
  simp [positiveComplex, hb]

variable {K : Type} [Field K] [NumberField K]

def coordinates (A : SArithmeticData K) :
    ProbeAnnularTensorWeights.AnnularCoordinates K A.Sf :=
  ProbeAnnularTensorWeights.shellCoordinates K A positiveComplex positiveComplex_annular
    positiveComplex_radial

def originalTest (A : SArithmeticData K) : SLocalProduct K A.Sf → ℂ :=
  ProbeAnnularTensorWeights.tensor K A.Sf (coordinates A)

theorem originalTest_annular (A : SArithmeticData K) :
    ProbeWeight.IsAnnularTensor K A.Sf (originalTest A) := by
  exact ⟨(coordinates A).fReal, (coordinates A).fComplex, (coordinates A).fFinite,
    (coordinates A).real_regular, (coordinates A).complex_regular,
    (coordinates A).finite_regular, fun _ => rfl⟩

theorem originalTest_compact_unit_support (A : SArithmeticData K) :
    HasCompactSupport (originalTest A) ∧ tsupport (originalTest A) ⊆ {x | IsUnit x} :=
  ProbeAnnularTensorWeights.tensor_compactSupport_and_unit_support K A.Sf (coordinates A)

def finiteReal (A : SArithmeticData K) (x : (v : ↥A.Sf) → v.val.adicCompletion K) : ℝ :=
  ∏ v, if x v ∈ TateFiniteShell.unitShell K v.val then 1 else 0

def finiteTest (A : SArithmeticData K) (x : (v : ↥A.Sf) → v.val.adicCompletion K) : ℂ :=
  ∏ v, TateFiniteShell.annularTest K v.val (x v)

theorem finiteTest_eq_real (A : SArithmeticData K) (x) :
    finiteTest A x = (finiteReal A x : ℂ) := by
  rw [finiteTest, finiteReal, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro v _
  by_cases h : x v ∈ TateFiniteShell.unitShell K v.val <;>
    simp [TateFiniteShell.annularTest, h]

theorem finiteReal_nonneg (A : SArithmeticData K) (x) : 0 ≤ finiteReal A x := by
  apply Finset.prod_nonneg
  intro v _
  split_ifs <;> norm_num

def originalReal (A : SArithmeticData K) (x : SLocalProduct K A.Sf) : ℝ :=
  (∏ v : {v : InfinitePlace K // v.IsComplex}, positiveBump
    (Complex.normSq ((InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).2 v))) *
    finiteReal A x.2

theorem originalTest_eq_real (A : SArithmeticData K) (x) :
    originalTest A x = (originalReal A x : ℂ) := by
  haveI : IsEmpty {v : InfinitePlace K // v.IsReal} :=
    ⟨fun v => (InfinitePlace.not_isReal_iff_isComplex.mpr (A.infinite_isComplex v.1)) v.2⟩
  simp only [originalTest, ProbeAnnularTensorWeights.tensor, coordinates,
    ProbeAnnularTensorWeights.shellCoordinates, Finset.prod_of_isEmpty, one_mul]
  change (∏ v : {v : InfinitePlace K // v.IsComplex}, positiveComplex
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).2 v)) * finiteTest A x.2 = _
  rw [finiteTest_eq_real, originalReal, Complex.ofReal_mul, Complex.ofReal_prod]
  rfl

theorem originalReal_nonneg (A : SArithmeticData K) (x) : 0 ≤ originalReal A x :=
  mul_nonneg (Finset.prod_nonneg fun _ _ => positiveBump.nonneg) (finiteReal_nonneg A _)

theorem originalTest_re_nonneg (A : SArithmeticData K) (x) : 0 ≤ (originalTest A x).re := by
  rw [originalTest_eq_real]
  exact originalReal_nonneg A x

theorem originalTest_im (A : SArithmeticData K) (x) : (originalTest A x).im = 0 := by
  rw [originalTest_eq_real]
  rfl

theorem originalTest_one (A : SArithmeticData K) (x : SLocalProduct K A.Sf)
    (harch : ∀ v : {v : InfinitePlace K // v.IsComplex},
      1 / 4 ≤ Complex.normSq ((InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).2 v) ∧
      Complex.normSq ((InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).2 v) ≤ 7 / 4)
    (hfinite : ∀ v : ↥A.Sf, x.2 v = 1) : originalTest A x = 1 := by
  haveI : IsEmpty {v : InfinitePlace K // v.IsReal} :=
    ⟨fun v => (InfinitePlace.not_isReal_iff_isComplex.mpr (A.infinite_isComplex v.1)) v.2⟩
  unfold originalTest ProbeAnnularTensorWeights.tensor coordinates
  simp only [ProbeAnnularTensorWeights.shellCoordinates, Finset.prod_of_isEmpty, one_mul]
  have h₁ : (∏ v : {v : InfinitePlace K // v.IsComplex}, positiveComplex
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K x.1).2 v)) = 1 :=
    Finset.prod_eq_one fun v _ => positiveComplex_one _ (harch v).1 (harch v).2
  have h₂ : (∏ v : ↥A.Sf, TateFiniteShell.annularTest K v.val (x.2 v)) = 1 := by
    apply Finset.prod_eq_one
    intro v _
    have hu : (1 : v.val.adicCompletion K) ∈ TateFiniteShell.unitShell K v.val :=
      (TateFiniteShell.mem_unitShell_iff K v.val 1).mpr (by simp)
    simp [hfinite v, TateFiniteShell.annularTest, hu]
  rw [h₁, h₂, one_mul]

end CubicSieve.Profile
