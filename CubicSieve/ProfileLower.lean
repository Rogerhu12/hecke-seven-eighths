import CubicSieve.ProfileTest
import HeckeGeneral.Analysis.SUnitProfileEuler

/-! The chosen positive annular tensor gives an actual common orbital profile
bounded below by a positive constant on the norm window [1/2,1]. -/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.Profile

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeAxiom.ProbeUnits
open scoped Classical NumberField

variable {K : Type} [Field K] [NumberField K] (A : SArithmeticData K)
local notation "S" => (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
local instance profilelowerLocalInstance1 : MeasurableSpace (sLocalNormOneGroup K S) := borel _
local instance profilelowerLocalInstance2 : BorelSpace (sLocalNormOneGroup K S) := ⟨rfl⟩

theorem finiteTest_continuous : Continuous (finiteTest A) := by
  apply continuous_finsetProd
  intro v _
  exact (TateFiniteShell.annularTest_mem_localSchwartz K v.val).1.continuous.comp
    (continuous_apply v)

theorem finiteTest_compactSupport : HasCompactSupport (finiteTest A) := by
  refine HasCompactSupport.intro (isCompact_univ_pi fun v =>
    (TateFiniteShell.annularTest_mem_localSchwartz K v.val).2.isCompact) fun x hx => ?_
  simp only [Set.mem_univ_pi, not_forall] at hx
  obtain ⟨v, hv⟩ := hx
  exact Finset.prod_eq_zero (Finset.mem_univ v)
    (image_eq_zero_of_notMem_tsupport (f := TateFiniteShell.annularTest K v.val) hv)

def originalLocalFunction (x : sLocalMultiplicativeGroup K S) : ℂ :=
  originalTest A (toUnits A x).val

theorem originalLocalFunction_eq_tensor (x : sLocalMultiplicativeGroup K S) :
    originalLocalFunction A x = sLocalTensorTestFunction K S
      (HeckeAxiom.ProbeTestChoice.schwartzTest A (coordinates A) 1) (finiteTest A) x := by
  unfold originalLocalFunction originalTest
  rw [HeckeAxiom.ProbeTestChoice.tensor_eq, val_toUnits, RingEquiv.apply_symm_apply]
  unfold sLocalTensorTestFunction
  rw [HeckeAxiom.ProbeTestChoice.schwartzTest_symm]
  simp only [one_mul]
  congr 1

theorem original_section_one (r : ℝ) (hr : 0 < r)
    (hl : 1 / 2 ≤ r) (hu : r ≤ 1) :
    originalLocalFunction A (sLocalNormSection K S ⟨r, hr⟩) = 1 := by
  apply originalTest_one A
  · intro v
    have hcoord : ((InfiniteAdeleRing.ringEquiv_mixedSpace K)
        (toUnits A (sLocalNormSection K S ⟨r, hr⟩)).val.1).2 v =
        ((r ^ ((Module.finrank ℚ K : ℝ)⁻¹) : ℝ) : ℂ) := by
      rw [val_toUnits, RingEquiv.apply_symm_apply]
      rfl
    rw [hcoord, Complex.normSq_ofReal, ← pow_two]
    have hn : (1 : ℝ) ≤ InfinitePlace.nrComplexPlaces K := by
      exact_mod_cast A.nrComplexPlaces_pos
    have hnpos : (0 : ℝ) < InfinitePlace.nrComplexPlaces K := lt_of_lt_of_le zero_lt_one hn
    have he : ((Module.finrank ℚ K : ℝ)⁻¹) * 2 =
        (InfinitePlace.nrComplexPlaces K : ℝ)⁻¹ := by
      rw [HeckeAxiom.ProbeUnits.finrank_inv A]
      field_simp
    have hp : (r ^ ((Module.finrank ℚ K : ℝ)⁻¹)) ^ 2 =
        r ^ ((InfinitePlace.nrComplexPlaces K : ℝ)⁻¹) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
      norm_num only [Nat.cast_ofNat]
      rw [he]
    rw [hp]
    have hexp : (InfinitePlace.nrComplexPlaces K : ℝ)⁻¹ ≤ 1 :=
      (inv_le_one₀ hnpos).mpr hn
    have hlow : r ≤ r ^ ((InfinitePlace.nrComplexPlaces K : ℝ)⁻¹) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hr hu hexp
    have hupp : r ^ ((InfinitePlace.nrComplexPlaces K : ℝ)⁻¹) ≤ 1 :=
      Real.rpow_le_one hr.le hu (inv_nonneg.mpr hnpos.le)
    constructor <;> linarith
  · intro v
    rfl

def originalProfile (r : {r : ℝ // 0 < r}) : ℂ :=
  sUnitOrbitalProfile K S (originalLocalFunction A) r

theorem original_slice_integrable (r : {r : ℝ // 0 < r}) :
    Integrable (fun t : sLocalNormOneGroup K S =>
      originalLocalFunction A (sLocalNormSection K S r * (t : sLocalMultiplicativeGroup K S)))
      (sUnitHaarMeasure K S) := by
  simp_rw [originalLocalFunction_eq_tensor]
  exact integrable_sLocalSchwartzSlice K S
    (⊤ : Subgroup ((A.Sf : Set (HeightOneSpectrum (𝓞 K))).unit K))
    (HeckeAxiom.ProbeTestChoice.schwartzTest A (coordinates A) 1) (finiteTest A)
    (finiteTest_continuous A) (finiteTest_compactSupport A) r

theorem originalProfile_pos (r : {r : ℝ // 0 < r})
    (hl : 1 / 2 ≤ r.val) (hu : r.val ≤ 1) : 0 < (originalProfile A r).re := by
  have hc : Continuous (fun t : sLocalNormOneGroup K S =>
      originalLocalFunction A (sLocalNormSection K S r * (t : sLocalMultiplicativeGroup K S))) := by
    simp_rw [originalLocalFunction_eq_tensor]
    exact continuous_sLocalSchwartzSlice K S
      (HeckeAxiom.ProbeTestChoice.schwartzTest A (coordinates A) 1) (finiteTest A)
      (finiteTest_continuous A) r
  change 0 < (∫ t : sLocalNormOneGroup K S,
    originalLocalFunction A (sLocalNormSection K S r * (t : sLocalMultiplicativeGroup K S))
    ∂sUnitHaarMeasure K S).re
  change 0 < RCLike.re (∫ t : sLocalNormOneGroup K S,
    originalLocalFunction A (sLocalNormSection K S r * (t : sLocalMultiplicativeGroup K S))
    ∂sUnitHaarMeasure K S)
  rw [← integral_re (original_slice_integrable A r)]
  apply integral_pos_of_integrable_nonneg_nonzero (Complex.continuous_re.comp hc)
    ((original_slice_integrable A r).re)
  · intro t
    exact originalTest_re_nonneg A _
  · show (originalLocalFunction A (sLocalNormSection K S r *
      ((1 : sLocalNormOneGroup K S) : sLocalMultiplicativeGroup K S))).re ≠ 0
    simp only [Subgroup.coe_one, mul_one]
    rw [original_section_one A r.val r.property hl hu]
    norm_num

theorem originalProfile_im (r : {r : ℝ // 0 < r}) : (originalProfile A r).im = 0 := by
  change (∫ t : sLocalNormOneGroup K S,
    originalLocalFunction A (sLocalNormSection K S r * (t : sLocalMultiplicativeGroup K S))
    ∂sUnitHaarMeasure K S).im = 0
  change RCLike.im (∫ t : sLocalNormOneGroup K S,
    originalLocalFunction A (sLocalNormSection K S r * (t : sLocalMultiplicativeGroup K S))
    ∂sUnitHaarMeasure K S) = 0
  rw [← integral_im (original_slice_integrable A r)]
  change (∫ t : sLocalNormOneGroup K S,
    (originalTest A (toUnits A (sLocalNormSection K S r *
      (t : sLocalMultiplicativeGroup K S))).val).im ∂sUnitHaarMeasure K S) = 0
  simp only [originalLocalFunction, originalTest_im, integral_zero]

theorem originalProfile_continuous_exp :
    Continuous (fun t : ℝ => originalProfile A (sUnitExpRadius t)) := by
  have heq : originalLocalFunction A = sLocalTensorTestFunction K S
      (HeckeAxiom.ProbeTestChoice.schwartzTest A (coordinates A) 1) (finiteTest A) :=
    funext (originalLocalFunction_eq_tensor A)
  simp only [originalProfile, heq]
  exact continuous_sUnitOrbitalProfile_exp K S
    (⊤ : Subgroup ((A.Sf : Set (HeightOneSpectrum (𝓞 K))).unit K))
    (HeckeAxiom.ProbeTestChoice.schwartzTest A (coordinates A) 1) (finiteTest A)
    (finiteTest_continuous A) (finiteTest_compactSupport A)

/-- A concrete test supplies a common positive majorant on a full norm window;
the positive constant is obtained by the proved continuity and compact minimum. -/
theorem exists_originalProfile_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ (r : ℝ) (hr : 0 < r),
      1 / 2 ≤ r → r ≤ 1 → c ≤ (originalProfile A ⟨r, hr⟩).re := by
  obtain ⟨c, hc, hbound⟩ := (isCompact_Icc : IsCompact
      (Set.Icc (Real.log (1 / 2 : ℝ)) 0)).exists_forall_le'
    (Complex.continuous_re.comp (originalProfile_continuous_exp A)).continuousOn
    (a := 0) (by
      intro t ht
      apply originalProfile_pos A
      · change 1 / 2 ≤ Real.exp t
        calc (1 / 2 : ℝ) = Real.exp (Real.log (1 / 2 : ℝ)) :=
              (Real.exp_log (by norm_num)).symm
             _ ≤ Real.exp t := Real.exp_le_exp.mpr ht.1
      · change Real.exp t ≤ 1
        calc Real.exp t ≤ Real.exp 0 := Real.exp_le_exp.mpr ht.2
             _ = 1 := Real.exp_zero)
  refine ⟨c, hc, fun r hr hl hu => ?_⟩
  have ht : Real.log r ∈ Set.Icc (Real.log (1 / 2 : ℝ)) 0 :=
    ⟨Real.log_le_log (by norm_num) hl, Real.log_nonpos hr.le hu⟩
  simpa [sUnitExpRadius, Real.exp_log hr] using hbound (Real.log r) ht

end CubicSieve.Profile
