import HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalZero
import HeckeGeneral.Bridge.TraceSchwartzFourierBounds

/-!
# Finite Schwartz control of the actual additive zero terms

The finite local test and Haar measures are fixed before the seminorm
indices and constant. Both the physical and the genuine trace Fourier
values at zero are controlled by that single finite collection.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalProfileBounds

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton MeasureTheory
open PrincipalZero ActualPoissonScale
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

theorem physical_tensor_zero (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) :
    sIntegerTensorTerm K S (traceSchwartzToMixed K φ) h 0 =
      φ 0 * ∏ v ∈ S, h v 0 := by
  simp only [sIntegerTensorTerm, map_zero, traceSchwartzToMixed_apply]

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

theorem dual_tensor_zero (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) :
    sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ) h 0 =
      traceSchwartzFourier K φ 0 * sIntegerLocalFourierProduct K μv S h 0 := by
  have hf := fourierIntegral_traceSchwartzToMixed_traceToMixed K φ 0
  simp only [map_zero] at hf
  change AdelicFourier.fourierIntegral (standardMixedAddCharacter K) volume
    (traceSchwartzToMixed K φ) ((InfiniteAdeleRing.ringEquiv_mixedSpace K) 0) *
      sIntegerLocalFourierProduct K μv S h 0 = _
  rw [map_zero, hf]

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [Γ.FiniteIndex]

/-- The seminorm and constant are independent of the original marks,
coefficients, physical row scale, and archimedean test. -/
theorem exists_zeroProfileSize_bound
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) :
    ∃ s : Finset (ℕ × ℕ), ∃ A : ℝ, 0 ≤ A ∧
      ∀ φ : SchwartzMap V ℂ,
        zeroProfileSize K S Γ μv φ h ≤
          A * s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
  obtain ⟨F, C, hC, hFT⟩ := traceSchwartzFourier_real_seminorm_bound K 0 0
  let s := F ∪ {(0, 0)}
  let a := ‖sIntegerLocalFourierProduct K μv S h 0‖
  let b := ‖∏ v ∈ S, h v 0‖
  let A := (sUnitHaarCovolume K Sset Γ).toReal *
    (fieldConstant K * (C : ℝ) * a + b)
  refine ⟨s, A, ?_, ?_⟩
  · dsimp only [A, a, b]
    exact mul_nonneg ENNReal.toReal_nonneg
      (add_nonneg
        (mul_nonneg (mul_nonneg (fieldConstant_nonneg K) C.property) (norm_nonneg _))
        (norm_nonneg _))
  intro φ
  have hsup : F.sup (schwartzSeminormFamily ℝ V ℂ) φ ≤
      s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro i hi
    exact Seminorm.le_finset_sup_apply (Finset.mem_union_left _ hi)
  have hzero : SchwartzMap.seminorm ℝ 0 0 φ ≤
      s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
    have hz : (schwartzSeminormFamily ℝ V ℂ (0, 0)) φ ≤
        s.sup (schwartzSeminormFamily ℝ V ℂ) φ := Seminorm.le_finset_sup_apply
      (show (0, 0) ∈ s by simp only [s, Finset.mem_union, Finset.mem_singleton, or_true])
    simpa only [SchwartzMap.schwartzSeminormFamily_apply] using hz
  have hphysical : ‖φ 0‖ ≤ s.sup (schwartzSeminormFamily ℝ V ℂ) φ :=
    (SchwartzMap.norm_le_seminorm ℝ φ 0).trans hzero
  have hfourier : ‖traceSchwartzFourier K φ 0‖ ≤
      (C : ℝ) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ :=
    (SchwartzMap.norm_le_seminorm ℝ (traceSchwartzFourier K φ) 0).trans
      ((hFT φ).trans (mul_le_mul_of_nonneg_left hsup C.property))
  unfold zeroProfileSize
  rw [physical_tensor_zero K S, dual_tensor_zero K S μv, norm_mul, norm_mul]
  calc
    _ ≤ (sUnitHaarCovolume K Sset Γ).toReal *
      (fieldConstant K * ((C : ℝ) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ) * a +
        s.sup (schwartzSeminormFamily ℝ V ℂ) φ * b) := by
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      apply add_le_add
      · dsimp only [a]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hfourier (norm_nonneg _))
          (fieldConstant_nonneg K)
      · exact mul_le_mul_of_nonneg_right hphysical (norm_nonneg _)
    _ = A * s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by dsimp only [A]; ring

end HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalProfileBounds

end
