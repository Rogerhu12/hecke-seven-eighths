import HeckeSkeleton.SmallRadius.SmallRadiusAnnularMellinFourier
import HeckeGeneral.Analysis.SUnitTotalNormFourierBounds

/-!
UNCOMPILED candidate. Reindex the genuine all-radius Mellin Fourier
estimate by the product of BOTH finite column norms. On the original
valuation box that product to the sigma power has a uniform bound;
off the box the actual Fourier kernel vanishes. No radius threshold or
fixed finite-fibre assumption is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Analysis.SmallRadiusTotalNormDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Bridge
open SmallRadiusAnnularMellinDraft
open scoped Classical ContDiff BigOperators

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
attribute [local instance] LanglandsTunnell.TateLocal.localBorel
  LanglandsTunnell.TateLocal.borelSpace_localBorel
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : S, MeasurableSpace (v.val.adicCompletion K)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion K)ˣ]
variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Z" => SFiniteLocalGroup K S

private theorem exists_finiteNormFactor_power_bound (σ : ℝ) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ ζ ξ : Z,
      ζ ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ) →
      ξ ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ) →
      sUnitTotalNormFibreFactor K S ζ ξ ^ σ ≤ T := by
  let Q : Set (Z × Z) :=
    finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ) ×ˢ
      finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)
  have hQ : IsCompact Q :=
    (isCompact_finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)).prod
      (isCompact_finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ))
  let F : Z × Z → ℝ := fun p => sUnitTotalNormFibreFactor K S p.1 p.2
  have hF : Continuous F :=
    ((continuous_sFiniteProductNorm K S).comp continuous_fst).mul
      ((continuous_sFiniteProductNorm K S).comp continuous_snd)
  have hFσ : ContinuousOn (fun p => F p ^ σ) Q :=
    hF.continuousOn.rpow_const (fun p _ => Or.inl
      (sUnitTotalNormFibreFactor_pos K S p.1 p.2).ne')
  obtain ⟨T, hT⟩ := hQ.bddAbove_image hFσ
  refine ⟨max 1 T, le_max_left _ _, fun ζ ξ hζ hξ => ?_⟩
  have hmem : (ζ, ξ) ∈ Q := ⟨hζ, hξ⟩
  have h1 : F (ζ, ξ) ^ σ ≤ T := hT ⟨(ζ, ξ), hmem, rfl⟩
  exact h1.trans (le_max_right _ _)

/-- The actual total-norm Fourier family has one bound for every positive
radius and all finite coordinates. Its constants precede all moving data. -/
theorem exists_sUnitTotalNormAnnularPartitionJointFourier_seminorm_allRadius_bound
    (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
    (a0 b0 : ℝ) (ha0 : 0 < a0) (haSupport : tsupport a ⊆ Set.Icc a0 b0)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (k n : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, ∃ J : ℕ, 0 ≤ C ∧
      ∀ ν : ℝ, ∀ ζ ξ : Z, ∀ φ : SchwartzMap V ℂ,
      ∀ R : {r : ℝ // 0 < r},
        SchwartzMap.seminorm ℝ k n
          (sUnitTotalNormAnnularPartitionJointFourier K S Γ a ha a0 b0 ha0 haSupport
            ψ hψ hψsupport ν ζ ξ φ R) ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-σ) := by
  obtain ⟨s, C, J, hC, hb⟩ :=
    exists_sUnitMellinAnnularPartitionJointFourier_seminorm_allRadius_bound
      K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport σ hσ hσ1 k n
  obtain ⟨T, hT, hbox⟩ := exists_finiteNormFactor_power_bound K S Γ σ
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  refine ⟨s, C * T, J, mul_nonneg hC hT0, fun ν ζ ξ φ R => ?_⟩
  have hfinal : 0 ≤ (C * T) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
      (1 + |ν|) ^ J * R.val ^ (-σ) :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hC hT0) (apply_nonneg _ _))
        (pow_nonneg (by positivity) _)) (Real.rpow_nonneg R.property.le _)
  by_cases hζ : ζ ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)
  · by_cases hξ : ξ ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)
    · have hFT := hbox ζ ξ hζ hξ
      have hFpos := sUnitTotalNormFibreFactor_pos K S ζ ξ
      have hpow : (sUnitTotalNormRadius K S ζ ξ R).val ^ (-σ) =
          sUnitTotalNormFibreFactor K S ζ ξ ^ σ * R.val ^ (-σ) := by
        change (R.val / sUnitTotalNormFibreFactor K S ζ ξ) ^ (-σ) = _
        rw [Real.div_rpow R.property.le hFpos.le, Real.rpow_neg hFpos.le,
          div_inv_eq_mul]
        exact mul_comm _ _
      let P : ℝ := C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
        (1 + |ν|) ^ J * R.val ^ (-σ)
      have hP : 0 ≤ P :=
        mul_nonneg
          (mul_nonneg (mul_nonneg hC (apply_nonneg _ _)) (pow_nonneg (by positivity) _))
          (Real.rpow_nonneg R.property.le _)
      change SchwartzMap.seminorm ℝ k n
        (sUnitMellinAnnularPartitionJointFourier K S Γ a ha a0 b0 ha0 haSupport
          ψ hψ hψsupport ν ζ ξ φ (sUnitTotalNormRadius K S ζ ξ R)) ≤ _
      calc
        _ ≤ C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
            (1 + |ν|) ^ J * (sUnitTotalNormRadius K S ζ ξ R).val ^ (-σ) :=
          hb ν ζ ξ φ (sUnitTotalNormRadius K S ζ ξ R)
        _ = P * sUnitTotalNormFibreFactor K S ζ ξ ^ σ := by rw [hpow]; dsimp [P]; ring
        _ ≤ P * T := mul_le_mul_of_nonneg_left hFT hP
        _ = (C * T) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
            (1 + |ν|) ^ J * R.val ^ (-σ) := by dsimp [P]; ring
    · rw [sUnitTotalNormAnnularPartitionJointFourier_eq_zero_of_not_mem_box K S Γ
        a ha a0 b0 ha0 haSupport ψ hψ hψsupport ν ζ ξ φ R (Or.inr hξ), map_zero]
      exact hfinal
  · rw [sUnitTotalNormAnnularPartitionJointFourier_eq_zero_of_not_mem_box K S Γ
      a ha a0 b0 ha0 haSupport ψ hψ hψsupport ν ζ ξ φ R (Or.inl hζ), map_zero]
    exact hfinal

end HeckeGeneral.Analysis.SmallRadiusTotalNormDraft
