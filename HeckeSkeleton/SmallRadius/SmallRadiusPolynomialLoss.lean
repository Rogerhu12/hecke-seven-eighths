import HeckeSkeleton.SmallRadius.SmallRadiusTotalNormFourier

/-!
UNCOMPILED candidate. The small-radius loss of the genuine total-norm
Fourier family is absorbed into an arbitrary prescribed power of Z on
fixed polynomial ranges. The moment exponent and all seminorm constants
are chosen before Z, the two finite columns, height, and test function.
This supplies the small-radius scale step, not the Gram summation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Analysis.SmallRadiusPolynomialLossDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Bridge
open SmallRadiusTotalNormDraft
open scoped Classical ContDiff BigOperators

/-- Choose a small positive Mellin loss once for a fixed polynomial range. -/
theorem exists_small_radius_exponent (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ L * σ ≤ ε := by
  let σ := min 1 (ε / (L + 1))
  have hden : 0 < L + 1 := by linarith
  have hσ : 0 < σ := lt_min zero_lt_one (div_pos hε hden)
  have hσ1 : σ ≤ 1 := min_le_left _ _
  have hb : σ * (L + 1) ≤ ε :=
    (le_div_iff₀ hden).mp (min_le_right 1 (ε / (L + 1)))
  exact ⟨σ, hσ, hσ1, by nlinarith⟩

/-- Monotonicity at the actual small positive radius, with no cutoff at 1. -/
theorem radius_neg_rpow_le_small_power
    (Z R L ε σ : ℝ) (hZ : 1 ≤ Z) (hR : Z ^ (-L) ≤ R)
    (hσ : 0 ≤ σ) (hσε : L * σ ≤ ε) : R ^ (-σ) ≤ Z ^ ε := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  calc
    R ^ (-σ) ≤ (Z ^ (-L)) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hZ0 _) hR (neg_nonpos.mpr hσ)
    _ = Z ^ (L * σ) := by
      rw [← Real.rpow_mul hZ0.le]
      congr 1
      ring
    _ ≤ Z ^ ε := Real.rpow_le_rpow_of_exponent_le hZ hσε

/-- The Gram radius Q*c*k/Y^2 has a polynomial lower bound whenever
the two arithmetic norms and Q are at least one and Y is polynomially bounded. -/
theorem polynomial_lower_bound_gram_radius
    (Z Y Q c k D : ℝ) (hZ : 1 ≤ Z) (hY : 0 < Y)
    (hQ : 1 ≤ Q) (hc : 1 ≤ c) (hk : 1 ≤ k) (hYZ : Y ≤ Z ^ D) :
    Z ^ (-(2 * D)) ≤ Q * c * k / Y ^ 2 := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hnum : 1 ≤ Q * c * k :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hQ hc) hk
  have hsq : Y ^ 2 ≤ (Z ^ D) ^ 2 := pow_le_pow_left₀ hY.le hYZ 2
  calc
    Z ^ (-(2 * D)) = 1 / (Z ^ D) ^ 2 := by
      rw [Real.rpow_neg hZ0.le, one_div]
      congr 1
      rw [show 2 * D = D * (2 : ℝ) by ring, Real.rpow_mul hZ0.le,
        Real.rpow_two]
    _ ≤ 1 / Y ^ 2 := one_div_le_one_div_of_le (pow_pos hY 2) hsq
    _ ≤ Q * c * k / Y ^ 2 := div_le_div_of_nonneg_right hnum (sq_nonneg Y)

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
local notation "F" => SFiniteLocalGroup K S

/-- The existing total-norm Fourier kernel has an arbitrary small power
loss, uniformly in every radius in the prescribed polynomial range. -/
theorem exists_totalNormFourier_seminorm_polynomial_range_bound
    (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
    (a0 b0 : ℝ) (ha0 : 0 < a0) (haSupport : tsupport a ⊆ Set.Icc a0 b0)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) (k n : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, ∃ J : ℕ, 0 ≤ C ∧
      ∀ Z : ℝ, 1 ≤ Z → ∀ ν : ℝ, ∀ ζ ξ : F, ∀ φ : SchwartzMap V ℂ,
      ∀ R : {r : ℝ // 0 < r}, Z ^ (-L) ≤ R.val →
        SchwartzMap.seminorm ℝ k n
          (sUnitTotalNormAnnularPartitionJointFourier K S Γ a ha a0 b0 ha0 haSupport
            ψ hψ hψsupport ν ζ ξ φ R) ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * Z ^ ε := by
  obtain ⟨σ, hσ, hσ1, hσε⟩ := exists_small_radius_exponent L ε hL hε
  obtain ⟨s, C, J, hC, hb⟩ :=
    exists_sUnitTotalNormAnnularPartitionJointFourier_seminorm_allRadius_bound
      K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport σ hσ hσ1 k n
  refine ⟨s, C, J, hC, fun Z hZ ν ζ ξ φ R hR => ?_⟩
  have hfactor : 0 ≤ C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J :=
    mul_nonneg (mul_nonneg hC (apply_nonneg _ _)) (pow_nonneg (by positivity) _)
  exact (hb ν ζ ξ φ R).trans
    (mul_le_mul_of_nonneg_left
      (radius_neg_rpow_le_small_power Z R.val L ε σ hZ hR hσ.le hσε) hfactor)

end HeckeGeneral.Analysis.SmallRadiusPolynomialLossDraft
