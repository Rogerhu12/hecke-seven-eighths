import CubicSieve.ProfileTransfer
import CubicSieve.OrbitDualNorm
import CubicSieve.CoprimeGram

/-! Instantiate the Mellin Gram transfer with the actual all-sector cubic
kernel. Both column ideal norms remain in the common radial profile. -/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.PoissonBlocks

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open CubicSieve.ExteriorKernel CubicSieve.OrbitRows CubicSieve.OrbitKernel
open CubicSieve.AnalyticDualNorm
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K] (A : SArithmeticData K)
local notation "S" => (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))

def support (J : ExteriorIdeal K S) : Finset (Ideal (𝓞 K)) :=
  (UniqueFactorizationMonoid.normalizedFactors J.val.val).toFinset

theorem coprime_iff_disjoint (I J : ExteriorIdeal K S) :
    IsCoprime I.val.val J.val.val ↔ Disjoint (support A I) (support A J) := by
  rw [Ideal.isCoprime_iff_sup_eq]
  exact CoprimeGram.sup_eq_top_iff_disjoint_normalizedFactors
    (nonZeroDivisors.coe_ne_zero I.val) (nonZeroDivisors.coe_ne_zero J.val)

theorem orbital_subtype_bound (H N : ℝ) (R : Finset (Orbits K S))
    (T : Finset (ExteriorIdeal K S))
    (hR : ∀ q ∈ R, (sIntegerOrbitNorm K S (Γ K S) q).val ≤ H)
    (hT : ∀ J ∈ T, Squarefree J.val.val ∧ exteriorNorm K S J ≤ N)
    (x : ↥T → ℂ) :
    (∑ q : R, ‖∑ J : T, coefficient K S D J.val q.val * x J‖ ^ 2) ≤
      ((Nat.card (SixthUnitClasses K S) : ℝ) * U K S D H N) * ∑ J : T, ‖x J‖ ^ 2 := by
  let z : ExteriorIdeal K S → ℂ := fun J => if hJ : J ∈ T then x ⟨J, hJ⟩ else 0
  have he (q : Orbits K S) : (∑ J ∈ T, coefficient K S D J q * z J) =
      ∑ J : T, coefficient K S D J.val q * x J := by
    rw [← Finset.sum_coe_sort T (fun J => coefficient K S D J q * z J)]
    apply Finset.sum_congr rfl
    intro J _
    simp only [z, dif_pos J.property]
  have henergy : (∑ J ∈ T, ‖z J‖ ^ 2) = ∑ J : T, ‖x J‖ ^ 2 := by
    rw [← Finset.sum_coe_sort T (fun J => ‖z J‖ ^ 2)]
    apply Finset.sum_congr rfl
    intro J _
    simp only [z, dif_pos J.property]
  have hh := OrbitDualNorm.orbital_family_bound K S D H N R T hR hT z
  rw [henergy] at hh
  simp_rw [he] at hh
  rw [Finset.sum_coe_sort R
    (fun q => ‖∑ J : T, coefficient K S D J.val q * x J‖ ^ 2)]
  exact hh

def blockRow (R : Finset (Orbits K S)) (T : Finset (ExteriorIdeal K S))
    (M : ℝ) (z : ↥T → ℂ) (q : ↥R) : ℂ :=
  ∑ I : T, ∑ J : T, if IsCoprime I.val.val.val J.val.val.val then
    (coefficient K S D I.val q.val * z I) *
      star (coefficient K S D J.val q.val * z J) *
        Profile.Gaussian.rawEnvelope A
          (M * (sIntegerOrbitNorm K S (Γ K S) q.val).val /
            (exteriorNorm K S I.val * exteriorNorm K S J.val)) else 0

theorem blockRow_eq (R : Finset (Orbits K S)) (T : Finset (ExteriorIdeal K S))
    (M N : ℝ) (hN : 0 < N) (z : ↥T → ℂ) (q : ↥R) :
    blockRow A D R T M z q = Profile.Gaussian.profileWeightedRow A
      (fun J : T => support A J.val) (fun q : R => fun J : T => coefficient K S D J.val q.val)
      (fun q : R => M * (sIntegerOrbitNorm K S (Γ K S) q.val).val / N ^ 2)
      (fun J : T => exteriorNorm K S J.val / N) z q := by
  unfold blockRow Profile.Gaussian.profileWeightedRow
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  rw [coprime_iff_disjoint A I.val J.val]
  have hI : 0 < exteriorNorm K S I.val := by
    change 0 < (I.val.val.val.absNorm : ℝ)
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I.val.val
  have hJ : 0 < exteriorNorm K S J.val := by
    change 0 < (J.val.val.val.absNorm : ℝ)
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors J.val.val
  by_cases hdisj : Disjoint (support A I.val) (support A J.val)
  · simp only [hdisj, if_true]
    congr 2
    field_simp [hN.ne', hI.ne', hJ.ne']
    <;> ring
  · simp only [hdisj, if_false]

theorem actual_profile_block_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ H N M : ℝ, 1 ≤ H → 1 ≤ N → 0 < M →
      ∀ R : Finset (Orbits K S), ∀ T : Finset (ExteriorIdeal K S),
      (∀ q ∈ R, H / 2 ≤ (sIntegerOrbitNorm K S (Γ K S) q).val ∧
        (sIntegerOrbitNorm K S (Γ K S) q).val ≤ H) →
      (∀ J ∈ T, Squarefree J.val.val ∧ exteriorNorm K S J ≤ N) →
      ∀ z : ↥T → ℂ,
        (∑ q : R, ‖blockRow A D R T M z q‖) ≤
          C * ((M * H / N ^ 2) ^ (-(1 / 6 : ℝ)) / (1 + M * H / N ^ 2) ^ 3) *
            U K S D H N * N ^ ε * ∑ J : T, ‖z J‖ ^ 2 := by
  obtain ⟨C₀, hC₀, hb⟩ := Profile.Gaussian.profileWeightedRow_block_bound A
  obtain ⟨C₁, hC₁, hc⟩ := CoprimeGram.supportCost_epsilon K ε hε
  let L : ℝ := Nat.card (SixthUnitClasses K S)
  have hL : 0 < L := by
    change 0 < (Nat.card (SixthUnitClasses K S) : ℝ)
    exact_mod_cast (Nat.card_pos (α := SixthUnitClasses K S))
  refine ⟨C₀ * L * C₁, mul_pos (mul_pos hC₀ hL) (by linarith), ?_⟩
  intro H N M hH hN hM R T hR hT z
  have hN₀ : 0 < N := by linarith
  have hH₀ : 0 < H := by linarith
  have hx (J : T) : 0 < exteriorNorm K S J.val / N := by
    apply div_pos _ hN₀
    change 0 < (J.val.val.val.absNorm : ℝ)
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors J.val.val
  have hx₁ (J : T) : exteriorNorm K S J.val / N ≤ 1 :=
    (div_le_one hN₀).mpr (hT J.val J.property).2
  have hcost (J : T) : (2 : ℝ) ^ (support A J.val).card ≤ C₁ * N ^ ε := by
    exact (hc J.val.val.val (nonZeroDivisors.coe_ne_zero J.val.val)).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hT J.val J.property).2 hε.le) (by linarith))
  have hr (q : R) : (M * H / N ^ 2) / 2 ≤
      M * (sIntegerOrbitNorm K S (Γ K S) q.val).val / N ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left (hR q.val q.property).1 hM.le
    calc
      (M * H / N ^ 2) / 2 = (M * (H / 2)) / N ^ 2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hh (sq_nonneg N)
  have hh := hb (fun J : T => support A J.val)
    (fun q : R => fun J : T => coefficient K S D J.val q.val)
    (fun q : R => M * (sIntegerOrbitNorm K S (Γ K S) q.val).val / N ^ 2)
    (fun J : T => exteriorNorm K S J.val / N) z (M * H / N ^ 2)
    (L * U K S D H N) (C₁ * N ^ ε) (∑ J : T, ‖z J‖ ^ 2)
    (by positivity) (mul_nonneg hL.le (U_nonneg K S D H N)) (by positivity)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hr hx hx₁ hcost
    (orbital_subtype_bound A D H N R T (fun q hq => (hR q hq).2) hT) le_rfl
  simp_rw [← blockRow_eq A D R T M N hN₀] at hh
  convert hh using 1 <;> dsimp only [L] <;> ring

end CubicSieve.PoissonBlocks
