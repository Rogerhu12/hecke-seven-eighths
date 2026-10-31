module

public import HeckeGeneral.Analysis.SIntegerProfileTail
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# A fixed outer frequency ball and its genuine orbital tail

The ball is chosen in the bare orbit norm, independently of the residual
column pair. A lower bound for the actual physical radius puts its entire
complement in the large-argument profile tail for every supported pair.
The theorem uses the proved orbit count and Schwartz decay, and retains
all original subgroup sectors. No bound for the tail itself is an input.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.OuterFrequencyTail

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

local notation "Q" => SIntegerOrbits K S Γ
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "L" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- Any prescribed saving is reached by one fixed kernel order, chosen
before the base, physical radius, column pair and orbit coefficient. -/
theorem exists_tail_order (B tau saving : ℝ) (hB : 0 ≤ B)
    (htau : 0 < tau) (hsaving : 0 ≤ saving) :
    ∃ A : ℝ, 1 < A ∧ B + tau * (1 - A) ≤ -saving := by
  refine ⟨2 + (B + saving) / tau, ?_, ?_⟩
  · have h : 0 ≤ (B + saving) / tau := div_nonneg (add_nonneg hB hsaving) htau.le
    linarith
  · have hid : B + tau * (1 - (2 + (B + saving) / tau)) = -tau - saving := by
      field_simp [ne_of_gt htau]
      ring
    rw [hid]
    linarith

/-- The source-independent outer cutoff is contained in the true
large-argument profile tail at every supported physical radius. -/
theorem outer_ball_imp_profile_tail (Z B tau rho q : ℝ)
    (hZ : 1 ≤ Z) (hrho : Z ^ (-B) ≤ rho) (hq : Z ^ (B + tau) < q) :
    Z ^ tau < rho * q := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hr : 0 < rho := (Real.rpow_pos_of_pos hz _).trans_le hrho
  have hs : Z ^ tau ≤ rho * Z ^ (B + tau) := by
    calc
      _ = Z ^ (-B) * Z ^ (B + tau) := by rw [← Real.rpow_add hz]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hrho (Real.rpow_nonneg hz.le _)
  exact hs.trans_lt (mul_lt_mul_of_pos_left hq hr)

theorem radius_cutoff_ge (Z B tau rho : ℝ) (hZ : 1 ≤ Z)
    (hrho : Z ^ (-B) ≤ rho) : Z ^ tau ≤ rho * Z ^ (B + tau) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  calc
    _ = Z ^ (-B) * Z ^ (B + tau) := by rw [← Real.rpow_add hz]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hrho (Real.rpow_nonneg hz.le _)

/-- The radius factor is retained and then paid for by the kernel
order. This is valid even when the actual physical radius is below one. -/
theorem tail_scale_bound (Z B tau saving A rho : ℝ)
    (hZ : 1 ≤ Z) (hB : 0 ≤ B) (htau : 0 ≤ tau) (hA : 1 < A)
    (hrho : Z ^ (-B) ≤ rho) (horder : B + tau * (1 - A) ≤ -saving) :
    (1 + rho⁻¹) * (rho * Z ^ (B + tau)) ^ (1 - A) ≤ 2 * Z ^ (-saving) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hr : 0 < rho := (Real.rpow_pos_of_pos hz _).trans_le hrho
  have hinv : rho⁻¹ ≤ Z ^ B := by
    calc
      _ ≤ (Z ^ (-B))⁻¹ := (inv_le_inv₀ hr (Real.rpow_pos_of_pos hz _)).mpr hrho
      _ = _ := by rw [← Real.rpow_neg hz.le, neg_neg]
  have hBpow : 1 ≤ Z ^ B := Real.one_le_rpow hZ hB
  have hfirst : 1 + rho⁻¹ ≤ 2 * Z ^ B := by linarith
  have hsecond : (rho * Z ^ (B + tau)) ^ (1 - A) ≤ Z ^ (tau * (1 - A)) := by
    rw [Real.rpow_mul hz.le]
    exact Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hz _)
      (radius_cutoff_ge Z B tau rho hZ hrho) (by linarith)
  calc
    _ ≤ (2 * Z ^ B) * Z ^ (tau * (1 - A)) :=
      mul_le_mul hfirst hsecond (Real.rpow_nonneg (by positivity) _)
        (by positivity)
    _ = 2 * Z ^ (B + tau * (1 - A)) := by rw [mul_assoc, ← Real.rpow_add hz]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ horder) (by norm_num)

/-- Quantitative tail on a fixed bare-frequency ball. The same constant
works for every radius satisfying its source lower bound, every actual
subgroup orbit coefficient and every Schwartz test. -/
theorem exists_outer_frequency_tail_bound
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (A : ℝ) (hA : 1 < A) (M : ℕ) (hM : Module.finrank ℤ L < M)
    (hOrder : (Module.finrank ℚ K : ℝ) * A ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : SchwartzMap V ℂ,
      ∀ (Z B tau saving : ℝ) (rho : {r : ℝ // 0 < r}),
      1 ≤ Z → 0 ≤ B → 0 ≤ tau → Z ^ (-B) ≤ rho.val →
      B + tau * (1 - A) ≤ -saving →
      ∀ (w : Q → ℂ) (W : ℝ), 0 ≤ W → (∀ q, ‖w q‖ ≤ W) →
        let f := fun q : {q : Q // Z ^ (B + tau) < (sIntegerOrbitNorm K S Γ q).val} =>
          w q.val * sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
            ⟨rho.val * (sIntegerOrbitNorm K S Γ q.val).val,
              mul_pos rho.property (sIntegerOrbitNorm K S Γ q.val).property⟩
        Summable f ∧ ‖∑' q, f q‖ ≤
          W * C * SchwartzMap.seminorm ℂ M 0 φ * Z ^ (-saving) := by
  obtain ⟨C, hC, htail⟩ := exists_sIntegerSchwartzProfile_weighted_tail_bound
    K S Γ ψ hψ hψsupport A hA M hM hOrder
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro φ Z B tau saving rho hZ hB htau hrho horder w W hW hw
  dsimp only
  let Y := Z ^ (B + tau)
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hY : 1 ≤ rho.val * Y :=
    (Real.one_le_rpow hZ htau).trans (radius_cutoff_ge Z B tau rho.val hZ hrho)
  obtain ⟨hs, hb⟩ := htail φ rho (rho.val * Y) hY w W hW hw
  let e : {q : Q // Y < (sIntegerOrbitNorm K S Γ q).val} ≃
      {q : Q // rho.val * Y < rho.val * (sIntegerOrbitNorm K S Γ q).val} :=
    Equiv.subtypeEquivRight fun q => (mul_lt_mul_iff_right₀ rho.property).symm
  let f := fun q : {q : Q // rho.val * Y < rho.val * (sIntegerOrbitNorm K S Γ q).val} =>
    w q.val * sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
      ⟨rho.val * (sIntegerOrbitNorm K S Γ q.val).val,
        mul_pos rho.property (sIntegerOrbitNorm K S Γ q.val).property⟩
  have hs' : Summable (fun q => f (e q)) := e.summable_iff.mpr hs
  refine ⟨hs', ?_⟩
  change ‖∑' q, f (e q)‖ ≤ _
  rw [e.tsum_eq f]
  apply hb.trans
  have hp : 0 ≤ W * C * SchwartzMap.seminorm ℂ M 0 φ := by positivity
  calc
    _ = (W * C * SchwartzMap.seminorm ℂ M 0 φ) *
        ((1 + rho.val⁻¹) * (rho.val * Y) ^ (1 - A)) := by ring
    _ ≤ (W * C * SchwartzMap.seminorm ℂ M 0 φ) * (2 * Z ^ (-saving)) :=
      mul_le_mul_of_nonneg_left (tail_scale_bound Z B tau saving A rho.val
        hZ hB htau hA hrho horder) hp
    _ = _ := by ring

end HeckeSkeleton.Moments.MOM_INV_STEP.OuterFrequencyTail

end
