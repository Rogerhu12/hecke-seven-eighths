import HeckeSkeleton.Moments.MOM_INV_STEP.OuterFrequencyTail

/-!
# Genuine tails for cutoffs frozen at an arithmetic source slice

The bare cutoff may depend on the already frozen extraction and mask
divisor. It remains independent of the residual column pair and sector.
Only its actual large-argument inclusion and a common radius lower bound
are used. In particular, the bare cutoff is not required to be at least
one and is not replaced by a larger global source ball.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.AdaptiveFrequencyTail

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis MeasureTheory
open scoped Classical nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
local notation "Q" => SIntegerOrbits K S Γ
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

theorem scale_bound (Z B tau saving A rho H : ℝ)
    (hZ : 1 ≤ Z) (hB : 0 ≤ B) (hA : 1 < A)
    (hrho : Z ^ (-B) ≤ rho) (hcut : Z ^ tau ≤ rho * H)
    (horder : B + tau * (1 - A) ≤ -saving) :
    (1 + rho⁻¹) * (rho * H) ^ (1 - A) ≤ 2 * Z ^ (-saving) := by
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hr : 0 < rho := (Real.rpow_pos_of_pos hZpos _).trans_le hrho
  have hinv : rho⁻¹ ≤ Z ^ B := by
    calc
      _ ≤ (Z ^ (-B))⁻¹ := (inv_le_inv₀ hr (Real.rpow_pos_of_pos hZpos _)).mpr hrho
      _ = _ := by rw [← Real.rpow_neg hZpos.le, neg_neg]
  have hfirst : 1 + rho⁻¹ ≤ 2 * Z ^ B := by
    have hh := Real.one_le_rpow hZ hB
    linarith
  have hsecond : (rho * H) ^ (1 - A) ≤ Z ^ (tau * (1 - A)) := by
    rw [Real.rpow_mul hZpos.le]
    exact Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hZpos _) hcut (by linarith)
  calc
    _ ≤ (2 * Z ^ B) * Z ^ (tau * (1 - A)) :=
      mul_le_mul hfirst hsecond
        (Real.rpow_nonneg ((Real.rpow_pos_of_pos hZpos _).trans_le hcut).le _) (by positivity)
    _ = 2 * Z ^ (B + tau * (1 - A)) := by rw [mul_assoc, ← Real.rpow_add hZpos]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ horder) (by norm_num)

/-- One decay order and one constant are chosen before the actual
radius, the fine bare cutoff, all Fourier coefficients and the base. -/
theorem exists_tail_bound
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (Rmax tauMin savingMax : ℝ) (hRmax : 0 ≤ Rmax)
    (htauMin : 0 < tauMin) (hsavingMax : 0 ≤ savingMax) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : SchwartzMap V ℂ,
      ∀ (Z tau saving H : ℝ) (rho : {r : ℝ // 0 < r}),
      1 ≤ Z → tauMin ≤ tau → 0 ≤ saving → saving ≤ savingMax →
      Z ^ (-Rmax) ≤ rho.val → Z ^ tau ≤ rho.val * H →
      ∀ (w : Q → ℂ) (W : ℝ), 0 ≤ W → (∀ q, ‖w q‖ ≤ W) →
        let f := fun q : {q : Q // H < (sIntegerOrbitNorm K S Γ q).val} =>
          w q.val * sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
            ⟨rho.val * (sIntegerOrbitNorm K S Γ q.val).val,
              mul_pos rho.property (sIntegerOrbitNorm K S Γ q.val).property⟩
        Summable f ∧ ‖∑' q, f q‖ ≤
          W * C * SchwartzMap.seminorm ℂ m 0 φ * Z ^ (-saving) := by
  obtain ⟨A, hA, horder⟩ := OuterFrequencyTail.exists_tail_order
    Rmax tauMin savingMax hRmax htauMin hsavingMax
  let L := traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  let m : ℕ := Module.finrank ℤ L + ⌈(Module.finrank ℚ K : ℝ) * A⌉₊ + 1
  have hm : Module.finrank ℤ L < m := by dsimp only [m]; omega
  have hmorder : (Module.finrank ℚ K : ℝ) * A ≤ m := by
    have hc := Nat.le_ceil ((Module.finrank ℚ K : ℝ) * A)
    have hn : ⌈(Module.finrank ℚ K : ℝ) * A⌉₊ ≤ m := by dsimp only [m]; omega
    exact hc.trans (by exact_mod_cast hn)
  obtain ⟨C, hC, htail⟩ := exists_sIntegerSchwartzProfile_weighted_tail_bound
    K S Γ ψ hψ hψsupport A hA m hm hmorder
  refine ⟨m, 2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro φ Z tau saving H rho hZ htau hsaving hsave hρ hcut w W hW hw
  dsimp only
  have hτ : 0 ≤ tau := htauMin.le.trans htau
  have hH : 1 ≤ rho.val * H := (Real.one_le_rpow hZ hτ).trans hcut
  obtain ⟨hs, hb⟩ := htail φ rho (rho.val * H) hH w W hW hw
  let e : {q : Q // H < (sIntegerOrbitNorm K S Γ q).val} ≃
      {q : Q // rho.val * H < rho.val * (sIntegerOrbitNorm K S Γ q).val} :=
    Equiv.subtypeEquivRight fun q => (mul_lt_mul_iff_right₀ rho.property).symm
  let f := fun q : {q : Q // rho.val * H < rho.val * (sIntegerOrbitNorm K S Γ q).val} =>
    w q.val * sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
      ⟨rho.val * (sIntegerOrbitNorm K S Γ q.val).val,
        mul_pos rho.property (sIntegerOrbitNorm K S Γ q.val).property⟩
  have hs' : Summable (fun q => f (e q)) := e.summable_iff.mpr hs
  refine ⟨hs', ?_⟩
  change ‖∑' q, f (e q)‖ ≤ _
  rw [e.tsum_eq f]
  have hcurrent : Rmax + tau * (1 - A) ≤ -saving :=
    (add_le_add_left (mul_le_mul_of_nonpos_right htau (by linarith)) Rmax).trans
      (horder.trans (neg_le_neg hsave))
  apply hb.trans
  calc
    _ = (W * C * SchwartzMap.seminorm ℂ m 0 φ) *
        ((1 + rho.val⁻¹) * (rho.val * H) ^ (1 - A)) := by ring
    _ ≤ (W * C * SchwartzMap.seminorm ℂ m 0 φ) * (2 * Z ^ (-saving)) :=
      mul_le_mul_of_nonneg_left
        (scale_bound Z Rmax tau saving A rho.val H hZ hRmax hA hρ hcut hcurrent)
        (by positivity)
    _ = _ := by ring

end HeckeSkeleton.Moments.MOM_INV_STEP.AdaptiveFrequencyTail

end

