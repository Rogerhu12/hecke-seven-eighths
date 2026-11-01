import HeckeSkeleton.LowEnergy.MellinEnergy
import HeckeSkeleton.LowEnergy.HybridScaling

/-!
# Integrating the actual ideal hybrid estimate against one common profile

The only energy hypotheses are the two original arbitrary-coefficient
large sieves. Each Mellin mode has coefficients depending on the correct
variables only. The common density is integrated after the full marked row
has been formed, and the small kernel scalar is retained before squaring.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.MellinHybrid

open NumberField Ideal MeasureTheory
open HeckeSkeleton.LowEnergy.KeepOriginalRow
open HeckeSkeleton.LowEnergy.IdealCanonicalColumns
open HeckeSkeleton.LowEnergy.HybridScaling
open scoped NumberField Classical BigOperators

variable {K : Type} [Field K] [NumberField K]

theorem continuous_mode_row
    (cubic quad : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (ps ns bs : Finset (Ideal (𝓞 K)))
    (a r : ℝ → Ideal (𝓞 K) → ℂ)
    (beta : ℝ → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (ha : ∀ P, Continuous (fun t => a t P))
    (hr : ∀ k, Continuous (fun t => r t k))
    (hbeta : ∀ n b, Continuous (fun t => beta t n b)) (k : Ideal (𝓞 K)) :
    Continuous (fun t => r t k * hybridRow cubic quad ps ns bs (a t) (beta t) k) := by
  apply (hr k).mul
  unfold hybridRow
  apply continuous_finset_sum
  intro P hP
  apply (((ha P).div_const _).mul_const _).mul
  unfold hybridInner
  apply continuous_finset_sum
  intro n hn
  apply continuous_finset_sum
  intro b hb
  exact (((hbeta n b).mul_const _).mul_const _).mul_const _

/-- Uniform four-scale integrated hybrid inequality. All constants precede
the scales, supports, profile, retained row factor and both coefficient arrays. -/
theorem integrated_hybrid_energy
    (Ext : Ideal (𝓞 K) → Prop)
    (hext_ne : ∀ I, Ext I → I ≠ ⊥)
    (hext_mul : ∀ I J, Ext I → Ext J → Ext (I * J))
    (hext_dvd : ∀ I J, Ext I → J ∣ I → Ext J)
    (cubic quad : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hκ : CubicKernelAxioms Ext cubic)
    (hsquare : ∀ k c m h t, Ext k → Ext c → Ext t →
      quad k ((c * m) * ((c * h) * t ^ 2)) = mask k (c * t) * quad k (m * h))
    (hquadratic : IdealQuadraticInput Ext quad)
    (hcubic : IdealCubicInput Ext cubic)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ K0 N0 B0 L0 : ℝ,
      1 ≤ K0 → 1 ≤ N0 → 1 ≤ B0 → 1 ≤ L0 →
      ∀ rows ns bs ps : Finset (Ideal (𝓞 K)),
      (∀ k ∈ rows, Ext k ∧ Squarefree k ∧ (Ideal.absNorm k : ℝ) ≤ K0) →
      (∀ n ∈ ns, Ext n ∧ Squarefree n ∧ (Ideal.absNorm n : ℝ) ≤ N0) →
      (∀ b ∈ bs, Ext b ∧ (Ideal.absNorm b : ℝ) ≤ B0) →
      (∀ P ∈ ps, Ext P ∧ Squarefree P ∧ (Ideal.absNorm P : ℝ) ≤ L0) →
      ∀ (rho : ℝ → ℂ) (a r : ℝ → Ideal (𝓞 K) → ℂ)
        (beta : ℝ → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ),
      Continuous rho → Integrable (fun t => ‖rho t‖) →
      (∀ P, Continuous (fun t => a t P)) →
      (∀ k, Continuous (fun t => r t k)) →
      (∀ n b, Continuous (fun t => beta t n b)) →
      ∀ A B R s : ℝ, 0 < A → 0 < B → 0 ≤ R →
      (∀ t P, P ∈ ps → ‖a t P‖ ≤ A) →
      (∀ t n, n ∈ ns → ∀ b, b ∈ bs → ‖beta t n b‖ ≤ B) →
      (∀ t k, k ∈ rows → ‖r t k‖ ≤ R) →
      (∑ k ∈ rows, ‖(s : ℂ) * ∫ t : ℝ,
        rho t * (r t k * hybridRow cubic quad ps ns bs (a t) (beta t) k)‖ ^ 2) ≤
        s ^ 2 * (∫ t : ℝ, ‖rho t‖) ^ 2 * (R * A * B) ^ 2 *
          C * (K0 * N0 * B0 * L0) ^ eps * (K0 + N0 * B0) * B0 *
          (N0 + L0 + (N0 * L0) ^ (2 / 3 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := raw_hybrid_energy_with_amplitudes
    Ext hext_ne hext_mul hext_dvd cubic quad hκ hsquare hquadratic hcubic eps heps
  refine ⟨C, hC, ?_⟩
  intro K0 N0 B0 L0 hK hN hB hL rows ns bs ps hrows hn hb hp
    rho a r beta hrho hint ha_cont hr_cont hbeta_cont A B R s hA hBamp hR ha hbeta hr
  let E : ℝ := (R * A * B) ^ 2 * C * (K0 * N0 * B0 * L0) ^ eps *
    (K0 + N0 * B0) * B0 * (N0 + L0 + (N0 * L0) ^ (2 / 3 : ℝ))
  have hE : 0 ≤ E := by
    dsimp [E]
    have hK0 : 0 ≤ K0 := zero_le_one.trans hK
    have hN0 : 0 ≤ N0 := zero_le_one.trans hN
    have hB0 : 0 ≤ B0 := zero_le_one.trans hB
    have hL0 : 0 ≤ L0 := zero_le_one.trans hL
    positivity
  have hmode (t : ℝ) :
      (∑ k ∈ rows, ‖r t k * hybridRow cubic quad ps ns bs (a t) (beta t) k‖ ^ 2) ≤ E :=
    hbound K0 N0 B0 L0 hK hN hB hL rows ns bs ps hrows hn hb hp
      (a t) (r t) (beta t) A B R hA hBamp hR (ha t) (hbeta t) (hr t)
  have h := MellinEnergy.finite_rows_common_profile_scalar rows s rho
    (fun t k => r t k * hybridRow cubic quad ps ns bs (a t) (beta t) k) E
    hrho (continuous_mode_row cubic quad ps ns bs a r beta ha_cont hr_cont hbeta_cont)
    hint hE hmode
  apply h.trans_eq
  dsimp [E]
  ring

#print axioms continuous_mode_row
#print axioms integrated_hybrid_energy

end HeckeSkeleton.LowEnergy.MellinHybrid
