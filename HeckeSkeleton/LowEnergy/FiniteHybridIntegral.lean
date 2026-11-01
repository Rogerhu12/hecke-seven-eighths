import HeckeSkeleton.LowEnergy.MellinEnergy
import HeckeSkeleton.LowEnergy.IdealCanonicalColumns

/-!
# Exact finite reflected block / common-profile hybrid integral

This is a linear identity before any row norm is taken.  Integrability is
proved from continuity and uniform mode bounds against the common L1
profile.  The fixed ideal kernels may be arbitrary: their finitely many
norms are retained in an explicit integrable majorant.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.FiniteHybridIntegral
open NumberField Ideal MeasureTheory
open HeckeSkeleton.LowEnergy.KeepOriginalRow
open HeckeSkeleton.LowEnergy.IdealCanonicalColumns
open scoped NumberField Classical BigOperators

variable {K : Type} [Field K] [NumberField K]

/-- Every non-Mellin factor of one literal raw hybrid summand. -/
def hybridKernel (κ q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (k P n b : Ideal (𝓞 K)) : ℂ :=
  (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)⁻¹ * mask k P *
    q k (n * b) * κ P n * mask P b

theorem hybridRow_expansion
    (κ q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (ps ns bs : Finset (Ideal (𝓞 K)))
    (a : Ideal (𝓞 K) → ℂ) (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (r : ℂ) (k : Ideal (𝓞 K)) :
    r * hybridRow κ q ps ns bs a beta k =
      ∑ P ∈ ps, ∑ n ∈ ns, ∑ b ∈ bs,
        r * a P * beta n b * hybridKernel κ q k P n b := by
  unfold hybridRow hybridInner
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P _
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro b _
  simp only [hybridKernel, mask, div_eq_mul_inv]
  ring

/-- Interchange all three actual finite ideal sums with one common profile
integral.  Every occurrence of the row factor remains inside that integral. -/
theorem hybrid_integral_identity
    (κ q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (ps ns bs : Finset (Ideal (𝓞 K)))
    (rho r : ℝ → ℂ) (a : ℝ → Ideal (𝓞 K) → ℂ)
    (beta : ℝ → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (k : Ideal (𝓞 K))
    (hrho : Continuous rho) (hint : Integrable (fun t => ‖rho t‖))
    (hr : Continuous r) (ha : ∀ P, Continuous (fun t => a t P))
    (hbeta : ∀ n b, Continuous (fun t => beta t n b))
    (R : ℝ) (A : Ideal (𝓞 K) → ℝ) (B : Ideal (𝓞 K) → Ideal (𝓞 K) → ℝ)
    (hrbound : ∀ t, ‖r t‖ ≤ R)
    (habound : ∀ P ∈ ps, ∀ t, ‖a t P‖ ≤ A P)
    (hbetabound : ∀ n ∈ ns, ∀ b ∈ bs, ∀ t, ‖beta t n b‖ ≤ B n b) :
    (∑ P ∈ ps, ∑ n ∈ ns, ∑ b ∈ bs,
      ∫ t : ℝ, rho t *
        (r t * a t P * beta t n b * hybridKernel κ q k P n b)) =
      ∫ t : ℝ, rho t * (r t * hybridRow κ q ps ns bs (a t) (beta t) k) := by
  let f : (Ideal (𝓞 K) × Ideal (𝓞 K) × Ideal (𝓞 K)) → ℝ → ℂ :=
    fun d t => r t * a t d.1 * beta t d.2.1 d.2.2 *
      hybridKernel κ q k d.1 d.2.1 d.2.2
  let C : (Ideal (𝓞 K) × Ideal (𝓞 K) × Ideal (𝓞 K)) → ℝ :=
    fun d => R * A d.1 * B d.2.1 d.2.2 * ‖hybridKernel κ q k d.1 d.2.1 d.2.2‖
  have hcont (d : Ideal (𝓞 K) × Ideal (𝓞 K) × Ideal (𝓞 K)) : Continuous (f d) :=
    (((hr.mul (ha d.1)).mul (hbeta d.2.1 d.2.2)).mul_const _)
  have hbound : ∀ d ∈ ps ×ˢ (ns ×ˢ bs), ∀ t, ‖f d t‖ ≤ C d := by
    intro d hd t
    obtain ⟨hP, hnb⟩ := Finset.mem_product.mp hd
    obtain ⟨hn, hb⟩ := Finset.mem_product.mp hnb
    have hR0 : 0 ≤ R := (norm_nonneg _).trans (hrbound t)
    have hA0 : 0 ≤ A d.1 := (norm_nonneg _).trans (habound d.1 hP t)
    have hra := mul_le_mul (hrbound t) (habound d.1 hP t) (norm_nonneg _) hR0
    have hrab := mul_le_mul hra (hbetabound d.2.1 hn d.2.2 hb t)
      (norm_nonneg _) (mul_nonneg hR0 hA0)
    simpa only [f, C, norm_mul] using
      mul_le_mul_of_nonneg_right hrab (norm_nonneg (hybridKernel κ q k d.1 d.2.1 d.2.2))
  have hsum := MellinEnergy.finite_sum_profile_integral (ps ×ˢ (ns ×ˢ bs))
    rho f C hrho (fun d _ => hcont d) hint hbound
  calc
    (∑ P ∈ ps, ∑ n ∈ ns, ∑ b ∈ bs,
        ∫ t : ℝ, rho t *
          (r t * a t P * beta t n b * hybridKernel κ q k P n b)) =
        ∫ t : ℝ, rho t *
          ∑ P ∈ ps, ∑ n ∈ ns, ∑ b ∈ bs,
            r t * a t P * beta t n b * hybridKernel κ q k P n b := by
      simpa only [Finset.sum_product, f] using hsum
    _ = ∫ t : ℝ, rho t * (r t * hybridRow κ q ps ns bs (a t) (beta t) k) := by
      congr 1
      funext t
      rw [← hybridRow_expansion]

/-- Direct adapter for a per-term separated Mellin kernel.  The scalar
survives outside the whole linear row, so later energy bounds square it.
The static coefficient arrays have exactly their original dependencies. -/
theorem separated_kernel_sum_eq_hybrid_integral
    (κ q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (ps ns bs : Finset (Ideal (𝓞 K)))
    (a₀ : Ideal (𝓞 K) → ℂ) (beta₀ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (rho r : ℝ → ℂ) (u : ℝ → Ideal (𝓞 K) → ℂ)
    (v : ℝ → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (kernel : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (scalar : ℂ) (k : Ideal (𝓞 K))
    (hrho : Continuous rho) (hint : Integrable (fun t => ‖rho t‖))
    (hr : Continuous r) (hu : ∀ P, Continuous (fun t => u t P))
    (hv : ∀ n b, Continuous (fun t => v t n b))
    (R : ℝ) (U : Ideal (𝓞 K) → ℝ) (V : Ideal (𝓞 K) → Ideal (𝓞 K) → ℝ)
    (hrbound : ∀ t, ‖r t‖ ≤ R)
    (hubound : ∀ P ∈ ps, ∀ t, ‖u t P‖ ≤ U P)
    (hvbound : ∀ n ∈ ns, ∀ b ∈ bs, ∀ t, ‖v t n b‖ ≤ V n b)
    (hkernel : ∀ P ∈ ps, ∀ n ∈ ns, ∀ b ∈ bs,
      kernel P n b = scalar * ∫ t : ℝ, rho t * (r t * u t P * v t n b)) :
    (∑ P ∈ ps, ∑ n ∈ ns, ∑ b ∈ bs,
      a₀ P * beta₀ n b * hybridKernel κ q k P n b * kernel P n b) =
      scalar * ∫ t : ℝ, rho t * (r t * hybridRow κ q ps ns bs
        (fun P => a₀ P * u t P) (fun n b => beta₀ n b * v t n b) k) := by
  have hmain := hybrid_integral_identity κ q ps ns bs rho r
    (fun t P => a₀ P * u t P) (fun t n b => beta₀ n b * v t n b) k
    hrho hint hr (fun P => (hu P).const_mul _) (fun n b => (hv n b).const_mul _)
    R (fun P => ‖a₀ P‖ * U P) (fun n b => ‖beta₀ n b‖ * V n b) hrbound
    (fun P hP t => by
      simpa only [norm_mul] using mul_le_mul_of_nonneg_left (hubound P hP t) (norm_nonneg (a₀ P)))
    (fun n hn b hb t => by
      simpa only [norm_mul] using
        mul_le_mul_of_nonneg_left (hvbound n hn b hb t) (norm_nonneg (beta₀ n b)))
  rw [← hmain]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro b hb
  rw [hkernel P hP n hn b hb]
  calc
    a₀ P * beta₀ n b * hybridKernel κ q k P n b *
        (scalar * ∫ t : ℝ, rho t * (r t * u t P * v t n b)) =
        scalar * ∫ t : ℝ,
          (a₀ P * beta₀ n b * hybridKernel κ q k P n b) *
            (rho t * (r t * u t P * v t n b)) := by
      rw [integral_const_mul]
      ring
    _ = scalar * ∫ t : ℝ, rho t *
        (r t * (a₀ P * u t P) * (beta₀ n b * v t n b) * hybridKernel κ q k P n b) := by
      congr 1
      congr 1
      funext t
      ring

#print axioms hybrid_integral_identity
#print axioms separated_kernel_sum_eq_hybrid_integral

end HeckeSkeleton.LowEnergy.FiniteHybridIntegral
