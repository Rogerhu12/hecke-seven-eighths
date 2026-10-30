import HeckePort.Moments.Descent.IdealMasks
import HeckePort.CenteredMoment.Generator

/-!
# Marked completed sums

Port of the generic part of openai/math `OAI/NumberTheory/DirichletL/Descent/Completion.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`.

In openai `markedCompletedT Ψ W X d = ∑' I J, summand Ψ W X I J * d (I * J^3)`, where
`summand Ψ W X I J` is the completed-cube summand of `GaussSum/CompletedExpansion` (a specific
function of the Hecke character, the test function `W` and the scale `X`).  Here the summand is an
arbitrary `s : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ` with the three properties openai uses
(`CompletedSummand`: vanishing at the zero ideal, finite support, the content of
`summand_zero_left/right` and `completedT_finite_support`).  Ported: `markedCompletedT`,
its congruence, summability, `tsum` form, linearity and `markedCompletedT_prime_priority`
(the mark-priority expansion), and `markedCompletedT_congr_exterior` (the analogue of
`markedCompletedT_congr_primary`, with exteriority replacing "the primary generator is nonzero").

Not ported: `markedExpandedTerm_*`, `weighted_markedCompletedT_reopen`, `marked_cube_inner_inverse`,
`marked_cube_inverse_vstar`, `marked_cube_inverse`.  They unfold the specific
`expandedTerm`/`cubeWeight`/`Vstar`/`columnWeight` of the cubic completed expansion and use
`ideal_cube_convolution`; they belong with the theta-reflection machinery, not S0.
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators
open HeckePort.IdealMobiusDivisorSum HeckePort.CenteredMomentGenerator

variable {K : Type} [Field K] [NumberField K]

/-- openai `markedCompletedT`, for an abstract summand. -/
def markedCompletedT (s : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (d : Ideal (𝓞 K) → ℂ) : ℂ :=
  ∑' I : Ideal (𝓞 K), ∑' J : Ideal (𝓞 K), s I J * d (I * J ^ 3)

/-- The properties of the completed summand used by openai. -/
structure CompletedSummand (s : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) : Prop where
  zero_left : ∀ J, s ⊥ J = 0
  zero_right : ∀ I, s I ⊥ = 0
  finite_support : (Function.support (fun p : Ideal (𝓞 K) × Ideal (𝓞 K) => s p.1 p.2)).Finite

variable {s : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ}

theorem markedCompletedT_one (hs : CompletedSummand s) :
    markedCompletedT s (fun _ => 1) = ∑' I, ∑' J, s I J := by
  simp only [markedCompletedT, mul_one]

theorem markedCompletedT_congr_nonzero (hs : CompletedSummand s)
    (d e : Ideal (𝓞 K) → ℂ) (h : ∀ A ≠ ⊥, d A = e A) :
    markedCompletedT s d = markedCompletedT s e := by
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  by_cases hI : I = ⊥
  · simp only [hI, hs.zero_left, zero_mul]
  by_cases hJ : J = ⊥
  · simp only [hJ, hs.zero_right, zero_mul]
  rw [h (I * J ^ 3) (mul_ne_zero hI (pow_ne_zero 3 hJ))]

theorem markedCompletedT_summable (hs : CompletedSummand s) (d : Ideal (𝓞 K) → ℂ) :
    Summable (fun p : Ideal (𝓞 K) × Ideal (𝓞 K) => s p.1 p.2 * d (p.1 * p.2 ^ 3)) := by
  apply summable_of_finite_support
  apply hs.finite_support.subset
  intro p hp hz
  exact hp (by simp only [hz, zero_mul])

theorem markedCompletedT_eq_tsum (hs : CompletedSummand s) (d : Ideal (𝓞 K) → ℂ) :
    markedCompletedT s d = ∑' p : Ideal (𝓞 K) × Ideal (𝓞 K),
      s p.1 p.2 * d (p.1 * p.2 ^ 3) :=
  (markedCompletedT_summable hs d).tsum_prod.symm

theorem markedCompletedT_const_mul (c : ℂ) (d : Ideal (𝓞 K) → ℂ) :
    markedCompletedT s (fun A => c * d A) = c * markedCompletedT s d := by
  simp only [markedCompletedT, mul_left_comm _ c, tsum_mul_left]

theorem markedCompletedT_finset_sum {ι : Type*} (hs : CompletedSummand s) (t : Finset ι)
    (d : ι → Ideal (𝓞 K) → ℂ) :
    markedCompletedT s (fun A => ∑ i ∈ t, d i A) =
      ∑ i ∈ t, markedCompletedT s (d i) := by
  simp only [markedCompletedT_eq_tsum hs, Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun i _ => markedCompletedT_summable hs (d i))

theorem markedCompletedT_prime_priority {σ : Type*} [DecidableEq σ] (hs : CompletedSummand s)
    (slots : Finset σ) (L : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ) (H : Ideal (𝓞 K)) (hH : H ≠ ⊥) :
    markedCompletedT s
      (fun A => primeMark slots L a (primeSupport (H ^ 3 * A))) =
    ∑ J ∈ slots.powerset,
      primeMark J L a (primeSupport H) *
        markedCompletedT s (fun A =>
          primeMark (slots \ J)
            (fun i => L i \ primeSupport H) a
            (primeSupport A)) := by
  have hmark (A : Ideal (𝓞 K)) (hA : A ≠ ⊥) :
      primeMark slots L a (primeSupport (H ^ 3 * A)) =
      ∑ J ∈ slots.powerset,
        primeMark J L a (primeSupport H) *
          primeMark (slots \ J)
            (fun i => L i \ primeSupport H) a
            (primeSupport A) := by
    rw [mul_comm (H ^ 3) A, ideal_primeSupport_mul_cube A H hA hH,
      Finset.union_comm, primeMark_priority]
    simp only [primeMark_residual_lists]
  rw [markedCompletedT_congr_nonzero hs _ _ hmark,
    markedCompletedT_finset_sum hs slots.powerset]
  simp only [markedCompletedT_const_mul]

/-- openai `markedCompletedT_congr_primary`: the summand is supported on products whose primary
generator is nonzero; over a general field this is exteriority.  The support hypothesis is the
content of openai's `completed_summand_primary_support`. -/
theorem markedCompletedT_congr_exterior (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (d e : Ideal (𝓞 K) → ℂ)
    (hsupp : ∀ I J, s I J ≠ 0 → IsExterior K S (I * J ^ 3))
    (h : ∀ A, IsExterior K S A → d A = e A) :
    markedCompletedT s d = markedCompletedT s e := by
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  by_cases hz : s I J = 0
  · simp only [hz, zero_mul]
  · rw [h (I * J ^ 3) (hsupp I J hz)]

end HeckePort.Moments

end
