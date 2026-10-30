import CubicSieve.AnalyticGrowth
import CubicSieve.AnalyticDecay

/-!
The actual unrestricted-ideal dual norm. It is a matrix of the same kernel:
rows retain all ideal cube factors and columns remain squarefree. Its growth
is proved by cubic extraction from the current squarefree bootstrap bound.
-/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.AnalyticDualNorm

open NumberField IsDedekindDomain
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open CubicSieve.ExteriorKernel
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

theorem finite_full_cutoff (M : ℝ) :
    {I : ExteriorIdeal K S | exteriorNorm K S I ≤ M}.Finite :=
  ((DedekindZetaZeroFree.LargeSieve.finite_ideals_absNorm_le K M).preimage
    (ExteriorSieve.underlyingIdeal_injective K S).injOn).subset (fun _ hI => hI)

def fullCutoff (M : ℝ) : Finset (ExteriorIdeal K S) := (finite_full_cutoff K S M).toFinset

@[simp] theorem mem_fullCutoff (M : ℝ) (I : ExteriorIdeal K S) :
    I ∈ fullCutoff K S M ↔ exteriorNorm K S I ≤ M := Set.Finite.mem_toFinset _

def U (M N : ℝ) : ℝ :=
  ‖FiniteKernel.operator (fullCutoff K S M) (ExteriorSieve.cutoff K S N)
    (positiveKernel K S D)‖ ^ 2

theorem U_nonneg (M N : ℝ) : 0 ≤ U K S D M N := sq_nonneg _

theorem cutoff_bound (M N : ℝ) :
    FiniteKernel.HasBound (fullCutoff K S M) (ExteriorSieve.cutoff K S N)
      (positiveKernel K S D) (U K S D M N) :=
  (FiniteKernel.hasBound_iff_norm_sq_le _ _ _ _ (U_nonneg K S D M N)).mpr le_rfl

theorem family_bound (M N : ℝ) (R T : Finset (ExteriorIdeal K S))
    (hR : ∀ I ∈ R, exteriorNorm K S I ≤ M)
    (hT : ∀ j ∈ T, Squarefree j.val.val ∧ exteriorNorm K S j ≤ N) :
    FiniteKernel.HasBound R T (positiveKernel K S D) (U K S D M N) :=
  FiniteKernel.restrict_bound (fullCutoff K S M) R (ExteriorSieve.cutoff K S N) T
    (fun I hI => (mem_fullCutoff K S M I).mpr (hR I hI))
    (fun j hj => (ExteriorSieve.mem_cutoff K S N j).mpr (hT j hj))
    (positiveKernel K S D) (U K S D M N) (U_nonneg K S D M N) (cutoff_bound K S D M N)

theorem B_le_U (M N : ℝ) : ExteriorSieve.B K S D M N ≤ U K S D M N := by
  apply (FiniteKernel.hasBound_iff_norm_sq_le _ _ _ _ (U_nonneg K S D M N)).mp
  exact family_bound K S D M N (ExteriorSieve.cutoff K S M) (ExteriorSieve.cutoff K S N)
    (fun I hI => ((ExteriorSieve.mem_cutoff K S M I).mp hI).2)
    (fun j hj => (ExteriorSieve.mem_cutoff K S N j).mp hj)

theorem U_growth (hD : AllowedGeneratorInput K S D) {ξ : ℝ}
    (h : Bootstrap.HasCubicExponent (ExteriorSieve.B K S D) ξ)
    (hξ : (4 / 3 : ℝ) ≤ ξ) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      U K S D M N ≤ A * (M * N) ^ ε * (M ^ (1 / 3 : ℝ) * N + M ^ ξ) := by
  obtain ⟨A, hA, hb⟩ := AnalyticGrowth.full_ideal_growth K S D hD h hξ ε hε
  refine ⟨A, hA, ?_⟩
  intro M N hM hN
  have hnonneg : 0 ≤ A * (M * N) ^ ε * (M ^ (1 / 3 : ℝ) * N + M ^ ξ) := by positivity
  apply (FiniteKernel.hasBound_iff_norm_sq_le _ _ _ _ hnonneg).mp
  intro z
  have hh := hb M N hM hN (fullCutoff K S M) (ExteriorSieve.cutoff K S N)
    (fun I hI => (mem_fullCutoff K S M I).mp hI)
    (fun j hj => (ExteriorSieve.mem_cutoff K S N j).mp hj) z
  simpa only [FiniteKernel.form, FiniteKernel.energy, ExteriorKernel.energy,
    ExteriorKernel.rowSum, mul_comm] using hh

/-- Genuine summability and the correct low-radius weighted dual growth.
The fixed singularity exponent is less than the cubic exponent one third. -/
theorem weighted_dual_growth (hD : AllowedGeneratorInput K S D) {ξ : ℝ}
    (h : Bootstrap.HasCubicExponent (ExteriorSieve.B K S D) ξ)
    (hξ : (4 / 3 : ℝ) ≤ ξ) (hξ2 : ξ ≤ 2) (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ < 1 / 2) :
    ∃ A : ℝ, 0 < A ∧ ∀ N t : ℝ, 1 ≤ N → 0 < t →
      Summable (AnalyticDecay.weightedTerm (fun M => U K S D M N) t (1 / 6)) ∧
        (∑' j : ℕ, AnalyticDecay.weightedTerm (fun M => U K S D M N) t (1 / 6) j) ≤
          A * N ^ δ *
            (N * AnalyticDecay.decayConstant (1 / 3 + δ - 1 / 6) * t ^ (-(1 / 3 + δ)) +
              AnalyticDecay.decayConstant (ξ + δ - 1 / 6) * t ^ (-(ξ + δ))) := by
  obtain ⟨A, hA, hb⟩ := U_growth K S D hD h hξ δ hδ
  refine ⟨A, hA, ?_⟩
  intro N t hN ht
  exact AnalyticDecay.weighted_sieve_growth_majorant (fun M => U K S D M N)
    A N t δ ξ (1 / 6) hA.le (by linarith) ht
    (by linarith) (by linarith) (by linarith) (by linarith)
    (fun M _ => U_nonneg K S D M N)
    (fun M hM => by simpa only [mul_comm] using hb M N hM hN)

/-- The weighted Poisson tail of the actual dual operator follows from extraction growth. -/
theorem weighted_poisson_tail (hD : AllowedGeneratorInput K S D) {ξ : ℝ}
    (h : Bootstrap.HasCubicExponent (ExteriorSieve.B K S D) ξ)
    (hξ : (4 / 3 : ℝ) ≤ ξ) (hξ2 : ξ ≤ 2) (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ < 1 / 2) :
    ∃ A : ℝ, 0 < A ∧ ∀ M N : ℝ, 0 < M → 1 ≤ N →
      (M / N) * (∑' j : ℕ,
        AnalyticDecay.weightedTerm (fun L => U K S D L N) (M / N ^ 2) (1 / 6) j) ≤
          A * N ^ (3 * δ) * M ^ (-δ) *
            (AnalyticDecay.decayConstant (1 / 3 + δ - 1 / 6) * (M * N) ^ (2 / 3 : ℝ) +
              AnalyticDecay.decayConstant (ξ + δ - 1 / 6) *
                M ^ (1 - ξ) * N ^ (2 * ξ - 1)) := by
  obtain ⟨A, hA, hb⟩ := U_growth K S D hD h hξ δ hδ
  refine ⟨A, hA, ?_⟩
  intro M N hM hN
  exact AnalyticDecay.weighted_sieve_poisson_bound (fun L => U K S D L N)
    A M N δ ξ (1 / 6) hA.le hM (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)
    (fun L _ => U_nonneg K S D L N)
    (fun L hL => by simpa only [mul_comm] using hb L N hL hN)

end CubicSieve.AnalyticDualNorm
