import ActualTraceProductFourierDilation
import ActualTraceProductResidueQuotient
import ActualNormalizedLatticeMask

/-!
UNCOMPILED candidate. The actual mean-zero periodic two-column Poisson sum
has a uniform high-decay bound, after deriving the N^2 Jacobian and canceling
the true quotient cardinal against the true period-lattice covolume.
The only weight premises are its pointwise magnitude and complete mean zero.
The arithmetic Gram coefficient still has to be transported to this weight,
and the small-scale/trivial branch and orbital seminorms remain separate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeGeneral.Analysis.ActualMeanZeroProductPoissonDraft

open NumberField IsDedekindDomain MeasureTheory HeckeGeneral.Arithmetic
open ActualTraceProductFourierDilationDraft ActualTraceProductResidueQuotientDraft
open ActualNormalizedLatticeMaskDraft ActualIdealProductPolarMassDraft
open scoped Classical BigOperators FourierTransform nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
local notation "W" => traceProductSpace K
local notation "L" => ordinaryProductLattice K

/-- The literal scaled weighted sum; translation is arbitrary. -/
def productPeriodicSum (I : (Ideal (𝓞 K))⁰)
    (w : LatticeQuotient L (integralProductLattice K I) → ℂ)
    (F : SchwartzMap W ℂ) (N : ℝ) (v : W) : ℂ :=
  ∑' l : L, w (latticeQuotientMap L (integralProductLattice K I) l) *
    F ((traceNormScale K N)⁻¹ • (v + l))

/-- Exact mean-zero Poisson formula with normalized coefficients. The
prefactor is N^2/|discr K|; no modulus-norm factor has been suppressed. -/
theorem productPeriodicSum_eq_nonzero (I : (Ideal (𝓞 K))⁰)
    (w : LatticeQuotient L (integralProductLattice K I) → ℂ)
    (hw : ∑ q, w q = 0) (F : SchwartzMap W ℂ)
    (N : ℝ) (hN : 0 < N) (v : W) :
    productPeriodicSum K I w F N v =
      ((N : ℂ) ^ 2 / ((|(discr K : ℝ)| : ℝ) : ℂ)) *
        ∑' m : NonzeroLattice (dualLattice (integralProductLattice K I)),
          𝓕 (F : W → ℂ) (traceNormScale K N •
            ((m : dualLattice (integralProductLattice K I)) : W)) *
            latticePhase v (m : dualLattice (integralProductLattice K I)) *
              normalizedLatticeMaskCoefficient L (integralProductLattice K I) w m := by
  let J := integralProductLattice K I
  let D := dualLattice J
  let T : D → ℂ := fun m => 𝓕 (F : W → ℂ) (traceNormScale K N • (m : W)) *
    latticePhase v m * normalizedLatticeMaskCoefficient L J w m
  have hzero : T 0 = 0 := by
    dsimp only [T]
    rw [normalizedLatticeMaskCoefficient_zero_of_sum_zero L J w hw, mul_zero]
  have hremove : (∑' m : D, T m) = ∑' m : NonzeroLattice D, T m := by
    exact (tsum_subtype_eq_of_support_subset (f := T) (s := {m : D | m ≠ 0})
      (by intro m hm hm0; subst m; exact hm hzero)).symm
  have hcoeff :
      (∑' m : D, 𝓕 (F : W → ℂ) (traceNormScale K N • (m : W)) *
        latticePhase v m * latticeMaskCoefficient L J w m) =
      (Fintype.card (LatticeQuotient L J) : ℂ) * ∑' m : D, T m := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    rw [latticeMaskCoefficient_eq_card_mul_normalized L J w m]
    dsimp only [T]
    ring
  have hratio : (Fintype.card (LatticeQuotient L J) : ℂ) /
      (ZLattice.covolume J : ℂ) = 1 / ((|(discr K : ℝ)| : ℝ) : ℂ) := by
    exact_mod_cast card_div_covolume_traceProductResidueQuotient K I
  have hps := weighted_lattice_poisson_trace_scaled K L J
    (integralProductLattice_le K I) w F N hN v
  change productPeriodicSum K I w F N v = _ at hps
  rw [hcoeff, hremove] at hps
  refine hps.trans ?_
  have hmid : ∀ X : ℂ, (1 / ZLattice.covolume J : ℂ) * (N : ℂ) ^ 2 *
      ((Fintype.card (LatticeQuotient L J) : ℂ) * X) =
      (N : ℂ) ^ 2 * ((Fintype.card (LatticeQuotient L J) : ℂ) /
        (ZLattice.covolume J : ℂ)) * X := fun X => by ring
  rw [hmid, hratio]
  dsimp only [T]
  ring

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

include S Γ in
/-- The actual mean-zero Poisson high-decay estimate. All constants precede
the modulus, weight, test, scale and translation. The bound holds at every
N>0; combining it with the trivial branch is still a separate step. -/
theorem exists_uniform_productPeriodicSum_bound (A : ℕ) (hA : 2 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : (Ideal (𝓞 K))⁰)
      (w : LatticeQuotient L (integralProductLattice K I) → ℂ)
      (F : SchwartzMap W ℂ) (N Q : ℝ), 0 < N → 0 ≤ Q →
      (∀ q, ‖w q‖ ≤ Q) → (∑ q, w q = 0) → ∀ v : W,
        ‖productPeriodicSum K I w F N v‖ ≤
          C * Q * SchwartzMap.seminorm ℂ (Module.finrank ℚ K * A) 0 (𝓕 F) *
            N ^ 2 * ((Ideal.absNorm I.val : ℝ) / N) ^ A := by
  obtain ⟨C, hC, htail⟩ := exists_uniform_idealProduct_normalized_mask_tail K S Γ A hA
  have hd : 0 < |(discr K : ℝ)| := abs_pos.mpr (by
    exact_mod_cast NumberField.discr_ne_zero K)
  refine ⟨C / |(discr K : ℝ)|, div_pos hC hd, fun I w F N Q hN hQ hw hzero v => ?_⟩
  have ht := htail I L w F N Q hN hQ hw v
  have hpref : ‖(N : ℂ) ^ 2 / ((|(discr K : ℝ)| : ℝ) : ℂ)‖ =
      N ^ 2 / |(discr K : ℝ)| := by
    simp only [norm_div, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hN.le, Real.norm_of_nonneg (abs_nonneg _)]
  rw [productPeriodicSum_eq_nonzero K I w hzero F N hN v, norm_mul, hpref]
  calc
    _ ≤ (N ^ 2 / |(discr K : ℝ)|) *
        (C * Q * SchwartzMap.seminorm ℂ (Module.finrank ℚ K * A) 0 (𝓕 F) *
          ((Ideal.absNorm I.val : ℝ) / N) ^ A) :=
      mul_le_mul_of_nonneg_left ht (div_nonneg (sq_nonneg N) hd.le)
    _ = _ := by ring

end HeckeGeneral.Analysis.ActualMeanZeroProductPoissonDraft
