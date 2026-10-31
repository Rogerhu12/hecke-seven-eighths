import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FiniteBranchIndex
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FiniteBranchMass

/-!
# The literal finite arithmetic carrier of the one-pool engine

The main branch and each of the three valuation-error branches retain
both common-support labels, both independent divisor variables and both
complete occurrence allocations. The pool average occurs once. This
carrier is the target of the map from the actual decorated source
leaves; a finite fibre estimate charges the remaining labels without
discarding them from the original sum.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}

abbrev AmplifiedCommonIndex
    (P : PowerScaleExteriorPool A bad Z ell eps)
    (main : TwoDivisorCommonBranch (K := K))
    (error : ℕ → ExteriorPrime A → TwoDivisorCommonBranch (K := K)) :=
  main.Index ⊕
    (Σ n : ({1, 6, 7} : Finset ℕ), Σ p : P.primes, (error n.val p.val).Index)

def amplifiedIndexWeight
    (P : PowerScaleExteriorPool A bad Z ell eps) (M B : ℝ)
    (main : TwoDivisorCommonBranch (K := K))
    (error : ℕ → ExteriorPrime A → TwoDivisorCommonBranch (K := K))
    (i : AmplifiedCommonIndex P main error) : ℝ :=
  (4 / P.rowDensity M B) *
    match i with
    | .inl j => ((M + 6 * ell) / (ell / 2)) * Z ^ ell * main.indexWeight j
    | .inr j => FirstGaussPoolData.localErrorWeight j.2.1.val j.1.val *
        Q j.2.1.val ^ amplifierMovingExponent j.1.val *
          (error j.1.val j.2.1.val).indexWeight j.2.2

theorem amplifiedIndexWeight_nonneg
    (P : PowerScaleExteriorPool A bad Z ell eps) (M B : ℝ)
    (main : TwoDivisorCommonBranch (K := K))
    (error : ℕ → ExteriorPrime A → TwoDivisorCommonBranch (K := K))
    (hZ : 0 ≤ Z) (hell : 0 < ell) (hM : 0 ≤ M)
    (hdensity : 0 ≤ P.rowDensity M B) (i : AmplifiedCommonIndex P main error) :
    0 ≤ amplifiedIndexWeight P M B main error i := by
  apply mul_nonneg (div_nonneg (by norm_num) hdensity)
  cases i with
  | inl j =>
    exact mul_nonneg
      (mul_nonneg (div_nonneg (by positivity) (by positivity))
        (Real.rpow_nonneg hZ ell)) (main.indexWeight_nonneg j)
  | inr j =>
    exact mul_nonneg
      (mul_nonneg (FirstGaussPoolData.localErrorWeight_nonneg _ _)
        (pow_nonneg (by
          change (0 : ℝ) ≤ (Ideal.absNorm j.2.1.val.val.asIdeal : ℝ)
          positivity) _))
      ((error j.1.val j.2.1.val).indexWeight_nonneg j.2.2)

/-- Exact enumeration, with no estimate of a child or of an allocation
count. Every occurrence of the pool density is the same outer one. -/
theorem sum_amplifiedIndexWeight
    (P : PowerScaleExteriorPool A bad Z ell eps) (M B : ℝ)
    (main : TwoDivisorCommonBranch (K := K))
    (error : ℕ → ExteriorPrime A → TwoDivisorCommonBranch (K := K)) :
    (∑ i : AmplifiedCommonIndex P main error, amplifiedIndexWeight P M B main error i) =
      amplifiedCommonBranchMass P M B main error := by
  have herror :
      (∑ j : (Σ n : ({1, 6, 7} : Finset ℕ),
          Σ p : P.primes, (error n.val p.val).Index),
        FirstGaussPoolData.localErrorWeight j.2.1.val j.1.val *
          Q j.2.1.val ^ amplifierMovingExponent j.1.val *
            (error j.1.val j.2.1.val).indexWeight j.2.2) =
        ∑ n ∈ ({1, 6, 7} : Finset ℕ), ∑ p ∈ P.primes,
          FirstGaussPoolData.localErrorWeight p n * Q p ^ amplifierMovingExponent n *
            (error n p).mass := by
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ n : ({1, 6, 7} : Finset ℕ), ∑ p : P.primes,
          FirstGaussPoolData.localErrorWeight p.val n.val *
            Q p.val ^ amplifierMovingExponent n.val * (error n.val p.val).mass := by
        apply Finset.sum_congr rfl
        intro n _
        rw [Fintype.sum_sigma]
        apply Finset.sum_congr rfl
        intro p _
        rw [← Finset.mul_sum, TwoDivisorCommonBranch.sum_indexWeight]
      _ = _ := by simp only [Finset.sum_coe_sort]
  have hthree (f : ℕ → ℝ) :
      (∑ n ∈ ({1, 6, 7} : Finset ℕ), f n) = f 1 + (f 6 + f 7) := by
    simp
  rw [show (∑ i : AmplifiedCommonIndex P main error,
      amplifiedIndexWeight P M B main error i) =
      (4 / P.rowDensity M B) *
        ∑ i : AmplifiedCommonIndex P main error,
          (match i with
          | .inl j => ((M + 6 * ell) / (ell / 2)) * Z ^ ell * main.indexWeight j
          | .inr j => FirstGaussPoolData.localErrorWeight j.2.1.val j.1.val *
              Q j.2.1.val ^ amplifierMovingExponent j.1.val *
                (error j.1.val j.2.1.val).indexWeight j.2.2) by
    simp only [amplifiedIndexWeight, Finset.mul_sum]]
  unfold amplifiedCommonBranchMass
  congr 1
  rw [Fintype.sum_sum_type, ← Finset.mul_sum,
    TwoDivisorCommonBranch.sum_indexWeight, herror, hthree]
  simp only [add_assoc]

/-- The literal finite arithmetic carrier has the already-proved
uniform mass. The constants precede the scale and every moving index. -/
theorem amplified_finite_index_mass
    (N : ℕ) (normBox δ ell eps Mmax Bmax : ℝ)
    (hbox : 0 ≤ normBox) (hδ : 0 < δ)
    (hell : 0 < ell) (heps : 0 < eps) (hepsell : eps < ell)
    (hMmax : 0 ≤ Mmax) (hBmax : 0 ≤ Bmax) :
    ∃ C Z₀ : ℝ, 0 < C ∧ 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
    ∀ bad : Finset (HeightOneSpectrum (𝓞 K)),
    ∀ P : PowerScaleExteriorPool A bad Z ell eps,
    ∀ M B : ℝ, 0 ≤ M → M ≤ Mmax → B ≤ Bmax →
    ∀ s : Ideal (𝓞 K), Squarefree s → s ≠ 0 →
    ∀ main : TwoDivisorCommonBranch (K := K), main.Admissible N normBox Z s →
    ∀ error : ℕ → ExteriorPrime A → TwoDivisorCommonBranch (K := K),
      (∀ n ∈ ({1, 6, 7} : Finset ℕ), ∀ p ∈ P.primes,
        (error n p).Admissible N normBox Z s) →
      (∑ i : AmplifiedCommonIndex P main error,
        amplifiedIndexWeight P M B main error i) ≤
          C * Z ^ (δ + eps) / (Ideal.absNorm s : ℝ) := by
  obtain ⟨C, Z₀, hC, hZ₀, hm⟩ := actual_amplified_common_branch_mass
    (A := A) N normBox δ ell eps Mmax Bmax hbox hδ hell heps hepsell hMmax hBmax
  refine ⟨C, Z₀, hC, hZ₀, ?_⟩
  intro Z hZ bad P M B hM hMM hBB s hs hs0 main hmain error herror
  rw [sum_amplifiedIndexWeight]
  exact hm Z hZ bad P M B hM hMM hBB s hs hs0 main hmain error herror

/-- A bound proved for each actual source leaf is summed along its
actual arithmetic index. This helper does not supply that per-leaf
bound or its fibre cardinality as an engine hypothesis. -/
theorem sum_decorated_amplified_weights_le
    (P : PowerScaleExteriorPool A bad Z ell eps) (M B : ℝ)
    (main : TwoDivisorCommonBranch (K := K))
    (error : ℕ → ExteriorPrime A → TwoDivisorCommonBranch (K := K))
    (hZ : 0 ≤ Z) (hell : 0 < ell) (hM : 0 ≤ M)
    (hdensity : 0 ≤ P.rowDensity M B)
    {I : Type*} [Fintype I] (index : I → AmplifiedCommonIndex P main error)
    (weight : I → ℝ) (factor multiplicity : ℝ) (hfactor : 0 ≤ factor)
    (hweight : ∀ i, weight i ≤ factor * amplifiedIndexWeight P M B main error (index i))
    (hcard : ∀ j, ((Finset.univ.filter (fun i => index i = j)).card : ℝ) ≤ multiplicity) :
    (∑ i : I, weight i) ≤
      factor * multiplicity * amplifiedCommonBranchMass P M B main error := by
  calc
    _ ≤ ∑ i : I, factor * amplifiedIndexWeight P M B main error (index i) :=
      Finset.sum_le_sum (fun i _ => hweight i)
    _ = factor * ∑ i : I, amplifiedIndexWeight P M B main error (index i) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ factor * (multiplicity * ∑ j : AmplifiedCommonIndex P main error,
        amplifiedIndexWeight P M B main error j) :=
      mul_le_mul_of_nonneg_left
        (sum_weighted_fibres_le index (amplifiedIndexWeight P M B main error)
          (amplifiedIndexWeight_nonneg P M B main error hZ hell hM hdensity)
          multiplicity hcard) hfactor
    _ = _ := by rw [sum_amplifiedIndexWeight]; ring

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.sum_amplifiedIndexWeight
#print axioms HeckeSkeleton.Moments.EngineStep.amplified_finite_index_mass
