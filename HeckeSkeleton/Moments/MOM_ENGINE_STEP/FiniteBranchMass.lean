import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NestedCommonMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolMass

/-!
# Shared-divisor finite carriers and their one pool average

This counting lemma retains both complete common-support labels and
allocations of their shared first divisor S. It does not yet represent
the independent second residual divisor L in SecondAllocationKernel.
That additional divisor requires its own harmonic sum with the literal
1 / N(L) density from the frozen factors; allocation counts of S cannot
replace it. Consequently the bound below is a restricted carrier lemma,
not a complete mass bound for the actual two-stage branch family.

Within this stated carrier, main branches pay one pool-length allowance.
The 1/6/7 errors have no pool-length allowance: their genuine local squared
factors pay their moving norm before the single pool average is taken.
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree UniqueFactorizationMonoid LocalFiniteSums
open CommonSupportMass HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]

structure CommonSupportBranch where
  first : Finset (Label K)
  divisors : Label K → Finset (Ideal (𝓞 K))
  second : Label K → Ideal (𝓞 K) → Finset (Label K)
  leftOccurrences : Label K → Ideal (𝓞 K) → ℕ
  rightOccurrences : Label K → Ideal (𝓞 K) → ℕ

namespace CommonSupportBranch

def mass (b : CommonSupportBranch (K := K)) : ℝ :=
  ∑ v ∈ b.first, (1 / (Ideal.absNorm (commonRadical v.1.1 v.1.2) : ℝ)) *
    ∑ D ∈ b.divisors v,
      allocatedRadicalMass D (b.leftOccurrences v D) (b.rightOccurrences v D) (b.second v D)

theorem mass_nonneg (b : CommonSupportBranch (K := K)) : 0 ≤ b.mass :=
  Finset.sum_nonneg fun v _ => mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun D _ => allocatedRadicalMass_nonneg D _ _ _)

/-- Only original finite carriers, literal norm windows and counts. -/
structure Admissible (b : CommonSupportBranch (K := K))
    (N : ℕ) (B Z : ℝ) (s : Ideal (𝓞 K)) : Prop where
  first_valid : ∀ v ∈ b.first, Valid s v
  first_norm : ∀ v ∈ b.first,
    (Ideal.absNorm v.1.1 : ℝ) ≤ Z ^ B ∧ (Ideal.absNorm v.1.2 : ℝ) ≤ Z ^ B
  divisor_valid : ∀ v ∈ b.first, ∀ D ∈ b.divisors v, Squarefree D ∧ D ≠ 0
  divisor_norm : ∀ v ∈ b.first, ∀ D ∈ b.divisors v, (Ideal.absNorm D : ℝ) ≤ Z ^ B
  second_valid : ∀ v ∈ b.first, ∀ D ∈ b.divisors v, ∀ w ∈ b.second v D, Valid D w
  second_norm : ∀ v ∈ b.first, ∀ D ∈ b.divisors v, ∀ w ∈ b.second v D,
    (Ideal.absNorm w.1.1 : ℝ) ≤ Z ^ B ∧ (Ideal.absNorm w.1.2 : ℝ) ≤ Z ^ B
  occurrences : ∀ v ∈ b.first, ∀ D ∈ b.divisors v,
    b.leftOccurrences v D ≤ N ∧ b.rightOccurrences v D ≤ N

theorem uniform_mass (N : ℕ) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ s : Ideal (𝓞 K), Squarefree s → s ≠ 0 →
      ∀ b : CommonSupportBranch (K := K), b.Admissible N B Z s →
        b.mass ≤ C * Z ^ ε / (Ideal.absNorm s : ℝ) := by
  obtain ⟨C, hC, hmass⟩ := nested_common_support_mass (K := K) N B ε hB hε
  refine ⟨C, hC, ?_⟩
  intro Z hZ s hs hs0 b hb
  exact hmass Z hZ s hs hs0 b.first hb.first_valid hb.first_norm
    b.divisors hb.divisor_valid hb.divisor_norm b.second hb.second_valid hb.second_norm
    b.leftOccurrences b.rightOccurrences hb.occurrences

end CommonSupportBranch

variable {A : SArithmeticData K}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}

/-- One density, one main representation factor, and three genuine
local error weights, with all finite labels retained. -/
def amplifiedCommonBranchMass
    (P : PowerScaleExteriorPool A bad Z ell eps) (M B : ℝ)
    (main : CommonSupportBranch (K := K))
    (error : ℕ → ExteriorPrime A → CommonSupportBranch (K := K)) : ℝ :=
  (4 / P.rowDensity M B) *
    (((M + 6 * ell) / (ell / 2)) * Z ^ ell * main.mass +
      (∑ p ∈ P.primes, FirstGaussPoolData.localErrorWeight p 1 *
        Q p ^ amplifierMovingExponent 1 * (error 1 p).mass) +
      (∑ p ∈ P.primes, FirstGaussPoolData.localErrorWeight p 6 *
        Q p ^ amplifierMovingExponent 6 * (error 6 p).mass) +
      (∑ p ∈ P.primes, FirstGaussPoolData.localErrorWeight p 7 *
        Q p ^ amplifierMovingExponent 7 * (error 7 p).mass))

/-- The constants and scale threshold precede every moving pool,
common-support label, divisor and occurrence-allocation family. -/
theorem actual_amplified_common_branch_mass
    (N : ℕ) (normBox δ ell eps Mmax Bmax : ℝ)
    (hbox : 0 ≤ normBox) (hδ : 0 < δ)
    (hell : 0 < ell) (heps : 0 < eps) (hepsell : eps < ell)
    (hMmax : 0 ≤ Mmax) (hBmax : 0 ≤ Bmax) :
    ∃ C Z₀ : ℝ, 0 < C ∧ 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
    ∀ bad : Finset (HeightOneSpectrum (𝓞 K)),
    ∀ P : PowerScaleExteriorPool A bad Z ell eps,
    ∀ M B : ℝ, 0 ≤ M → M ≤ Mmax → B ≤ Bmax →
    ∀ s : Ideal (𝓞 K), Squarefree s → s ≠ 0 →
    ∀ main : CommonSupportBranch (K := K), main.Admissible N normBox Z s →
    ∀ error : ℕ → ExteriorPrime A → CommonSupportBranch (K := K),
      (∀ n ∈ ({1, 6, 7} : Finset ℕ), ∀ p ∈ P.primes,
        (error n p).Admissible N normBox Z s) →
      amplifiedCommonBranchMass P M B main error ≤
        C * Z ^ (δ + eps) / (Ideal.absNorm s : ℝ) := by
  obtain ⟨C₀, hC₀, hmass⟩ := CommonSupportBranch.uniform_mass (K := K)
    N normBox δ hbox hδ
  obtain ⟨Z₀, hZ₀, hpool⟩ := uniform_pool_density_and_mass (A := A)
    ell eps Mmax Bmax hell heps hepsell hMmax hBmax
  let T : ℝ := (Mmax + 6 * ell) / (ell / 2)
  have hT : 0 < T := by dsimp [T]; positivity
  let C : ℝ := 4 * (2 * T + 6 * idealCountConstant K) * C₀
  have hI : 0 < idealCountConstant K :=
    zero_lt_one.trans_le (one_le_idealCountConstant K)
  refine ⟨C, Z₀, by dsimp [C]; positivity, hZ₀, ?_⟩
  intro Z hZ bad P M B hM hMM hBB s hs hs0 main hmain error herrors
  have hZ1 : 1 < Z := hZ₀.trans_le hZ
  have hz : 0 < Z := zero_lt_one.trans hZ1
  obtain ⟨hd, hinv, hcard, herrorsum⟩ := hpool Z hZ bad P M B hMM hBB
  let H : ℝ := C₀ * Z ^ δ / (Ideal.absNorm s : ℝ)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hmainMass : main.mass ≤ H := hmass Z hZ1.le s hs hs0 main hmain
  have herrorMass (n : ℕ) (hn : n ∈ ({1, 6, 7} : Finset ℕ)) (p : ExteriorPrime A)
      (hp : p ∈ P.primes) : (error n p).mass ≤ H :=
    hmass Z hZ1.le s hs hs0 (error n p) (herrors n hn p hp)
  have hmainPrefactor : Z ^ ell / P.rowDensity M B ≤ 2 * Z ^ eps := by
    calc
      _ = Z ^ ell * (1 / P.rowDensity M B) := by ring
      _ ≤ Z ^ ell * (2 * Z ^ (-ell + eps)) :=
        mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg hz.le _)
      _ = _ := by
        rw [show Z ^ ell * (2 * Z ^ (-ell + eps)) =
          2 * (Z ^ ell * Z ^ (-ell + eps)) by ring, ← Real.rpow_add hz]
        congr 2
        ring
  have hmult : (M + 6 * ell) / (ell / 2) ≤ T :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hmainBound :
      (((M + 6 * ell) / (ell / 2)) * Z ^ ell * main.mass) /
          P.rowDensity M B ≤ 2 * T * Z ^ eps * H := by
    calc
      _ = ((M + 6 * ell) / (ell / 2)) *
          (Z ^ ell / P.rowDensity M B) * main.mass := by ring
      _ ≤ T * (2 * Z ^ eps) * H :=
        mul_le_mul
          (mul_le_mul hmult hmainPrefactor
            (div_nonneg (Real.rpow_nonneg hz.le _) hd.le) hT.le)
          hmainMass main.mass_nonneg (by positivity)
      _ = _ := by ring
  have herrorBound (n : ℕ) (hn : n ∈ ({1, 6, 7} : Finset ℕ)) :
      (∑ p ∈ P.primes, FirstGaussPoolData.localErrorWeight p n *
        Q p ^ amplifierMovingExponent n * (error n p).mass) /
        P.rowDensity M B ≤ 2 * idealCountConstant K * Z ^ eps * H := by
    calc
      _ ≤ (∑ p ∈ P.primes, FirstGaussPoolData.localErrorWeight p n *
          Q p ^ amplifierMovingExponent n * H) / P.rowDensity M B :=
        div_le_div_of_nonneg_right
          (Finset.sum_le_sum fun p hp =>
            mul_le_mul_of_nonneg_left (herrorMass n hn p hp)
              (mul_nonneg (FirstGaussPoolData.localErrorWeight_nonneg p n)
                (pow_nonneg (by change (0 : ℝ) ≤ (Ideal.absNorm p.val.asIdeal : ℝ); positivity) _)))
          hd.le
      _ = ((∑ p ∈ P.primes, FirstGaussPoolData.localErrorWeight p n *
          Q p ^ amplifierMovingExponent n) / P.rowDensity M B) * H := by
        rw [← Finset.sum_mul]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (herrorsum n) hH
  have he1 := herrorBound 1 (by simp)
  have he6 := herrorBound 6 (by simp)
  have he7 := herrorBound 7 (by simp)
  calc
    amplifiedCommonBranchMass P M B main error =
        4 * ((((M + 6 * ell) / (ell / 2)) * Z ^ ell * main.mass) / P.rowDensity M B +
          (∑ p ∈ P.primes, FirstGaussPoolData.localErrorWeight p 1 *
            Q p ^ amplifierMovingExponent 1 * (error 1 p).mass) / P.rowDensity M B +
          (∑ p ∈ P.primes, FirstGaussPoolData.localErrorWeight p 6 *
            Q p ^ amplifierMovingExponent 6 * (error 6 p).mass) / P.rowDensity M B +
          (∑ p ∈ P.primes, FirstGaussPoolData.localErrorWeight p 7 *
            Q p ^ amplifierMovingExponent 7 * (error 7 p).mass) / P.rowDensity M B) := by
      unfold amplifiedCommonBranchMass
      ring
    _ ≤ 4 * (2 * T * Z ^ eps * H +
        2 * idealCountConstant K * Z ^ eps * H +
        2 * idealCountConstant K * Z ^ eps * H +
        2 * idealCountConstant K * Z ^ eps * H) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add (add_le_add hmainBound he1) he6) he7) (by norm_num)
    _ = _ := by
      dsimp only [C, H]
      rw [Real.rpow_add hz]
      ring

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CommonSupportBranch.uniform_mass
#print axioms HeckeSkeleton.Moments.EngineStep.actual_amplified_common_branch_mass

