import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondDivisorMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolMass

/-!
# Two independent divisor carriers and their one pool average

The carrier keeps first common labels, their shared first divisor S,
second common labels and the independent second residual divisor L.
Both full occurrence-allocation families are attached to L and paid by
its own literal inverse norm. The old mask, first S and second L each
retain the harmonic factor proved in SecondDivisorMass.

Main branches pay their one pool-length allowance. The 1/6/7 errors
have no pool-length allowance: their genuine local squared factors pay
their moving norm before the single pool average is taken. Constants
and the scale threshold precede every moving finite carrier and pool.
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree UniqueFactorizationMonoid LocalFiniteSums
open CommonSupportMass HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]



variable {A : SArithmeticData K}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}

/-- One density, one main representation factor, and three genuine
local error weights, with all finite labels retained. -/
def amplifiedCommonBranchMass
    (P : PowerScaleExteriorPool A bad Z ell eps) (M B : ℝ)
    (main : TwoDivisorCommonBranch (K := K))
    (error : ℕ → ExteriorPrime A → TwoDivisorCommonBranch (K := K)) : ℝ :=
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
    ∀ main : TwoDivisorCommonBranch (K := K), main.Admissible N normBox Z s →
    ∀ error : ℕ → ExteriorPrime A → TwoDivisorCommonBranch (K := K),
      (∀ n ∈ ({1, 6, 7} : Finset ℕ), ∀ p ∈ P.primes,
        (error n p).Admissible N normBox Z s) →
      amplifiedCommonBranchMass P M B main error ≤
        C * Z ^ (δ + eps) / (Ideal.absNorm s : ℝ) := by
  obtain ⟨C₀, hC₀, hmass⟩ := TwoDivisorCommonBranch.uniform_mass (K := K)
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

#print axioms HeckeSkeleton.Moments.EngineStep.CommonSupportMass.TwoDivisorCommonBranch.uniform_mass
#print axioms HeckeSkeleton.Moments.EngineStep.actual_amplified_common_branch_mass

