import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AmplifiedFiniteIndex
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalSameCarrierMass

/-!
# Exceptional divisor dyads on the actual amplified index

The exceptional source keeps its second-divisor lower dyad.  Its upper
norm window recovers the harmonic denominator of the same ordinary
index, with one mesh loss.  The main/1/6/7 tag, prime, all allocations
and the single pool density remain unchanged.  The finite sum below is
an internal assembly lemma: actual source fibres are proved separately
from their original row and support dictionaries.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree CommonSupportMass LocalFiniteSums

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}

def amplifiedInnerDivisor
    {P : PowerScaleExteriorPool A bad Z ell eps}
    {main : TwoDivisorCommonBranch (K := K)}
    {error : ℕ → ExteriorPrime A → TwoDivisorCommonBranch (K := K)} :
    AmplifiedCommonIndex P main error → Ideal (𝓞 K)
  | .inl j => j.2.2.2.1.val
  | .inr j => j.2.2.2.2.2.1.val

def amplifiedExceptionalDyadWeight
    (P : PowerScaleExteriorPool A bad Z ell eps) (M B : ℝ)
    (main : TwoDivisorCommonBranch (K := K))
    (error : ℕ → ExteriorPrime A → TwoDivisorCommonBranch (K := K))
    (lower : ℝ) (i : AmplifiedCommonIndex P main error) : ℝ :=
  (4 / P.rowDensity M B) *
    match i with
    | .inl j => ((M + 6 * ell) / (ell / 2)) * Z ^ ell *
        main.exceptionalDyadWeight Z lower j
    | .inr j => FirstGaussPoolData.localErrorWeight j.2.1.val j.1.val *
        Q j.2.1.val ^ amplifierMovingExponent j.1.val *
          (error j.1.val j.2.1.val).exceptionalDyadWeight Z lower j.2.2

private theorem scale_dyad_weight {a b x y s : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : x ≤ s * y) :
    a * (b * x) ≤ s * (a * (b * y)) := by
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h hb) ha).trans_eq (by ring)

/-- Only the original upper norm of the literal second divisor is
used.  The prime-pool multiplier is never estimated by a pool count. -/
theorem amplifiedExceptionalDyadWeight_le_indexWeight
    (P : PowerScaleExteriorPool A bad Z ell eps) (M B : ℝ)
    (main : TwoDivisorCommonBranch (K := K))
    (error : ℕ → ExteriorPrime A → TwoDivisorCommonBranch (K := K))
    (hZ : 0 < Z) (hell : 0 < ell) (hM : 0 ≤ M)
    (hdensity : 0 ≤ P.rowDensity M B)
    (lower mesh : ℝ) (i : AmplifiedCommonIndex P main error)
    (hL : amplifiedInnerDivisor i ≠ 0)
    (hwindow : (Ideal.absNorm (amplifiedInnerDivisor i) : ℝ) ≤ Z ^ (lower + mesh)) :
    amplifiedExceptionalDyadWeight P M B main error lower i ≤
      Z ^ mesh * amplifiedIndexWeight P M B main error i := by
  cases i with
  | inl j =>
    change (4 / P.rowDensity M B) *
      (((M + 6 * ell) / (ell / 2)) * Z ^ ell * main.exceptionalDyadWeight Z lower j) ≤ _
    exact scale_dyad_weight (div_nonneg (by norm_num) hdensity) (by positivity)
      (main.exceptionalDyadWeight_le_indexWeight Z lower mesh hZ j hL hwindow)
  | inr j =>
    change (4 / P.rowDensity M B) *
      ((FirstGaussPoolData.localErrorWeight j.2.1.val j.1.val *
        Q j.2.1.val ^ amplifierMovingExponent j.1.val) *
        (error j.1.val j.2.1.val).exceptionalDyadWeight Z lower j.2.2) ≤ _
    apply scale_dyad_weight (div_nonneg (by norm_num) hdensity)
    · exact mul_nonneg (FirstGaussPoolData.localErrorWeight_nonneg _ _)
        (pow_nonneg (by
          change (0 : ℝ) ≤ (Ideal.absNorm j.2.1.val.val.asIdeal : ℝ)
          positivity) _)
    · exact (error j.1.val j.2.1.val).exceptionalDyadWeight_le_indexWeight
        Z lower mesh hZ j.2.2 hL hwindow

/-- This is the exceptional counterpart of the uniform ordinary index
mass.  The numerical constant and threshold precede every moving source
and every original divisor dyad. -/
theorem uniform_amplified_exceptional_dyad_mass
    (N : ℕ) (normBox δ ell eps Mmax Bmax : ℝ)
    (hbox : 0 ≤ normBox) (hδ : 0 < δ)
    (hell : 0 < ell) (heps : 0 < eps) (hepsell : eps < ell)
    (hMmax : 0 ≤ Mmax) (hBmax : 0 ≤ Bmax) :
    ∃ C Z₀ : ℝ, 0 < C ∧ 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
    ∀ bad : Finset (HeightOneSpectrum (𝓞 K)),
    ∀ P : PowerScaleExteriorPool A bad Z ell eps,
    ∀ M B : ℝ, 0 ≤ M → M ≤ Mmax → B ≤ Bmax →
    ∀ mask : Ideal (𝓞 K), Squarefree mask → mask ≠ 0 →
    ∀ main : TwoDivisorCommonBranch (K := K), main.Admissible N normBox Z mask →
    ∀ error : ℕ → ExteriorPrime A → TwoDivisorCommonBranch (K := K),
      (∀ n ∈ ({1, 6, 7} : Finset ℕ), ∀ p ∈ P.primes,
        (error n p).Admissible N normBox Z mask) →
    ∀ {I : Type*} [Fintype I] (index : I → AmplifiedCommonIndex P main error)
      (multiplicity mesh : ℝ), 0 ≤ multiplicity →
      (∀ j, ((Finset.univ.filter (fun i => index i = j)).card : ℝ) ≤ multiplicity) →
      ∀ lower : I → ℝ,
      (∀ i, (Ideal.absNorm (amplifiedInnerDivisor (index i)) : ℝ) ≤ Z ^ (lower i + mesh)) →
      (∑ i : I, amplifiedExceptionalDyadWeight P M B main error (lower i) (index i)) ≤
        multiplicity * C * Z ^ (δ + eps + mesh) / (Ideal.absNorm mask : ℝ) := by
  obtain ⟨C, Zi, hC, hZi, hindex⟩ := amplified_finite_index_mass
    (A := A) N normBox δ ell eps Mmax Bmax hbox hδ hell heps hepsell hMmax hBmax
  obtain ⟨Zp, hZp, hpool⟩ := uniform_pool_density_and_mass (A := A)
    ell eps Mmax Bmax hell heps hepsell hMmax hBmax
  refine ⟨C, max Zi Zp, hC, hZi.trans_le (le_max_left _ _), ?_⟩
  intro Z hZ bad P M B hM hMM hBB mask hmask hmask0 main hmain error herror
    I inst index multiplicity mesh hmult hcard lower hwindow
  have hzi : Zi ≤ Z := (le_max_left _ _).trans hZ
  have hzp : Zp ≤ Z := (le_max_right _ _).trans hZ
  have hz : 0 < Z := zero_lt_one.trans (hZi.trans_le hzi)
  obtain ⟨hdensity, _, _, _⟩ := hpool Z hzp bad P M B hMM hBB
  have hL (j : AmplifiedCommonIndex P main error) : amplifiedInnerDivisor j ≠ 0 := by
    cases j with
    | inl j =>
      exact hmain.second_divisor_ne_zero j.1.val j.1.property j.2.1.val j.2.1.property
        j.2.2.1.val j.2.2.1.property j.2.2.2.1.val j.2.2.2.1.property
    | inr j =>
      have ha := herror j.1.val j.1.property j.2.1.val j.2.1.property
      exact ha.second_divisor_ne_zero j.2.2.1.val j.2.2.1.property
        j.2.2.2.1.val j.2.2.2.1.property j.2.2.2.2.1.val j.2.2.2.2.1.property
        j.2.2.2.2.2.1.val j.2.2.2.2.2.1.property
  have hfibre := sum_weighted_fibres_le index (amplifiedIndexWeight P M B main error)
    (amplifiedIndexWeight_nonneg P M B main error hz.le hell hM hdensity.le)
    multiplicity hcard
  have hm := hfibre.trans (mul_le_mul_of_nonneg_left
    (hindex Z hzi bad P M B hM hMM hBB mask hmask hmask0 main hmain error herror) hmult)
  calc
    _ ≤ ∑ i : I, Z ^ mesh * amplifiedIndexWeight P M B main error (index i) :=
      Finset.sum_le_sum fun i _ => amplifiedExceptionalDyadWeight_le_indexWeight
        P M B main error hz hell hM hdensity.le (lower i) mesh (index i) (hL _) (hwindow i)
    _ = Z ^ mesh * ∑ i : I, amplifiedIndexWeight P M B main error (index i) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ Z ^ mesh * (multiplicity * (C * Z ^ (δ + eps) / (Ideal.absNorm mask : ℝ))) :=
      mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hz.le _)
    _ = _ := by
      rw [Real.rpow_add hz (δ + eps) mesh]
      ring

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.amplifiedExceptionalDyadWeight_le_indexWeight
#print axioms HeckeSkeleton.Moments.EngineStep.uniform_amplified_exceptional_dyad_mass
