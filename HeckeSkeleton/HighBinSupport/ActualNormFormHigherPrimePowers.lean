import HeckeGeneral.Analysis.IdealDerivativePrimePowers
import HeckeGeneral.Characters.PrimeCoefficients
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Finset.Preimage
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
Higher prime powers in the actual annular prime detector.

The exponents start at two. Their norm series converges for every real
part above one half, by actual ideal-norm summability and a uniform
geometric majorant. A finite annular higher-power sum consequently costs
only an arbitrarily small power of its scale. No prime ideal theorem or
prime-sum estimate is assumed.
-/

noncomputable section
namespace HighBinVerified.HigherPrimePowers

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

def powerNorm (pn : HeightOneSpectrum (𝓞 K) × ℕ) : ℝ :=
  (pn.1.asIdeal.absNorm : ℝ) ^ (pn.2 + 2)

theorem powerNorm_pos (pn : HeightOneSpectrum (𝓞 K) × ℕ) : 0 < powerNorm K pn := by
  apply pow_pos
  exact_mod_cast lt_trans Nat.zero_lt_one (one_lt_primeIdeal_absNorm K pn.1)

theorem summable_higher_primePowers {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    Summable (fun pn : HeightOneSpectrum (𝓞 K) × ℕ =>
      ((pn.1.asIdeal.absNorm : ℝ) ^ (-sigma)) ^ (pn.2 + 2)) := by
  let r : ℝ := (2 : ℝ) ^ (-sigma)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hg : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0 hr1
  have hp : Summable (fun p : HeightOneSpectrum (𝓞 K) =>
      (p.asIdeal.absNorm : ℝ) ^ (-(2 * sigma))) := by
    simpa only [primeNonzeroIdeal] using
      (summable_nonzeroIdeal_norm_rpow K (show 1 < 2 * sigma by linarith)).comp_injective
        (primeNonzeroIdeal_injective K)
  have hm := hp.mul_of_nonneg hg
    (fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun n => pow_nonneg hr0 n)
  apply Summable.of_nonneg_of_le
    (fun pn => pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _) ?_ hm
  rintro ⟨p, n⟩
  have hq2 : (2 : ℝ) ≤ (p.asIdeal.absNorm : ℝ) := by
    exact_mod_cast one_lt_primeIdeal_absNorm K p
  have hq : 0 < (p.asIdeal.absNorm : ℝ) := by linarith
  have hx : 0 ≤ (p.asIdeal.absNorm : ℝ) ^ (-sigma) :=
    Real.rpow_nonneg hq.le _
  have hxr : (p.asIdeal.absNorm : ℝ) ^ (-sigma) ≤ r :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hq2 (by linarith)
  calc
    ((p.asIdeal.absNorm : ℝ) ^ (-sigma)) ^ (n + 2) =
        ((p.asIdeal.absNorm : ℝ) ^ (-sigma)) ^ n *
          ((p.asIdeal.absNorm : ℝ) ^ (-sigma) * (p.asIdeal.absNorm : ℝ) ^ (-sigma)) := by
      rw [pow_add, pow_two]
    _ ≤ r ^ n * ((p.asIdeal.absNorm : ℝ) ^ (-sigma) *
          (p.asIdeal.absNorm : ℝ) ^ (-sigma)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx hxr n) (mul_nonneg hx hx)
    _ = (p.asIdeal.absNorm : ℝ) ^ (-(2 * sigma)) * r ^ n := by
      rw [← Real.rpow_add hq, show -sigma + -sigma = -(2 * sigma) by ring]
      ring

theorem summable_higher_powerNorm {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    Summable (fun pn : HeightOneSpectrum (𝓞 K) × ℕ => powerNorm K pn ^ (-sigma)) := by
  have hs := summable_higher_primePowers K hsigma
  convert hs using 1
  funext pn
  exact (Real.rpow_pow_comm (Nat.cast_nonneg pn.1.asIdeal.absNorm) (-sigma) (pn.2 + 2)).symm

def higherPowerConstant (delta : ℝ) : ℝ :=
  (∑' pn : HeightOneSpectrum (𝓞 K) × ℕ, powerNorm K pn ^ (-(1 / 2 + delta))) + 1

theorem higherPowerConstant_pos (delta : ℝ) : 0 < higherPowerConstant K delta := by
  apply add_pos_of_nonneg_of_pos
  · exact tsum_nonneg (fun pn => Real.rpow_nonneg (powerNorm_pos K pn).le _)
  · exact zero_lt_one

/-- Uniformly over every finite collection of actual higher prime powers
inside the annular cutoff, their square-root weights cost P^delta. -/
theorem higher_powerNorm_sum_le (F : Finset (HeightOneSpectrum (𝓞 K) × ℕ))
    (P delta : ℝ) (hP : 0 < P) (hdelta : 0 < delta)
    (hcut : ∀ pn ∈ F, powerNorm K pn ≤ 2 * P) :
    (∑ pn ∈ F, powerNorm K pn ^ (-(1 / 2 : ℝ))) ≤
      higherPowerConstant K delta * (2 * P) ^ delta := by
  have hsum := summable_higher_powerNorm K (show 1 / 2 < 1 / 2 + delta by linarith)
  have hterm : ∀ pn ∈ F, powerNorm K pn ^ (-(1 / 2 : ℝ)) ≤
      (2 * P) ^ delta * powerNorm K pn ^ (-(1 / 2 + delta)) := by
    intro pn hpn
    calc
      _ = powerNorm K pn ^ delta * powerNorm K pn ^ (-(1 / 2 + delta)) := by
        rw [← Real.rpow_add (powerNorm_pos K pn)]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (powerNorm_pos K pn).le (hcut pn hpn) hdelta.le)
        (Real.rpow_nonneg (powerNorm_pos K pn).le _)
  calc
    _ ≤ ∑ pn ∈ F, (2 * P) ^ delta * powerNorm K pn ^ (-(1 / 2 + delta)) :=
      Finset.sum_le_sum hterm
    _ = (2 * P) ^ delta * ∑ pn ∈ F, powerNorm K pn ^ (-(1 / 2 + delta)) :=
      (Finset.mul_sum ..).symm
    _ ≤ (2 * P) ^ delta * higherPowerConstant K delta := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
      exact (hsum.sum_le_tsum F
        (fun pn _ => Real.rpow_nonneg (powerNorm_pos K pn).le _)).trans
          (le_add_of_nonneg_right zero_le_one)
    _ = _ := mul_comm _ _

/-- Actual complex phase factors have precisely their square-root norm.
This finite-sum estimate may be used after the genuine Mellin inversion. -/
theorem higher_power_weighted_phase_sum_le
    (F : Finset (HeightOneSpectrum (𝓞 K) × ℕ)) (weight : HeightOneSpectrum (𝓞 K) × ℕ → ℂ)
    (P delta t M : ℝ) (hP : 0 < P) (hdelta : 0 < delta) (hM : 0 ≤ M)
    (hcut : ∀ pn ∈ F, powerNorm K pn ≤ 2 * P)
    (hweight : ∀ pn ∈ F, ‖weight pn‖ ≤ M) :
    ‖∑ pn ∈ F, weight pn *
        (powerNorm K pn : ℂ) ^ (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      M * higherPowerConstant K delta * (2 * P) ^ delta := by
  have hnorm : ∀ pn ∈ F,
      ‖weight pn * (powerNorm K pn : ℂ) ^ (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        M * powerNorm K pn ^ (-(1 / 2 : ℝ)) := by
    intro pn hpn
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (powerNorm_pos K pn)]
    have hre : (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I).re = -(1 / 2 : ℝ) := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_right (hweight pn hpn)
      (Real.rpow_nonneg (powerNorm_pos K pn).le _)
  calc
    _ ≤ ∑ pn ∈ F, ‖weight pn *
        (powerNorm K pn : ℂ) ^ (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ := norm_sum_le _ _
    _ ≤ ∑ pn ∈ F, M * powerNorm K pn ^ (-(1 / 2 : ℝ)) := Finset.sum_le_sum hnorm
    _ = M * ∑ pn ∈ F, powerNorm K pn ^ (-(1 / 2 : ℝ)) := (Finset.mul_sum ..).symm
    _ ≤ M * (higherPowerConstant K delta * (2 * P) ^ delta) :=
      mul_le_mul_of_nonneg_left (higher_powerNorm_sum_le K F P delta hP hdelta hcut) hM
    _ = _ := by ring

/-- The higher-power term after removing the logarithmic weight from the
actual Hecke logarithmic derivative. The factor `1 / (n+2)` is retained:
it is the ratio `log Np / log N(p^(n+2))`. -/
def heckeHigherPowerTerm (chi : HeckeCharacter K)
    (weight : HeightOneSpectrum (𝓞 K) × ℕ → ℂ) (t : ℝ)
    (pn : HeightOneSpectrum (𝓞 K) × ℕ) : ℂ :=
  (weight pn * primeCoefficient K chi pn.1 ^ (pn.2 + 2) /
      ((pn.2 + 2 : ℕ) : ℂ)) *
    (powerNorm K pn : ℂ) ^ (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I)

/-- All coefficient and ramification masks are the actual Hecke
coefficients. This estimate is uniform in the character and frequency,
and it preserves the exact higher-power multiplicity. -/
theorem hecke_higherPower_sum_le
    (chi : HeckeCharacter K) (F : Finset (HeightOneSpectrum (𝓞 K) × ℕ))
    (weight : HeightOneSpectrum (𝓞 K) × ℕ → ℂ)
    (P delta t M : ℝ) (hP : 0 < P) (hdelta : 0 < delta) (hM : 0 ≤ M)
    (hcut : ∀ pn ∈ F, powerNorm K pn ≤ 2 * P)
    (hweight : ∀ pn ∈ F, ‖weight pn‖ ≤ M) :
    ‖∑ pn ∈ F, heckeHigherPowerTerm K chi weight t pn‖ ≤
      M * higherPowerConstant K delta * (2 * P) ^ delta := by
  apply higher_power_weighted_phase_sum_le K F
    (fun pn => weight pn * primeCoefficient K chi pn.1 ^ (pn.2 + 2) /
      ((pn.2 + 2 : ℕ) : ℂ)) P delta t M hP hdelta hM hcut
  intro pn hpn
  have hn : (1 : ℝ) ≤ (pn.2 + 2 : ℕ) := by exact_mod_cast (by omega : 1 ≤ pn.2 + 2)
  have hcoef : ‖primeCoefficient K chi pn.1 ^ (pn.2 + 2)‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_primeCoefficient_le_one K chi pn.1)
  rw [norm_div, norm_mul, Complex.norm_natCast]
  calc
    _ ≤ M / ((pn.2 + 2 : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact (mul_le_mul (hweight pn hpn) hcoef (norm_nonneg _) hM).trans_eq
        (mul_one M)
    _ ≤ M := div_le_self hM hn

/-- The actual ideal associated to an exponent at least two. -/
def higherPowerIdeal (pn : HeightOneSpectrum (𝓞 K) × ℕ) : NonzeroIdeal K :=
  primePowerIdeal K (pn.1, pn.2 + 1)

theorem higherPowerIdeal_injective : Function.Injective (higherPowerIdeal K) := by
  intro x y h
  have hpair := primePowerIdeal_injective K h
  exact Prod.ext (congrArg Prod.fst hpair)
    (Nat.add_right_cancel (congrArg Prod.snd hpair))

theorem idealNorm_higherPowerIdeal (pn : HeightOneSpectrum (𝓞 K) × ℕ) :
    idealNorm K (higherPowerIdeal K pn) = powerNorm K pn := by
  rw [higherPowerIdeal, idealNorm_primePowerIdeal]
  rfl

/-- A literal finite cutoff, obtained by the injective prime-power map into
the repository's actual nonzero ideals of norm at most `floor (2P)`. -/
def higherPowerCutoff (P : ℝ) : Finset (HeightOneSpectrum (𝓞 K) × ℕ) :=
  (Ideal.finite_setOfPred_absNorm_le₀ (S := 𝓞 K) ⌊2 * P⌋₊).toFinset.preimage
    (higherPowerIdeal K) (higherPowerIdeal_injective K).injOn

theorem mem_higherPowerCutoff_iff {P : ℝ} (hP : 0 ≤ P)
    (pn : HeightOneSpectrum (𝓞 K) × ℕ) :
    pn ∈ higherPowerCutoff K P ↔ powerNorm K pn ≤ 2 * P := by
  simp only [higherPowerCutoff, Finset.mem_preimage, Set.Finite.mem_toFinset,
    Set.mem_ofPred_eq]
  rw [← idealNorm_higherPowerIdeal]
  exact Nat.le_floor_iff (by positivity)

/-- The actual annular higher-power term, with the Hecke coefficient,
frequency phase and exact reciprocal multiplicity retained. -/
def heckeHigherAnnularTerm (chi : HeckeCharacter K) (phi : ℝ → ℂ)
    (P t : ℝ) (pn : HeightOneSpectrum (𝓞 K) × ℕ) : ℂ :=
  heckeHigherPowerTerm K chi (fun pn => phi (powerNorm K pn / P)) t pn

theorem heckeHigherAnnularTerm_eq_zero_outside
    (chi : HeckeCharacter K) (phi : ℝ → ℂ) {P : ℝ} (hP : 0 < P) (t : ℝ)
    (hphi : Function.support phi ⊆ Set.Ioo (1 : ℝ) 2)
    (pn : HeightOneSpectrum (𝓞 K) × ℕ) (hpn : pn ∉ higherPowerCutoff K P) :
    heckeHigherAnnularTerm K chi phi P t pn = 0 := by
  have hz : phi (powerNorm K pn / P) = 0 := by
    by_contra hne
    have hupper := (hphi hne).2
    exact hpn ((mem_higherPowerCutoff_iff K hP.le pn).mpr
      ((div_lt_iff₀ hP).mp hupper).le)
  simp only [heckeHigherAnnularTerm, heckeHigherPowerTerm, hz, zero_mul, zero_div]

/-- Compact annular support makes the full actual higher-power series a
finite sum. The finite support is constructed, rather than supplied. -/
theorem summable_heckeHigherAnnularTerm
    (chi : HeckeCharacter K) (phi : ℝ → ℂ) {P : ℝ} (hP : 0 < P) (t : ℝ)
    (hphi : Function.support phi ⊆ Set.Ioo (1 : ℝ) 2) :
    Summable (heckeHigherAnnularTerm K chi phi P t) :=
  summable_of_ne_finset_zero
    (heckeHigherAnnularTerm_eq_zero_outside K chi phi hP t hphi)

/-- The complete annular higher-power error is `O(P^delta)`, uniformly in
the actual Hecke character and the phase height. No finite cutoff or
summability hypothesis remains in the statement. -/
theorem hecke_higherAnnular_tsum_le
    (chi : HeckeCharacter K) (phi : ℝ → ℂ) (P delta t M : ℝ)
    (hP : 0 < P) (hdelta : 0 < delta) (hM : 0 ≤ M)
    (hann : Function.support phi ⊆ Set.Ioo (1 : ℝ) 2)
    (hphi : ∀ y : ℝ, ‖phi y‖ ≤ M) :
    ‖∑' pn, heckeHigherAnnularTerm K chi phi P t pn‖ ≤
      M * higherPowerConstant K delta * (2 * P) ^ delta := by
  rw [tsum_eq_sum (heckeHigherAnnularTerm_eq_zero_outside K chi phi hP t hann)]
  exact hecke_higherPower_sum_le K chi (higherPowerCutoff K P)
    (fun pn => phi (powerNorm K pn / P)) P delta t M hP hdelta hM
    (fun pn hpn => (mem_higherPowerCutoff_iff K hP.le pn).mp hpn)
    (fun pn _ => hphi _)

/-- All positive prime powers with their exact logarithmic-derivative
multiplicity. Exponent one is the actual normalized prime polynomial. -/
def heckeAnnularPrimePowerTerm (chi : HeckeCharacter K) (phi : ℝ → ℂ)
    (P t : ℝ) (pn : HeightOneSpectrum (𝓞 K) × ℕ) : ℂ :=
  (phi (((pn.1.asIdeal.absNorm : ℝ) ^ (pn.2 + 1)) / P) *
      primeCoefficient K chi pn.1 ^ (pn.2 + 1) / ((pn.2 + 1 : ℕ) : ℂ)) *
    (((pn.1.asIdeal.absNorm : ℝ) ^ (pn.2 + 1)) : ℂ) ^
      (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I)

def primePowerCutoff (P : ℝ) : Finset (HeightOneSpectrum (𝓞 K) × ℕ) :=
  (Ideal.finite_setOfPred_absNorm_le₀ (S := 𝓞 K) ⌊2 * P⌋₊).toFinset.preimage
    (primePowerIdeal K) (primePowerIdeal_injective K).injOn

theorem mem_primePowerCutoff_iff {P : ℝ} (hP : 0 ≤ P)
    (pn : HeightOneSpectrum (𝓞 K) × ℕ) :
    pn ∈ primePowerCutoff K P ↔
      (pn.1.asIdeal.absNorm : ℝ) ^ (pn.2 + 1) ≤ 2 * P := by
  simp only [primePowerCutoff, Finset.mem_preimage, Set.Finite.mem_toFinset,
    Set.mem_ofPred_eq]
  rw [← idealNorm_primePowerIdeal]
  exact Nat.le_floor_iff (by positivity)

theorem heckeAnnularPrimePowerTerm_eq_zero_outside
    (chi : HeckeCharacter K) (phi : ℝ → ℂ) {P : ℝ} (hP : 0 < P) (t : ℝ)
    (hphi : Function.support phi ⊆ Set.Ioo (1 : ℝ) 2)
    (pn : HeightOneSpectrum (𝓞 K) × ℕ) (hpn : pn ∉ primePowerCutoff K P) :
    heckeAnnularPrimePowerTerm K chi phi P t pn = 0 := by
  have hz : phi (((pn.1.asIdeal.absNorm : ℝ) ^ (pn.2 + 1)) / P) = 0 := by
    by_contra hne
    exact hpn ((mem_primePowerCutoff_iff K hP.le pn).mpr
      ((div_lt_iff₀ hP).mp (hphi hne).2).le)
  simp only [heckeAnnularPrimePowerTerm, hz, zero_mul, zero_div]

theorem summable_heckeAnnularPrimePowerTerm
    (chi : HeckeCharacter K) (phi : ℝ → ℂ) {P : ℝ} (hP : 0 < P) (t : ℝ)
    (hphi : Function.support phi ⊆ Set.Ioo (1 : ℝ) 2) :
    Summable (heckeAnnularPrimePowerTerm K chi phi P t) :=
  summable_of_ne_finset_zero
    (heckeAnnularPrimePowerTerm_eq_zero_outside K chi phi hP t hphi)

/-- Exact removal of higher prime powers. Both series are finite by the
actual annular ideal cutoff; the prime coefficient keeps ramified zeros. -/
theorem hecke_annular_primePower_decomposition
    (chi : HeckeCharacter K) (phi : ℝ → ℂ) {P : ℝ} (hP : 0 < P) (t : ℝ)
    (hann : Function.support phi ⊆ Set.Ioo (1 : ℝ) 2) :
    (∑' pn, heckeAnnularPrimePowerTerm K chi phi P t pn) =
      (∑' p : HeightOneSpectrum (𝓞 K),
        phi ((p.asIdeal.absNorm : ℝ) / P) * primeCoefficient K chi p *
          (p.asIdeal.absNorm : ℂ) ^ (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I)) +
      ∑' pn, heckeHigherAnnularTerm K chi phi P t pn := by
  let f := heckeAnnularPrimePowerTerm K chi phi P t
  have hf := summable_heckeAnnularPrimePowerTerm K chi phi hP t hann
  have hzero : Summable (fun p : HeightOneSpectrum (𝓞 K) => f (p, 0)) :=
    hf.comp_injective (fun _ _ h => congrArg Prod.fst h)
  have hhigh := summable_heckeHigherAnnularTerm K chi phi hP t hann
  have htail (p : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
      f (p, n + 1) = heckeHigherAnnularTerm K chi phi P t (p, n) := rfl
  have hfirst (p : HeightOneSpectrum (𝓞 K)) :
      f (p, 0) = phi ((p.asIdeal.absNorm : ℝ) / P) * primeCoefficient K chi p *
        (p.asIdeal.absNorm : ℂ) ^ (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I) := by
    simp only [f, heckeAnnularPrimePowerTerm, Nat.zero_add, pow_one,
      Nat.cast_one, div_one, Complex.ofReal_natCast]
  calc
    _ = ∑' p : HeightOneSpectrum (𝓞 K), ∑' n : ℕ, f (p, n) := hf.tsum_prod
    _ = ∑' p : HeightOneSpectrum (𝓞 K),
        (f (p, 0) + ∑' n : ℕ, heckeHigherAnnularTerm K chi phi P t (p, n)) := by
      apply tsum_congr
      intro p
      rw [(hf.prod_factor p).tsum_eq_zero_add]
      simp only [htail]
    _ = (∑' p : HeightOneSpectrum (𝓞 K), f (p, 0)) +
        ∑' p : HeightOneSpectrum (𝓞 K), ∑' n : ℕ,
          heckeHigherAnnularTerm K chi phi P t (p, n) := hzero.tsum_add hhigh.prod
    _ = _ := by
      simp only [hfirst]
      rw [← hhigh.tsum_prod]

/-- The genuine annular prime polynomial differs from the full
logarithmic detector's prime-power expression by `O(P^delta)`. -/
theorem norm_annular_prime_sum_sub_primePower_sum_le
    (chi : HeckeCharacter K) (phi : ℝ → ℂ) (P delta t M : ℝ)
    (hP : 0 < P) (hdelta : 0 < delta) (hM : 0 ≤ M)
    (hann : Function.support phi ⊆ Set.Ioo (1 : ℝ) 2)
    (hphi : ∀ y : ℝ, ‖phi y‖ ≤ M) :
    ‖(∑' p : HeightOneSpectrum (𝓞 K),
        phi ((p.asIdeal.absNorm : ℝ) / P) * primeCoefficient K chi p *
          (p.asIdeal.absNorm : ℂ) ^ (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I)) -
      (∑' pn, heckeAnnularPrimePowerTerm K chi phi P t pn)‖ ≤
      M * higherPowerConstant K delta * (2 * P) ^ delta := by
  rw [hecke_annular_primePower_decomposition K chi phi hP t hann,
    sub_add_cancel_left, norm_neg]
  exact hecke_higherAnnular_tsum_le K chi phi P delta t M hP hdelta hM hann hphi

end HighBinVerified.HigherPrimePowers

#print axioms HighBinVerified.HigherPrimePowers.summable_higher_primePowers
#print axioms HighBinVerified.HigherPrimePowers.higher_powerNorm_sum_le
#print axioms HighBinVerified.HigherPrimePowers.higher_power_weighted_phase_sum_le
#print axioms HighBinVerified.HigherPrimePowers.hecke_higherPower_sum_le
#print axioms HighBinVerified.HigherPrimePowers.summable_heckeHigherAnnularTerm
#print axioms HighBinVerified.HigherPrimePowers.hecke_higherAnnular_tsum_le
#print axioms HighBinVerified.HigherPrimePowers.hecke_annular_primePower_decomposition
#print axioms HighBinVerified.HigherPrimePowers.norm_annular_prime_sum_sub_primePower_sum_le
