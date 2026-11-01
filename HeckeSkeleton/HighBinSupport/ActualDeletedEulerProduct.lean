import HeckeSkeleton.HighBinSupport.ActualEulerProduct
import HeckeGeneral.Analysis.HeckeEulerProduct
import HeckeGeneral.Analysis.HeckeEulerDeletion

/-!
# Actual deleted Hecke products and the row continuation

Finite Euler deletion is performed in the genuine Hecke Euler product on
its half-plane of absolute convergence. Combining those three products
with the constructed finite-table correction gives a prime product for
the repository's literal `rowEulerContinuation`. This theorem does not
assume the initial Fourier-series calibration.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinActualEuler

open NumberField IsDedekindDomain Set Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinContinuation
open HighBinBoundary.CoarseEuler
open scoped Classical BigOperators Topology ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem mem_exceptionalPrimes_iff (p : HeightOneSpectrum (𝓞 K)) :
    p ∈ exceptionalPrimes K S ↔ p ∈ S := by
  constructor
  · intro hp
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hp
    exact hq ▸ q.property
  · intro hp
    exact Finset.mem_image.mpr ⟨⟨p, hp⟩, Finset.mem_univ _, rfl⟩

/-- The original deleted continuation is the product over the actual
exterior primes; no new series or continuation is introduced. -/
theorem heckeDeletedContinuation_hasProd (χ : HeckeCharacter K)
    {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : ExteriorPrime K S => heckeLocalEulerFactor K χ p.val s)
      (heckeDeletedContinuation K χ (exceptionalPrimes K S) s) := by
  let F := exceptionalPrimes K S
  let d : HeightOneSpectrum (𝓞 K) → ℂ := fun p =>
    if p ∈ F then eulerPolynomial (residueCard K p : ℝ)
      (primeCoefficient K χ p) s else 1
  have hd : HasProd d (heckeEulerDeletionPolynomial K χ F s) := by
    have h := hasProd_prod_of_ne_finset_one (s := F) (f := d)
      (L := SummationFilter.unconditional (HeightOneSpectrum (𝓞 K)))
      (fun p hp => if_neg hp)
    have heq : (∏ p ∈ F, d p) = heckeEulerDeletionPolynomial K χ F s := by
      apply Finset.prod_congr rfl
      intro p hp
      exact if_pos hp
    rwa [heq] at h
  have hfull := hd.mul (hasProd_heckeLSeries K χ hs)
  have hprod : HasProd
      ({p : HeightOneSpectrum (𝓞 K) | p ∉ S}.mulIndicator
        (fun p => heckeLocalEulerFactor K χ p s))
      (heckeDeletedContinuation K χ F s) := by
    rw [heckeDeletedContinuation, heckeContinuation_eq_series K χ hs]
    apply hfull.congr_fun
    intro p
    by_cases hp : p ∈ S
    · have hpF : p ∈ F := (mem_exceptionalPrimes_iff K S p).mpr hp
      have hpoly : eulerPolynomial (residueCard K p : ℝ)
          (primeCoefficient K χ p) s ≠ 0 :=
        eulerPolynomial_ne_zero (by exact_mod_cast one_lt_residueCard K p)
          (norm_primeCoefficient_le_one K χ p) (by linarith)
      simp only [Set.mulIndicator_of_notMem (show p ∉ {p | p ∉ S} from not_not.mpr hp),
        d, if_pos hpF, heckeLocalEulerFactor, mul_inv_cancel₀ hpoly]
    · have hpF : p ∉ F := fun hpF => hp ((mem_exceptionalPrimes_iff K S p).mp hpF)
      simp only [Set.mulIndicator_of_mem (show p ∈ {p | p ∉ S} from hp),
        d, if_neg hpF, one_mul]
  exact hasProd_subtype_iff_mulIndicator.mpr hprod

theorem heckeDeletedContinuation_ne_zero_initial (χ : HeckeCharacter K)
    {s : ℂ} (hs : 1 < s.re) :
    heckeDeletedContinuation K χ (exceptionalPrimes K S) s ≠ 0 := by
  rw [heckeDeletedContinuation, heckeContinuation_eq_series K χ hs]
  exact mul_ne_zero
    (heckeEulerDeletionPolynomial_ne_zero K χ _ (by linarith))
    (heckeLSeries_ne_zero K χ hs)

/-- The three literal local factors extracted from an actual row. -/
def rowLocalLRatio (P : ProbeData K S) (ψ : HeckeCharacter K)
    (u : FrequencyRow K S) (s w z : ℂ) (p : ExteriorPrime K S) : ℂ :=
  heckeLocalEulerFactor K 1 p.val (6 * z) *
    heckeLocalEulerFactor K (arithmeticRowCharacter K S P u) p.val w /
    heckeLocalEulerFactor K (ψ * conjugate (arithmeticRowCharacter K S P u)) p.val s

theorem rowLocalLRatio_hasProd (P : ProbeData K S) (ψ : HeckeCharacter K)
    (u : FrequencyRow K S) {s w z : ℂ}
    (hs : 1 < s.re) (hw : 1 < w.re) (hz : 1 < (6 * z).re) :
    HasProd (rowLocalLRatio K S P ψ u s w z)
      (heckeDeletedContinuation K 1 (exceptionalPrimes K S) (6 * z) *
        heckeDeletedContinuation K (arithmeticRowCharacter K S P u)
          (exceptionalPrimes K S) w /
        heckeDeletedContinuation K (ψ * conjugate (arithmeticRowCharacter K S P u))
          (exceptionalPrimes K S) s) :=
  ((heckeDeletedContinuation_hasProd K S 1 hz).mul
      (heckeDeletedContinuation_hasProd K S (arithmeticRowCharacter K S P u) hw)).div₀
    (heckeDeletedContinuation_hasProd K S
      (ψ * conjugate (arithmeticRowCharacter K S P u)) hs)
    (heckeDeletedContinuation_ne_zero_initial K S _ hs)

theorem rowCorrection_hasProd_sweptTube (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    {a e : ℝ} (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1)
    (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (v : ℂ × ℂ × ℂ) (hv : v ∈ sweptTube a e) :
    HasProd (fun p => localFactor K S P ψ Q u p v)
      (rowCorrection K S P ψ (arithmeticHighEulerData K S P ψ) Q u v.1 v.2.1 v.2.2) := by
  rw [rowCorrection_eq_explicitEuler K S P ψ Q u ha he.le v hv]
  have h := explicitEuler_hasProdLocallyUniformlyOn (exteriorSupport K S u.ideal) Q
    (fun p : ExteriorPrime K S => (p.val.asIdeal.absNorm : ℝ))
    (rowW K S P u) (rowD K S P ψ u) (rowE K S P ψ)
    (rowPhaseData K S P ψ u) (rowIndex K S u)
    (exteriorPrime_norm_two_le K S) ha ha1 he.le he1
    (rowW_norm K S P u) (rowD_norm K S P ψ u) (rowE_norm K S P ψ)
    (summable_exteriorPrime_swept_error K S he)
  exact (h.hasProd hv).congr_fun fun p =>
    localFactor_eq_explicit K S P ψ Q u ha he.le p v hv

theorem initialDomain_mem_sweptTube {s w z : ℂ}
    (hs : 4 < s.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    (s, w, z) ∈ sweptTube 1 (1 / 20000) := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num at * <;> linarith

/-- Prime product for the actual row continuation on the same open domain
as the original four-ideal series. The remaining arithmetic task is the
local equality between `primeBlockTerm`'s sum and these factors. -/
theorem rowEulerContinuation_hasProd_initial (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) {s w z : ℂ}
    (hs : 4 < s.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    HasProd (fun p : ExteriorPrime K S =>
      rowLocalLRatio K S P ψ u s w z p * localFactor K S P ψ Q u p (s, w, z))
      (rowEulerContinuation K S P ψ (arithmeticHighEulerData K S P ψ) Q u s w z) := by
  have hz6 : 1 < (6 * z).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have hs1 : 1 < s.re := lt_trans (by norm_num) hs
  have hw1 : 1 < w.re := lt_trans (by norm_num) hw
  have hL := rowLocalLRatio_hasProd K S P ψ u (s := s) (w := w) (z := z) hs1 hw1 hz6
  have hE := rowCorrection_hasProd_sweptTube K S P ψ Q u
    (a := 1) (e := 1 / 20000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (s, w, z) (initialDomain_mem_sweptTube hs hw hz)
  simpa only [rowEulerContinuation, arithmeticHighEulerData_character] using hL.mul hE

end HeckeSkeleton.HighBinActualEuler
