import Expansion.ActualAnnularIdentification
import HeckeGeneral.Analysis.MomentInputs

/-!
# The unchanged dyadic profile as an actual ideal test

The repository's recipe requires an exact finite support, whereas Fourier
extraction uses a larger ambient norm window. The test below filters that
window by the literal profile, and the following equalities discard only
terms whose smooth profile is zero. Coefficients and their ramified masks
are retained. This is a data and equality adapter; it introduces no moment
admissibility or detector-bound assumption.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.ActualRecipePolynomials

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.IdealMobiusReciprocal
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ExpansionBufferedPolynomials
open Expansion.ActualAnnularIdentification ExpansionInterfaces.Mellin
open ExpansionDetector.Fourier ExpansionDetector.IdealCutoff
open scoped Classical BigOperators ContDiff

variable (K : Type) [Field K] [NumberField K]

/-- The source's one fixed physical profile, with exact support for every
real scale. Nonpositive scales have empty support automatically. -/
def dyadicAnnularIdealTest : IdealTest K where
  profile _ _ x := Expansion.Dyadic.annularProfile x
  support _ _ D := (finiteIdealNormWindow K (2 * D)).filter
    (fun I => Expansion.Dyadic.annularProfile (idealNorm K I / D) ≠ 0)
  support_spec _ _ D I := by
    simp only [Finset.mem_filter, and_iff_right_iff_imp]
    intro hn
    have hs := Expansion.Dyadic.annularProfile_support hn
    have hD : 0 < D := by
      by_contra hD
      have hdiv := div_nonpos_of_nonneg_of_nonpos (idealNorm_pos K I).le (le_of_not_gt hD)
      linarith [hs.1]
    exact mem_finiteIdealNormWindow_of_le K (2 * D) I ((div_le_iff₀ hD).mp hs.2)

@[simp] theorem dyadicAnnularIdealTest_profile (u : NonzeroIdeal K) (t x : ℝ) :
    (dyadicAnnularIdealTest K).profile u t x = Expansion.Dyadic.annularProfile x := rfl

/-- An ambient support can be replaced by any exact support of the same
profile. Both sides are the same finite sum, including the central factor. -/
theorem normalizedPolynomial_eq_of_profile_support {ι : Type*}
    (S T : Finset ι) (c : ι → ℂ) (N : ι → ℝ) (W : ℝ → ℂ) (X β ν : ℝ)
    (hS : ∀ i, W (N i / X) ≠ 0 → i ∈ S)
    (hT : ∀ i, W (N i / X) ≠ 0 → i ∈ T) :
    normalizedPolynomial S c N W X β ν = normalizedPolynomial T c N W X β ν := by
  let f : ι → ℂ := fun i =>
    c i * W (N i / X) * ((N i / X : ℝ) : ℂ) ^ (-centralShift β ν)
  have hs : (∑' i, f i) = ∑ i ∈ S, f i := by
    apply tsum_eq_sum
    intro i hi
    have hw : W (N i / X) = 0 := by
      by_contra hn
      exact hi (hS i hn)
    simp only [f, hw, mul_zero, zero_mul]
  have ht : (∑' i, f i) = ∑ i ∈ T, f i := by
    apply tsum_eq_sum
    intro i hi
    have hw : W (N i / X) = 0 := by
      by_contra hn
      exact hi (hT i hn)
    simp only [f, hw, mul_zero, zero_mul]
  unfold normalizedPolynomial
  change _ * (∑ i ∈ S, f i) = _ * (∑ i ∈ T, f i)
  rw [← hs, ← ht]

/-- Every complete annular factor, possibly multiplied by another scalar
profile, agrees with the exact `IdealTest` at its dyadic scale. -/
theorem normalized_ambient_eq_dyadicTest
    (u : NonzeroIdeal K) (c : NonzeroIdeal K → ℂ) (g : ℝ → ℂ)
    (H X β ν : ℝ) (hX : 0 < X) (hXcap : X ≤ 6 * H) :
    normalizedPolynomial (finiteIdealNormWindow K (2 * (6 * H))) c (idealNorm K)
      (fun x => Expansion.Dyadic.annularProfile x * g x) X β ν =
    normalizedPolynomial ((dyadicAnnularIdealTest K).support u 0 X) c (idealNorm K)
      (fun x => (dyadicAnnularIdealTest K).profile u 0 x * g x) X β ν := by
  apply normalizedPolynomial_eq_of_profile_support
  · intro I hn
    have hprofile := (mul_ne_zero_iff.mp hn).1
    have hnorm : idealNorm K I ≤ 2 * X :=
      (div_le_iff₀ hX).mp (Expansion.Dyadic.annularProfile_support hprofile).2
    exact mem_finiteIdealNormWindow_of_le K (2 * (6 * H)) I (by linarith)
  · intro I hn
    exact ((dyadicAnnularIdealTest K).support_spec u 0 X I).mpr
      (mul_ne_zero_iff.mp hn).1

/-- Exact plain-factor identification with the repository's ideal test. -/
theorem actual_plain_normalized_eq_test
    (u : NonzeroIdeal K) (χ : HeckeCharacter K)
    (E : Finset (HeightOneSpectrum (𝓞 K)))
    (H X β ν : ℝ) (hX : 0 < X) (hXcap : X ≤ 6 * H) :
    normalizedPolynomial (nonzeroTerminalSet (6 * H))
      (idealCoefficientHom (deletePrimes K E (primeCoefficient K χ)))
      Expansion.Dyadic.idealNorm Expansion.Dyadic.annularProfile X β ν =
    normalizedPolynomial ((dyadicAnnularIdealTest K).support u 0 X)
      (deletedAnnularCoefficient K false χ E) (idealNorm K)
      ((dyadicAnnularIdealTest K).profile u 0) X β ν := by
  rw [actual_plain_normalized_eq_mellin K χ E (6 * H) X β ν]
  rw [show (dyadicAnnularIdealTest K).profile u 0 =
    Expansion.Dyadic.annularProfile from rfl]
  simpa only [dyadicMellinProfile, dyadicAnnularIdealTest_profile, mul_one] using
    normalized_ambient_eq_dyadicTest K u (deletedAnnularCoefficient K false χ E)
      (fun _ => 1) H X β ν hX hXcap

/-- Exact inverse-factor identification, with its original cutoff ratio. -/
theorem actual_inverse_normalized_eq_test
    (u : NonzeroIdeal K) (χ : HeckeCharacter K)
    (E : Finset (HeightOneSpectrum (𝓞 K))) (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (H D X β ν : ℝ) (hD : 0 < D) (hX : 0 < X) (hXcap : X ≤ 6 * H) :
    normalizedPolynomial (nonzeroTerminalSet (6 * H))
      (Expansion.Dyadic.inverseRawCoefficient
        (idealCoefficientHom (deletePrimes K E (primeCoefficient K χ))) V D)
      Expansion.Dyadic.idealNorm Expansion.Dyadic.annularProfile X β ν =
    normalizedPolynomial ((dyadicAnnularIdealTest K).support u 0 X)
      (deletedAnnularCoefficient K true χ E) (idealNorm K)
      (fun x => (dyadicAnnularIdealTest K).profile u 0 x * V (X / D * x)) X β ν := by
  rw [actual_inverse_normalized_eq_mellin K χ E V hV (6 * H) D X β ν hD hX]
  exact normalized_ambient_eq_dyadicTest K u (deletedAnnularCoefficient K true χ E)
    (fun x => V (X / D * x)) H X β ν hX hXcap

end Expansion.ActualRecipePolynomials
