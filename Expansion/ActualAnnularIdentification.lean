import Expansion.IdealDyadicExtraction
import HeckeGeneral.Analysis.ExpansionPolynomialSupport
import ExpansionInterfaces.AnnularCutoffFamily

/-!
# Exact identification of the Fourier and Mellin detector polynomials

The physical dyadic profile is packaged without alteration as a Mellin
annular profile. Finite sums are reindexed along the nonzero-ideal subtype,
and the original inverse cutoff is moved into that same smooth profile by
an exact equality. The enlarged terminal ambient set contains the entire
annular support; no hard truncation is silently discarded.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.ActualAnnularIdentification

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ExpansionBufferedPolynomials
open HeckeGeneral.Analysis.IdealMobiusReciprocal
open ExpansionInterfaces.Mellin ExpansionDetector.Fourier
open ExpansionDetector.IdealCutoff
open scoped Classical BigOperators ContDiff

variable (K : Type) [Field K] [NumberField K]

/-- This is literally the profile used by the finite dyadic extraction. -/
def dyadicMellinProfile : AnnularProfile where
  function := Expansion.Dyadic.annularProfile
  lower := 1 / 2
  upper := 2
  lower_pos := by norm_num
  lower_le_upper := by norm_num
  smooth := Expansion.Dyadic.annularProfile_smooth
  supported := Expansion.Dyadic.annularProfile_support

@[simp] theorem dyadicMellinProfile_function (x : ℝ) :
    dyadicMellinProfile.function x = Expansion.Dyadic.annularProfile x := rfl

/-- The terminal ideal set and the analytic nonzero-ideal norm window have
exactly the same elements after forgetting the nonzero certificate. -/
theorem sum_nonzeroTerminalSet_eq_normWindow (H : ℝ)
    (f : Ideal (𝓞 K) → ℂ) :
    (∑ I ∈ nonzeroTerminalSet H, f I) =
      ∑ I ∈ finiteIdealNormWindow K (2 * H), f I.val := by
  symm
  apply Finset.sum_bij (fun I _ => I.val)
  · intro I hI
    apply (mem_nonzeroTerminalSet H I.val).mpr
    refine ⟨?_, mem_nonZeroDivisors_iff_ne_zero.mp I.property⟩
    unfold finiteIdealNormWindow at hI
    have hmem := Finset.mem_preimage.mp hI
    exact (Set.Finite.mem_toFinset _).mp hmem
  · intro I _ J _ hIJ
    exact Subtype.ext hIJ
  · intro I hI
    obtain ⟨hN, hne⟩ := (mem_nonzeroTerminalSet H I).mp hI
    refine ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hne⟩, ?_, rfl⟩
    unfold finiteIdealNormWindow
    exact Finset.mem_preimage.mpr ((Set.Finite.mem_toFinset _).mpr hN)
  · intro I hI
    rfl

/-- The ordinary Fourier factor is the identical normalized finite
polynomial to which the Mellin upper bounds apply. -/
theorem actual_plain_normalized_eq_mellin
    (χ : HeckeCharacter K) (E : Finset (HeightOneSpectrum (𝓞 K)))
    (H X β ν : ℝ) :
    normalizedPolynomial (nonzeroTerminalSet H)
      (idealCoefficientHom (deletePrimes K E (primeCoefficient K χ)))
      Expansion.Dyadic.idealNorm Expansion.Dyadic.annularProfile X β ν =
    normalizedPolynomial (finiteIdealNormWindow K (2 * H))
      (deletedAnnularCoefficient K false χ E) (idealNorm K)
      dyadicMellinProfile.function X β ν := by
  unfold normalizedPolynomial
  rw [sum_nonzeroTerminalSet_eq_normWindow K H]
  rfl

/-- The inverse factor retains the same Mobius coefficient and all deleted
Euler-factor zero masks. The equality moves only the literal scalar cutoff
`V(NI/D)` into the annular profile with ratio `X/D`. -/
theorem actual_inverse_normalized_eq_mellin
    (χ : HeckeCharacter K) (E : Finset (HeightOneSpectrum (𝓞 K)))
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (H D X β ν : ℝ) (hD : 0 < D) (hX : 0 < X) :
    normalizedPolynomial (nonzeroTerminalSet H)
      (Expansion.Dyadic.inverseRawCoefficient
        (idealCoefficientHom (deletePrimes K E (primeCoefficient K χ))) V D)
      Expansion.Dyadic.idealNorm Expansion.Dyadic.annularProfile X β ν =
    normalizedPolynomial (finiteIdealNormWindow K (2 * H))
      (deletedAnnularCoefficient K true χ E) (idealNorm K)
      (dyadicMellinProfile.cutoffFamily V hV (X / D)).function X β ν := by
  unfold normalizedPolynomial
  rw [sum_nonzeroTerminalSet_eq_normWindow K H]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  have hratio : X / D * (idealNorm K I / X) = idealNorm K I / D := by
    field_simp [hD.ne', hX.ne']
  change (UniqueFactorizationMonoid.moebius I.val : ℂ) *
      V (idealNorm K I / D) *
      idealCoefficient (deletePrimes K E (primeCoefficient K χ)) I.val *
      Expansion.Dyadic.annularProfile (idealNorm K I / X) *
      ((idealNorm K I / X : ℝ) : ℂ) ^ (-centralShift β ν) =
    ((UniqueFactorizationMonoid.moebius I.val : ℂ) *
      idealCoefficient (deletePrimes K E (primeCoefficient K χ)) I.val) *
      (Expansion.Dyadic.annularProfile (idealNorm K I / X) *
        V (X / D * (idealNorm K I / X))) *
      ((idealNorm K I / X : ℝ) : ℂ) ^ (-centralShift β ν)
  rw [hratio]
  ring

/-- The enlarged finite source window contains every ideal required by the
full annular profile at each retained dyadic scale. -/
theorem terminal_normWindow_contains_annular
    {H : ℝ} (hH : 1 ≤ H) {j : ℕ} (hj : j ≤ Expansion.Dyadic.dyadicCap (3 * H))
    (I : NonzeroIdeal K) (hI : idealNorm K I ≤ dyadicMellinProfile.upper * (2 : ℝ) ^ j) :
    I ∈ finiteIdealNormWindow K (2 * (6 * H)) := by
  apply mem_finiteIdealNormWindow_of_le
  have hscale : (2 : ℝ) ^ j ≤ 6 * H :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj).trans
      (Expansion.Dyadic.two_pow_terminal_dyadicCap_le hH)
  change idealNorm K I ≤ 2 * (2 : ℝ) ^ j at hI
  linarith

end Expansion.ActualAnnularIdentification
