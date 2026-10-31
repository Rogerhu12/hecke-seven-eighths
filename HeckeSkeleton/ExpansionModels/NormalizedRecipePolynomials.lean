import HeckeSkeleton.ExpansionModels.Core
import HeckeSkeleton.ExpansionModels.OriginalMask
import HeckeGeneral.Analysis.ExpansionBufferedPolynomials
import ExpansionDetector.AnnularNormalization

/-!
# The actual recipe values are the normalized detector polynomials

This is a finite-sum identity, with the original complete-row mask and the
original ideal test supports. The inverse cutoff profile is W(x)V(Rx),
where R is the recipe's D/U^t. No equality between independently selected
witness values is assumed.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeGeneral.Analysis.ExpansionRecipe

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global ExpansionBufferedPolynomials
open ExpansionDetector.Fourier
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (R : RowCharacterInput K S P)
variable (ω ψ : HeckeCharacter K)

lemma deleted_inverse_coefficient_eq_originalMasked
    (χ : HeckeCharacter K) (u I : NonzeroIdeal K) :
    deletedAnnularCoefficient K true χ (originalDeletedPrimes K S u) I =
      (moebius I.val : ℂ) * originalMaskedCoefficientHom K S χ u I.val := rfl

lemma deleted_plain_coefficient_eq_originalMasked
    (χ : HeckeCharacter K) (u I : NonzeroIdeal K) :
    deletedAnnularCoefficient K false χ (originalDeletedPrimes K S u) I =
      originalMaskedCoefficientHom K S χ u I.val := rfl

/-- The shared inverse finite polynomial, including its cutoff filter,
is exactly the normalized deleted Moebius polynomial from the detector. -/
theorem shared_inverse_cutoff_eq_normalized
    (a : PolynomialPresentation K ψ) (g : SlotGeometry K)
    (c : Fin g.slotCount → HeckeCharacter K) (W Wplain : IdealTest K)
    (V : ℝ → ℂ) (ratio : ℝ) (β ν : NonzeroIdeal K → ℝ)
    (u : FrequencyRow K S) (D : ℝ) (hD : 0 < D) :
    inversePolynomial (sharedMomentData K S P R ω ψ a g c u.sector
        (recipeCutoffTwist K W V ratio β ν) Wplain) u.ideal.val D 0 =
      normalizedPolynomial (W.support u.ideal.val 0 D)
        (deletedAnnularCoefficient K true (a.inverseBackground * R.character u ^ a.direction)
          (originalDeletedPrimes K S u.ideal.val))
        (idealNorm K) (fun y => W.profile u.ideal.val 0 y * V (ratio * y))
        D (β u.ideal.val) (ν u.ideal.val) := by
  rw [shared_inversePolynomial_eq_maskedHom K S P R ω ψ,
    sqrt_inverse_eq_cpow D hD]
  unfold normalizedPolynomial
  congr 1
  simp only [recipeCutoffTwist, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  rw [deleted_inverse_coefficient_eq_originalMasked K S]
  have hpower : profilePower (-(β u.ideal.val : ℂ) + (ν u.ideal.val : ℂ) * Complex.I)
      (idealNorm K I / D) =
      ((idealNorm K I / D : ℝ) : ℂ) ^ (-centralShift (β u.ideal.val) (ν u.ideal.val)) := by
    rw [profilePower_eq_cpow _ (div_pos (idealNorm_pos K I) hD)]
    congr 1
    unfold centralShift
    ring
  rw [hpower]
  by_cases hv : V (ratio * (idealNorm K I / D)) ≠ 0
  · rw [if_pos hv]
    ring
  · have hz : V (ratio * (idealNorm K I / D)) = 0 := not_ne_iff.mp hv
    simp only [hz, mul_zero, zero_mul, ite_self]

/-- The plain factor uses the same original deletion set and the same
real/imaginary shifts, with the exact sqrt normalizer. -/
theorem shared_plain_twist_eq_normalized
    (a : PolynomialPresentation K ψ) (g : SlotGeometry K)
    (c : Fin g.slotCount → HeckeCharacter K) (Winverse W : IdealTest K)
    (β ν : NonzeroIdeal K → ℝ) (u : FrequencyRow K S) (D : ℝ) (hD : 0 < D) :
    let Wtwist := W.freezeTwist (fun _ => 0)
      (fun J => -(β J : ℂ) + (ν J : ℂ) * Complex.I)
    plainPolynomial (sharedMomentData K S P R ω ψ a g c u.sector Winverse Wtwist)
      Wtwist u.ideal.val D 0 =
      normalizedPolynomial (W.support u.ideal.val 0 D)
        (deletedAnnularCoefficient K false (a.plainBackground * R.character u)
          (originalDeletedPrimes K S u.ideal.val))
        (idealNorm K) (W.profile u.ideal.val 0) D (β u.ideal.val) (ν u.ideal.val) := by
  dsimp only
  rw [shared_plainPolynomial_eq_maskedHom K S P R ω ψ, sqrt_inverse_eq_cpow D hD]
  unfold normalizedPolynomial
  congr 1
  simp only [IdealTest.freezeTwist]
  apply Finset.sum_congr rfl
  intro I hI
  rw [deleted_plain_coefficient_eq_originalMasked K S,
    profilePower_eq_cpow _ (div_pos (idealNorm_pos K I) hD)]
  have hp : -(β u.ideal.val : ℂ) + (ν u.ideal.val : ℂ) * Complex.I =
      -centralShift (β u.ideal.val) (ν u.ideal.val) := by unfold centralShift; ring
  rw [hp]
  ring

end HeckeGeneral.Analysis.ExpansionRecipe
