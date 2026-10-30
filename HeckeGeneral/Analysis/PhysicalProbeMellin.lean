import HeckeGeneral.Analysis.MellinInverseLine
import HeckeGeneral.Analysis.PhysicalProbePrincipal
import HeckeGeneral.Analysis.VerticalLineIdentity

/-!
The actual principal line-2 probe supplies its Mellin identity by Fourier
inversion. Spectral regularity remains explicit; the identity is proved.
The numerator, deleted L-function and Gaussian are the literal definitions
from the physical probe, and finite Euler deletion is removed at the end.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def principalDetectorNumerator (P : ProbeData K S) (ψ : HeckeCharacter K) (s : ℂ) : ℂ :=
  Complex.exp ((s - 5 / 6) ^ 2) * principalCorrection K S P ψ s

def principalSpectrum (P : ProbeData K S) (ψ : HeckeCharacter K) (s : ℂ) : ℂ :=
  principalDetectorNumerator K S P ψ s /
    heckeDeletedContinuation K ψ (exceptionalPrimes K S) s

def PrincipalSpectralRegularity (P : ProbeData K S) (ψ : HeckeCharacter K) : Prop :=
  PositiveLineRegularity 2 (11 / 16) (principalSpectrum K S P ψ)

theorem principalLineProbe_eq_positiveLineInverse
    (P : ProbeData K S) (ψ : HeckeCharacter K) :
    principalLineProbe K S P ψ = positiveLineInverse 2 (11 / 16) (principalSpectrum K S P ψ) := by
  funext Z
  unfold principalLineProbe positiveLineInverse
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [principalSpectrum, principalDetectorNumerator,
    Complex.ofReal_ofNat, Complex.ofReal_div]
  ring

theorem principalLineProbe_mellin_identity
    (P : ProbeData K S) (ψ : HeckeCharacter K)
    (hreg : PrincipalSpectralRegularity K S P ψ) (t : ℝ) :
    heckeDeletedContinuation K ψ (exceptionalPrimes K S) (2 + (t : ℂ) * Complex.I) *
      physicalMellin (principalLineProbe K S P ψ) (2 + (t : ℂ) * Complex.I) =
      principalDetectorNumerator K S P ψ (2 + (t : ℂ) * Complex.I) := by
  have hM := physicalMellin_positiveLineInverse 2 _ hreg t
  norm_num only [Complex.ofReal_ofNat] at hM
  rw [principalLineProbe_eq_positiveLineInverse, hM]
  have hs : (1 : ℝ) < (2 + (t : ℂ) * Complex.I).re := by norm_num
  have hL : heckeDeletedContinuation K ψ (exceptionalPrimes K S)
      (2 + (t : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (heckeEulerDeletionPolynomial_ne_zero K ψ _ (by linarith))
      (heckeContinuation_ne_zero K ψ hs)
  unfold principalSpectrum
  field_simp [hL]

theorem principal_initialMellinDetectorIdentity
    (P : ProbeData K S) (ψ : HeckeCharacter K) {b : ℝ}
    (hb : 7 / 8 ≤ b) (hb2 : b < 2)
    (hreg : PrincipalSpectralRegularity K S P ψ)
    (hf : PhysicalProbeBound (principalLineProbe K S P ψ) b)
    (hH : AnalyticOnNhd ℂ (principalCorrection K S P ψ) (rightHalfPlane (7 / 8)))
    (hHne : ∀ s ∈ rightHalfPlane (7 / 8), principalCorrection K S P ψ s ≠ 0) :
    InitialMellinDetectorIdentity (heckeDeletedContinuation K ψ (exceptionalPrimes K S))
      (principalLineProbe K S P ψ) (principalDetectorNumerator K S P ψ) b := by
  apply initialMellinDetectorIdentity_of_verticalLine
    (fun s _ => meromorphicOn_heckeDeletedContinuation K ψ _ s (mem_univ _)) hf
  · intro s hs
    have he : AnalyticAt ℂ (fun z : ℂ => Complex.exp ((z - 5 / 6) ^ 2)) s := by fun_prop
    exact he.mul (hH s (lt_of_le_of_lt hb hs))
  · intro s hs
    exact mul_ne_zero (Complex.exp_ne_zero _) (hHne s (lt_of_le_of_lt hb hs))
  · exact hb2
  · exact principalLineProbe_mellin_identity K S P ψ hreg

theorem heckeContinuation_zeroFreeOn_of_principalProbe
    (P : ProbeData K S) (ψ : HeckeCharacter K) {b : ℝ}
    (hb : 7 / 8 ≤ b) (hb2 : b < 2)
    (hreg : PrincipalSpectralRegularity K S P ψ)
    (hf : PhysicalProbeBound (principalLineProbe K S P ψ) b)
    (hH : AnalyticOnNhd ℂ (principalCorrection K S P ψ) (rightHalfPlane (7 / 8)))
    (hHne : ∀ s ∈ rightHalfPlane (7 / 8), principalCorrection K S P ψ s ≠ 0) :
    MeromorphicZeroFreeOn (heckeContinuation K ψ) (rightHalfPlane b) := by
  exact heckeContinuation_zeroFreeOn_of_deleted_initial_physicalMellin K ψ _ (by linarith) hf
    (principal_initialMellinDetectorIdentity K S P ψ hb hb2 hreg hf hH hHne)

end HeckeGeneral.ThetaSkeleton.Physical
