import HeckeGeneral.Analysis.PrincipalProbeNearZero
import HeckeGeneral.Analysis.PrincipalProbeContinuity
import HeckeGeneral.Analysis.PhysicalHeightComparison

/-! Close the actual principal detector from a low estimate and a finite
height comparison. Local integrability, rapid origin decay, spectral
regularity, the initial Mellin identity and finite Euler removal are all
derived. The high comparison remains an explicit downstream obligation,
not a replacement definition for the source T/I/P inputs. -/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain MeasureTheory Set Filter
open HeckeGeneral.Characters HeckeGeneral.Analysis
open scoped Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem principalPhysicalProbeBound_of_heightComparison
    (P : ProbeData K S) (ψ : HeckeCharacter K) (J : ℝ → ℂ) {B σ : ℝ}
    (hσ : 0 < σ) (hσsmall : σ < (B - 7 / 8) / 2)
    (hlow : ∀ ε : ℝ, 0 < ε → J =O[atTop] (fun Z : ℝ => Z ^ (3 / 16 + ε)))
    (hhigh : PhysicalHeightComparison J (principalLineProbe K S P ψ) (B - 11 / 16) σ)
    (hH : AnalyticOnNhd ℂ (principalCorrection K S P ψ) (rightHalfPlane (7 / 8)))
    (hHbound : ∀ s : ℂ, 7 / 8 < s.re → ‖principalCorrection K S P ψ s - 1‖ ≤ 1 / 2) :
    PhysicalProbeBound (principalLineProbe K S P ψ) (B - σ) :=
  physicalProbeBound_of_low_and_heightComparison hσ hσsmall hlow hhigh
    (locallyIntegrableOn_principalLineProbe K S P ψ hH hHbound)
    (principalLineProbe_isBigO_rpow_near_zero K S P ψ hH hHbound)

theorem principal_zeroFree_of_heightComparison
    (P : ProbeData K S) (ψ : HeckeCharacter K) (J : ℝ → ℂ) {B σ : ℝ}
    (hB : B ≤ 11 / 12) (hσ : 0 < σ) (hσsmall : σ < (B - 7 / 8) / 2)
    (hlow : ∀ ε : ℝ, 0 < ε → J =O[atTop] (fun Z : ℝ => Z ^ (3 / 16 + ε)))
    (hhigh : PhysicalHeightComparison J (principalLineProbe K S P ψ) (B - 11 / 16) σ)
    (hH : AnalyticOnNhd ℂ (principalCorrection K S P ψ) (rightHalfPlane (7 / 8)))
    (hHbound : ∀ s : ℂ, 7 / 8 < s.re → ‖principalCorrection K S P ψ s - 1‖ ≤ 1 / 2) :
    MeromorphicZeroFreeOn (heckeContinuation K ψ) (rightHalfPlane (B - σ)) := by
  exact heckeContinuation_zeroFreeOn_of_principalProbe_contraction K S P ψ
    (by linarith) (by linarith)
    (principalPhysicalProbeBound_of_heightComparison K S P ψ J hσ hσsmall hlow hhigh hH hHbound)
    hH hHbound

end HeckeGeneral.ThetaSkeleton.Physical
