module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFirstPhase
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SupportCartesianReindex

@[expose] public section

set_option linter.unusedSectionVars false

set_option autoImplicit false

/-!
# Recovering the original finite support from nonzero source atoms

A generated element retains the coprimality zero of its complete ideal.
The support reconstruction below uses that zero before selecting a child
or any calibration data.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveSupportRecovery

open EngineStep NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

theorem plain_residual_mem (T S : Finset (Ideal (𝓞 K)))
    (hS : ∀ q ∈ S, Prime q) (D I : Ideal (𝓞 K)) (hD : D ≠ 0) (hI : I ≠ 0)
    (hsmooth : primeSupport D ⊆ S) (havoid : ∀ q ∈ S, IsCoprime I q)
    (hmem : D * I ∈ T) : I ∈ SupportCartesian.plainResidual T S D := by
  have hp := split_product S hS ⟨⟨D, hD⟩, hsmooth⟩
    ⟨⟨I, hI⟩, (outside_iff_coprime S hS ⟨I, hI⟩).mpr havoid⟩
  exact Finset.mem_image.mpr
    ⟨D * I, Finset.mem_filter.mpr ⟨hmem, hp.1⟩, hp.2⟩

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
variable (hemb : P.arithmetic.embedding = σ)

include P R hroot hemb

theorem residue_nonzero_coprime (G : A.Exterior) (g : A.R) (hg : A.Generates G g)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hn : actualIdealResidue (A := A) (σ := σ) J.val g ≠ 0) : IsCoprime J.val G.val := by
  by_contra hcop
  apply hn
  rw [CanonicalOriginalPhaseCalibration.residue_eq_probe_evaluation P hroot hemb,
    CanonicalLiteralFirstPhase.singleton_evaluation P R G g hg J,
    if_neg (fun h => hcop h.2), mul_zero]

theorem residue_mul_nonzero_coprime (G : A.Exterior) (g h : A.R) (hg : A.Generates G g)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hn : actualIdealResidue (A := A) (σ := σ) J.val (g * h) ≠ 0) :
    IsCoprime J.val G.val := by
  apply residue_nonzero_coprime P R hroot hemb G g hg J
  intro hz
  exact hn (by rw [actualIdealResidue_frequency_mul, hz, zero_mul])

theorem plainTerm_nonzero_coprime (G : A.Exterior) (g h : A.R) (hg : A.Generates G g)
    (χ θ : HeckeCharacter K) (mask : Ideal (𝓞 K) →* ℂ)
    (w : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ) (N : ℝ)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hn : sourcePlainTerm (σ := σ) χ θ mask g h w N J ≠ 0) :
    IsCoprime J.val G.val := by
  apply residue_mul_nonzero_coprime P R hroot hemb G g h hg J
  intro hz
  exact hn (by simp only [sourcePlainTerm, hz, mul_zero, zero_mul])

theorem primeTerm_nonzero_coprime (G : A.Exterior) (g h : A.R) (hg : A.Generates G g)
    (χ θ : HeckeCharacter K) (mask : Ideal (𝓞 K) →* ℂ)
    (w : HeightOneSpectrum (𝓞 K) → ℂ) (N : ℝ)
    (q : HeightOneSpectrum (𝓞 K))
    (hn : sourcePrimeTerm (σ := σ) χ θ mask g h w N q ≠ 0) :
    IsCoprime q.asIdeal G.val := by
  apply residue_mul_nonzero_coprime P R hroot hemb G g h hg
    (CanonicalOriginalPhaseCalibration.primeIdeal q)
  intro hz
  change actualIdealResidue (A := A) (σ := σ) q.asIdeal (g * h) = 0 at hz
  exact hn (by simp only [sourcePrimeTerm, hz, mul_zero, zero_mul])

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveSupportRecovery

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveSupportRecovery.plain_residual_mem
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveSupportRecovery.residue_nonzero_coprime
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveSupportRecovery.plainTerm_nonzero_coprime
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveSupportRecovery.primeTerm_nonzero_coprime
