import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CombinedDirectSourceTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CombinedPoolSourceTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstParent

/-!
# The same original first terminal windows after pool installation

The sole pool changes the first row processing. It preserves the full
original columns, first kernel and computed first profile weight.
The original arithmetic counting windows therefore transfer exactly.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.LargeSieve
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup
open CommonSupportMass UniqueFactorizationMonoid MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {E W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Z : ℝ}
variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX}

namespace ActualDirectFirstSource.CombinedTerminalOriginalWindows

variable {normBound parentWidth firstAmplitude kernelBound : ℝ}
variable {total shift : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ}
variable (O : s.CombinedTerminalOriginalWindows normBound parentWidth firstAmplitude kernelBound total shift)

/-- Installing the one original pool preserves all first arithmetic,
profile and Fourier windows. No new terminal estimate is introduced. -/
def withOriginalPool
    {bad : Finset (HeightOneSpectrum (𝓞 K))} {ell eps : ℝ}
    (P : PowerScaleExteriorPool A bad Z ell eps)
    (frozenLeft frozenRight : Ideal (𝓞 K))
    (hfrozenLeft : frozenLeft ≠ 0) (hfrozenRight : frozenRight ≠ 0)
    (rowLeft rowRight boundLeft boundRight divisorBound : ℝ)
    (hrowLeft : 0 ≤ rowLeft) (hrowRight : 0 ≤ rowRight)
    (hdivisor : 0 ≤ divisorBound)
    (hrowsLeft : ∀ v D, ∀ h ∈ (s.pieces v D).leftData.rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤ Z ^ rowLeft)
    (hrowsRight : ∀ v D, ∀ h ∈ (s.pieces v D).rightData.rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤ Z ^ rowRight)
    (hfrozenNormLeft : (Ideal.absNorm frozenLeft : ℝ) ≤ Z ^ boundLeft)
    (hfrozenNormRight : (Ideal.absNorm frozenRight : ℝ) ≤ Z ^ boundRight)
    (hcolumns : ∀ j ∈ s.columns, (Ideal.absNorm (s.ideal j).val : ℝ) ≤ Z ^ divisorBound)
    (hdensityLeft : 0 < P.rowDensity rowLeft (boundLeft + divisorBound))
    (hdensityRight : 0 < P.rowDensity rowRight (boundRight + divisorBound)) :
    ActualFirstSource.CombinedTerminalOriginalWindows
      (s.withOriginalPool P frozenLeft frozenRight hfrozenLeft hfrozenRight
      rowLeft rowRight boundLeft boundRight divisorBound hrowLeft hrowRight hdivisor
      hrowsLeft hrowsRight hfrozenNormLeft hfrozenNormRight hcolumns hdensityLeft hdensityRight)
      normBound parentWidth firstAmplitude kernelBound total shift where
  oldMask := O.oldMask
  old_squarefree := O.old_squarefree
  old_ne_zero := O.old_ne_zero
  old_divides := O.old_divides
  column_norm := O.column_norm
  maskIdeal := O.maskIdeal
  mask_ne_zero := O.mask_ne_zero
  mask_norm := O.mask_norm
  original_mask := O.original_mask
  first_profile := O.first_profile
  first_kernel := O.first_kernel

end ActualDirectFirstSource.CombinedTerminalOriginalWindows
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.CombinedTerminalOriginalWindows.withOriginalPool
