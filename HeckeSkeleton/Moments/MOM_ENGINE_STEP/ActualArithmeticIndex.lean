import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualLeafNormWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalAmplifiedCarrier

/-!
# The actual parent-to-arithmetic index and its original windows

This connects the internally computed tagged image to the literal live
parent leaves. The two image branches are proved admissible from the
original column window, before applying the harmonic mass estimate.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree CommonSupportMass
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K] {A : SArithmeticData K}

namespace OriginalArithmeticLabels

variable {I : Type*} [Fintype I] {cap : ℕ}

/-- Restricting to the actual pool tag preserves the original windows
already derived for the full image. This is used internally after the
actual source proof, not as a new source calibration premise. -/
theorem amplified_carriers_admissible_of
    (L : OriginalArithmeticLabels K I cap) (tag : I → Option (ℕ × ExteriorPrime A))
    {B Z : ℝ} {oldMask : Ideal (𝓞 K)}
    (h : L.carrier.Admissible (cap + 2) B Z oldMask) :
    (L.mainCarrier tag).Admissible (cap + 2) B Z oldMask ∧
      ∀ n p, (L.errorCarrier tag n p).Admissible (cap + 2) B Z oldMask := by
  apply L.amplified_carriers_admissible tag B Z oldMask
  · intro i
    exact h.first_valid _ (L.first_mem i)
  · intro i
    exact h.first_norm _ (L.first_mem i)
  · intro i
    exact h.first_divisor_valid _ (L.first_mem i) _ (L.firstDivisor_mem i)
  · intro i
    exact h.first_divisor_norm _ (L.first_mem i) _ (L.firstDivisor_mem i)
  · intro i
    exact h.second_valid _ (L.first_mem i) _ (L.firstDivisor_mem i) _ (L.second_mem i)
  · intro i
    exact h.second_norm _ (L.first_mem i) _ (L.firstDivisor_mem i) _ (L.second_mem i)
  · intro i
    exact h.second_divisor_ne_zero _ (L.first_mem i) _ (L.firstDivisor_mem i)
      _ (L.second_mem i) _ (L.secondDivisor_mem i)
  · intro i
    exact h.second_divisor_norm _ (L.first_mem i) _ (L.firstDivisor_mem i)
      _ (L.second_mem i) _ (L.secondDivisor_mem i)

end OriginalArithmeticLabels

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
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
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}

namespace ActualFirstSource.SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal) {cap : ℕ}
variable (hcap : L.slotCount ≤ cap)
variable (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)

abbrev ArithmeticIndex :=
  AmplifiedCommonIndex P
    ((R.arithmeticLabels L hcap exceptional N).mainCarrier (R.arithmeticTag L exceptional N))
    ((R.arithmeticLabels L hcap exceptional N).errorCarrier (R.arithmeticTag L exceptional N))

def arithmeticIndex (j : R.liveLeaves L exceptional N) :
    R.ArithmeticIndex L hcap exceptional N :=
  (R.arithmeticLabels L hcap exceptional N).amplifiedIndex
    (R.arithmeticTag L exceptional N) P (R.arithmeticTag_mem L exceptional N) j

theorem arithmeticIndex_allocation (j : R.liveLeaves L exceptional N) :
    (R.arithmeticLabels L hcap exceptional N).amplifiedAllocation
      (R.arithmeticTag L exceptional N) P (R.arithmeticIndex L hcap exceptional N j) =
        (R.arithmeticLabels L hcap exceptional N).allocation j :=
  (R.arithmeticLabels L hcap exceptional N).amplifiedIndex_allocation
    (R.arithmeticTag L exceptional N) P (R.arithmeticTag_mem L exceptional N) j

variable {exceptional}

/-- Both actual image branches inherit their windows from the same
original column family; no separate image-branch hypothesis is needed. -/
theorem arithmeticCarriers_admissible
    (exceptional : R.supported.gated.CoverHybridPredicates L)
    (B : ℝ) (oldMask : Ideal (𝓞 K)) (hs : Squarefree oldMask)
    (hmask : ∀ i ∈ s.columns, oldMask ∣ (s.ideal i).val)
    (hN : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B) :
    ((R.supported.gated.arithmeticLabels L hcap exceptional N).mainCarrier
      (R.supported.gated.arithmeticTag L exceptional N)).Admissible (cap + 2) B Z oldMask ∧
    ∀ n p, ((R.supported.gated.arithmeticLabels L hcap exceptional N).errorCarrier
      (R.supported.gated.arithmeticTag L exceptional N) n p).Admissible (cap + 2) B Z oldMask :=
  OriginalArithmeticLabels.amplified_carriers_admissible_of _ _
    (R.arithmeticLabels_admissible L hcap exceptional N B oldMask hs hmask hN)

end ActualFirstSource.SecondStages
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.arithmeticIndex_allocation
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.arithmeticCarriers_admissible
