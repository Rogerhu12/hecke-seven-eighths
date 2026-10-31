import HeckeSkeleton.Moments.MOM_ENGINE_STEP.MovingOriginalArithmeticAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstParent

/-!
# Construct the actual first source from the original moving model

The original complete-row recipe supplies the ideal-to-orbit map and
the actual single-ideal phases.  The fixed norm-profile recipe supplies
the row-independent original smooth atoms.  Their whole Cartesian
coefficient, its complete centered subtraction and its positive Gram
test are then constructed by the existing canonical source theorem.

The row ball uses no extra avoidance mask. All original common-mask
zeros are still in the actual arithmetic coefficients and orbital
phases. This constructor is uniform in the original finite slot count
and the centered Boolean; it takes neither a phase dictionary, a Gram
identity nor a bound for the parent source.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

variable {K : Type} [Field K] [NumberField K]

theorem actualSixthUnits_are_sixth
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] :
    ∀ u : sixthPowerSUnitSubgroup K S, ∃ v : S.unit K, u.val = v ^ 6 := by
  intro u
  obtain ⟨v, hv⟩ := u.property
  exact ⟨v, hv.symm⟩

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]
variable {ω ψ : HeckeCharacter K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {X : Type*} {data : X → MomentData K ω ψ}

namespace CompleteMovingRowRecipe

variable (Q : CompleteMovingRowRecipe A P R data)

/-- The original source is now constructed from the original raw
recipe.  The same actual arithmetic choice supplies hroot and hemb. -/
def canonicalMovingDirectFirstSource
    (C : A.GeneralArithmeticContext σ η hS)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (W : NormProfileRecipe data) (ξ : X)
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (hZ : 0 < Z)
    (centered : Bool) (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
    (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    ActualDirectFirstSource
      (Γ := sixthPowerSUnitSubgroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (E := ℝ) (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      μv C Z (rowBallFiniteFamily K A.Sf 1)
      centered (data ξ) a t Y₁ Y₂ cutoff hcutoff := by
  let atoms := (Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) a Z t
  let raw := atoms.raw Y₁ Y₂
  exact (atoms.values Y₁ Y₂).canonicalDirectFirstSource
    (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (μv := μv) (ν := ν) C hZ ∅
    (fun u hu => Q.arithmeticAtoms_originalIdeal ξ u
      (((data ξ).rows_spec _ u).mp (Finset.mem_filter.mp hu).1).1)
    (fun _ _ => by simp [sIntegerOrbitAvoidanceMask])
    (fun I _ q => Q.arithmeticAtoms_leftPhase hroot hemb ξ q I)
    (fun I _ q => Q.arithmeticAtoms_rightPhase hroot hemb ξ q I)
    (fun i p _ q => Q.arithmeticAtoms_primePhase hroot hemb ξ q i p)
    centered cutoff hcutoff δ hδ hδhalf

@[simp] theorem canonicalMovingDirectFirstSource_mask
    (C : A.GeneralArithmeticContext σ η hS)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
    (hemb : P.arithmetic.embedding = σ)
    (W : NormProfileRecipe data) (ξ : X)
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (hZ : 0 < Z)
    (centered : Bool) (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
    (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    (Q.canonicalMovingDirectFirstSource μv ν C hroot hemb W ξ a Z t Y₁ Y₂ hZ
      centered cutoff hcutoff δ hδ hδhalf).mask = ∅ := rfl

end CompleteMovingRowRecipe

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actualSixthUnits_are_sixth
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalMovingDirectFirstSource
