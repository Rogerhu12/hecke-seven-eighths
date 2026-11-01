import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectParentFibre
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectSupportedLeaves

/-!
# Original row classifiers on prepared stages

The existing support and coefficient gates preserve the source profiles,
physical rows, mask, and chart row labels. The original blockwise prime
support, ideal windows, row code, and encoding therefore transport to
these stages by copying their fields.

The remaining constructors follow the original pool tags, sides, and
parent indices. Direct preparation is the existing `supported.gated`
operation.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments

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
variable {Θ : Type*} [Fintype Θ] {dimension width : ℕ} {B Z : ℝ}

namespace ActualGaussStage

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest}

namespace OriginalFibreRows

def supported (rows : s.OriginalFibreRows Θ dimension width B Z) :
    s.supported.OriginalFibreRows Θ dimension width B Z where
  support := rows.support
  maskIdeal := rows.maskIdeal
  rowIdeal := rows.rowIdeal
  mask_nonzero := rows.mask_nonzero
  row_nonzero := rows.row_nonzero
  maskPrimes := rows.maskPrimes
  row_divides := rows.row_divides
  mask_norm := rows.mask_norm
  row_norm := rows.row_norm
  code := rows.code
  encode := rows.encode
  row_label := rows.row_label

def gated (rows : s.OriginalFibreRows Θ dimension width B Z) :
    s.gated.OriginalFibreRows Θ dimension width B Z where
  support := rows.support
  maskIdeal := rows.maskIdeal
  rowIdeal := rows.rowIdeal
  mask_nonzero := rows.mask_nonzero
  row_nonzero := rows.row_nonzero
  maskPrimes := rows.maskPrimes
  row_divides := rows.row_divides
  mask_norm := rows.mask_norm
  row_norm := rows.row_norm
  code := rows.code
  encode := rows.encode
  row_label := rows.row_label

end OriginalFibreRows
end ActualGaussStage

section PoolTransport

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {poolBase ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad poolBase ell eps} {ι : Type*}
variable {dpool : FirstGaussPoolData C P ι} {c : ι → ℂ}

namespace ActualPoolStages.OriginalFibreRows

variable {s : ActualPoolStages (E := E) hΓ μv hDiff dpool c finiteTest}

def supported (rows : s.OriginalFibreRows Θ dimension width B Z) :
    s.supported.OriginalFibreRows Θ dimension width B Z where
  main := rows.main.supported
  one p := (rows.one p).supported
  six p := (rows.six p).supported
  seven p := (rows.seven p).supported

def gated (rows : s.OriginalFibreRows Θ dimension width B Z) :
    s.gated.OriginalFibreRows Θ dimension width B Z where
  main := rows.main.gated
  one p := (rows.one p).gated
  six p := (rows.six p).gated
  seven p := (rows.seven p).gated

end ActualPoolStages.OriginalFibreRows

namespace FirstBlockPoolData.SecondStages.OriginalFibreRows

variable {κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockPoolData chart P M X hX}
variable {s : p.SecondStages (E := E) (hDiff := hDiff)}

def supported (rows : s.OriginalFibreRows Θ dimension width B Z) :
    s.supported.OriginalFibreRows Θ dimension width B Z where
  left S χ := (rows.left S χ).supported
  right S χ := (rows.right S χ).supported

def gated (rows : s.OriginalFibreRows Θ dimension width B Z) :
    s.gated.OriginalFibreRows Θ dimension width B Z where
  left S χ := (rows.left S χ).gated
  right S χ := (rows.right S χ).gated

end FirstBlockPoolData.SecondStages.OriginalFibreRows

namespace ActualFirstSource.SecondStages.OriginalFibreRows

variable {omega psi : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K omega psi} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}
variable {R : s.SecondStages (E := E) (hDiff := hDiff)}

def supported (rows : R.OriginalFibreRows Θ dimension width B Z) :
    R.supported.OriginalFibreRows Θ dimension width B Z where
  source v D := (rows.source v D).supported

def gated (rows : R.OriginalFibreRows Θ dimension width B Z) :
    R.gated.OriginalFibreRows Θ dimension width B Z where
  source v D := (rows.source v D).gated

end ActualFirstSource.SecondStages.OriginalFibreRows

end PoolTransport

namespace FirstBlockDirectData.SecondStages.OriginalFibreRows

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockDirectData chart M X hX}
variable {s : p.SecondStages (E := E) (hDiff := hDiff)}

def prepared (rows : s.OriginalFibreRows Θ dimension width B Z) :
    s.prepared.OriginalFibreRows Θ dimension width B Z where
  left S χ := (rows.left S χ).supported.gated
  right S χ := (rows.right S χ).supported.gated

end FirstBlockDirectData.SecondStages.OriginalFibreRows

namespace ActualDirectFirstSource.SecondStages.OriginalFibreRows

variable {sourceBase : ℝ} {omega psi : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K omega psi} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualDirectFirstSource (E := W) hΓ μv C sourceBase
  finiteTest centered d a t Y₁ Y₂ X hX}
variable {R : s.SecondStages (E := E) (hDiff := hDiff)}

def prepared (rows : R.OriginalFibreRows Θ dimension width B Z) :
    R.prepared.OriginalFibreRows Θ dimension width B Z where
  source v D := (rows.source v D).prepared

end ActualDirectFirstSource.SecondStages.OriginalFibreRows

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.OriginalFibreRows.supported
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.OriginalFibreRows.gated
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.OriginalFibreRows.supported
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.OriginalFibreRows.gated
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.SecondStages.OriginalFibreRows.supported
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.SecondStages.OriginalFibreRows.gated
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.OriginalFibreRows.supported
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.OriginalFibreRows.gated
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.SecondStages.OriginalFibreRows.prepared
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.OriginalFibreRows.prepared
