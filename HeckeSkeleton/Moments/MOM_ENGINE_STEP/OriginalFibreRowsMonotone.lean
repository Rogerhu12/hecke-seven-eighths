import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PreparedOriginalFibreRows

/-!
# Enlarging the norm box of the original physical classifier

Only the two norm inequalities change. Original support sets, ideals,
row codes and encoding maps are retained, through each source side
and each original pool tag. The base of the pool is independent of
this certificate's norm-window base.
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
variable {Θ : Type*} [Fintype Θ] {dimension width : ℕ} {B B' Z : ℝ}

namespace ActualGaussStage

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest}

namespace OriginalFibreRows

def enlargeBound (rows : s.OriginalFibreRows Θ dimension width B Z)
    (hZ : 1 ≤ Z) (hB : B ≤ B') :
    s.OriginalFibreRows Θ dimension width B' Z where
  support := rows.support
  maskIdeal := rows.maskIdeal
  rowIdeal := rows.rowIdeal
  mask_nonzero := rows.mask_nonzero
  row_nonzero := rows.row_nonzero
  maskPrimes := rows.maskPrimes
  row_divides := rows.row_divides
  mask_norm := rows.mask_norm.trans (Real.rpow_le_rpow_of_exponent_le hZ hB)
  row_norm DE := (rows.row_norm DE).trans (Real.rpow_le_rpow_of_exponent_le hZ hB)
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

def enlargeBound (rows : s.OriginalFibreRows Θ dimension width B Z)
    (hZ : 1 ≤ Z) (hB : B ≤ B') :
    s.OriginalFibreRows Θ dimension width B' Z where
  main := rows.main.enlargeBound hZ hB
  one p := (rows.one p).enlargeBound hZ hB
  six p := (rows.six p).enlargeBound hZ hB
  seven p := (rows.seven p).enlargeBound hZ hB

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

def enlargeBound (rows : s.OriginalFibreRows Θ dimension width B Z)
    (hZ : 1 ≤ Z) (hB : B ≤ B') :
    s.OriginalFibreRows Θ dimension width B' Z where
  left S χ := (rows.left S χ).enlargeBound hZ hB
  right S χ := (rows.right S χ).enlargeBound hZ hB

end FirstBlockPoolData.SecondStages.OriginalFibreRows

namespace ActualFirstSource.SecondStages.OriginalFibreRows

variable {omega psi : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K omega psi} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}
variable {R : s.SecondStages (E := E) (hDiff := hDiff)}

def enlargeBound (rows : R.OriginalFibreRows Θ dimension width B Z)
    (hZ : 1 ≤ Z) (hB : B ≤ B') :
    R.OriginalFibreRows Θ dimension width B' Z where
  source v D := (rows.source v D).enlargeBound hZ hB

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

def enlargeBound (rows : s.OriginalFibreRows Θ dimension width B Z)
    (hZ : 1 ≤ Z) (hB : B ≤ B') :
    s.OriginalFibreRows Θ dimension width B' Z where
  left S χ := (rows.left S χ).enlargeBound hZ hB
  right S χ := (rows.right S χ).enlargeBound hZ hB

end FirstBlockDirectData.SecondStages.OriginalFibreRows

namespace ActualDirectFirstSource.SecondStages.OriginalFibreRows

variable {sourceBase : ℝ} {omega psi : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K omega psi} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualDirectFirstSource (E := W) hΓ μv C sourceBase
  finiteTest centered d a t Y₁ Y₂ X hX}
variable {R : s.SecondStages (E := E) (hDiff := hDiff)}

def enlargeBound (rows : R.OriginalFibreRows Θ dimension width B Z)
    (hZ : 1 ≤ Z) (hB : B ≤ B') :
    R.OriginalFibreRows Θ dimension width B' Z where
  source v D := (rows.source v D).enlargeBound hZ hB

end ActualDirectFirstSource.SecondStages.OriginalFibreRows

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.OriginalFibreRows.enlargeBound
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.OriginalFibreRows.enlargeBound
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.SecondStages.OriginalFibreRows.enlargeBound
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.OriginalFibreRows.enlargeBound
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.SecondStages.OriginalFibreRows.enlargeBound
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.OriginalFibreRows.enlargeBound
