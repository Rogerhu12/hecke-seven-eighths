import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectLeafArithmetic
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualLeafNormWindows

set_option linter.unusedSectionVars false

/-!
# Original norm windows on the genuine direct arithmetic carrier

Only the original per-column ideal window and old-mask divisibility
enter the result.  Common extraction and the actual source dictionary
transport these bounds to both independent divisors.  The prepared
live leaf supplies squarefreeness and the inherited second old mask.
No prime pool or transformed-label estimate is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup HeckePort.Moments.Support
open CommonSupportMass UniqueFactorizationMonoid

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
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local instance directLeafNormWindowsCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Z : ℝ}

namespace FirstBlockDirectData

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable (p : FirstBlockDirectData chart M X hX)

theorem left_ideal_norm_le (Y : ℝ)
    (hN : ∀ i ∈ left, (Ideal.absNorm (fullI i).val : ℝ) ≤ Y)
    (i : ι) (hi : i ∈ p.leftData.columns) :
    (Ideal.absNorm (p.leftData.ideal i).val : ℝ) ≤ Y := by
  sorry

theorem right_ideal_norm_le (Y : ℝ)
    (hN : ∀ i ∈ right, (Ideal.absNorm (fullJ i).val : ℝ) ≤ Y)
    (i : κ) (hi : i ∈ p.rightData.columns) :
    (Ideal.absNorm (p.rightData.ideal i).val : ℝ) ≤ Y := by
  sorry

theorem firstDivisor_norm_le (Y : ℝ)
    (hN : ∀ i ∈ right, (Ideal.absNorm (fullJ i).val : ℝ) ≤ Y)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) :
    (Ideal.absNorm S.val : ℝ) ≤ Y := by
  sorry

namespace SecondStages

variable {p} (R : p.SecondStages (E := E) (hDiff := hDiff))
variable (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ)

theorem commonLabel_norm_le (Y : ℝ)
    (hL : ∀ i ∈ left, (Ideal.absNorm (fullI i).val : ℝ) ≤ Y)
    (hR : ∀ i ∈ right, (Ideal.absNorm (fullJ i).val : ℝ) ≤ Y)
    (j : R.CoveredLeafKey LA RA) :
    (Ideal.absNorm (R.commonLabel LA RA j).1 : ℝ) ≤ Y ∧
      (Ideal.absNorm (R.commonLabel LA RA j).2 : ℝ) ≤ Y := by
  sorry

theorem innerDivisor_norm_le (Y : ℝ)
    (hL : ∀ i ∈ left, (Ideal.absNorm (fullI i).val : ℝ) ≤ Y)
    (hR : ∀ i ∈ right, (Ideal.absNorm (fullJ i).val : ℝ) ≤ Y)
    (j : R.CoveredLeafKey LA RA) :
    (Ideal.absNorm (R.innerDivisor LA RA j) : ℝ) ≤ Y := by
  sorry

variable
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)

theorem prepared_live_inner_squarefree
    (exceptional : R.prepared.CoverHybridPredicates LA RA)
    (j : R.prepared.CoveredLeafKey LA RA)
    (hj : (R.prepared.coveredLeaf LA RA NL NR hNL hNR exceptional j).Live) :
    Squarefree (R.prepared.innerDivisor LA RA j) := by
  sorry

end SecondStages
end FirstBlockDirectData

variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX}

namespace ActualDirectFirstSource.SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)

theorem prepared_live_inner_divisor_squarefree
    (exceptional : R.prepared.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.prepared.liveLeaves L exceptional N) :
    Squarefree (R.prepared.innerDivisor L j.val) := by
  sorry

/-- Admissibility is derived from the original source windows on the
same actual live carrier, with both divisors and both allocations kept. -/
theorem arithmeticLabels_admissible {cap : ℕ} (hcap : L.slotCount ≤ cap)
    (exceptional : R.prepared.CoverHybridPredicates L) (N : s.Normalization)
    (B : ℝ) (oldMask : Ideal (𝓞 K)) (hs : Squarefree oldMask)
    (hmask : ∀ i ∈ s.columns, oldMask ∣ (s.ideal i).val)
    (hN : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B) :
    (R.prepared.arithmeticLabels L hcap exceptional N).carrier.Admissible
      (cap + 2) B Z oldMask := by
  sorry

end ActualDirectFirstSource.SecondStages
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.SecondStages.innerDivisor_norm_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.prepared_live_inner_divisor_squarefree
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.arithmeticLabels_admissible
