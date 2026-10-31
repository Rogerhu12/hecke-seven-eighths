import HeckeSkeleton.Moments.MOM_ENGINE_STEP.LiveSourceConditions
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCoveredFibre
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalSourceSlotCaps
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalArithmeticCarrier

/-!
# Arithmetic projections of the literal parent leaves

The occurrence cap is inherited from the original Cartesian atlas.
Every projection below is computed from the actual dependent leaf key:
both common pairs, both independent divisors, both complete allocations,
and the original main/1/6/7 prime tag. Finite phases and actual mask/row
labels remain in the original carrier and are charged by its fibres.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup HeckePort.Moments.Support

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
local instance actualLeafArithmeticCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*} {cap : ℕ}

namespace FirstGaussPoolData

variable {d : FirstGaussPoolData C P ι} {c : ι → ℂ}

/-- This intermediate property is proved from the original atlas below,
and never needs to be assumed for a computed source cover. -/
structure SourceCovers.SlotCap (B : d.SourceCovers c) (cap : ℕ) : Prop where
  main : ∀ a, (B.main.branch a).slotCount ≤ cap
  residual : ∀ p n a, ((B.residual p n).branch a).slotCount ≤ cap

theorem sourceCoversOfOriginal_slotCap
    (d : FirstGaussPoolData C P ι) (c : ι → ℂ)
    {originalColumns : Finset ι} {originalIdeal : ι → A.Exterior}
    (T : SourceCartesianAtlas originalColumns originalIdeal)
    (S : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
    (hcolumns : d.columns = originalColumns.filter
      (fun i => supportExtract (originalIdeal i).val S = D))
    (hideal : ∀ i, (d.ideal i).val = supportResidual (originalIdeal i).val S)
    (hcap : T.slotCount ≤ cap) :
    (d.sourceCoversOfOriginal c T S D hcolumns hideal).SlotCap cap where
  main a := (d.mainSourceCartesianCover_slotCount_le T S D hcolumns hideal c a).trans hcap
  residual p n a :=
    (d.residualSourceCartesianCover_slotCount_le T S D hcolumns hideal p.val n c a).trans hcap

end FirstGaussPoolData

namespace ActualGaussStage

variable {G : ActualGaussSource C ι}
variable (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
variable (LC RC : SourceCartesianCover G.columns G.ideal)

/-- Padding both real occurrence allocations uses only the inherited
source-cover cap; no allocation count or new allocation is chosen. -/
def cappedAllocationFingerprint
    (hLC : ∀ a, (LC.branch a).slotCount ≤ cap)
    (hRC : ∀ a, (RC.branch a).slotCount ≤ cap)
    (j : s.CoveredLeafKey LC RC) : OriginalAllocationFingerprint K cap :=
  coveredAllocationFingerprint
    (fun v => v.leftSlots_le hLC) (fun v => v.rightSupportSlots_le hRC) j

@[simp] theorem cappedAllocationFingerprint_divisor
    (hLC : ∀ a, (LC.branch a).slotCount ≤ cap)
    (hRC : ∀ a, (RC.branch a).slotCount ≤ cap)
    (j : s.CoveredLeafKey LC RC) :
    (s.cappedAllocationFingerprint LC RC hLC hRC j).1 = j.2.1.val := rfl

end ActualGaussStage

namespace ActualPoolStages

variable {d : FirstGaussPoolData C P ι} {c : ι → ℂ}
variable (s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest)
variable (B : d.SourceCovers c)

def allocationFingerprint (hcap : B.SlotCap cap) :
    s.CoveredLeafKey B → OriginalAllocationFingerprint K cap
  | .inl j => s.main.cappedAllocationFingerprint B.main B.main hcap.main hcap.main j
  | .inr (.inl ⟨p, j⟩) =>
    (s.one p).cappedAllocationFingerprint (B.residual p 1) (B.residual p 1)
      (hcap.residual p 1) (hcap.residual p 1) j
  | .inr (.inr (.inl ⟨p, j⟩)) =>
    (s.six p).cappedAllocationFingerprint (B.residual p 6) (B.residual p 6)
      (hcap.residual p 6) (hcap.residual p 6) j
  | .inr (.inr (.inr ⟨p, j⟩)) =>
    (s.seven p).cappedAllocationFingerprint (B.residual p 7) (B.residual p 7)
      (hcap.residual p 7) (hcap.residual p 7) j

@[simp] theorem allocationFingerprint_divisor (hcap : B.SlotCap cap)
    (j : s.CoveredLeafKey B) :
    (s.allocationFingerprint B hcap j).1 = s.innerDivisor B j := by
  rcases j with j | (⟨p, j⟩ | (⟨p, j⟩ | ⟨p, j⟩)) <;> rfl

def amplifierTag : s.CoveredLeafKey B → Option (ℕ × ExteriorPrime A)
  | .inl _ => none
  | .inr (.inl ⟨p, _⟩) => some (1, p.val)
  | .inr (.inr (.inl ⟨p, _⟩)) => some (6, p.val)
  | .inr (.inr (.inr ⟨p, _⟩)) => some (7, p.val)

theorem amplifierTag_mem (j : s.CoveredLeafKey B) (n : ℕ) (p : ExteriorPrime A)
    (h : s.amplifierTag B j = some (n, p)) :
    n ∈ ({1, 6, 7} : Finset ℕ) ∧ p ∈ P.primes := by
  rcases j with j | (⟨q, j⟩ | (⟨q, j⟩ | ⟨q, j⟩))
  · cases h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨by simp, q.property⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨by simp, q.property⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨by simp, q.property⟩

end ActualPoolStages

namespace FirstBlockPoolData

variable {κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable (p : FirstBlockPoolData chart P M X hX)

theorem leftSourceCovers_slotCap (LA : SourceCartesianAtlas left fullI)
    (hcap : LA.slotCount ≤ cap)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) : (p.leftSourceCovers LA S χ).SlotCap cap :=
  (p.divisorPools.leftData S).sourceCoversOfOriginal_slotCap
    (p.leftDivisorCoefficient S χ) LA (primeSupport DE.1) DE.1
    ((p.divisorPools.left_columns S).trans p.left_columns)
    (by intro i; rw [p.divisorPools.left_ideal S, p.left_ideal]; exact b.left_residual i) hcap

theorem rightSourceCovers_slotCap (RA : SourceCartesianAtlas right fullJ)
    (hcap : RA.slotCount ≤ cap)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) : (p.rightSourceCovers RA S χ).SlotCap cap :=
  (p.divisorPools.rightData S).sourceCoversOfOriginal_slotCap
    (p.rightDivisorCoefficient S χ) RA (primeSupport DE.1) DE.2
    ((p.divisorPools.right_columns S).trans p.right_columns)
    (by intro i; rw [p.divisorPools.right_ideal S, p.right_ideal]; exact b.right_residual i) hcap

namespace SecondStages

variable {p} (R : p.SecondStages (E := E) (hDiff := hDiff))
variable (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ)

def allocationFingerprint (hLA : LA.slotCount ≤ cap) (hRA : RA.slotCount ≤ cap)
    (j : R.CoveredLeafKey LA RA) : OriginalAllocationFingerprint K cap :=
  match j.2.2 with
  | .inl a => (R.left j.1 j.2.1).allocationFingerprint (p.leftSourceCovers LA j.1 j.2.1)
      (p.leftSourceCovers_slotCap LA hLA j.1 j.2.1) a
  | .inr a => (R.right j.1 j.2.1).allocationFingerprint (p.rightSourceCovers RA j.1 j.2.1)
      (p.rightSourceCovers_slotCap RA hRA j.1 j.2.1) a

@[simp] theorem allocationFingerprint_divisor
    (hLA : LA.slotCount ≤ cap) (hRA : RA.slotCount ≤ cap)
    (j : R.CoveredLeafKey LA RA) :
    (R.allocationFingerprint LA RA hLA hRA j).1 = R.innerDivisor LA RA j := by
  rcases j with ⟨S, χ, j | j⟩
  · exact (R.left S χ).allocationFingerprint_divisor _ _ j
  · exact (R.right S χ).allocationFingerprint_divisor _ _ j

def amplifierTag (j : R.CoveredLeafKey LA RA) : Option (ℕ × ExteriorPrime A) :=
  match j.2.2 with
  | .inl a => (R.left j.1 j.2.1).amplifierTag (p.leftSourceCovers LA j.1 j.2.1) a
  | .inr a => (R.right j.1 j.2.1).amplifierTag (p.rightSourceCovers RA j.1 j.2.1) a

theorem amplifierTag_mem (j : R.CoveredLeafKey LA RA) (n : ℕ) (q : ExteriorPrime A)
    (h : R.amplifierTag LA RA j = some (n, q)) :
    n ∈ ({1, 6, 7} : Finset ℕ) ∧ q ∈ P.primes := by
  rcases j with ⟨S, χ, j | j⟩
  · exact (R.left S χ).amplifierTag_mem _ j n q h
  · exact (R.right S χ).amplifierTag_mem _ j n q h

end SecondStages
end FirstBlockPoolData

variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}

namespace ActualFirstSource.SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)

/-- These are the actual projections supplied to the internally built
image carrier. Empty common-subset coordinates do not erase physical
masks: those masks remain in this original source's fibre. -/
def arithmeticLabels (hcap : L.slotCount ≤ cap)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization) :
    OriginalArithmeticLabels K (R.liveLeaves L exceptional N) cap where
  first j := (j.val.1.val, ∅)
  firstDivisor j := j.val.2.2.1.val
  second j := (R.commonLabel L j.val, ∅)
  allocation j :=
    (R j.val.1 j.val.2.1).allocationFingerprint L L hcap hcap j.val.2.2

@[simp] theorem arithmeticLabels_secondDivisor (hcap : L.slotCount ≤ cap)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.liveLeaves L exceptional N) :
    ((R.arithmeticLabels L hcap exceptional N).allocation j).1 =
      R.innerDivisor L j.val :=
  (R j.val.1 j.val.2.1).allocationFingerprint_divisor L L hcap hcap j.val.2.2

def arithmeticTag (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.liveLeaves L exceptional N) : Option (ℕ × ExteriorPrime A) :=
  (R j.val.1 j.val.2.1).amplifierTag L L j.val.2.2

theorem arithmeticTag_mem (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.liveLeaves L exceptional N) (n : ℕ) (q : ExteriorPrime A)
    (h : R.arithmeticTag L exceptional N j = some (n, q)) :
    n ∈ ({1, 6, 7} : Finset ℕ) ∧ q ∈ P.primes :=
  (R j.val.1 j.val.2.1).amplifierTag_mem L L j.val.2.2 n q h

end ActualFirstSource.SecondStages
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.sourceCoversOfOriginal_slotCap
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.arithmeticLabels_secondDivisor
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.arithmeticTag_mem
