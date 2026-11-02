import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualLeafArithmetic
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectSupportedLeaves

set_option linter.unusedSectionVars false

set_option Elab.async false
set_option stderrAsMessages false

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS DirectLeafArithmetic imports_done"
  log.flush

/-!
# Literal arithmetic coordinates of the direct parent leaves

The original Cartesian atlas supplies every direct-source slot cap.
The actual parent key then supplies the two common pairs, first divisor
and second divisor with both full padded allocations.  The direct
entrance has no prime-pool tag.  On the engine-prepared live family the
old first divisor is proved to divide the second common pair, using
the original coefficient gate before either Fourier transform.
-/

noncomputable section
open HeckePort.IdealMobiusDivisorSum
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
local instance directLeafArithmeticCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Z : ℝ} {cap : ℕ}

namespace FirstBlockDirectData

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable (p : FirstBlockDirectData chart M X hX)

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS DirectLeafArithmetic sourceCover_before"
  log.flush

theorem leftSourceCover_slotCap (LA : SourceCartesianAtlas left fullI)
    (hcap : LA.slotCount ≤ cap)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) :
    ∀ a, ((p.leftSourceCover LA S χ).branch a).slotCount ≤ cap := fun a =>
  (p.leftData.sourceCartesianCover_slotCount_le LA (primeSupport DE.1) DE.1
    p.left_columns (fun i => by rw [p.left_ideal]; exact b.left_residual i)
    (p.leftDivisorCoefficient S χ) a).trans hcap

theorem rightSourceCover_slotCap (RA : SourceCartesianAtlas right fullJ)
    (hcap : RA.slotCount ≤ cap)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) :
    ∀ a, ((p.rightSourceCover RA S χ).branch a).slotCount ≤ cap := fun a =>
  (p.rightData.sourceCartesianCover_slotCount_le RA (primeSupport DE.1) DE.2
    p.right_columns (fun j => by rw [p.right_ideal]; exact b.right_residual j)
    (p.rightDivisorCoefficient S χ) a).trans hcap

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS DirectLeafArithmetic sourceCover_done__arithmeticDefs_before"
  log.flush

namespace SecondStages

variable {p} (R : p.SecondStages (E := E) (hDiff := hDiff))
variable (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ)

def commonLabel (j : R.CoveredLeafKey LA RA) : Ideal (𝓞 K) × Ideal (𝓞 K) :=
  match j.2.2 with
  | .inl a => a.1.1.val
  | .inr a => a.1.1.val

def innerDivisor (j : R.CoveredLeafKey LA RA) : Ideal (𝓞 K) :=
  match j.2.2 with
  | .inl a => a.2.1.val
  | .inr a => a.2.1.val

def allocationFingerprint (hLA : LA.slotCount ≤ cap) (hRA : RA.slotCount ≤ cap)
    (j : R.CoveredLeafKey LA RA) : OriginalAllocationFingerprint K cap :=
  match j.2.2 with
  | .inl a => (R.left j.1 j.2.1).cappedAllocationFingerprint
      (p.leftSourceCover LA j.1 j.2.1) (p.leftSourceCover LA j.1 j.2.1)
      (p.leftSourceCover_slotCap LA hLA j.1 j.2.1)
      (p.leftSourceCover_slotCap LA hLA j.1 j.2.1) a
  | .inr a => (R.right j.1 j.2.1).cappedAllocationFingerprint
      (p.rightSourceCover RA j.1 j.2.1) (p.rightSourceCover RA j.1 j.2.1)
      (p.rightSourceCover_slotCap RA hRA j.1 j.2.1)
      (p.rightSourceCover_slotCap RA hRA j.1 j.2.1) a

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS DirectLeafArithmetic arithmeticDefs_done__allocationFingerprint_divisor_before"
  log.flush

@[simp] theorem allocationFingerprint_divisor
    (hLA : LA.slotCount ≤ cap) (hRA : RA.slotCount ≤ cap)
    (j : R.CoveredLeafKey LA RA) :
    (R.allocationFingerprint LA RA hLA hRA j).1 = R.innerDivisor LA RA j := by
  exact Sum.rec
    (motive := fun side =>
      (R.allocationFingerprint LA RA hLA hRA ⟨j.1, j.2.1, side⟩).1 =
        R.innerDivisor LA RA ⟨j.1, j.2.1, side⟩)
    (fun _ => rfl) (fun _ => rfl) j.2.2

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS DirectLeafArithmetic allocationFingerprint_divisor_done__commonLabel_nonzero_before"
  log.flush

theorem commonLabel_nonzero (j : R.CoveredLeafKey LA RA) :
    (R.commonLabel LA RA j).1 ≠ 0 ∧ (R.commonLabel LA RA j).2 ≠ 0 := by
  exact Sum.rec
    (motive := fun side =>
      (R.commonLabel LA RA ⟨j.1, j.2.1, side⟩).1 ≠ 0 ∧
        (R.commonLabel LA RA ⟨j.1, j.2.1, side⟩).2 ≠ 0)
    (fun a => commonSupportPool_nonzero _ _ _ _ _ a.1.1.property)
    (fun a => commonSupportPool_nonzero _ _ _ _ _ a.1.1.property) j.2.2

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS DirectLeafArithmetic commonLabel_nonzero_done__commonLabel_support_eq_before"
  log.flush

theorem commonLabel_support_eq (j : R.CoveredLeafKey LA RA) :
    primeSupport (R.commonLabel LA RA j).1 = primeSupport (R.commonLabel LA RA j).2 := by
  exact Sum.rec
    (motive := fun side =>
      primeSupport (R.commonLabel LA RA ⟨j.1, j.2.1, side⟩).1 =
        primeSupport (R.commonLabel LA RA ⟨j.1, j.2.1, side⟩).2)
    (fun a => commonSupportPool_support_eq _ _ _ _ _ a.1.1.property)
    (fun a => commonSupportPool_support_eq _ _ _ _ _ a.1.1.property) j.2.2

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS DirectLeafArithmetic commonLabel_support_eq_done"
  log.flush

variable
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS DirectLeafArithmetic prepared_live_old_mask_before"
  log.flush

/-- The first divisor is inherited on genuine live direct sources,
from the original coefficient gate and the engine's support preparation. -/
theorem prepared_live_old_mask
    (exceptional : R.prepared.CoverHybridPredicates LA RA)
    (j : R.prepared.CoveredLeafKey LA RA)
    (hj : (R.prepared.coveredLeaf LA RA NL NR hNL hNR exceptional j).Live) :
    Squarefree j.1.val ∧
      j.1.val ∣ (R.prepared.commonLabel LA RA j).1 ∧
      j.1.val ∣ (R.prepared.commonLabel LA RA j).2 := by
  have hS := R.prepared.coveredLeaf_weight_nonzero_squarefree
    LA RA NL NR hNL hNR exceptional j hj.1
  refine ⟨hS, ?_⟩
  exact Sum.rec
    (motive := fun side =>
      (R.prepared.coveredLeaf LA RA NL NR hNL hNR exceptional
        ⟨j.1, j.2.1, side⟩).Live →
      j.1.val ∣ (R.prepared.commonLabel LA RA ⟨j.1, j.2.1, side⟩).1 ∧
        j.1.val ∣ (R.prepared.commonLabel LA RA ⟨j.1, j.2.1, side⟩).2)
    (fun a halive => by
      have hlive := ((R.left j.1 j.2.1).supported.gated.fiberCoveredLeaf
        (p.leftSourceCover LA j.1 j.2.1) (p.leftSourceCover LA j.1 j.2.1)
        (exceptional.left j.1 j.2.1) chart.kernel chart.leftPoint a).live_of_scale_live
          (classWeight (p := p) NL NR j.1 j.2.1 / NL j.1 j.2.1)
          (div_nonneg (classWeight_nonneg (p := p) NL NR j.1 j.2.1)
            (hNL j.1 j.2.1).le) halive
      have hs := (R.left j.1 j.2.1).supported_gated_fiberLeaf_live
        (p.leftSourceCover LA j.1 j.2.1) (p.leftSourceCover LA j.1 j.2.1)
        (exceptional.left j.1 j.2.1) chart.kernel chart.leftPoint a hlive
      exact (p.leftData.directSource (p.leftDivisorCoefficient j.1 j.2.1)).activeCommon_old_mask
        j.1.val hS (fun i _ hi =>
          FirstBlockDirectData.leftDivisorCoefficient_nonzero_dvd (p := p) j.1 j.2.1 i hi)
        a.1.1.val hs.2.1)
    (fun a halive => by
      have hlive := ((R.right j.1 j.2.1).supported.gated.fiberCoveredLeaf
        (p.rightSourceCover RA j.1 j.2.1) (p.rightSourceCover RA j.1 j.2.1)
        (exceptional.right j.1 j.2.1) chart.kernel (fun i => -chart.rightPoint i) a).live_of_scale_live
          (classWeight (p := p) NL NR j.1 j.2.1 / NR j.1 j.2.1)
          (div_nonneg (classWeight_nonneg (p := p) NL NR j.1 j.2.1)
            (hNR j.1 j.2.1).le) halive
      have hs := (R.right j.1 j.2.1).supported_gated_fiberLeaf_live
        (p.rightSourceCover RA j.1 j.2.1) (p.rightSourceCover RA j.1 j.2.1)
        (exceptional.right j.1 j.2.1) chart.kernel (fun i => -chart.rightPoint i) a hlive
      exact (p.rightData.directSource (p.rightDivisorCoefficient j.1 j.2.1)).activeCommon_old_mask
        j.1.val hS (fun i _ hi =>
          FirstBlockDirectData.rightDivisorCoefficient_nonzero_dvd (p := p) j.1 j.2.1 i hi)
        a.1.1.val hs.2.1) j.2.2 hj

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS DirectLeafArithmetic prepared_live_old_mask_done__prepared_live_second_valid_before"
  log.flush

theorem prepared_live_second_valid
    (exceptional : R.prepared.CoverHybridPredicates LA RA)
    (j : R.prepared.CoveredLeafKey LA RA)
    (hj : (R.prepared.coveredLeaf LA RA NL NR hNL hNR exceptional j).Live) :
    Valid j.1.val (R.prepared.commonLabel LA RA j, ∅) := by
  have hm := R.prepared_live_old_mask LA RA NL NR hNL hNR exceptional j hj
  have hn := R.prepared.commonLabel_nonzero LA RA j
  exact ⟨hn.1, hn.2, R.prepared.commonLabel_support_eq LA RA j,
    hm.2.1, hm.2.2, Finset.empty_subset _⟩

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS DirectLeafArithmetic prepared_live_second_valid_done"
  log.flush

end SecondStages
end FirstBlockDirectData

variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX}

namespace ActualDirectFirstSource.SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS DirectLeafArithmetic parentArithmeticDefs_before"
  log.flush

def commonLabel (j : R.CoveredLeafKey L) : Ideal (𝓞 K) × Ideal (𝓞 K) :=
  (R j.1 j.2.1).commonLabel L L j.2.2

def innerDivisor (j : R.CoveredLeafKey L) : Ideal (𝓞 K) :=
  (R j.1 j.2.1).innerDivisor L L j.2.2

def arithmeticLabels (hcap : L.slotCount ≤ cap)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization) :
    OriginalArithmeticLabels K (R.liveLeaves L exceptional N) cap where
  first j := (j.val.1.val, ∅)
  firstDivisor j := j.val.2.2.1.val
  second j := (R.commonLabel L j.val, ∅)
  allocation j :=
    (R j.val.1 j.val.2.1).allocationFingerprint L L hcap hcap j.val.2.2

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS DirectLeafArithmetic parentArithmeticDefs_done"
  log.flush

@[simp] theorem arithmeticLabels_first (hcap : L.slotCount ≤ cap)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.liveLeaves L exceptional N) :
    (R.arithmeticLabels L hcap exceptional N).first j = (j.val.1.val, ∅) := rfl

@[simp] theorem arithmeticLabels_firstDivisor (hcap : L.slotCount ≤ cap)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.liveLeaves L exceptional N) :
    (R.arithmeticLabels L hcap exceptional N).firstDivisor j = j.val.2.2.1.val := rfl

@[simp] theorem arithmeticLabels_second (hcap : L.slotCount ≤ cap)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.liveLeaves L exceptional N) :
    (R.arithmeticLabels L hcap exceptional N).second j = (R.commonLabel L j.val, ∅) := rfl

@[simp] theorem arithmeticLabels_secondDivisor (hcap : L.slotCount ≤ cap)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.liveLeaves L exceptional N) :
    ((R.arithmeticLabels L hcap exceptional N).allocation j).1 = R.innerDivisor L j.val :=
  (R j.val.1 j.val.2.1).allocationFingerprint_divisor L L hcap hcap j.val.2.2

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS DirectLeafArithmetic prepared_arithmeticLabels_second_valid_before"
  log.flush

/-- The direct input's actual live labels satisfy the second old-mask
condition internally after the proved preparation. -/
theorem prepared_arithmeticLabels_second_valid (hcap : L.slotCount ≤ cap)
    (exceptional : R.prepared.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.prepared.liveLeaves L exceptional N) :
    Valid ((R.prepared.arithmeticLabels L hcap exceptional N).firstDivisor j)
      ((R.prepared.arithmeticLabels L hcap exceptional N).second j) := by
  have hlive := ((R.prepared j.val.1 j.val.2.1).coveredLeaf L L
    (N.left j.val.1 j.val.2.1) (N.right j.val.1 j.val.2.1)
    (N.left_pos j.val.1 j.val.2.1) (N.right_pos j.val.1 j.val.2.1)
    (exceptional j.val.1 j.val.2.1) j.val.2.2).live_of_scale_live
      (s.fiber : ℝ) (Nat.cast_nonneg s.fiber)
      (R.prepared.liveLeaves_spec L exceptional N j)
  exact (R j.val.1 j.val.2.1).prepared_live_second_valid L L
    (N.left j.val.1 j.val.2.1) (N.right j.val.1 j.val.2.1)
    (N.left_pos j.val.1 j.val.2.1) (N.right_pos j.val.1 j.val.2.1)
    (exceptional j.val.1 j.val.2.1) j.val.2.2 hlive

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS DirectLeafArithmetic prepared_arithmeticLabels_second_valid_done"
  log.flush

end ActualDirectFirstSource.SecondStages
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.SecondStages.allocationFingerprint_divisor
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.SecondStages.prepared_live_second_valid
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.arithmeticLabels_secondDivisor
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.prepared_arithmeticLabels_second_valid

#eval show IO Unit from do
  let log ← IO.getStderr
  log.putStrLn "G2_PROGRESS DirectLeafArithmetic axioms_done"
  log.flush
