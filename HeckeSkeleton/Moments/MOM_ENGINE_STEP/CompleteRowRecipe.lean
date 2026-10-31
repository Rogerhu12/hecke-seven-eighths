import HeckeGeneral.Analysis.DecomposedZeroSlotMomentData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.JointRowBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FiniteNormalizedChildren

/-!
# The complete original arithmetic row recipe in every actual child

The probe and row-character input are fixed original MOM_BASE data.
Each allowed complete ideal is exterior to the same A.Sf, and its
character is the literal completeIdealRowCharacter in a unit sector
chosen before the Fourier parameter.  An arbitrary row-character
function is not an input to this recipe.

All allowed rows are calibrated, including rows outside the physical
source image.  Hence deleting the last slot may enlarge pairedRows
without losing the character identification.  The joint row-budget
filter only removes allowed rows.  The actual normalized family uses
the same fixed sectors and the same original probe after clipping,
normalization, capacity restriction and time freezing.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

/-- This is an original full-row arithmetic dictionary, not a final
admissibility predicate or an estimate for any polynomial. -/
structure CompleteRowRecipe (A : SArithmeticData K)
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
    {X : Type*} (data : X → MomentData K ω ψ) where
  sector : HeckeGeneral.Analysis.NonzeroIdeal K →
    SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
  exterior : ∀ ξ u, (data ξ).allowedRow u →
    completeIdealIsExterior K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u
  character : ∀ ξ u, (data ξ).allowedRow u →
    (data ξ).rowCharacter u =
      completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R (sector u) u

namespace CompleteRowRecipe

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {X : Type*} {data other : X → MomentData K ω ψ}
variable (Q : CompleteRowRecipe A P R data)

/-- Only the allowed predicate may shrink.  The character function
itself remains identical on the actual transformed data. -/
def ofAllowedSubset
    (allowed : ∀ ξ u, (other ξ).allowedRow u → (data ξ).allowedRow u)
    (character : ∀ ξ, (other ξ).rowCharacter = (data ξ).rowCharacter) :
    CompleteRowRecipe A P R other where
  sector := Q.sector
  exterior ξ u hu := Q.exterior ξ u (allowed ξ u hu)
  character ξ u hu := by
    rw [character ξ]
    exact Q.character ξ u (allowed ξ u hu)

def clipped (a : RealParameters) (Z : ℝ) (hZ : 0 < Z) :
    CompleteRowRecipe A P R (fun ξ => clipPlainData (data ξ) a Z hZ) :=
  Q.ofAllowedSubset (fun _ _ hu => hu) (fun _ => rfl)

def normalized (B : X → ℝ) (hB : ∀ ξ, 0 < B ξ) :
    CompleteRowRecipe A P R
      (fun ξ => normalizedMomentProfiles (data ξ) (B ξ) (hB ξ)) :=
  Q.ofAllowedSubset (fun _ _ hu => hu) (fun _ => rfl)

def frozen (t : X → ℝ) :
    CompleteRowRecipe A P R (fun ξ => frozenMomentProfiles (data ξ) (t ξ)) :=
  Q.ofAllowedSubset (fun _ _ hu => hu) (fun _ => rfl)

def restricted (keep : ∀ ξ, Finset (Fin (data ξ).geometry.slotCount)) :
    CompleteRowRecipe A P R (fun ξ => (data ξ).restrictSlots (keep ξ)) :=
  Q.ofAllowedSubset (fun _ _ hu => hu) (fun _ => rfl)

def jointRows (support : HeckeGeneral.Analysis.NonzeroIdeal K → A.Exterior) (budget : ℝ) :
    CompleteRowRecipe A P R (fun ξ => jointRowBudgetData (data ξ) support budget) :=
  Q.ofAllowedSubset (fun _ _ hu => hu.1) (fun _ => rfl)

/-- This has exactly the identification field needed by ordinary
reflection, for every paired row and any parameter/width choice. -/
theorem identify (ξ : X) (a : RealParameters) (Z : ℝ)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hu : u ∈ pairedRows (data ξ) a Z) :
    ∃ v : ExteriorIdeal K (A.Sf : Set (HeightOneSpectrum (𝓞 K))), v.val = u ∧
      ∃ sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
        (data ξ).rowCharacter u =
          completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R sector u := by
  have hallowed := (((data ξ).rows_spec _ u).1 (Finset.mem_filter.mp hu).1).1
  exact ⟨⟨u, Q.exterior ξ u hallowed⟩, rfl, Q.sector u, Q.character ξ u hallowed⟩

/-- The selected sector is the same fixed sector even after the
paired-row predicate changes because all slots were removed. -/
theorem paired_character (ξ : X) (a : RealParameters) (Z : ℝ)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hu : u ∈ pairedRows (data ξ) a Z) :
    (data ξ).rowCharacter u =
      completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R (Q.sector u) u :=
  Q.character ξ u ((((data ξ).rows_spec _ u).1 (Finset.mem_filter.mp hu).1).1)

end CompleteRowRecipe

section OriginalCompleteData

variable (A : SArithmeticData K)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

/-- The literal original complete-ideal constructor supplies this raw
recipe by reduction, for every profile family and every complete row. -/
def completeRowRecipe_ofDecomposed {X : Type*}
    (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (W : X → IdealTest K) :
    CompleteRowRecipe A P R (fun ξ =>
      decomposedZeroSlotMomentData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R ω ψ sector (W ξ)) where
  sector _ := sector
  exterior _ _ hu := hu
  character _ _ _ := rfl

end OriginalCompleteData

namespace ActualAllocatedSource.Calibration

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k : ℕ} {s : ActualAllocatedSource A V H k}
variable (D : s.Calibration (σ := σ) ω ψ)

/-- The engine's actual source-preserving filter uses precisely the
same fixed probe, row-character input and unit sectors. -/
def completeRows_withJointRowBudget (Q : CompleteRowRecipe A P R D.data)
    (M : ActualMovingMaskRecipe A D.data)
    (hsource : ∀ h ∈ s.rows,
      A.exteriorNorm (s.originalIdeal h) * A.exteriorNorm (M.support (s.row h).momentIdeal) ≤
        s.normFactor h * s.base ^ (D.parameters.m + D.parameters.q)) :
    CompleteRowRecipe A P R (D.withJointRowBudget M hsource).data :=
  Q.jointRows M.support (s.base ^ (D.parameters.m + D.parameters.q))

end ActualAllocatedSource.Calibration

namespace ActualAllocatedSource.Calibration.NormalizedCapacityData.Child

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k : ℕ} {s : ActualAllocatedSource A V H k}
variable {D : s.Calibration (σ := σ) ω ψ} {G : D.NormalizedCapacityData}
variable (out : G.Child)

/-- The actual chosen, normalized and frozen child retains the full
original arithmetic dictionary, not only the physical source image. -/
def completeRowRecipe (Q : CompleteRowRecipe A P R D.data) :
    CompleteRowRecipe A P R out.frozenData :=
  Q.ofAllowedSubset (fun _ _ hu => hu) (fun _ => rfl)

theorem completeRowRecipe_sector (Q : CompleteRowRecipe A P R D.data) :
    (out.completeRowRecipe Q).sector = Q.sector := rfl

theorem completeRowIdentify (Q : CompleteRowRecipe A P R D.data) (ξ : V)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hu : u ∈ pairedRows (out.frozenData ξ) out.parameters s.base) :
    ∃ v : ExteriorIdeal K (A.Sf : Set (HeightOneSpectrum (𝓞 K))), v.val = u ∧
      ∃ sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
        (out.frozenData ξ).rowCharacter u =
          completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R sector u :=
  (out.completeRowRecipe Q).identify ξ out.parameters s.base u hu

end ActualAllocatedSource.Calibration.NormalizedCapacityData.Child

namespace ActualNormalizedPairFamily

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {V Λ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : ℝ}
variable (family : ActualNormalizedPairFamily A σ V Λ ω ψ Z) (labels : Finset Λ)

/-- Inputs concern the original branch calibrations, before the active
carrier and its capacity children are selected. -/
structure CompleteRowInputs where
  left : ∀ b ∈ labels, CompleteRowRecipe A P R (family.leftCalibration b).data
  right : ∀ b ∈ labels, CompleteRowRecipe A P R (family.rightCalibration b).data

namespace CompleteRowInputs

variable {family labels} (raw : family.CompleteRowInputs (P := P) (R := R) labels)

def leftRecipe (b : family.active labels) :
    CompleteRowRecipe A P R (family.leftData labels b) :=
  (family.leftChild labels b).completeRowRecipe (raw.left b.val (Finset.mem_filter.mp b.property).1)

def rightRecipe (b : family.active labels) :
    CompleteRowRecipe A P R (family.rightData labels b) :=
  (family.rightChild labels b).completeRowRecipe (raw.right b.val (Finset.mem_filter.mp b.property).1)

/-- Both identifications refer to the literal public frozen data and
their actual paired rows, for the same original probe and row recipe. -/
theorem identify (b : family.active labels) (ξ : V) :
    (∀ u ∈ pairedRows (family.leftData labels b ξ) (family.leftParameters labels b) Z,
      ∃ v : ExteriorIdeal K (A.Sf : Set (HeightOneSpectrum (𝓞 K))), v.val = u ∧
        ∃ sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
          (family.leftData labels b ξ).rowCharacter u =
            completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R sector u) ∧
    (∀ u ∈ pairedRows (family.rightData labels b ξ) (family.rightParameters labels b) Z,
      ∃ v : ExteriorIdeal K (A.Sf : Set (HeightOneSpectrum (𝓞 K))), v.val = u ∧
        ∃ sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
          (family.rightData labels b ξ).rowCharacter u =
            completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R sector u) :=
  ⟨fun u hu => (raw.leftRecipe b).identify ξ (family.leftParameters labels b) Z u hu,
    fun u hu => (raw.rightRecipe b).identify ξ (family.rightParameters labels b) Z u hu⟩

end CompleteRowInputs
end ActualNormalizedPairFamily

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteRowRecipe.identify
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.NormalizedCapacityData.Child.completeRowIdentify
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.CompleteRowInputs.identify
