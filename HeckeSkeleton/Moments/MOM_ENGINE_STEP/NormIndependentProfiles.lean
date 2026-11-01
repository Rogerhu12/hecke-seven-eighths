import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CharacterRecipePreservation
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FiniteNormalizedChildren

/-!
# Literal norm profiles throughout the actual child construction

The original two plain tests have one norm function for all allowed
rows.  This is an identity on each profile, before any polynomial or
estimate.  Prime profiles already have no row argument in PrimeWindow.

The identity is retained by the actual clipping, positive normalization,
slot restriction, time freezing and source-preserving row filter.  In
particular the same chosen capacity child has a norm profile; no new
child or profile is chosen after its kernel has been constructed.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open DedekindZetaZeroFree

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

/-- Both functions may depend on the original Fourier parameters and
on time, but not on the moving arithmetic row.  Every allowed row is
covered, so deleting the last slot does not lose this calibration. -/
structure NormProfileRecipe {X : Type*} (data : X → MomentData K ω ψ) where
  left : X → ℝ → ℝ → ℂ
  right : X → ℝ → ℝ → ℂ
  left_eq : ∀ ξ u, (data ξ).allowedRow u → ∀ t y,
    (data ξ).plainTest₁.profile u t y = left ξ t y
  right_eq : ∀ ξ u, (data ξ).allowedRow u → ∀ t y,
    (data ξ).plainTest₂.profile u t y = right ξ t y

namespace NormProfileRecipe

variable {X : Type*} {data : X → MomentData K ω ψ}
variable (W : NormProfileRecipe data)

def «at» (ξ : X) : NormProfileRecipe (fun _ : PUnit => data ξ) where
  left _ := W.left ξ
  right _ := W.right ξ
  left_eq _ := W.left_eq ξ
  right_eq _ := W.right_eq ξ

def clipped (a : RealParameters) (Z : ℝ) (hZ : 0 < Z) :
    NormProfileRecipe (fun ξ => clipPlainData (data ξ) a Z hZ) where
  left ξ t y := (Real.sqrt (plainClippingFactor Z a.n₁) : ℂ) *
    W.left ξ t (plainClippingFactor Z a.n₁ * y)
  right ξ t y := (Real.sqrt (plainClippingFactor Z a.n₂) : ℂ) *
    W.right ξ t (plainClippingFactor Z a.n₂ * y)
  left_eq ξ u hu t y := by
    change (Real.sqrt (plainClippingFactor Z a.n₁) : ℂ) *
      (data ξ).plainTest₁.profile u t (plainClippingFactor Z a.n₁ * y) = _
    rw [W.left_eq ξ u hu]
  right_eq ξ u hu t y := by
    change (Real.sqrt (plainClippingFactor Z a.n₂) : ℂ) *
      (data ξ).plainTest₂.profile u t (plainClippingFactor Z a.n₂ * y) = _
    rw [W.right_eq ξ u hu]

def normalized (B : X → ℝ) (hB : ∀ ξ, 0 < B ξ) :
    NormProfileRecipe (fun ξ => normalizedMomentProfiles (data ξ) (B ξ) (hB ξ)) where
  left ξ t y := (((B ξ)⁻¹ : ℝ) : ℂ) * W.left ξ t y
  right ξ t y := (((B ξ)⁻¹ : ℝ) : ℂ) * W.right ξ t y
  left_eq ξ u hu t y := by
    change (((B ξ)⁻¹ : ℝ) : ℂ) * (data ξ).plainTest₁.profile u t y = _
    rw [W.left_eq ξ u hu]
  right_eq ξ u hu t y := by
    change (((B ξ)⁻¹ : ℝ) : ℂ) * (data ξ).plainTest₂.profile u t y = _
    rw [W.right_eq ξ u hu]

def restricted (keep : ∀ ξ, Finset (Fin (data ξ).geometry.slotCount)) :
    NormProfileRecipe (fun ξ => (data ξ).restrictSlots (keep ξ)) where
  left := W.left
  right := W.right
  left_eq := W.left_eq
  right_eq := W.right_eq

def frozen (time : X → ℝ) :
    NormProfileRecipe (fun ξ => frozenMomentProfiles (data ξ) (time ξ)) where
  left ξ _ y := W.left ξ (time ξ) y
  right ξ _ y := W.right ξ (time ξ) y
  left_eq ξ u hu t y := by
    change (data ξ).plainTest₁.profile u (time ξ) y * profilePower 0 y = _
    rw [profilePower_zero, mul_one, W.left_eq ξ u hu]
  right_eq ξ u hu t y := by
    change (data ξ).plainTest₂.profile u (time ξ) y * profilePower 0 y = _
    rw [profilePower_zero, mul_one, W.right_eq ξ u hu]

def jointRows {A : SArithmeticData K}
    (support : HeckeGeneral.Analysis.NonzeroIdeal K → A.Exterior) (budget : ℝ) :
    NormProfileRecipe (fun ξ => jointRowBudgetData (data ξ) support budget) where
  left := W.left
  right := W.right
  left_eq ξ u hu := W.left_eq ξ u hu.1
  right_eq ξ u hu := W.right_eq ξ u hu.1

/-- The complete source uses these same functions at either independent
scale.  The functions do not need to be chosen again for centering. -/
theorem left_paired (ξ : X) (a : RealParameters) (Z : ℝ)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (hu : u ∈ pairedRows (data ξ) a Z)
    (t y : ℝ) : (data ξ).plainTest₁.profile u t y = W.left ξ t y :=
  W.left_eq ξ u ((((data ξ).rows_spec _ u).1 (Finset.mem_filter.mp hu).1).1) t y

theorem right_paired (ξ : X) (a : RealParameters) (Z : ℝ)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (hu : u ∈ pairedRows (data ξ) a Z)
    (t y : ℝ) : (data ξ).plainTest₂.profile u t y = W.right ξ t y :=
  W.right_eq ξ u ((((data ξ).rows_spec _ u).1 (Finset.mem_filter.mp hu).1).1) t y

end NormProfileRecipe

/-- A literal norm test, using one original finite-support test.  The
support specification is inherited exactly and no analytic condition
or finite-support conclusion is assumed. -/
def normIdealTest (W : IdealTest K) (reference : HeckeGeneral.Analysis.NonzeroIdeal K) :
    IdealTest K where
  profile _ := W.profile reference
  support _ := W.support reference
  support_spec _ := W.support_spec reference

/-- This constructor is useful for a raw source made from two fixed
norm tests, including the ordinary annular power-window tests. -/
def normProfileRecipe_ofTests {X : Type*} (data : X → MomentData K ω ψ)
    (left right : X → IdealTest K)
    (referenceLeft referenceRight : X → HeckeGeneral.Analysis.NonzeroIdeal K) :
    NormProfileRecipe (ω := ω) (ψ := ψ) (fun ξ => { data ξ with
      plainTest₁ := normIdealTest (left ξ) (referenceLeft ξ)
      plainTest₂ := normIdealTest (right ξ) (referenceRight ξ) }) where
  left ξ := (left ξ).profile (referenceLeft ξ)
  right ξ := (right ξ).profile (referenceRight ξ)
  left_eq _ _ _ _ _ := rfl
  right_eq _ _ _ _ _ := rfl

namespace ActualAllocatedSource.Calibration

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k : ℕ} {s : ActualAllocatedSource A V H k}
variable (D : s.Calibration (σ := σ) ω ψ)

def normProfiles_withJointRowBudget (W : NormProfileRecipe D.data)
    (M : ActualMovingMaskRecipe A D.data)
    (hsource : ∀ h ∈ s.rows,
      A.exteriorNorm (s.originalIdeal h) * A.exteriorNorm (M.support (s.row h).momentIdeal) ≤
        s.normFactor h * s.base ^ (D.parameters.m + D.parameters.q)) :
    NormProfileRecipe (D.withJointRowBudget M hsource).data :=
  W.jointRows M.support (s.base ^ (D.parameters.m + D.parameters.q))

end ActualAllocatedSource.Calibration

namespace ActualAllocatedSource.Calibration.NormalizedCapacityData.Child

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k : ℕ} {s : ActualAllocatedSource A V H k}
variable {D : s.Calibration (σ := σ) ω ψ} {G : D.NormalizedCapacityData}
variable (out : G.Child)

/-- Every transformation here is the one already present in this
chosen child.  In particular its fixed removed set is unchanged. -/
def normProfileRecipe (W : NormProfileRecipe D.data) : NormProfileRecipe out.frozenData :=
  (((W.clipped D.parameters s.base (zero_lt_one.trans s.base_gt_one)).normalized
      G.radius G.radius_pos).restricted
        (fun ξ => lengthSelection (G.normalizedData ξ) s.allocation.keep.card (D.count ξ)
          (Finset.univ \ out.removed))).frozen D.height

end ActualAllocatedSource.Calibration.NormalizedCapacityData.Child

namespace ActualNormalizedPairFamily

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {V Λ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : ℝ}
variable (family : ActualNormalizedPairFamily A σ V Λ ω ψ Z) (labels : Finset Λ)

/-- Original per-profile identities on the two raw calibrations.  No
admissibility or energy of a selected child is an input. -/
structure NormProfileInputs where
  left : ∀ b ∈ labels, NormProfileRecipe (family.leftCalibration b).data
  right : ∀ b ∈ labels, NormProfileRecipe (family.rightCalibration b).data

namespace NormProfileInputs

variable {family labels} (raw : family.NormProfileInputs labels)

def leftRecipe (b : family.active labels) : NormProfileRecipe (family.leftData labels b) :=
  (family.leftChild labels b).normProfileRecipe
    (raw.left b.val (Finset.mem_filter.mp b.property).1)

def rightRecipe (b : family.active labels) : NormProfileRecipe (family.rightData labels b) :=
  (family.rightChild labels b).normProfileRecipe
    (raw.right b.val (Finset.mem_filter.mp b.property).1)

end NormProfileInputs
end ActualNormalizedPairFamily

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.NormProfileRecipe.left_paired
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.NormalizedCapacityData.Child.normProfileRecipe
