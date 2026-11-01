import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondHybridSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondBranchPartition
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CenteredAllocatedChildren
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NestedHybridKernel

/-!
# The ordinary part of a true hybrid branch produces actual children

The source has already fixed its row label, extracted-occurrence keys,
second divisor, finite phase and two allocations.  The actual exceptional
predicate is now used to restrict both sides to the same complementary
rows.  Only there is the original whole-centered coefficient written as
its two individual rectangle terms.

The inputs below are single-column identities and the existing
single-ideal arithmetic/profile dictionaries.  The engine constructs
actual side frames, proves their relation to the ordinary integrand,
and invokes the genuine fixed-capacity/profile-normalization producer.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments WholeAllocation

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k l : ℕ}

/-- All columns and both actual allocations are retained.  The two
rectangle identities are required only at individual allocated columns,
after the genuine exceptional predicate has already been fixed. -/
structure HybridOrdinaryRectangles
    (R : ActualSecondCorrelationRows A σ H ι)
    (Ray : Type*) [CommGroup Ray] [Fintype Ray]
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (T₁ T₂ : Finset (Ideal (𝓞 K))) (T : Fin l → Finset (HeightOneSpectrum (𝓞 K)))
    (IA : AllocationColumn K k → A.Exterior) (IB : AllocationColumn K l → A.Exterior)
    (rayLeft : AllocationColumn K k → Ray) (rayRight : AllocationColumn K l → Ray)
    (wholeLeft : AllocationColumn K k → ℂ) (wholeRight : AllocationColumn K l → ℂ)
    (x : H → AllocationColumn K k → V) (y : H → AllocationColumn K l → V)
    (b : liveSecondAllocationBranches (Ray := Ray) S₁ S₂ S T₁ T₂ T IB)
    (exceptional : H → Prop) where
  leftTerms : Bool → AllocationColumn K k → ℂ
  rightTerms : Bool → AllocationColumn K l → ℂ
  left_difference : ∀ i ∈ b.val.leftColumns S₁ S₂ S,
    wholeLeft i = leftTerms false i - leftTerms true i
  right_difference : ∀ j ∈ b.val.rightColumns,
    wholeRight j = rightTerms false j - rightTerms true j
  leftFactors : ∀ r : Bool,
    SecondRectangularFactors (R.restrictRows (fun h => ¬exceptional h)) Ray .left
      S₁ S₂ S IA rayLeft (leftTerms r) x b.val.2.1
  rightFactors : ∀ r : Bool,
    SecondRectangularFactors (R.restrictRows (fun h => ¬exceptional h)) Ray .right
      T₁ T₂ T IB rayRight (rightTerms r) y b.val.2.1

namespace HybridOrdinaryRectangles

variable {R : ActualSecondCorrelationRows A σ H ι}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {S₁ S₂ : Finset (Ideal (𝓞 K))} {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable {T₁ T₂ : Finset (Ideal (𝓞 K))} {T : Fin l → Finset (HeightOneSpectrum (𝓞 K))}
variable {IA : AllocationColumn K k → A.Exterior} {IB : AllocationColumn K l → A.Exterior}
variable {rayLeft : AllocationColumn K k → Ray} {rayRight : AllocationColumn K l → Ray}
variable {wholeLeft : AllocationColumn K k → ℂ} {wholeRight : AllocationColumn K l → ℂ}
variable {x : H → AllocationColumn K k → V} {y : H → AllocationColumn K l → V}
variable {b : liveSecondAllocationBranches (Ray := Ray) S₁ S₂ S T₁ T₂ T IB}
variable {exceptional : H → Prop}
variable (B : HybridOrdinaryRectangles R Ray S₁ S₂ S T₁ T₂ T IA IB
  rayLeft rayRight wholeLeft wholeRight x y b exceptional)

def leftFrame (C : A.GeneralArithmeticContext σ η hS) (r : Bool) :
    SecondSideFrame (V := V) C (R.restrictRows (fun h => ¬exceptional h)) Ray .left k :=
  (B.leftFactors r).frame C b.val.1.val b.val.2.2.1.val
    (Finset.mem_filter.mp b.property).2.2.1

def rightFrame (C : A.GeneralArithmeticContext σ η hS) (r : Bool) :
    SecondSideFrame (V := V) C (R.restrictRows (fun h => ¬exceptional h)) Ray .right l :=
  (B.rightFactors r).frame C b.val.1.val b.val.2.2.2.val
    (Finset.mem_filter.mp b.property).2.2.2

/-- This is precisely the ordinary summand of the actual hybrid
integrand, including its original complete-correlation row weight. -/
def originalIntegrand (_B : HybridOrdinaryRectangles R Ray S₁ S₂ S T₁ T₂ T IA IB
    rayLeft rayRight wholeLeft wholeRight x y b exceptional) (ξ : V) : ℝ :=
  Real.sqrt (jointColumnEnergy (R.rows.filter (fun h => ¬exceptional h))
    (b.val.leftColumns S₁ S₂ S) (fun h => R.weight h * R.correlation h)
    (secondAllocatedLeftCoefficient (σ := σ) Ray IA R.frequency rayLeft b.val.2.1 wholeLeft) x ξ) *
  Real.sqrt (jointColumnEnergy (R.rows.filter (fun h => ¬exceptional h))
    b.val.rightColumns (fun h => R.weight h * R.correlation h)
    (secondAllocatedRightCoefficient (σ := σ) Ray IB R.frequency rayRight b.val.2.1 wholeRight) y ξ)

theorem left_energy_eq (C : A.GeneralArithmeticContext σ η hS) (r : Bool) (ξ : V) :
    (B.leftFrame C r).energy ξ =
      jointColumnEnergy (R.rows.filter (fun h => ¬exceptional h))
        (b.val.leftColumns S₁ S₂ S) (fun h => R.weight h * R.correlation h)
        (secondAllocatedLeftCoefficient (σ := σ) Ray IA R.frequency rayLeft b.val.2.1 (B.leftTerms r)) x ξ :=
  (B.leftFactors r).frame_energy C b.val.1.val b.val.2.2.1.val
    (Finset.mem_filter.mp b.property).2.2.1 ξ

theorem right_energy_eq (C : A.GeneralArithmeticContext σ η hS) (r : Bool) (ξ : V) :
    (B.rightFrame C r).energy ξ =
      jointColumnEnergy (R.rows.filter (fun h => ¬exceptional h))
        b.val.rightColumns (fun h => R.weight h * R.correlation h)
        (secondAllocatedRightCoefficient (σ := σ) Ray IB R.frequency rayRight b.val.2.1 (B.rightTerms r)) y ξ :=
  (B.rightFactors r).frame_energy C b.val.1.val b.val.2.2.2.val
    (Finset.mem_filter.mp b.property).2.2.2 ξ

/-- Finite weighted L2 Minkowski is used on the complementary rows only.
The exceptional whole subtraction never enters this four-term bound. -/
theorem ordinary_le_rectangles (C : A.GeneralArithmeticContext σ η hS) (ξ : V) :
    B.originalIntegrand ξ ≤
      Real.sqrt ((B.leftFrame C false).energy ξ) *
        Real.sqrt ((B.rightFrame C false).energy ξ) +
      Real.sqrt ((B.leftFrame C false).energy ξ) *
        Real.sqrt ((B.rightFrame C true).energy ξ) +
      Real.sqrt ((B.leftFrame C true).energy ξ) *
        Real.sqrt ((B.rightFrame C false).energy ξ) +
      Real.sqrt ((B.leftFrame C true).energy ξ) *
        Real.sqrt ((B.rightFrame C true).energy ξ) := by
  let rows := R.rows.filter (fun h => ¬exceptional h)
  let q : H → ℂ := fun h => R.weight h * R.correlation h
  let c₀ := secondAllocatedLeftCoefficient (σ := σ) Ray IA R.frequency rayLeft b.val.2.1 (B.leftTerms false)
  let c₁ := secondAllocatedLeftCoefficient (σ := σ) Ray IA R.frequency rayLeft b.val.2.1 (B.leftTerms true)
  let d₀ := secondAllocatedRightCoefficient (σ := σ) Ray IB R.frequency rayRight b.val.2.1 (B.rightTerms false)
  let d₁ := secondAllocatedRightCoefficient (σ := σ) Ray IB R.frequency rayRight b.val.2.1 (B.rightTerms true)
  have he {J : Type*} (columns : Finset J) (u v : H → J → ℂ)
      (point : H → J → V) (huv : ∀ h i, i ∈ columns → u h i = v h i) :
      jointColumnEnergy rows columns q u point ξ =
        jointColumnEnergy rows columns q v point ξ := by
    unfold jointColumnEnergy
    apply Finset.sum_congr rfl
    intro h _
    have hp : jointFourierColumn columns (u h) (point h) ξ =
        jointFourierColumn columns (v h) (point h) ξ := by
      unfold jointFourierColumn
      exact Finset.sum_congr rfl fun i hi => by rw [huv h i hi]
    rw [hp]
  have hlE := he (b.val.leftColumns S₁ S₂ S)
    (secondAllocatedLeftCoefficient (σ := σ) Ray IA R.frequency rayLeft b.val.2.1 wholeLeft)
    (fun h i => c₀ h i - c₁ h i) x (by
      intro h i hi
      simp only [secondAllocatedLeftCoefficient, B.left_difference i hi, sub_mul, c₀, c₁])
  have hrE := he b.val.rightColumns
    (secondAllocatedRightCoefficient (σ := σ) Ray IB R.frequency rayRight b.val.2.1 wholeRight)
    (fun h j => d₀ h j - d₁ h j) y (by
      intro h j hj
      simp only [secondAllocatedRightCoefficient, B.right_difference j hj,
        sub_mul, star_sub, d₀, d₁])
  have hl := sqrt_joint_energy_sub rows (b.val.leftColumns S₁ S₂ S) q c₀ c₁ x ξ
  have hr := sqrt_joint_energy_sub rows b.val.rightColumns q d₀ d₁ y ξ
  rw [← B.left_energy_eq C false ξ, ← B.left_energy_eq C true ξ] at hl
  rw [← B.right_energy_eq C false ξ, ← B.right_energy_eq C true ξ] at hr
  calc
    B.originalIntegrand ξ ≤
        (Real.sqrt ((B.leftFrame C false).energy ξ) +
          Real.sqrt ((B.leftFrame C true).energy ξ)) *
        (Real.sqrt ((B.rightFrame C false).energy ξ) +
          Real.sqrt ((B.rightFrame C true).energy ξ)) := by
      unfold originalIntegrand
      rw [hlE, hrE]
      exact mul_le_mul hl hr (Real.sqrt_nonneg _)
        (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = _ := by ring

/-- The actual frame comparisons and child production are a single
per-branch result.  Each child/deletion is fixed before ξ; all inputs
are the primitive per-term, capacity-ledger and raw profile windows
already required by the actual source calibration. -/
theorem produce
    (C : A.GeneralArithmeticContext σ η hS)
    {ω ψ : HeckeCharacter K} (P : ProfileNormalizationInput K ω ψ)
    (rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K))
    (heightDomain window : Set ℝ) (seminorms : Finset (ℕ × ℕ))
    (lc : ∀ r : Bool, SecondSideNormalization (B.leftFrame C r)
      ω ψ rowDomain heightDomain window seminorms)
    (rc : ∀ r : Bool, SecondSideNormalization (B.rightFrame C r)
      ω ψ rowDomain heightDomain window seminorms) :
    (∀ ξ, B.originalIntegrand ξ ≤
      Real.sqrt ((B.leftFrame C false).energy ξ) *
        Real.sqrt ((B.rightFrame C false).energy ξ) +
      Real.sqrt ((B.leftFrame C false).energy ξ) *
        Real.sqrt ((B.rightFrame C true).energy ξ) +
      Real.sqrt ((B.leftFrame C true).energy ξ) *
        Real.sqrt ((B.rightFrame C false).energy ξ) +
      Real.sqrt ((B.leftFrame C true).energy ξ) *
        Real.sqrt ((B.rightFrame C true).energy ξ)) ∧
    ∀ r s : Bool, SecondSideNormalization.Produced P (lc r) (rc s) :=
  ⟨B.ordinary_le_rectangles C, fun r s => SecondSideNormalization.produce P (lc r) (rc s)⟩

end HybridOrdinaryRectangles

section ActualNestedIntegrand

variable {U W : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
variable (R : ActualSecondCorrelationRows A σ H ι)
variable (Ray : Type*) [CommGroup Ray] [Fintype Ray]
variable (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
variable (T₁ T₂ : Finset (Ideal (𝓞 K))) (T : Fin l → Finset (HeightOneSpectrum (𝓞 K)))
variable (IA : AllocationColumn K k → A.Exterior) (IB : AllocationColumn K l → A.Exterior)
variable (rayLeft : AllocationColumn K k → Ray) (rayRight : AllocationColumn K l → Ray)
variable (c : AllocationColumn K k → ℂ) (f : AllocationColumn K l → ℂ)
variable (x₁ : H → AllocationColumn K k → U) (x₂ : H → AllocationColumn K k → W)
variable (y₁ : H → AllocationColumn K l → U) (y₂ : H → AllocationColumn K l → W)
variable (b : liveSecondAllocationBranches (Ray := Ray) S₁ S₂ S T₁ T₂ T IB)
variable (exceptional : H → Prop)

/-- This is the literal branch integrand obtained by the actual two
Fourier transforms.  Its ordinary part is exactly the producer input;
the first right Fourier coordinate is negated and its whole coefficient
is conjugated once. -/
theorem nested_hybrid_eq_exception_plus_ordinary
    (B : HybridOrdinaryRectangles R Ray S₁ S₂ S T₁ T₂ T IA IB rayLeft rayRight c f
      (fun h i => WithLp.toLp 2 (x₁ h i, x₂ h i))
      (fun h j => WithLp.toLp 2 (-y₁ h j, y₂ h j)) b exceptional)
    (z : U × W) :
    nestedJointHybridIntegrand R.rows (b.val.leftColumns S₁ S₂ S) b.val.rightColumns
      (fun h => R.weight h * R.correlation h)
      (secondAllocatedLeftCoefficient (σ := σ) Ray IA R.frequency rayLeft b.val.2.1 c)
      (fun h j => f j * (fixedRightPhase Ray b.val.2.1 (rayRight j) : ℂ) *
        σ (A.sexticResidue (IB j) (-R.frequency h)))
      x₁ x₂ y₁ y₂ exceptional z =
    jointColumnPairMagnitude (R.rows.filter exceptional)
      (b.val.leftColumns S₁ S₂ S) b.val.rightColumns
      (fun h => R.weight h * R.correlation h)
      (secondAllocatedLeftCoefficient (σ := σ) Ray IA R.frequency rayLeft b.val.2.1 c)
      (secondAllocatedRightCoefficient (σ := σ) Ray IB R.frequency rayRight b.val.2.1 f)
      (fun h i => WithLp.toLp 2 (x₁ h i, x₂ h i))
      (fun h j => WithLp.toLp 2 (-y₁ h j, y₂ h j)) (WithLp.toLp 2 z) +
        B.originalIntegrand (WithLp.toLp 2 z) := rfl

end ActualNestedIntegrand

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.HybridOrdinaryRectangles.ordinary_le_rectangles
#print axioms HeckeSkeleton.Moments.EngineStep.HybridOrdinaryRectangles.produce
#print axioms HeckeSkeleton.Moments.EngineStep.nested_hybrid_eq_exception_plus_ordinary

