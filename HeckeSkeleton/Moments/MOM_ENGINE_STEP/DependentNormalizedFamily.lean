import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FiniteNormalizedProductFamily

/-!
# Dependent finite families of the same normalized children

Each original outer label may have its own type of passive allocation
labels. The sigma family reads the source, calibration, capacity and
normalizer from that exact component. Its active carrier is the sigma
of the original component active carriers.

The component child and the sigma-family child are definitionally the
same choice from the same capacity theorem: the two nonzero witnesses
differ only as proofs. The data, arithmetic weight and kernel identities
below therefore preserve the already selected children.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

namespace ActualNormalizedPairFamily

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}
variable {V J : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Λ : J → Type*} {Z : ℝ}
variable (families : ∀ j, ActualNormalizedPairFamily A σ V (Λ j) ω ψ Z)

/-- The dependent label is the original outer label together with
one of its own original inner labels. -/
def sigmaCombine : ActualNormalizedPairFamily A σ V (Sigma Λ) ω ψ Z where
  LeftRow b := (families b.1).LeftRow b.2
  RightRow b := (families b.1).RightRow b.2
  leftSlots b := (families b.1).leftSlots b.2
  rightSlots b := (families b.1).rightSlots b.2
  leftSource b := (families b.1).leftSource b.2
  rightSource b := (families b.1).rightSource b.2
  leftCalibration b := (families b.1).leftCalibration b.2
  rightCalibration b := (families b.1).rightCalibration b.2
  leftCapacity b := (families b.1).leftCapacity b.2
  rightCapacity b := (families b.1).rightCapacity b.2
  left_base b := (families b.1).left_base b.2
  right_base b := (families b.1).right_base b.2
  leftNormalizer b := (families b.1).leftNormalizer b.2
  rightNormalizer b := (families b.1).rightNormalizer b.2

@[simp] theorem sigmaCombine_leftCalibration (b : Sigma Λ) :
    (sigmaCombine families).leftCalibration b = (families b.1).leftCalibration b.2 := rfl

@[simp] theorem sigmaCombine_rightCalibration (b : Sigma Λ) :
    (sigmaCombine families).rightCalibration b = (families b.1).rightCalibration b.2 := rfl

@[simp] theorem sigmaCombine_leftCapacity (b : Sigma Λ) :
    (sigmaCombine families).leftCapacity b = (families b.1).leftCapacity b.2 := rfl

@[simp] theorem sigmaCombine_rightCapacity (b : Sigma Λ) :
    (sigmaCombine families).rightCapacity b = (families b.1).rightCapacity b.2 := rfl

@[simp] theorem sigmaCombine_sourcePair (parentWidth : ℝ) (b : Sigma Λ) (ξ : V) :
    (sigmaCombine families).sourcePair parentWidth b ξ =
      (families b.1).sourcePair parentWidth b.2 ξ := rfl

variable (outer : Finset J) (labels : ∀ j, Finset (Λ j))

@[simp] theorem mem_sigmaCombine_active (b : Sigma Λ) :
    b ∈ (sigmaCombine families).active (outer.sigma labels) ↔
      b.1 ∈ outer ∧ b.2 ∈ (families b.1).active (labels b.1) := by
  simp only [active, Finset.mem_filter, Finset.mem_sigma]
  simp only [sigmaCombine, and_assoc]

/-- Activity is tested on each original source, after its actual
inner labels have been constructed. -/
theorem sigmaCombine_active :
    (sigmaCombine families).active (outer.sigma labels) =
      outer.sigma (fun j => (families j).active (labels j)) := by
  ext b
  simp only [mem_sigmaCombine_active, Finset.mem_sigma]

def sigmaActiveOuter
    (b : (sigmaCombine families).active (outer.sigma labels)) : outer :=
  ⟨b.val.1, ((mem_sigmaCombine_active families outer labels b.val).mp b.property).1⟩

def sigmaActiveInner
    (b : (sigmaCombine families).active (outer.sigma labels)) :
    (families b.val.1).active (labels b.val.1) :=
  ⟨b.val.2, ((mem_sigmaCombine_active families outer labels b.val).mp b.property).2⟩

/-- This reindexing contains exactly the same outer and inner values. -/
def sigmaActiveEquiv :
    (sigmaCombine families).active (outer.sigma labels) ≃
      Σ j : outer, (families j.val).active (labels j.val) where
  toFun b := ⟨sigmaActiveOuter families outer labels b, sigmaActiveInner families outer labels b⟩
  invFun b := ⟨⟨b.1.val, b.2.val⟩,
    (mem_sigmaCombine_active families outer labels _).mpr ⟨b.1.property, b.2.property⟩⟩
  left_inv := by
    rintro ⟨⟨j, b⟩, hb⟩
    rfl
  right_inv := by
    rintro ⟨⟨j, hj⟩, ⟨b, hb⟩⟩
    rfl

@[simp] theorem sigmaActiveEquiv_outer
    (b : (sigmaCombine families).active (outer.sigma labels)) :
    ((sigmaActiveEquiv families outer labels b).1).val = b.val.1 := rfl

@[simp] theorem sigmaActiveEquiv_inner
    (b : (sigmaCombine families).active (outer.sigma labels)) :
    ((sigmaActiveEquiv families outer labels b).2).val = b.val.2 := rfl

@[simp] theorem sigmaCombine_leftChild
    (b : (sigmaCombine families).active (outer.sigma labels)) :
    (sigmaCombine families).leftChild (outer.sigma labels) b =
      (families b.val.1).leftChild (labels b.val.1)
        (sigmaActiveInner families outer labels b) := rfl

@[simp] theorem sigmaCombine_rightChild
    (b : (sigmaCombine families).active (outer.sigma labels)) :
    (sigmaCombine families).rightChild (outer.sigma labels) b =
      (families b.val.1).rightChild (labels b.val.1)
        (sigmaActiveInner families outer labels b) := rfl

@[simp] theorem sigmaCombine_leftData
    (b : (sigmaCombine families).active (outer.sigma labels)) (ξ : V) :
    (sigmaCombine families).leftData (outer.sigma labels) b ξ =
      (families b.val.1).leftData (labels b.val.1)
        (sigmaActiveInner families outer labels b) ξ := rfl

@[simp] theorem sigmaCombine_rightData
    (b : (sigmaCombine families).active (outer.sigma labels)) (ξ : V) :
    (sigmaCombine families).rightData (outer.sigma labels) b ξ =
      (families b.val.1).rightData (labels b.val.1)
        (sigmaActiveInner families outer labels b) ξ := rfl

@[simp] theorem sigmaCombine_leftParameters
    (b : (sigmaCombine families).active (outer.sigma labels)) :
    (sigmaCombine families).leftParameters (outer.sigma labels) b =
      (families b.val.1).leftParameters (labels b.val.1)
        (sigmaActiveInner families outer labels b) := rfl

@[simp] theorem sigmaCombine_rightParameters
    (b : (sigmaCombine families).active (outer.sigma labels)) :
    (sigmaCombine families).rightParameters (outer.sigma labels) b =
      (families b.val.1).rightParameters (labels b.val.1)
        (sigmaActiveInner families outer labels b) := rfl

@[simp] theorem sigmaCombine_childPair
    (b : (sigmaCombine families).active (outer.sigma labels)) (ξ : V) :
    (sigmaCombine families).childPair (outer.sigma labels) b ξ =
      (families b.val.1).childPair (labels b.val.1)
        (sigmaActiveInner families outer labels b) ξ := rfl

@[simp] theorem sigmaCombine_envelope
    (b : (sigmaCombine families).active (outer.sigma labels)) (ξ : V) :
    (sigmaCombine families).envelope (outer.sigma labels) b ξ =
      (families b.val.1).envelope (labels b.val.1)
        (sigmaActiveInner families outer labels b) ξ := rfl

@[simp] theorem sigmaCombine_weight (parentWidth : ℝ)
    (b : (sigmaCombine families).active (outer.sigma labels)) :
    (sigmaCombine families).weight (outer.sigma labels) parentWidth b =
      (families b.val.1).weight (labels b.val.1) parentWidth
        (sigmaActiveInner families outer labels b) := rfl

/-- A finite sum over the combined active carrier is exactly the
dependent sum over the original component active carriers. -/
theorem sum_sigmaCombine_active {M : Type*} [AddCommMonoid M]
    (f : (sigmaCombine families).active (outer.sigma labels) → M) :
    (∑ b, f b) =
      ∑ j : outer, ∑ b : (families j.val).active (labels j.val),
        f ((sigmaActiveEquiv families outer labels).symm ⟨j, b⟩) := by
  calc
    _ = ∑ b : (Σ j : outer, (families j.val).active (labels j.val)),
        f ((sigmaActiveEquiv families outer labels).symm b) :=
      Fintype.sum_equiv (sigmaActiveEquiv families outer labels) _ _
        (fun _ => by simp only [Equiv.symm_apply_apply])
    _ = _ := by rw [Fintype.sum_sigma]

theorem sigmaCombine_source_sum (parentWidth : ℝ) (ξ : V) :
    (∑ b ∈ outer.sigma labels, (sigmaCombine families).sourcePair parentWidth b ξ) =
      ∑ j ∈ outer, ∑ b ∈ labels j, (families j).sourcePair parentWidth b ξ := by
  rw [Finset.sum_sigma]
  rfl

section Kernel

variable [MeasurableSpace V]

@[simp] theorem sigmaCombine_kernel (μ : ∀ j, Λ j → Measure V) (parentWidth : ℝ)
    (b : (sigmaCombine families).active (outer.sigma labels)) :
    (sigmaCombine families).kernel (outer.sigma labels)
        (fun p => μ p.1 p.2) parentWidth b =
      (families b.val.1).kernel (labels b.val.1) (μ b.val.1) parentWidth
        (sigmaActiveInner families outer labels b) := rfl

end Kernel
end ActualNormalizedPairFamily
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.sigmaCombine
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.sigmaActiveEquiv
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.sigmaCombine_leftChild
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.sigmaCombine_rightChild
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.sum_sigmaCombine_active
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.sigmaCombine_kernel
