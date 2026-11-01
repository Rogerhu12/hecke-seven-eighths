import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FiniteNormalizedProductFamily

/-!
# The same normalized children after restricting to active labels

Structural input dictionaries may be constructed only for labels whose
two actual sources are nonzero. Reapplying the active filter to that
finite set changes no label, capacity choice, frozen child or kernel.
The equivalence below preserves the original label value exactly.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

namespace ActualNormalizedPairFamily

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}
variable {V Λ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : ℝ}
variable (s : ActualNormalizedPairFamily A σ V Λ ω ψ Z) (labels : Finset Λ)

@[simp] theorem active_active : s.active (s.active labels) = s.active labels := by
  ext b
  constructor
  · intro hb
    exact (Finset.mem_filter.mp hb).1
  · intro hb
    exact Finset.mem_filter.mpr ⟨hb, (Finset.mem_filter.mp hb).2⟩

/-- Both directions preserve the original label value; only its
membership proof changes. -/
def activeActiveEquiv : s.active (s.active labels) ≃ s.active labels where
  toFun b := ⟨b.val, (Finset.mem_filter.mp b.property).1⟩
  invFun b := ⟨b.val, Finset.mem_filter.mpr ⟨b.property, (Finset.mem_filter.mp b.property).2⟩⟩
  left_inv := by
    rintro ⟨b, hb⟩
    rfl
  right_inv := by
    rintro ⟨b, hb⟩
    rfl

@[simp] theorem activeActiveEquiv_val (b : s.active (s.active labels)) :
    (s.activeActiveEquiv labels b).val = b.val := rfl

@[simp] theorem activeActiveEquiv_symm_val (b : s.active labels) :
    ((s.activeActiveEquiv labels).symm b).val = b.val := rfl

@[simp] theorem activeActive_leftChild (b : s.active (s.active labels)) :
    s.leftChild (s.active labels) b = s.leftChild labels (s.activeActiveEquiv labels b) := rfl

@[simp] theorem activeActive_rightChild (b : s.active (s.active labels)) :
    s.rightChild (s.active labels) b = s.rightChild labels (s.activeActiveEquiv labels b) := rfl

@[simp] theorem activeActive_leftData (b : s.active (s.active labels)) (ξ : V) :
    s.leftData (s.active labels) b ξ =
      s.leftData labels (s.activeActiveEquiv labels b) ξ := rfl

@[simp] theorem activeActive_rightData (b : s.active (s.active labels)) (ξ : V) :
    s.rightData (s.active labels) b ξ =
      s.rightData labels (s.activeActiveEquiv labels b) ξ := rfl

@[simp] theorem activeActive_leftParameters (b : s.active (s.active labels)) :
    s.leftParameters (s.active labels) b =
      s.leftParameters labels (s.activeActiveEquiv labels b) := rfl

@[simp] theorem activeActive_rightParameters (b : s.active (s.active labels)) :
    s.rightParameters (s.active labels) b =
      s.rightParameters labels (s.activeActiveEquiv labels b) := rfl

@[simp] theorem activeActive_childPair (b : s.active (s.active labels)) (ξ : V) :
    s.childPair (s.active labels) b ξ =
      s.childPair labels (s.activeActiveEquiv labels b) ξ := rfl

@[simp] theorem activeActive_envelope (b : s.active (s.active labels)) (ξ : V) :
    s.envelope (s.active labels) b ξ =
      s.envelope labels (s.activeActiveEquiv labels b) ξ := rfl

@[simp] theorem activeActive_weight (parentWidth : ℝ) (b : s.active (s.active labels)) :
    s.weight (s.active labels) parentWidth b =
      s.weight labels parentWidth (s.activeActiveEquiv labels b) := rfl

/-- A theorem on the active input labels sums over exactly the original
active carrier, including when that carrier is empty. -/
theorem sum_active_active {M : Type*} [AddCommMonoid M]
    (f : s.active (s.active labels) → M) :
    (∑ b, f b) = ∑ b : s.active labels, f ((s.activeActiveEquiv labels).symm b) :=
  Fintype.sum_equiv (s.activeActiveEquiv labels) _ _
    (fun _ => by simp only [Equiv.symm_apply_apply])

section Kernel

variable [MeasurableSpace V]

@[simp] theorem activeActive_kernel (μ : Λ → Measure V) (parentWidth : ℝ)
    (b : s.active (s.active labels)) :
    s.kernel (s.active labels) μ parentWidth b =
      s.kernel labels μ parentWidth (s.activeActiveEquiv labels b) := rfl

end Kernel
end ActualNormalizedPairFamily
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.active_active
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.activeActiveEquiv
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.activeActive_leftChild
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.activeActive_rightChild
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.sum_active_active
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.activeActive_kernel
