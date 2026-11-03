import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalSameCarrierMass

/-!
# Exchanging the two actual second common columns

The first common label and first divisor remain fixed. The second
common ideal pair exchanges its two entries, retaining its original
prime subset. The independent second divisor is unchanged, while its
two full occurrence allocations exchange places. This gives a literal
equivalence of the finite arithmetic carriers and preserves both their
harmonic weight and their exceptional divisor-dyad weight.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep.CommonSupportMass

open NumberField UniqueFactorizationMonoid
open HeckePort.IdealMobiusDivisorSum HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

def swapSecondLabel (w : Label K) : Label K := ((w.1.2, w.1.1), w.2)

@[simp] theorem swapSecondLabel_involutive (w : Label K) :
    swapSecondLabel (swapSecondLabel w) = w := rfl

theorem swapSecondLabel_injective : Function.Injective (swapSecondLabel (K := K)) := by
  intro u v h
  exact (congrArg swapSecondLabel h)

theorem commonRadical_comm (I J : Ideal (𝓞 K)) :
    commonRadical I J = commonRadical J I := by
  unfold commonRadical
  rw [Finset.inter_comm]

theorem valid_swapSecondLabel {S : Ideal (𝓞 K)} {w : Label K} (h : Valid S w) :
    Valid S (swapSecondLabel w) := by
  rcases h with ⟨hL, hR, hs, hSL, hSR, hp⟩
  refine ⟨hR, hL, hs.symm, hSR, hSL, ?_⟩
  simpa only [swapSecondLabel, commonRadical_comm w.1.2 w.1.1] using hp

namespace TwoDivisorCommonBranch

variable (b : TwoDivisorCommonBranch (K := K))

/-- Exchange only the second common pair and its two occurrence
families. Both actual divisor variables retain their literal values. -/
def swapSecond : TwoDivisorCommonBranch (K := K) where
  first := b.first
  firstDivisors := b.firstDivisors
  second v S := (b.second v S).image swapSecondLabel
  secondDivisors v S w := b.secondDivisors v S (swapSecondLabel w)
  leftOccurrences v S w := b.rightOccurrences v S (swapSecondLabel w)
  rightOccurrences v S w := b.leftOccurrences v S (swapSecondLabel w)

theorem mem_swapSecond_second (v : Label K) (S : Ideal (𝓞 K)) (w : Label K) :
    w ∈ b.swapSecond.second v S ↔ swapSecondLabel w ∈ b.second v S := by
  constructor
  · intro hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    exact hu
  · intro hw
    exact Finset.mem_image.mpr ⟨swapSecondLabel w, hw, rfl⟩

/-- The true full index, including both allocation coordinates. -/
def swapSecondIndex (j : b.Index) : b.swapSecond.Index :=
  ⟨j.1, j.2.1,
    ⟨swapSecondLabel j.2.2.1.val, Finset.mem_image_of_mem _ j.2.2.1.property⟩,
    j.2.2.2.1, j.2.2.2.2.2, j.2.2.2.2.1⟩

def unswapSecondIndex (j : b.swapSecond.Index) : b.Index :=
  ⟨j.1, j.2.1,
    ⟨swapSecondLabel j.2.2.1.val,
      (b.mem_swapSecond_second j.1.val j.2.1.val j.2.2.1.val).mp j.2.2.1.property⟩,
    j.2.2.2.1, j.2.2.2.2.2, j.2.2.2.2.1⟩

@[simp] theorem unswapSecondIndex_swapSecondIndex (j : b.Index) :
    b.unswapSecondIndex (b.swapSecondIndex j) = j := by
  rcases j with ⟨v, S, w, L, α, β⟩
  rfl

@[simp] theorem swapSecondIndex_unswapSecondIndex (j : b.swapSecond.Index) :
    b.swapSecondIndex (b.unswapSecondIndex j) = j := by
  rcases j with ⟨v, S, w, L, α, β⟩
  rfl

def swapSecondIndexEquiv : b.Index ≃ b.swapSecond.Index where
  toFun := b.swapSecondIndex
  invFun := b.unswapSecondIndex
  left_inv := b.unswapSecondIndex_swapSecondIndex
  right_inv := b.swapSecondIndex_unswapSecondIndex

@[simp] theorem swapSecondIndex_first (j : b.Index) :
    (b.swapSecondIndex j).1.val = j.1.val := rfl

@[simp] theorem swapSecondIndex_firstDivisor (j : b.Index) :
    (b.swapSecondIndex j).2.1.val = j.2.1.val := rfl

@[simp] theorem swapSecondIndex_secondLeft (j : b.Index) :
    (b.swapSecondIndex j).2.2.1.val.1.1 = j.2.2.1.val.1.2 := rfl

@[simp] theorem swapSecondIndex_secondRight (j : b.Index) :
    (b.swapSecondIndex j).2.2.1.val.1.2 = j.2.2.1.val.1.1 := rfl

@[simp] theorem swapSecondIndex_secondSubset (j : b.Index) :
    (b.swapSecondIndex j).2.2.1.val.2 = j.2.2.1.val.2 := rfl

@[simp] theorem swapSecondIndex_secondDivisor (j : b.Index) :
    (b.swapSecondIndex j).2.2.2.1.val = j.2.2.2.1.val := rfl

@[simp] theorem swapSecondIndex_leftAllocation (j : b.Index) :
    HEq (b.swapSecondIndex j).2.2.2.2.1.val j.2.2.2.2.2.val := HEq.rfl

@[simp] theorem swapSecondIndex_rightAllocation (j : b.Index) :
    HEq (b.swapSecondIndex j).2.2.2.2.2.val j.2.2.2.2.1.val := HEq.rfl

/-- Symmetry of the actual second radical is the entire scalar
calculation. Neither divisor nor its allocations are removed. -/
@[simp] theorem indexWeight_swapSecondIndex (j : b.Index) :
    b.swapSecond.indexWeight (b.swapSecondIndex j) = b.indexWeight j := by
  dsimp only [indexWeight, swapSecondIndex, swapSecondLabel]
  exact congrArg (fun I : Ideal (𝓞 K) =>
    (1 / (Ideal.absNorm (commonRadical j.1.val.1.1 j.1.val.1.2) : ℝ)) *
      ‖(moebius j.2.1.val : ℂ)‖ * (1 / (Ideal.absNorm I : ℝ)) *
        ‖(moebius j.2.2.2.1.val : ℂ)‖ / (Ideal.absNorm j.2.2.2.1.val : ℝ))
    (commonRadical_comm j.2.2.1.val.1.2 j.2.2.1.val.1.1)

@[simp] theorem exceptionalDyadWeight_swapSecondIndex (Z lower : ℝ) (j : b.Index) :
    b.swapSecond.exceptionalDyadWeight Z lower (b.swapSecondIndex j) =
      b.exceptionalDyadWeight Z lower j := by
  dsimp only [exceptionalDyadWeight, swapSecondIndex, swapSecondLabel]
  exact congrArg (fun I : Ideal (𝓞 K) =>
    (1 / (Ideal.absNorm (commonRadical j.1.val.1.1 j.1.val.1.2) : ℝ)) *
      ‖(moebius j.2.1.val : ℂ)‖ * (1 / (Ideal.absNorm I : ℝ)) *
        ‖(moebius j.2.2.2.1.val : ℂ)‖ * Z ^ (-lower))
    (commonRadical_comm j.2.2.1.val.1.2 j.2.2.1.val.1.1)

theorem swapSecond_mass : b.swapSecond.mass = b.mass := by
  calc
    _ = ∑ j : b.swapSecond.Index, b.swapSecond.indexWeight j :=
      b.swapSecond.sum_indexWeight.symm
    _ = ∑ j : b.Index, b.indexWeight j :=
      (Fintype.sum_equiv b.swapSecondIndexEquiv b.indexWeight b.swapSecond.indexWeight
        (fun j => (b.indexWeight_swapSecondIndex j).symm)).symm
    _ = _ := b.sum_indexWeight

namespace Admissible

variable {b} {cap : ℕ} {B Z : ℝ} {oldMask : Ideal (𝓞 K)}

/-- Every original arithmetic condition survives the coordinate
exchange, with the same norm box and the same occurrence cap. -/
def swapSecond (h : b.Admissible cap B Z oldMask) :
    b.swapSecond.Admissible cap B Z oldMask where
  first_valid := h.first_valid
  first_norm := h.first_norm
  first_divisor_valid := h.first_divisor_valid
  first_divisor_norm := h.first_divisor_norm
  second_valid v hv S hS w hw := by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    exact valid_swapSecondLabel (h.second_valid v hv S hS u hu)
  second_norm v hv S hS w hw := by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    exact (h.second_norm v hv S hS u hu).symm
  second_divisor_ne_zero v hv S hS w hw L hL := by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    exact h.second_divisor_ne_zero v hv S hS u hu L hL
  second_divisor_norm v hv S hS w hw L hL := by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    exact h.second_divisor_norm v hv S hS u hu L hL
  occurrences v hv S hS w hw L hL := by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    exact (h.occurrences v hv S hS u hu L hL).symm

end Admissible
end TwoDivisorCommonBranch
end HeckeSkeleton.Moments.EngineStep.CommonSupportMass

#print axioms HeckeSkeleton.Moments.EngineStep.CommonSupportMass.TwoDivisorCommonBranch.swapSecondIndexEquiv
#print axioms HeckeSkeleton.Moments.EngineStep.CommonSupportMass.TwoDivisorCommonBranch.exceptionalDyadWeight_swapSecondIndex
#print axioms HeckeSkeleton.Moments.EngineStep.CommonSupportMass.TwoDivisorCommonBranch.swapSecond_mass
#print axioms HeckeSkeleton.Moments.EngineStep.CommonSupportMass.TwoDivisorCommonBranch.Admissible.swapSecond
