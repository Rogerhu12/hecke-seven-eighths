import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.SideAnnulusSupport
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.IndependentChildSupport

/-!
# Original calibration support independently of the normalization box

A raw-support certificate depends only on each original calibration's
literal data, before any capacity normalization. It may therefore be
transported between two support certificates for the same original
functions. The actual family's radius and selected children stay fixed.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeSkeleton.Moments.EngineStep
open ActiveChildAnnulus

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}

section Family
variable {V Λ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : ℝ}

/-- Supports of the actual pre-clipping calibration data; this record
contains no normalization radius or selected child. -/
structure FamilyOriginalSupport
    (family : ActualNormalizedPairFamily A σ V Λ ω ψ Z) (lo hi : ℝ) : Prop where
  left : ∀ b ξ, ProfileSupport Set.univ Set.univ (Set.Icc lo hi)
    ((family.leftCalibration b).data ξ)
  right : ∀ b ξ, ProfileSupport Set.univ Set.univ (Set.Icc lo hi)
    ((family.rightCalibration b).data ξ)
  left_prime : ∀ b ξ i t,
    Function.support ((((family.leftCalibration b).data ξ).geometry.slots i).profile t) ⊆
      Set.Ioo (1 : ℝ) 2
  right_prime : ∀ b ξ i t,
    Function.support ((((family.rightCalibration b).data ξ).geometry.slots i).profile t) ⊆
      Set.Ioo (1 : ℝ) 2

namespace FamilyOriginalSupport
variable {family : ActualNormalizedPairFamily A σ V Λ ω ψ Z} {lo hi : ℝ}

theorem atBase (h : FamilyOriginalSupport family lo hi) (base : ℝ) (sameBase : Z = base) :
    FamilyOriginalSupport (family.atBase base sameBase) lo hi where
  left := h.left
  right := h.right
  left_prime := h.left_prime
  right_prime := h.right_prime

/-- Only equality of the literal pre-clipping data is used. Capacities
and their original radii may differ and are never equated. -/
theorem congrData {other : ActualNormalizedPairFamily A σ V Λ ω ψ Z}
    (h : FamilyOriginalSupport other lo hi)
    (left : ∀ b ξ, (family.leftCalibration b).data ξ = (other.leftCalibration b).data ξ)
    (right : ∀ b ξ, (family.rightCalibration b).data ξ = (other.rightCalibration b).data ξ) :
    FamilyOriginalSupport family lo hi where
  left b ξ := by rw [left b ξ]; exact h.left b ξ
  right b ξ := by rw [right b ξ]; exact h.right b ξ
  left_prime b ξ := by rw [left b ξ]; exact h.left_prime b ξ
  right_prime b ξ := by rw [right b ξ]; exact h.right_prime b ξ

variable {J : Type*} {Λs : J → Type*}
variable (families : ∀ j, ActualNormalizedPairFamily A σ V (Λs j) ω ψ Z)

theorem sigmaCombine (h : ∀ j, FamilyOriginalSupport (families j) lo hi) :
    FamilyOriginalSupport (ActualNormalizedPairFamily.sigmaCombine families) lo hi where
  left b ξ := (h b.1).left b.2 ξ
  right b ξ := (h b.1).right b.2 ξ
  left_prime b ξ := (h b.1).left_prime b.2 ξ
  right_prime b ξ := (h b.1).right_prime b.2 ξ

/-- The same active children inherit the smaller support even when
their numerical normalization was constructed in a larger window. -/
theorem strengthen (h : FamilyOriginalSupport family lo hi)
    (labels : Finset Λ) (hlo : 0 ≤ lo) (hhi : 1 ≤ hi)
    {orders : Finset (ℕ × ℕ)} {broad : Set ℝ}
    (windows : ∀ (b : family.active labels) (ξ : V),
      InFixedProfileWindow Set.univ Set.univ broad orders (family.leftData labels b ξ) ∧
        InFixedProfileWindow Set.univ Set.univ broad orders (family.rightData labels b ξ)) :
    FamilyAnnulusSupport family labels lo hi orders where
  window b ξ := by
    have hb := Finset.mem_filter.mp b.property
    exact ⟨unitWindow_withSupport (windows b ξ).1
        (active_child_support (family.leftChild labels b) hlo hhi (h.left b.val)
          (fun _ _ _ => Set.mem_univ _) (fun _ => Set.mem_univ _) hb.2.1 ξ),
      unitWindow_withSupport (windows b ξ).2
        (active_child_support (family.rightChild labels b) hlo hhi (h.right b.val)
          (fun _ _ _ => Set.mem_univ _) (fun _ => Set.mem_univ _) hb.2.2 ξ)⟩
  prime := actualNormalizedFamily_prime_support family labels
    (fun b _ => h.left_prime b) (fun b _ => h.right_prime b)

end FamilyOriginalSupport
end Family

section PassiveFamily

open CanonicalLiteralPassiveSource CanonicalLiteralPassiveFrames
open CanonicalLiteralPassiveNonzero CanonicalLiteralPassiveNormalizedFamily

variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS)
variable (R : ActualSecondCorrelationRows A σ H ι)
variable {k l : ℕ}
variable {leftAtoms : CanonicalLiteralRectangles.Atoms (K := K) k}
variable {rightAtoms : CanonicalLiteralRectangles.Atoms (K := K) l}
variable (leftProfiles : leftAtoms.ProfileData) (rightProfiles : rightAtoms.ProfileData)
variable (leftAllocation : ActualColumnAllocation K k)
variable (rightAllocation : ActualColumnAllocation K l)
variable (leftPaid : FixedChildCharacters K leftAllocation.keep.card)
variable (rightPaid : FixedChildCharacters K rightAllocation.keep.card)
variable (leftMask rightMask : NonzeroIdeal K)
variable (leftSign rightSign : ℝ)
variable {window : Set ℝ} {orders : Finset (ℕ × ℕ)}
variable (leftNormalization : ∀ b : SideLabel leftProfiles leftAllocation A leftMask,
  SecondSideNormalization
    (frame leftProfiles leftAllocation A leftPaid C R .left leftMask b.1.val leftSign b.2)
    ω ψ Set.univ Set.univ window orders)
variable (rightNormalization : ∀ b : SideLabel rightProfiles rightAllocation A rightMask,
  SecondSideNormalization
    (frame rightProfiles rightAllocation A rightPaid C R .right rightMask b.1.val rightSign b.2)
    ω ψ Set.univ Set.univ window orders)
variable (sameBase : rightAtoms.base = leftAtoms.base)

/-- The actual raw calibration supports are read before activity or
capacity choice, from the same two original side normalizations. -/
theorem passive_family_originalSupport {lo hi : ℝ}
    (left : ∀ b, SideAnnulusSupport (leftNormalization b) lo hi)
    (right : ∀ b, SideAnnulusSupport (rightNormalization b) lo hi) :
    FamilyOriginalSupport
      (CanonicalLiteralPassiveNormalizedFamily.family C R leftProfiles rightProfiles
        leftAllocation rightAllocation leftPaid rightPaid leftMask rightMask leftSign rightSign
        leftNormalization rightNormalization sameBase) lo hi where
  left b ξ := rawWindow_support ((left b.1).raw ξ)
  right b ξ := rawWindow_support ((right b.2).raw ξ)
  left_prime b := (left b.1).prime
  right_prime b := (right b.2).prime

end PassiveFamily
end HeckeSkeleton.Moments.EngineInduction

#print axioms HeckeSkeleton.Moments.EngineInduction.FamilyOriginalSupport.strengthen
#print axioms HeckeSkeleton.Moments.EngineInduction.passive_family_originalSupport
