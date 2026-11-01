import HeckeSkeleton.Moments.MOM_ENGINE_INTEGRATION.LiteralCalibrationSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveNormalizedFamily
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedFamilyBase
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DependentNormalizedGeometry

/-!
# Literal side support through the actual normalized family

The support record refers to the original calibration inside an existing
side normalization. The selected capacity child, radius, and data are
therefore fixed before these stronger support proofs are consumed.
The family record refers to the same active carrier and public frozen
children, and transports through the owner's exact base and sigma maps.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain
open DedekindZetaZeroFree (SArithmeticData RayClassCharacter)
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeSkeleton.Moments.EngineStep

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}

section Side

variable {H ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {side : SecondColumnSide} {k : ℕ}
variable {f : SecondSideFrame (V := V) C R Ray side k}
variable {window : Set ℝ} {orders : Finset (ℕ × ℕ)}

/-- Original, unnormalized profile windows belonging to this literal
side, including its strict prime support. -/
structure SideAnnulusSupport
    (N : SecondSideNormalization f ω ψ Set.univ Set.univ window orders)
    (lo hi : ℝ) : Prop where
  original : ∃ budget : V → ℝ,
    Nonempty (∀ ξ, RawProfileWindow Set.univ Set.univ (Set.Icc lo hi) orders
      (N.calibration.data ξ) (budget ξ))
  prime : ∀ ξ i t,
    Function.support (((N.calibration.data ξ).geometry.slots i).profile t) ⊆
      Set.Ioo (1 : ℝ) 2

namespace SideAnnulusSupport

variable {N : SecondSideNormalization f ω ψ Set.univ Set.univ window orders}
variable {lo hi : ℝ} (h : SideAnnulusSupport N lo hi)

/-- A support witness chooses only representatives for the already
fixed data. It cannot change any capacity choice or normalization. -/
def rawBudget : V → ℝ := Classical.choose h.original

def raw (ξ : V) : RawProfileWindow Set.univ Set.univ (Set.Icc lo hi) orders
    (N.calibration.data ξ) (h.rawBudget ξ) :=
  Classical.choice (Classical.choose_spec h.original) ξ

include h in
theorem child_window (hlo : 0 ≤ lo) (hhi : 1 ≤ hi)
    (out : N.normalizedCapacityData.Child)
    (hactive : ¬ ∀ ξ, f.source.energy (σ := σ) ξ = 0) (ξ : V) :
    InFixedProfileWindow Set.univ Set.univ (Set.Icc (lo / hi) hi) orders
      (out.frozenData ξ) :=
  (ActiveChildAnnulus.active_child_windows out hlo hhi h.raw N.profile
    (fun _ _ _ => Set.mem_univ _) (fun _ => Set.mem_univ _) hactive ξ).2

include h in
theorem child_prime (out : N.normalizedCapacityData.Child) :
    ∀ ξ i t, Function.support (((out.frozenData ξ).geometry.slots i).profile t) ⊆
      Set.Ioo (1 : ℝ) 2 :=
  ActiveChildAnnulus.frozen_child_prime_support out h.prime

end SideAnnulusSupport
end Side

section Family

variable {V Λ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : ℝ}

/-- Positive annuli and strict prime support for the public frozen
children of this exact active family. -/
structure FamilyAnnulusSupport
    (family : ActualNormalizedPairFamily A σ V Λ ω ψ Z) (labels : Finset Λ)
    (lo hi : ℝ) (orders : Finset (ℕ × ℕ)) : Prop where
  window : ∀ (b : family.active labels) (ξ : V),
    InFixedProfileWindow Set.univ Set.univ (Set.Icc (lo / hi) hi) orders
        (family.leftData labels b ξ) ∧
      InFixedProfileWindow Set.univ Set.univ (Set.Icc (lo / hi) hi) orders
        (family.rightData labels b ξ)
  prime : ∀ (b : family.active labels) (ξ : V),
    (∀ i t, Function.support (((family.leftData labels b ξ).geometry.slots i).profile t) ⊆
        Set.Ioo (1 : ℝ) 2) ∧
      (∀ i t, Function.support (((family.rightData labels b ξ).geometry.slots i).profile t) ⊆
        Set.Ioo (1 : ℝ) 2)

namespace FamilyAnnulusSupport

variable {family : ActualNormalizedPairFamily A σ V Λ ω ψ Z}
variable {labels : Finset Λ} {lo hi : ℝ} {orders : Finset (ℕ × ℕ)}

theorem atBase (h : FamilyAnnulusSupport family labels lo hi orders)
    (base : ℝ) (sameBase : Z = base) :
    FamilyAnnulusSupport (family.atBase base sameBase) labels lo hi orders where
  window := h.window
  prime := h.prime

variable {J : Type*} {Λs : J → Type*}
variable (families : ∀ j, ActualNormalizedPairFamily A σ V (Λs j) ω ψ Z)
variable (outer : Finset J) (inner : ∀ j, Finset (Λs j))

theorem sigmaCombine
    (h : ∀ j ∈ outer, FamilyAnnulusSupport (families j) (inner j) lo hi orders) :
    FamilyAnnulusSupport (ActualNormalizedPairFamily.sigmaCombine families)
      (outer.sigma inner) lo hi orders where
  window b ξ := (h b.val.1
    (ActualNormalizedPairFamily.sigmaActiveOuter families outer inner b).property).window
      (ActualNormalizedPairFamily.sigmaActiveInner families outer inner b) ξ
  prime b ξ := (h b.val.1
    (ActualNormalizedPairFamily.sigmaActiveOuter families outer inner b).property).prime
      (ActualNormalizedPairFamily.sigmaActiveInner families outer inner b) ξ

end FamilyAnnulusSupport
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

/-- The actual passive family uses exactly the two original
normalizations stored at the selected source labels. -/
theorem passive_family_annulusSupport
    {lo hi : ℝ} (hlo : 0 ≤ lo) (hhi : 1 ≤ hi)
    (left : ∀ b, SideAnnulusSupport (leftNormalization b) lo hi)
    (right : ∀ b, SideAnnulusSupport (rightNormalization b) lo hi) :
    FamilyAnnulusSupport
      (CanonicalLiteralPassiveNormalizedFamily.family C R leftProfiles rightProfiles
        leftAllocation rightAllocation leftPaid rightPaid leftMask rightMask leftSign rightSign
        leftNormalization rightNormalization sameBase) Finset.univ lo hi orders := by
  let family := CanonicalLiteralPassiveNormalizedFamily.family C R leftProfiles rightProfiles
    leftAllocation rightAllocation leftPaid rightPaid leftMask rightMask leftSign rightSign
    leftNormalization rightNormalization sameBase
  constructor
  · intro b ξ
    have hb := Finset.mem_filter.mp b.property
    exact ⟨(left b.val.1).child_window hlo hhi
        (family.leftChild Finset.univ b) hb.2.1 ξ,
      (right b.val.2).child_window hlo hhi
        (family.rightChild Finset.univ b) hb.2.2 ξ⟩
  · intro b ξ
    exact ⟨(left b.val.1).child_prime (family.leftChild Finset.univ b) ξ,
      (right b.val.2).child_prime (family.rightChild Finset.univ b) ξ⟩

end PassiveFamily
end HeckeSkeleton.Moments.EngineInduction

#print axioms HeckeSkeleton.Moments.EngineInduction.passive_family_annulusSupport
#print axioms HeckeSkeleton.Moments.EngineInduction.FamilyAnnulusSupport.sigmaCombine
