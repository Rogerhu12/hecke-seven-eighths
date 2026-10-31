import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualGaussFiniteLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocationPadding

/-!
# The actual allocation labels have an injective fixed-cap fingerprint

The occurrence count varies with the genuine source-cover key.  Once
that key is fixed, padding preserves every original allocation.  The
actual phase character is a character of `PUnit × PUnit`, so omitting
it from this fingerprint loses no information.  Consequently a fibre
over the padded allocation is counted by its actual source-class keys;
no allocation cardinality or abstract multiplicity is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckePort.Moments HeckePort.Moments.MobiusRegroup WholeAllocation

variable {K : Type} [Field K] [NumberField K]

/-- The divisor is the literal second Möbius divisor.  Both complete
allocation functions have the same earlier occurrence cap. -/
abbrev OriginalAllocationFingerprint (K : Type) [Field K] [NumberField K]
    (cap : ℕ) :=
  Σ D : Ideal (𝓞 K), AllocationMass.idealAllocations D (cap + 2) ×
    AllocationMass.idealAllocations D (cap + 2)

section OneClass

variable {k l cap : ℕ} {γ : Type*} [Fintype γ] [Subsingleton γ]
variable {T₁ T₂ : Finset (Ideal (𝓞 K))}
variable {T : Fin l → Finset (HeightOneSpectrum (𝓞 K))}
variable {rightIdeals : AllocationColumn K l → Ideal (𝓞 K)}

def hybridAllocationFingerprint (hk : k ≤ cap) (hl : l ≤ cap)
    (b : HybridAllocationLabel T₁ T₂ T rightIdeals k γ) :
    OriginalAllocationFingerprint K cap :=
  ⟨b.1.val,
    AllocationMass.idealPad b.1.val (Nat.add_le_add_right hk 2) b.2.2.1,
    AllocationMass.idealPad b.1.val (Nat.add_le_add_right hl 2) b.2.2.2⟩

/-- This is an injection of the actual finite divisor/phase/allocation
carrier, including empty prime supports and the two plain occurrences. -/
theorem hybridAllocationFingerprint_injective (hk : k ≤ cap) (hl : l ≤ cap) :
    Function.Injective
      (hybridAllocationFingerprint (T₁ := T₁) (T₂ := T₂) (T := T)
        (rightIdeals := rightIdeals) (γ := γ) hk hl) := by
  rintro ⟨D, χ, a, e⟩ ⟨L, ψ, b, f⟩ h
  have hDL : D = L := Subtype.ext (congrArg Sigma.fst h)
  cases hDL
  have hp :
      (AllocationMass.idealPad D.val (Nat.add_le_add_right hk 2) a,
        AllocationMass.idealPad D.val (Nat.add_le_add_right hl 2) e) =
      (AllocationMass.idealPad D.val (Nat.add_le_add_right hk 2) b,
        AllocationMass.idealPad D.val (Nat.add_le_add_right hl 2) f) :=
    eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have ha := AllocationMass.idealPad_injective D.val
    (Nat.add_le_add_right hk 2) (congrArg Prod.fst hp)
  have he := AllocationMass.idealPad_injective D.val
    (Nat.add_le_add_right hl 2) (congrArg Prod.snd hp)
  cases ha
  cases he
  have hχ : χ = ψ := Subsingleton.elim _ _
  cases hχ
  rfl

end OneClass

section DependentClasses

variable {I : Type*} [Fintype I]
variable (leftSlots rightSlots : I → ℕ)
variable (plain₁ plain₂ : I → Finset (Ideal (𝓞 K)))
variable (slots : ∀ i, Fin (rightSlots i) → Finset (HeightOneSpectrum (𝓞 K)))
variable (ideals : ∀ i, AllocationColumn K (rightSlots i) → Ideal (𝓞 K))
variable {γ : Type*} [Fintype γ] [Subsingleton γ]

/-- This is the dependent carrier occurring inside `CoveredLeafKey`;
the class retains both support-cover keys and therefore its slot counts. -/
abbrev OriginalAllocatedClass :=
  Σ i : I, HybridAllocationLabel (plain₁ i) (plain₂ i) (slots i) (ideals i)
    (leftSlots i) γ

variable {leftSlots rightSlots plain₁ plain₂ slots ideals}
variable {cap : ℕ}
variable (hleft : ∀ i, leftSlots i ≤ cap) (hright : ∀ i, rightSlots i ≤ cap)

def originalAllocationFingerprint
    (b : OriginalAllocatedClass leftSlots rightSlots plain₁ plain₂ slots ideals
      (γ := γ)) : OriginalAllocationFingerprint K cap :=
  hybridAllocationFingerprint (hleft b.1) (hright b.1) b.2

theorem original_class_allocationFingerprint_injective :
    Function.Injective (fun b : OriginalAllocatedClass leftSlots rightSlots
      plain₁ plain₂ slots ideals (γ := γ) =>
        (b.1, originalAllocationFingerprint hleft hright b)) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have hij : i = j := congrArg Prod.fst h
  cases hij
  have hab := hybridAllocationFingerprint_injective (hleft i) (hright i)
    (congrArg Prod.snd h)
  cases hab
  rfl

/-- For a fixed arithmetic allocation, projection to the genuine
source class is injective.  Thus occurrence allocations do not create
an additional fibre cost after they have entered the arithmetic index. -/
theorem original_allocation_fibre_card_eq_class_image
    (S : Finset (OriginalAllocatedClass leftSlots rightSlots plain₁ plain₂
      slots ideals (γ := γ))) (a : OriginalAllocationFingerprint K cap) :
    (S.filter (fun b => originalAllocationFingerprint hleft hright b = a)).card =
      ((S.filter (fun b => originalAllocationFingerprint hleft hright b = a)).image
        Sigma.fst).card := by
  symm
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  apply original_class_allocationFingerprint_injective hleft hright
  apply Prod.ext hxy
  exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm

/-- An actual arithmetic index may retain additional coordinates,
including the prime-pool tag, prime and valuation.  Its fibre is still
counted exactly by the genuine class image whenever its allocation
projection is the literal padded allocation. -/
theorem original_index_fibre_card_eq_class_image {J : Type*}
    (index : OriginalAllocatedClass leftSlots rightSlots plain₁ plain₂
      slots ideals (γ := γ) → J)
    (allocation : J → OriginalAllocationFingerprint K cap)
    (hindex : ∀ b, allocation (index b) = originalAllocationFingerprint hleft hright b)
    (S : Finset (OriginalAllocatedClass leftSlots rightSlots plain₁ plain₂
      slots ideals (γ := γ))) (j : J) :
    (S.filter (fun b => index b = j)).card =
      ((S.filter (fun b => index b = j)).image Sigma.fst).card := by
  symm
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  apply original_class_allocationFingerprint_injective hleft hright
  apply Prod.ext hxy
  rw [← hindex x, ← hindex y, (Finset.mem_filter.mp hx).2,
    (Finset.mem_filter.mp hy).2]

end DependentClasses

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.hybridAllocationFingerprint_injective
#print axioms HeckeSkeleton.Moments.EngineStep.original_index_fibre_card_eq_class_image
