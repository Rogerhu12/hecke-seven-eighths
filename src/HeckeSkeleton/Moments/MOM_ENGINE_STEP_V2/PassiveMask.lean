module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveExpansion
public import Mathlib.RingTheory.Coprime.Lemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The paid gate splits the original deletion mask exactly

The restored carrier retains the fixed bad-prime gate and the paid
moving gate occurrence by occurrence. Consequently deleting from the
original first mask its already paid primes changes no summand. The
result below inserts exactly the residual Mobius/occurrence expansion
on this carrier, with the original full mask still visible on the left.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

namespace PassiveAllocation

variable {k : ℕ}

/-- Every full column retains any gate imposed on all of its factors. -/
theorem carrierColumns_coprime (B : Carrier K k) (mask : Ideal (𝓞 K))
    (hplain : ∀ side I, I ∈ B.plain side → IsCoprime I.val mask)
    (hslot : ∀ j q, q ∈ B.slots j → IsCoprime q.asIdeal mask)
    (i : AllocationColumn K k) (hi : i ∈ carrierColumns B) :
    IsCoprime (columnIdeal i) mask := by
  obtain ⟨hp, hs⟩ := Finset.mem_product.mp hi
  obtain ⟨hl, hr⟩ := Finset.mem_product.mp hp
  obtain ⟨I, hI, hIe⟩ := Finset.mem_image.mp hl
  obtain ⟨J, hJ, hJe⟩ := Finset.mem_image.mp hr
  have hleft : IsCoprime i.1.1 mask := hIe ▸ hplain false I hI
  have hright : IsCoprime i.1.2 mask := hJe ▸ hplain true J hJ
  have hprimes : IsCoprime (∏ j, (i.2 j).asIdeal) mask :=
    IsCoprime.prod_left fun j _ => hslot j (i.2 j) (Fintype.mem_piFinset.mp hs j)
  exact (hleft.mul_left hright).mul_left hprimes

end PassiveAllocation

variable {c : TargetContext K} {call : Call c}

namespace SmoothSideSupport

variable {input : ProfileInput call} {k : ℕ} (S : SmoothSideSupport input k)

theorem carrierColumns_fixed_paid (paid : (Arithmetic.data c).Exterior)
    (i : AllocationColumn K k)
    (hi : i ∈ PassiveAllocation.carrierColumns (S.carrier paid)) :
    IsCoprime (PassiveAllocation.columnIdeal i) (Arithmetic.data c).cS ∧
      IsCoprime (PassiveAllocation.columnIdeal i) paid.val := by
  constructor
  · exact PassiveAllocation.carrierColumns_coprime (S.carrier paid)
      (Arithmetic.data c).cS
      (fun side I hI => (S.plainCarrier_fixed_paid paid side I hI).1)
      (fun j q hq => (S.slotCarrier_fixed_paid paid j q hq).1) i hi
  · exact PassiveAllocation.carrierColumns_coprime (S.carrier paid) paid.val
      (fun side I hI => (S.plainCarrier_fixed_paid paid side I hI).2)
      (fun j q hq => (S.slotCarrier_fixed_paid paid j q hq).2) i hi

end SmoothSideSupport

namespace OrdinaryData

variable {p : SourceParameters c} {packet : RawLeafPacket call p}
variable (O : OrdinaryData packet)

/-- The discarded factors are divisors of the paid support, hence
their coprimality is already enforced rather than silently removed. -/
theorem residual_coprime_iff (I : Ideal (𝓞 K))
    (hpaid : IsCoprime I packet.second.physical.first.paidSupport.val) :
    IsCoprime I (∏ P ∈ packet.second.physical.first.fullDeletion, P) ↔
      IsCoprime I O.passiveMask := by
  simp only [passiveMask, IsCoprime.prod_right_iff]
  constructor
  · intro h P hP
    exact h P (Finset.mem_filter.mp hP).1
  · intro h P hP
    by_cases hd : P ∣ packet.second.physical.first.paidSupport.val
    · exact hpaid.of_isCoprime_of_dvd_right hd
    · exact h P (Finset.mem_filter.mpr ⟨hP, hd⟩)

/-- The complete original deletion mask, on the original restored
fixed/paid carrier, is exactly its residual allocation sum. -/
theorem restored_residual_expansion {input : ProfileInput call}
    (support : O.PassiveSupport input) (side : Bool)
    (hfull : (∏ I ∈ packet.second.physical.first.fullDeletion, I) ≠ 0)
    (C : AllocationColumn K (O.residualSlotCount side) → ℂ) :
    (∑ i ∈ PassiveAllocation.carrierColumns (support.carrier side) with
      IsCoprime (PassiveAllocation.columnIdeal i)
        (∏ P ∈ packet.second.physical.first.fullDeletion, P), C i) =
      ∑ a : support.labels side, PassiveAllocation.sign a.val *
        ∑ i ∈ PassiveAllocation.columns (support.carrier side) a.val, C i := by
  calc
    _ = ∑ i ∈ PassiveAllocation.carrierColumns (support.carrier side) with
        IsCoprime O.passiveMask (PassiveAllocation.columnIdeal i), C i := by
      rw [Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      have hp := ((support.side side).carrierColumns_fixed_paid
        packet.second.physical.first.paidSupport i hi).2
      rw [O.residual_coprime_iff _ hp, isCoprime_comm]
    _ = _ := PassiveAllocation.residual_mobius_labels (support.carrier side)
      O.passiveMask (O.passiveMask_ne_zero hfull) C

end OrdinaryData
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryData.restored_residual_expansion
