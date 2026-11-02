import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.WholeAllocation
import HeckePort.Moments.Descent.IdealMasks

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Exact residual coprimality expansion on the restored carrier

The finite divisor/occurrence labels are those already fixed in
`PassiveData`. The identities below retain the whole complex summand,
so both continuous Fourier factors and both comparison rectangles can
be substituted without any additional expansion or density factor.
Only labels with zero sign or no actual columns are removed.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep NumberField IsDedekindDomain
open HeckePort.IdealMobiusDivisorSum
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global WholeAllocation

variable {K : Type} [Field K] [NumberField K]

namespace PassiveAllocation

variable {k : ℕ}

/-- The restored product carrier, before the residual coprimality gate. -/
def carrierColumns (B : Carrier K k) : Finset (AllocationColumn K k) :=
  childCartesianColumns (idealCarrier (B.plain false))
    (idealCarrier (B.plain true)) B.slots

/-- The same whole ideal is used by the residual mask at every occurrence. -/
def columnIdeal (i : AllocationColumn K k) : Ideal (𝓞 K) :=
  i.1.1 * i.1.2 * ∏ j, (i.2 j).asIdeal

theorem columns_subset_carrierColumns (B : Carrier K k) (a : Key K k) :
    columns B a ⊆ carrierColumns B := by
  unfold columns carrierColumns
  rw [paired_allocated_columns_eq_filter]
  exact Finset.filter_subset _ _

theorem label_mem_candidates (B : Carrier K k) (mask : Ideal (𝓞 K))
    (a : labels B mask) : a.val ∈ candidates mask k :=
  (Finset.mem_filter.mp a.property).1

theorem label_sign_ne_zero (B : Carrier K k) (mask : Ideal (𝓞 K))
    (a : labels B mask) : sign a.val ≠ 0 :=
  (Finset.mem_filter.mp a.property).2.1

theorem label_columns_nonempty (B : Carrier K k) (mask : Ideal (𝓞 K))
    (a : labels B mask) : (columns B a.val).Nonempty :=
  (Finset.mem_filter.mp a.property).2.2

theorem label_key_injective (B : Carrier K k) (mask : Ideal (𝓞 K)) :
    Function.Injective (fun a : labels B mask => a.val) :=
  Subtype.val_injective

@[simp] theorem allocation_columns (B : Carrier K k) (mask : Ideal (𝓞 K))
    (a : labels B mask) : (allocation B mask a).columns = columns B a.val := rfl

/-- The Mobius sum and all nonempty occurrence selections are exact,
including non-squarefree divisors, whose Mobius coefficient is zero. -/
theorem residual_mobius_candidates (B : Carrier K k) (mask : Ideal (𝓞 K))
    (hmask : mask ≠ 0) (C : AllocationColumn K k → ℂ) :
    (∑ i ∈ carrierColumns B with IsCoprime mask (columnIdeal i), C i) =
      ∑ a ∈ candidates mask k, sign a * ∑ i ∈ columns B a, C i := by
  have hterm (i : AllocationColumn K k) :
      (if IsCoprime mask (columnIdeal i) then C i else 0) =
        ∑ D ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors mask, (UniqueFactorizationMonoid.moebius D : ℂ) *
          (if D ∣ columnIdeal i then C i else 0) := by
    have h := congrArg (fun z : ℂ => z * C i)
      (HeckePort.Moments.ideal_coprime_mobius mask (columnIdeal i) hmask)
    simpa only [ite_mul, one_mul, zero_mul, Finset.sum_mul,
      mul_ite, mul_zero] using h
  calc
    _ = ∑ i ∈ carrierColumns B, ∑ D ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors mask,
        (UniqueFactorizationMonoid.moebius D : ℂ) * (if D ∣ columnIdeal i then C i else 0) := by
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun i _ => hterm i
    _ = ∑ D ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors mask, (UniqueFactorizationMonoid.moebius D : ℂ) *
        ∑ i ∈ carrierColumns B with D ∣ columnIdeal i, C i := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter, Finset.mul_sum]
    _ = _ := by
      rw [candidates, Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro D _
      have hD := moebius_paired_divisor_allocation D
        (idealCarrier (B.plain false)) (idealCarrier (B.plain true)) B.slots
        id id HeightOneSpectrum.asIdeal C
      calc
        _ = (UniqueFactorizationMonoid.moebius D : ℂ) *
            ∑ v ∈ AllocationMass.idealAllocations D (k + 2),
              AllocationMass.sign (primeSupport D) v *
                ∑ i ∈ columns B ⟨D, v⟩, C i := by
          simpa only [carrierColumns, columnIdeal, columns, id_eq] using hD
        _ = _ := by
          simp only [Finset.mul_sum, sign, mul_assoc]

/-- Filtering by the exact nonzero sign and actual nonempty carrier
deletes only zero terms; the dependent labels occur exactly once. -/
theorem candidates_sum_eq_labels (B : Carrier K k) (mask : Ideal (𝓞 K))
    (C : AllocationColumn K k → ℂ) :
    (∑ a ∈ candidates mask k, sign a * ∑ i ∈ columns B a, C i) =
      ∑ a : labels B mask, sign a.val * ∑ i ∈ columns B a.val, C i := by
  rw [Finset.sum_coe_sort]
  symm
  unfold labels
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hz : sign a = 0
  · simp [hz]
  · by_cases hc : (columns B a).Nonempty
    · simp [hz, hc]
    · have he : columns B a = ∅ := Finset.not_nonempty_iff_eq_empty.mp hc
      simp [hz, hc, he]

/-- The residual gate expands with the original whole coefficient.
The restored carriers still contain their fixed and paid exclusions. -/
theorem residual_mobius_labels (B : Carrier K k) (mask : Ideal (𝓞 K))
    (hmask : mask ≠ 0) (C : AllocationColumn K k → ℂ) :
    (∑ i ∈ carrierColumns B with IsCoprime mask (columnIdeal i), C i) =
      ∑ a : labels B mask, sign a.val * ∑ i ∈ columns B a.val, C i :=
  (residual_mobius_candidates B mask hmask C).trans
    (candidates_sum_eq_labels B mask C)

/-- A prime slot cannot contain two distinct selected divisor primes.
Such labels have no actual columns and were removed by `labels`. -/
theorem label_slot_unique (B : Carrier K k) (mask : Ideal (𝓞 K))
    (a : labels B mask) (i : Fin k) (p q : primeSupport a.val.1)
    (hp : i.succ.succ ∈ a.val.2 p) (hq : i.succ.succ ∈ a.val.2 q) :
    p = q := by
  by_contra hpq
  have he : columns B a.val = ∅ :=
    paired_columns_empty_of_double_slot a.val.1 a.val.2
      (idealCarrier (B.plain false)) (idealCarrier (B.plain true)) B.slots
      id id i p q hpq hp hq
  have hn := label_columns_nonempty B mask a
  simpa only [he, Finset.not_nonempty_empty] using hn

end PassiveAllocation

variable {c : TargetContext K} {call : Call c}

namespace SmoothSideSupport

variable {input : ProfileInput call} {k : ℕ} (S : SmoothSideSupport input k)

theorem plainCarrier_fixed_paid (paid : (Arithmetic.data c).Exterior)
    (side : Bool) (I : NonzeroIdeal K) (hI : I ∈ S.plainCarrier paid side) :
    IsCoprime I.val (Arithmetic.data c).cS ∧ IsCoprime I.val paid.val :=
  (Finset.mem_filter.mp hI).2

theorem slotCarrier_fixed_paid (paid : (Arithmetic.data c).Exterior)
    (i : Fin k) (q : HeightOneSpectrum (𝓞 K)) (hq : q ∈ S.slotCarrier paid i) :
    IsCoprime q.asIdeal (Arithmetic.data c).cS ∧ IsCoprime q.asIdeal paid.val :=
  (Finset.mem_filter.mp hq).2

end SmoothSideSupport

namespace OrdinaryData

variable {p : SourceParameters c} {packet : RawLeafPacket call p}
variable (O : OrdinaryData packet)

/-- Removing the already paid divisors preserves nonzeroness of the
literal finite deletion product, without choosing a replacement mask. -/
theorem passiveMask_ne_zero
    (hfull : (∏ I ∈ packet.second.physical.first.fullDeletion, I) ≠ 0) :
    O.passiveMask ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro I hI
  apply (Finset.prod_ne_zero_iff.mp hfull) I
  exact (Finset.mem_filter.mp hI).1

end OrdinaryData
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveAllocation.residual_mobius_labels
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveAllocation.label_slot_unique
