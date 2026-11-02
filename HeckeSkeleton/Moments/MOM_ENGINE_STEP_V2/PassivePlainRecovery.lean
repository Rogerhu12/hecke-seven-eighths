import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveSupportRecovery
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralTerms

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-! # Reconstructing the actual two support quotients and the inner divisor -/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassivePlainRecovery

open EngineStep NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

theorem residual_coprime (T P : Finset (Ideal (𝓞 K))) (D G : Ideal (𝓞 K))
    (hT : ∀ I ∈ T, I ≠ 0) (hcop : ∀ I ∈ T, IsCoprime I G)
    (J : Ideal (𝓞 K)) (hJ : J ∈ SupportCartesian.plainResidual T P D) :
    IsCoprime J G := by
  have hm := (Finset.mem_filter.mp
    (SupportCartesian.plain_reconstruct_mem T P D J hT hJ)).1
  exact (hcop _ hm).of_mul_left_right

theorem residual_avoids (T P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
    (hP : ∀ q ∈ P, Prime q) (J : Ideal (𝓞 K))
    (hJ : J ∈ SupportCartesian.plainResidual T P D) :
    ∀ q ∈ P, IsCoprime J q := by
  obtain ⟨I, _, rfl⟩ := Finset.mem_image.mp hJ
  exact (outside_iff_coprime P hP ⟨_, supportResidual_ne_zero I P⟩).mp
    (residual_outside P hP I)

variable {k : ℕ} {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable {P : Finset (Ideal (𝓞 K))}

def branchInput (_b : SupportCartesianBranch S₁ S₂ S P) (plain : Bool) :
    Finset (Ideal (𝓞 K)) := if plain then S₂ else S₁

def branchDivisor (b : SupportCartesianBranch S₁ S₂ S P) (plain : Bool) :
    HeckeGeneral.Analysis.NonzeroIdeal K := if plain then b.plainDivisor₂ else b.plainDivisor₁

def branchWitness (b : SupportCartesianBranch S₁ S₂ S P) (plain : Bool) :
    Ideal (𝓞 K) := if plain then b.witness.1.2 else b.witness.1.1

theorem branch_nonzero (b : SupportCartesianBranch S₁ S₂ S P) (plain : Bool)
    (I : Ideal (𝓞 K)) (hI : I ∈ branchInput b plain) : I ≠ 0 := by
  cases plain
  · exact b.plain₁_nonzero I hI
  · exact b.plain₂_nonzero I hI

theorem branch_witness (b : SupportCartesianBranch S₁ S₂ S P) (plain : Bool) :
    branchWitness b plain ∈ branchInput b plain ∧
      supportExtract (branchWitness b plain) P = (branchDivisor b plain).val := by
  have hw := Finset.mem_product.mp (Finset.mem_product.mp b.witness_mem).1
  cases plain
  · exact Finset.mem_filter.mp hw.1
  · exact Finset.mem_filter.mp hw.2

theorem branch_smooth (b : SupportCartesianBranch S₁ S₂ S P) (plain : Bool) :
    primeSupport (branchDivisor b plain).val ⊆ P := by
  rw [← (branch_witness b plain).2, supportExtract_support]
  exact Finset.inter_subset_right

theorem branch_divisor_dvd (b : SupportCartesianBranch S₁ S₂ S P) (plain : Bool) :
    (branchDivisor b plain).val ∣ branchWitness b plain := by
  refine ⟨supportResidual (branchWitness b plain) P, ?_⟩
  rw [← (branch_witness b plain).2]
  exact (support_reconstruct _ (branch_nonzero b plain _ (branch_witness b plain).1) P).symm

theorem branch_coprime (b : SupportCartesianBranch S₁ S₂ S P) (plain : Bool)
    (G : Ideal (𝓞 K)) (hG : ∀ I ∈ branchInput b plain, IsCoprime I G) :
    IsCoprime (branchDivisor b plain).val G :=
  (hG _ (branch_witness b plain).1).of_isCoprime_of_dvd_left (branch_divisor_dvd b plain)

def allocationInput (B : ActualColumnAllocation K k) (plain : Bool) :
    Finset (Ideal (𝓞 K)) := if plain then B.plain₂ else B.plain₁

def allocationDivisor (B : ActualColumnAllocation K k) (plain : Bool) :
    HeckeGeneral.Analysis.NonzeroIdeal K := B.plainDivisor (if plain then Fin.succ 0 else 0)

def allocationChild (B : ActualColumnAllocation K k) (plain : Bool) :
    Finset (HeckeGeneral.Analysis.NonzeroIdeal K) := if plain then B.childPlain₂ else B.childPlain₁

def allocationWitness (B : ActualColumnAllocation K k) (plain : Bool) :
    Ideal (𝓞 K) := if plain then B.witness.1.2 else B.witness.1.1

theorem allocation_witness (B : ActualColumnAllocation K k) (plain : Bool) :
    allocationWitness B plain ∈ allocationInput B plain ∧
      (allocationDivisor B plain).val ∣ allocationWitness B plain := by
  have hw := Finset.mem_product.mp (Finset.mem_product.mp B.witness_mem).1
  cases plain
  · exact Finset.mem_filter.mp hw.1
  · exact Finset.mem_filter.mp hw.2

theorem allocation_coprime (B : ActualColumnAllocation K k) (plain : Bool)
    (G : Ideal (𝓞 K)) (hG : ∀ I ∈ allocationInput B plain, IsCoprime I G) :
    IsCoprime (allocationDivisor B plain).val G :=
  (hG _ (allocation_witness B plain).1).of_isCoprime_of_dvd_left
    (allocation_witness B plain).2

theorem allocationChild_mem (B : ActualColumnAllocation K k) (plain : Bool)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) : I ∈ allocationChild B plain ↔
      (allocationDivisor B plain).val * I.val ∈ allocationInput B plain := by
  cases plain <;>
    exact mem_nonzeroQuotientMomentSupport _ (nonZeroDivisors.coe_ne_zero _) _ _

section Nested

variable {l : ℕ} {T₁ T₂ : Finset (Ideal (𝓞 K))}
variable {T : Fin l → Finset (HeightOneSpectrum (𝓞 K))}
variable {Q : Finset (Ideal (𝓞 K))} {n : ℕ}
variable (b₁ : SupportCartesianBranch S₁ S₂ S P)
variable (b₂ : SupportCartesianBranch T₁ T₂ T Q)
variable (B : ActualColumnAllocation K n) (plain : Bool)
variable (h₂ : branchInput b₂ plain = SupportCartesian.plainResidual
  (branchInput b₁ plain) P (branchDivisor b₁ plain).val)
variable (h₀ : allocationInput B plain = SupportCartesian.plainResidual
  (branchInput b₂ plain) Q (branchDivisor b₂ plain).val)

include h₂ h₀

theorem nested_divisor_coprime (G : Ideal (𝓞 K))
    (hG : ∀ I ∈ branchInput b₁ plain, IsCoprime I G) :
    IsCoprime ((branchDivisor b₁ plain).val *
      ((branchDivisor b₂ plain).val * (allocationDivisor B plain).val)) G := by
  have hf : ∀ I ∈ branchInput b₂ plain, IsCoprime I G := by
    rw [h₂]
    exact residual_coprime _ _ _ G (branch_nonzero b₁ plain) hG
  have hs : ∀ I ∈ allocationInput B plain, IsCoprime I G := by
    rw [h₀]
    exact residual_coprime _ _ _ G (branch_nonzero b₂ plain) hf
  exact (branch_coprime b₁ plain G hG).mul_left
    ((branch_coprime b₂ plain G hf).mul_left (allocation_coprime B plain G hs))

/-- The fixed first extraction, fixed second extraction and original
inner divisor can all be reconstructed from a nonzero original profile.
The old witness forces the extracted divisors to retain the earlier gates. -/
theorem nested_mem (hP : ∀ q ∈ P, Prime q) (hQ : ∀ q ∈ Q, Prime q)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) (hIP : ∀ q ∈ P, IsCoprime I.val q)
    (hIQ : ∀ q ∈ Q, IsCoprime I.val q)
    (hmem : (branchDivisor b₁ plain).val *
      ((branchDivisor b₂ plain).val * ((allocationDivisor B plain).val * I.val)) ∈
        branchInput b₁ plain) : I ∈ allocationChild B plain := by
  have hf (q : Ideal (𝓞 K)) (hq : q ∈ P) :
      ∀ J ∈ branchInput b₂ plain, IsCoprime J q := by
    rw [h₂]
    intro J hJ
    exact residual_avoids _ _ _ hP J hJ q hq
  have hs (q : Ideal (𝓞 K)) (hq : q ∈ P) :
      ∀ J ∈ allocationInput B plain, IsCoprime J q := by
    rw [h₀]
    exact residual_coprime _ _ _ q (branch_nonzero b₂ plain) (hf q hq)
  have hz (q : Ideal (𝓞 K)) (hq : q ∈ Q) :
      ∀ J ∈ allocationInput B plain, IsCoprime J q := by
    rw [h₀]
    intro J hJ
    exact residual_avoids _ _ _ hQ J hJ q hq
  apply (allocationChild_mem B plain I).mpr
  rw [h₀]
  apply PassiveSupportRecovery.plain_residual_mem _ Q hQ
    (branchDivisor b₂ plain).val ((allocationDivisor B plain).val * I.val)
    (nonZeroDivisors.coe_ne_zero _)
    (mul_ne_zero (nonZeroDivisors.coe_ne_zero _) (nonZeroDivisors.coe_ne_zero I))
    (branch_smooth b₂ plain)
  · intro q hq
    exact (allocation_coprime B plain q (hz q hq)).mul_left (hIQ q hq)
  · rw [h₂]
    apply PassiveSupportRecovery.plain_residual_mem _ P hP
      (branchDivisor b₁ plain).val
      ((branchDivisor b₂ plain).val * ((allocationDivisor B plain).val * I.val))
      (nonZeroDivisors.coe_ne_zero _)
      (mul_ne_zero (nonZeroDivisors.coe_ne_zero _)
        (mul_ne_zero (nonZeroDivisors.coe_ne_zero _) (nonZeroDivisors.coe_ne_zero I)))
      (branch_smooth b₁ plain) _ hmem
    intro q hq
    exact (branch_coprime b₂ plain q (hf q hq)).mul_left
      ((allocation_coprime B plain q (hs q hq)).mul_left (hIP q hq))

end Nested
end HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassivePlainRecovery

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassivePlainRecovery.nested_divisor_coprime
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassivePlainRecovery.nested_mem
