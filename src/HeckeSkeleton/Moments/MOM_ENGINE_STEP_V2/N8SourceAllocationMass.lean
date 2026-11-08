module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8SourceClassCounts

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Both original inner-divisor allocation families

The two independent occurrence allocations in `AllocationKey` are
summed exactly with their own inner-divisor density.  Their occurrences
are those of the two reconstructed original Cartesian sources.  The
uniform estimate uses the proved harmonic allocation bound and the
actual residual-column norm window.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open DedekindZetaZeroFree.LargeSieve
open CommonSupportMass HeckePort.IdealMobiusDivisorSum
open HeckePort.Moments HeckePort.Moments.MobiusRegroup
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  coveredClassKeyFintype

local instance n8AllocationMassCircleFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace SourceClassKey

variable {source : SecondSource call p}
variable {LC RC : OriginalCover source.physical}
variable (key : SourceClassKey source.stage LC.cover RC.cover)

/-- The actual independent second Möbius divisor pool. -/
def innerDivisors : Finset (Ideal (𝓞 K)) :=
  divisorPool
    (childCartesianColumns (SourceClassKey.rightReindex key).plain₁
      (SourceClassKey.rightReindex key).plain₂ (SourceClassKey.rightReindex key).slots)
    (fun j => ((SourceClassKey.block key).rightResidual
      ((SourceClassKey.rightReindex key).index j)).val)

/-- Both full occurrence-allocation families remain in this exact sum. -/
def allocationIndexMass : ℝ :=
  ∑ a : SourceClassKey.AllocationKey key,
    ‖(UniqueFactorizationMonoid.moebius a.1.val : ℂ)‖ / (Ideal.absNorm a.1.val : ℝ)

theorem allocationIndexMass_nonneg : 0 ≤ key.allocationIndexMass :=
  Finset.sum_nonneg (fun _ _ => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))

theorem allocationIndexMass_eq :
    key.allocationIndexMass =
      (Fintype.card ((PUnit.{1} × PUnit.{1}) →* Circle) : ℝ) *
        secondDivisorAllocationMass key.innerDivisors
          (fun _ => SourceClassKey.leftSlots key + 2)
          (fun _ => SourceClassKey.rightSlots key + 2) := by
  simp only [allocationIndexMass, AllocationKey, HybridAllocationLabel,
    Fintype.sum_sigma, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_coe, nsmul_eq_mul, Nat.cast_mul]
  conv_rhs =>
    rw [secondDivisorAllocationMass, Finset.mul_sum, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro D _
  have hslots : (SourceClassKey.rightReindexInputs key).slotCount =
      SourceClassKey.rightSlots key := rfl
  have hcard :
      ((AllocationMass.idealAllocations D.val
        ((SourceClassKey.rightReindexInputs key).slotCount + 2)).card : ℝ) =
      ((AllocationMass.idealAllocations D.val
        (SourceClassKey.rightSlots key + 2)).card : ℝ) :=
    congrArg (fun n : ℕ =>
      ((AllocationMass.idealAllocations D.val (n + 2)).card : ℝ)) hslots
  exact (congrArg (fun mass : ℝ =>
    (Fintype.card ((PUnit.{1} × PUnit.{1}) →* Circle) : ℝ) *
      (((AllocationMass.idealAllocations D.val
        (SourceClassKey.leftSlots key + 2)).card : ℝ) * mass) *
      (‖(UniqueFactorizationMonoid.moebius D.val : ℂ)‖ /
        (Ideal.absNorm D.val : ℝ))) hcard).trans (by ring)

theorem innerDivisor_ne_zero (D : Ideal (𝓞 K)) (hD : D ∈ key.innerDivisors) :
    D ≠ 0 := by
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hD
  have hJ := ((SourceClassKey.block key).rightResidual
    ((SourceClassKey.rightReindex key).index j)).property.1
  exact ne_zero_of_dvd_ne_zero hJ ((mem_idealDivisors hJ).mp hj)

theorem innerDivisor_norm_le (M : ℝ)
    (hnorm : ∀ j ∈ childCartesianColumns (SourceClassKey.rightReindex key).plain₁
      (SourceClassKey.rightReindex key).plain₂ (SourceClassKey.rightReindex key).slots,
      (Ideal.absNorm ((SourceClassKey.block key).rightResidual
        ((SourceClassKey.rightReindex key).index j)).val : ℝ) ≤ M)
    (D : Ideal (𝓞 K)) (hD : D ∈ key.innerDivisors) :
    (Ideal.absNorm D : ℝ) ≤ M := by
  obtain ⟨j, hj, hDj⟩ := Finset.mem_biUnion.mp hD
  have hJ := ((SourceClassKey.block key).rightResidual
    ((SourceClassKey.rightReindex key).index j)).property.1
  have hd := (mem_idealDivisors hJ).mp hDj
  have hN : Ideal.absNorm D ≤ Ideal.absNorm
      ((SourceClassKey.block key).rightResidual
        ((SourceClassKey.rightReindex key).index j)).val :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ))
      (map_dvd Ideal.absNorm hd)
  exact (Nat.cast_le.mpr hN).trans (hnorm j hj)

end SourceClassKey

namespace N8Source

/-- A fixed constant for the actual inner-divisor and two-allocation
sum.  The only moving quantitative input is a norm window for the
original reconstructed right residual columns. -/
theorem actual_allocation_index_mass (c : TargetContext K) (B ε : ℝ)
    (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (call : Call c) (p : SourceParameters c)
      (source : SecondSource call p) (LC RC : OriginalCover source.physical),
      LC.Realizes → RC.Realizes →
      ∀ key : SourceClassKey source.stage LC.cover RC.cover,
      (∀ j ∈ childCartesianColumns (SourceClassKey.rightReindex key).plain₁
        (SourceClassKey.rightReindex key).plain₂ (SourceClassKey.rightReindex key).slots,
        (Ideal.absNorm ((SourceClassKey.block key).rightResidual
          ((SourceClassKey.rightReindex key).index j)).val : ℝ) ≤ call.base ^ B) →
      key.allocationIndexMass ≤ C * call.base ^ ε := by
  obtain ⟨C, hC, hmass⟩ := second_divisor_allocation_mass (K := K)
    (c.geometry.slots + 2) B ε hB hε
  have hphase : 0 < (Fintype.card ((PUnit.{1} × PUnit.{1}) →* Circle) : ℝ) := by
    exact_mod_cast (Fintype.card_pos :
      0 < Fintype.card ((PUnit.{1} × PUnit.{1}) →* Circle))
  refine ⟨(Fintype.card ((PUnit.{1} × PUnit.{1}) →* Circle) : ℝ) * C,
    mul_pos hphase hC, ?_⟩
  intro call p source LC RC hLC hRC key hnorm
  have hbase_pos : 0 < call.base := call.base_pos
  have h := hmass call.base call.domain.scale.le key.innerDivisors
    key.innerDivisor_ne_zero (key.innerDivisor_norm_le _ hnorm)
    (fun _ => SourceClassKey.leftSlots key + 2)
    (fun _ => SourceClassKey.rightSlots key + 2)
    (fun _ _ => ⟨Nat.add_le_add_right (key.leftSlots_le_original hLC) 2,
      Nat.add_le_add_right (key.rightSlots_le_original hRC) 2⟩)
  rw [key.allocationIndexMass_eq]
  exact (mul_le_mul_of_nonneg_left h hphase.le).trans_eq (by ring)

end N8Source
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.SourceClassKey.allocationIndexMass_eq
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8Source.actual_allocation_index_mass
