module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceIndexContracts

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Exact arithmetic projection of the original N8a carrier

The finite ledger below is the image of the actual raw labels.  Its
four ideal coordinates retain both common pairs and both independent
Möbius divisors.  The original physical-source index is a separate
coordinate, so the pool factor is neither reselected nor charged twice.

The exact fibre identity separates this arithmetic ledger from the
original cover, row-class and occurrence decorations.  This file proves
identities and positivity only; it asserts no uniform bound for those
fibres.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open CommonSupportMass HeckePort.IdealMobiusDivisorSum
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  coveredClassKeyFintype

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

namespace PoolExpansion

theorem indexPrefactor_nonneg (expansion : PoolExpansion family)
    (i : Fin expansion.count) : 0 ≤ expansion.indexPrefactor i := by
  cases expansion with
  | direct => norm_num [indexPrefactor]
  | pooled pool count index source =>
    change 0 ≤ (4 / (pool.data (index i).1).density) * _
    apply mul_nonneg (div_nonneg (by norm_num) (pool.data (index i).1).density_pos.le)
    cases h : (index i).2 with
    | inl u =>
      exact mul_nonneg (pool.data (index i).1).multiplicity_nonneg
        (Real.rpow_nonneg call.base_pos.le _)
    | inr qe =>
      exact mul_nonneg (FirstGaussPoolData.localErrorWeight_nonneg _ _)
        (pow_nonneg (by
          change (0 : ℝ) ≤ (Ideal.absNorm qe.1.val.val.asIdeal : ℝ)
          positivity) _)

end PoolExpansion

namespace N8Source

/-- The original source label and the four original arithmetic ideals.
The pairs are ordered: no symmetry quotient identifies opposite sides. -/
abbrev ArithmeticKey (sourceCount : ℕ) :=
  Fin sourceCount × (Ideal (𝓞 K) × Ideal (𝓞 K)) × Ideal (𝓞 K) ×
    (Ideal (𝓞 K) × Ideal (𝓞 K)) × Ideal (𝓞 K)

def arithmeticWeight (expansion : PoolExpansion family)
    (key : ArithmeticKey (K := K) expansion.count) : ℝ :=
  expansion.indexPrefactor key.1 *
    ((1 / (Ideal.absNorm (commonRadical key.2.1.1 key.2.1.2) : ℝ)) *
      ‖(UniqueFactorizationMonoid.moebius key.2.2.1 : ℂ)‖ *
      (1 / (Ideal.absNorm (commonRadical key.2.2.2.1.1 key.2.2.2.1.2) : ℝ)) *
      ‖(UniqueFactorizationMonoid.moebius key.2.2.2.2 : ℂ)‖) /
    (Ideal.absNorm key.2.2.2.2 : ℝ)

theorem arithmeticWeight_nonneg (expansion : PoolExpansion family)
    (key : ArithmeticKey (K := K) expansion.count) :
    0 ≤ arithmeticWeight expansion key := by
  unfold arithmeticWeight
  apply div_nonneg
  · apply mul_nonneg (expansion.indexPrefactor_nonneg _)
    positivity
  · positivity

end N8Source

namespace RawFamily

variable {expansion : PoolExpansion family} {second : SecondFamily expansion}
variable {geometry : GeometryFamily second} (raw : RawFamily geometry)

theorem commonIndexFactor_nonneg (j : Fin raw.count) :
    0 ≤ raw.commonIndexFactor j := by
  unfold commonIndexFactor
  positivity

theorem indexWeight_nonneg (j : Fin raw.count) : 0 ≤ raw.indexWeight j :=
  div_nonneg
    (mul_nonneg (expansion.indexPrefactor_nonneg _) (raw.commonIndexFactor_nonneg j))
    (Nat.cast_nonneg _)

theorem exceptionalDyadWeight_nonneg (lower : ℝ) (j : Fin raw.count) :
    0 ≤ raw.exceptionalDyadWeight lower j :=
  mul_nonneg
    (mul_nonneg (expansion.indexPrefactor_nonneg _) (raw.commonIndexFactor_nonneg j))
    (Real.rpow_nonneg call.base_pos.le _)

theorem indexMass_nonneg : 0 ≤ raw.indexMass :=
  Finset.sum_nonneg (fun j _ => raw.indexWeight_nonneg j)

/-- This projection forgets only the decorative finite coordinates.
It retains the same original source index and both divisor variables. -/
def arithmeticKey (j : Fin raw.count) :
    N8Source.ArithmeticKey (K := K) expansion.count :=
  let packet := raw.packet j
  (raw.sourceIndex j,
    (packet.second.physical.first.selected.val, packet.second.physical.first.opposite.val),
    packet.second.physical.first.residualDivisor.val,
    (packet.key.1.val.1, packet.key.1.val.2), raw.innerDivisor j)

/-- The ledger is the exact image of the original live raw carrier. -/
def arithmeticCarrier : Finset (N8Source.ArithmeticKey (K := K) expansion.count) :=
  Finset.univ.image raw.arithmeticKey

theorem arithmeticKey_mem (j : Fin raw.count) :
    raw.arithmeticKey j ∈ raw.arithmeticCarrier :=
  Finset.mem_image_of_mem _ (Finset.mem_univ j)

/-- The projected weight is definitionally the original N8a weight. -/
theorem arithmeticWeight_eq (j : Fin raw.count) :
    N8Source.arithmeticWeight expansion (raw.arithmeticKey j) = raw.indexWeight j := rfl

theorem indexWeight_eq_of_arithmeticKey_eq (i j : Fin raw.count)
    (h : raw.arithmeticKey i = raw.arithmeticKey j) :
    raw.indexWeight i = raw.indexWeight j := by
  rw [← raw.arithmeticWeight_eq i, ← raw.arithmeticWeight_eq j, h]

def arithmeticFibre (key : N8Source.ArithmeticKey (K := K) expansion.count) :
    Finset (Fin raw.count) :=
  Finset.univ.filter (fun j => raw.arithmeticKey j = key)

theorem sum_indexWeight_arithmeticFibre
    (key : N8Source.ArithmeticKey (K := K) expansion.count) :
    (∑ j ∈ raw.arithmeticFibre key, raw.indexWeight j) =
      ((raw.arithmeticFibre key).card : ℝ) * N8Source.arithmeticWeight expansion key := by
  calc
    _ = ∑ _j ∈ raw.arithmeticFibre key, N8Source.arithmeticWeight expansion key := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← raw.arithmeticWeight_eq j, (Finset.mem_filter.mp hj).2]
    _ = _ := by simp

/-- Exact finite partition, before any divisor or profile estimate.
In particular every passive physical decoration is counted once. -/
theorem indexMass_eq_sum_arithmeticFibres :
    raw.indexMass = ∑ key ∈ raw.arithmeticCarrier,
      ((raw.arithmeticFibre key).card : ℝ) * N8Source.arithmeticWeight expansion key := by
  have hpartition := Finset.sum_fiberwise_of_maps_to
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin raw.count))) => raw.arithmeticKey_mem j)
    (fun j => raw.indexWeight j)
  change (∑ j : Fin raw.count, raw.indexWeight j) = _
  rw [← hpartition]
  apply Finset.sum_congr rfl
  intro key _
  exact raw.sum_indexWeight_arithmeticFibre key

/-- Only a bound for the actual projected fibre may be used in this
finite comparison.  The arithmetic weight is unchanged. -/
theorem indexMass_le_arithmeticCarrier (multiplicity : ℝ)
    (hcard : ∀ key ∈ raw.arithmeticCarrier,
      ((raw.arithmeticFibre key).card : ℝ) ≤ multiplicity) :
    raw.indexMass ≤ multiplicity *
      ∑ key ∈ raw.arithmeticCarrier, N8Source.arithmeticWeight expansion key := by
  rw [raw.indexMass_eq_sum_arithmeticFibres, Finset.mul_sum]
  exact Finset.sum_le_sum fun key hkey => mul_le_mul_of_nonneg_right
    (hcard key hkey) (N8Source.arithmeticWeight_nonneg expansion key)

/-- A compatibility filter is paid by the same finite ledger. -/
theorem sum_indexWeight_subset_le (labels : Finset (Fin raw.count)) :
    (∑ j ∈ labels, raw.indexWeight j) ≤ raw.indexMass := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ labels)
    (fun j _ _ => raw.indexWeight_nonneg j)

end RawFamily
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawFamily.indexMass_eq_sum_arithmeticFibres
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawFamily.indexMass_le_arithmeticCarrier
