import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstZeroColumnWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstZeroInputBounds

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# T1: the actual input supplies the first profile and product windows

The original one-variable representatives are restricted only in their
finite set of controlled seminorms. Their values, support window and
amplitude are unchanged. The original arithmetic atoms then supply the
negative central exponent of each literal working coefficient.

Every mixed seminorm is evaluated on the same fixed row-ball test. Its
scalar bound therefore depends only on the target and the finite orders,
before any call or profile input. The original source equivalence
transports the full column carrier, and sharp product windows are used
only where the actual original profile is nonzero.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstZeroProof

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineStep HeckeSkeleton.Moments.EngineInduction
open HeckeSkeleton.Moments.EngineInduction.Source

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

/-- Only the four seminorm proofs change; the original representatives
and all their support proofs are retained verbatim. -/
private def restrictRawProfileOrders
    {ω ψ : HeckeCharacter K}
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {s t : Finset (ℕ × ℕ)}
    {d : MomentData K ω ψ} {B : ℝ}
    (w : RawProfileWindow rowDomain heightDomain window t d B) (hst : s ⊆ t) :
    RawProfileWindow rowDomain heightDomain window s d B :=
  { w with
    inverse_bound := fun u hu v hv =>
      (Seminorm.le_def.mp (Finset.sup_mono hst) (w.inverseRep u v)).trans
        (w.inverse_bound u hu v hv)
    left_bound := fun u hu v hv =>
      (Seminorm.le_def.mp (Finset.sup_mono hst) (w.leftRep u v)).trans
        (w.left_bound u hu v hv)
    right_bound := fun u hu v hv =>
      (Seminorm.le_def.mp (Finset.sup_mono hst) (w.rightRep u v)).trans
        (w.right_bound u hu v hv)
    prime_bound := fun i v hv =>
      (Seminorm.le_def.mp (Finset.sup_mono hst) (w.primeRep i v)).trans
        (w.prime_bound i v hv) }

variable {c : TargetContext K} {call : Call c}

/-- The ready check supplies the fixed point-evaluation order. -/
theorem point_orders_of_ready {cost : UniformCost} {input : ProfileInput call}
    (hready : cost.Ready call input) (hpoint : (0, 0) ∈ cost.orders) :
    {(0, 0)} ⊆ input.orders := by
  intro q hq
  rw [Finset.mem_singleton.mp hq]
  exact hready.orders hpoint

/-- Localization and order restriction reuse all original functions. -/
def localizedPointProfiles (input : ProfileInput call)
    (horders : {(0, 0)} ⊆ input.orders) :
    RawProfileWindow Set.univ Set.univ call.window
      (OriginalProfileAtomBounds.profileOrders ∅) call.localizedData input.amplitude :=
  restrictRawProfileOrders input.localized
    (by simpa only [OriginalProfileAtomBounds.profileOrders, Finset.insert_empty] using horders)

/-- The actual coefficient retains both central plain factors and
every original prime factor. Its scalar degree uses the fixed slot cap. -/
theorem working_coefficient_norm_le (input : ProfileInput call)
    (horders : {(0, 0)} ⊆ input.orders)
    (v : call.workingRaw.Column) (hv : v ∈ call.workingRaw.exteriorColumns) :
    ‖call.workingValues.coefficient call.node.centered v‖ ≤
      (2 * input.amplitude ^ (c.geometry.slots + 2)) *
        call.base ^ (-(call.workingParameters.n₁ + call.workingParameters.n₂ +
          call.workingParameters.z) / 2) := by
  have hleft : ∀ I, ‖call.workingAtoms.leftArithmetic I‖ ≤ 1 := by
    intro I
    exact arithmeticAtoms_left_norm_le_one call.localizedSource.source.recipe PUnit.unit I
  have hright : ∀ I, ‖call.workingAtoms.rightArithmetic I‖ ≤ 1 := by
    intro I
    exact arithmeticAtoms_right_norm_le_one call.localizedSource.source.recipe PUnit.unit I
  have hprime : ∀ i p, ‖call.workingAtoms.primeArithmetic i p‖ ≤ 1 := by
    intro i p
    exact arithmeticAtoms_prime_norm_le_one call.localizedSource.source.recipe PUnit.unit i p
  have hcap : call.localizedData.geometry.slotCount ≤ c.geometry.slots := call.slots_le
  have hraw : v ∈ (call.workingAtoms.raw (call.base ^ call.workingComparison₁)
      (call.base ^ call.workingComparison₂)).columns := (Finset.mem_filter.mp hv).1
  have hbound := coefficient_norm_le_raw_profile_window call.workingAtoms
    (localizedPointProfiles input horders) hleft hright hprime
    c.geometry.slots hcap input.amplitude_one_le call.base_pos
    (fun _ _ => Set.mem_univ _) (Set.mem_univ _)
    call.node.centered (fun _ => working_comparison₁_scale_nonneg call)
    (fun _ => working_comparison_product call) v hraw
  simpa only [working_total_length call] using hbound

/-- A fixed finite mixed seminorm of the original row-ball test.
There is no call, original profile or moving scalar in this constant. -/
def originalArchSeminorm (c : TargetContext K) (eta : Finset (ℕ × ℕ)) : ℝ :=
  eta.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (CanonicalRowBall.archTest K (Arithmetic.data c).Sf 1)

theorem originalArchSeminorm_nonneg (c : TargetContext K) (eta : Finset (ℕ × ℕ)) :
    0 ≤ originalArchSeminorm c eta := apply_nonneg _ _

variable {p : SourceParameters c}

/-- The source equivalence transports every original column literally. -/
theorem first_index_mem (F : FirstPresentation call p) (hF : F.Realizes)
    (i : F.source.Column) (hi : i ∈ F.source.columns) :
    F.index i ∈ call.workingRaw.exteriorColumns := by
  rw [← hF.columns]
  exact Finset.mem_map.mpr ⟨i, hi, rfl⟩

theorem first_coefficient_norm_le (input : ProfileInput call)
    (horders : {(0, 0)} ⊆ input.orders)
    (F : FirstPresentation call p) (hF : F.Realizes)
    (i : F.source.Column) (hi : i ∈ F.source.columns) :
    ‖F.coefficient i‖ ≤
      (2 * input.amplitude ^ (c.geometry.slots + 2)) *
        call.base ^ (-(call.workingParameters.n₁ + call.workingParameters.n₂ +
          call.workingParameters.z) / 2) :=
  working_coefficient_norm_le input horders (F.index i) (first_index_mem F hF i hi)

/-- The same original Gram profile has arbitrary finite mixed orders.
Only its two scalar coefficients depend on the actual input. -/
theorem first_original_profile_seminorm_le (input : ProfileInput call)
    (horders : {(0, 0)} ⊆ input.orders)
    (F : FirstPresentation call p) (hF : F.Realizes) (eta : Finset (ℕ × ℕ))
    (i j : F.source.Column) (hi : i ∈ F.source.columns) (hj : j ∈ F.source.columns) :
    eta.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
        (F.originalProfile i j) ≤
      4 * originalArchSeminorm c eta * input.amplitude ^ (2 * (c.geometry.slots + 2)) *
        call.base ^ (-(call.workingParameters.n₁ + call.workingParameters.n₂ +
          call.workingParameters.z)) := by
  let total := call.workingParameters.n₁ + call.workingParameters.n₂ +
    call.workingParameters.z
  let bound := (2 * input.amplitude ^ (c.geometry.slots + 2)) *
    call.base ^ (-total / 2)
  have hbound : 0 ≤ bound :=
    mul_nonneg (mul_nonneg (by norm_num)
      (pow_nonneg (zero_le_one.trans input.amplitude_one_le) _))
      (Real.rpow_nonneg call.base_pos.le _)
  have hi' : ‖F.coefficient i‖ ≤ bound := first_coefficient_norm_le input horders F hF i hi
  have hj' : ‖F.coefficient j‖ ≤ bound := first_coefficient_norm_le input horders F hF j hj
  have hamp : input.amplitude ^ (c.geometry.slots + 2) *
      input.amplitude ^ (c.geometry.slots + 2) =
      input.amplitude ^ (2 * (c.geometry.slots + 2)) := by
    simpa only [two_mul] using
      (pow_add input.amplitude (c.geometry.slots + 2) (c.geometry.slots + 2)).symm
  have hscale : call.base ^ (-total / 2) * call.base ^ (-total / 2) =
      call.base ^ (-total) := by
    rw [← Real.rpow_add call.base_pos]
    congr 1
    ring
  rw [FirstPresentation.originalProfile, map_smul_eq_mul, norm_mul, norm_star]
  change ‖F.coefficient i‖ * ‖F.coefficient j‖ * originalArchSeminorm c eta ≤ _
  calc
    _ ≤ bound * bound * originalArchSeminorm c eta :=
      mul_le_mul_of_nonneg_right (mul_le_mul hi' hj' (norm_nonneg _) hbound)
        (originalArchSeminorm_nonneg c eta)
    _ = 4 * originalArchSeminorm c eta *
        (input.amplitude ^ (c.geometry.slots + 2) * input.amplitude ^ (c.geometry.slots + 2)) *
        (call.base ^ (-total / 2) * call.base ^ (-total / 2)) := by
      dsimp only [bound]
      ring
    _ = _ := by rw [hamp, hscale]

/-- The realization equality identifies the actual source profiles;
the source is neither redefined nor replaced by a comparison family. -/
theorem first_source_profile_seminorm_le (input : ProfileInput call)
    (horders : {(0, 0)} ⊆ input.orders)
    (F : FirstPresentation call p) (hF : F.Realizes) (eta : Finset (ℕ × ℕ))
    (i j : F.source.Column) (hi : i ∈ F.source.columns) (hj : j ∈ F.source.columns) :
    eta.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
        (F.source.profiles i j) ≤
      4 * originalArchSeminorm c eta * input.amplitude ^ (2 * (c.geometry.slots + 2)) *
        call.base ^ (-(call.workingParameters.n₁ + call.workingParameters.n₂ +
          call.workingParameters.z)) := by
  rw [hF.profile]
  exact first_original_profile_seminorm_le input horders F hF eta i j hi hj

/-- The fixed annulus threshold gives a sharp whole-column window
on the support of the actual centered coefficient. -/
theorem working_active_column_norm_le (frame : SourceFrame) (input : ProfileInput call)
    (hframe : call.frame = frame) (loss : ℝ)
    (hannulusZ : uniformAnnulus c frame ^ (c.geometry.slots + 2) ≤ call.base ^ loss)
    (v : call.workingRaw.Column) (hv : v ∈ call.workingRaw.exteriorColumns)
    (hcoefficient : call.workingValues.coefficient call.node.centered v ≠ 0) :
    (Ideal.absNorm (call.workingRaw.columnExterior v).val : ℝ) ≤
      call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
        call.workingParameters.z + loss) := by
  have hcap : call.localizedData.geometry.slotCount ≤ c.geometry.slots := call.slots_le
  have hbound := original_active_column_norm_le_power
    (A := Arithmetic.data c) (Γ := Arithmetic.unitSubgroup c)
    call.workingAtoms input.localized c.geometry.slots (uniformAnnulus c frame) loss
    (uniformAnnulus_one_le c frame) hcap hannulusZ call.base_pos
    (fun _ _ => Set.mem_univ _) (Set.mem_univ _)
    (window_subset_uniformAnnulus frame call input hframe)
    call.node.centered (fun _ => working_comparison₁_scale_nonneg call)
    (fun _ => working_comparison_product call) v hv hcoefficient
  simpa only [working_total_length call] using hbound

theorem first_active_column_norm_le (frame : SourceFrame) (input : ProfileInput call)
    (hframe : call.frame = frame) (loss : ℝ)
    (hannulusZ : uniformAnnulus c frame ^ (c.geometry.slots + 2) ≤ call.base ^ loss)
    (F : FirstPresentation call p) (hF : F.Realizes)
    (i : F.source.Column) (hi : i ∈ F.source.columns) (hcoefficient : F.coefficient i ≠ 0) :
    (Ideal.absNorm (F.source.ideal i).val : ℝ) ≤
      call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
        call.workingParameters.z + loss) := by
  rw [hF.ideal i]
  exact working_active_column_norm_le frame input hframe loss hannulusZ
    (F.index i) (first_index_mem F hF i hi) hcoefficient

/-- Nonzero original profiles force both original coefficients to be
nonzero. The full Cartesian carrier remains the source carrier. -/
theorem first_active_pair_norm_le (frame : SourceFrame) (input : ProfileInput call)
    (hframe : call.frame = frame) (loss : ℝ)
    (hannulusZ : uniformAnnulus c frame ^ (c.geometry.slots + 2) ≤ call.base ^ loss)
    (F : FirstPresentation call p) (hF : F.Realizes)
    (ij : F.source.Column × F.source.Column)
    (hij : ij ∈ F.source.columns ×ˢ F.source.columns)
    (hprofile : F.source.profiles ij.1 ij.2 ≠ 0) :
    (Ideal.absNorm ((F.source.ideal ij.1).val * (F.source.ideal ij.2).val) : ℝ) ≤
      call.base ^ (2 * (call.workingParameters.n₁ + call.workingParameters.n₂ +
        call.workingParameters.z + loss)) := by
  have hleft : F.coefficient ij.1 ≠ 0 := by
    intro h
    apply hprofile
    rw [hF.profile, FirstPresentation.originalProfile, h, zero_mul, zero_smul]
  have hright : F.coefficient ij.2 ≠ 0 := by
    intro h
    apply hprofile
    rw [hF.profile, FirstPresentation.originalProfile, h, star_zero, mul_zero, zero_smul]
  have hi := first_active_column_norm_le frame input hframe loss hannulusZ F hF
    ij.1 (Finset.mem_product.mp hij).1 hleft
  have hj := first_active_column_norm_le frame input hframe loss hannulusZ F hF
    ij.2 (Finset.mem_product.mp hij).2 hright
  rw [map_mul, Nat.cast_mul]
  exact (mul_le_mul hi hj (Nat.cast_nonneg _) (Real.rpow_nonneg call.base_pos.le _)).trans_eq
    (by rw [← Real.rpow_add call.base_pos]; congr 1; ring)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstZeroProof

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstZeroProof.working_coefficient_norm_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstZeroProof.first_source_profile_seminorm_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstZeroProof.first_active_pair_norm_le
