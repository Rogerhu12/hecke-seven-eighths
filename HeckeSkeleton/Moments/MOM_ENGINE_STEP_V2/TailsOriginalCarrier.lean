import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsOriginalBounds
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ActiveChildAnnulus
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentOriginalAtlas

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The complete original carrier after comparison normalization

The ordinary unused comparison windows are now the main windows.
The support argument applies also to zero coefficients and therefore
bounds every literal finite Cauchy label. Its fixed exponent is allowed
to depend on the original slot cap. The scalar support argument follows
the independent S3 carrier calculation.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

private theorem carrier_ideal_support_norm_le (W : IdealTest K) (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (t N Z A lo hi : ℝ) (hN : 0 < N) (hZ : 0 < Z)
    (hscale : N ≤ Z ^ A) (hupper : hi ≤ Z)
    (hsupport : Function.support (W.profile u t) ⊆ Set.Icc lo hi)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) (hI : I ∈ W.support u t N) :
    idealNorm K I ≤ Z ^ (A + 1) := by
  have hr := (hsupport ((W.support_spec u t N I).mp hI)).2.trans hupper
  have hn : idealNorm K I ≤ Z * N := (div_le_iff₀ hN).mp hr
  calc
    idealNorm K I ≤ Z * N := hn
    _ ≤ Z * Z ^ A := mul_le_mul_of_nonneg_left hscale hZ.le
    _ = Z ^ (A + 1) := by rw [Real.rpow_add hZ, Real.rpow_one]; ring

private theorem carrier_plain_carrier_norm_le
    (rows : Finset (HeckeGeneral.Analysis.NonzeroIdeal K)) (W : IdealTest K)
    (t X Y Z A lo hi : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (hscaleX : X ≤ Z ^ A) (hscaleY : Y ≤ Z ^ A) (hupper : hi ≤ Z)
    (hsupport : ∀ u, Function.support (W.profile u t) ⊆ Set.Icc lo hi)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) (hI : I ∈ parentPlainCarrier rows W t X Y) :
    idealNorm K I ≤ Z ^ (A + 1) := by
  obtain ⟨u, _, hI⟩ := Finset.mem_biUnion.mp hI
  rcases Finset.mem_union.mp hI with hI | hI
  · exact carrier_ideal_support_norm_le W u t X Z A lo hi hX hZ hscaleX hupper (hsupport u) I hI
  · exact carrier_ideal_support_norm_le W u t Y Z A lo hi hY hZ hscaleY hupper (hsupport u) I hI

theorem carrier_raw_column_norm_le
    {Adata : SArithmeticData K} {Γ : Subgroup Adata.U}
    {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ} {a : RealParameters}
    {Z t Y₁ Y₂ lo hi A : ℝ}
    (raw : ParentRawAtoms
      (SIntegerOrbits K (Adata.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) d a Z t Y₁ Y₂)
    (profiles : ActiveChildAnnulus.ProfileSupport Set.univ Set.univ (Set.Icc lo hi) d)
    (hZ : 0 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hn₁ : Z ^ a.n₁ ≤ Z ^ A) (hn₂ : Z ^ a.n₂ ≤ Z ^ A)
    (hcomp₁ : Y₁ ≤ Z ^ A) (hcomp₂ : Y₂ ≤ Z ^ A) (hupper : hi ≤ Z)
    (v : raw.Column) (hv : v ∈ raw.exteriorColumns) :
    Adata.exteriorNorm (raw.columnExterior v) ≤
      Z ^ (2 * (A + 1) + d.geometry.totalLength + d.geometry.slotCount) := by
  have hmem := (Finset.mem_filter.mp hv).1
  change v ∈ (raw.leftColumns.product raw.rightColumns).product
    (Fintype.piFinset raw.slotColumns) at hmem
  have hprod := Finset.mem_product.mp hmem
  have hplain := Finset.mem_product.mp hprod.1
  have hleft : idealNorm K v.1.1 ≤ Z ^ (A + 1) :=
    carrier_plain_carrier_norm_le (pairedRows d a Z) d.plainTest₁ t (Z ^ a.n₁) Y₁ Z A lo hi
      (Real.rpow_pos_of_pos hZ _) hY₁ hZ hn₁ hcomp₁ hupper
      (fun u => profiles.left u (Set.mem_univ _) t (Set.mem_univ _)) v.1.1 hplain.1
  have hright : idealNorm K v.1.2 ≤ Z ^ (A + 1) :=
    carrier_plain_carrier_norm_le (pairedRows d a Z) d.plainTest₂ t (Z ^ a.n₂) Y₂ Z A lo hi
      (Real.rpow_pos_of_pos hZ _) hY₂ hZ hn₂ hcomp₂ hupper
      (fun u => profiles.right u (Set.mem_univ _) t (Set.mem_univ _)) v.1.2 hplain.2
  have hslot (i : Fin d.geometry.slotCount) :
      (Ideal.absNorm (v.2 i).asIdeal : ℝ) ≤ Z ^ ((d.geometry.slots i).length + 1) := by
    have hi := Fintype.mem_piFinset.mp hprod.2 i
    have hne := ((d.geometry.slots i).support_spec t
      (Z ^ (d.geometry.slots i).length) (v.2 i)).mp hi
    have hw := (profiles.prime i t (Set.mem_univ _) hne).2.trans hupper
    have hn := (div_le_iff₀ (Real.rpow_pos_of_pos hZ (d.geometry.slots i).length)).mp hw
    calc
      (Ideal.absNorm (v.2 i).asIdeal : ℝ) ≤ Z * Z ^ (d.geometry.slots i).length := hn
      _ = Z ^ ((d.geometry.slots i).length + 1) := by
        rw [Real.rpow_add hZ, Real.rpow_one]; ring
  have hslots : (∏ i, (Ideal.absNorm (v.2 i).asIdeal : ℝ)) ≤
      Z ^ (d.geometry.totalLength + d.geometry.slotCount) := by
    calc
      (∏ i, (Ideal.absNorm (v.2 i).asIdeal : ℝ)) ≤
          ∏ i, Z ^ ((d.geometry.slots i).length + 1) :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => hslot i)
      _ = Z ^ (d.geometry.totalLength + d.geometry.slotCount) := by
        rw [← Real.rpow_sum_of_pos hZ]
        congr 1
        simp [SlotGeometry.totalLength, Finset.sum_add_distrib]
  have hplainProd : idealNorm K v.1.1 * idealNorm K v.1.2 ≤ Z ^ (2 * (A + 1)) := by
    calc
      idealNorm K v.1.1 * idealNorm K v.1.2 ≤ Z ^ (A + 1) * Z ^ (A + 1) :=
        mul_le_mul hleft hright (idealNorm_pos K v.1.2).le (Real.rpow_pos_of_pos hZ _).le
      _ = Z ^ (2 * (A + 1)) := by rw [← Real.rpow_add hZ]; congr 1; ring
  change (Ideal.absNorm (raw.columnExterior v).val : ℝ) ≤ _
  rw [raw.columnExterior_val_of_mem v hv]
  simp only [ParentRawAtoms.columnIdeal, map_mul, map_prod, Nat.cast_mul, Nat.cast_prod]
  change idealNorm K v.1.1 * idealNorm K v.1.2 *
    (∏ i, (Ideal.absNorm (v.2 i).asIdeal : ℝ)) ≤ _
  calc
    _ ≤ Z ^ (2 * (A + 1)) * Z ^ (d.geometry.totalLength + d.geometry.slotCount) :=
      mul_le_mul hplainProd hslots (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
        (Real.rpow_pos_of_pos hZ _).le
    _ = Z ^ (2 * (A + 1) + d.geometry.totalLength + d.geometry.slotCount) := by
      rw [← Real.rpow_add hZ]; congr 1; ring

def carrierColumnCore (c : TargetContext K) : ℝ := 2 + recipeInductionSigma c / 16

def carrierColumnExponent (c : TargetContext K) : ℝ :=
  3 * carrierColumnCore c + c.geometry.slots + 2

theorem carrier_parameter_bounds {c : TargetContext K} (call : Call c) :
    call.node.parameters.n₁ ≤ carrierColumnCore c ∧
    call.node.parameters.n₂ ≤ carrierColumnCore c ∧
    call.node.parameters.z ≤ carrierColumnCore c := by
  have hz : 0 ≤ call.node.parameters.z := by
    rw [call.domain.total_length]
    exact Finset.sum_nonneg (fun i _ => (call.node.data.geometry.slots i).length_pos.le)
  have hp := call.domain.padded_core
  have hw := call.width_le
  have hn₁ := call.domain.plain_left_nonneg
  have hn₂ := call.domain.plain_right_nonneg
  dsimp [carrierColumnCore]
  constructor
  · linarith
  constructor <;> linarith

theorem carrier_comparison_bounds {c : TargetContext K} (call : Call c) :
    call.base ^ call.workingComparison₁ ≤ call.base ^ carrierColumnCore c ∧
    call.base ^ call.workingComparison₂ ≤ call.base ^ carrierColumnCore c := by
  have hparams := carrier_parameter_bounds call
  cases hc : call.node.centered with
  | false =>
      simp only [Call.workingComparison₁, Call.workingComparison₂, hc, Bool.false_eq_true,
        ↓reduceIte]
      exact ⟨Real.rpow_le_rpow_of_exponent_le call.domain.scale.le hparams.1,
        Real.rpow_le_rpow_of_exponent_le call.domain.scale.le hparams.2.1⟩
  | true =>
      simp only [Call.workingComparison₁, Call.workingComparison₂, hc, ↓reduceIte]
      rw [call.domain.comparison_left hc, call.domain.comparison_right hc]
      have hz : 0 ≤ call.node.parameters.z := by
        rw [call.domain.total_length]
        exact Finset.sum_nonneg (fun i _ => (call.node.data.geometry.slots i).length_pos.le)
      have hp := call.domain.padded_core
      have hw := call.width_le
      have hw0 := call.domain.width_nonneg
      have hs := (recipeInduction_budget (c := c)).1
      constructor <;> apply Real.rpow_le_rpow_of_exponent_le call.domain.scale.le <;>
        dsimp [carrierColumnCore] <;> linarith

theorem carrierColumnExponent_nonneg (c : TargetContext K) :
    0 ≤ carrierColumnExponent c := by
  have hs := (recipeInduction_budget (c := c)).1
  dsimp [carrierColumnExponent, carrierColumnCore]
  positivity

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

theorem original_carrier_window_upper (input : ProfileInput call)
    (hlarge : originalThreshold c call.frame ≤ call.base) :
    2 * call.prepared.upper ≤ call.base := by
  have hA : originalAnnulus c call.frame ≤ originalThreshold c call.frame := by
    simpa only [originalThreshold, pow_one] using
      pow_le_pow_right₀ (originalAnnulus_one_le c call.frame)
        (show 1 ≤ c.geometry.slots + 2 by omega)
  have hu : call.prepared.upper ≤ call.frame.upper * (2 : ℝ) ^ call.rankBound := by
    rw [input.regular.upper]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num)
        (Nat.sub_le call.rankBound call.rank))
      (by linarith [call.frame.upper_large])
  exact (mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℝ) ≤ 2)).trans
    ((le_max_right _ _).trans (hA.trans hlarge))

theorem original_carrier_ideal_norm_le (input : ProfileInput call)
    (hlarge : originalThreshold c call.frame ≤ call.base)
    (j : call.workingRaw.Column) (hj : j ∈ call.workingRaw.exteriorColumns) :
    (Arithmetic.data c).exteriorNorm (call.workingRaw.columnExterior j) ≤
      call.base ^ carrierColumnExponent c := by
  have hparams := carrier_parameter_bounds call
  have hcomparison := carrier_comparison_bounds call
  have hraw := carrier_raw_column_norm_le (Adata := Arithmetic.data c)
    (A := carrierColumnCore c) call.workingRaw
    (ActiveChildAnnulus.rawWindow_support input.localized)
    call.base_pos (Real.rpow_pos_of_pos call.base_pos _)
    (Real.rpow_pos_of_pos call.base_pos _)
    (Real.rpow_le_rpow_of_exponent_le call.domain.scale.le hparams.1)
    (Real.rpow_le_rpow_of_exponent_le call.domain.scale.le hparams.2.1)
    hcomparison.1 hcomparison.2 (original_carrier_window_upper input hlarge) j hj
  apply hraw.trans
  apply Real.rpow_le_rpow_of_exponent_le call.domain.scale.le
  have hslots : (call.node.data.geometry.slotCount : ℝ) ≤ c.geometry.slots :=
    Nat.cast_le.mpr call.slots_le
  change 2 * (carrierColumnCore c + 1) + call.node.data.geometry.totalLength +
    call.node.data.geometry.slotCount ≤ carrierColumnExponent c
  rw [← call.domain.total_length]
  dsimp [carrierColumnExponent]
  linarith [hparams.2.2]

theorem original_carrier_card (input : ProfileInput call)
    (hlarge : originalThreshold c call.frame ≤ call.base) :
    (call.workingRaw.exteriorColumns.card : ℝ) ≤
      (idealCountConstant K * call.base ^ carrierColumnExponent c) ^
        (c.geometry.slots + 2) := by
  apply whole_ideal_tuple_card call.workingRaw.exteriorColumns
    (call.workingRaw.paddedOriginalIdealFactors c.geometry.slots (working_slots_le call))
    (call.workingRaw.paddedOriginalIdealFactors_injective c.geometry.slots
      (working_slots_le call)).injOn
    (call.base ^ carrierColumnExponent c)
    (Real.one_le_rpow call.domain.scale.le (carrierColumnExponent_nonneg c))
  · intro j hj
    rw [call.workingRaw.paddedOriginalIdealFactors_product]
    exact call.workingRaw.columnIdeal_ne_zero j
  · intro j hj
    rw [call.workingRaw.paddedOriginalIdealFactors_product,
      ← call.workingRaw.columnExterior_val_of_mem j hj]
    exact original_carrier_ideal_norm_le input hlarge j hj

theorem first_ideal_norm_le_all (F : FirstPresentation call p) (hF : F.Realizes)
    (input : ProfileInput call) (hlarge : originalThreshold c call.frame ≤ call.base)
    (j : F.source.Column) (hj : j ∈ F.source.columns) :
    (Arithmetic.data c).exteriorNorm (F.source.ideal j) ≤
      call.base ^ carrierColumnExponent c := by
  rw [hF.ideal]
  exact original_carrier_ideal_norm_le input hlarge (F.index j) (first_index_mem F hF j hj)

theorem first_columns_card (F : FirstPresentation call p) (hF : F.Realizes)
    (input : ProfileInput call) (hlarge : originalThreshold c call.frame ≤ call.base) :
    (F.source.columns.card : ℝ) ≤
      (idealCountConstant K * call.base ^ carrierColumnExponent c) ^
        (c.geometry.slots + 2) := by
  have he : F.source.columns.card = call.workingRaw.exteriorColumns.card := by
    simpa only [Finset.card_map] using congrArg Finset.card hF.columns
  rw [he]
  exact original_carrier_card input hlarge

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.original_carrier_ideal_norm_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.first_columns_card

