import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsSecondEstimate
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsCauchyWeights
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsCauchyCounting
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsPoolTransport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsPoolScalar

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original source and its single pool satisfy the second tail budget

Every entry of the numerical budget is proved from original atom bounds,
actual first Cauchy indices and the exact main/error origins. This closes
the second truncation certificate without changing either cutoff or either
logarithmic kernel.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton.Global HeckePort.Moments
open HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

def secondPhysicalBudget (c : TargetContext K) (p : SourceParameters c) : PhysicalTailBudget where
  columnConstant := idealCountConstant K ^ (c.geometry.slots + 2)
  columnConstant_nonneg := pow_nonneg (zero_le_one.trans (one_le_idealCountConstant K)) _
  columnDegree := ((c.geometry.slots + 2 : ℕ) : ℝ) * originalColumnExponent c
  coefficientConstant := 2
  coefficientConstant_nonneg := by norm_num
  coefficientDegree := 7 * (recipeInductionSigma c / 3)
  profileDegree := c.geometry.slots + 2
  rowConstant := (2 * orbitRowConstant c) * idealCountConstant K
  rowConstant_nonneg := mul_nonneg
    (mul_nonneg (by norm_num) (orbitRowConstant_pos c).le)
    (zero_le_one.trans (one_le_idealCountConstant K))
  rowDegree := firstRowExponent c p + recipeInductionSigma c / 3
  outerConstant := firstOuterConstant c p * poolOuterFactor c p
  outerConstant_nonneg := mul_nonneg (orbitalFieldFactor_nonneg K) (poolOuterFactor_nonneg c p)
  outerDegree := firstOuterDegree c p
  kernelMass := firstFixedKernelMass c p
  kernelMass_nonneg := firstFixedKernelMass_nonneg c p
  retainedDegree := firstRowExponent c p
  lengthBound := carrierColumnExponent c

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

theorem first_family_active_polynomial
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hf : family.Realizes)
    (input : ProfileInput call) (hlarge : originalThreshold c call.frame ≤ call.base)
    (i : Fin family.count) :
    ((physicalActiveColumns (family.source i)).card : ℝ) ≤
      idealCountConstant K ^ (c.geometry.slots + 2) *
        call.base ^ (((c.geometry.slots + 2 : ℕ) : ℝ) * originalColumnExponent c) := by
  apply (first_family_activeColumns_card F hF family hf input hlarge i).trans_eq
  have hp : (call.base ^ originalColumnExponent c) ^ (c.geometry.slots + 2) =
      call.base ^ (((c.geometry.slots + 2 : ℕ) : ℝ) * originalColumnExponent c) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul call.base_pos.le]
    congr 1
    ring
  rw [mul_pow, hp]

theorem first_physical_budget
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hf : family.Realizes)
    (input : ProfileInput call) (horders : originalOrders ⊆ input.orders)
    (hlarge : originalThreshold c call.frame ≤ call.base) (i : Fin family.count) :
    (secondPhysicalBudget c p).Holds input (family.source i) := by
  have hs := (recipeInduction_budget (c := c)).1
  have hpool : 1 ≤ idealCountConstant K * call.base ^ (recipeInductionSigma c / 3) :=
    (one_le_idealCountConstant K).trans (le_mul_of_one_le_right
      (zero_le_one.trans (one_le_idealCountConstant K))
      (Real.one_le_rpow call.domain.scale.le (by linarith)))
  have hpower : 1 ≤ call.base ^ (7 * (recipeInductionSigma c / 3)) :=
    Real.one_le_rpow call.domain.scale.le (by linarith)
  refine {
    columns := first_family_active_polynomial F hF family hf input hlarge i
    coefficient := ?_
    rows := ?_
    outer := ?_
    kernel := ?_
    retained := first_family_retained_le F hF family hf input hlarge i
    activeLength := first_family_active_length_le F hF family hf input hlarge i
    complementaryLength := first_family_complementary_length_le F hF family hf input hlarge i }
  · intro j hj
    apply (first_family_coefficient_bound F hF family hf input horders i j hj).trans
    exact le_mul_of_one_le_right
      (mul_nonneg (by norm_num) (pow_nonneg (zero_le_one.trans input.amplitude_one_le) _)) hpower
  · calc
      _ ≤ 2 * orbitRowConstant c * call.base ^ firstRowExponent c p :=
        first_family_rows_card F hF family hf input hlarge i
      _ ≤ (2 * orbitRowConstant c * call.base ^ firstRowExponent c p) *
          (idealCountConstant K * call.base ^ (recipeInductionSigma c / 3)) :=
        le_mul_of_one_le_right
          (mul_nonneg (mul_nonneg (by norm_num) (orbitRowConstant_pos c).le)
            (Real.rpow_nonneg call.base_pos.le _)) hpool
      _ = _ := by
        change _ = ((2 * orbitRowConstant c) * idealCountConstant K) *
          call.base ^ (firstRowExponent c p + recipeInductionSigma c / 3)
        rw [Real.rpow_add call.base_pos]
        ring
  · calc
      _ ≤ firstOuterConstant c p * call.base ^ firstOuterDegree c p :=
        first_family_outer_le F hF family hf input hlarge i
      _ ≤ (firstOuterConstant c p * call.base ^ firstOuterDegree c p) * poolOuterFactor c p :=
        le_mul_of_one_le_right
          (mul_nonneg (orbitalFieldFactor_nonneg K) (Real.rpow_nonneg call.base_pos.le _))
          (poolOuterFactor_one_le c p)
      _ = _ := by change _ = (firstOuterConstant c p * poolOuterFactor c p) *
          call.base ^ firstOuterDegree c p; ring
  · rw [first_family_kernel_eq F hF family hf i]
    exact le_rfl

theorem pooled_physical_budget
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hf : family.Realizes)
    (input : ProfileInput call) (horders : originalOrders ⊆ input.orders)
    (hlarge : originalThreshold c call.frame ≤ call.base)
    (hfirstWindows : ∀ i, (family.source i).Windows)
    (P : PoolPresentation family) (hP : P.Realizes)
    (index : P.Index) (source : PhysicalSource call p) (horigin : P.Origin index source) :
    (secondPhysicalBudget c p).Holds input source := by
  obtain ⟨hkernel, hretained, hselected, hopposite, hcomplementary⟩ :=
    pool_origin_coordinates P index source horigin
  have hrowDegree := first_family_rowExponent_le F hF family hf input hlarge
    index.1 (hfirstWindows index.1)
  have houter := pool_origin_outer_le P hP index source horigin hrowDegree
  have hcount := pool_origin_active_card P hP index source horigin
  have hrow := pool_origin_row_card P hP index source horigin
  have hprimeCount : 1 ≤ P.pool.primes.card := by exact_mod_cast pool_card_one_le P
  have hrow' : (source.source.rows.card : ℝ) ≤
      ((family.source index.1).source.rows.card : ℝ) * (P.pool.primes.card : ℝ) := by
    rw [max_eq_right hprimeCount] at hrow
    exact_mod_cast hrow
  refine {
    columns := hcount.trans (first_family_active_polynomial F hF family hf input hlarge index.1)
    coefficient := pool_origin_coefficient_bound P hP index source horigin
      (2 * input.amplitude ^ (c.geometry.slots + 2))
      (mul_nonneg (by norm_num) (pow_nonneg (zero_le_one.trans input.amplitude_one_le) _))
      (first_family_coefficient_bound F hF family hf input horders index.1)
    rows := ?_
    outer := ?_
    kernel := ?_
    retained := ?_
    activeLength := ?_
    complementaryLength := ?_ }
  · calc
      _ ≤ ((family.source index.1).source.rows.card : ℝ) * (P.pool.primes.card : ℝ) := hrow'
      _ ≤ (2 * orbitRowConstant c * call.base ^ firstRowExponent c p) *
          (idealCountConstant K * call.base ^ (recipeInductionSigma c / 3)) :=
        mul_le_mul (first_family_rows_card F hF family hf input hlarge index.1)
          (pool_card_upper P) (Nat.cast_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num) (orbitRowConstant_pos c).le)
            (Real.rpow_nonneg call.base_pos.le _))
      _ = _ := by
        change _ = ((2 * orbitRowConstant c) * idealCountConstant K) *
          call.base ^ (firstRowExponent c p + recipeInductionSigma c / 3)
        rw [Real.rpow_add call.base_pos]
        ring
  · calc
      _ ≤ (family.source index.1).outerWeight * poolOuterFactor c p := houter
      _ ≤ (firstOuterConstant c p * call.base ^ firstOuterDegree c p) * poolOuterFactor c p :=
        mul_le_mul_of_nonneg_right
          (first_family_outer_le F hF family hf input hlarge index.1) (poolOuterFactor_nonneg c p)
      _ = _ := by change _ = (firstOuterConstant c p * poolOuterFactor c p) *
          call.base ^ firstOuterDegree c p; ring
  · rw [hkernel, first_family_kernel_eq F hF family hf index.1]
    exact le_rfl
  · rw [hretained]
    exact first_family_retained_le F hF family hf input hlarge index.1
  · rw [hselected, hopposite]
    exact first_family_active_length_le F hF family hf input hlarge index.1
  · rw [hcomplementary]
    exact first_family_complementary_length_le F hF family hf input hlarge index.1

theorem expansion_physical_budget
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hf : family.Realizes)
    (input : ProfileInput call) (horders : originalOrders ⊆ input.orders)
    (hlarge : originalThreshold c call.frame ≤ call.base)
    (hfirstWindows : ∀ i, (family.source i).Windows)
    (expansion : PoolExpansion family) (he : expansion.Realizes) :
    ∀ i, (secondPhysicalBudget c p).Holds input (expansion.source i) := by
  cases expansion with
  | direct =>
      exact first_physical_budget F hF family hf input horders hlarge
  | pooled P count index source =>
      intro i
      exact pooled_physical_budget F hF family hf input horders hlarge hfirstWindows
        P he.2.1 (index i) (source i) (he.2.2 i)

def secondFamilyCountConstant (c : TargetContext K) : ℝ :=
  (4 * idealCountConstant K) * firstFamilyCountConstant c

def secondFamilyCountDegree (c : TargetContext K) : ℝ :=
  firstFamilyCountDegree c + recipeInductionSigma c / 3

theorem secondFamilyCountConstant_nonneg (c : TargetContext K) :
    0 ≤ secondFamilyCountConstant c := by
  have hI := zero_le_one.trans (one_le_idealCountConstant K)
  dsimp only [secondFamilyCountConstant, firstFamilyCountConstant]
  positivity

theorem second_family_count_bound (input : ProfileInput call)
    (hlarge : originalThreshold c call.frame ≤ call.base)
    (trace : SourceTrace call p) (ht : trace.Realizes) :
    (trace.expansion.count : ℝ) ≤
      secondFamilyCountConstant c * call.base ^ secondFamilyCountDegree c := by
  have hcount := first_family_count_le trace.first ht.first trace.cauchy input hlarge
  calc
    _ ≤ (4 * idealCountConstant K) * (trace.cauchy.count : ℝ) *
        call.base ^ (recipeInductionSigma c / 3) := expansion_count_le trace.expansion
    _ ≤ (4 * idealCountConstant K) *
        (firstFamilyCountConstant c * call.base ^ firstFamilyCountDegree c) *
          call.base ^ (recipeInductionSigma c / 3) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcount
          (mul_nonneg (by norm_num) (zero_le_one.trans (one_le_idealCountConstant K))))
        (Real.rpow_nonneg call.base_pos.le _)
    _ = _ := by
      simp only [secondFamilyCountConstant, secondFamilyCountDegree, Real.rpow_add call.base_pos]
      ring

theorem exists_secondTailCertificate (c : TargetContext K) (frame : SourceFrame)
    (p : SourceParameters c) : Nonempty (SecondTailCertificate c frame p) := by
  apply secondTailCertificate_of_physical_bounds c frame p (secondPhysicalBudget c p)
    (secondFamilyCountConstant c) (secondFamilyCountDegree c) (secondFamilyCountConstant_nonneg c)
  · intro call input hframe horders hlarge trace ht i
    rw [ht.second.physical i]
    exact expansion_physical_budget trace.first ht.first trace.cauchy ht.cauchy
      input horders hlarge ht.firstWindows trace.expansion ht.expansion i
  · intro call input hframe horders hlarge trace ht
    exact second_family_count_bound input hlarge trace ht

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.exists_secondTailCertificate
