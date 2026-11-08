module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S5GeometryConstruction
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstActiveDictionary

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The exact paid support of the original S5 class

The first active radical, actual complementary divisor and one pool
error power determine the paid support literally. Taking norms gives
the nominal support exponent before adding the positive window loss.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.S5Proof

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

theorem activeRadical_symm_of_support_eq (I J : Ideal (𝓞 K))
    (hsupport : primeSupport I = primeSupport J) :
    firstActiveRadical I J = firstActiveRadical J I := by
  unfold firstActiveRadical
  rw [hsupport]
  have hfilter :
      (primeSupport J).filter (fun P =>
        (UniqueFactorizationMonoid.normalizedFactors I).count P % 6 ≠
          (UniqueFactorizationMonoid.normalizedFactors J).count P % 6) =
      (primeSupport J).filter (fun P =>
        (UniqueFactorizationMonoid.normalizedFactors J).count P % 6 ≠
          (UniqueFactorizationMonoid.normalizedFactors I).count P % 6) := by
    apply Finset.filter_congr
    intro P hP
    exact ne_comm
  rw [hfilter]

def movingSupportIdeal (tag : OriginalNominalTag K) : Ideal (𝓞 K) :=
  match tag with
  | .direct | .main => 1
  | .error e q => q.asIdeal ^ e.movingMultiplicity

def paidSupportIdeal (first : FirstCoordinates call) : Ideal (𝓞 K) :=
  call.oldSupport.val * firstActiveRadical first.selected.val first.opposite.val *
    first.complementary.val * movingSupportIdeal first.tag

theorem cauchy_active_ideal {F : FirstPresentation call p}
    {family : FirstCauchyFamily F} (realized : family.Realizes) (i : Fin family.count) :
    (firstActiveIdeal (FirstCauchyKey.block (family.index i)).primes
      (FirstCauchyKey.block (family.index i)).leftMultiplicity
      (FirstCauchyKey.block (family.index i)).rightMultiplicity).val =
      firstActiveRadical (family.source i).first.selected.val
        (family.source i).first.opposite.val := by
  have he := (FirstCauchyKey.block (family.index i)).activeIdeal_eq
  have hs := (FirstCauchyKey.block (family.index i)).common_support_eq
  rw [realized.selected i, realized.opposite i]
  split_ifs
  · exact he.trans (activeRadical_symm_of_support_eq _ _ hs)
  · exact he

theorem cauchy_paid_support {F : FirstPresentation call p}
    {family : FirstCauchyFamily F} (realized : family.Realizes) (i : Fin family.count) :
    (family.source i).first.paidSupport.val = paidSupportIdeal (family.source i).first := by
  unfold paidSupportIdeal
  rw [realized.tag i, movingSupportIdeal, mul_one, realized.paid i,
    cauchy_active_ideal realized i]

theorem expansion_paid_support {F : FirstPresentation call p}
    {family : FirstCauchyFamily F} (realized : family.Realizes)
    (expansion : PoolExpansion family) (hexpansion : expansion.Realizes)
    (i : Fin expansion.count) :
    (expansion.source i).first.paidSupport.val =
      paidSupportIdeal (expansion.source i).first := by
  cases expansion with
  | direct => exact cauchy_paid_support realized i
  | pooled pool count index sources =>
    rcases hexpansion with ⟨_, _, horigin⟩
    have ho := horigin i
    change (sources i).first.paidSupport.val = paidSupportIdeal (sources i).first
    cases hk : (index i).2 with
    | inl unit =>
      simp only [PoolPresentation.Origin, hk] at ho
      rcases ho with ⟨_, _, _, _, _, _, _, hfirst⟩
      rw [hfirst]
      have hpaid := cauchy_paid_support realized (index i).1
      simpa only [paidSupportIdeal, realized.tag (index i).1,
        movingSupportIdeal, mul_one] using hpaid
    | inr qe =>
      simp only [PoolPresentation.Origin, hk] at ho
      rcases ho with ⟨_, _, _, _, _, _, _, hselected, hopposite, hcomplementary,
        _, _, _, _, _, htag, _, hpaid⟩
      unfold paidSupportIdeal
      rw [hpaid, hselected, hopposite, hcomplementary, htag, movingSupportIdeal]
      have hfirst := cauchy_paid_support realized (index i).1
      simpa only [paidSupportIdeal, realized.tag (index i).1,
        movingSupportIdeal, mul_one] using
        congrArg (fun I : Ideal (𝓞 K) => I * qe.1.val.val.asIdeal ^ qe.2.movingMultiplicity)
          hfirst

theorem source_paid_support (trace : SourceTrace call p) (realized : trace.Realizes)
    (key : SecondClassKey trace.second) :
    key.source.physical.first.paidSupport.val = paidSupportIdeal key.source.physical.first := by
  change (trace.second.source key.sourceIndex).physical.first.paidSupport.val =
    paidSupportIdeal (trace.second.source key.sourceIndex).physical.first
  rw [realized.second.physical key.sourceIndex]
  exact expansion_paid_support realized.cauchy trace.expansion realized.expansion key.sourceIndex

theorem movingSupportIdeal_norm (tag : OriginalNominalTag K) :
    (Ideal.absNorm (movingSupportIdeal tag) : ℝ) =
      call.base ^ tag.movingLength call.base := by
  cases tag with
  | direct => simp [movingSupportIdeal, OriginalNominalTag.movingLength]
  | main => simp [movingSupportIdeal, OriginalNominalTag.movingLength]
  | error e q =>
    change (Ideal.absNorm (q.asIdeal ^ e.movingMultiplicity) : ℝ) =
      call.base ^ ((e.movingMultiplicity : ℝ) * idealLogLength call.base q.asIdeal)
    rw [← idealLogLength_pow,
      rpow_idealLogLength call.base call.domain.scale _ (pow_ne_zero _ q.ne_bot)]

theorem paidSupport_norm (first : FirstCoordinates call)
    (hpaid : first.paidSupport.val = paidSupportIdeal first) :
    (Arithmetic.data c).exteriorNorm first.paidSupport =
      call.base ^ (call.workingParameters.q +
        idealLogLength call.base (firstActiveRadical first.selected.val first.opposite.val) +
        idealLogLength call.base first.complementary.val + first.tag.movingLength call.base) := by
  have hq : call.base ^ call.workingParameters.q =
      (Ideal.absNorm call.oldSupport.val : ℝ) :=
    rpow_idealLogLength call.base call.domain.scale call.oldSupport.val call.oldSupport.property.1
  change (Ideal.absNorm first.paidSupport.val : ℝ) = _
  rw [hpaid, paidSupportIdeal, map_mul, map_mul, map_mul,
    Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
    Real.rpow_add call.base_pos, Real.rpow_add call.base_pos,
    Real.rpow_add call.base_pos, hq,
    rpow_idealLogLength call.base call.domain.scale _
      (firstActiveRadical_ne_zero first.selected.val first.opposite.val),
    rpow_idealLogLength call.base call.domain.scale _
      (nonZeroDivisors.coe_ne_zero first.complementary), movingSupportIdeal_norm]

theorem classGeometry_supportWindow
    (trace : SourceTrace call p) (realized : trace.Realizes)
    (key : SecondClassKey trace.second) (active : key.Active) (side : Bool) :
    ((Arithmetic.data c).exteriorNorm key.source.physical.first.paidSupport) *
      (Ideal.absNorm ((classGeometry trace realized key active).nominal side).ideals.unitPart.val : ℝ) *
      (Ideal.absNorm ((classGeometry trace realized key active).nominal side).ideals.nonunitPart.val : ℝ) ≤
        call.base ^ (((classGeometry trace realized key active).nominal side).skeleton.nominalSupport +
          4 * p.loss) := by
  let G := (classGeometry trace realized key active).nominal side
  have hp := paidSupport_norm key.source.physical.first (source_paid_support trace realized key)
  have hformula :
      ((Arithmetic.data c).exteriorNorm key.source.physical.first.paidSupport) *
        (Ideal.absNorm G.ideals.unitPart.val : ℝ) *
        (Ideal.absNorm G.ideals.nonunitPart.val : ℝ) = call.base ^ G.skeleton.nominalSupport := by
    rw [hp]
    rw [← rpow_idealLogLength call.base call.domain.scale G.ideals.unitPart.val
      (nonZeroDivisors.coe_ne_zero G.ideals.unitPart),
      ← rpow_idealLogLength call.base call.domain.scale G.ideals.nonunitPart.val
        (nonZeroDivisors.coe_ne_zero G.ideals.nonunitPart),
      ← Real.rpow_add call.base_pos, ← Real.rpow_add call.base_pos]
    congr 1
    change _ = call.workingParameters.q +
      idealLogLength call.base (firstActiveRadical G.ideals.first.val G.ideals.opposite.val) +
      idealLogLength call.base G.ideals.complementary.val + G.tag.movingLength call.base +
      idealLogLength call.base G.ideals.unitPart.val + idealLogLength call.base G.ideals.nonunitPart.val
    rw [show G.ideals.first.val = _ from classGeometry_first trace realized key active side,
      show G.ideals.opposite.val = _ from classGeometry_opposite trace realized key active side,
      show G.ideals.complementary.val = _ from classGeometry_complementary trace realized key active side]
    rfl
  change _ ≤ call.base ^ (G.skeleton.nominalSupport + 4 * p.loss)
  rw [hformula]
  exact Real.rpow_le_rpow_of_exponent_le call.domain.scale.le
    (by linarith [p.loss_pos])

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.S5Proof

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S5Proof.classGeometry_supportWindow
