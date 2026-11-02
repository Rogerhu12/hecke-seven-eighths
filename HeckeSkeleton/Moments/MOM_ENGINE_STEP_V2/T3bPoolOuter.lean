import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bOuterWeights
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondCommonIndexSwap

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original amplifier prefactor and selected first allowance

The main pool length and each error's moving prime power are precisely
the factors already present in the N8a index. They are transferred once
from the nominal allowance to that same original index prefactor.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum CommonSupportMass

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

namespace T3b

theorem firstActiveRadical_swap (I J : Ideal (𝓞 K))
    (hs : primeSupport I = primeSupport J) :
    firstActiveRadical I J = firstActiveRadical J I := by
  unfold firstActiveRadical
  rw [hs]
  congr 1
  ext q
  simp only [Finset.mem_filter, ne_comm]

end T3b

namespace FirstCoordinates

def t3bAllowance (first : FirstCoordinates call) : ℝ :=
  call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z +
    call.workingParameters.q + idealLogLength call.base
      (firstActiveRadical first.selected.val first.opposite.val) +
    idealLogLength call.base first.complementary.val - idealLogLength call.base first.selected.val +
    firstAllowance (idealLogLength call.base first.selected.val)
      (idealLogLength call.base first.opposite.val)
      (idealLogLength call.base (firstActiveRadical first.selected.val first.opposite.val)))

def t3bScalarCoordinates (first : FirstCoordinates call) :=
  (first.selected.val, first.opposite.val, first.complementary.val, first.residualDivisor.val)

theorem t3bAllowance_pos (first : FirstCoordinates call) : 0 < first.t3bAllowance :=
  Real.rpow_pos_of_pos call.base_pos _

end FirstCoordinates

namespace FirstCauchyFamily

theorem t3b_selectedAllowance_eq (family : FirstCauchyFamily F) (hfamily : family.Realizes)
    (i : Fin family.count) :
    (family.source i).first.t3bAllowance = T3b.selectedAllowance F (family.index i) := by
  have hs := T3b.firstActiveRadical_swap (family.index i).1.val.1 (family.index i).1.val.2
    (F.source.block (family.index i).1).common_support_eq
  unfold FirstCoordinates.t3bAllowance T3b.selectedAllowance T3b.firstAllowanceTotal
    firstLeftAllowance firstRightAllowance
  rw [hfamily.selected i, hfamily.opposite i, hfamily.complementary i]
  split_ifs <;> simp only [← hs]

end FirstCauchyFamily

namespace PoolExpansion

def t3bFirstIndex (expansion : PoolExpansion family) : Fin expansion.count → Fin family.count :=
  match expansion with
  | .direct => id
  | .pooled _ _ index _ => fun i => (index i).1

theorem t3b_first_scalarCoordinates (expansion : PoolExpansion family)
    (hexpansion : expansion.Realizes) (i : Fin expansion.count) :
    (expansion.source i).first.t3bScalarCoordinates =
      (family.source (expansion.t3bFirstIndex i)).first.t3bScalarCoordinates := by
  cases expansion with
  | direct => rfl
  | pooled P count index source =>
    cases hi : (index i).2 with
    | inl u =>
      have ho : P.MainOrigin (index i).1 (source i) := by
        simpa only [PoolPresentation.Origin, hi] using hexpansion.2.2 i
      rcases ho with ⟨_, _, _, _, _, _, _, hf⟩
      change (source i).first.t3bScalarCoordinates = _
      rw [hf]
      rfl
    | inr qe =>
      have ho : P.ErrorOrigin (index i).1 qe.1 qe.2 (source i) := by
        simpa only [PoolPresentation.Origin, hi] using hexpansion.2.2 i
      rcases ho with ⟨_, _, _, _, _, _, _, hs, ho, hc, hr, _, _, _, _, _, _, _⟩
      change ((source i).first.selected.val, (source i).first.opposite.val,
        (source i).first.complementary.val, (source i).first.residualDivisor.val) = _
      rw [hs, ho, hc, hr]
      rfl

theorem t3b_first_allowance (expansion : PoolExpansion family)
    (hexpansion : expansion.Realizes) (i : Fin expansion.count) :
    (expansion.source i).first.t3bAllowance =
      (family.source (expansion.t3bFirstIndex i)).first.t3bAllowance := by
  exact congrArg
    (fun x : Ideal (𝓞 K) × Ideal (𝓞 K) × Ideal (𝓞 K) × Ideal (𝓞 K) =>
      call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
        call.workingParameters.z + call.workingParameters.q +
        idealLogLength call.base (firstActiveRadical x.1 x.2.1) +
        idealLogLength call.base x.2.2.1 - idealLogLength call.base x.1 +
        firstAllowance (idealLogLength call.base x.1) (idealLogLength call.base x.2.1)
          (idealLogLength call.base (firstActiveRadical x.1 x.2.1))))
    (expansion.t3b_first_scalarCoordinates hexpansion i)

private theorem pool_outer_mul_of_eq {w w₀ a b x y : ℝ}
    (hw : w = w₀ * a * b) (hx : x = y) :
    w * x = w₀ * (a * (b * y)) := by
  exact (congrArg₂ (fun u v : ℝ => u * v) hw hx).trans
    ((mul_assoc (w₀ * a) b y).trans (mul_assoc w₀ a (b * y)))

theorem t3b_outer_poolAllowance (expansion : PoolExpansion family)
    (hfamily : family.Realizes) (hexpansion : expansion.Realizes) (i : Fin expansion.count) :
    (expansion.source i).outerWeight * call.base ^
        ((expansion.source i).first.tag.movingLength call.base +
          (expansion.source i).first.tag.poolLength (recipeInductionSigma c)) =
      (family.source (expansion.t3bFirstIndex i)).outerWeight * expansion.indexPrefactor i := by
  cases expansion with
  | direct =>
    change (family.source i).outerWeight * call.base ^
      ((family.source i).first.tag.movingLength call.base +
        (family.source i).first.tag.poolLength (recipeInductionSigma c)) =
      (family.source i).outerWeight * 1
    rw [hfamily.tag i]
    simp only [OriginalNominalTag.movingLength, OriginalNominalTag.poolLength,
      zero_add, Real.rpow_zero]
  | pooled P count index source =>
    let prefactor : Unit ⊕ (P.pool.primes × AmplifierValuation) → ℝ := fun label =>
      (4 / (P.data (index i).1).density) * (match label with
        | .inl _ => (P.data (index i).1).multiplicity *
            call.base ^ (recipeInductionSigma c / 3)
        | .inr qe => FirstGaussPoolData.localErrorWeight qe.1.val qe.2.multiplicity *
            Q qe.1.val ^ qe.2.movingMultiplicity)
    cases hi : (index i).2 with
    | inl u =>
      have ho : P.MainOrigin (index i).1 (source i) := by
        simpa only [PoolPresentation.Origin, hi] using hexpansion.2.2 i
      rcases ho with ⟨_, _, _, _, _, _, hout, hf⟩
      have htag : (source i).first.tag = OriginalNominalTag.main :=
        congrArg (fun first : FirstCoordinates call => first.tag) hf
      have hpow := (congrArg (fun tag : OriginalNominalTag K =>
        call.base ^ (tag.movingLength call.base + tag.poolLength (recipeInductionSigma c)))
          htag).trans
        (congrArg (fun exponent : ℝ => call.base ^ exponent)
          (zero_add (recipeInductionSigma c / 3)))
      have hproduct := pool_outer_mul_of_eq hout hpow
      have hpref := congrArg prefactor hi
      exact hproduct.trans (congrArg (fun z : ℝ =>
        (family.source (index i).1).outerWeight * z) hpref.symm)
    | inr qe =>
      have ho : P.ErrorOrigin (index i).1 qe.1 qe.2 (source i) := by
        simpa only [PoolPresentation.Origin, hi] using hexpansion.2.2 i
      rcases ho with ⟨_, _, _, _, _, _, hout, _, _, _, _, _, _, _, _, htag, _, _⟩
      have hp : call.base ^ ((qe.2.movingMultiplicity : ℝ) *
          idealLogLength call.base qe.1.val.val.asIdeal) = Q qe.1.val ^ qe.2.movingMultiplicity := by
        rw [mul_comm, Real.rpow_mul call.base_pos.le,
          rpow_idealLogLength call.base call.domain.scale _ qe.1.val.val.ne_bot,
          Real.rpow_natCast]
        rfl
      have hpow := (congrArg (fun tag : OriginalNominalTag K =>
        call.base ^ (tag.movingLength call.base + tag.poolLength (recipeInductionSigma c)))
          htag).trans
        ((congrArg (fun exponent : ℝ => call.base ^ exponent)
          (add_zero ((qe.2.movingMultiplicity : ℝ) *
            idealLogLength call.base qe.1.val.val.asIdeal))).trans hp)
      have hproduct := pool_outer_mul_of_eq hout hpow
      have hpref := congrArg prefactor hi
      exact hproduct.trans (congrArg (fun z : ℝ =>
        (family.source (index i).1).outerWeight * z) hpref.symm)

end PoolExpansion
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PoolExpansion.t3b_first_scalarCoordinates
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PoolExpansion.t3b_outer_poolAllowance
