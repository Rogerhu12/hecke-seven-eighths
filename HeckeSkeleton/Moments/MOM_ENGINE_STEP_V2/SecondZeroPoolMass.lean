import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondZeroFirstMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolTerminalMass

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The one original pool in the second zero estimate

The V2 main/valuation index is put in bijection with the existing four
literal pool branches. The original Fourier kernel, side allowance and
residual divisor are unchanged by this reindexing. The one density
factor is used exactly once in the finite mass estimate.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

local instance secondMassValuationFintype : Fintype AmplifierValuation where
  elems := {.one, .six, .seven}
  complete := by intro e; cases e <;> simp

section PoolTags

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}

/-- The three valuation constructors are the original 1, 6 and 7
branches, with the original prime in each branch. -/
def secondPoolTagEquiv (P : PowerScaleExteriorPool A bad Z ell eps) :
    (Unit ⊕ (P.primes × AmplifierValuation)) ≃ PoolSourceTag P where
  toFun
    | .inl u => .inl u
    | .inr (q, .one) => .inr (.inl q)
    | .inr (q, .six) => .inr (.inr (.inl q))
    | .inr (q, .seven) => .inr (.inr (.inr q))
  invFun
    | .inl u => .inl u
    | .inr (.inl q) => .inr (q, .one)
    | .inr (.inr (.inl q)) => .inr (q, .six)
    | .inr (.inr (.inr q)) => .inr (q, .seven)
  left_inv := by
    intro t
    rcases t with u | ⟨q, e⟩
    · rfl
    · cases e <;> rfl
  right_inv := by
    intro t
    rcases t with u | q | q | q <;> rfl

def secondPoolTagCharge (P : PowerScaleExteriorPool A bad Z ell eps)
    (t : Unit ⊕ (P.primes × AmplifierValuation)) : ℝ :=
  poolTagNormCharge P (secondPoolTagEquiv P t)

def secondPoolTagWeight {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}
    (d : FirstGaussPoolData C P ι) (t : Unit ⊕ (P.primes × AmplifierValuation)) : ℝ :=
  d.tagWeight (secondPoolTagEquiv P t)

theorem secondPoolTagCharge_nonneg (P : PowerScaleExteriorPool A bad Z ell eps)
    (t : Unit ⊕ (P.primes × AmplifierValuation)) : 0 ≤ secondPoolTagCharge P t :=
  poolTagNormCharge_nonneg (secondPoolTagEquiv P t)

theorem secondPoolTagCharge_one_le (P : PowerScaleExteriorPool A bad Z ell eps)
    (t : Unit ⊕ (P.primes × AmplifierValuation)) : 1 ≤ secondPoolTagCharge P t := by
  rcases t with u | ⟨q, e⟩
  · exact Real.one_le_rpow P.base_gt_one.le P.exponent_pos.le
  · have hq : 1 ≤ Q q.val := by
      change (1 : ℝ) ≤ (Ideal.absNorm q.val.val.asIdeal : ℝ)
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr q.val.val.ne_bot)
    cases e with
    | one =>
      simpa only [secondPoolTagCharge, secondPoolTagEquiv, Equiv.coe_fn_mk,
        poolTagNormCharge, amplifierMovingExponent, ite_true, pow_one] using hq
    | six =>
      norm_num [secondPoolTagCharge, secondPoolTagEquiv,
        poolTagNormCharge, amplifierMovingExponent]
    | seven =>
      simpa [secondPoolTagCharge, secondPoolTagEquiv,
        poolTagNormCharge, amplifierMovingExponent] using hq

theorem secondPoolTagWeight_nonneg {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}
    (d : FirstGaussPoolData C P ι) (t : Unit ⊕ (P.primes × AmplifierValuation)) :
    0 ≤ secondPoolTagWeight d t := d.tagWeight_nonneg _

theorem secondPoolTagWeight_error {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}
    (d : FirstGaussPoolData C P ι) (q : P.primes) (e : AmplifierValuation) :
    secondPoolTagWeight d (.inr (q, e)) =
      FirstGaussPoolData.localErrorWeight q.val e.multiplicity := by
  cases e <;> rfl

/-- The existing main plus 1/6/7 mass, on the exact V2 tag carrier. -/
theorem second_pool_tag_mass_le {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}
    (d : FirstGaussPoolData C P ι) (Mmax : ℝ) (hrow : d.rowExponent ≤ Mmax)
    (hlarge : 2 * (d.rowExponent / (ell / 2) + d.frozenExponent / (ell / 2)) ≤
      Z ^ (ell - eps)) :
    (4 / d.density) *
      (∑ t : Unit ⊕ (P.primes × AmplifierValuation),
        secondPoolTagWeight d t * secondPoolTagCharge P t) ≤
      poolTerminalConstant K ell Mmax * Z ^ eps := by
  have he : (∑ t : Unit ⊕ (P.primes × AmplifierValuation),
      secondPoolTagWeight d t * secondPoolTagCharge P t) =
      ∑ b : PoolSourceTag P, d.tagWeight b * poolTagNormCharge P b :=
    Fintype.sum_equiv (secondPoolTagEquiv P) _ _ (fun _ => rfl)
  rw [he]
  exact d.tag_norm_charge_mass_le Mmax hrow hlarge

end PoolTags

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

/-- The physical scalar that precedes the per-source second zero
bound. It includes the actual first measure and residual divisor. -/
def firstSourceMass (source : PhysicalSource call p) : ℝ :=
  source.outerWeight * (actualFourierMeasure source.firstKernel).real Set.univ *
    sourceSideAllowance source / (Ideal.absNorm source.first.residualDivisor.val : ℝ) /
    call.parentNormalizer

theorem firstSourceMass_nonneg (source : PhysicalSource call p) :
    0 ≤ firstSourceMass source := by
  have hallowance : 0 ≤ sourceSideAllowance source := Real.rpow_nonneg call.base_pos.le _
  exact div_nonneg (div_nonneg (mul_nonneg (mul_nonneg source.outerWeight_nonneg
    measureReal_nonneg) hallowance) (Nat.cast_nonneg _)) call.parentNormalizer_pos.le

theorem pool_main_firstSourceMass (P : PoolPresentation family) (i : Fin family.count)
    (source : PhysicalSource call p) (hsource : P.MainOrigin i source) :
    firstSourceMass source = firstSourceMass (family.source i) *
      (4 / (P.data i).density) * (P.data i).multiplicity := by
  rcases hsource with ⟨_, _, _, _, hkernel, _, houter, hfirst⟩
  have hallowance : sourceSideAllowance source = sourceSideAllowance (family.source i) := by
    rw [sourceSideAllowance, hfirst]
    rfl
  have hresidual : source.first.residualDivisor = (family.source i).first.residualDivisor := by
    rw [hfirst]
  rw [firstSourceMass, hkernel, houter, hallowance, hresidual]
  unfold firstSourceMass
  ring

theorem pool_error_firstSourceMass (P : PoolPresentation family) (i : Fin family.count)
    (q : P.pool.primes) (e : AmplifierValuation)
    (source : PhysicalSource call p) (hsource : P.ErrorOrigin i q e source) :
    firstSourceMass source = firstSourceMass (family.source i) *
      (4 / (P.data i).density) * FirstGaussPoolData.localErrorWeight q.val e.multiplicity := by
  rcases hsource with ⟨_, _, _, _, hkernel, _, houter, hselected, hopposite,
    hcomplementary, hresidual, _, _, _, _, _, _, _⟩
  have hallowance : sourceSideAllowance source = sourceSideAllowance (family.source i) := by
    simp only [sourceSideAllowance, hselected, hopposite, hcomplementary]
  rw [firstSourceMass, hkernel, houter, hallowance, hresidual]
  unfold firstSourceMass
  ring

theorem pool_origin_firstSourceMass (P : PoolPresentation family)
    (index : P.Index) (source : PhysicalSource call p) (hsource : P.Origin index source) :
    firstSourceMass source = firstSourceMass (family.source index.1) *
      (4 / (P.data index.1).density) * secondPoolTagWeight (P.data index.1) index.2 := by
  rcases index with ⟨i, t⟩
  rcases t with u | ⟨q, e⟩
  · exact pool_main_firstSourceMass P i source hsource
  · rw [secondPoolTagWeight_error]
    exact pool_error_firstSourceMass P i q e source hsource

/-- This is an equality on the original pooled source list. Neither
an extra density nor a different first Fourier kernel is introduced. -/
theorem pooled_firstSourceMass_sum (P : PoolPresentation family)
    (count : ℕ) (index : Fin count ≃ P.Index)
    (source : Fin count → PhysicalSource call p)
    (horigin : ∀ i, P.Origin (index i) (source i)) :
    (∑ i, firstSourceMass (source i) * secondPoolTagCharge P.pool (index i).2) =
      ∑ i, firstSourceMass (family.source i) * (4 / (P.data i).density) *
        ∑ t : Unit ⊕ (P.pool.primes × AmplifierValuation),
          secondPoolTagWeight (P.data i) t * secondPoolTagCharge P.pool t := by
  calc
    _ = ∑ i, (firstSourceMass (family.source (index i).1) * (4 / (P.data (index i).1).density) *
        secondPoolTagWeight (P.data (index i).1) (index i).2) *
        secondPoolTagCharge P.pool (index i).2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [pool_origin_firstSourceMass P (index i) (source i) (horigin i)]
    _ = ∑ j : P.Index, (firstSourceMass (family.source j.1) * (4 / (P.data j.1).density) *
        secondPoolTagWeight (P.data j.1) j.2) * secondPoolTagCharge P.pool j.2 :=
      Fintype.sum_equiv index _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring

theorem pooled_firstSourceMass_le (P : PoolPresentation family)
    (count : ℕ) (index : Fin count ≃ P.Index)
    (source : Fin count → PhysicalSource call p)
    (horigin : ∀ i, P.Origin (index i) (source i))
    (Mmax : ℝ) (hrow : ∀ i, (P.data i).rowExponent ≤ Mmax)
    (hlarge : ∀ i, 2 * ((P.data i).rowExponent / ((recipeInductionSigma c / 3) / 2) +
      (P.data i).frozenExponent / ((recipeInductionSigma c / 3) / 2)) ≤
        call.base ^ (recipeInductionSigma c / 3 - p.loss)) :
    (∑ i, firstSourceMass (source i) * secondPoolTagCharge P.pool (index i).2) ≤
      poolTerminalConstant K (recipeInductionSigma c / 3) Mmax * call.base ^ p.loss *
        ∑ i, firstSourceMass (family.source i) := by
  rw [pooled_firstSourceMass_sum P count index source horigin]
  calc
    _ ≤ ∑ i, firstSourceMass (family.source i) *
        (poolTerminalConstant K (recipeInductionSigma c / 3) Mmax * call.base ^ p.loss) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (second_pool_tag_mass_le (P.data i) Mmax (hrow i) (hlarge i))
        (firstSourceMass_nonneg (family.source i))
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- One threshold, selected before every moving call and every pool,
works for the original row and frozen-ideal exponent box. -/
theorem second_pool_mass_threshold (c : TargetContext K) (p : SourceParameters c)
    (Mmax Bmax : ℝ) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ {call : Call c}, Z₀ ≤ call.base →
      ∀ {F : FirstPresentation call p} {family : FirstCauchyFamily F}
        (P : PoolPresentation family),
      (∀ i, (P.data i).rowExponent ≤ Mmax) →
      (∀ i, (P.data i).frozenExponent ≤ Bmax) →
      ∀ i, 2 * ((P.data i).rowExponent / ((recipeInductionSigma c / 3) / 2) +
        (P.data i).frozenExponent / ((recipeInductionSigma c / 3) / 2)) ≤
        call.base ^ (recipeInductionSigma c / 3 - p.loss) := by
  have hsigma : 0 < recipeInductionSigma c := (recipeInduction_budget (c := c)).1
  have hexponent : 0 < recipeInductionSigma c / 3 - p.loss := by
    have hsmall := p.loss_small
    have hloss := p.loss_pos
    linarith
  have hevent := (_root_.tendsto_rpow_atTop hexponent).eventually
    (Filter.eventually_ge_atTop
      (2 * (Mmax / ((recipeInductionSigma c / 3) / 2) +
        Bmax / ((recipeInductionSigma c / 3) / 2))))
  obtain ⟨Z₁, hZ₁⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨max Z₁ 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro call hZ F family P hrow hfrozen i
  apply le_trans _ (hZ₁ call.base ((le_max_left _ _).trans hZ))
  exact mul_le_mul_of_nonneg_left
    (add_le_add (div_le_div_of_nonneg_right (hrow i) (by positivity))
      (div_le_div_of_nonneg_right (hfrozen i) (by positivity))) (by norm_num)

theorem original_tag_padding_le_twice (tag : OriginalNominalTag K)
    (step : ℝ) (hstep : 0 ≤ step) : tag.padding step ≤ 2 * step := by
  cases tag <;> simp only [OriginalNominalTag.padding] <;> linarith

/-- The literal padding of each actual main/error source is included
in the same finite sum. The tag norm charge is the one paid above. -/
theorem pooled_firstSourceMass_padding_le (P : PoolPresentation family)
    (count : ℕ) (index : Fin count ≃ P.Index)
    (source : Fin count → PhysicalSource call p)
    (horigin : ∀ i, P.Origin (index i) (source i))
    (Mmax : ℝ) (hrow : ∀ i, (P.data i).rowExponent ≤ Mmax)
    (hlarge : ∀ i, 2 * ((P.data i).rowExponent / ((recipeInductionSigma c / 3) / 2) +
      (P.data i).frozenExponent / ((recipeInductionSigma c / 3) / 2)) ≤
        call.base ^ (recipeInductionSigma c / 3 - p.loss)) :
    (∑ i, firstSourceMass (source i) *
      call.base ^ ((source i).first.tag.padding (recipeInductionSigma c))) ≤
      poolTerminalConstant K (recipeInductionSigma c / 3) Mmax *
        call.base ^ (2 * recipeInductionSigma c + p.loss) *
        ∑ i, firstSourceMass (family.source i) := by
  have hsigma : 0 ≤ recipeInductionSigma c := (recipeInduction_budget (c := c)).1.le
  calc
    _ ≤ ∑ i, firstSourceMass (source i) *
        (secondPoolTagCharge P.pool (index i).2 * call.base ^ (2 * recipeInductionSigma c)) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (firstSourceMass_nonneg (source i))
      apply (Real.rpow_le_rpow_of_exponent_le call.domain.scale.le
        (original_tag_padding_le_twice (source i).first.tag _ hsigma)).trans
      exact (one_mul _).symm.trans_le (mul_le_mul_of_nonneg_right
        (secondPoolTagCharge_one_le P.pool (index i).2)
        (Real.rpow_nonneg call.base_pos.le _))
    _ = (∑ i, firstSourceMass (source i) * secondPoolTagCharge P.pool (index i).2) *
        call.base ^ (2 * recipeInductionSigma c) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ (poolTerminalConstant K (recipeInductionSigma c / 3) Mmax * call.base ^ p.loss *
        ∑ i, firstSourceMass (family.source i)) * call.base ^ (2 * recipeInductionSigma c) :=
      mul_le_mul_of_nonneg_right (pooled_firstSourceMass_le P count index source horigin
        Mmax hrow hlarge) (Real.rpow_nonneg call.base_pos.le _)
    _ = _ := by rw [Real.rpow_add call.base_pos]; ring

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof
