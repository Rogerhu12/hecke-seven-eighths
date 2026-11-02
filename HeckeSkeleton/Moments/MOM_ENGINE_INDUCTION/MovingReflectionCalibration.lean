import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RestorationRows
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.PrunedConductorModulus
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MovingRecipeConductor

/-!
# Ordinary reflection for the actual moving-row arithmetic

The calibration below retains a finite product of complete-ideal
characters, its original integer exponents, a single fixed correction,
and a displayed radical support. The q budget for that support and the
joint row/remaining budget are distinct fields. Neither is inferred
from equality of Boolean masks or from the full width alone.

The actual owner recipe constructs this calibration by its own factors,
sectors, support and full mask support. The correction belongs to one
fixed finite theta set chosen before the moving data. Conductors and
redundant deletions use a common modulus, so neither integer powers nor
the number of moving factors enlarges the norm exponent. The old bare
complete-row calibration remains available as the empty-factor case.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Arithmetic.ConductorNormDraft
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.HeckeConductorNorm HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum HeckePort.Moments.ReflectionMass
open HeckeSkeleton.ThetaKernel
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]
variable {omegaCharacter psiCharacter : HeckeCharacter K}

/-- All fixed correction/background possibilities are paid before the
moving row is selected. Multiplicative closure of theta is not assumed. -/
def movingReflectionConductorConstant
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (psiCharacter : HeckeCharacter K) (theta : Finset (HeckeCharacter K)) : ℝ :=
  ∑ gamma ∈ insert 1 theta,
    (reflectionConductorConstant S gamma +
      reflectionConductorConstant S (psiCharacter * gamma) +
        reflectionConductorConstant S (psiCharacter⁻¹ * gamma))

theorem reflectionConductorConstant_le_moving
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (psiCharacter : HeckeCharacter K) (theta : Finset (HeckeCharacter K))
    (beta gamma : HeckeCharacter K)
    (hbeta : beta = 1 ∨ beta = psiCharacter ∨ beta = psiCharacter⁻¹)
    (hgamma : gamma ∈ insert 1 theta) :
    reflectionConductorConstant S (beta * gamma) ≤
      movingReflectionConductorConstant S psiCharacter theta := by
  have hsum : reflectionConductorConstant S gamma +
      reflectionConductorConstant S (psiCharacter * gamma) +
        reflectionConductorConstant S (psiCharacter⁻¹ * gamma) ≤
      movingReflectionConductorConstant S psiCharacter theta := by
    apply Finset.single_le_sum _ hgamma
    intro eta _
    exact add_nonneg (add_nonneg (reflectionConductorConstant_pos S eta).le
      (reflectionConductorConstant_pos S (psiCharacter * eta)).le)
      (reflectionConductorConstant_pos S (psiCharacter⁻¹ * eta)).le
  have h1 := (reflectionConductorConstant_pos S gamma).le
  have h2 := (reflectionConductorConstant_pos S (psiCharacter * gamma)).le
  have h3 := (reflectionConductorConstant_pos S (psiCharacter⁻¹ * gamma)).le
  rcases hbeta with rfl | rfl | rfl
  · simp only [one_mul]
    linarith
  · linarith
  · linarith

theorem movingReflectionConductorConstant_pos
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (psiCharacter : HeckeCharacter K) (theta : Finset (HeckeCharacter K)) :
    0 < movingReflectionConductorConstant S psiCharacter theta := by
  have h := reflectionConductorConstant_le_moving S psiCharacter theta 1 1
    (Or.inl rfl) (Finset.mem_insert_self 1 theta)
  simp only [one_mul] at h
  exact (reflectionConductorConstant_pos S 1).trans_le h

/-- An arithmetic projection of a genuine moving recipe. The factors
are complete exterior ideals and their original sectors, not arbitrary
characters or phases. The displayed support and q budget are retained
independently of the joint row budget. -/
structure MovingReflectionRowCalibration
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (probe : ProbeData K S) (rows : RowCharacterInput K S probe)
    (theta : Finset (HeckeCharacter K))
    (node : Node K omegaCharacter psiCharacter)
    (extra : NonzeroIdeal K → NonzeroIdeal K) (U : ℝ) : Prop where
  identify : ∃ (count : ℕ) (factor : Fin count → ExteriorIdeal K S)
    (sector : Fin count → SixthUnitClasses K S) (power : Fin count → ℤ)
    (displayed : NonzeroIdeal K) (correction : HeckeCharacter K),
      correction ∈ insert 1 theta ∧
      (∀ i, (nonzeroIdealRadical K (factor i).val).val ∣ displayed.val) ∧
      idealNorm K displayed ≤ U ^ node.parameters.q ∧
      (∀ u ∈ pairedRows node.data node.parameters U, displayed.val ∣ (extra u).val) ∧
      ∀ u ∈ pairedRows node.data node.parameters U,
        ∃ v : ExteriorIdeal K S, v.val = u ∧ ∃ rowSector : SixthUnitClasses K S,
          node.data.rowCharacter u = correction *
            ((∏ i, completeIdealRowCharacter K S probe rows (sector i) (factor i).val ^ power i) *
              completeIdealRowCharacter K S probe rows rowSector u)
  product_budget : ∀ u ∈ pairedRows node.data node.parameters U,
    idealNorm K u * idealNorm K (extra u) ≤ U ^ node.width

/-- The old complete-row class is a proved empty-moving specialization.
The only additional hypothesis is its literal q-support inequality. -/
theorem ReflectionRowCalibration.toMoving
    {S : Set (HeightOneSpectrum (𝓞 K))} [Fintype S]
    {probe : ProbeData K S} {rows : RowCharacterInput K S probe}
    {node : Node K omegaCharacter psiCharacter}
    {extra : NonzeroIdeal K → NonzeroIdeal K} {U : ℝ}
    (cal : ReflectionRowCalibration S probe rows node extra U)
    (theta : Finset (HeckeCharacter K)) (hq : 1 ≤ U ^ node.parameters.q) :
    MovingReflectionRowCalibration S probe rows theta node extra U := by
  refine ⟨?_, cal.product_budget⟩
  refine ⟨0, (fun i => Fin.elim0 i), (fun i => Fin.elim0 i),
    (fun i => Fin.elim0 i), 1, 1, Finset.mem_insert_self 1 theta,
    (fun i => Fin.elim0 i), ?_, ?_, ?_⟩
  · have hone : idealNorm K (1 : NonzeroIdeal K) = 1 := by
      change (Ideal.absNorm (1 : Ideal (𝓞 K)) : ℝ) = 1
      simp only [map_one, Nat.cast_one]
    simpa only [hone] using hq
  · intro u hu
    exact one_dvd _
  · intro u hu
    obtain ⟨v, hv, sector, hrow⟩ := cal.identify u hu
    refine ⟨v, hv, sector, ?_⟩
    simpa only [Finset.univ_eq_empty, Finset.prod_empty, one_mul] using hrow

/-- This constructor uses the actual owner factors and the same full
mask support named in its joint budget. No estimate is inferred merely
from the effective mask equality. The root may supply the budget just
on its actual paired rows; canonical child FullJointBudget is stronger. -/
theorem movingReflectionCalibration_of_recipe
    {A : DedekindZetaZeroFree.SArithmeticData K}
    {probe : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
    {rows : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) probe}
    (node : Node K omegaCharacter psiCharacter)
    (recipe : EngineStep.CompleteMovingRowRecipe A probe rows
      (fun _ : PUnit => node.data))
    (theta : Finset (HeckeCharacter K)) (htheta : node.data.theta ⊆ theta)
    (U : ℝ) (hsupport : recipe.SupportBudget U node.parameters.q)
    (hjoint : ∀ u ∈ pairedRows node.data node.parameters U,
      idealNorm K u * idealNorm K (recipe.moving.fullMaskSupport recipe.remaining) ≤
        U ^ node.width) :
    MovingReflectionRowCalibration (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      probe rows theta node (fun _ => recipe.moving.fullMaskSupport recipe.remaining) U := by
  refine ⟨?_, hjoint⟩
  let support : NonzeroIdeal K := ⟨recipe.moving.support.val,
    mem_nonZeroDivisors_of_ne_zero recipe.moving.support.property.1⟩
  refine ⟨recipe.moving.count, (fun i => (recipe.moving.decomposition i).1),
    (fun i => (recipe.moving.decomposition i).2), recipe.moving.power,
    support, recipe.correction, ?_, ?_, ?_, ?_, ?_⟩
  · rcases recipe.correction_mem PUnit.unit with h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert.mpr (Or.inr (htheta h))
  · exact MovingRecipe.factor_radical_dvd_support recipe.moving
  · exact hsupport
  · intro u hu
    exact recipe.moving.support_dvd_fullMaskSupport recipe.remaining
  · intro u hu
    have hallowed := (node.data.rows_spec _ u).mp (Finset.mem_filter.mp hu).1
    refine ⟨⟨u, recipe.exterior PUnit.unit u hallowed.1⟩, rfl,
      recipe.sector u, ?_⟩
    rw [recipe.character PUnit.unit u hallowed.1,
      MovingRecipe.character_eq_complete_product]
    simp only [mul_assoc]

private theorem actualConductorScale_one_le (chi : HeckeCharacter K) :
    1 ≤ heckeConductorScale K chi := by
  have hd : (1 : ℝ) ≤ ((NumberField.discr K).natAbs : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Int.natAbs_pos.mpr (NumberField.discr_ne_zero K))
  have hc : (1 : ℝ) ≤ (Ideal.absNorm (finiteConductor K chi).val : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr
      (Ideal.absNorm_pos_of_nonZeroDivisors (finiteConductor K chi))
  change 1 ≤ ((NumberField.discr K).natAbs : ℝ) *
    (Ideal.absNorm (finiteConductor K chi).val : ℝ)
  nlinarith

/-- The one actual modulus gives both scalar inputs required by the
ordinary restoration operator. The finite theta constant is fixed
before all moving factors, rows and remaining ideals. -/
theorem MovingReflectionRowCalibration.scalar_bounds
    {S : Set (HeightOneSpectrum (𝓞 K))} [Fintype S]
    {probe : ProbeData K S} {rows : RowCharacterInput K S probe}
    {theta : Finset (HeckeCharacter K)}
    {node : Node K omegaCharacter psiCharacter}
    {extra : NonzeroIdeal K → NonzeroIdeal K} {U cost : ℝ}
    (cal : MovingReflectionRowCalibration S probe rows theta node extra U)
    (hU : 1 < U)
    (hfixed : movingReflectionConductorConstant S psiCharacter theta ≤ U ^ cost)
    (u : NonzeroIdeal K) (hu : u ∈ pairedRows node.data node.parameters U) :
    (Ideal.absNorm (∏ p ∈ rowRestorationDeletion S node.data extra u, p) : ℝ) ≤
        U ^ (node.width + cost) ∧
      ∀ length : ℝ, ∀ D ∈ (rowRestorationDeletion S node.data extra u).powerset,
        ∀ H : SmoothIdeal (rowRestorationDeletion S node.data extra u),
          heckeConductorScale K (node.data.plainBackground * node.data.rowCharacter u) *
              (Ideal.absNorm (∏ p ∈ D, p) : ℝ) / (U ^ length * inorm H.val) ≤
            U ^ (node.width - length + cost) := by
  obtain ⟨count, factors, sectors, powers, displayed, correction,
    hcorrection, hfactors, hsupport, hextra, hidentify⟩ := cal.identify
  obtain ⟨v, hv, sector, hrow⟩ := hidentify u hu
  let chi := node.data.plainBackground * node.data.rowCharacter u
  let E := rowRestorationDeletion S node.data extra u
  have hchar : chi = (node.data.plainBackground * correction) *
      ((∏ i, completeIdealRowCharacter K S probe rows (sectors i) (factors i).val ^ powers i) *
        completeIdealRowCharacter K S probe rows sector v.val) := by
    dsimp only [chi]
    rw [hrow, hv]
    simp only [mul_assoc]
  have hbound := actualMovingReflectionScale_remainingProduct_le S probe rows
    (node.data.plainBackground * correction) Finset.univ factors sectors powers (extra u)
    (fun i _ => (hfactors i).trans (hextra u hu)) sector v (extra u) (dvd_refl _)
  dsimp only at hbound
  rw [← hchar] at hbound
  have hbound' : heckeConductorScale K chi * (Ideal.absNorm (∏ p ∈ E, p) : ℝ) ≤
      reflectionConductorConstant S (node.data.plainBackground * correction) *
        idealNorm K u * idealNorm K (extra u) := by
    simpa only [hv, E, rowRestorationDeletion, chi] using hbound
  have hU0 : 0 < U := zero_lt_one.trans hU
  have hconstant : reflectionConductorConstant S (node.data.plainBackground * correction) ≤
      U ^ cost := (reflectionConductorConstant_le_moving S psiCharacter theta
        node.data.plainBackground correction node.data.plain_background_spec hcorrection).trans hfixed
  have htotal : heckeConductorScale K chi * (Ideal.absNorm (∏ p ∈ E, p) : ℝ) ≤
      U ^ (node.width + cost) := by
    apply hbound'.trans
    calc
      _ = reflectionConductorConstant S (node.data.plainBackground * correction) *
          (idealNorm K u * idealNorm K (extra u)) := mul_assoc _ _ _
      _ ≤ U ^ cost * U ^ node.width :=
        mul_le_mul hconstant (cal.product_budget u hu)
          (mul_nonneg (idealNorm_pos K u).le (idealNorm_pos K (extra u)).le)
          (Real.rpow_nonneg hU0.le _)
      _ = U ^ (node.width + cost) := by
        rw [← Real.rpow_add hU0]
        congr 1
        ring
  constructor
  · have hsmall : (Ideal.absNorm (∏ p ∈ E, p) : ℝ) ≤
        heckeConductorScale K chi * (Ideal.absNorm (∏ p ∈ E, p) : ℝ) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (actualConductorScale_one_le chi)
          (Nat.cast_nonneg (Ideal.absNorm (∏ p ∈ E, p)))
    exact hsmall.trans htotal
  · intro length D hD H
    have hE : ∀ p ∈ E, Prime p := rowRestorationDeletion_prime S node.data extra u
    have hE0 := subset_product_nonzero E hE
    have hs : primeSupport (∏ p ∈ E, p) = E := by
      have hf : normalizedFactors (∏ p ∈ E, p) = E.val := by
        simpa using normalizedFactors_prod_of_prime (m := E.val) hE
      simp only [primeSupport, hf, Finset.val_toFinset]
    have hdiv : (∏ p ∈ D, p) ∣ ∏ p ∈ E, p := by
      apply support_product_dvd hE0
      simpa only [hs] using Finset.mem_powerset.mp hD
    have hnorm : (Ideal.absNorm (∏ p ∈ D, p) : ℝ) ≤
        (Ideal.absNorm (∏ p ∈ E, p) : ℝ) := by
      exact_mod_cast Nat.le_of_dvd
        (Nat.pos_of_ne_zero (fun hz => hE0 (Ideal.absNorm_eq_zero_iff.mp hz)))
        (map_dvd Ideal.absNorm hdiv)
    have hQ := conductorScale_pos K chi
    have hDscale := (mul_le_mul_of_nonneg_left hnorm hQ.le).trans htotal
    have hH : 1 ≤ inorm H.val := by
      change (1 : ℝ) ≤ (Ideal.absNorm H.val.val : ℝ)
      exact_mod_cast Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero
        (fun hz => H.val.property (Ideal.absNorm_eq_zero_iff.mp hz)))
    calc
      _ = (heckeConductorScale K chi * (Ideal.absNorm (∏ p ∈ D, p) : ℝ) /
          U ^ length) / inorm H.val := by rw [div_div]
      _ ≤ heckeConductorScale K chi * (Ideal.absNorm (∏ p ∈ D, p) : ℝ) /
          U ^ length :=
        div_le_self (div_nonneg (mul_nonneg hQ.le (Nat.cast_nonneg _))
          (Real.rpow_nonneg hU0.le _)) hH
      _ ≤ U ^ (node.width + cost) / U ^ length :=
        div_le_div_of_nonneg_right hDscale (Real.rpow_nonneg hU0.le _)
      _ = U ^ (node.width - length + cost) := by
        rw [← Real.rpow_sub hU0]
        congr 1
        ring

/-- The previously proved analytic operator is consumed with the two
scalar inequalities derived from the real moving factors above. -/
theorem uniform_movingRowRestorationPiece_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) (psiCharacter : HeckeCharacter K)
    {delta A epsilon : ℝ} (hdelta : 0 < delta) (hdeltaA : delta ≤ A)
    (hA : 1 < A) (hepsilon : 0 < epsilon) :
    ∃ L : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
      (probe : ProbeData K S) (rows : RowCharacterInput K S probe)
      (theta : Finset (HeckeCharacter K))
      {omega : HeckeCharacter K} (node : Node K omega psiCharacter)
      (extra : NonzeroIdeal K → NonzeroIdeal K) (V : NonzeroIdeal K → SmoothAnnularTest)
      (U cost length loss : ℝ), 1 < U →
      MovingReflectionRowCalibration S probe rows theta node extra U →
      movingReflectionConductorConstant S psiCharacter theta ≤ U ^ cost →
      epsilon * (node.width + cost) ≤ loss →
      ∀ (tail : Bool) (J : ℕ) (u : NonzeroIdeal K),
      u ∈ pairedRows node.data node.parameters U →
      ‖rowRestorationPiece tail S node.data extra V delta U length J u‖ ≤
        C * testSeminorm (V u).toFun L A *
          U ^ ((A + 1 / 2) * (node.width - length + cost) +
            (if tail then (1 - A) * reflectionDyadicExponent U J else 0) + loss) := by
  obtain ⟨L, C, hC, hbound⟩ :=
    uniform_rowRestorationPiece_bound_of_scalars hcomplex psiCharacter hdelta hdeltaA hA hepsilon
  refine ⟨L, C, hC, ?_⟩
  intro S instS probe rows theta omega node extra V U cost length loss hU cal hfixed hloss
  exact hbound S node extra V U cost length loss hU
    (fun u hu => cal.scalar_bounds hU hfixed u hu) hloss

end HeckeSkeleton.Moments.EngineInduction
