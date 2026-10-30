module

public import ThetaGlobal.GlobalProjectReflectedPhases
public import ThetaGlobal.GlobalSkeletonChoice

@[expose] public section

/-!
# The actual exterior product is the literal Omega--rho--pi--lambda coefficient

The proof first multiplies the one-place formulas, then evaluates their
unit phases with the fixed allowed generators, and finally applies the
zero-extended sextic reciprocity calculation. The three ideal variables
and both active sets are kept throughout. The final theorem is for the
same skeleton arithmetic choice and the actual source factorization.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section

namespace ThetaGlobal.GlobalProjectReflectedDictionary

open NumberField IsDedekindDomain DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.GlobalProjectLocalDigitTables ThetaGlobal.GlobalProjectLocalPhases
open ThetaGlobal.GlobalProjectReflectedLocalModel ThetaGlobal.GlobalProjectReflectedPhases
open ThetaGlobal.GlobalProjectArithmeticProduct
open scoped NumberField Classical BigOperators nonZeroDivisors

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)

local notation "Sf" => (R.A.Sf : Set (HeightOneSpectrum (𝓞 F)))
local notation "P" => ThetaBranch.ExteriorPrime R.A

variable (Adata : ThetaArithmeticData F Sf)
  (hA : AllowedGeneratorInput F Sf Adata)
  (hgen : ∀ I : ExteriorIdeal F Sf,
    GlobalActualFrequency.generatorUnit F Sf Adata I =
      R.probe.allowed.generator ((HeckeAxiom.exteriorEquiv R.A).symm I))
  (d : MarkedDatum F Sf) (i : ReflectionIndex F Sf d) (hi : Admissible R d i)

include hA hgen hi in
theorem moving_product :
    (∏ p ∈ exteriorSupport F Sf d.moving, movingLocal R Adata d i p) =
      (∏ p ∈ exteriorSupport F Sf d.moving, movingCore R Adata d i p) *
      idealSymbol F Sf Adata d.moving (Adata.generator i.c) *
      idealSymbol F Sf Adata d.moving (Adata.generator i.n) ^ 3 *
      idealSymbol F Sf Adata d.moving (Adata.generator (activeMarkedIdeal F Sf d i)) ^ (-2 : ℤ) := by
  calc
    _ = ∏ p ∈ exteriorSupport F Sf d.moving,
        movingCore R Adata d i p * evaluation R Adata p i.c *
          evaluation R Adata p i.n ^ 3 *
          evaluation R Adata p (activeMarkedIdeal F Sf d i) ^ (-2 : ℤ) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact movingLocal_split R Adata hA hgen d i hi p hp
    _ = _ := by
      simp only [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_zpow, evaluation]
      rw [idealSymbol_squarefree_product F Sf Adata d.moving d.moving_squarefree,
        idealSymbol_squarefree_product F Sf Adata d.moving d.moving_squarefree,
        idealSymbol_squarefree_product F Sf Adata d.moving d.moving_squarefree] <;> rfl

include hA hgen hi in
theorem frozen_product :
    (∏ p ∈ i.activeFrozen, frozenLocal R Adata d i p) =
      (∏ p ∈ i.activeFrozen, frozenCore R Adata d i p) *
      (∏ p ∈ i.activeFrozen, evaluation R Adata p i.c ^
        localWeylExponent (rowDigit F Sf d p) (primeExponents i.numeratorFrozen.val p.val)) *
      (∏ p ∈ i.activeFrozen, evaluation R Adata p d.moving ^
        (-(2 * localWeylExponent (rowDigit F Sf d p) (primeExponents i.numeratorFrozen.val p.val) : ℤ))) *
      (∏ p ∈ i.activeFrozen, evaluation R Adata p (activeMarkedIdeal F Sf d i) ^
        (-(2 * localWeylExponent (rowDigit F Sf d p) (primeExponents i.numeratorFrozen.val p.val) : ℤ))) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  exact frozenLocal_split R Adata hA hgen d i hi p hp

include hA hgen hi in
theorem marked_product :
    (∏ p ∈ i.activeMarks, quadraticLocal R Adata d i p) =
      (Real.sqrt (exteriorNorm F Sf (activeMarkedIdeal F Sf d i)) : ℂ)⁻¹ *
      (∏ p ∈ i.activeMarks, markedCore R Adata d i p) *
      idealSymbol F Sf Adata (activeMarkedIdeal F Sf d i) (Adata.generator i.c) ^ 2 *
      idealSymbol F Sf Adata (activeMarkedIdeal F Sf d i) (Adata.generator i.n) ^ 6 *
      idealSymbol F Sf Adata (activeMarkedIdeal F Sf d i) (Adata.generator d.moving) ^ (-4 : ℤ) := by
  calc
    _ = ∏ p ∈ i.activeMarks,
        (Real.sqrt (p.val.asIdeal.absNorm : ℝ) : ℂ)⁻¹ * markedCore R Adata d i p *
          evaluation R Adata p i.c ^ 2 * evaluation R Adata p i.n ^ 6 *
          evaluation R Adata p d.moving ^ (-4 : ℤ) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact markedLocal_split R Adata hA hgen d i hi p hp
    _ = _ := by
      have hn := sqrt_exteriorNorm_squarefree F Sf (activeMarkedIdeal F Sf d i)
        (primeSetIdeal_squarefree F Sf i.activeMarks)
      rw [activeMarkedIdeal, primeSetIdeal_support] at hn
      simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib,
        Finset.prod_pow, Finset.prod_zpow, evaluation]
      rw [← hn]
      simp only [activeMarkedIdeal, idealSymbol_primeSet_product] <;> rfl

include hA hgen hi in
theorem column_product :
    (∏ p ∈ exteriorSupport F Sf i.c, quadraticLocal R Adata d i p) =
      (Real.sqrt (exteriorNorm F Sf i.c) : ℂ)⁻¹ *
      (∏ p ∈ exteriorSupport F Sf i.c, columnCore R Adata d i p) *
      idealSymbol F Sf Adata i.c (Adata.generator d.moving) ^ (-4 : ℤ) *
      idealSymbol F Sf Adata i.c (Adata.generator (activeMarkedIdeal F Sf d i)) ^ (-4 : ℤ) := by
  calc
    _ = ∏ p ∈ exteriorSupport F Sf i.c,
        (Real.sqrt (p.val.asIdeal.absNorm : ℝ) : ℂ)⁻¹ * columnCore R Adata d i p *
          evaluation R Adata p d.moving ^ (-4 : ℤ) *
          evaluation R Adata p (activeMarkedIdeal F Sf d i) ^ (-4 : ℤ) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact columnLocal_split R Adata hA hgen d i hi p hp
    _ = _ := by
      simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib,
        Finset.prod_zpow, evaluation]
      rw [← sqrt_exteriorNorm_squarefree F Sf i.c i.c_squarefree,
        idealSymbol_squarefree_product F Sf Adata i.c i.c_squarefree,
        idealSymbol_squarefree_product F Sf Adata i.c i.c_squarefree] <;> rfl

def idealPeriodProduct (θ : HeckeCharacter F) : ℂ :=
  periodValue F Sf Adata d θ i.numeratorFrozen * periodValue F Sf Adata d θ i.c *
    periodValue F Sf Adata d θ i.n ^ 3 * periodValue F Sf Adata d θ d.moving ^ (-2 : ℤ) *
    periodValue F Sf Adata d θ (activeFrozenIdeal F Sf d i) ^ (-2 : ℤ) *
    periodValue F Sf Adata d θ (activeMarkedIdeal F Sf d i) ^ (-2 : ℤ)

include hA hgen hi in
theorem raw_coefficient_period (θ : HeckeCharacter F) :
    rawCoefficient R Adata d i * (idealPeriodProduct R Adata d i θ)⁻¹ =
      ReflectedArithmetic.reflectedCoefficient F Sf Adata d i θ := by
  rw [← symmetricCoefficient_eq F Sf Adata d i θ hA, rawCoefficient,
    moving_product R Adata hA hgen d i hi,
    frozen_product R Adata hA hgen d i hi,
    marked_product R Adata hA hgen d i hi,
    column_product R Adata hA hgen d i hi]
  simp only [symmetricCoefficient, frozenOmega, reflectedMarkFactor,
    reflectedRowFactor, reflectedColumnFactor, idealPeriodProduct,
    movingCore, frozenCore, markedCore, columnCore, movingPhase, frozenPhase,
    markedPhase, columnPhase, evaluation, unitEvaluation, skeletonPrime,
    div_eq_mul_inv, mul_inv_rev, inv_pow, zpow_neg, zpow_ofNat, inv_inv]
  ring

end ThetaGlobal.GlobalProjectReflectedDictionary

namespace HeckeSkeleton

open NumberField IsDedekindDomain DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.GlobalProjectReflectedLocalModel
open scoped NumberField Classical

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

/-- The source coefficient, after its actual target-period factor, is
the paper's complete literal arithmetic prefactor. The only unresolved
exterior input is the explicitly one-place `LocalDigitTables.Input`. -/
theorem thetaRecipe_reflected_coefficient
    (θ : HeckeCharacter K)
    (hS : conductorPlaces K θ ⊆ (thetaRecipe K c).A.Sf)
    {Q : AdmissibleFlatSources (thetaRecipe K c)}
    {T : Realization (thetaRecipe K c) Q}
    (D : SourceFactorization (thetaRecipe K c) Q T)
    (H : ThetaGlobal.GlobalProjectLocalDigitTables.Input (thetaRecipe K c) D (arithmeticData K c))
    (hA : AllowedGeneratorInput K (places K c) (arithmeticData K c))
    (d : MarkedDatum K (places K c)) (i : ReflectionIndex K (places K c) d)
    (hi : Admissible (thetaRecipe K c) d i) :
    ThetaGlobal.GlobalProjectSignedExtraction.reverseCoefficient (thetaRecipe K c) D
      (ThetaGlobal.GlobalProjectMarkedSupport.row (thetaRecipe K c) d)
      (ThetaGlobal.GlobalProjectMarkedSupport.weight (thetaRecipe K c) (arithmeticData K c) d)
      (ThetaGlobal.GlobalActualFrequency.representative K (places K c) (arithmeticData K c) d i) *
    (ThetaGlobal.GlobalTargetPeriod.period (thetaRecipe K c) θ (QuotientGroup.mk d.rowUnit)
      ((thetaRecipe K c).A.diagonal
        (ThetaGlobal.GlobalActualFrequency.representative K (places K c) (arithmeticData K c) d i)))⁻¹ =
      ThetaGlobal.ReflectedArithmetic.reflectedCoefficient K (places K c) (arithmeticData K c) d i θ := by
  rw [thetaRecipe_period_representative K c θ hS]
  change ThetaGlobal.GlobalProjectSignedExtraction.reverseCoefficient (thetaRecipe K c) D
    (ThetaGlobal.GlobalProjectMarkedSupport.row (thetaRecipe K c) d)
    (ThetaGlobal.GlobalProjectMarkedSupport.weight (thetaRecipe K c) (arithmeticData K c) d)
    (x (thetaRecipe K c) (arithmeticData K c) d i) *
    (ThetaGlobal.GlobalProjectReflectedDictionary.idealPeriodProduct
      (thetaRecipe K c) (arithmeticData K c) d i θ)⁻¹ = _
  rw [reverseCoefficient_raw (thetaRecipe K c) (arithmeticData K c) d i hi D H]
  exact ThetaGlobal.GlobalProjectReflectedDictionary.raw_coefficient_period
    (thetaRecipe K c) (arithmeticData K c) hA (thetaRecipe_generator K c) d i hi θ

end HeckeSkeleton
