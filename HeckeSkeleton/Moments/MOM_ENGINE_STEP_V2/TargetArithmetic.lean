import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceFrame
import Expansion.ActualProbeContext
import ThetaGlobal.GlobalSameChoice
import DedekindZetaZeroFree.CharacterSums.Gauss.FiniteSupportReciprocityCancellation
import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Sextic.PrincipalExteriorCharacter

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The unchanged target arithmetic and its actual Haar measures

All physical stages use Base's one arithmetic choice. The coefficient
dictionary is selected by the already proved same-recipe binding;
the generators remain the context's allowed generators. The measures
are the existing self-dual local measures and auxiliary adelic Haar
measures, with their existing Borel structures.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.TargetArithmetic

open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

abbrev choice (c : TargetContext K) := axiomChoice K c
abbrev arithmetic (c : TargetContext K) := (choice c).A
abbrev embedding (c : TargetContext K) := complexEmbedding K c
abbrev context (c : TargetContext K) := (choice c).C

theorem principalRing (c : TargetContext K) : IsPrincipalIdealRing (arithmetic c).R :=
  (context c).principal

theorem totallyComplex (c : TargetContext K) : IsTotallyComplex K :=
  Expansion.ActualProbeContext.totallyComplex K (choice c)

theorem different (c : TargetContext K) (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ (arithmetic c).Sf) :
    HeckeGeneral.Characters.localDifferentExponent K v = 0 :=
  (choice c).different v hv

attribute [local instance]
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar
  Expansion.ActualProbeContext.adeleSpace
  Expansion.ActualProbeContext.adeleBorel
  Expansion.ActualProbeContext.adeleMeasure_isAddHaar

abbrev localMeasures := Expansion.ActualProbeContext.allLocalMeasures K
abbrev finiteMeasure := Expansion.ActualProbeContext.finiteAdeleMeasure K
abbrev fullMeasure := Expansion.ActualProbeContext.adeleMeasure K

def coefficients (c : TargetContext K) : ComparisonPoissonCoefficientData K (arithmetic c) :=
  (ThetaGlobal.GlobalSameChoice.exists_binding_with_chosen_recipe
    (arithmetic c) (embedding c) (choice c).η (choice c).hS (context c)).choose

theorem coefficients_binding (c : TargetContext K) :
    PrincipalProbeConstruction.ArithmeticBinding (arithmetic c) (embedding c)
      (choice c).η (choice c).hS (context c)
      (HeckeAxiom.recipeOfContext (arithmetic c) (context c)) (coefficients c) :=
  (ThetaGlobal.GlobalSameChoice.exists_binding_with_chosen_recipe
    (arithmetic c) (embedding c) (choice c).η (choice c).hS (context c)).choose_spec

theorem coefficients_character_apply (c : TargetContext K)
    (I : (arithmetic c).Exterior) (a : (arithmetic c).R)
    (ha : (arithmetic c).Generates I a)
    (x : FiniteTransform.Residue (arithmetic c).R.toSubring a) :
    (coefficients c).character a x =
      (arithmetic c).sexticResiduePowerChar (embedding c) I 1
        (Ideal.quotientEquivAlgOfEq (arithmetic c).R ha.2 x) := by
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ((coefficients_binding c).exteriorCharacters I a t ha).trans
    (NormalizedProbe.exteriorSexticRowCharacter_eq_sexticResiduePowerChar
      (arithmetic c) (embedding c) I t)

theorem coefficients_gammaTwo (c : TargetContext K)
    (q : ExteriorSquarefreeIdeal (arithmetic c).cS) :
    (coefficients c).gammaTwo q =
      (arithmetic c).idealGauss (embedding c) (choice c).hS q.val
        ((coefficients c).generator q.val) ((coefficients c).generates q.val) 2 := by
  let A := arithmetic c
  let a := (coefficients c).generator q.val
  have ha : A.Generates q.val a := (coefficients c).generates q.val
  letI := (coefficients c).finiteResidue a ha.1
  letI : Finite (A.R ⧸ A.extendIdeal q.val) := A.exteriorResidue_finite q.val
  letI : Fintype (A.R ⧸ A.extendIdeal q.val) := Fintype.ofFinite _
  let e := Ideal.quotientEquivAlgOfEq A.R ha.2
  rw [(coefficients_binding c).gammaTwo q]
  unfold ThetaReflectionData.gammaTwoRecipe SArithmeticData.idealGauss
  congr 1
  unfold FiniteTransform.gaussSum FiniteTransform.gaussSumWithLifts
  apply Fintype.sum_equiv e.toEquiv
  intro x
  congr 1
  · rw [MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0),
      coefficients_character_apply c q.val a ha x]
    simp only [SArithmeticData.sexticResiduePowerChar, SArithmeticData.sexticExponent]
    norm_num
    rw [MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0)]
  · simp only [OneMemClass.coe_one, one_mul]
    rw [(coefficients_binding c).fieldTrace]
    have hx := (FiniteTransform.canonicalLifts A.R.toSubring a).property x
    have he : e x = Ideal.Quotient.mk (A.extendIdeal q.val)
        ((FiniteTransform.canonicalLifts A.R.toSubring a).val x) := by
      calc
        e x = e (FiniteTransform.residueMap A.R.toSubring a
            ((FiniteTransform.canonicalLifts A.R.toSubring a).val x)) := congrArg e hx.symm
        _ = _ := Ideal.quotientEquivAlgOfEq_mk A.R ha.2 _
    change (A.fieldTraceCharacter
        (((FiniteTransform.canonicalLifts A.R.toSubring a).val x : K) / (a : K)) : ℂ) =
      (A.residueTraceCharacter (choice c).hS q.val a ha (e x) : ℂ)
    rw [he, A.residueTraceCharacter_apply]

/-- The allowed-generator witness is the context's existing generator.
The other three clauses are proved identities for the same dictionary. -/
theorem coefficients_recipe (c : TargetContext K) :
    GlobalPairCancel.HasArithmeticRecipes (arithmetic c) (embedding c)
      (choice c).hS (context c).correction.B (coefficients c) := by
  refine ⟨?_, ?_, (coefficients_binding c).fieldTrace, coefficients_gammaTwo c⟩
  · intro I
    refine ⟨(HeckeAxiom.recipeOfContext (arithmetic c) (context c)).generator I,
      (coefficients_binding c).sameGenerator I, ?_⟩
    exact (HeckeAxiom.recipeOfContext (arithmetic c) (context c)).allowed I
  · intro I a ha
    ext x
    rw [coefficients_character_apply c I a ha]
    have ht {J L : Ideal (arithmetic c).R} (h : J = L)
        (χ : MulChar ((arithmetic c).R ⧸ J) ℂ) (y : (arithmetic c).R ⧸ L) :
        GeneratorInvariance.transportCharacter J L h χ y =
          χ (Ideal.quotientEquivAlgOfEq (arithmetic c).R h.symm y) := by
      subst L
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
      rfl
    exact (ht ha.2.symm _ x).symm

end HeckeSkeleton.Moments.EngineStepV2.TargetArithmetic
