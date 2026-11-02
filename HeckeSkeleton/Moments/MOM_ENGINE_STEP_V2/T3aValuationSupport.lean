import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3aValuations
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFirstPhase

set_option autoImplicit false

/-!
# The original displayed moving support controls local ramification

Every listed moving factor is treated with its original generated ideal,
including factors whose exponent is zero or cancels another exponent.
Coprimality to the displayed support makes each genuine factor character
unramified and hence also their full product with its integer powers.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3a

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

/-- The factor's complete character depends on its actual original
element, so the generated-singleton unramifiedness theorem applies. -/
theorem movingFactor_unramified_of_coprime
    (D : OriginalMovingFactors A P R) (i : Fin D.count)
    (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (hcop : IsCoprime p.asIdeal (D.factorIdeal i).val) :
    UnramifiedAt K (D.factorCharacter i) p := by
  let E := OriginalMovingFactors.singleton (P := P) (R := R) (D.element i) 1
  have hchar : E.character = D.factorCharacter i := by
    change (∏ j : Fin 1, E.factorCharacter j ^ (1 : ℤ)) = D.factorCharacter i
    rw [Fin.prod_univ_one, zpow_one]
    rfl
  have hsingle := CanonicalLiteralFirstPhase.singleton_unramified P R
    (D.factorIdeal i) (D.element i).val (D.factorIdeal_generates i) p hp hcop
  change UnramifiedAt K E.character p at hsingle
  rw [hchar] at hsingle
  exact hsingle

/-- The exact original displayed support controls every integer power
in the literal moving-character product. -/
theorem moving_unramified_of_coprime_support
    (D : OriginalMovingFactors A P R) (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (hcop : IsCoprime p.asIdeal D.support.val) :
    UnramifiedAt K D.character p := by
  have hfull : IsCoprime p.asIdeal D.fullIdeal.val :=
    (D.coprime_support_iff_fullIdeal p.asIdeal).mp hcop
  have hfactor (i : Fin D.count) : UnramifiedAt K (D.factorCharacter i) p := by
    apply movingFactor_unramified_of_coprime D i p hp
    apply hfull.of_isCoprime_of_dvd_right
    exact Finset.dvd_prod_of_mem (fun j => (D.factorIdeal j).val) (Finset.mem_univ i)
  have hpower (i : Fin D.count) :
      UnramifiedAt K (D.factorCharacter i ^ D.power i) p := by
    intro u hu
    rw [localComponent_zpow]
    change localComponent K p (D.factorCharacter i) u ^ D.power i = 1
    rw [hfactor i u hu, one_zpow]
  have hprod (s : Finset (Fin D.count)) :
      UnramifiedAt K (∏ i ∈ s, D.factorCharacter i ^ D.power i) p := by
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty]
      exact unramifiedAt_one K p
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (hpower i).mul K ih
  exact hprod Finset.univ

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3a

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3a.moving_unramified_of_coprime_support
