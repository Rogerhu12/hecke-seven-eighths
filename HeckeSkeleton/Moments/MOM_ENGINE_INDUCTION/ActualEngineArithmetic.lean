import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CompleteSourceReflection
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalArithmetic
import Expansion.ActualProbeContext
import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.ProbeRowCharacters

/-!
# The original arithmetic choice supplies the engine's coefficient data

The finite Poisson coefficient data use the allowed generators of the
same arithmetic context, its sextic residue characters, field trace and
Gauss correction. Their arithmetic recipes are proved here. The original
canonical theta also ramifies only at the already selected finite places.
These choices precede every recursive node and do not change the source.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global Expansion.Project EngineStep

variable {K : Type} [Field K] [NumberField K]

private theorem transported_character_mk {T : Type*} [CommRing T]
    (I J : Ideal T) (h : I = J) (chi : MulChar (T ⧸ I) ℂ) (a : T) :
    GeneratorInvariance.transportCharacter I J h chi (Ideal.Quotient.mk J a) =
      chi (Ideal.Quotient.mk I a) := by
  subst J
  rfl

/-- The genuine principal residue character of an allowed generator. -/
theorem originalRowCharacter_recipe (A : SArithmeticData K) (sigma : K →+* ℂ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a) :
    PrincipalProbeConstruction.Inputs.rowCharacter A sigma a =
      GlobalPairCancel.principalCharacter A sigma I a ha := by
  apply MulChar.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change PrincipalProbeConstruction.Inputs.rowCharacter A sigma a
      (FiniteTransform.residueMap A.R.toSubring a r) = _
  rw [PrincipalProbeConstruction.Inputs.rowCharacter_apply A sigma I a r ha]
  rw [GlobalPairCancel.principalCharacter, transported_character_mk]
  exact NormalizedProbe.exteriorSexticRowCharacter_eq_sexticResiduePowerChar A sigma I r

/-- The same fixed arithmetic context produces all coefficient recipes
required by the genuine second Poisson terminal. -/
theorem exists_originalCoefficientData
    (A : SArithmeticData K) (sigma : K →+* ℂ)
    (eta : RayClassCharacter K A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext sigma eta hS) :
    ∃ D : ComparisonPoissonCoefficientData K A,
      GlobalPairCancel.HasArithmeticRecipes A sigma hS C.correction.B D := by
  choose r a hr har ha using C.allowed_integral
  let e : AddChar K ℂ := {
    toFun := fun x => (A.fieldTraceCharacter x : ℂ)
    map_zero_eq_one' := by simp
    map_add_eq_mul' := by
      intro x y
      exact congrArg Circle.coeHom (A.fieldTraceCharacter.map_add_eq_mul x y) }
  let D : ComparisonPoissonCoefficientData K A := {
    generator := r
    generates := hr
    finiteResidue := PrincipalProbeConstruction.Inputs.finiteResidue A
    character := PrincipalProbeConstruction.Inputs.rowCharacter A sigma
    additiveCharacter := e
    gammaTwo := fun q => A.idealGauss sigma hS q.val (r q.val) (hr q.val) 2
    theta := fun x => if hx : x ≠ 0 then
      (A.correctionLS C.correction.Λ C.correction.G C.correction.η_id
        (A.diagonal (Units.mk0 (x : K) (by exact_mod_cast hx))) : ℂ) else 0 }
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · intro I
    exact ⟨a I, har I, ha I⟩
  · intro I x hx
    exact originalRowCharacter_recipe A sigma I x hx
  · intro x
    rfl
  · intro q
    rfl

namespace Source

variable (c : TargetContext K)

/-- No new arithmetic context is chosen for the strict source. -/
def actualEngineCoefficientData : ComparisonPoissonCoefficientData K (axiomChoice K c).A :=
  (exists_originalCoefficientData (axiomChoice K c).A (complexEmbedding K c)
    (axiomChoice K c).η (axiomChoice K c).hS (axiomChoice K c).C).choose

theorem actualEngineCoefficientData_recipes :
    GlobalPairCancel.HasArithmeticRecipes (axiomChoice K c).A (complexEmbedding K c)
      (axiomChoice K c).hS (axiomChoice K c).C.correction.B
      (actualEngineCoefficientData c) :=
  (exists_originalCoefficientData (axiomChoice K c).A (complexEmbedding K c)
    (axiomChoice K c).η (axiomChoice K c).hS (axiomChoice K c).C).choose_spec

/-- The fixed exceptional catalogue uses only the target and its
inverse, so the original set of places already covers its ramification. -/
theorem actualEngineTheta_badPrimes :
    CanonicalLiteralExceptionalArithmetic.thetaBadPrimes
      (canonicalDetectorTheta K (targetCharacter K c)) ⊆ (axiomChoice K c).A.Sf := by
  intro p hp
  obtain ⟨chi, hchi, hpchi⟩ := Finset.mem_biUnion.mp hp
  have hr := (finite_ramifiedPlaces K chi).mem_toFinset.mp hpchi
  by_contra hp
  have htarget : UnramifiedAt K (targetCharacter K c) p :=
    target_unramified_outside K c p hp
  by_cases hfinite : FiniteOrder (targetCharacter K c)
  · simp only [canonicalDetectorTheta, if_pos hfinite, Finset.mem_insert,
      Finset.mem_singleton] at hchi
    rcases hchi with rfl | rfl | rfl
    · exact hr (unramifiedAt_one K p)
    · exact hr htarget
    · exact hr (htarget.inv K)
  · have heq : chi = 1 := by simpa [canonicalDetectorTheta, hfinite] using hchi
    subst chi
    exact hr (unramifiedAt_one K p)

end Source
end HeckeSkeleton.Moments.EngineInduction

#print axioms HeckeSkeleton.Moments.EngineInduction.exists_originalCoefficientData
#print axioms HeckeSkeleton.Moments.EngineInduction.Source.actualEngineTheta_badPrimes
