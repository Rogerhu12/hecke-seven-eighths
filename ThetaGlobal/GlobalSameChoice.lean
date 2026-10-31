import ThetaGlobal.GlobalChoice
import DedekindZetaZeroFree.Moments.Reflected.RankOneExpansion

/-!
# The existing theta source on the project's exact arithmetic choice

The source existence theorem used upstream chooses a new enlarged recipe.
Here the shared-probe construction is strengthened to prescribe exactly
`HeckeAxiom.recipeOfContext A C`, then placed in a recipe with `R.A = A`.
The complement, correction characters, and allowed generators are retained
literally.  Only the finite/archimedean vectors need later replacement for
the target infinity type.

Project-facing source; no claim of dependency-complete compilation is made.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.GlobalSameChoice

open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open PrincipalProbeConstruction MomentSources
open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]

/-- Prescribe the existing allowed-generator section instead of hiding a
new section inside an existential arithmetic binding. -/
theorem exists_binding_with_chosen_recipe (A : SArithmeticData F)
    (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus)
    (hS : A.ContainsTraceBadPlaces) (C : A.GeneralArithmeticContext σ η hS) :
    ∃ D : ComparisonPoissonCoefficientData F A,
      ArithmeticBinding A σ η hS C (HeckeAxiom.recipeOfContext A C) D := by
  let r (I : A.Exterior) : A.R := Classical.choose (C.allowed_integral I)
  have hr (I : A.Exterior) : A.Generates I (r I) :=
    (Classical.choose_spec (Classical.choose_spec (C.allowed_integral I))).1
  have har (I : A.Exterior) :
      ((HeckeAxiom.recipeOfContext A C).generator I : F) = (r I : F) :=
    (Classical.choose_spec (Classical.choose_spec (C.allowed_integral I))).2.1
  let e : AddChar F ℂ := {
    toFun := fun x => (A.fieldTraceCharacter x : ℂ)
    map_zero_eq_one' := by simp
    map_add_eq_mul' := by
      intro x y
      exact congrArg Circle.coeHom (A.fieldTraceCharacter.map_add_eq_mul x y) }
  let D₀ : ComparisonPoissonCoefficientData F A := {
    generator := r
    generates := hr
    finiteResidue := Inputs.finiteResidue A
    character := Inputs.rowCharacter A σ
    additiveCharacter := e
    gammaTwo := fun _ => 0
    theta := fun m => if hm : m ≠ 0 then
      (A.correctionLS C.correction.Λ C.correction.G 1
        (A.diagonal (ThetaReflectionData.rowUnit A ⟨m, hm⟩)) : ℂ) else 0 }
  let D : ComparisonPoissonCoefficientData F A :=
    { D₀ with gammaTwo := ThetaReflectionData.gammaTwoRecipe A D₀ }
  refine ⟨D, rfl, har, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Inputs.rowCharacter_apply A σ
  · intro m
    exact dif_pos m.property
  · intro c
    rfl
  · intro c n u
    apply Inputs.rowCharacter_sixth
    exact mul_ne_zero (hr c.val).1 (pow_ne_zero 3 (hr n).1)
  · intro x
    rfl
  · exact Inputs.fieldTrace_phase A

/-- The original normalized-probe construction, with its exact chosen
allowed recipe retained as an additional conclusion. -/
theorem exists_probe_with_chosen_recipe (A : SArithmeticData F)
    (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus)
    (hS : A.ContainsTraceBadPlaces) (C : A.GeneralArithmeticContext σ η hS)
    (hη : η.IsPrincipal) (hprincipal : C.correction.η_id = 1)
    (hdiff : PoissonS.ContainsDifferent F A.Sf) :
    ∃ P : NormalizedProbe.PrincipalData A σ η hS,
      P.allowed = HeckeAxiom.recipeOfContext A C ∧
      P.correction = C.correction ∧
      Nonempty (NormalizedProbe.MellinNormalizationData A σ η hS P) := by
  obtain ⟨D, B⟩ := exists_binding_with_chosen_recipe A σ η hS C
  let G := HeckeAxiom.recipeOfContext A C
  obtain ⟨Q, ν, hν, hdis⟩ := exists_domain_with_disintegration A σ η hS C
  obtain ⟨U, ⟨frequencies⟩⟩ :=
    exists_frequency_representatives A σ η hS C G B.sameComplement
  obtain ⟨μ, hμ, hlocal, hprod⟩ := exists_trace_normalized_haar A
  obtain ⟨hcontinuous, htrace, hconductor⟩ := canonical_trace_contract A hS
  obtain ⟨W₁, W₀, hannular, hcompact, hunits, hnonzero, hzero, hmellin, hW₁⟩ :=
    probe_fixed_weight_construction F A (fun v => ResidueTrace.localTraceCharacter v.val)
      hcontinuous htrace (NormalizedProbe.poissonAdditiveMeasure A μ) ν hprod hν
  let P : NormalizedProbe.PrincipalData A σ η hS := {
    principal := hη
    correction := C.correction
    principalIdele := hprincipal
    coefficients := D
    allowed := G
    sameComplement := B.sameComplement
    sameGenerator := B.sameGenerator
    exteriorCharacters := B.exteriorCharacters
    theta_principal := B.theta
    gammaTwo_recipe := B.gammaTwo
    sixthUnitCharacters := B.sixthUnits
    unitReps := U
    frequencies := frequencies
    domain := Q
    finiteTrace := fun v => ResidueTrace.localTraceCharacter v.val
    continuousTrace := hcontinuous
    traceCompatible := htrace
    sameTrace := B.sameTrace
    additiveMeasure := NormalizedProbe.poissonAdditiveMeasure A μ
    additiveHaar := hprod
    multiplicativeMeasure := ν
    multiplicativeHaar := hν
    W0 := W₀
    W1 := W₁
    annular := hannular
    compactSupport := hcompact
    supportUnits := hunits
    nonzero := hnonzero
    zeroFrequency := hzero
    nonzeroMellin := hmellin }
  refine ⟨P, rfl, rfl, ⟨?_⟩⟩
  exact {
    finiteMeasure := μ
    finiteHaar := hμ
    localNormalization := hlocal
    containsDifferent := hdiff
    sameAdditiveMeasure := rfl
    sameFiniteTrace := fun _ => rfl
    disintegration := hdis }

variable {S₀ : Finset (HeightOneSpectrum (𝓞 F))} {ζ : F} {σ : F →+* ℂ}
  (X : HeckeAxiom.ArithmeticChoice F S₀ ζ σ)

structure FixedProbe where
  probe : NormalizedProbe.PrincipalData X.A σ X.η X.hS
  normalization : NormalizedProbe.MellinNormalizationData X.A σ X.η X.hS probe
  allowed_eq : probe.allowed = HeckeAxiom.recipeOfContext X.A X.C
  correction_eq : probe.correction = X.C.correction

theorem fixedProbe_nonempty : Nonempty (FixedProbe X) := by
  obtain ⟨P, hP, hC, ⟨N⟩⟩ := exists_probe_with_chosen_recipe X.A σ X.η X.hS
    X.C X.principal X.principalIdele X.containsDifferent
  exact ⟨⟨P, N, hP, hC⟩⟩

def fixedProbe : FixedProbe X := Classical.choice (fixedProbe_nonempty X)

/-- The recipe uses literally the input choice's `A`, `C`, embedding and
allowed generators. Its continuation is supplied by the trivial modulus. -/
def recipe (hmod : X.A.modulus = ⊤) : PrincipalMellin.ActualRecipe X.A X.η where
  A := X.A
  containsOriginal := le_rfl
  sameModulus := rfl
  sameRoot := rfl
  classKilled := X.C.classGroup_trivial
  σ := σ
  traceBad := X.hS
  probe := (fixedProbe X).probe
  normalization := (fixedProbe X).normalization
  continuation := GlobalChoice.continuation X hmod

theorem recipe_A (hmod : X.A.modulus = ⊤) : (recipe X hmod).A = X.A := rfl
theorem recipe_embedding (hmod : X.A.modulus = ⊤) : (recipe X hmod).σ = σ := rfl
theorem recipe_allowed (hmod : X.A.modulus = ⊤) :
    (recipe X hmod).probe.allowed = HeckeAxiom.recipeOfContext X.A X.C :=
  (fixedProbe X).allowed_eq
theorem recipe_correction (hmod : X.A.modulus = ⊤) :
    (recipe X hmod).probe.correction = X.C.correction :=
  (fixedProbe X).correction_eq

/-- Run the source construction on this recipe, without calling the
upstream theorem that would first enlarge and choose another arithmetic set. -/
theorem source_on_same_choice (hmod : X.A.modulus = ⊤)
    (halign : ∀ z : rootsOfUnity 6 F, σ ((z : Fˣ) : F) =
      (KPLocalCover.coefficientEmbedding F X.A.zeta12 X.A.primitive_zeta12 z : ℂ)) :
    ∃ N : TraceHaarTransport (recipe X hmod),
      Nonempty (JointExteriorCoefficientSources (recipe X hmod) N) := by
  let R := recipe X hmod
  have hR : RootAligned R := halign
  obtain ⟨N⟩ := ThetaExpansion.trace_haar_transport_exists R hR
  have p₅ := ThetaExpansion.admissible_flat_sources R hR N
  have p₆ := ThetaExpansion.common_smooth_laurent_germ_exists R hR N p₅
  have p₇ := ThetaExpansion.detected_period_factorization R hR N p₆
  exact ⟨N, ThetaExpansion.exterior_coefficients R hR N p₇⟩

/-- Retain the same recipe through the existing normalization, finite
cutoff packet, constant-term and digit stages.  These selected vectors
provide the starting source; a target with additional unit ramification
still requires the explicit local cutoff refinement described in the report. -/
theorem digit_source_on_same_choice (hmod : X.A.modulus = ⊤)
    (halign : ∀ z : rootsOfUnity 6 F, σ ((z : Fˣ) : F) =
      (KPLocalCover.coefficientEmbedding F X.A.zeta12 X.A.primitive_zeta12 z : ℂ)) :
    ∃ N : TraceHaarTransport (recipe X hmod),
      Nonempty (JointDigitDescentSources (recipe X hmod) N) := by
  let R := recipe X hmod
  have hR : RootAligned R := halign
  obtain ⟨N, p₈⟩ := source_on_same_choice X hmod halign
  have p₉ := ThetaExpansion.first_root_packet R hR N p₈
  have p₁₀ := ThetaExpansion.residual_constant_term R hR N p₉
  have p₁₁ := ThetaExpansion.mellin_gaussian R N p₁₀
  exact ⟨N, ThetaExpansion.weighted_digits_descent R hR N p₁₁⟩

end ThetaGlobal.GlobalSameChoice
