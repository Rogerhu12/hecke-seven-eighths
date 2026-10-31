import HeckeSkeleton.Theta
import HeckeGeneral.Analysis.TInputParameterUniformMoments
import HeckeSkeleton.HighArithmeticInputs
import HeckeAxiom.QuadraticSieve
import CubicSieve.Complete
import HeckeSkeleton.ExpansionModels.SourceData
import HeckeSkeleton.ExpansionModels.ActualRowEligibility
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.FiniteSectorReindex
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileControl
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SourceProfileControl
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SourceReindex
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SixthPowerRecipe
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.AmplificationSource
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.WitnessSource

/-! Exploratory actual I/P pipeline, revised §§4–5 and §7.
This file intentionally contains named admissions. None is native verified.
The existing cache arithmetic/fiber proofs are migration candidates; the
canonical recursions, KP consumption and full kappa range are separate gaps.
The 5/6-capped old PRegion and ParameterUniformPInput are never used here.
All finite energies below are the original MomentInputs polynomials.
-/
set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton
open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open scoped Classical BigOperators ContDiff

variable (K : Type) [Field K] [NumberField K]

local instance momentSectorFintype (c : TargetContext K) :
    Fintype (SixthUnitClasses K (places K c)) := Fintype.ofFinite _

/-- The actual source is selected once, after the generic source interface. -/
abbrev actualMomentSourceData (c : TargetContext K) : MomentSourceData K c :=
  recipeMomentSourceData K c (expansionRecipeRaw K c)

/-- Compatibility name for the indices of that same actual source. -/
abbrev SourceMomentIndex (c : TargetContext K) (Z T : ℝ) : Type 1 :=
  SourceMomentIndexFor K c (actualMomentSourceData K c) Z T

variable {K}
variable {c : TargetContext K} {Z T : ℝ}
abbrev momentBlock (i : SourceMomentIndex K c Z T) := momentBlockFor i
abbrev momentAmplitude (i : SourceMomentIndex K c Z T) := momentAmplitudeFor i
abbrev momentWitness (i : SourceMomentIndex K c Z T) := momentWitnessFor i
abbrev momentBase (i : SourceMomentIndex K c Z T) : ℝ := momentBaseFor i
abbrev selectedLength (i : SourceMomentIndex K c Z T) : ℝ := selectedLengthFor i
abbrev SourceMomentIndex.noSlots (i : SourceMomentIndex K c Z T) :
    SourceMomentIndex K c Z T := SourceMomentIndexFor.noSlots i
abbrev inverseParameters (i : SourceMomentIndex K c Z T) : RealParameters :=
  inverseParametersFor i
abbrev pairedParameters (i : SourceMomentIndex K c Z T) : RealParameters :=
  pairedParametersFor i
abbrev ExtendedPRegion (a : RealParameters) : Prop := ExtendedPRegionFor a
abbrev inverseCapacity (i : SourceMomentIndex K c Z T) : Prop := inverseCapacityFor i
abbrev pairedCapacity (i : SourceMomentIndex K c Z T) : Prop := pairedCapacityFor i

variable (K)

/-- Compatibility name; all models use the same fixed actual source. -/
abbrev SourceMomentModels (c : TargetContext K) :=
  SourceMomentModelsFor K c (actualMomentSourceData K c)

variable {K}

abbrev sourceRecipeBlock (i : SourceMomentIndex K c Z T) := recipeSourceBlock i
abbrev sourceRecipeAmplitude (i : SourceMomentIndex K c Z T) := recipeSourceAmplitude i
abbrev sourceRecipeWitness (i : SourceMomentIndex K c Z T) := recipeSourceWitness i

abbrev sourceSelectedMomentModel (i : SourceMomentIndex K c Z T)
    (s : SixthUnitClasses K (places K c))
    (ξ : ExpansionRecipe.RecipeVector)
    (σ τ : NonzeroIdeal K → ExpansionRecipe.RecipeVector) :
    MomentData K c.family.omega (targetCharacter K c) :=
  recipeSourceSelectedMomentModel i s ξ σ τ

variable (K)

-- MI-M-MODELS | §4.1–4.2,§7.1,pp16–20,43.
-- Both marked models and the independent U,D family are generated from
-- the SAME D-EXPANSION recipe.  No independent model choice remains.
abbrev momentModels (c : TargetContext K) : SourceMomentModels K c :=
  recipeMomentModels K c (expansionRecipeRaw K c)

variable {K}
abbrev inverseModel (M : SourceMomentModels K c) (i : SourceMomentIndex K c Z T)
    (s : SixthUnitClasses K (places K c)) := inverseModelFor M i s
abbrev pairedModel (M : SourceMomentModels K c) (i : SourceMomentIndex K c Z T)
    (s : SixthUnitClasses K (places K c)) := pairedModelFor M i s
abbrev unmarkedModel (M : SourceMomentModels K c) (i : SourceMomentIndex K c Z T)
    (s : SixthUnitClasses K (places K c)) := unmarkedModelFor M i s

/-- Literal polynomial calibration. Sector dependence is retained, and the
two plain factors are both matched, with their actual conjugated profiles. -/
abbrev SourcePolynomialCalibration
    (R : RowCharacterInput K (places K c) (probeData K c))
    (M : SourceMomentModels K c) : Prop := SourcePolynomialCalibrationFor R M

/-- The base ideal, original sector and complete common mask must survive
the true source reindex. Large complete norm alone cannot prove this. -/
abbrev SourceRowEligibility (M : SourceMomentModels K c) : Prop :=
  SourceRowEligibilityFor M

/-- Shared whole-profile control, including the prime windows from #10.
The original parameter region and actual source are retained. -/
abbrev WholeMomentProfileControl (M : SourceMomentModels K c) : Prop :=
  WholeMomentProfileControlFor M

/-- Every actual source index lies in the retained physical range. -/
theorem momentBase_ge_two (i : SourceMomentIndex K c Z T) : 2 ≤ momentBase i :=
  recipeMomentBase_ge_two i

theorem momentRowExponent_spec (i : SourceMomentIndex K c Z T) :
    1 < momentRowExponent (momentBase i) ∧ momentRowExponent (momentBase i) ≤ 2 ∧
      (momentBase i) ^ momentRowExponent (momentBase i) = 2 * momentBase i :=
  recipeMoment_rowWidth_spec i

theorem sourceSelectedMomentModel_slots (i : SourceMomentIndex K c Z T)
    (u : FrequencyRow K (places K c)) :
    (∏ j ∈ i.selected, (momentAmplitude i).slotValue j u) =
      slotProduct (inverseModel (momentModels K c) i u.sector)
        u.ideal.val (momentBase i) 0 :=
  recipeSourceSelectedMomentModel_slots i u

variable (K) (c : TargetContext K)

-- MI-M-POLYNOMIAL-CALIBRATION | §4.2,§6.2,§7.1,pp18–20,38,43.
-- Literal identities from the one actual raw data recipe, shared with
-- the physical expansion and its all-label geometry.
theorem moment_polynomial_calibration :
    SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c) :=
  recipeMoment_polynomial_calibration K c (expansionRecipeRaw K c)

-- MI-M-FIBER-ELIGIBILITY | §4.9,§7.1,pp35,43–44.
-- The actual strict shell excludes the unit base ideal for every label.
-- Ramification then excludes the same finite theta family on all scales;
-- both original pairedRows branches retain every original zero mask.
theorem moment_row_eligibility
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c)) :
    SourceRowEligibility (momentModels K c) := by
  exact actualRecipeRowEligibility K c

-- OBLIGATION MI-M-PROFILE-UNIFORMITY | Lemma4.12,Prop4.14,pp33–35.
-- Actual dyadic inverse/plain profiles and selected prime windows, with
-- all independent unmarked scales and the same physical parameter box.
theorem moment_profile_control
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c)) :
    WholeMomentProfileControl (momentModels K c) := by
  exact Moments.UniformAmplify.actual_source_profile_control K c

/-- Actual allowed-symbol quadratic sieve, with arbitrary independent
column coefficients and common-prime zeros. -/
def QuadraticSieveBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X Y : ℝ, 1 ≤ X → 1 ≤ Y →
    ∀ A B : Finset (ExteriorIdeal K (places K c)),
      (∀ I ∈ A, Squarefree I.val.val ∧ exteriorNorm K (places K c) I ≤ X) →
      (∀ J ∈ B, Squarefree J.val.val ∧ exteriorNorm K (places K c) J ≤ Y) →
      ∀ z : ExteriorIdeal K (places K c) → ℂ,
        ∑ I ∈ A, ‖∑ J ∈ B, z J *
          idealSymbol K (places K c) (probeData K c).arithmetic J
            ((probeData K c).arithmetic.generator I) ^ 3‖ ^ 2 ≤
          C * (X * Y) ^ ε * (X + Y) * ∑ J ∈ B, ‖z J‖ ^ 2

def CubicSieveBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X Y : ℝ, 1 ≤ X → 1 ≤ Y →
    ∀ A B : Finset (ExteriorIdeal K (places K c)),
      (∀ I ∈ A, Squarefree I.val.val ∧ exteriorNorm K (places K c) I ≤ X) →
      (∀ J ∈ B, Squarefree J.val.val ∧ exteriorNorm K (places K c) J ≤ Y) →
      ∀ e : ℤ, (e = 2 ∨ e = -2) → ∀ z : ExteriorIdeal K (places K c) → ℂ,
        ∑ I ∈ A, ‖∑ J ∈ B, z J *
          idealSymbol K (places K c) (probeData K c).arithmetic J
            ((probeData K c).arithmetic.generator I) ^ e‖ ^ 2 ≤
          C * (X * Y) ^ ε * (X + Y + (X * Y) ^ (2 / 3 : ℝ)) *
            ∑ J ∈ B, ‖z J‖ ^ 2

-- MI-M-QUADRATIC-SIEVE | §4.3,(4.12),pp20–21.
-- Axiom's Goldmakher–Louvel sieve for the actual Kummer quadratic family of the
-- same arithmetic context (HeckeAxiom.QuadraticSieve).
theorem moment_quadratic_sieve : QuadraticSieveBound K c :=
  HeckeAxiom.quadratic_sieve_bound (axiomChoice K c)

-- MI-M-CUBIC-SIEVE | Lemma4.5,(4.13),p21. Proved by Codex in CubicSieve/ (BGL n = 3).
-- Includes exact BGL/ray-class comparison, not an unspecified cubic family.
theorem moment_cubic_sieve : CubicSieveBound K c := by
  change CubicSieve.ExteriorSieve.TargetBound K (places K c)
    (probeData K c).arithmetic
  exact CubicSieve.Complete.targetBound (axiomChoice K c).A
    (probeData K c).arithmetic (allowedGenerators K c)

variable {K c}
abbrev markedModelEnergy (M : SourceMomentModels K c) {Z T}
    (i : SourceMomentIndex K c Z T) : ℝ := markedModelEnergyFor M i
abbrev pairedModelEnergy (M : SourceMomentModels K c) {Z T}
    (i : SourceMomentIndex K c Z T) : ℝ := pairedModelEnergyFor M i
abbrev amplifiedModelEnergy (M : SourceMomentModels K c) {Z T}
    (i : SourceMomentIndex K c Z T) : ℝ := amplifiedModelEnergyFor M i

/-- Constants are for the ENTIRE actual index/profile family. Height order
and ceiling precede tau; threshold and scalar may depend on that fixed tau. -/
abbrev UniformMomentBound
    (E power : ∀ Z T, SourceMomentIndex K c Z T → ℝ)
    (eligible : ∀ Z T, SourceMomentIndex K c Z T → Prop) : Prop :=
  UniformMomentBoundFor E power eligible

/-- Transport from the correct dyadic row exponent to the source exponent
costs exactly the constant 2.  Height order and ceiling stay unchanged. -/
theorem uniformMomentBound_repaired_power
    (E : ∀ Z T, SourceMomentIndex K c Z T → ℝ)
    (eligible : ∀ Z T, SourceMomentIndex K c Z T → Prop)
    (h : UniformMomentBound E
      (fun _ _ i => momentRowExponent (momentBase i)) eligible) :
    UniformMomentBound E (fun _ _ _ => 1) eligible := by
  obtain ⟨A, ceiling, hA, hc, hb⟩ := h
  refine ⟨A, ceiling, hA, hc, ?_⟩
  intro τ hτ hτc
  obtain ⟨Z₀, k, hZ₀, hk, hbound⟩ := hb τ hτ hτc
  refine ⟨Z₀, 2 * k, hZ₀, mul_nonneg (by norm_num) hk, ?_⟩
  intro Z hZ i hlive heligible
  have hU : 1 < momentBase i := lt_of_lt_of_le (by norm_num) (momentBase_ge_two i)
  have hh := hbound Z hZ i hlive heligible
  change E Z (Z ^ τ) i ≤ k *
    (momentBase i) ^ (momentRowExponent (momentBase i) + c.family.lamA) *
      (1 + Z ^ τ) ^ A at hh
  rw [momentRowExponent, if_pos hU] at hh
  exact _root_.ExpansionRecipe.repaired_moment_bound hU hh

abbrev StrictUnmarkedMomentBound (M : SourceMomentModels K c) : Prop :=
  StrictUnmarkedMomentBoundFor M

abbrev CanonicalInverseModelBounds (M : SourceMomentModels K c) : Prop :=
  CanonicalInverseModelBoundsFor M

abbrev SixthPowerMaskIdentity (M : SourceMomentModels K c) : Prop :=
  SixthPowerMaskIdentityFor M

abbrev AmplifiedIndependentMomentBound (M : SourceMomentModels K c) : Prop :=
  AmplifiedIndependentMomentBoundFor M

variable (K c)
-- OBLIGATION MI-I-CANONICAL-RECURSION | Lemma4.8,Prop4.10,Thm4.1,pp23–28.
-- COARSE analytic/arithmetic proof: two true Poisson transforms, child
-- masks/labels/fixed-triple fibers, prefactor and strict margins, finite
-- termination; must not be replaced by an assumed MIInput or row bound.
theorem canonical_inverse_models
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c))
    (hrows : SourceRowEligibility (momentModels K c))
    (hprofiles : WholeMomentProfileControl (momentModels K c))
    (hquadratic : QuadraticSieveBound K c) (hcubic : CubicSieveBound K c)
    (hreflection : MarkedCoefficientReflectionInput K (places K c)
      (probeData K c).arithmetic (finiteMellinData K c)
      (thetaPeriod K (places K c) (probeData K c) (targetCharacter K c))) :
    CanonicalInverseModelBounds (momentModels K c) := by
  sorry

-- OBLIGATION MI-I-SIXTH-POWER-ZEROS | Lemma5.1,(5.2),(5.3),pp35–36.
theorem inverse_sixth_power_masks
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c)) :
    SixthPowerMaskIdentity (momentModels K c) := by
  exact Moments.UniformAmplify.recipeMomentModels_sixthPowerMasks (expansionRecipeRaw K c)

-- OBLIGATION MI-I-INDEPENDENT-AMPLIFICATION | Lemma5.1,pp35–36.
-- Includes multiplier ideal count and injective(u,a)->u*a^6. U,D and the
-- physical/plain/inverse height vector remain independent after constants.
theorem inverse_independent_amplification
    (hmi : CanonicalInverseModelBounds (momentModels K c))
    (hmask : SixthPowerMaskIdentity (momentModels K c))
    (hprofiles : WholeMomentProfileControl (momentModels K c)) :
    AmplifiedIndependentMomentBound (momentModels K c) := by
  exact Moments.UniformAmplify.recipe_inverse_independent_amplification
    (expansionRecipeRaw K c) hmi.unmarked_strict

-- OBLIGATION MI-I-AMPLIFIED-WITNESS-CALIBRATION | (5.4),(7.6),pp36,43.
-- Choose the preliminary strict margin and epsilon from the actual
-- bounded witness lengths/loss, retaining the row-local profiles.
theorem inverse_amplified_witness_models
    (hamp : AmplifiedIndependentMomentBound (momentModels K c))
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c))
    (hrows : SourceRowEligibility (momentModels K c))
    (hprofiles : WholeMomentProfileControl (momentModels K c)) :
    UniformMomentBound
      (fun _ _ i => amplifiedModelEnergy (momentModels K c) i)
      (fun _ _ i => amplifiedInverseExponent (momentWitness i).inverseLength)
      (fun _ _ _ => True) := by
  exact Moments.UniformAmplify.actual_inverse_amplified_witness_models hamp

/-- These are inequalities for the ACTUAL selected finite prime products,
not arbitrary sublists in P. At kappa1 no zero-free premise is supplied. -/
abbrev PairedPrimeProductBound (M : SourceMomentModels K c) (κ : ℝ) : Prop :=
  PairedPrimeProductBoundFor M κ

-- OBLIGATION MI-P-PRIME-CANCELLATION-BELOW-ONE | §4.6,(4.38),p29.
-- Actual finite-character log derivative and smooth prime Mellin estimate.
theorem paired_primes_below_one
    (hB : c.family.B < 1)
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c))
    (hrows : SourceRowEligibility (momentModels K c))
    (hprofiles : WholeMomentProfileControl (momentModels K c)) :
    PairedPrimeProductBound K c (momentModels K c) (2 * c.family.B - 1) := by
  sorry

-- OBLIGATION MI-P-PRIME-ABSOLUTE-ENDPOINT | §4.6,p29.
-- Existing partial migration: ActualPrimeGeometryAbsoluteBound and
-- ActualPairedSlotRemoval; those do not prove the fourth-moment recursion.
theorem paired_primes_endpoint
    (hB : c.family.B = 1)
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c))
    (hrows : SourceRowEligibility (momentModels K c))
    (hprofiles : WholeMomentProfileControl (momentModels K c)) :
    PairedPrimeProductBound K c (momentModels K c) 1 := by
  sorry

-- OBLIGATION MI-P-ZERO-SLOT | Thm4.2 z=0,Lemma4.11,pp17–18,29–33.
-- Unrestricted bounded plain lengths; only actual nonprincipal character
-- excluded. Same-mask equal-product residues cancel before absolute values.
theorem paired_zero_slot_models
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c))
    (hrows : SourceRowEligibility (momentModels K c))
    (hprofiles : WholeMomentProfileControl (momentModels K c))
    (hquadratic : QuadraticSieveBound K c) :
    UniformMomentBound
      (fun _ _ i => pairedModelEnergy (momentModels K c) i.noSlots)
      (fun _ _ i => momentRowExponent (momentBase i)) (fun _ _ _ => True) := by
  sorry

-- OBLIGATION MI-P-POSITIVE-SLOTS-BELOW-ONE | Thm4.2,§4.8,pp17–18,30–33.
-- COARSE full recursive proof: whole centered coefficient, complete
-- nonprimitive correlations, amplifier pool and valuations1/6/7, child
-- support/capacity ledger, exceptional new rows, strict width termination.
theorem paired_positive_below_one
    (hB : c.family.B < 1)
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c))
    (hrows : SourceRowEligibility (momentModels K c))
    (hprofiles : WholeMomentProfileControl (momentModels K c))
    (hquadratic : QuadraticSieveBound K c)
    (hprime : PairedPrimeProductBound K c (momentModels K c) (2 * c.family.B - 1)) :
    UniformMomentBound
      (fun _ _ i => pairedModelEnergy (momentModels K c) i)
      (fun _ _ i => momentRowExponent (momentBase i))
      (fun _ _ i => pairedCapacity i ∧ i.selected.Nonempty) := by
  sorry

-- OBLIGATION MI-P-POSITIVE-SLOTS-ENDPOINT | Thm4.2,§4.8,pp17–18,30–33.
-- Exact kappa1 capacity; no hidden finite-order seven-eighths theorem.
theorem paired_positive_endpoint
    (hB : c.family.B = 1)
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c))
    (hrows : SourceRowEligibility (momentModels K c))
    (hprofiles : WholeMomentProfileControl (momentModels K c))
    (hquadratic : QuadraticSieveBound K c)
    (hprime : PairedPrimeProductBound K c (momentModels K c) 1) :
    UniformMomentBound
      (fun _ _ i => pairedModelEnergy (momentModels K c) i)
      (fun _ _ i => momentRowExponent (momentBase i))
      (fun _ _ i => pairedCapacity i ∧ i.selected.Nonempty) := by
  sorry

variable {K c}
abbrev physicalInverseEnergy {Z T} (i : SourceMomentIndex K c Z T) : ℝ :=
  physicalInverseEnergyFor i
abbrev physicalPlainEnergy {Z T} (i : SourceMomentIndex K c Z T) : ℝ :=
  physicalPlainEnergyFor i
abbrev physicalUnmarkedEnergy {Z T} (i : SourceMomentIndex K c Z T) : ℝ :=
  physicalUnmarkedEnergyFor i

variable (K c)
-- OBLIGATION MI-M-FINITE-SECTOR-REINDEX | §4.1,§7.1,pp16–18,43.
-- Uses actual pointwise calibration,
-- original pairedRows eligibility and injective(ideal,sector), no final
-- energy estimate. All sectors are summed rather than discarded.
theorem moment_finite_sector_reindex
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c))
    (hrows : SourceRowEligibility (momentModels K c)) :
    ∀ Z T (i : SourceMomentIndex K c Z T),
      physicalInverseEnergy i ≤ markedModelEnergy (momentModels K c) i ∧
      physicalPlainEnergy i ≤ pairedModelEnergy (momentModels K c) i ∧
      physicalUnmarkedEnergy i ≤ amplifiedModelEnergy (momentModels K c) i := by
  exact Moments.UniformAmplify.source_moment_finite_sector_reindex
    (momentModels K c) hcal hrows

variable {K c}

/-- Elementary common-constant plumbing for two actual energy families. -/
theorem uniformMomentBound_join
    (E F p q : ∀ Z T, SourceMomentIndex K c Z T → ℝ)
    (P Q : ∀ Z T, SourceMomentIndex K c Z T → Prop)
    (hE : UniformMomentBound E p P) (hF : UniformMomentBound F q Q) :
    ∃ A ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ ceiling → ∃ Z₀ k : ℝ, 1 ≤ Z₀ ∧ 0 ≤ k ∧
        ∀ Z : ℝ, Z₀ ≤ Z → ∀ i : SourceMomentIndex K c Z (Z ^ τ),
          51 / 100 < (momentBlock i).bin →
          (P Z (Z ^ τ) i → E Z (Z ^ τ) i ≤
            k * momentBase i ^ (p Z (Z ^ τ) i + c.family.lamA) * (1 + Z ^ τ) ^ A) ∧
          (Q Z (Z ^ τ) i → F Z (Z ^ τ) i ≤
            k * momentBase i ^ (q Z (Z ^ τ) i + c.family.lamA) * (1 + Z ^ τ) ^ A) := by
  obtain ⟨A₁, H₁, hA₁, hH₁, hb₁⟩ := hE
  obtain ⟨A₂, H₂, hA₂, hH₂, hb₂⟩ := hF
  refine ⟨max A₁ A₂, min H₁ H₂, hA₁.trans (le_max_left _ _), lt_min hH₁ hH₂, ?_⟩
  intro τ hτ hτH
  obtain ⟨Z₁, k₁, hZ₁, hk₁, he⟩ := hb₁ τ hτ (hτH.trans (min_le_left _ _))
  obtain ⟨Z₂, k₂, hZ₂, hk₂, hf⟩ := hb₂ τ hτ (hτH.trans (min_le_right _ _))
  refine ⟨max Z₁ Z₂, max k₁ k₂, hZ₁.trans (le_max_left _ _),
    hk₁.trans (le_max_left _ _), ?_⟩
  intro Z hZ i hbin
  have hZ₁' : Z₁ ≤ Z := (le_max_left _ _).trans hZ
  have hZ₂' : Z₂ ≤ Z := (le_max_right _ _).trans hZ
  have hZn : 0 ≤ Z := zero_le_one.trans (hZ₁.trans hZ₁')
  have hT : 1 ≤ 1 + Z ^ τ := by linarith [Real.rpow_nonneg hZn τ]
  have hU : 0 ≤ momentBase i := Real.rpow_nonneg hZn _
  have raise (k A r x : ℝ) (hk : 0 ≤ k) (hkk : k ≤ max k₁ k₂)
      (hAA : A ≤ max A₁ A₂)
      (hx : x ≤ k * momentBase i ^ r * (1 + Z ^ τ) ^ A) :
      x ≤ max k₁ k₂ * momentBase i ^ r * (1 + Z ^ τ) ^ max A₁ A₂ := by
    apply hx.trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right hkk (Real.rpow_nonneg hU _)
    · exact Real.rpow_le_rpow_of_exponent_le hT hAA
    · exact Real.rpow_nonneg (zero_le_one.trans hT) _
    · exact mul_nonneg (hk₁.trans (le_max_left _ _)) (Real.rpow_nonneg hU _)
  constructor
  · intro hi
    exact raise k₁ A₁ _ _ hk₁ (le_max_left _ _) (le_max_left _ _) (he Z hZ₁' i hbin hi)
  · intro hi
    exact raise k₂ A₂ _ _ hk₂ (le_max_right _ _) (le_max_right _ _) (hf Z hZ₂' i hbin hi)

variable (K c)

/-- Actual ISource assembled from literal marked and amplified ideal energies. -/
theorem inverseSource :
    ISource c.geometry (targetData K c) c.family.lamA := by
  have hcal := moment_polynomial_calibration K c
  have hrows := moment_row_eligibility K c hcal
  have hprofiles := moment_profile_control K c hcal
  have hmi := canonical_inverse_models K c hcal hrows hprofiles
    (moment_quadratic_sieve K c) (moment_cubic_sieve K c) (markedReflection K c)
  have hamp := inverse_independent_amplification K c hmi
    (inverse_sixth_power_masks K c hcal) hprofiles
  have hw := inverse_amplified_witness_models K c hamp hcal hrows hprofiles
  have hreindex := moment_finite_sector_reindex K c hcal hrows
  have hmarked := uniformMomentBound_repaired_power
    (fun _ _ i => markedModelEnergy (momentModels K c) i)
    (fun _ _ i => inverseCapacity i) hmi.marked
  obtain ⟨A, H, hA, hH, hb⟩ := uniformMomentBound_join
    (fun _ _ i => markedModelEnergy (momentModels K c) i)
    (fun _ _ i => amplifiedModelEnergy (momentModels K c) i)
    (fun _ _ _ => 1)
    (fun _ _ i => amplifiedInverseExponent (momentWitness i).inverseLength)
    (fun _ _ i => inverseCapacity i) (fun _ _ _ => True) hmarked hw
  refine ⟨A, H, hA, hH, ?_⟩
  intro τ hτ hτH
  obtain ⟨Z₀, k, hZ₀, hk, hbound⟩ := hb τ hτ hτH
  refine ⟨Z₀, k, hZ₀, hk, ?_⟩
  intro Z hZ b hbin ℓ t ht ht' j
  constructor
  · intro I h₁ h₂
    let i : SourceMomentIndex K c Z (Z ^ τ) := ⟨b, ℓ, t, ht, ht', j, I⟩
    exact (hreindex Z (Z ^ τ) i).1.trans
      ((hbound Z hZ i hbin).1 ⟨h₁, h₂⟩)
  · let i : SourceMomentIndex K c Z (Z ^ τ) := ⟨b, ℓ, t, ht, ht', j, ∅⟩
    exact (hreindex Z (Z ^ τ) i).2.2.trans
      ((hbound Z hZ i hbin).2 trivial)

/-- Actual PSource assembled with an explicit B<1 / B=1 split and the
unrestricted zero-slot energy. The old capped PRegion is absent. -/
theorem plainSource :
    PSource c.geometry (targetData K c) c.family.B c.family.lamA
      (momentMesh K c.family).val := by
  have hcal := moment_polynomial_calibration K c
  have hrows := moment_row_eligibility K c hcal
  have hprofiles := moment_profile_control K c hcal
  have hquad := moment_quadratic_sieve K c
  have hpositive_raw : UniformMomentBound
      (fun _ _ i => pairedModelEnergy (momentModels K c) i)
      (fun _ _ i => momentRowExponent (momentBase i))
      (fun _ _ i => pairedCapacity i ∧ i.selected.Nonempty) := by
    rcases lt_or_eq_of_le c.family.B_upper with hB | hB
    · exact paired_positive_below_one K c hB hcal hrows hprofiles hquad
        (paired_primes_below_one K c hB hcal hrows hprofiles)
    · exact paired_positive_endpoint K c hB hcal hrows hprofiles hquad
        (paired_primes_endpoint K c hB hcal hrows hprofiles)
  have hpositive := uniformMomentBound_repaired_power
    (fun _ _ i => pairedModelEnergy (momentModels K c) i)
    (fun _ _ i => pairedCapacity i ∧ i.selected.Nonempty) hpositive_raw
  have hzero := uniformMomentBound_repaired_power
    (fun _ _ i => pairedModelEnergy (momentModels K c) i.noSlots)
    (fun _ _ _ => True) (paired_zero_slot_models K c hcal hrows hprofiles hquad)
  have hreindex := moment_finite_sector_reindex K c hcal hrows
  obtain ⟨A, H, hA, hH, hb⟩ := uniformMomentBound_join
    (fun _ _ i => pairedModelEnergy (momentModels K c) i)
    (fun _ _ i => pairedModelEnergy (momentModels K c) i.noSlots)
    (fun _ _ _ => 1) (fun _ _ _ => 1)
    (fun _ _ i => pairedCapacity i ∧ i.selected.Nonempty)
    (fun _ _ _ => True) hpositive hzero
  refine ⟨A, H, hA, hH, ?_⟩
  intro τ hτ hτH
  obtain ⟨Z₀, k, hZ₀, hk, hbound⟩ := hb τ hτ hτH
  refine ⟨Z₀, k, hZ₀, hk, ?_⟩
  intro Z hZ b hbin ℓ t ht ht' j
  constructor
  · intro I hmesh hcap
    let i : SourceMomentIndex K c Z (Z ^ τ) := ⟨b, ℓ, t, ht, ht', j, I⟩
    by_cases hI : I.Nonempty
    · exact (hreindex Z (Z ^ τ) i).2.1.trans
        ((hbound Z hZ i hbin).1 ⟨⟨hmesh, hcap⟩, hI⟩)
    · have hIempty : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
      subst I
      exact (hreindex Z (Z ^ τ) i).2.1.trans
        ((hbound Z hZ i hbin).2 trivial)
  · let i : SourceMomentIndex K c Z (Z ^ τ) := ⟨b, ℓ, t, ht, ht', j, ∅⟩
    have hh := (hreindex Z (Z ^ τ) i).2.1.trans ((hbound Z hZ i hbin).2 trivial)
    simpa only [i, physicalPlainEnergy, physicalPlainEnergyFor,
      SourceMomentIndex.noSlots, SourceMomentIndexFor.noSlots,
      momentWitness, momentWitnessFor, momentAmplitude, momentAmplitudeFor,
      momentBlock, momentBlockFor, momentBase, momentBaseFor,
      actualMomentSourceData, recipeMomentSourceData, targetData, highExpansion,
      momentRowCharacters,
      Finset.prod_empty, mul_one] using hh

end HeckeSkeleton
