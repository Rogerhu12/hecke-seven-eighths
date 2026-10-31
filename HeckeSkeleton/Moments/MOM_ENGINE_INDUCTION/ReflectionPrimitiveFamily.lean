import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RankedProfileControl
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ReflectionChildGeometry
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.UniversalReflectionBranches

/-!
# Actual arithmetic and profile closure of ordinary reflection

The ordinary-reflection part of primitive admissibility consists of a
genuine remaining ideal, complete-mask identity, exterior row/character
calibration, the joint norm budget, non-norm-twist exclusion, and the
finite rank's actual profile control. All these properties are proved
for the literal reflected children from the original parent facts.

This is only the ordinary-reflection portion of the final primitive
family. The strict two-transform theorem must additionally supply its
actual source dictionaries and mixed-row regularity. In particular,
arbitrary rowwise profile control is not asserted to be a canonical
Poisson source, and no energy estimate is an admissibility field.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.Moments.UniformAmplify
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- The representative is used solely for predicates depending on the
invariant numerical parameters; it never replaces the actual energy. -/
def Node.invariantRepresentative (n : Node K ω ψ) : Node K ω ψ :=
  Node.ordinary n.data (pairedInvariantParameters n.parameters).parameters

theorem Node.invariantRepresentative_arithmetic (n : Node K ω ψ) (U : ℝ) :
    ReflectionArithmeticPreserved n n.invariantRepresentative U :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ReflectionArithmeticPreserved.representatives
    {parent child : Node K ω ψ} {U : ℝ}
    (h : ReflectionArithmeticPreserved parent child U) :
    ReflectionArithmeticPreserved parent.invariantRepresentative child.invariantRepresentative U :=
  ⟨h.rows, h.rowCharacter, h.plainBackground, h.theta, h.commonMask, h.width⟩

/-- The full original mask and the joint remaining-ideal budget are
retained. The remaining ideal is actual primitive data, not a norm-only
surrogate or an extra small loss exponent. -/
def reflectionArithmeticPrimitive
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (probe : ProbeData K S) (rows : RowCharacterInput K S probe) (U : ℝ)
    (d : MomentData K ω ψ) (p : PairedInvariantParameters) : Prop :=
  ∃ extra : NonzeroIdeal K → NonzeroIdeal K,
    ReflectionRowCalibration S probe rows (Node.ordinary d p.parameters) extra U ∧
    (∀ u I, d.commonMask u I =
      (completeIdealCommonMask K S u I && decide (IsCoprime I (extra u).val))) ∧
    (∀ u ∈ pairedRows d p.parameters U, ∀ t : ℝ,
      d.plainBackground * d.rowCharacter u ≠ heckeNormTwist K t)

/-- Arithmetic closure is an actual transport of the same complete
mask, row characters and remaining ideal. -/
theorem reflectionArithmeticPrimitive_of_preserved
    {S : Set (HeightOneSpectrum (𝓞 K))} [Fintype S]
    {probe : ProbeData K S} {rows : RowCharacterInput K S probe} {U : ℝ}
    {parent child : Node K ω ψ}
    (h : ReflectionArithmeticPreserved parent child U)
    (hparent : admissibleOfInvariant (reflectionArithmeticPrimitive S probe rows U)
      parent.data parent.parameters) :
    admissibleOfInvariant (reflectionArithmeticPrimitive S probe rows U)
      child.data child.parameters := by
  obtain ⟨extra, hcal, hmask, hnonNorm⟩ := hparent
  exact ⟨extra, h.representatives.calibration hcal,
    h.representatives.remainingMask hmask, h.representatives.nonNorm hnonNorm⟩

/-- The profile and arithmetic portions of the actual reflection family.
They remain separately visible to the canonical source producer. -/
def reflectionProfilePrimitive
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (probe : ProbeData K S) (rows : RowCharacterInput K S probe) (U : ℝ)
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    (σ W padding A P lower upper : ℝ)
    (d : MomentData K ω ψ) (p : PairedInvariantParameters) : Prop :=
  reflectionArithmeticPrimitive S probe rows U d p ∧
    rankedProfilePrimitive ground engine reflection σ W padding A P lower upper d p

/-- The finite derivative loss is paid by the true strict rank decrease.
The only analytic child premise is the already proved unit profile
control at the requested predecessor order, never a child moment bound. -/
theorem reflectionProfilePrimitive_normalized_child
    {S : Set (HeightOneSpectrum (𝓞 K))} [Fintype S]
    {probe : ProbeData K S} {rows : RowCharacterInput K S probe} {U : ℝ}
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    {σ W padding A P lower upper : ℝ} {parent child : Node K ω ψ}
    (hP : 1 ≤ P)
    (hparent : admissibleOfInvariant
      (reflectionProfilePrimitive S probe rows U ground engine reflection
        σ W padding A P lower upper) parent.data parent.parameters)
    (harithmetic : ReflectionArithmeticPreserved parent child U)
    (hearlier : parameterCoreRank σ W padding child.parameters <
      parameterCoreRank σ W padding parent.parameters)
    (hunit : ModelProfileControl child.data
      (backwardProfileOrder ground engine reflection
        (parameterCoreRank σ W padding parent.parameters - 1)) A 1 0 lower upper 0) :
    admissibleOfInvariant
      (reflectionProfilePrimitive S probe rows U ground engine reflection
        σ W padding A P lower upper) child.data child.parameters :=
  ⟨reflectionArithmeticPrimitive_of_preserved harithmetic hparent.1,
    rankedProfilePrimitive_normalized_child ground engine reflection hP hearlier hunit⟩

/-- For the literal fixed-line operator the arithmetic premise above is
proved by the actual construction, with the original remaining ideal. -/
theorem reflectionProfilePrimitive_fixedLine_child
    {S : Set (HeightOneSpectrum (𝓞 K))} [Fintype S]
    {probe : ProbeData K S} {rows : RowCharacterInput K S probe} {U : ℝ}
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    {σ W padding A P lower upper : ℝ} (parent : Node K ω ψ)
    (first : Bool) (E0 : ℝ) (hE0 : 1 ≤ E0)
    (x : (ℕ × Bool) × ℝ) (hP : 1 ≤ P)
    (hparent : admissibleOfInvariant
      (reflectionProfilePrimitive S probe rows U ground engine reflection
        σ W padding A P lower upper) parent.data parent.parameters)
    (hearlier :
      parameterCoreRank σ W padding
        (parent.fixedLineReflectionChild first U E0 hE0
          (backwardProfileOrder ground engine reflection
            (parameterCoreRank σ W padding parent.parameters - 1)) x).parameters <
        parameterCoreRank σ W padding parent.parameters)
    (hunit : ModelProfileControl
      (parent.fixedLineReflectionChild first U E0 hE0
        (backwardProfileOrder ground engine reflection
          (parameterCoreRank σ W padding parent.parameters - 1)) x).data
      (backwardProfileOrder ground engine reflection
        (parameterCoreRank σ W padding parent.parameters - 1)) A 1 0 lower upper 0) :
    admissibleOfInvariant
      (reflectionProfilePrimitive S probe rows U ground engine reflection
        σ W padding A P lower upper)
      (parent.fixedLineReflectionChild first U E0 hE0
        (backwardProfileOrder ground engine reflection
          (parameterCoreRank σ W padding parent.parameters - 1)) x).data
      (parent.fixedLineReflectionChild first U E0 hE0
        (backwardProfileOrder ground engine reflection
          (parameterCoreRank σ W padding parent.parameters - 1)) x).parameters :=
  reflectionProfilePrimitive_normalized_child ground engine reflection hP hparent
    (parent.fixedLineReflectionChild_arithmetic first U E0 hE0 _ x) hearlier hunit

/-- Instantiate the uniform branch factory's primitive transfer with
the actual complete mask, joint norm budget and ranked profiles. -/
theorem reflectionProfilePrimitive_transfer
    {S : Set (HeightOneSpectrum (𝓞 K))} [Fintype S]
    {probe : ProbeData K S} {rows : RowCharacterInput K S probe} {U : ℝ}
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    {σ W padding A P lower upper : ℝ} (parent : Node K ω ψ)
    (E0 : ℝ) (hE0 : 1 ≤ E0) (hP : 1 ≤ P)
    (hparent : admissibleOfInvariant
      (reflectionProfilePrimitive S probe rows U ground engine reflection
        σ W padding A P lower upper) parent.data parent.parameters) :
    ReflectionPrimitiveTransfer
      (reflectionProfilePrimitive S probe rows U ground engine reflection
        σ W padding A P lower upper)
      σ W padding A lower upper U E0 hE0
      (backwardProfileOrder ground engine reflection
        (parameterCoreRank σ W padding parent.parameters - 1)) parent := by
  intro x hunit harithmetic hearlier
  exact reflectionProfilePrimitive_normalized_child ground engine reflection hP hparent
    harithmetic hearlier hunit

namespace Source

variable {c : TargetContext K}
variable (R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
  c.geometry (expansionShellAllowance K c))
variable {Z T : ℝ}
variable (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
variable (s : SixthUnitClasses K (places K c))

/-- The original full model ball supplies the primitive reflection data.
Only the original radial anchor and finite-background exclusion are
required; no physical-row eligibility is substituted for model rows. -/
theorem recipeRoot_reflectionArithmeticPrimitive (w : InfinitePlace K)
    (hψ : heckeRadialParameter K w (targetCharacter K c) = 0)
    (hfinite : ∀ j : Fin R.family.presentationCount,
      FiniteOrder (R.family.presentation j).plainBackground →
        (R.family.presentation j).plainBackground⁻¹ ∈ (R.family.presentation j).theta) :
    admissibleOfInvariant
      (reflectionArithmeticPrimitive (places K c) (probeData K c) (momentRowCharacters K c)
        (momentBaseFor i)) (recipeRoot R i s).data (recipeRoot R i s).parameters := by
  have hp := (recipeRoot R i s).invariantRepresentative_arithmetic (momentBaseFor i)
  exact ⟨fun _ => 1, hp.calibration (recipeRoot_reflectionCalibration R i s),
    hp.remainingMask (recipeRoot_remainingMask R i s),
    hp.nonNorm (recipeRoot_nonNorm R i s w hψ hfinite)⟩

/-- The no-slot entrance has only the original radial-anchor premise;
it does not require an additional finite exceptional-set condition. -/
theorem recipeRoot_noSlots_reflectionArithmeticPrimitive (w : InfinitePlace K)
    (hψ : heckeRadialParameter K w (targetCharacter K c) = 0) :
    admissibleOfInvariant
      (reflectionArithmeticPrimitive (places K c) (probeData K c) (momentRowCharacters K c)
        (momentBaseFor i)) (recipeRoot R i.noSlots s).data
          (recipeRoot R i.noSlots s).parameters := by
  have hp := (recipeRoot R i.noSlots s).invariantRepresentative_arithmetic (momentBaseFor i)
  exact ⟨fun _ => 1, hp.calibration (recipeRoot_noSlots_reflectionCalibration R i s),
    hp.remainingMask (recipeRoot_noSlots_remainingMask R i s),
    hp.nonNorm (recipeRoot_noSlots_nonNorm R i s w hψ)⟩

end Source

end HeckeSkeleton.Moments.EngineInduction
