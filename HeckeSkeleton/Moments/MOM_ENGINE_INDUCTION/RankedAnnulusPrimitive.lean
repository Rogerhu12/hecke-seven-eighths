import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RankedAnnulus
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ClippedAnnulusSchedule
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ReflectionPrimitiveFamily

/-!
# Literal reflection closure for the finite annulus schedule

The support part of a profile bound is recorded separately while a
genuine normalized reflection child is constructed. The replaced plain
profile is the actual fixed power window, supported in [1/2,2]; the
other plain profile, inverse profile and all prime windows retain their
original supports. Positive scalar normalization preserves those
supports exactly.

The rank-dependent primitive below combines that literal support with
the already established unit seminorm estimate. Its projection to the
single maximal annulus feeds the existing analytic reflection producer.
The transfer back to the child's own annulus is proved here from the
actual child definition and the actual rank decrease. No transformed
support, parent energy, local reduction or child moment estimate is an
additional primitive field.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.Moments.UniformAmplify
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {theta : Finset (HeckeCharacter K)}

/-- A support fact about the literal profiles at their actual evaluation
time. It contains neither derivative bounds nor an energy estimate. -/
def ModelProfileSupport (d : MomentData K ω ψ) (lower upper : ℝ) : Prop :=
  ∀ q : ModelProfileIndex d,
    Function.support (modelProfile d q) ⊆ Icc lower upper

theorem modelProfileControl_support {d : MomentData K ω ψ} {J : ℕ}
    {A C H lower upper T : ℝ}
    (h : ModelProfileControl d J A C H lower upper T) :
    ModelProfileSupport d lower upper := fun q => (h q).2.1

/-- A proved tighter support can replace the support clause without
altering the function, Euler order, weighted seminorm or constants. -/
theorem modelProfileControl_with_support {d : MomentData K ω ψ} {J : ℕ}
    {A C H lower upper lower' upper' T : ℝ}
    (h : ModelProfileControl d J A C H lower upper T)
    (hsupport : ModelProfileSupport d lower' upper') :
    ModelProfileControl d J A C H lower' upper' T :=
  fun q => ⟨(h q).1, hsupport q, (h q).2.2⟩

theorem modelProfileSupport_mono {d : MomentData K ω ψ}
    {lower upper lower' upper' : ℝ}
    (h : ModelProfileSupport d lower upper)
    (hinterval : Icc lower upper ⊆ Icc lower' upper') :
    ModelProfileSupport d lower' upper' := fun q => (h q).trans hinterval

/-- Every kind of actual profile retains its support under the positive
normalization used by the ordinary reflection operator. -/
theorem modelProfileSupport_scaled {d : MomentData K ω ψ}
    {lower upper : ℝ} (h : ModelProfileSupport d lower upper)
    (scalar : ℝ) (hscalar : 0 < scalar) :
    ModelProfileSupport (scaledMomentProfiles d scalar hscalar) lower upper := by
  intro q
  cases q with
  | inverse u =>
    change Function.support ((scaledIdealTest d.inverseTest scalar hscalar).profile u 0) ⊆ _
    rw [scaledIdealTest_profile_support]
    exact h (.inverse u)
  | plain₁ u =>
    change Function.support ((scaledIdealTest d.plainTest₁ scalar hscalar).profile u 0) ⊆ _
    rw [scaledIdealTest_profile_support]
    exact h (.plain₁ u)
  | plain₂ u =>
    change Function.support ((scaledIdealTest d.plainTest₂ scalar hscalar).profile u 0) ⊆ _
    rw [scaledIdealTest_profile_support]
    exact h (.plain₂ u)
  | prime j =>
    change Function.support ((scaledPrimeWindow (d.geometry.slots j) scalar hscalar).profile 0) ⊆ _
    rw [scaledPrimeWindow_profile_support]
    exact h (.prime j)

/-- The new plain test has the proved [1/2,2] support of the literal
power window; every other profile is unchanged. -/
theorem ordinaryPowerChild_profileSupport {d : MomentData K ω ψ}
    {lower upper : ℝ} (h : ModelProfileSupport d lower upper)
    (hwindow : Icc (1 / 2 : ℝ) 2 ⊆ Icc lower upper)
    (first : Bool) (sigma frequency : ℝ) :
    ModelProfileSupport (ordinaryPowerChild K d first sigma frequency) lower upper := by
  have hnew : Function.support (ordinaryPowerWindow sigma frequency) ⊆ Icc lower upper :=
    (ordinaryPowerWindow_support sigma frequency).trans hwindow
  intro q
  cases q with
  | inverse u => exact h (.inverse u)
  | plain₁ u =>
    cases first with
    | false => exact h (.plain₁ u)
    | true =>
      simpa only [modelProfile, ordinaryPowerChild, eq_self, ite_true,
        IdealTest.freezeTwist, ordinaryPowerWindowIdealTest, profilePower_zero,
        mul_one] using hnew
  | plain₂ u =>
    cases first with
    | false =>
      simpa only [modelProfile, ordinaryPowerChild, Bool.false_eq_true, ite_false,
        IdealTest.freezeTwist, ordinaryPowerWindowIdealTest, profilePower_zero,
        mul_one] using hnew
    | true => exact h (.plain₂ u)
  | prime j => exact h (.prime j)

theorem normalizedOrdinaryPowerChild_profileSupport {d : MomentData K ω ψ}
    {lower upper : ℝ} (h : ModelProfileSupport d lower upper)
    (hwindow : Icc (1 / 2 : ℝ) 2 ⊆ Icc lower upper)
    (first : Bool) (sigma frequency E0 : ℝ) (hE0 : 1 ≤ E0) (J : ℕ) :
    ModelProfileSupport
      (normalizedOrdinaryPowerChild d first sigma frequency E0 hE0 J) lower upper :=
  modelProfileSupport_scaled (ordinaryPowerChild_profileSupport h hwindow first sigma frequency)
    _ _

theorem Node.fixedLineReflectionChild_profileSupport (parent : Node K ω ψ)
    {lower upper : ℝ} (h : ModelProfileSupport parent.data lower upper)
    (hwindow : Icc (1 / 2 : ℝ) 2 ⊆ Icc lower upper)
    (first : Bool) (U E0 : ℝ) (hE0 : 1 ≤ E0) (J : ℕ) (x : (ℕ × Bool) × ℝ) :
    ModelProfileSupport (parent.fixedLineReflectionChild first U E0 hE0 J x).data
      lower upper :=
  normalizedOrdinaryPowerChild_profileSupport h hwindow first _ _ E0 hE0 J

/-- Passing to an earlier rank only enlarges its scheduled support.
This weak inclusion does not spend the factor two reserved for strict
Mellin preprocessing. -/
theorem rankedAnnulus_descendant_subset {lower upper : ℝ}
    (hlower : 0 ≤ lower) (hupper : 0 ≤ upper) (N : ℕ) {child parent : ℕ}
    (hearlier : child ≤ parent) :
    Icc (rankedAnnulusLower lower N parent) (rankedAnnulusUpper upper N parent) ⊆
      Icc (rankedAnnulusLower lower N child) (rankedAnnulusUpper upper N child) := by
  have hp : (2 : ℝ) ^ (N - parent) ≤ 2 ^ (N - child) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  intro y hy
  exact ⟨(div_le_div_of_nonneg_left hlower (by positivity) hp).trans hy.1,
    hy.2.trans (mul_le_mul_of_nonneg_left hp hupper)⟩

/-- The derivative order and support annulus use the same genuine
geometric rank. Their schedules are selected before any moving data. -/
def rankedAnnulusProfilePrimitive (ground : ℕ) (engine reflection : ℕ → ℕ)
    (sigma widthLimit padding A P lower upper : ℝ)
    (d : MomentData K ω ψ) (p : PairedInvariantParameters) : Prop :=
  let rank := parameterCoreRank sigma widthLimit padding p.parameters
  let N := 6 * (widthBand sigma widthLimit + 1)
  ModelProfileControl d (backwardProfileOrder ground engine reflection rank) A P 0
    (clippedAnnulusLower lower upper N rank) (rankedAnnulusUpper upper N rank) 0

theorem rankedAnnulusProfilePrimitive_iff (ground : ℕ) (engine reflection : ℕ → ℕ)
    (sigma widthLimit padding A P lower upper : ℝ)
    (d : MomentData K ω ψ) (a : RealParameters) :
    admissibleOfInvariant
      (rankedAnnulusProfilePrimitive ground engine reflection
        sigma widthLimit padding A P lower upper) d a ↔
      ModelProfileControl d (backwardProfileOrder ground engine reflection
        (parameterCoreRank sigma widthLimit padding a)) A P 0
        (clippedAnnulusLower lower upper (6 * (widthBand sigma widthLimit + 1))
          (parameterCoreRank sigma widthLimit padding a))
        (rankedAnnulusUpper upper (6 * (widthBand sigma widthLimit + 1))
          (parameterCoreRank sigma widthLimit padding a)) 0 := by
  unfold admissibleOfInvariant rankedAnnulusProfilePrimitive
  rw [pairedInvariantParameters_coreRank]

/-- The single fixed maximal annulus is sufficient for choosing all
analytic constants, before the current node or its rank is selected. -/
theorem rankedAnnulusProfilePrimitive_maximal
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    {sigma widthLimit padding A P lower upper : ℝ}
    {d : MomentData K ω ψ} {a : RealParameters}
    (hlower : 0 ≤ lower) (hupper : 0 ≤ upper)
    (h : admissibleOfInvariant
      (rankedAnnulusProfilePrimitive ground engine reflection
        sigma widthLimit padding A P lower upper) d a) :
    admissibleOfInvariant
      (rankedProfilePrimitive ground engine reflection sigma widthLimit padding A P
        (lower / clippedAnnulusStep upper (6 * (widthBand sigma widthLimit + 1)) ^
          (6 * (widthBand sigma widthLimit + 1)))
        (upper * (2 : ℝ) ^ (6 * (widthBand sigma widthLimit + 1)))) d a := by
  rw [rankedProfilePrimitive_iff]
  rw [rankedAnnulusProfilePrimitive_iff] at h
  exact modelProfileControl_annulus_mono h
    (clippedAnnulus_maximal_subset hlower hupper _ _)

/-- The literal source at the one maximal Euler order enters its own
rank's support layer directly from the original source annulus. -/
theorem rankedAnnulusProfilePrimitive_of_top
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    {sigma widthLimit padding A P lower upper : ℝ}
    {d : MomentData K ω ψ} {a : RealParameters}
    (hsigma : 0 < sigma) (hwidth : a.m + a.q ≤ widthLimit)
    (hlower : 0 ≤ lower) (hupper : 0 ≤ upper)
    (h : ModelProfileControl d
      (backwardProfileOrder ground engine reflection (6 * (widthBand sigma widthLimit + 1)))
      A P 0 lower upper 0) :
    admissibleOfInvariant
      (rankedAnnulusProfilePrimitive ground engine reflection
        sigma widthLimit padding A P lower upper) d a := by
  rw [rankedAnnulusProfilePrimitive_iff]
  exact modelProfileControl_annulus_mono
    (modelProfileControl_mono_order h
      (backwardProfileOrder_monotone ground engine reflection
        (parameterCoreRank_lt_bound a hsigma hwidth).le))
    (clippedAnnulus_original_subset hlower hupper _ _)

/-- The actual Mellin plateau and actual active clipping fit the
earlier child's scheduled annulus. The finite Schwartz-to-Euler
coefficient is paid by the already fixed source profile budget. -/
theorem rankedAnnulusProfilePrimitive_strictChild
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    {sigma widthLimit padding A P D lower upper : ℝ}
    {parentParameters childParameters : RealParameters}
    {child : MomentData K ω ψ}
    (hlower : 0 ≤ lower) (hupper : 0 < upper) (hDP : D ≤ P)
    (hparent : parameterCoreRank sigma widthLimit padding parentParameters ≤
      6 * (widthBand sigma widthLimit + 1))
    (hearlier : parameterCoreRank sigma widthLimit padding childParameters <
      parameterCoreRank sigma widthLimit padding parentParameters)
    (hchild : ModelProfileControl child
      (backwardProfileOrder ground engine reflection
        (parameterCoreRank sigma widthLimit padding parentParameters - 1)) A D 0
      ((clippedAnnulusLower lower upper (6 * (widthBand sigma widthLimit + 1))
          (parameterCoreRank sigma widthLimit padding parentParameters) / 2) /
        (2 * rankedAnnulusUpper upper (6 * (widthBand sigma widthLimit + 1))
          (parameterCoreRank sigma widthLimit padding parentParameters)))
      (2 * rankedAnnulusUpper upper (6 * (widthBand sigma widthLimit + 1))
        (parameterCoreRank sigma widthLimit padding parentParameters)) 0) :
    admissibleOfInvariant
      (rankedAnnulusProfilePrimitive ground engine reflection
        sigma widthLimit padding A P lower upper) child childParameters := by
  rw [rankedAnnulusProfilePrimitive_iff]
  apply modelProfileControl_mono_budget _ hDP
  apply modelProfileControl_mono_order _
    (backwardProfileOrder_child_le ground engine reflection hearlier)
  exact modelProfileControl_annulus_mono hchild
    (clippedAnnulus_child_enlargement_subset hlower hupper hparent hearlier)

/-- The normalized child's tight support follows from its literal
construction, while its seminorm bound is the actual reflection
producer's unit estimate on the common maximal annulus. -/
theorem rankedAnnulusProfilePrimitive_fixedLine_child
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    {sigma widthLimit padding A P lower upper U : ℝ}
    (parent : Node K ω ψ) (first : Bool) (E0 : ℝ) (hE0 : 1 ≤ E0)
    (x : (ℕ × Bool) × ℝ) (hP : 1 ≤ P)
    (hlower : 0 ≤ lower) (hlowerSmall : lower ≤ 1 / 2) (hupper : 2 ≤ upper)
    (hparent : admissibleOfInvariant
      (rankedAnnulusProfilePrimitive ground engine reflection
        sigma widthLimit padding A P lower upper) parent.data parent.parameters)
    (hearlier :
      parameterCoreRank sigma widthLimit padding
        (parent.fixedLineReflectionChild first U E0 hE0
          (backwardProfileOrder ground engine reflection
            (parameterCoreRank sigma widthLimit padding parent.parameters - 1)) x).parameters <
        parameterCoreRank sigma widthLimit padding parent.parameters)
    (hunit : ModelProfileControl
      (parent.fixedLineReflectionChild first U E0 hE0
        (backwardProfileOrder ground engine reflection
          (parameterCoreRank sigma widthLimit padding parent.parameters - 1)) x).data
      (backwardProfileOrder ground engine reflection
        (parameterCoreRank sigma widthLimit padding parent.parameters - 1)) A 1 0
      (lower / clippedAnnulusStep upper (6 * (widthBand sigma widthLimit + 1)) ^
          (6 * (widthBand sigma widthLimit + 1)))
      (upper * (2 : ℝ) ^ (6 * (widthBand sigma widthLimit + 1))) 0) :
    admissibleOfInvariant
      (rankedAnnulusProfilePrimitive ground engine reflection
        sigma widthLimit padding A P lower upper)
      (parent.fixedLineReflectionChild first U E0 hE0
        (backwardProfileOrder ground engine reflection
          (parameterCoreRank sigma widthLimit padding parent.parameters - 1)) x).data
      (parent.fixedLineReflectionChild first U E0 hE0
        (backwardProfileOrder ground engine reflection
          (parameterCoreRank sigma widthLimit padding parent.parameters - 1)) x).parameters := by
  rw [rankedAnnulusProfilePrimitive_iff] at hparent ⊢
  have hsupport := parent.fixedLineReflectionChild_profileSupport
    (modelProfileControl_support hparent)
    (clippedAnnulus_reflection_subset hlower hlowerSmall hupper _ _)
    first U E0 hE0
    (backwardProfileOrder ground engine reflection
      (parameterCoreRank sigma widthLimit padding parent.parameters - 1)) x
  have hchildSupport := modelProfileSupport_mono hsupport
    (clippedAnnulus_descendant_subset hlower (by linarith) _ hearlier.le)
  exact modelProfileControl_mono_budget
    (normalized_child_rank_profile_control ground engine reflection hearlier
      (modelProfileControl_with_support hunit hchildSupport)) hP

/-- Actual arithmetic calibration and the ranked annulus profile
control remain separate visible parts of primitive admissibility. -/
def reflectionRankedAnnulusPrimitive
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (probe : ProbeData K S) (rows : RowCharacterInput K S probe)
    (theta : Finset (HeckeCharacter K)) (U : ℝ)
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    (sigma widthLimit padding A P lower upper : ℝ)
    (d : MomentData K ω ψ) (p : PairedInvariantParameters) : Prop :=
  reflectionArithmeticPrimitive S probe rows theta U d p ∧
    rankedAnnulusProfilePrimitive ground engine reflection
      sigma widthLimit padding A P lower upper d p

/-- The already proved literal support closure instantiates the genuine
reflection factory's primitive callback; no support premise is added
to that factory or to the final source theorem. -/
theorem reflectionRankedAnnulusPrimitive_transfer
    {S : Set (HeightOneSpectrum (𝓞 K))} [Fintype S]
    {probe : ProbeData K S} {rows : RowCharacterInput K S probe} {U : ℝ}
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    {sigma widthLimit padding A P lower upper : ℝ}
    (parent : Node K ω ψ) (E0 : ℝ) (hE0 : 1 ≤ E0) (hP : 1 ≤ P)
    (hlower : 0 ≤ lower) (hlowerSmall : lower ≤ 1 / 2) (hupper : 2 ≤ upper)
    (hparent : admissibleOfInvariant
      (reflectionRankedAnnulusPrimitive S probe rows theta U ground engine reflection
        sigma widthLimit padding A P lower upper) parent.data parent.parameters) :
    ReflectionPrimitiveTransfer
      (reflectionRankedAnnulusPrimitive S probe rows theta U ground engine reflection
        sigma widthLimit padding A P lower upper)
      sigma widthLimit padding A
      (lower / clippedAnnulusStep upper (6 * (widthBand sigma widthLimit + 1)) ^
          (6 * (widthBand sigma widthLimit + 1)))
      (upper * (2 : ℝ) ^ (6 * (widthBand sigma widthLimit + 1))) U E0 hE0
      (backwardProfileOrder ground engine reflection
        (parameterCoreRank sigma widthLimit padding parent.parameters - 1)) parent := by
  intro x child hunit harithmetic hearlier
  exact ⟨reflectionArithmeticPrimitive_of_preserved harithmetic hparent.1,
    rankedAnnulusProfilePrimitive_fixedLine_child ground engine reflection parent
      (reflectionLongFirst parent.parameters) E0 hE0 x hP hlower hlowerSmall hupper
      hparent.2 hearlier hunit⟩

end HeckeSkeleton.Moments.EngineInduction
