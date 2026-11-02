import HeckeGeneral.Analysis.MomentInputs
import HeckeGeneral.Characters.InfinityPacket

/-!
# Actual paired rows are not pure norm twists

Ordinary Hecke reflection requires exclusion of every pure norm twist,
whereas the zero-slot row filter only excludes the principal actual
character.  A zero radial parameter at one fixed infinite place bridges
these two conditions.  It does not require the relative radial parameters
at different places to vanish.

For positive slots the actual filter excludes `rowCharacter` from `theta`.
The additional primitive calibration below asks that the inverse plain
background belong to `theta` whenever that background has finite order.
This is precisely the finite-background absorption needed to deduce
nonprincipality of `plainBackground * rowCharacter` from that filter.

All statements retain the original `MomentData`, its exact `pairedRows`,
and the common mask.  No non-norm conclusion or energy estimate is an
input.  The source provider must prove the background normalization and
finite-background absorption for its actual family.  Neither property is
asserted here for the old skeleton's arbitrary packet representative.

Paper: `weil_seven_eighths_revised.tex`, lines 1537--1556 (fixed finite
background and norm-phase separation), 1651--1653 (the two row filters),
886--904 and 3819--3823 (the ordinary reflection non-norm requirement).
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open scoped Classical

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

/-- At a fixed radial anchor, a normalized nonprincipal character cannot
be any pure norm twist.  The sign uses the actual convention
`heckeRadialParameter (heckeNormTwist t) = -t`. -/
theorem radial_zero_ne_normTwist (w : InfinitePlace K) (χ : HeckeCharacter K)
    (hzero : heckeRadialParameter K w χ = 0) (hne : χ ≠ 1) :
    ∀ t : ℝ, χ ≠ heckeNormTwist K t := by
  intro t heq
  have h := hzero
  rw [heq, heckeRadialParameter_normTwist] at h
  have ht : t = 0 := by linarith
  apply hne
  simpa only [ht, heckeNormTwist, normTwist_zero] using heq

/-- The three permitted plain backgrounds all inherit the same single
radial anchor from the actual target representative. -/
theorem plainBackground_radial_zero (d : MomentData K ω ψ) (w : InfinitePlace K)
    (hψ : heckeRadialParameter K w ψ = 0) :
    heckeRadialParameter K w d.plainBackground = 0 := by
  rcases d.plain_background_spec with hb | hb | hb
  · rw [hb, heckeRadialParameter_one]
  · rw [hb, hψ]
  · rw [hb, heckeRadialParameter_inv, hψ, neg_zero]

/-- The actual finite-order moving row does not change the normalized
radial parameter of the plain background. -/
theorem actualPlain_radial_zero (d : MomentData K ω ψ) (w : InfinitePlace K)
    (hbackground : heckeRadialParameter K w d.plainBackground = 0)
    (u : NonzeroIdeal K) :
    heckeRadialParameter K w (d.plainBackground * d.rowCharacter u) = 0 := by
  rw [heckeRadialParameter_mul, hbackground,
    heckeRadialParameter_finiteOrder K w (d.rowCharacter_finite u), add_zero]

/-- Zero slots exclude the principal actual character directly; no
assumption about the finite exceptional set is needed in this branch. -/
theorem pairedRows_actualPlain_ne_one_zero (d : MomentData K ω ψ)
    (a : RealParameters) (U : ℝ) (hzero : a.z = 0)
    (u : NonzeroIdeal K) (hu : u ∈ pairedRows d a U) :
    d.plainBackground * d.rowCharacter u ≠ 1 := by
  have hfilter : (if a.z = 0 then d.plainBackground * d.rowCharacter u ≠ 1
      else d.rowCharacter u ∉ d.theta) := (Finset.mem_filter.mp hu).2
  simpa only [if_pos hzero] using hfilter

/-- The genuine positive-slot filter excludes the principal actual
character once the fixed finite background has been absorbed into
`theta`.  This lemma does not enlarge or replace that filter. -/
theorem pairedRows_actualPlain_ne_one (d : MomentData K ω ψ)
    (hfiniteBackground : FiniteOrder d.plainBackground →
      d.plainBackground⁻¹ ∈ d.theta)
    (a : RealParameters) (U : ℝ) (u : NonzeroIdeal K)
    (hu : u ∈ pairedRows d a U) :
    d.plainBackground * d.rowCharacter u ≠ 1 := by
  by_cases hzero : a.z = 0
  · exact pairedRows_actualPlain_ne_one_zero d a U hzero u hu
  have hfilter : (if a.z = 0 then d.plainBackground * d.rowCharacter u ≠ 1
      else d.rowCharacter u ∉ d.theta) := (Finset.mem_filter.mp hu).2
  have hnotmem : d.rowCharacter u ∉ d.theta := by
    simpa only [if_neg hzero] using hfilter
  intro heq
  have hbackground : d.plainBackground = (d.rowCharacter u)⁻¹ := by
    calc
      d.plainBackground = d.plainBackground *
          (d.rowCharacter u * (d.rowCharacter u)⁻¹) := by
        rw [mul_inv_cancel, mul_one]
      _ = (d.plainBackground * d.rowCharacter u) * (d.rowCharacter u)⁻¹ :=
        (mul_assoc _ _ _).symm
      _ = (d.rowCharacter u)⁻¹ := by rw [heq, one_mul]
  have hfinite : FiniteOrder d.plainBackground := by
    rw [hbackground]
    exact (d.rowCharacter_finite u).inv
  apply hnotmem
  simpa only [hbackground, inv_inv] using hfiniteBackground hfinite

/-- The zero-slot entrance to ordinary reflection needs only actual
radial normalization, with no extra condition on `theta`. -/
theorem pairedRows_actualPlain_nonNorm_zero (d : MomentData K ω ψ)
    (w : InfinitePlace K)
    (hbackground : heckeRadialParameter K w d.plainBackground = 0)
    (a : RealParameters) (U : ℝ) (hzero : a.z = 0) :
    ∀ u ∈ pairedRows d a U, ∀ t : ℝ,
      d.plainBackground * d.rowCharacter u ≠ heckeNormTwist K t := by
  intro u hu
  exact radial_zero_ne_normTwist w _ (actualPlain_radial_zero d w hbackground u)
    (pairedRows_actualPlain_ne_one_zero d a U hzero u hu)

/-- Both genuine row filters now supply the exact hypothesis consumed by
ordinary Hecke reflection, uniformly in its twist parameter. -/
theorem pairedRows_actualPlain_nonNorm (d : MomentData K ω ψ)
    (w : InfinitePlace K)
    (hbackground : heckeRadialParameter K w d.plainBackground = 0)
    (hfiniteBackground : FiniteOrder d.plainBackground →
      d.plainBackground⁻¹ ∈ d.theta)
    (a : RealParameters) (U : ℝ) :
    ∀ u ∈ pairedRows d a U, ∀ t : ℝ,
      d.plainBackground * d.rowCharacter u ≠ heckeNormTwist K t := by
  intro u hu
  exact radial_zero_ne_normTwist w _ (actualPlain_radial_zero d w hbackground u)
    (pairedRows_actualPlain_ne_one d hfiniteBackground a U u hu)

/-- Source-facing form: the target's normalized radial anchor propagates
through `plain_background_spec`, then the actual filters do the exclusion. -/
theorem pairedRows_actualPlain_nonNorm_of_target (d : MomentData K ω ψ)
    (w : InfinitePlace K) (hψ : heckeRadialParameter K w ψ = 0)
    (hfiniteBackground : FiniteOrder d.plainBackground →
      d.plainBackground⁻¹ ∈ d.theta)
    (a : RealParameters) (U : ℝ) :
    ∀ u ∈ pairedRows d a U, ∀ t : ℝ,
      d.plainBackground * d.rowCharacter u ≠ heckeNormTwist K t :=
  pairedRows_actualPlain_nonNorm d w (plainBackground_radial_zero d w hψ)
    hfiniteBackground a U

end HeckeSkeleton.Moments.EngineInduction
