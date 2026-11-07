module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3aRealization
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryMultiplierTransport
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstLogBounds
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.EmptyGaussMask
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.GeneratedCorrelation

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual second row weight and complete correlation

The original empty second divisor and logarithmic row chart give an
exact norm formula before a bound is taken. The original orbital norm
is at least one, so no physical-window loss is needed for the row tilt.
The complete correlation remains a separate factor and is used once.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

namespace T3b

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

/-- Exact empty-mask Poisson weight, retaining its original orbit norm. -/
theorem second_empty_weight_norm
    (ρ : {r : ℝ // 0 < r}) (δ : ℝ)
    (q : SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    ‖secondOrbitalScalar (K := K) (S := S) ρ ∅ *
      ((((CanonicalSecondLogChart.rowRadius ρ ∅ q).val ^ (-δ) : ℝ) : ℂ))‖ =
        orbitalFieldFactor K * ρ.val ^ (δ - 1) *
          (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val ^ (-δ) := by
  let N := sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q
  have hscalar : ‖secondOrbitalScalar (K := K) (S := S) ρ ∅‖ =
      orbitalFieldFactor K * ρ.val⁻¹ := by
    rw [secondOrbitalScalar_empty, norm_mul, norm_inv]
    simp only [Complex.norm_real, Real.norm_of_nonneg ρ.property.le,
      Real.norm_of_nonneg (orbitalFieldFactor_nonneg K)]
    ring
  have hradius : (CanonicalSecondLogChart.rowRadius ρ ∅ q).val = N.val / ρ.val := by
    simp only [CanonicalSecondLogChart.rowRadius,
      sIntegerMaskGenerator_empty_norm K S, mul_one, N]
  rw [norm_mul, hscalar,
    CanonicalFirstLog.tiltScalar_norm (CanonicalSecondLogChart.rowRadius ρ ∅ q).property,
    hradius, Real.div_rpow N.property.le ρ.property.le,
    Real.rpow_neg ρ.property.le, Real.rpow_sub_one ρ.property.ne' δ]
  simp only [div_eq_mul_inv, inv_inv]
  ring

end T3b

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

/-- This is computed from the original second radius and Mellin tilt. -/
def t3bRowAmplitude : ℝ :=
  orbitalFieldFactor K * packet.second.stage.radius.val ^ (p.tilt - 1)

theorem t3bRowAmplitude_nonneg : 0 ≤ packet.t3bRowAmplitude :=
  mul_nonneg (orbitalFieldFactor_nonneg K)
    (Real.rpow_nonneg packet.second.stage.radius.property.le _)

theorem t3b_rowWeight_eq (hpacket : packet.Realizes) (q : Arithmetic.Orbit c) :
    packet.R.weight q =
      secondOrbitalScalar (K := K) (S := (Arithmetic.data c).Sf)
        packet.second.stage.radius ∅ *
          ((((CanonicalSecondLogChart.rowRadius packet.second.stage.radius ∅ q).val ^
            (-p.tilt) : ℝ) : ℂ)) := by
  change secondOrbitalScalar packet.second.stage.radius packet.key.2.1.val *
    packet.chart.weight q = _
  rw [(packet.exceptional_second_realizes hpacket).weight,
    packet.secondDivisor_eq_empty hpacket]

/-- The unchanged actual frequency still occurs in the exact formula. -/
theorem t3b_rowWeight_norm (hpacket : packet.Realizes) (q : Arithmetic.Orbit c) :
    ‖packet.R.weight q‖ = packet.t3bRowAmplitude *
      (sIntegerOrbitNorm K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
        (Arithmetic.unitSubgroup c) q).val ^ (-p.tilt) := by
  rw [packet.t3b_rowWeight_eq hpacket q]
  exact T3b.second_empty_weight_norm packet.second.stage.radius p.tilt q

/-- Arithmetic norm at least one bounds every actual row, even before
the original finite cutoff and live predicate are applied. -/
theorem t3b_rowWeight_le (hpacket : packet.Realizes) (q : Arithmetic.Orbit c) :
    ‖packet.R.weight q‖ ≤ packet.t3bRowAmplitude := by
  rw [packet.t3b_rowWeight_norm hpacket q]
  exact (mul_le_mul_of_nonneg_left
    (Real.rpow_le_one_of_one_le_of_nonpos (one_le_sIntegerOrbitNorm q)
      (neg_nonpos.mpr p.tilt_pos.le)) packet.t3bRowAmplitude_nonneg).trans_eq (mul_one _)

/-- The source radius is the reciprocal of the retained original scale
times its actual enlargement. No replacement cutoff is introduced. -/
theorem t3bRowAmplitude_eq_retained (hpacket : packet.Realizes) :
    packet.t3bRowAmplitude = orbitalFieldFactor K *
      (packet.second.physical.first.retainedScale *
        call.base ^ packet.second.physical.enlargement) ^ (1 - p.tilt) := by
  have hscale : 0 < packet.second.physical.first.retainedScale *
      call.base ^ packet.second.physical.enlargement :=
    mul_pos packet.second.physical.first.retainedScale_pos
      (Real.rpow_pos_of_pos call.base_pos _)
  have hexponent : -(p.tilt - 1) = 1 - p.tilt := by ring
  unfold t3bRowAmplitude
  rw [(packet.exceptional_second_realizes hpacket).radius,
    Real.inv_rpow hscale.le, ← Real.rpow_neg hscale.le, hexponent]

/-- The local complete-correlation theorem uses the actual generators
and the unit-frequency radical of this same original row. -/
theorem t3b_correlation_gcd_radical_le (q : Arithmetic.Orbit c) :
    ‖packet.R.correlation q‖ ≤
      (Ideal.absNorm (gcd
        (primePowerProduct packet.R.primes packet.R.leftMultiplicity).val
        (primePowerProduct packet.R.primes packet.R.rightMultiplicity).val) : ℝ) /
        (Arithmetic.data c).exteriorNorm
          (unitFrequencyRadical (Arithmetic.context c) packet.R.primes
            packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency q)) := by
  exact actual_complete_correlation_gcd_radical_bound_of_generates
    (Arithmetic.context c) packet.R.primes packet.R.primes_injective
    packet.R.leftMultiplicity packet.R.rightMultiplicity packet.block.left_positive
    packet.R.leftGenerator packet.R.rightGenerator packet.R.leftGenerates
    packet.R.rightGenerates (packet.R.frequency q)

theorem t3b_correlation_nominal_le (hpacket : packet.Realizes) (side : Bool)
    (h : packet.R.live) :
    ‖packet.R.correlation h.val‖ ≤
      call.base ^ ((packet.nominal side).skeleton.g₂ - (packet.nominal side).skeleton.t₂) := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).correlation side h

/-- The raw leaf has one complete correlation, multiplied by the
literal second logarithmic row weight. -/
theorem t3b_leafRowWeight_le (hpacket : packet.Realizes) (side : Bool)
    (h : packet.R.live) :
    ‖packet.leaf.rowWeight h.val‖ ≤ packet.t3bRowAmplitude *
      call.base ^ ((packet.nominal side).skeleton.g₂ - (packet.nominal side).skeleton.t₂) := by
  rw [packet.exceptional_leaf_rowWeight, norm_mul]
  exact mul_le_mul (packet.t3b_rowWeight_le hpacket h.val)
    (packet.t3b_correlation_nominal_le hpacket side h) (norm_nonneg _)
    packet.t3bRowAmplitude_nonneg

end RawLeafPacket

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_rowWeight_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_leafRowWeight_le
