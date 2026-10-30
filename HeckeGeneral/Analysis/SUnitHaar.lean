import HeckeGeneral.Analysis.CompactQuotientFundamentalDomain
import HeckeGeneral.Arithmetic.SUnitNormOneTopology
import Mathlib.MeasureTheory.Measure.Haar.Quotient

/-!
Haar measure on the actual norm-one S-local group and its S-unit quotient.

The Borel structure on the norm-one group is a structure parameter. No new
measurable instance is placed on that subtype. The quotient uses Mathlib's
standard coinduced measurable structure, which is Borel by the actual Polish
topology upstairs and the separated, second-countable quotient topology.

A Borel fundamental domain with compact closure is chosen from the proved
compact-quotient construction. Its restricted Haar measure is pushed forward
to the quotient. The volume of the domain is retained, rather than silently
normalizing the quotient to probability. Every fundamental-domain and measure
compatibility assertion below follows from that construction.

The final unfolding identity has explicit integrability and strong a.e.
measurability hypotheses on its function. It makes no assertion that a later
adelic Schwartz integrand already satisfies those analytic obligations.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open MeasureTheory MeasureTheory.Measure Set Topology
open scoped Classical ENNReal

-- Haar.Quotient disables this instance before its general unfolding section.
-- Here the same standard quotient structure is deliberately used throughout.
attribute [local instance] Quotient.instMeasurableSpace

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]

/-- A genuine Mathlib Haar measure on the actual norm-one local group. -/
abbrev sUnitHaarMeasure : Measure (sLocalNormOneGroup K S) :=
  MeasureTheory.Measure.haar (G := sLocalNormOneGroup K S)

instance isHaarMeasure_sUnitHaarMeasure : IsHaarMeasure (sUnitHaarMeasure K S) :=
  inferInstance

variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

local notation "T" => sLocalNormOneGroup K S
local notation "H" => sLocalNormOneGamma K S Γ
local notation "Q" => SUnitNormOneQuotient K S Γ

/-- A measure-independent choice of actual Borel coset representatives. -/
def sUnitFundamentalDomain : Set T :=
  (exists_precompact_fundamentalDomain_of_compact_quotient H
    (isDiscrete_sLocalNormOneGamma K S Γ)).choose

theorem sUnitFundamentalDomain_spec :
    MeasurableSet (sUnitFundamentalDomain K S Γ) ∧
      IsCompact (closure (sUnitFundamentalDomain K S Γ)) ∧
      ∀ ν : Measure T, IsFundamentalDomain (H).op (sUnitFundamentalDomain K S Γ) ν :=
  (exists_precompact_fundamentalDomain_of_compact_quotient H
    (isDiscrete_sLocalNormOneGamma K S Γ)).choose_spec

theorem measurableSet_sUnitFundamentalDomain :
    MeasurableSet (sUnitFundamentalDomain K S Γ) :=
  (sUnitFundamentalDomain_spec K S Γ).1

theorem isCompact_closure_sUnitFundamentalDomain :
    IsCompact (closure (sUnitFundamentalDomain K S Γ)) :=
  (sUnitFundamentalDomain_spec K S Γ).2.1

theorem isFundamentalDomain_sUnitFundamentalDomain (ν : Measure T) :
    IsFundamentalDomain (H).op (sUnitFundamentalDomain K S Γ) ν :=
  (sUnitFundamentalDomain_spec K S Γ).2.2 ν

instance hasFundamentalDomain_sUnitHaarMeasure : HasFundamentalDomain (H).op T
    (sUnitHaarMeasure K S) :=
  (isFundamentalDomain_sUnitFundamentalDomain K S Γ (sUnitHaarMeasure K S)).hasFundamentalDomain _

/-- The actual, unnormalized quotient measure induced from the selected Haar measure. -/
def sUnitQuotientMeasure : Measure Q :=
  ((sUnitHaarMeasure K S).restrict (sUnitFundamentalDomain K S Γ)).map
    (QuotientGroup.mk : T → Q)

/-- The retained Haar covolume, with its normalization determined by the upstairs Haar measure. -/
def sUnitHaarCovolume : ℝ≥0∞ := sUnitHaarMeasure K S (sUnitFundamentalDomain K S Γ)

theorem sUnitHaarCovolume_lt_top : sUnitHaarCovolume K S Γ < ∞ :=
  lt_of_le_of_lt (measure_mono subset_closure)
    (isCompact_closure_sUnitFundamentalDomain K S Γ).measure_lt_top

theorem sUnitHaarCovolume_ne_zero : sUnitHaarCovolume K S Γ ≠ 0 :=
  (isFundamentalDomain_sUnitFundamentalDomain K S Γ (sUnitHaarMeasure K S)).measure_ne_zero
    (NeZero.ne (sUnitHaarMeasure K S))

theorem sUnitHaarCovolume_eq_covolume :
    sUnitHaarCovolume K S Γ = covolume (H).op T (sUnitHaarMeasure K S) :=
  (isFundamentalDomain_sUnitFundamentalDomain K S Γ (sUnitHaarMeasure K S)).covolume_eq_volume
    (sUnitHaarMeasure K S) |>.symm

/-- This compatibility is proved for the constructed measure, not supplied as input. -/
instance quotientMeasureEqMeasurePreimage_sUnitQuotientMeasure :
    QuotientMeasureEqMeasurePreimage (sUnitHaarMeasure K S) (sUnitQuotientMeasure K S Γ) :=
  (isFundamentalDomain_sUnitFundamentalDomain K S Γ (sUnitHaarMeasure K S)).quotientMeasureEqMeasurePreimage_quotientMeasure

omit [Γ.FiniteIndex] in
theorem measurable_sUnitQuotient_mk : Measurable (QuotientGroup.mk : T → Q) :=
  QuotientGroup.continuous_mk.measurable

/-- Exact total mass; the quotient is not implicitly rescaled to mass one. -/
theorem sUnitQuotientMeasure_univ : sUnitQuotientMeasure K S Γ Set.univ =
    sUnitHaarCovolume K S Γ := by
  rw [sUnitQuotientMeasure,
    Measure.map_apply (measurable_sUnitQuotient_mk K S Γ) MeasurableSet.univ]
  simp [sUnitHaarCovolume]

instance isFiniteMeasure_sUnitQuotientMeasure : IsFiniteMeasure (sUnitQuotientMeasure K S Γ) := by
  constructor
  rw [sUnitQuotientMeasure_univ]
  exact sUnitHaarCovolume_lt_top K S Γ

/-- The measure actually constructed from the domain is Haar on the compact quotient. -/
instance isHaarMeasure_sUnitQuotientMeasure : IsHaarMeasure (sUnitQuotientMeasure K S Γ) :=
  QuotientMeasureEqMeasurePreimage.haarMeasure_quotient (sUnitHaarMeasure K S)

theorem sUnitQuotientMeasure_apply (A : Set Q) (hA : MeasurableSet A) :
    sUnitQuotientMeasure K S Γ A =
      sUnitHaarMeasure K S ((QuotientGroup.mk : T → Q) ⁻¹' A ∩
        sUnitFundamentalDomain K S Γ) :=
  (isFundamentalDomain_sUnitFundamentalDomain K S Γ (sUnitHaarMeasure K S)).projection_respects_measure_apply (sUnitQuotientMeasure K S Γ) hA

theorem sUnitQuotient_projection_measurePreserving :
    MeasurePreserving (QuotientGroup.mk : T → Q)
      ((sUnitHaarMeasure K S).restrict (sUnitFundamentalDomain K S Γ))
      (sUnitQuotientMeasure K S Γ) :=
  measurePreserving_quotientGroup_mk_of_QuotientMeasureEqMeasurePreimage
    (sUnitHaarMeasure K S)
    (isFundamentalDomain_sUnitFundamentalDomain K S Γ (sUnitHaarMeasure K S))
    (sUnitQuotientMeasure K S Γ)

/-- An actual unfolding formula once the function's two analytic obligations are met. -/
theorem integral_sUnitHaar_eq_integral_automorphize {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : T → E}
    (hf : Integrable f (sUnitHaarMeasure K S))
    (ha : AEStronglyMeasurable (QuotientGroup.automorphize f) (sUnitQuotientMeasure K S Γ)) :
    (∫ x : T, f x ∂sUnitHaarMeasure K S) =
      ∫ x : Q, QuotientGroup.automorphize f x ∂sUnitQuotientMeasure K S Γ :=
  QuotientGroup.integral_eq_integral_automorphize
    (isFundamentalDomain_sUnitFundamentalDomain K S Γ (sUnitHaarMeasure K S)) hf ha

/-- Haar translations remain nonsingular after restricting the source to the chosen domain. -/
private theorem quasiMeasurePreserving_sUnitFundamentalDomain_smul (g : (H).op) :
    Measure.QuasiMeasurePreserving (fun x : T => g • x)
      ((sUnitHaarMeasure K S).restrict (sUnitFundamentalDomain K S Γ))
      (sUnitHaarMeasure K S) :=
  (measurePreserving_smul g (sUnitHaarMeasure K S)).quasiMeasurePreserving.mono_left
    Measure.restrict_le_self.absolutelyContinuous

/-- Nonnegative orbital integration uses the actual counting action of the diagonal subgroup.
There is no integrability assumption for this extended-valued identity. -/
theorem lintegral_sUnitFundamentalDomain_tsum_smul {f : T → ℝ≥0∞}
    (hf : AEMeasurable f (sUnitHaarMeasure K S)) :
    (∫⁻ x in sUnitFundamentalDomain K S Γ, ∑' g : (H).op, f (g • x)
      ∂sUnitHaarMeasure K S) = ∫⁻ x : T, f x ∂sUnitHaarMeasure K S := by
  have hcomp : ∀ g : (H).op, AEMeasurable (fun x : T => f (g • x))
      ((sUnitHaarMeasure K S).restrict (sUnitFundamentalDomain K S Γ)) := fun g =>
    hf.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sUnitFundamentalDomain_smul K S Γ g)
  rw [lintegral_tsum hcomp]
  exact (isFundamentalDomain_sUnitFundamentalDomain K S Γ (sUnitHaarMeasure K S)).lintegral_eq_tsum'' f |>.symm

/-- Given genuine integrability upstairs, the orbit series is absolutely summable
at almost every representative. This does not assert integrability of Schwartz slices. -/
theorem ae_summable_norm_sUnitFundamentalDomain_smul {f : T → ℂ}
    (hf : Integrable f (sUnitHaarMeasure K S)) :
    ∀ᵐ x ∂((sUnitHaarMeasure K S).restrict (sUnitFundamentalDomain K S Γ)),
      Summable fun g : (H).op => ‖f (g • x)‖ := by
  have hnorm : AEMeasurable (fun x : T => ‖f x‖ₑ) (sUnitHaarMeasure K S) :=
    hf.aestronglyMeasurable.enorm
  have hcomp : ∀ g : (H).op, AEMeasurable (fun x : T => ‖f (g • x)‖ₑ)
      ((sUnitHaarMeasure K S).restrict (sUnitFundamentalDomain K S Γ)) := fun g =>
    hnorm.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sUnitFundamentalDomain_smul K S Γ g)
  have hfin : (∫⁻ x in sUnitFundamentalDomain K S Γ,
      ∑' g : (H).op, ‖f (g • x)‖ₑ ∂sUnitHaarMeasure K S) ≠ ⊤ := by
    rw [lintegral_sUnitFundamentalDomain_tsum_smul K S Γ hnorm]
    exact hf.2.ne
  have hae : ∀ᵐ x ∂((sUnitHaarMeasure K S).restrict (sUnitFundamentalDomain K S Γ)),
      (∑' g : (H).op, ‖f (g • x)‖ₑ) < ⊤ :=
    ae_lt_top' (AEMeasurable.tsum hcomp) hfin
  filter_upwards [hae] with x hx
  have h2 : (∑' g : (H).op, (‖f (g • x)‖₊ : ℝ≥0∞)) ≠ ⊤ := by
    simpa [enorm_eq_nnnorm] using hx.ne
  have h3 : Summable fun g : (H).op => ‖f (g • x)‖₊ :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp h2
  exact NNReal.summable_coe.mpr h3

/-- The complex orbit series is summable on the same almost-everywhere representative set. -/
theorem ae_summable_sUnitFundamentalDomain_smul {f : T → ℂ}
    (hf : Integrable f (sUnitHaarMeasure K S)) :
    ∀ᵐ x ∂((sUnitHaarMeasure K S).restrict (sUnitFundamentalDomain K S Γ)),
      Summable fun g : (H).op => f (g • x) := by
  filter_upwards [ae_summable_norm_sUnitFundamentalDomain_smul K S Γ hf] with x hx
  exact Summable.of_norm hx

/-- Set-integral unfolding needs only actual integrability upstairs. Its proof uses
Mathlib's fundamental-domain partition and Tonelli, with no large FLT import. -/
theorem integral_sUnitHaar_eq_setIntegral_tsum_smul {f : T → ℂ}
    (hf : Integrable f (sUnitHaarMeasure K S)) :
    (∫ x : T, f x ∂sUnitHaarMeasure K S) =
      ∫ x in sUnitFundamentalDomain K S Γ, ∑' g : (H).op, f (g • x)
        ∂sUnitHaarMeasure K S := by
  have hsm : ∀ g : (H).op, AEStronglyMeasurable (fun x : T => f (g • x))
      ((sUnitHaarMeasure K S).restrict (sUnitFundamentalDomain K S Γ)) := fun g =>
    hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sUnitFundamentalDomain_smul K S Γ g)
  have hbound : (∑' g : (H).op, ∫⁻ x in sUnitFundamentalDomain K S Γ,
      ‖f (g • x)‖ₑ ∂sUnitHaarMeasure K S) ≠ ⊤ := by
    have hnorm : AEMeasurable (fun x : T => ‖f x‖ₑ) (sUnitHaarMeasure K S) :=
      hf.aestronglyMeasurable.enorm
    have hcomp : ∀ g : (H).op, AEMeasurable (fun x : T => ‖f (g • x)‖ₑ)
        ((sUnitHaarMeasure K S).restrict (sUnitFundamentalDomain K S Γ)) := fun g =>
      hnorm.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sUnitFundamentalDomain_smul K S Γ g)
    rw [← lintegral_tsum hcomp,
      lintegral_sUnitFundamentalDomain_tsum_smul K S Γ hnorm]
    exact hf.2.ne
  calc
    (∫ x : T, f x ∂sUnitHaarMeasure K S) =
        ∑' g : (H).op, ∫ x in sUnitFundamentalDomain K S Γ, f (g • x)
          ∂sUnitHaarMeasure K S :=
      (isFundamentalDomain_sUnitFundamentalDomain K S Γ (sUnitHaarMeasure K S)).integral_eq_tsum'' f hf
    _ = ∫ x in sUnitFundamentalDomain K S Γ, ∑' g : (H).op, f (g • x)
          ∂sUnitHaarMeasure K S := (integral_tsum hsm hbound).symm

end HeckeGeneral.Analysis
