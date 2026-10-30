import HeckeGeneral.Bridge.SIntegerPeriodicScaledSummability
import HeckeGeneral.Bridge.SIntegerScaledSchwartzModel
import HeckeGeneral.Arithmetic.SIntegerModulusNormSection
import HeckeGeneral.Analysis.SIntegerWeightedOrbitalSum
import HeckeGeneral.Analysis.SIntegerWeightedSeriesIntegrable

/-!
# Periodic orbital Poisson on the original S-unit quotient

The literal coefficient is `f(d*a)` on the actual principal quotient, and
the dual coefficient is its proved finite divisor transform. Both descend
to every orbit of the original subgroup. The inverse modulus's genuine
norm-one component is absorbed by shifted inverse Haar unfolding, leaving
the same common profile at radius `1 / (r * q_c)`.

The two zero contributions retain their actual values. The discriminant
factor, inverse modulus norm, and finite positive Haar covolume are explicit.
No unit condition on `d`, PID hypothesis, or analytic convergence input is
added to the actual locally constant compactly supported finite data.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Bridge
  HeckeGeneral.Characters MeasureTheory
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) [Γ.FiniteIndex]

local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "T" => sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "G" => sLocalMultiplicativeGroup K (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "N" => NonzeroRingElements OS
local notation "Q" => SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ

/-- The common orbital profile with one coefficient on every actual subgroup sector. -/
def sIntegerWeightedOrbitalSeries (φ : SchwartzMap V ℂ)
    (ψ : ((v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
    (r : {r : ℝ // 0 < r}) (w : Q → ℂ) : ℂ :=
  ∑' q : Q, w q *
    sUnitOrbitalProfile K (S : Set (HeightOneSpectrum (𝓞 K)))
      (sLocalTensorTestFunction K (S : Set (HeightOneSpectrum (𝓞 K))) φ ψ)
      ⟨r.val * (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val,
        mul_pos r.property (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).property⟩

variable (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
variable (c : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) (hc : c ≠ 0)


/-- Literal invariance survives dilation by every divisor, including nonunits. -/
theorem sIntegerPeriodic_divisorPullback_literal_invariant (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ)
    (hinv : ∀ u : Γ, ∀ a : OS,
      f (Ideal.Quotient.mk _ (((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K
        u.val).val * a)) = f (Ideal.Quotient.mk _ a)) (d : OS) :
    ∀ u : Γ, ∀ a : OS,
      (fun z : (OS ⧸ Ideal.span ({c} : Set OS)) => f (Ideal.Quotient.mk _ d * z))
          (Ideal.Quotient.mk _ (((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K
            u.val).val * a)) =
        (fun z : (OS ⧸ Ideal.span ({c} : Set OS)) => f (Ideal.Quotient.mk _ d * z)) (Ideal.Quotient.mk _ a) := by
  intro u a
  change f (Ideal.Quotient.mk _ d * Ideal.Quotient.mk _
      ((((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K u.val).val) * a)) =
    f (Ideal.Quotient.mk _ d * Ideal.Quotient.mk _ a)
  rw [← map_mul, ← map_mul, mul_left_comm d]
  exact hinv u (d * a)

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include μ ν in
/-- The periodic nonzero Poisson identity in the actual common Schwartz model. -/
theorem sIntegerPeriodicSchwartzTerm_poisson
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ) (d : OS)
    (r : {r : ℝ // 0 < r}) (x : T) :
    let C : ℂ := (r.val : ℂ)⁻¹ *
      (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K / Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) *
      ((sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c, hc⟩).val : ℂ)⁻¹
    let rDual : {r : ℝ // 0 < r} :=
      ⟨(r.val * (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c, hc⟩).val)⁻¹,
        inv_pos.mpr (mul_pos r.property
          (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c, hc⟩).property)⟩
    let t : T := sIntegerModulusNormOneShift K (S : Set (HeightOneSpectrum (𝓞 K))) c hc
    (∑' a : N, f (Ideal.Quotient.mk (Ideal.span ({c} : Set OS)) (d * a.val)) *
      sIntegerSchwartzTerm K (S : Set (HeightOneSpectrum (𝓞 K))) φ
        (sIntegerFiniteTestFunction K S h) r a x) =
      C * (∑' a : N,
        sIntegerPeriodicDivisorFourier K (S : Set (HeightOneSpectrum (𝓞 K))) hS c hc f d
          (Ideal.Quotient.mk _ a.val) *
        sIntegerSchwartzTerm K (S : Set (HeightOneSpectrum (𝓞 K)))
          (traceSchwartzFourier K φ) (sIntegerFiniteFourierTestFunction K S μv h)
          rDual a (t * x⁻¹)) +
      (C * (sIntegerPeriodicDivisorFourier K (S : Set (HeightOneSpectrum (𝓞 K))) hS c hc f d 0 *
          sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ) h 0) -
        f 0 * sIntegerTensorTerm K S (traceSchwartzToMixed K φ) h 0) := by
  have hx : sLocalProductNorm K (S : Set (HeightOneSpectrum (𝓞 K))) x.val = 1 :=
    (mem_sLocalNormOneGroup K _ x.val).mp x.property
  have hp : sLocalProductNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
      (sLocalNormSection K _ r * x.val) = r.val := by
    rw [sLocalProductNorm_mul, sLocalProductNorm_section, hx, mul_one]
  have he := sIntegerPeriodicScaledPoisson_nonzero K S hS c hc ν μv μ
    (traceSchwartzToMixed K φ) h hlc hcs f d (sLocalNormSection K _ r * x.val)
  dsimp only at he ⊢
  simp only [hp, sIntegerModulus_inverseBase_eq_section_shift,
    sIntegerScaledTensorTerm_zero, sIntegerScaledDualTensorTerm_zero,
    sIntegerScaledTensorTerm_eq_sLocalTensor, sIntegerScaledDualTensorTerm_eq_sLocalTensor] at he
  simpa only [sIntegerSchwartzTerm, add_sub_assoc] using he

include μ ν in
/-- Genuine periodic orbital Poisson on every sector of the original subgroup. -/
theorem sIntegerPeriodicOrbitalPoisson
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ)
    (hinv : ∀ u : Γ, ∀ a : OS,
      f (Ideal.Quotient.mk _ (((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K
        u.val).val * a)) = f (Ideal.Quotient.mk _ a))
    (d : OS) (r : {r : ℝ // 0 < r}) :
    let g : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ := fun z => f (Ideal.Quotient.mk _ d * z)
    let hg := sIntegerPeriodic_divisorPullback_literal_invariant K S Γ c f hinv d
    let C : ℂ := (r.val : ℂ)⁻¹ *
      (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K / Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) *
      ((sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c, hc⟩).val : ℂ)⁻¹
    let rDual : {r : ℝ // 0 < r} :=
      ⟨(r.val * (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c, hc⟩).val)⁻¹,
        inv_pos.mpr (mul_pos r.property
          (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c, hc⟩).property)⟩
    sIntegerWeightedOrbitalSeries K S Γ φ (sIntegerFiniteTestFunction K S h) r
        (sIntegerPeriodicOrbitWeight K (S : Set (HeightOneSpectrum (𝓞 K))) Γ c g hg) =
      C * sIntegerWeightedOrbitalSeries K S Γ (traceSchwartzFourier K φ)
        (sIntegerFiniteFourierTestFunction K S μv h) rDual
        (sIntegerPeriodicFourierOrbitWeight K (S : Set (HeightOneSpectrum (𝓞 K))) hS Γ c hc f hinv d) +
      ((sUnitHaarCovolume K (S : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ) *
        (C * (sIntegerPeriodicDivisorFourier K (S : Set (HeightOneSpectrum (𝓞 K))) hS c hc f d 0 *
            sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ) h 0) -
          f 0 * sIntegerTensorTerm K S (traceSchwartzToMixed K φ) h 0) := by
  let g : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ := fun z => f (Ideal.Quotient.mk _ d * z)
  let hg := sIntegerPeriodic_divisorPullback_literal_invariant K S Γ c f hinv d
  let ψ := sIntegerFiniteTestFunction K S h
  let ψhat := sIntegerFiniteFourierTestFunction K S μv h
  let rDual : {r : ℝ // 0 < r} :=
    ⟨(r.val * (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c, hc⟩).val)⁻¹,
      inv_pos.mpr (mul_pos r.property
        (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c, hc⟩).property)⟩
  let t : T := sIntegerModulusNormOneShift K (S : Set (HeightOneSpectrum (𝓞 K))) c hc
  let C : ℂ := (r.val : ℂ)⁻¹ *
    (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K / Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) *
    ((sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c, hc⟩).val : ℂ)⁻¹
  let z : ℂ := C *
      (sIntegerPeriodicDivisorFourier K (S : Set (HeightOneSpectrum (𝓞 K))) hS c hc f d 0 *
        sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ) h 0) -
    f 0 * sIntegerTensorTerm K S (traceSchwartzToMixed K φ) h 0
  let wL : Q → ℂ := sIntegerPeriodicOrbitWeight K
    (S : Set (HeightOneSpectrum (𝓞 K))) Γ c g hg
  let wR : Q → ℂ := sIntegerPeriodicFourierOrbitWeight K
    (S : Set (HeightOneSpectrum (𝓞 K))) hS Γ c hc f hinv d
  let μT := (sUnitHaarMeasure K (S : Set (HeightOneSpectrum (𝓞 K)))).restrict
    (sUnitFundamentalDomain K (S : Set (HeightOneSpectrum (𝓞 K))) Γ)
  let L : T → ℂ := fun x => ∑' a : N,
    g (Ideal.Quotient.mk _ a.val) *
      sIntegerSchwartzTerm K (S : Set (HeightOneSpectrum (𝓞 K))) φ ψ r a x
  let Rdual : T → ℂ := fun x => ∑' a : N,
    sIntegerPeriodicDivisorFourier K (S : Set (HeightOneSpectrum (𝓞 K))) hS c hc f d
        (Ideal.Quotient.mk _ a.val) *
      sIntegerSchwartzTerm K (S : Set (HeightOneSpectrum (𝓞 K)))
        (traceSchwartzFourier K φ) ψhat rDual a (t * x⁻¹)
  have hψ : Continuous ψ := continuous_sIntegerFiniteTestFunction K S h hlc
  have hψcs : HasCompactSupport ψ := hasCompactSupport_sIntegerFiniteTestFunction K S h hcs
  have hhat := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport K S ν μv h hlc hcs
  have hL := (hasSum_sIntegerPeriodicOrbitalProfile K (S : Set (HeightOneSpectrum (𝓞 K))) Γ
    φ ψ hψ hψcs r c hc g hg).tsum_eq
  have hR := (hasSum_sIntegerPeriodicOrbitalProfile_shift_inverse
    K (S : Set (HeightOneSpectrum (𝓞 K))) Γ (traceSchwartzFourier K φ) ψhat
    hhat.1.continuous hhat.2 rDual t c hc
    (sIntegerPeriodicDivisorFourier K (S : Set (HeightOneSpectrum (𝓞 K))) hS c hc f d)
    (sIntegerPeriodicDivisorFourier_literal_invariant K
      (S : Set (HeightOneSpectrum (𝓞 K))) hS Γ c hc f hinv d)).tsum_eq
  have hRint : Integrable Rdual μT := by
    exact integrable_sIntegerWeightedSchwartzSeries_comp
      K (S : Set (HeightOneSpectrum (𝓞 K))) Γ (traceSchwartzFourier K φ) ψhat
      hhat.1.continuous hhat.2 rDual (fun x : T => t * x⁻¹)
      (continuous_const.mul continuous_inv)
      (fun a : N => sIntegerPeriodicDivisorFourier K
        (S : Set (HeightOneSpectrum (𝓞 K))) hS c hc f d (Ideal.Quotient.mk _ a.val))
      (sIntegerPeriodicResidueL1 K (S : Set (HeightOneSpectrum (𝓞 K))) c hc g)
      (fun a => norm_sIntegerPeriodicDivisorFourier_le_pullback_L1 K
        (S : Set (HeightOneSpectrum (𝓞 K))) hS c hc f d (Ideal.Quotient.mk _ a.val))
  have hzint : Integrable (fun _ : T => z) μT :=
    integrableOn_const (sUnitHaarCovolume_lt_top K _ Γ).ne
  have hpoint (x : T) : L x = C * Rdual x + z := by
    simpa only [L, Rdual, g, ← map_mul] using
      sIntegerPeriodicSchwartzTerm_poisson K S hS c hc ν μv μ φ h hlc hcs f d r x
  change sIntegerWeightedOrbitalSeries K S Γ φ ψ r wL =
    C * sIntegerWeightedOrbitalSeries K S Γ (traceSchwartzFourier K φ) ψhat rDual wR +
      ((sUnitHaarCovolume K (S : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ) * z
  change sIntegerWeightedOrbitalSeries K S Γ φ ψ r wL = ∫ x, L x ∂μT at hL
  change sIntegerWeightedOrbitalSeries K S Γ (traceSchwartzFourier K φ) ψhat rDual wR =
    ∫ x, Rdual x ∂μT at hR
  rw [hL, hR]
  calc
    (∫ x, L x ∂μT) = ∫ x, C * Rdual x + z ∂μT :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = C * (∫ x, Rdual x ∂μT) + (∫ _ : T, z ∂μT) := by
      rw [integral_add (hRint.const_mul C) hzint, integral_const_mul]
    _ = _ := by
      rw [integral_const, Complex.real_smul]
      congr 2
      simp only [μT, Measure.real, Measure.restrict_apply MeasurableSet.univ,
        Set.univ_inter, sUnitHaarCovolume]

end HeckeGeneral.Analysis

