import HeckeGeneral.Bridge.SIntegerScaledSchwartzModel
import HeckeGeneral.Analysis.SIntegerOrbitalSum
import HeckeGeneral.Analysis.SIntegerInverseOrbitalSum
import HeckeGeneral.Arithmetic.SLocalNormSectionAlgebra
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Orbital Poisson for the actual unweighted S-integer tensor

The full nonzero S-integer sums are unfolded into all actual subgroup
orbits. Both Fourier factors are proved Schwartz--Bruhat data. The reciprocal
radius, discriminant factor, and the positive finite Haar covolume remain
explicit. Each zero contribution is an actual test-function value at zero.

This theorem precedes the periodic residue coefficient and moving ideal mask.
It does not establish their Fourier coefficients or the later Gram bounds.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Bridge
  HeckeGeneral.Characters MeasureTheory
open scoped Classical ENNReal

private theorem integrable_complex_tsum_of_lintegral_enorm
    {A I : Type*} [MeasurableSpace A] [Countable I] (ν : Measure A)
    (F : I → A → ℂ) (hF : ∀ i, Measurable (F i))
    (hbound : (∑' i, ∫⁻ x, ‖F i x‖ₑ ∂ν) < ∞) :
    Integrable (fun x => ∑' i, F i x) ν := by
  refine ⟨(Measurable.tsum hF).aestronglyMeasurable,
    hasFiniteIntegral_iff_enorm.mpr ?_⟩
  calc
    (∫⁻ x, ‖∑' i, F i x‖ₑ ∂ν) ≤ ∫⁻ x, ∑' i, ‖F i x‖ₑ ∂ν :=
      lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)
    _ = ∑' i, ∫⁻ x, ‖F i x‖ₑ ∂ν :=
      lintegral_tsum (fun i => (hF i).aestronglyMeasurable.enorm)
    _ < ∞ := hbound

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) [Γ.FiniteIndex]

local notation "T" => sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "G" => sLocalMultiplicativeGroup K (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "N" => NonzeroRingElements (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)

/-- Sum of the actual common profile over every nonzero S-integer orbit. -/
def sIntegerOrbitalSeries (φ : SchwartzMap V ℂ)
    (ψ : ((v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
    (r : {r : ℝ // 0 < r}) : ℂ :=
  ∑' q : SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ,
    sUnitOrbitalProfile K (S : Set (HeightOneSpectrum (𝓞 K)))
      (sLocalTensorTestFunction K (S : Set (HeightOneSpectrum (𝓞 K))) φ ψ)
      ⟨r.val * (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val,
        mul_pos r.property (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).property⟩

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
/-- Pointwise nonzero Poisson in exactly the two orbital Schwartz families. -/
theorem sIntegerSchwartzTerm_poisson
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (r : {r : ℝ // 0 < r}) (x : T) :
    let c : ℂ := (r.val : ℂ)⁻¹ *
      (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K / Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ)
    (∑' a : N, sIntegerSchwartzTerm K (S : Set (HeightOneSpectrum (𝓞 K))) φ
      (sIntegerFiniteTestFunction K S h) r a x) =
      c * (∑' a : N, sIntegerSchwartzTerm K (S : Set (HeightOneSpectrum (𝓞 K)))
        (traceSchwartzFourier K φ) (sIntegerFiniteFourierTestFunction K S μv h)
        ⟨r.val⁻¹, inv_pos.mpr r.property⟩ a x⁻¹) +
      (c * sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ) h 0 -
        sIntegerTensorTerm K S (traceSchwartzToMixed K φ) h 0) := by
  have hx : sLocalProductNorm K (S : Set (HeightOneSpectrum (𝓞 K))) x.val = 1 :=
    (mem_sLocalNormOneGroup K _ x.val).mp x.property
  have hp : sLocalProductNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
      (sLocalNormSection K _ r * x.val) = r.val := by
    rw [sLocalProductNorm_mul, sLocalProductNorm_section, hx, mul_one]
  have he := sIntegerScaledPoisson_nonzero K S ν μv μ hS
    (traceSchwartzToMixed K φ) h hlc hcs (sLocalNormSection K _ r * x.val)
  dsimp only at he ⊢
  simp only [hp, sIntegerScaledTensorTerm_zero, sIntegerScaledDualTensorTerm_zero,
    sIntegerScaledTensorTerm_eq_sLocalTensor, sIntegerScaledDualTensorTerm_eq_sLocalTensor,
    sLocalNormSection_mul_inverse, ← Subgroup.coe_inv] at he
  simpa only [sIntegerSchwartzTerm, add_sub_assoc] using he

include μ ν in
/-- Genuine unweighted orbital Poisson, with reciprocal radius and both
actual zero terms multiplied by the finite nonzero Haar covolume. -/
theorem sIntegerOrbitalPoisson
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (r : {r : ℝ // 0 < r}) :
    let c : ℂ := (r.val : ℂ)⁻¹ *
      (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K / Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ)
    sIntegerOrbitalSeries K S Γ φ (sIntegerFiniteTestFunction K S h) r =
      c * sIntegerOrbitalSeries K S Γ (traceSchwartzFourier K φ)
        (sIntegerFiniteFourierTestFunction K S μv h) ⟨r.val⁻¹, inv_pos.mpr r.property⟩ +
      ((sUnitHaarCovolume K (S : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ) *
        (c * sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ) h 0 -
          sIntegerTensorTerm K S (traceSchwartzToMixed K φ) h 0) := by
  let ψ := sIntegerFiniteTestFunction K S h
  let ψhat := sIntegerFiniteFourierTestFunction K S μv h
  let rInv : {r : ℝ // 0 < r} := ⟨r.val⁻¹, inv_pos.mpr r.property⟩
  let c : ℂ := (r.val : ℂ)⁻¹ *
    (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K / Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ)
  let z : ℂ := c * sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ) h 0 -
    sIntegerTensorTerm K S (traceSchwartzToMixed K φ) h 0
  let μT := (sUnitHaarMeasure K (S : Set (HeightOneSpectrum (𝓞 K)))).restrict
    (sUnitFundamentalDomain K (S : Set (HeightOneSpectrum (𝓞 K))) Γ)
  let L : T → ℂ := fun x => ∑' a : N,
    sIntegerSchwartzTerm K (S : Set (HeightOneSpectrum (𝓞 K))) φ ψ r a x
  let R : T → ℂ := fun x => ∑' a : N,
    sIntegerSchwartzTerm K (S : Set (HeightOneSpectrum (𝓞 K)))
      (traceSchwartzFourier K φ) ψhat rInv a x⁻¹
  have hψ : Continuous ψ := continuous_sIntegerFiniteTestFunction K S h hlc
  have hψcs : HasCompactSupport ψ := hasCompactSupport_sIntegerFiniteTestFunction K S h hcs
  have hhat := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport K S ν μv h hlc hcs
  have hL := (hasSum_sIntegerOrbitalProfile K (S : Set (HeightOneSpectrum (𝓞 K))) Γ
    φ ψ hψ hψcs r).tsum_eq
  have hR := (hasSum_sIntegerOrbitalProfile_inverse K (S : Set (HeightOneSpectrum (𝓞 K))) Γ
    (traceSchwartzFourier K φ) ψhat hhat.1.continuous hhat.2 rInv).tsum_eq
  have hRint : Integrable R μT := by
    apply integrable_complex_tsum_of_lintegral_enorm μT
      (fun a x => sIntegerSchwartzTerm K (S : Set (HeightOneSpectrum (𝓞 K)))
        (traceSchwartzFourier K φ) ψhat rInv a x⁻¹)
    · intro a
      exact ((continuous_sIntegerSchwartzTerm K _ (traceSchwartzFourier K φ) ψhat
        hhat.1.continuous rInv a).comp continuous_inv).measurable
    · exact tsum_lintegral_enorm_sIntegerSchwartzTerm_comp_lt_top K _ Γ
        (traceSchwartzFourier K φ) ψhat hhat.1.continuous hhat.2 rInv
        (fun x : T => x⁻¹) continuous_inv
  have hzint : Integrable (fun _ : T => z) μT :=
    integrableOn_const (sUnitHaarCovolume_lt_top K _ Γ).ne
  have hpoint (x : T) : L x = c * R x + z :=
    sIntegerSchwartzTerm_poisson K S ν μv μ hS φ h hlc hcs r x
  change sIntegerOrbitalSeries K S Γ φ ψ r =
    c * sIntegerOrbitalSeries K S Γ (traceSchwartzFourier K φ) ψhat rInv +
      ((sUnitHaarCovolume K (S : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ) * z
  change sIntegerOrbitalSeries K S Γ φ ψ r = ∫ x, L x ∂μT at hL
  change sIntegerOrbitalSeries K S Γ (traceSchwartzFourier K φ) ψhat rInv = ∫ x, R x ∂μT at hR
  rw [hL, hR]
  calc
    (∫ x, L x ∂μT) = ∫ x, c * R x + z ∂μT :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = c * (∫ x, R x ∂μT) + (∫ _ : T, z ∂μT) := by
      rw [integral_add (hRint.const_mul c) hzint, integral_const_mul]
    _ = _ := by
      rw [integral_const, Complex.real_smul]
      congr 2
      simp only [μT, Measure.real, Measure.restrict_apply MeasurableSet.univ,
        Set.univ_inter, sUnitHaarCovolume]

end HeckeGeneral.Analysis
