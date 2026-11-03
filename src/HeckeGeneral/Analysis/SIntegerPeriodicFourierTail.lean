import HeckeGeneral.Analysis.SIntegerProfileTail
import HeckeGeneral.Arithmetic.SIntegerPeriodicFourier
import HeckeGeneral.Bridge.SLocalFiniteFourier
import HeckeGeneral.Bridge.TraceSchwartzFourierBounds

/-! Quantitative tails for the actual periodic divisor Fourier coefficients
and actual Fourier orbital profile. The finite seminorm set and constant
are fixed before the modulus, periodic function, divisor and test function. -/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Bridge MeasureTheory
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "T" => sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "L" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) [Γ.FiniteIndex]
local notation "Q" => SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

include ν in
/-- The tail retains every original Γ-sector. Its coefficients are the true
divisor Fourier transform and its profile uses the genuine trace and local
Fourier transforms. No Fourier decay or boundedness is assumed. -/
theorem exists_sIntegerPeriodicFourierProfile_tail_bound
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (A : ℝ) (hA : 1 < A) (M : ℕ) (hM : Module.finrank ℤ L < M)
    (hOrder : (Module.finrank ℚ K : ℝ) * A ≤ M) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : SchwartzMap V ℂ, ∀ c : OS, ∀ hc : c ≠ 0,
      ∀ f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ,
      ∀ hinv : ∀ u : Γ, ∀ a : OS,
        f (Ideal.Quotient.mk _
          (((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K u.val).val * a)) =
            f (Ideal.Quotient.mk _ a),
      ∀ d : OS, ∀ ρ : {r : ℝ // 0 < r}, ∀ X : ℝ, 1 ≤ X →
        let w := sIntegerPeriodicFourierOrbitWeight K
          (S : Set (HeightOneSpectrum (𝓞 K))) hS Γ c hc f hinv d
        let F := fun q : {q : Q // X < ρ.val *
            (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val} =>
          w q.val * sUnitOrbitalProfile K (S : Set (HeightOneSpectrum (𝓞 K)))
            (sLocalTensorTestFunction K (S : Set (HeightOneSpectrum (𝓞 K)))
              (traceSchwartzFourier K φ) (sIntegerFiniteFourierTestFunction K S μv h))
            ⟨ρ.val * (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q.val).val,
              mul_pos ρ.property (sIntegerOrbitNorm K
                (S : Set (HeightOneSpectrum (𝓞 K))) Γ q.val).property⟩
        Summable F ∧ ‖∑' q, F q‖ ≤
          sIntegerPeriodicResidueL1 K (S : Set (HeightOneSpectrum (𝓞 K))) c hc
            (fun a => f (Ideal.Quotient.mk _ d * a)) *
          C * s.sup (schwartzSeminormFamily ℂ V ℂ) φ *
            (1 + ρ.val⁻¹) * X ^ (1 - A) := by
  have hclosure := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport
    K S ν μv h hlc hcs
  obtain ⟨D, hD, htail⟩ := exists_sIntegerSchwartzProfile_weighted_tail_bound K
    (S : Set (HeightOneSpectrum (𝓞 K))) Γ
    (sIntegerFiniteFourierTestFunction K S μv h) hclosure.1.continuous hclosure.2
    A hA M hM hOrder
  obtain ⟨s, C, _hC, hFT⟩ := traceSchwartzFourier_seminorm_bound K M 0
  refine ⟨s, D * (C : ℝ), mul_nonneg hD C.property, ?_⟩
  intro φ c hc f hinv d ρ X hX
  dsimp only
  let B := sIntegerPeriodicResidueL1 K (S : Set (HeightOneSpectrum (𝓞 K))) c hc
    (fun a => f (Ideal.Quotient.mk _ d * a))
  have hB : 0 ≤ B := sIntegerPeriodicResidueL1_nonneg K
    (S : Set (HeightOneSpectrum (𝓞 K))) c hc _
  obtain ⟨hsum, hbound⟩ := htail (traceSchwartzFourier K φ) ρ X hX
    (sIntegerPeriodicFourierOrbitWeight K (S : Set (HeightOneSpectrum (𝓞 K)))
      hS Γ c hc f hinv d) B hB
    (norm_sIntegerPeriodicFourierOrbitWeight_le_pullback_L1 K
      (S : Set (HeightOneSpectrum (𝓞 K))) hS Γ c hc f hinv d)
  refine ⟨hsum, hbound.trans ?_⟩
  have hfac : 0 ≤ B * D * (1 + ρ.val⁻¹) * X ^ (1 - A) :=
    mul_nonneg
      (mul_nonneg (mul_nonneg hB hD)
        (add_nonneg zero_le_one (inv_nonneg.mpr ρ.property.le)))
      (Real.rpow_nonneg (zero_le_one.trans hX) _)
  calc
    _ = (B * D * (1 + ρ.val⁻¹) * X ^ (1 - A)) *
        SchwartzMap.seminorm ℂ M 0 (traceSchwartzFourier K φ) := by ring
    _ ≤ (B * D * (1 + ρ.val⁻¹) * X ^ (1 - A)) *
        ((C : ℝ) * s.sup (schwartzSeminormFamily ℂ V ℂ) φ) :=
      mul_le_mul_of_nonneg_left (hFT φ) hfac
    _ = _ := by dsimp only [B]; ring

end HeckeGeneral.Analysis
