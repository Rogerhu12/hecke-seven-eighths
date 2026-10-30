import CubicSieve.GaussPairLiteral
import HeckeGeneral.Analysis.SIntegerPeriodicOrbitalPoisson
import HeckeGeneral.Arithmetic.SIntegerOrbitDilation

/-! Actual mixed cubic orbital Poisson on the original sixth-power S-unit sectors.
The modulus is the literal product of the chosen generators. Both zero terms,
all divisor pullbacks and the exact separated Gauss phase are retained. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicSieve.GaussPairOrbitalPoisson

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.Analysis HeckeGeneral.Bridge
open CubicSieve.GaussPairLiteral
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup (Set.unit (S : Set (HeightOneSpectrum (𝓞 K))) K)) [Γ.FiniteIndex]
variable (hΓ : Γ ≤ (powMonoidHom 6 : Set.unit (S : Set (HeightOneSpectrum (𝓞 K))) K →*
  Set.unit (S : Set (HeightOneSpectrum (𝓞 K))) K).range)
variable (I J : ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K))))
  (hI : Squarefree I.val.val) (hJ : Squarefree J.val.val)

include hΓ in
theorem row_literal_invariant : ∀ u : Γ, ∀ a : OS,
    literalRow K S D I J hI hJ (Ideal.Quotient.mk _
      ((Set.unitEquivUnitsInteger (S : Set (HeightOneSpectrum (𝓞 K))) K u.val).val * a)) =
        literalRow K S D I J hI hJ (Ideal.Quotient.mk _ a) := by
  intro u a
  have hL (L : ExteriorIdeal K S) :
      idealSymbol K S D L
        ((Set.unitEquivUnitsInteger (S : Set (HeightOneSpectrum (𝓞 K))) K u.val).val * a) =
        idealSymbol K S D L a :=
    sIntegerSexticIdealEvaluation_literal_invariant K S D.root6 D.primitive6 D.embedding
      L.val.val (nonZeroDivisors.coe_ne_zero L.val) L.property
      (fun p hp => D.away_six p (L.property p hp)) Γ hΓ u a
  rw [literalRow_mk, literalRow_mk, hL I, hL J]

def rowWeight : SIntegerOrbits K S Γ → ℂ :=
  sIntegerPeriodicOrbitWeight K S Γ (D.generator I * D.generator J)
    (literalRow K S D I J hI hJ) (row_literal_invariant K S D Γ hΓ I J hI hJ)

@[simp] theorem rowWeight_mk (a : NonzeroRingElements OS) :
    rowWeight K S D Γ hΓ I J hI hJ (Quotient.mk _ a) =
      literalRow K S D I J hI hJ (Ideal.Quotient.mk _ a.val) := rfl

theorem fourierWeight_eq (hD : AllowedGeneratorInput K S D)
    (hcop : IsCoprime I.val.val J.val.val) (d : OS) (q : SIntegerOrbits K S Γ) :
    sIntegerPeriodicFourierOrbitWeight K S D.different_outside Γ
      (D.generator I * D.generator J)
      (mul_ne_zero (D.generator_ne_zero I) (D.generator_ne_zero J))
      (literalRow K S D I J hI hJ) (row_literal_invariant K S D Γ hΓ I J hI hJ) d q =
      (literalRow K S D I J hI hJ (Ideal.Quotient.mk _ d) *
        (Real.sqrt (exteriorNorm K S I * exteriorNorm K S J) : ℂ) *
        (star (thetaGamma K S D I 2) * thetaGamma K S D J 2)) *
          star (rowWeight K S D Γ hΓ I J hI hJ q) := by
  refine Quotient.inductionOn q (fun a => ?_)
  rw [sIntegerPeriodicFourierOrbitWeight_mk, rowWeight_mk,
    literal_divisorFourier K S D hD I J hI hJ hcop]
  ring

theorem modulus_norm (hD : AllowedGeneratorInput K S D) :
    (sIntegerElementNorm K S
      ⟨D.generator I * D.generator J,
        mul_ne_zero (D.generator_ne_zero I) (D.generator_ne_zero J)⟩).val =
      exteriorNorm K S I * exteriorNorm K S J := by
  change (sIntegerElementNorm K S (sIntegerNonzeroMul K S
    ⟨D.generator I, D.generator_ne_zero I⟩
    ⟨D.generator J, D.generator_ne_zero J⟩)).val = _
  rw [sIntegerElementNorm_nonzeroMul]
  exact congrArg₂ (fun x y : ℝ => x * y) (hD.generator_norm I) (hD.generator_norm J)

/-- The actual dual radius becomes M/(NI*NJ), with no generator phase change. -/
theorem dual_radius_eq (hD : AllowedGeneratorInput K S D) (M : ℝ) :
    (M⁻¹ * (sIntegerElementNorm K S
      ⟨D.generator I * D.generator J,
        mul_ne_zero (D.generator_ne_zero I) (D.generator_ne_zero J)⟩).val)⁻¹ =
      M / (exteriorNorm K S I * exteriorNorm K S J) := by
  rw [modulus_norm K S D I J hD]
  simp only [mul_inv_rev, inv_inv, div_eq_mul_inv, mul_comm]

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ hΓ in
theorem pair_orbital_poisson (hD : AllowedGeneratorInput K S D)
    (hcop : IsCoprime I.val.val J.val.val) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (d : OS)
    (r : {r : ℝ // 0 < r}) :
    let c := D.generator I * D.generator J
    let hc := mul_ne_zero (D.generator_ne_zero I) (D.generator_ne_zero J)
    let f := literalRow K S D I J hI hJ
    let hinv := row_literal_invariant K S D Γ hΓ I J hI hJ
    let g := fun z => f (Ideal.Quotient.mk _ d * z)
    let hg := sIntegerPeriodic_divisorPullback_literal_invariant K S Γ c f hinv d
    let C : ℂ := (r.val : ℂ)⁻¹ *
      (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K / Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) *
      ((sIntegerElementNorm K S ⟨c, hc⟩).val : ℂ)⁻¹
    let rDual : {r : ℝ // 0 < r} :=
      ⟨(r.val * (sIntegerElementNorm K S ⟨c, hc⟩).val)⁻¹,
        inv_pos.mpr (mul_pos r.property (sIntegerElementNorm K S ⟨c, hc⟩).property)⟩
    let G : ℂ := f (Ideal.Quotient.mk _ d) *
      (Real.sqrt (exteriorNorm K S I * exteriorNorm K S J) : ℂ) *
      (star (thetaGamma K S D I 2) * thetaGamma K S D J 2)
    sIntegerWeightedOrbitalSeries K S Γ φ (sIntegerFiniteTestFunction K S h) r
        (sIntegerPeriodicOrbitWeight K S Γ c g hg) =
      (C * G) * sIntegerWeightedOrbitalSeries K S Γ (traceSchwartzFourier K φ)
        (sIntegerFiniteFourierTestFunction K S μv h) rDual
        (fun q => star (rowWeight K S D Γ hΓ I J hI hJ q)) +
      ((sUnitHaarCovolume K S Γ).toReal : ℂ) *
        (C * (G * star (f 0) *
          sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ) h 0) -
            f 0 * sIntegerTensorTerm K S (traceSchwartzToMixed K φ) h 0) := by
  have hp := sIntegerPeriodicOrbitalPoisson K S Γ D.different_outside
    (D.generator I * D.generator J)
    (mul_ne_zero (D.generator_ne_zero I) (D.generator_ne_zero J)) ν μv μ φ h hlc hcs
    (literalRow K S D I J hI hJ) (row_literal_invariant K S D Γ hΓ I J hI hJ) d r
  dsimp only at hp ⊢
  rw [literal_divisorFourier K S D hD I J hI hJ hcop d 0] at hp
  have hweight : sIntegerPeriodicFourierOrbitWeight K S D.different_outside Γ
      (D.generator I * D.generator J)
      (mul_ne_zero (D.generator_ne_zero I) (D.generator_ne_zero J))
      (literalRow K S D I J hI hJ) (row_literal_invariant K S D Γ hΓ I J hI hJ) d =
      fun q => (literalRow K S D I J hI hJ (Ideal.Quotient.mk _ d) *
        (Real.sqrt (exteriorNorm K S I * exteriorNorm K S J) : ℂ) *
        (star (thetaGamma K S D I 2) * thetaGamma K S D J 2)) *
          star (rowWeight K S D Γ hΓ I J hI hJ q) :=
    funext (fourierWeight_eq K S D Γ hΓ I J hI hJ hD hcop d)
  rw [hweight] at hp
  simp only [sIntegerWeightedOrbitalSeries, mul_assoc, tsum_mul_left] at hp ⊢
  convert hp using 1 <;> ring

end CubicSieve.GaussPairOrbitalPoisson
