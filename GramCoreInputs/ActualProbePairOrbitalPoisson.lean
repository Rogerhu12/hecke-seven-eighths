import ActualProbePairPointwisePoisson
import ActualAdditiveGramUnitOrbits
import HeckeGeneral.Arithmetic.SUnitFiniteGeneration

/-!
UNCOMPILED / native 0. Actual first orbital Poisson under the ORIGINAL
sixthPowerUnits subgroup. Literal Gauss invariance and finite index are
proved inputs already available for this subgroup, not new hypotheses.
The dual orbit weight has a proved representative value equal to the
original full correlation. Both zero terms retain the genuine Haar covolume.
-/

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualProbePairOrbitalDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Bridge MeasureTheory
open ActualProbeGaussFourierDraft ActualProbePairFourierDraft ActualAdditiveGramDraft
open ActualProbePairPoissonDraft
open HeckeGeneral.Arithmetic.PeriodicFourier
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

local notation "SS" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer SS K
local notation "N" => NonzeroRingElements OS
local notation "Γ" => sixthPowerUnits K SS
local notation "Q" => SIntegerOrbits K SS Γ
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

local instance sixthUnits_finiteIndex : Subgroup.FiniteIndex Γ :=
  sUnit_power_range_finiteIndex K SS 6 (by decide)

local instance orbital_totalFinite (u v : NonzeroRingElements OS) :
    Finite (OS ⧸ commonFactorTotalIdeal (⊤ : Ideal OS) (Subtype.val u) (Subtype.val v)) := by
  letI : Finite (OS ⧸ Ideal.span ({(Subtype.val u) * (Subtype.val v)} : Set OS)) :=
    finite_sIntegerPrincipalResidue K SS _ (mul_ne_zero (Subtype.property u) (Subtype.property v))
  exact Finite.of_equiv _ (originalFullTotalPrincipalEquiv K SS u v).symm.toEquiv

local instance orbital_totalFintype (u v : NonzeroRingElements OS) :
    Fintype (OS ⧸ commonFactorTotalIdeal (⊤ : Ideal OS) (Subtype.val u) (Subtype.val v)) := Fintype.ofFinite _


def probePairOrbitCard (P : ProbeData K SS) (I J : ExteriorIdeal K SS) : ℂ :=
  (Fintype.card (OS ⧸ commonFactorTotalIdeal (⊤ : Ideal OS) (Subtype.val (probeGenerator K SS P.arithmetic I)) (Subtype.val (probeGenerator K SS P.arithmetic J))) : ℂ)

theorem probePairOrbitCard_ne_zero (P : ProbeData K SS) (I J : ExteriorIdeal K SS) : probePairOrbitCard K S P I J ≠ 0 := by
  unfold probePairOrbitCard
  rw [probePair_card_eq_modulusNorm]
  exact_mod_cast ne_of_gt (sIntegerElementNorm K SS
    ⟨(Subtype.val (probeGenerator K SS P.arithmetic I)) * (Subtype.val (probeGenerator K SS P.arithmetic J)), mul_ne_zero (Subtype.property (probeGenerator K SS P.arithmetic I)) (Subtype.property (probeGenerator K SS P.arithmetic J))⟩).property

/-- The literal negative-frequency Gauss pair on every original sector. -/
def probeNegativeGaussPairOrbitWeight (P : ProbeData K SS) (I J : ExteriorIdeal K SS) : Q → ℂ :=
  sIntegerPeriodicOrbitWeight K SS Γ ((Subtype.val (probeGenerator K SS P.arithmetic I)) * (Subtype.val (probeGenerator K SS P.arithmetic J)))
    (probeNegativeGaussPairResidue K SS P I J)
    (probeNegativeGaussPairResidue_literal_invariant K SS P I J)

@[simp] theorem probeNegativeGaussPairOrbitWeight_mk (P : ProbeData K SS) (I J : ExteriorIdeal K SS) (a : N) :
    probeNegativeGaussPairOrbitWeight K S P I J (Quotient.mk _ a) =
      probeGauss K SS P I (-a.val) * conj (probeGauss K SS P J (-a.val)) := by
  unfold probeNegativeGaussPairOrbitWeight
  rw [sIntegerPeriodicOrbitWeight_mk, probeNegativeGaussPairResidue_mk]

/-- Fourier invariance supplies descent. The inverse finite card is removed
by the representative theorem below, including zero/nonunit residue classes. -/
def probeOriginalCorrelationOrbitWeight (P : ProbeData K SS) (I J : ExteriorIdeal K SS) (q : Q) : ℂ :=
  (probePairOrbitCard K S P I J)⁻¹ *
    sIntegerPeriodicFourierOrbitWeight K SS P.arithmetic.different_outside Γ
      ((Subtype.val (probeGenerator K SS P.arithmetic I)) * (Subtype.val (probeGenerator K SS P.arithmetic J))) (mul_ne_zero (Subtype.property (probeGenerator K SS P.arithmetic I)) (Subtype.property (probeGenerator K SS P.arithmetic J)))
      (probeNegativeGaussPairResidue K SS P I J)
      (probeNegativeGaussPairResidue_literal_invariant K SS P I J) 1 q

@[simp] theorem probeOriginalCorrelationOrbitWeight_mk (P : ProbeData K SS) (I J : ExteriorIdeal K SS) (a : N) :
    probeOriginalCorrelationOrbitWeight K S P I J (Quotient.mk _ a) =
      sIntegerSexticOriginalFullCorrelation K SS P.arithmetic.root6
        P.arithmetic.primitive6 P.arithmetic.embedding
        (probeArithmetic_six_support K SS P.arithmetic) (probeGenerator K SS P.arithmetic I) (probeGenerator K SS P.arithmetic J) a.val := by
  unfold probeOriginalCorrelationOrbitWeight
  rw [sIntegerPeriodicFourierOrbitWeight_mk,
    probeNegativeGaussPairResidue_divisorFourier_mk]
  change (probePairOrbitCard K S P I J)⁻¹ *
    (probePairOrbitCard K S P I J * _) = _
  rw [← mul_assoc, inv_mul_cancel₀ (probePairOrbitCard_ne_zero K S P I J), one_mul]

theorem probePairFourierOrbit_eq_card_mul (P : ProbeData K SS) (I J : ExteriorIdeal K SS) (q : Q) :
    sIntegerPeriodicFourierOrbitWeight K SS P.arithmetic.different_outside Γ
      ((Subtype.val (probeGenerator K SS P.arithmetic I)) * (Subtype.val (probeGenerator K SS P.arithmetic J))) (mul_ne_zero (Subtype.property (probeGenerator K SS P.arithmetic I)) (Subtype.property (probeGenerator K SS P.arithmetic J)))
      (probeNegativeGaussPairResidue K SS P I J)
      (probeNegativeGaussPairResidue_literal_invariant K SS P I J) 1 q =
    probePairOrbitCard K S P I J * probeOriginalCorrelationOrbitWeight K S P I J q := by
  unfold probeOriginalCorrelationOrbitWeight
  rw [← mul_assoc, mul_inv_cancel₀ (probePairOrbitCard_ne_zero K S P I J), one_mul]

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
  [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
  (μv : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
  [∀ p, (μv p).IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

private theorem periodicOrbitWeight_one_pullback (c : OS)
    (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ)
    (hinv : ∀ u : Γ, ∀ a : OS,
      f (Ideal.Quotient.mk _ (((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K u.val).val * a)) =
        f (Ideal.Quotient.mk _ a)) :
    sIntegerPeriodicOrbitWeight K SS Γ c
      (fun z => f (Ideal.Quotient.mk _ (1 : OS) * z))
      (sIntegerPeriodic_divisorPullback_literal_invariant K S Γ c f hinv 1) =
    sIntegerPeriodicOrbitWeight K SS Γ c f hinv := by
  funext q
  refine Quotient.inductionOn q ?_
  intro a
  simp only [sIntegerPeriodicOrbitWeight_mk, map_one, one_mul]

set_option diagnostics true in
set_option maxHeartbeats 800000 in
include μ ν in
/-- The actual original-sector first orbital Poisson identity. Cardinality
and modulus norm cancel, while the discriminant and Haar covolume remain. -/
theorem probeGauss_pair_orbital_poisson (P : ProbeData K SS) (I J : ExteriorIdeal K SS)
    (φ : SchwartzMap V ℂ)
    (h : ∀ p : HeightOneSpectrum (𝓞 K), p.adicCompletion K → ℂ)
    (hlc : ∀ p ∈ S, IsLocallyConstant (h p))
    (hcs : ∀ p ∈ S, HasCompactSupport (h p)) (r : {r : ℝ // 0 < r}) :
    let c : OS := (Subtype.val (probeGenerator K SS P.arithmetic I)) * (Subtype.val (probeGenerator K SS P.arithmetic J))
    let hc : c ≠ 0 := mul_ne_zero (Subtype.property (probeGenerator K SS P.arithmetic I)) (Subtype.property (probeGenerator K SS P.arithmetic J))
    let rDual : {r : ℝ // 0 < r} :=
      ⟨(r.val * (sIntegerElementNorm K SS ⟨c, hc⟩).val)⁻¹,
        inv_pos.mpr (mul_pos r.property (sIntegerElementNorm K SS ⟨c, hc⟩).property)⟩
    let D : ℂ := (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K /
      Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ)
    let F : OS → ℂ := sIntegerSexticOriginalFullCorrelation K SS
      P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding
      (probeArithmetic_six_support K SS P.arithmetic) (probeGenerator K SS P.arithmetic I) (probeGenerator K SS P.arithmetic J)
    sIntegerWeightedOrbitalSeries K S Γ φ (sIntegerFiniteTestFunction K S h) r
        (probeNegativeGaussPairOrbitWeight K S P I J) =
      ((r.val : ℂ)⁻¹ * D) *
        sIntegerWeightedOrbitalSeries K S Γ (traceSchwartzFourier K φ)
          (sIntegerFiniteFourierTestFunction K S μv h) rDual
          (probeOriginalCorrelationOrbitWeight K S P I J) +
      ((sUnitHaarCovolume K SS Γ).toReal : ℂ) *
        (((r.val : ℂ)⁻¹ * D) *
            (F 0 * sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ) h 0) -
          (probeGauss K SS P I 0 * conj (probeGauss K SS P J 0)) *
            sIntegerTensorTerm K S (traceSchwartzToMixed K φ) h 0) := by
  let c : OS := (Subtype.val (probeGenerator K SS P.arithmetic I)) * (Subtype.val (probeGenerator K SS P.arithmetic J))
  let hc : c ≠ 0 := mul_ne_zero (Subtype.property (probeGenerator K SS P.arithmetic I)) (Subtype.property (probeGenerator K SS P.arithmetic J))
  let rDual : {r : ℝ // 0 < r} :=
    ⟨(r.val * (sIntegerElementNorm K SS ⟨c, hc⟩).val)⁻¹,
      inv_pos.mpr (mul_pos r.property (sIntegerElementNorm K SS ⟨c, hc⟩).property)⟩
  let D : ℂ := (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K /
    Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ)
  let B : ℂ := (r.val : ℂ)⁻¹ * D
  let C : ℂ := B * ((sIntegerElementNorm K SS ⟨c, hc⟩).val : ℂ)⁻¹
  let card : ℂ := probePairOrbitCard K S P I J
  let F : OS → ℂ := sIntegerSexticOriginalFullCorrelation K SS
    P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding
    (probeArithmetic_six_support K SS P.arithmetic) (probeGenerator K SS P.arithmetic I) (probeGenerator K SS P.arithmetic J)
  let wR : Q → ℂ := sIntegerPeriodicFourierOrbitWeight K SS
    P.arithmetic.different_outside Γ c hc (probeNegativeGaussPairResidue K SS P I J)
    (probeNegativeGaussPairResidue_literal_invariant K SS P I J) 1
  let zDual : ℂ := sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ) h 0
  let zOriginal : ℂ := sIntegerTensorTerm K S (traceSchwartzToMixed K φ) h 0
  let zGauss : ℂ := probeGauss K SS P I 0 * conj (probeGauss K SS P J 0)
  let covol : ℂ := ((sUnitHaarCovolume K SS Γ).toReal : ℂ)
  have hcancel : C * card = B := by
    simpa only [C, B, card, probePairOrbitCard, c, hc] using
      probePair_poisson_prefactor K SS P I J (r.val : ℂ)⁻¹ D
  have hfzero : sIntegerPeriodicDivisorFourier K SS P.arithmetic.different_outside
      c hc (probeNegativeGaussPairResidue K SS P I J) 1 0 = card * F 0 := by
    simpa only [map_zero, card, probePairOrbitCard, F, c, hc] using
      probeNegativeGaussPairResidue_divisorFourier_mk K SS P I J (0 : OS)
  have hzGauss : probeNegativeGaussPairResidue K SS P I J 0 = zGauss := by
    simpa only [map_zero, neg_zero, zGauss] using
      probeNegativeGaussPairResidue_mk K SS P I J (0 : OS)
  have hseries :
      sIntegerWeightedOrbitalSeries K S Γ (traceSchwartzFourier K φ)
        (sIntegerFiniteFourierTestFunction K S μv h) rDual wR =
      card * sIntegerWeightedOrbitalSeries K S Γ (traceSchwartzFourier K φ)
        (sIntegerFiniteFourierTestFunction K S μv h) rDual
        (probeOriginalCorrelationOrbitWeight K S P I J) := by
    unfold sIntegerWeightedOrbitalSeries
    simp_rw [show ∀ q : Q, wR q =
      card * probeOriginalCorrelationOrbitWeight K S P I J q from
        fun q => probePairFourierOrbit_eq_card_mul K S P I J q, mul_assoc]
    exact tsum_mul_left
  have horb := sIntegerPeriodicOrbitalPoisson K S Γ P.arithmetic.different_outside
    c hc ν μv μ φ h hlc hcs (probeNegativeGaussPairResidue K SS P I J)
    (probeNegativeGaussPairResidue_literal_invariant K SS P I J) 1 r
  have hweight : sIntegerPeriodicOrbitWeight K SS Γ c
      (probeNegativeGaussPairResidue K SS P I J)
      (probeNegativeGaussPairResidue_literal_invariant K SS P I J) =
      probeNegativeGaussPairOrbitWeight K S P I J := rfl
  dsimp only at horb
  rw [periodicOrbitWeight_one_pullback (K := K) (S := S) (c := c)
    (f := probeNegativeGaussPairResidue K SS P I J)
    (hinv := probeNegativeGaussPairResidue_literal_invariant K SS P I J),
    hweight, hfzero, hzGauss] at horb
  change sIntegerWeightedOrbitalSeries K S Γ φ (sIntegerFiniteTestFunction K S h) r
      (probeNegativeGaussPairOrbitWeight K S P I J) =
    C * sIntegerWeightedOrbitalSeries K S Γ (traceSchwartzFourier K φ)
      (sIntegerFiniteFourierTestFunction K S μv h) rDual wR +
      covol * (C * ((card * F 0) * zDual) - zGauss * zOriginal) at horb
  change sIntegerWeightedOrbitalSeries K S Γ φ (sIntegerFiniteTestFunction K S h) r
      (probeNegativeGaussPairOrbitWeight K S P I J) =
    B * sIntegerWeightedOrbitalSeries K S Γ (traceSchwartzFourier K φ)
      (sIntegerFiniteFourierTestFunction K S μv h) rDual
      (probeOriginalCorrelationOrbitWeight K S P I J) +
      covol * (B * (F 0 * zDual) - zGauss * zOriginal)
  rw [hseries] at horb
  calc
    _ = C * (card * sIntegerWeightedOrbitalSeries K S Γ (traceSchwartzFourier K φ)
        (sIntegerFiniteFourierTestFunction K S μv h) rDual
        (probeOriginalCorrelationOrbitWeight K S P I J)) +
        covol * (C * ((card * F 0) * zDual) - zGauss * zOriginal) := horb
    _ = (C * card) * sIntegerWeightedOrbitalSeries K S Γ (traceSchwartzFourier K φ)
        (sIntegerFiniteFourierTestFunction K S μv h) rDual
        (probeOriginalCorrelationOrbitWeight K S P I J) +
        covol * ((C * card) * (F 0 * zDual) - zGauss * zOriginal) := by
          simp only [mul_assoc]
    _ = _ := by rw [hcancel]

include μ ν in
/-- Specialization to the SAME probe tensor and its actual finite-factor
product, on all sectors of the original sixth-power subgroup. -/
theorem probeGauss_pair_additive_orbital_poisson (P : ProbeData K SS) (I J : ExteriorIdeal K SS) (r : {r : ℝ // 0 < r}) :
    let c : OS := (Subtype.val (probeGenerator K SS P.arithmetic I)) * (Subtype.val (probeGenerator K SS P.arithmetic J))
    let hc : c ≠ 0 := mul_ne_zero (Subtype.property (probeGenerator K SS P.arithmetic I)) (Subtype.property (probeGenerator K SS P.arithmetic J))
    let rDual : {r : ℝ // 0 < r} :=
      ⟨(r.val * (sIntegerElementNorm K SS ⟨c, hc⟩).val)⁻¹,
        inv_pos.mpr (mul_pos r.property (sIntegerElementNorm K SS ⟨c, hc⟩).property)⟩
    let D : ℂ := (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K /
      Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ)
    let F : OS → ℂ := sIntegerSexticOriginalFullCorrelation K SS
      P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding
      (probeArithmetic_six_support K SS P.arithmetic) (probeGenerator K SS P.arithmetic I) (probeGenerator K SS P.arithmetic J)
    sIntegerWeightedOrbitalSeries K S Γ P.additive.infiniteTest
        (fun y => ∏ p : SS, P.additive.finiteTest p (y p)) r
        (probeNegativeGaussPairOrbitWeight K S P I J) =
      ((r.val : ℂ)⁻¹ * D) *
        sIntegerWeightedOrbitalSeries K S Γ (traceSchwartzFourier K P.additive.infiniteTest)
          (sIntegerFiniteFourierTestFunction K S μv (probeFiniteFamily K S P)) rDual
          (probeOriginalCorrelationOrbitWeight K S P I J) +
      ((sUnitHaarCovolume K SS Γ).toReal : ℂ) *
        (((r.val : ℂ)⁻¹ * D) *
            (F 0 * sIntegerDualTensorTerm K μv S
              (traceSchwartzToMixed K P.additive.infiniteTest) (probeFiniteFamily K S P) 0) -
          (probeGauss K SS P I 0 * conj (probeGauss K SS P J 0)) *
            sIntegerTensorTerm K S (traceSchwartzToMixed K P.additive.infiniteTest)
              (probeFiniteFamily K S P) 0) := by
  simpa only [probeFiniteTestFunction_eq] using
    probeGauss_pair_orbital_poisson (K := K) (S := S) (P := P) (I := I) (J := J)
      (ν := ν) (μv := μv) (μ := μ) P.additive.infiniteTest
      (probeFiniteFamily K S P) (probeFiniteFamily_locallyConstant K S P)
      (probeFiniteFamily_compactSupport K S P) r

end HeckeGeneral.ThetaSkeleton.Physical.ActualProbePairOrbitalDraft
