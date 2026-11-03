import ActualProbePairPeriodicFourier
import HeckeGeneral.Analysis.SIntegerPeriodicOrbitalPoisson

/-!
UNCOMPILED / native 0. First periodic Poisson for the SAME actual negative
Gauss pair and original full correlation. The existing pointwise PSF supplies
convergence; no extra Summable premise or unit subgroup is introduced. The
actual Fourier tensor, shifted inverse norm-one argument and both zero terms
remain. Finite quotient cardinality cancels only its genuine modulus norm.
-/

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualProbePairPoissonDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Bridge MeasureTheory
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Arithmetic.PeriodicFourier
open ActualProbeGaussFourierDraft ActualProbePairFourierDraft
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

local notation "SS" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer SS K
local notation "N" => NonzeroRingElements OS
local notation "T" => sLocalNormOneGroup K SS
local notation "V" => mixedEmbedding.euclidean.mixedSpace K


local instance probePoisson_totalFinite (u v : NonzeroRingElements OS) :
    Finite (OS ⧸ commonFactorTotalIdeal (⊤ : Ideal OS) (Subtype.val u) (Subtype.val v)) := by
  letI : Finite (OS ⧸ Ideal.span ({(Subtype.val u) * (Subtype.val v)} : Set OS)) :=
    finite_sIntegerPrincipalResidue K SS _ (mul_ne_zero (Subtype.property u) (Subtype.property v))
  exact Finite.of_equiv _ (originalFullTotalPrincipalEquiv K SS u v).symm.toEquiv

local instance probePoisson_totalFintype (u v : NonzeroRingElements OS) :
    Fintype (OS ⧸ commonFactorTotalIdeal (⊤ : Ideal OS) (Subtype.val u) (Subtype.val v)) := Fintype.ofFinite _


/-- Extend exactly the probe's individual finite factors by zero off S.
Only its restriction to S is used by the actual tensor and local Fourier. -/
def probeFiniteFamily (P : ProbeData K SS) (p : HeightOneSpectrum (𝓞 K)) : p.adicCompletion K → ℂ :=
  if hp : p ∈ S then P.additive.finiteTest ⟨p, hp⟩ else 0

@[simp] theorem probeFiniteFamily_mem (P : ProbeData K SS) (p : SS) :
    probeFiniteFamily K S P p.val = P.additive.finiteTest p := by
  unfold probeFiniteFamily
  rw [dif_pos (show p.val ∈ S from p.property)]

theorem probeFiniteFamily_locallyConstant (P : ProbeData K SS) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ S) :
    IsLocallyConstant (probeFiniteFamily K S P p) := by
  simpa only [probeFiniteFamily, dif_pos hp] using P.additive.finite_locallyConstant ⟨p, hp⟩

theorem probeFiniteFamily_compactSupport (P : ProbeData K SS) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ S) :
    HasCompactSupport (probeFiniteFamily K S P p) := by
  simpa only [probeFiniteFamily, dif_pos hp] using P.additive.finite_compactSupport ⟨p, hp⟩

theorem probeFiniteTestFunction_eq (P : ProbeData K SS) :
    sIntegerFiniteTestFunction K S (probeFiniteFamily K S P) =
      (fun y => ∏ p : SS, P.additive.finiteTest p (y p)) := by
  funext y
  unfold sIntegerFiniteTestFunction
  apply Finset.prod_congr rfl
  intro p _
  rw [probeFiniteFamily_mem]

/-- The primal Schwartz term is the SAME P.additive tensor, not an arbitrary
joint finite function. Its scale convention is the existing section-times-x. -/
theorem probeSchwartzTerm_eq_additiveTest (P : ProbeData K SS) (r : {r : ℝ // 0 < r}) (a : N) (x : T) :
    sIntegerSchwartzTerm K SS P.additive.infiniteTest
        (sIntegerFiniteTestFunction K S (probeFiniteFamily K S P)) r a x =
      additiveTest K SS P.additive
        (sLocalNormSection K SS r * (x : sLocalMultiplicativeGroup K SS) *
          sLocalNonzeroIntegerDiagonal K SS a) := by
  unfold sIntegerSchwartzTerm additiveTest
  rw [probeFiniteTestFunction_eq]

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
/-- Actual first periodic Poisson, at every positive radius and norm-one
point. The original correlation F and both zero contributions are literal;
the finite Fourier cardinality and inverse modulus norm have disappeared
from the prefactor. The dual radius still contains the TRUE modulus norm. -/
theorem probeGauss_pair_pointwise_poisson (P : ProbeData K SS) (I J : ExteriorIdeal K SS)
    (φ : SchwartzMap V ℂ)
    (h : ∀ p : HeightOneSpectrum (𝓞 K), p.adicCompletion K → ℂ)
    (hlc : ∀ p ∈ S, IsLocallyConstant (h p))
    (hcs : ∀ p ∈ S, HasCompactSupport (h p))
    (r : {r : ℝ // 0 < r}) (x : T) :
    let c : OS := (Subtype.val (probeGenerator K SS P.arithmetic I)) * (Subtype.val (probeGenerator K SS P.arithmetic J))
    let hc : c ≠ 0 := mul_ne_zero (Subtype.property (probeGenerator K SS P.arithmetic I)) (Subtype.property (probeGenerator K SS P.arithmetic J))
    let rDual : {r : ℝ // 0 < r} :=
      ⟨(r.val * (sIntegerElementNorm K SS ⟨c, hc⟩).val)⁻¹,
        inv_pos.mpr (mul_pos r.property (sIntegerElementNorm K SS ⟨c, hc⟩).property)⟩
    let t : T := sIntegerModulusNormOneShift K SS c hc
    let D : ℂ := (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K /
      Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ)
    let F : OS → ℂ := sIntegerSexticOriginalFullCorrelation K SS
      P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding
      (probeArithmetic_six_support K SS P.arithmetic) (probeGenerator K SS P.arithmetic I) (probeGenerator K SS P.arithmetic J)
    (∑' a : N, (probeGauss K SS P I (-a.val) * conj (probeGauss K SS P J (-a.val))) *
      sIntegerSchwartzTerm K SS φ (sIntegerFiniteTestFunction K S h) r a x) =
      ((r.val : ℂ)⁻¹ * D) * (∑' a : N, F a.val *
        sIntegerSchwartzTerm K SS (traceSchwartzFourier K φ)
          (sIntegerFiniteFourierTestFunction K S μv h) rDual a (t * x⁻¹)) +
      (((r.val : ℂ)⁻¹ * D) *
          (F 0 * sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ) h 0) -
        (probeGauss K SS P I 0 * conj (probeGauss K SS P J 0)) *
          sIntegerTensorTerm K S (traceSchwartzToMixed K φ) h 0) := by
  let c : OS := (Subtype.val (probeGenerator K SS P.arithmetic I)) * (Subtype.val (probeGenerator K SS P.arithmetic J))
  let hc : c ≠ 0 := mul_ne_zero (Subtype.property (probeGenerator K SS P.arithmetic I)) (Subtype.property (probeGenerator K SS P.arithmetic J))
  let rDual : {r : ℝ // 0 < r} :=
    ⟨(r.val * (sIntegerElementNorm K SS ⟨c, hc⟩).val)⁻¹,
      inv_pos.mpr (mul_pos r.property (sIntegerElementNorm K SS ⟨c, hc⟩).property)⟩
  let t : T := sIntegerModulusNormOneShift K SS c hc
  let D : ℂ := (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K /
    Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ)
  let B : ℂ := (r.val : ℂ)⁻¹ * D
  let C : ℂ := B * ((sIntegerElementNorm K SS ⟨c, hc⟩).val : ℂ)⁻¹
  let card : ℂ := (Fintype.card (OS ⧸ commonFactorTotalIdeal (⊤ : Ideal OS) (Subtype.val (probeGenerator K SS P.arithmetic I)) (Subtype.val (probeGenerator K SS P.arithmetic J))) : ℂ)
  let F : OS → ℂ := sIntegerSexticOriginalFullCorrelation K SS
    P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding
    (probeArithmetic_six_support K SS P.arithmetic) (probeGenerator K SS P.arithmetic I) (probeGenerator K SS P.arithmetic J)
  let dual : N → ℂ := fun a => sIntegerSchwartzTerm K SS (traceSchwartzFourier K φ)
    (sIntegerFiniteFourierTestFunction K S μv h) rDual a (t * x⁻¹)
  let zDual : ℂ := sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ) h 0
  let zOriginal : ℂ := sIntegerTensorTerm K S (traceSchwartzToMixed K φ) h 0
  let zGauss : ℂ := probeGauss K SS P I 0 * conj (probeGauss K SS P J 0)
  have hcancel : C * card = B := by
    simpa only [C, B, card, c, hc] using
      probePair_poisson_prefactor K SS P I J (r.val : ℂ)⁻¹ D
  have hfzero :
      sIntegerPeriodicDivisorFourier K SS P.arithmetic.different_outside c hc
        (probeNegativeGaussPairResidue K SS P I J) 1 0 = card * F 0 := by
    simpa only [map_zero, card, F, c, hc] using
      probeNegativeGaussPairResidue_divisorFourier_mk K SS P I J (0 : OS)
  have hzGauss : probeNegativeGaussPairResidue K SS P I J 0 = zGauss := by
    simpa only [map_zero, neg_zero, zGauss] using
      probeNegativeGaussPairResidue_mk K SS P I J (0 : OS)
  letI : MeasurableSpace T := borel T
  letI : BorelSpace T := ⟨rfl⟩
  have hpoint := sIntegerPeriodicSchwartzTerm_poisson K S
    P.arithmetic.different_outside c hc ν μv μ φ h hlc hcs
    (probeNegativeGaussPairResidue K SS P I J) 1 r x
  dsimp only at hpoint
  simp only [c, one_mul, neg_zero, probeNegativeGaussPairResidue_mk,
    probeNegativeGaussPairResidue_divisorFourier_mk, hfzero, hzGauss] at hpoint
  change (∑' a : N, (probeGauss K SS P I (-a.val) * conj (probeGauss K SS P J (-a.val))) *
      sIntegerSchwartzTerm K SS φ (sIntegerFiniteTestFunction K S h) r a x) =
    C * (∑' a : N, (card * F a.val) * dual a) +
      (C * ((card * F 0) * zDual) - zGauss * zOriginal) at hpoint
  change (∑' a : N, (probeGauss K SS P I (-a.val) * conj (probeGauss K SS P J (-a.val))) *
      sIntegerSchwartzTerm K SS φ (sIntegerFiniteTestFunction K S h) r a x) =
    B * (∑' a : N, F a.val * dual a) + (B * (F 0 * zDual) - zGauss * zOriginal)
  have hsum : (∑' a : N, (card * F a.val) * dual a) =
      card * (∑' a : N, F a.val * dual a) := by
    simp_rw [mul_assoc]
    exact tsum_mul_left
  calc
    _ = C * (∑' a : N, (card * F a.val) * dual a) +
        (C * ((card * F 0) * zDual) - zGauss * zOriginal) := hpoint
    _ = (C * card) * (∑' a : N, F a.val * dual a) +
        ((C * card) * (F 0 * zDual) - zGauss * zOriginal) := by rw [hsum]; ring
    _ = _ := by rw [hcancel]

include μ ν in
/-- The first Poisson identity for the original probe's literal infinite
Schwartz test and product of individual finite tests. Both zero terms are
kept, with no support-away-from-zero shortcut. -/
theorem probeGauss_pair_additive_pointwise_poisson (P : ProbeData K SS) (I J : ExteriorIdeal K SS)
    (r : {r : ℝ // 0 < r}) (x : T) :
    let c : OS := (Subtype.val (probeGenerator K SS P.arithmetic I)) * (Subtype.val (probeGenerator K SS P.arithmetic J))
    let hc : c ≠ 0 := mul_ne_zero (Subtype.property (probeGenerator K SS P.arithmetic I)) (Subtype.property (probeGenerator K SS P.arithmetic J))
    let rDual : {r : ℝ // 0 < r} :=
      ⟨(r.val * (sIntegerElementNorm K SS ⟨c, hc⟩).val)⁻¹,
        inv_pos.mpr (mul_pos r.property (sIntegerElementNorm K SS ⟨c, hc⟩).property)⟩
    let t : T := sIntegerModulusNormOneShift K SS c hc
    let D : ℂ := (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K /
      Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ)
    let F : OS → ℂ := sIntegerSexticOriginalFullCorrelation K SS
      P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding
      (probeArithmetic_six_support K SS P.arithmetic) (probeGenerator K SS P.arithmetic I) (probeGenerator K SS P.arithmetic J)
    (∑' a : N, (probeGauss K SS P I (-a.val) * conj (probeGauss K SS P J (-a.val))) *
      additiveTest K SS P.additive
        (sLocalNormSection K SS r * (x : sLocalMultiplicativeGroup K SS) *
          sLocalNonzeroIntegerDiagonal K SS a)) =
      ((r.val : ℂ)⁻¹ * D) * (∑' a : N, F a.val *
        sIntegerSchwartzTerm K SS (traceSchwartzFourier K P.additive.infiniteTest)
          (sIntegerFiniteFourierTestFunction K S μv (probeFiniteFamily K S P))
          rDual a (t * x⁻¹)) +
      (((r.val : ℂ)⁻¹ * D) *
          (F 0 * sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K P.additive.infiniteTest)
            (probeFiniteFamily K S P) 0) -
        (probeGauss K SS P I 0 * conj (probeGauss K SS P J 0)) *
          sIntegerTensorTerm K S (traceSchwartzToMixed K P.additive.infiniteTest)
            (probeFiniteFamily K S P) 0) := by
  simpa only [probeSchwartzTerm_eq_additiveTest] using
    probeGauss_pair_pointwise_poisson K S ν μv μ P I J P.additive.infiniteTest
      (probeFiniteFamily K S P) (probeFiniteFamily_locallyConstant K S P)
      (probeFiniteFamily_compactSupport K S P) r x

end HeckeGeneral.ThetaSkeleton.Physical.ActualProbePairPoissonDraft
