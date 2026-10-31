import Expansion.ActualOuterInitialTransport
import Expansion.ActualOuterComponents

/-!
# Actual exterior-height tails after original row summation

The complete initial line (5,5,3) lies in one fixed absolute swept tube.
Its nonprincipal rows therefore have the summable power N(u)^(-2), before
any moderate or large cutoff is chosen.  This supplies one common initial
cube tail for the final expansion.  A separate finite-set statement keeps
arbitrary original cutoff exponents available for local transports.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain Set MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.Expansion.LargeRows
open Expansion.PhysicalInitialMellin
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
variable [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (nu : Measure (FiniteAdeleRing (𝓞 K) K)) [nu.IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K Sset)]
variable [BorelSpace (sLocalNormOneGroup K Sset)]

include nu in
/-- The entire actual nonprincipal initial cube tail has arbitrary height
decay with one fixed scale power, independent of the decay order. -/
theorem exists_actual_nonprincipal_initial_tail_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) (n : ℕ) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z H : ℝ, Z0 ≤ Z → 0 ≤ H →
      Summable (fun u : {u : FrequencyRow K Sset // ¬principalFrequencyRow K Sset u} =>
        ‖actualInitialRowTailIntegral K S mu P psi g ∅ Z H u.val‖) ∧
      ‖actualNonprincipalInitialTailSum K S mu P psi g Z H‖ ≤
        C * Z ^ (outerBoundaryScalePower 5 5 4) / (1 + H) ^ n := by
  obtain ⟨Cr, Z0, hCr, hZ0, hr⟩ := exists_actual_large_initial_tail_row_bound
    K S mu nu hcomplex P psi hcal hunram g (zeta := 1) zero_lt_one n
  let rows := {u : FrequencyRow K Sset // ¬principalFrequencyRow K Sset u}
  have hsum : Summable (fun u : rows => frequencyRowNorm K Sset u.val ^ (-2 : ℝ)) :=
    (summable_frequencyRowNorm_rpow K Sset (p := -2) (by norm_num)).subtype
      (fun u => ¬principalFrequencyRow K Sset u)
  let A : ℝ := ∑' u : rows, frequencyRowNorm K Sset u.val ^ (-2 : ℝ)
  have hA : 0 ≤ A := tsum_nonneg (fun u => Real.rpow_nonneg (idealNorm_pos K u.val.ideal.val).le _)
  refine ⟨Cr * (A + 1), Z0, by positivity, hZ0, ?_⟩
  intro Z H hZ hH
  have hZpos : 0 < Z := zero_lt_one.trans_le (hZ0.trans hZ)
  let D : ℝ := Cr * Z ^ (outerBoundaryScalePower 5 5 4) / (1 + H) ^ n
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hrow (u : rows) : ‖actualInitialRowTailIntegral K S mu P psi g ∅ Z H u.val‖ ≤
      D * frequencyRowNorm K Sset u.val ^ (-2 : ℝ) := by
    have hb := hr Z H hZ hH u.val u.property
    norm_num [largeSweepLower, largeSweepUpper, largeSweepRowPower] at hb
    exact hb.trans_eq (by dsimp [D]; ring)
  have hn : Summable (fun u : rows => ‖actualInitialRowTailIntegral K S mu P psi g ∅ Z H u.val‖) :=
    (hsum.mul_left D).of_nonneg_of_le (fun _ => norm_nonneg _) hrow
  refine ⟨hn, ?_⟩
  change ‖∑' u : rows, actualInitialRowTailIntegral K S mu P psi g ∅ Z H u.val‖ ≤ _
  calc
    _ ≤ ∑' u : rows, ‖actualInitialRowTailIntegral K S mu P psi g ∅ Z H u.val‖ :=
      norm_tsum_le_tsum_norm hn
    _ ≤ ∑' u : rows, D * frequencyRowNorm K Sset u.val ^ (-2 : ℝ) :=
      hn.tsum_le_tsum hrow (hsum.mul_left D)
    _ = D * A := tsum_mul_left
    _ ≤ D * (A + 1) := mul_le_mul_of_nonneg_left (by linarith) hD
    _ = _ := by dsimp [D]; ring

include nu in
/-- Every original finite nonprincipal row family has the same initial
tail estimate once its true norm cutoff is supplied. -/
theorem exists_actual_finite_initial_tail_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (g : PrimeWindowGeometry) {B e : ℝ}
    (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (n : ℕ) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ r Z H : ℝ, 0 ≤ r → Z0 ≤ Z → 0 ≤ H →
      ∀ rows : Finset (FrequencyRow K Sset),
      (∀ u ∈ rows, ¬principalFrequencyRow K Sset u) →
      (∀ u ∈ rows, frequencyRowNorm K Sset u ≤ Z ^ r) →
      ‖∑ u ∈ rows, actualInitialRowTailIntegral K S mu P psi g ∅ Z H u‖ ≤
        C * Z ^ (moderateBoundaryScalePower + r * (163 / 50)) / (1 + H) ^ n := by
  obtain ⟨Cr, Z0, hCr, hZ0, hr⟩ := exists_actual_finite_initial_tail_row_bound
    K S mu nu hcomplex P omega psi hpsi hAllowed g hB hB1 he he1 hboundary n
  obtain ⟨Cc, hCc, hcount⟩ := exists_finite_frequencyRow_power_count K Sset
  refine ⟨Cr * Cc, Z0, mul_pos hCr hCc, hZ0, ?_⟩
  intro r Z H hr0 hZ hH rows hnon hcut
  have hZpos : 0 < Z := zero_lt_one.trans_le (hZ0.trans hZ)
  have hU : 1 ≤ Z ^ r := Real.one_le_rpow (hZ0.trans hZ) hr0
  have hmass := hcount (Z ^ r) (113 / 50) hU (by norm_num) rows hcut
  norm_num only [show (113 / 50 : ℝ) + 1 = 163 / 50 by norm_num] at hmass
  have hscale : Z ^ moderateBoundaryScalePower * (Z ^ r) ^ (163 / 50 : ℝ) =
      Z ^ (moderateBoundaryScalePower + r * (163 / 50)) := by
    rw [← Real.rpow_mul hZpos.le, ← Real.rpow_add hZpos]
  calc
    _ ≤ ∑ u ∈ rows, ‖actualInitialRowTailIntegral K S mu P psi g ∅ Z H u‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ rows, Cr * Z ^ moderateBoundaryScalePower *
        frequencyRowNorm K Sset u ^ (113 / 50 : ℝ) / (1 + H) ^ n :=
      Finset.sum_le_sum (fun u hu => hr Z H hZ hH u (hnon u hu))
    _ = (Cr * Z ^ moderateBoundaryScalePower / (1 + H) ^ n) *
        ∑ u ∈ rows, frequencyRowNorm K Sset u ^ (113 / 50 : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ ≤ (Cr * Z ^ moderateBoundaryScalePower / (1 + H) ^ n) *
        (Cc * (Z ^ r) ^ (163 / 50 : ℝ)) := mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (Cr * Cc) * (Z ^ moderateBoundaryScalePower * (Z ^ r) ^ (163 / 50 : ℝ)) /
        (1 + H) ^ n := by ring
    _ = _ := by rw [hscale]

end Expansion.Project

#print axioms Expansion.Project.exists_actual_nonprincipal_initial_tail_bound
#print axioms Expansion.Project.exists_actual_finite_initial_tail_bound
