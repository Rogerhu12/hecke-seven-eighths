import Expansion.ActualPrimeFrequencySlotBridge
import Expansion.PrimeFrequencyPowerBudget

/-!
# A genuine power bound for the original masked physical prime polynomial

The finite-height logarithmic-derivative argument, divided-window identity,
prime-power tail, full original mask and imaginary profile phase are all
instantiated. The order and constants are chosen before every frequency,
row, zero boundary and outer scale. No physical-kernel calibration or
prime cancellation bound is a hypothesis.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Bridge HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckeGeneral.Analysis.ExpansionRecipe HeckeGeneral.Analysis.ConditionalMoments
open HeckeSkeleton.HeckeBufferedReciprocal ExpansionInterfaces.Mellin
open Expansion.NormalizedContourBudget Expansion.PrimeFrequencyPowerBudget
open ExpansionDetector.Hecke
open scoped Classical BigOperators ContDiff

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem exists_actual_normalized_prime_power_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (arch : InfinitePlace K → ℝ) (weight : InfinitePlace K → ℤ)
    (R : ℝ) (hR : 0 ≤ R) (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W ⊆ Icc (1 : ℝ) 2)
    (ℓ δ ε η τ L : ℝ) (hℓ : 0 ≤ ℓ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4)
    (hε : 0 < ε) (hloss : ε + δ * ℓ ≤ η)
    (hτ : 0 < τ) (hτ' : τ ≤ 1) (hL : 0 ≤ L) :
    ∃ P₀ Cslot : ℝ, 2 ≤ P₀ ∧ 0 ≤ Cslot ∧
      ∀ (χ : HeckeCharacter K) (u : NonzeroIdeal K) (Z β ν Hupper : ℝ)
        (pool : Finset (HeightOneSpectrum (𝓞 K))),
        1 ≤ Z → P₀ ≤ Z ^ ℓ → idealNorm K u ≤ 2 * Z →
        (∀ v : ℝ, χ ≠ heckeNormTwist K v) →
        (fun v => heckeRadialParameter K v χ) = arch →
        heckeArchWeight K χ = weight → heckeConductorScale K χ ≤ R * Z →
        1 / 2 ≤ β → β ≤ 1 → |ν| ≤ L * Z ^ τ →
        |ν| + Z ^ τ + 3 / 2 ≤ Hupper → ZeroUpperBound K χ Hupper β →
        (∀ p, W (actualPrimeNorm K p / Z ^ ℓ) ≠ 0 → p ∈ pool) →
        ‖(Real.sqrt (Z ^ ℓ) : ℂ)⁻¹ * actualOriginalMaskedPrimeSum K S χ u
          (fun y => W y * profilePower (-vertical 0 ν) y) (Z ^ ℓ) pool‖ ≤
          Cslot * Z ^ ((β - 1 / 2) * ℓ + η) := by
  obtain ⟨order, horder⟩ := exists_prime_contour_order (ℓ := ℓ) hτ
  obtain ⟨C, A, P₀, CW, B, M, hC, hA, hP₀, hCW, hB, hM, hb⟩ :=
    exists_actual_finite_height_masked_frequency_bound K S hcomplex arch weight R hR W hW hs order
  let degree := heightDegree K
  let Dder := logDerivativeConstant degree C A L δ ε
  let Dfix : ℝ := (Ideal.absNorm (fixedDeletedIdeal K S) : ℝ)
  let Ccont := contourPowerConstant Dder (actualPrimeLogMass K 2) CW
  let Cdel := deletionPowerConstant Dfix M ε
  have hdegree : 0 ≤ degree := by dsimp [degree, heightDegree]; positivity
  have hDder : 0 ≤ Dder :=
    logDerivativeConstant_nonneg hdegree hC (zero_le_one.trans hA) hL hε
  have hDfix : 1 ≤ Dfix := by
    have hn : 0 < Ideal.absNorm (fixedDeletedIdeal K S) := Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (fixedDeletedIdeal_ne_zero K S))
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
  have hCcont : 0 ≤ Ccont :=
    contourPowerConstant_nonneg hDder (actualPrimeLogMass_nonneg K 2) hCW
  have hCdel : 0 ≤ Cdel := deletionPowerConstant_nonneg hDfix hM.le hε
  refine ⟨P₀, Ccont + B + Cdel, hP₀, by positivity, ?_⟩
  intro χ u Z β ν Hupper pool hZ hP hu hχ harch hweight hQ hβ hβ'
    hν hpadding hupper hcover
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hPpos : 0 < Z ^ ℓ := Real.rpow_pos_of_pos hZpos _
  have hPone : 1 ≤ Z ^ ℓ := Real.one_le_rpow hZ hℓ
  have hsqrtpos : 0 < Real.sqrt (Z ^ ℓ) := Real.sqrt_pos.mpr hPpos
  have hsqrtone : 1 ≤ Real.sqrt (Z ^ ℓ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hPone
  have hinv : (Real.sqrt (Z ^ ℓ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsqrtone
  have hinv0 : 0 ≤ (Real.sqrt (Z ^ ℓ))⁻¹ := inv_nonneg.mpr hsqrtpos.le
  let Dnow := actualPrimeLogRectangleBound K C A Z δ ν (Z ^ τ)
  have hDnow : 0 ≤ Dnow := by
    have hlogC := Real.log_nonneg hC
    have hlogZ := Real.log_nonneg hZ
    have hlogH := Real.log_nonneg
      (by linarith [abs_nonneg ν, Real.rpow_pos_of_pos hZpos τ] : 1 ≤ 4 + |ν| + Z ^ τ)
    dsimp [Dnow, actualPrimeLogRectangleBound]
    change 0 ≤ 48 * (1 + Real.log C + 5 / 8 * Real.log Z +
      degree * Real.log (4 + |ν| + Z ^ τ) + A) / δ ^ 2
    positivity
  have hDnowBound : Dnow ≤ Dder * Z ^ ε :=
    logDerivative_le_power hdegree hC (zero_le_one.trans hA) hL hε
      hZ hZ le_rfl hτ.le hτ' hν
  have hcont : (Real.sqrt (Z ^ ℓ))⁻¹ *
      actualPrimeFrequencyEnvelope K C A CW order Z β δ ν (Z ^ τ) (Z ^ ℓ) ≤
      Ccont * Z ^ ((β - 1 / 2) * ℓ + η) := by
    have hh := normalized_contour_le_power (Z := Z) (ℓ := ℓ) (β := β) (δ := δ)
      (ε := ε) (η := η) (τ := τ) (M := Dnow) (D := Dder)
      (mass := actualPrimeLogMass K 2) (CW := CW) (order := order)
      hZ hℓ hβ hβ' hδ.le hδ' hε.le hloss horder hDnow hDder
      (actualPrimeLogMass_nonneg K 2) hCW hDnowBound
    simpa only [actualPrimeFrequencyEnvelope, contourMajorant, sub_zero, Dnow, Ccont] using hh
  have heη : ε ≤ η :=
    (le_add_of_nonneg_right (mul_nonneg hδ.le hℓ)).trans hloss
  have htarget : ε ≤ (β - 1 / 2) * ℓ + η :=
    heη.trans (le_add_of_nonneg_left (mul_nonneg (sub_nonneg.mpr hβ) hℓ))
  have hpow : Z ^ ε ≤ Z ^ ((β - 1 / 2) * ℓ + η) :=
    Real.rpow_le_rpow_of_exponent_le hZ htarget
  have hpowone : 1 ≤ Z ^ ((β - 1 / 2) * ℓ + η) :=
    (Real.one_le_rpow hZ hε.le).trans hpow
  have hdel : (Real.sqrt (Z ^ ℓ))⁻¹ *
      ((Real.log (Dfix * idealNorm K u) / Real.log 2) * M) ≤
      Cdel * Z ^ ((β - 1 / 2) * ℓ + η) := by
    have hd := deletion_log_le_power hZ hDfix (idealNorm_pos K u) hu hM.le hε
    calc
      _ ≤ (Real.sqrt (Z ^ ℓ))⁻¹ * (Cdel * Z ^ ε) :=
        mul_le_mul_of_nonneg_left hd hinv0
      _ ≤ 1 * (Cdel * Z ^ ε) := mul_le_mul_of_nonneg_right hinv (by positivity)
      _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_left hpow hCdel
  have htail : B ≤ B * Z ^ ((β - 1 / 2) * ℓ + η) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpowone hB.le
  have hraw := hb χ u Z β δ ν (Z ^ τ) (Z ^ ℓ) Hupper pool hχ harch hweight hZ hQ
    hβ hβ' hδ hδ' (Real.rpow_pos_of_pos hZpos τ) hP hpadding hupper hcover
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (mul_le_mul_of_nonneg_left hraw hinv0).trans
  change (Real.sqrt (Z ^ ℓ))⁻¹ *
    (actualPrimeFrequencyEnvelope K C A CW order Z β δ ν (Z ^ τ) (Z ^ ℓ) +
      B * Real.sqrt (Z ^ ℓ) + (Real.log (Dfix * idealNorm K u) / Real.log 2) * M) ≤ _
  calc
    _ = (Real.sqrt (Z ^ ℓ))⁻¹ *
          actualPrimeFrequencyEnvelope K C A CW order Z β δ ν (Z ^ τ) (Z ^ ℓ) +
        B + (Real.sqrt (Z ^ ℓ))⁻¹ * ((Real.log (Dfix * idealNorm K u) / Real.log 2) * M) := by
      rw [mul_add, mul_add]
      congr 2
      calc
        _ = B * ((Real.sqrt (Z ^ ℓ))⁻¹ * Real.sqrt (Z ^ ℓ)) := by ring
        _ = B := by rw [inv_mul_cancel₀ hsqrtpos.ne', mul_one]
    _ ≤ Ccont * Z ^ ((β - 1 / 2) * ℓ + η) +
        B * Z ^ ((β - 1 / 2) * ℓ + η) + Cdel * Z ^ ((β - 1 / 2) * ℓ + η) :=
      add_le_add (add_le_add hcont htail) hdel
    _ = _ := by ring

end Expansion.Project

#print axioms Expansion.Project.exists_actual_normalized_prime_power_bound
