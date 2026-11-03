import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceMarkedRawBound
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceMarkedActual
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceMarkedUniform
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceCanonicalClosure

/-!
# The original marked inverse moment

This is the literal selected-slot model of the original expansion
recipe.  All original slots are divided by one fixed coefficient cap,
the actual complete source is reindexed and estimated, and that same
cap is restored on every slot.  The original square-root normalization
is an exact identity.  The resulting bound is uniform before the source
index, unit sector, rowwise profile and height are selected.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceMarkedClosure

open NumberField IsDedekindDomain UniqueFactorizationMonoid MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.Moments.UniformAmplify
open HeckeSkeleton.Moments.MOM_BASE.Paired
open HeckeSkeleton.Moments.MOMInvStep HeckeSkeleton.Moments.MOM_INV_STEP AssignedMarkSource
open HeckeSkeleton.LowEnergy.ActualSieveDictionary
open SourceActualArithmetic ProviderNodes ProviderMarkedSlots ProviderMarkedReindex
  ProviderMarkedPacket ProviderMarkedSourceSplit SourceMarkedActual
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

local notation "S" => excludedPlaces K c
local notation "Sset" => places K c
local notation "P" => probeData K c
local notation "D" => HeckeGeneral.ThetaSkeleton.Physical.ProbeData.arithmetic (probeData K c)
local notation "Γ" => sixthPowerSUnitSubgroup K Sset
local notation "Θ" => twists K c
local notation "ψ" => targetCharacter K c
local notation "R" => expansionRecipeRaw K c
local notation "Models" => recipeMomentModels K c R

attribute [local instance] Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar
  Expansion.ActualProbeContext.adeleSpace
  Expansion.ActualProbeContext.adeleBorel
  Expansion.ActualProbeContext.adeleMeasure_isAddHaar

local instance normOneSpace : MeasurableSpace (sLocalNormOneGroup K Sset) :=
  (probeMeasures K c).normOneSpace
local instance normOneBorel : BorelSpace (sLocalNormOneGroup K Sset) :=
  (probeMeasures K c).normOneBorel
local instance principal : IsPrincipalIdealRing (Set.integer Sset K) :=
  (axiomChoice K c).C.principal

def originalGood (p : HeightOneSpectrum (𝓞 K)) : Prop :=
  p ∉ places K c ∧ (6 : 𝓞 K) ∉ p.asIdeal

theorem actual_mask {Z T : ℝ} (i : Index K c Z T) (sector : SixthUnitClasses K Sset)
    (u : NonzeroIdeal K) (I : Ideal (𝓞 K)) :
    maskValue (data K c i sector) u I = ProviderMarkedMask.value (originalGood K c) u.val I := by
  simp only [maskValue, context_mask K c i sector u I,
    ProviderMarkedMask.context_value, originalGood]
  rfl

theorem actual_background_on_mask {Z T : ℝ} (i : Index K c Z T)
    (sector : SixthUnitClasses K Sset) (u n : NonzeroIdeal K)
    (hm : (data K c i sector).commonMask u n.val = true)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p.asIdeal ∣ n.val) :
    UnramifiedAt K (data K c i sector).inverseBackground p := by
  rw [context_mask K c i sector u n.val] at hm
  unfold contextOriginalMask at hm
  split_ifs at hm with h
  exact background_unramified K c i sector p (h.1 p hp).1

/-- Exact restoration of the common coefficient cap on every original
slot, before any common-slot subset is extracted. -/
theorem polynomial_eq_raw {Z T : ℝ} (C : ℝ) (hC : C ≠ 0)
    (i : Index K c Z T) (sector : SixthUnitClasses K Sset) (u : NonzeroIdeal K) :
    inversePolynomial (data K c i sector) u
        (momentBaseFor i ^ (momentWitnessFor i).inverseLength) 0 *
      slotProduct (data K c i sector) u (momentBaseFor i) 0 =
      (ProviderMarkedOriginal.normalization (data K c i sector)
        (momentBaseFor i ^ (momentWitnessFor i).inverseLength) (momentBaseFor i) *
        (C : ℂ) ^ (data K c i sector).geometry.slotCount) *
      rawSource ((data K c i sector).inverseBackground * (data K c i sector).rowCharacter u)
        (ProviderMarkedOriginal.lists (data K c i sector) (momentBaseFor i) 0)
        (normalizedPrimeWeight K c C i sector) (originalGood K c) u.val
        (momentBaseFor i ^ (momentWitnessFor i).inverseLength)
        (ProviderMarkedLogMellin.profile (logProfile K c i u)) := by
  have hB : 0 < momentBaseFor i := (by norm_num : (0 : ℝ) < 2).trans_le
    (recipeMomentBase_ge_two i)
  have hX := Real.rpow_pos_of_pos hB (momentWitnessFor i).inverseLength
  rw [ProviderMarkedOriginal.inverse_marked_eq_complete_source c (data K c i sector) u
    _ _ 0 hX (direction K c i sector) (profile_support_upper K c i sector u)
    (context_mask K c i sector u) (background_unramified K c i sector)
    (fun j p _ => slot_unramified K c i sector j p)]
  conv_rhs => rw [mul_assoc]
  congr 1
  unfold rawSource
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 := (Finset.mem_filter.mp hn).2.ne_zero
  rw [prime_weight_product_eq_scalar K c C hC i sector Finset.univ p]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [profile_eq_log K c i sector u
    (div_pos (ProviderMarkedPools.norm_pos hn0) hX)]
  simp only [actual_mask, choiceWeight]
  ring

/-- The original square-root factor is retained exactly, including
every selected prime slot. -/
theorem normalization_norm_sq {Z T : ℝ} (i : Index K c Z T)
    (sector : SixthUnitClasses K Sset) :
    ‖ProviderMarkedOriginal.normalization (data K c i sector)
      (momentBaseFor i ^ (momentWitnessFor i).inverseLength) (momentBaseFor i)‖ ^ 2 =
      momentBaseFor i ^ (-(momentWitnessFor i).inverseLength - selectedLengthFor i) := by
  have hB : 0 < momentBaseFor i := (by norm_num : (0 : ℝ) < 2).trans_le
    (recipeMomentBase_ge_two i)
  have hnorm (x : ℝ) : ‖(Real.sqrt x : ℂ)⁻¹‖ = (Real.sqrt x)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg x)]
  simp only [ProviderMarkedOriginal.normalization, norm_mul, norm_prod, hnorm]
  rw [ProviderMarkedScale.slot_normalization Finset.univ
    (fun j => ((data K c i sector).geometry.slots j).length) (momentBaseFor i) hB,
    length_sum K c i sector]
  simp_rw [ProviderMarkedScale.inverse_sqrt_rpow _ _ hB]
  rw [← Real.rpow_add hB, ← Real.rpow_mul_natCast hB.le]
  congr 1
  norm_num
  <;> ring

theorem energy_eq_raw {Z T : ℝ} (C : ℝ) (hC : 0 < C)
    (i : Index K c Z T) (sector : SixthUnitClasses K Sset) :
    inverseEnergy (data K c i sector) (inverseParametersFor i) (momentBaseFor i) 0 =
      C ^ (2 * (data K c i sector).geometry.slotCount) *
        (momentBaseFor i ^ (-(momentWitnessFor i).inverseLength - selectedLengthFor i) *
          ∑ u ∈ (data K c i sector).rows (momentBaseFor i ^ rowWidthFor i),
            ‖rawSource ((data K c i sector).inverseBackground *
                (data K c i sector).rowCharacter u)
              (ProviderMarkedOriginal.lists (data K c i sector) (momentBaseFor i) 0)
              (normalizedPrimeWeight K c C i sector) (originalGood K c) u.val
              (momentBaseFor i ^ (momentWitnessFor i).inverseLength)
              (ProviderMarkedLogMellin.profile (logProfile K c i u))‖ ^ 2) := by
  unfold inverseEnergy
  change (∑ u ∈ (data K c i sector).rows (momentBaseFor i ^ rowWidthFor i),
    ‖inversePolynomial (data K c i sector) u
      (momentBaseFor i ^ (momentWitnessFor i).inverseLength) 0 *
      slotProduct (data K c i sector) u (momentBaseFor i) 0‖ ^ 2) = _
  simp_rw [polynomial_eq_raw K c C hC.ne' i sector, norm_mul, mul_pow,
    normalization_norm_sq K c i sector, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hC.le]
  rw [← Finset.mul_sum, ← pow_mul, Nat.mul_comm _ 2]
  ring

/-- A fixed uniform canonical family gives the whole original marked
model, with no added premise about its source energy. -/
theorem marked_bound_of_uniform
    (t : Finset (ℕ × ℕ)) (Cih Zih : ℝ) (hCih : 1 ≤ Cih) (hZih : 2 ≤ Zih)
    (hih : ∀ Z : ℝ, Zih ≤ Z → ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      UniformBound.{0} («Γ» := Γ) («Θ» := Θ) («ψ» := ψ) D (P).Lambda (P).G c.geometry.slots Z 2
        (3 * c.family.lamA / 4) z (1 / 2) 2 (c.family.lamA / 2) 2 Cih t) :
    UniformMomentBoundFor
      (fun _ _ i => markedModelEnergyFor Models i)
      (fun _ _ i => rowWidthFor i)
      (fun _ _ i => inverseCapacityFor i) := by
  obtain ⟨degree, CR, U₀, hCR, hU₀, hraw⟩ :=
    SourceMarkedRawBound.exists_raw_bound K c c.geometry.slots c.family.lamA c.family.lamA
      c.family.lamA_pos c.family.lamA_pos t Cih Zih hCih hZih hih
  obtain ⟨CW, hCW, hweight⟩ := exists_prime_weight_bound K c
  obtain ⟨Ue, hUe, hexterior⟩ := lists_exterior_of_base K c
  let A : ℝ := ((2 * (degree + 2) : ℕ) : ℝ)
  let C : ℝ := CW ^ (2 * c.geometry.slots) * CR
  have hCWp : 0 < CW := zero_lt_one.trans_le hCW
  have hC : 0 ≤ C := mul_nonneg (pow_nonneg hCWp.le _) hCR
  apply SourceMarkedUniform.of_sector_bound K c R A C (max U₀ Ue) c.family.lamA
    (Nat.cast_nonneg _) hC (hU₀.trans (le_max_left _ _)) le_rfl
  intro Z T i sector hZ hT hbase hbin hcap
  let d := data K c i sector
  let B := momentBaseFor i
  let m := rowWidthFor i
  let r := (momentWitnessFor i).inverseLength
  let z := selectedLengthFor i
  have hBraw : U₀ ≤ B := (le_max_left _ _).trans hbase
  have hBe : Ue ≤ B := (le_max_right _ _).trans hbase
  have hBp : 0 < B := (by norm_num : (0 : ℝ) < 2).trans_le (recipeMomentBase_ge_two i)
  let s : Slots K S c.geometry.slots B z := {
    count := d.geometry.slotCount
    lists := ProviderMarkedOriginal.lists d B 0
    weight := normalizedPrimeWeight K c CW i sector
    length := fun j => (d.geometry.slots j).length
    count_le := slot_count K c i sector
    length_nonneg := fun j => (length_pos K c i sector j).le
    length_sum := length_sum K c i sector
    disjoint := fun j k hjk => lists_disjoint K c i sector j k hjk
    exterior := fun j p hp => hexterior i hBe sector j p hp
    window := by
      intro j p hp
      have hb := lists_norm_bounds K c i sector j p hp
      have hhalf : (1 / 2 : ℝ) * B ^ (d.geometry.slots j).length ≤
          B ^ (d.geometry.slots j).length := mul_le_of_le_one_left
        (Real.rpow_nonneg hBp.le (d.geometry.slots j).length) (by norm_num)
      exact ⟨hhalf.trans hb.1.le, hb.2.le⟩
    weight_le := fun j p _ => normalized_prime_weight_norm K c CW hCWp i sector j p
      (hweight i sector j p) }
  have hm := row_width_bounds K c i
  have hz := selected_length_bounds K c i hcap
  have hmargins := capacity_margins K c i hcap
  have hb := hraw d sector (direction K c i sector) (row_character K c i sector)
    (common_mask K c i sector) (allowed_rows K c i sector) (background_admissible K c i sector)
    B T m r z hBraw (zero_le_one.trans hT) hm.1 hm.2 hz.2 hmargins.1 hmargins.2
    s (originalGood K c) (fun u _ => actual_mask K c i sector u)
    (fun u _ n hmask p hp => actual_background_on_mask K c i sector u n hmask p hp)
    (fun _ => B) (fun _ => B ^ r) (realParameter K c i) (imagParameter K c i)
    (fun _ => cutoffParameter K c i) (fun _ _ => hBp)
    (fun _ _ => (Real.rpow_pos_of_pos hBp r).le)
    (fun u _ => (parameter_box K c i u).1) (fun u _ => (parameter_box K c i u).2)
    (by
      intro u hu y hy hne
      change ProviderMarkedLogMellin.profile (logProfile K c i u) y ≠ 0 at hne
      rw [← profile_eq_log K c i sector u hy] at hne
      exact profile_support K c i sector u hne)
  have hheight : ((1 + T) ^ (degree + 2)) ^ 2 = (1 + T) ^ A := by
    rw [show A = ((2 * (degree + 2) : ℕ) : ℝ) from rfl, Real.rpow_natCast, ← pow_mul]
    congr 1
    omega
  calc
    _ = CW ^ (2 * d.geometry.slotCount) *
        (B ^ (-r - z) * ∑ u ∈ d.rows (B ^ m),
          ‖rawSource (d.inverseBackground * d.rowCharacter u) s.lists s.weight
            (originalGood K c) u.val (B ^ r)
            (ProviderMarkedLogMellin.profile (logProfile K c i u))‖ ^ 2) :=
      energy_eq_raw K c CW hCWp i sector
    _ ≤ CW ^ (2 * d.geometry.slotCount) *
        (CR * ((1 + T) ^ (degree + 2)) ^ 2 * B ^ (m + c.family.lamA)) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg hCWp.le _)
    _ ≤ CW ^ (2 * c.geometry.slots) *
        (CR * ((1 + T) ^ (degree + 2)) ^ 2 * B ^ (m + c.family.lamA)) :=
      mul_le_mul_of_nonneg_right (normalization_factor_le K c CW hCW i sector) (by positivity)
    _ = C * B ^ (m + c.family.lamA) * (1 + T) ^ A := by
      rw [hheight]
      dsimp only [C]
      ring

/-- The actual original marked estimate from the two permitted
primitive sieve inputs, through the proved canonical finite induction. -/
theorem actual_marked_bound
    (hquadratic : ExteriorQuadraticBound K Sset D)
    (hcubic : ExteriorCubicBound K Sset D) :
    UniformMomentBoundFor
      (fun _ _ i => markedModelEnergyFor Models i)
      (fun _ _ i => rowWidthFor i)
      (fun _ _ i => inverseCapacityFor i) := by
  have hlambda := c.family.lamA_pos
  obtain ⟨q, C, Z₀, hC, hZ₀, hcanonical⟩ :=
    SourceCanonicalClosure.exists_uniform_canonical_bound.{0} K c hquadratic hcubic
      c.geometry.slots 2 2 (3 * c.family.lamA / 4) 1 (1 / 2) 2 (c.family.lamA / 2)
      (by positivity) (by norm_num) (by norm_num) (by norm_num)
      (half_pos c.family.lamA_pos)
  exact marked_bound_of_uniform K c q C Z₀ hC hZ₀ hcanonical

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceMarkedClosure

end
