import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceActualArithmetic
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedOriginal
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedLogMellin
import HeckeSkeleton.ExpansionModels.ActualRowEligibility
import HeckeGeneral.Analysis.MomentPrimeWindowUnramified

/-!
# Arithmetic and profile data of the original marked source

Every object below is a projection of the same actual source recipe.
Changing to the shell base and selecting slots preserves the complete
rows, their character and common mask, and the original inverse profile.
The prime coefficients have a fixed bound before the scale, height,
source index or row is chosen.  All analytic windows eventually avoid
the original excluded places; no new places or energy premises occur.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceMarkedActual

open NumberField IsDedekindDomain Set Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.Moments.UniformAmplify
open HeckeSkeleton.Moments.MOM_BASE.Paired
open HeckeSkeleton.Moments.MOM_INV_STEP
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

abbrev Index (Z T : ℝ) := SourceMomentIndexFor K c
  (recipeMomentSourceData K c (expansionRecipeRaw K c)) Z T

abbrev data {Z T : ℝ} (i : Index K c Z T)
    (sector : SixthUnitClasses K (places K c)) :=
  inverseModelFor (recipeMomentModels K c (expansionRecipeRaw K c)) i sector

variable {Z T : ℝ}

theorem direction (i : Index K c Z T) (sector : SixthUnitClasses K (places K c)) :
    (data K c i sector).direction = 1 := rfl

theorem theta (i : Index K c Z T) (sector : SixthUnitClasses K (places K c)) :
    (data K c i sector).theta =
      Expansion.Project.canonicalDetectorTheta K (targetCharacter K c) := rfl

theorem row_character (i : Index K c Z T) (sector : SixthUnitClasses K (places K c)) :
    (data K c i sector).rowCharacter = completeIdealRowCharacter K (places K c)
      (probeData K c) (momentRowCharacters K c) sector := rfl

theorem common_mask (i : Index K c Z T) (sector : SixthUnitClasses K (places K c)) :
    (data K c i sector).commonMask = completeIdealCommonMask K (places K c) := rfl

theorem allowed_rows (i : Index K c Z T) (sector : SixthUnitClasses K (places K c)) :
    (data K c i sector).allowedRow = completeIdealIsExterior K (places K c) := rfl

theorem context_mask (i : Index K c Z T) (sector : SixthUnitClasses K (places K c))
    (u : NonzeroIdeal K) (I : Ideal (𝓞 K)) :
    (data K c i sector).commonMask u I = contextOriginalMask K c u I := by
  rw [common_mask]
  unfold completeIdealCommonMask contextOriginalMask
  split_ifs <;> simp_all

theorem background_admissible (i : Index K c Z T)
    (sector : SixthUnitClasses K (places K c)) :
    BackgroundCycle.Admissible K (SourceActualArithmetic.twists K c)
      (targetCharacter K c) (data K c i sector).inverseBackground⁻¹ := by
  have h := TerminalBackgrounds.directed_background_admissible K c.family.omega
    (targetCharacter K c) (data K c i sector) (probeData K c).G
  rw [direction, zpow_neg_one, theta] at h
  exact h

theorem background_unramified (i : Index K c Z T)
    (sector : SixthUnitClasses K (places K c))
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ places K c) :
    UnramifiedAt K (data K c i sector).inverseBackground p := by
  have h := SourceActualArithmetic.admissible_unramified K c _
    (background_admissible K c i sector) p hp
  simpa only [inv_inv] using h.inv K

theorem slot_coefficient (i : Index K c Z T)
    (sector : SixthUnitClasses K (places K c))
    (j : Fin (data K c i sector).geometry.slotCount) :
    (data K c i sector).slotCoefficient j = 1 := rfl

theorem slot_unramified (i : Index K c Z T)
    (sector : SixthUnitClasses K (places K c))
    (j : Fin (data K c i sector).geometry.slotCount) (p : HeightOneSpectrum (𝓞 K)) :
    UnramifiedAt K ((data K c i sector).slotCoefficient j) p := by
  rw [slot_coefficient]
  exact unramifiedAt_one K p

def realParameter (i : Index K c Z T) (u : NonzeroIdeal K) : ℝ :=
  -((recipeMomentModels K c (expansionRecipeRaw K c)).realShifts Z T i u 0)

def imagParameter (i : Index K c Z T) (u : NonzeroIdeal K) : ℝ :=
  (expansionRecipeRaw K c).family.frequencyScale *
    (recipeMomentModels K c (expansionRecipeRaw K c)).imagShifts Z T i u 0

def cutoffParameter (i : Index K c Z T) : ℝ :=
  (recipeMomentModels K c (expansionRecipeRaw K c)).heights Z T i 3

def logProfile (i : Index K c Z T) (u : NonzeroIdeal K) : SchwartzMap ℝ ℂ :=
  actualInverseLogProfile (momentBaseFor i)
    (momentBaseFor i ^ (momentWitnessFor i).inverseLength)
    (realParameter K c i u) (imagParameter K c i u) (cutoffParameter K c i)

theorem profile_eq_scalar (i : Index K c Z T)
    (sector : SixthUnitClasses K (places K c)) (u : NonzeroIdeal K) :
    (data K c i sector).inverseTest.profile u 0 =
      actualInverseScalarProfile K c u (momentBaseFor i)
        (momentBaseFor i ^ (momentWitnessFor i).inverseLength)
        (realParameter K c i u) (imagParameter K c i u) (cutoffParameter K c i) := by
  exact actual_unmarked_inverse_profile K c (momentBaseFor i)
    (momentBaseFor i ^ (momentWitnessFor i).inverseLength) sector
    ((recipeMomentModels K c (expansionRecipeRaw K c)).heights Z T i)
    ((recipeMomentModels K c (expansionRecipeRaw K c)).realShifts Z T i)
    ((recipeMomentModels K c (expansionRecipeRaw K c)).imagShifts Z T i) u

/-- The original positive norm argument is unchanged by logarithmic
Fourier separation.  In particular no sixth-power row pullback occurs. -/
theorem profile_eq_log (i : Index K c Z T)
    (sector : SixthUnitClasses K (places K c)) (u : NonzeroIdeal K)
    {y : ℝ} (hy : 0 < y) :
    (data K c i sector).inverseTest.profile u 0 y =
      ProviderMarkedLogMellin.profile (logProfile K c i u) y := by
  rw [profile_eq_scalar]
  have hB : 0 < momentBaseFor i := (by norm_num : (0 : ℝ) < 2).trans_le
    (recipeMomentBase_ge_two i)
  change _ = actualInverseLogProfile (momentBaseFor i)
    (momentBaseFor i ^ (momentWitnessFor i).inverseLength)
    (realParameter K c i u) (imagParameter K c i u)
    (cutoffParameter K c i) (Real.log y)
  rw [actualInverseLogProfile_apply K c u _ _ _ _ _ hB
    (Real.rpow_pos_of_pos hB _).le, Real.exp_log hy]

theorem profile_support (i : Index K c Z T)
    (sector : SixthUnitClasses K (places K c)) (u : NonzeroIdeal K) :
    Function.support ((data K c i sector).inverseTest.profile u 0) ⊆
      Set.Icc (1 / 2 : ℝ) 2 := by
  intro y hy
  rw [profile_eq_scalar] at hy
  change Expansion.Dyadic.annularProfile y * _ * _ ≠ 0 at hy
  exact Expansion.Dyadic.annularProfile_support
    (left_ne_zero_of_mul (left_ne_zero_of_mul hy))

theorem profile_support_upper (i : Index K c Z T)
    (sector : SixthUnitClasses K (places K c)) (u : NonzeroIdeal K) :
    Function.support ((data K c i sector).inverseTest.profile u 0) ⊆ Set.Iic 2 :=
  fun _ hy => (profile_support K c i sector u hy).2

theorem parameter_box (i : Index K c Z T) (u : NonzeroIdeal K) :
    |realParameter K c i u| ≤ 8 ∧
      |imagParameter K c i u| ≤
        |(expansionRecipeRaw K c).family.frequencyScale| * (1 + T) := by
  obtain ⟨hξ, hσ, hτ⟩ := (actualRecipeSourceGeometry K c).2 Z T i
  constructor
  · simpa only [realParameter, abs_neg, ← Real.norm_eq_abs] using
      (norm_le_pi_norm ((recipeMomentModels K c (expansionRecipeRaw K c)).realShifts
        Z T i u) 0).trans (hσ u)
  · rw [imagParameter, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have hu := (norm_le_pi_norm
      ((recipeMomentModels K c (expansionRecipeRaw K c)).imagShifts Z T i u) 0).trans
        (hτ u)
    rw [Real.norm_eq_abs] at hu
    exact hu.trans (add_le_add le_rfl hξ)

theorem slot_count (i : Index K c Z T) (sector : SixthUnitClasses K (places K c)) :
    (data K c i sector).geometry.slotCount ≤ c.geometry.slots := by
  change i.selected.card ≤ c.geometry.slots
  simpa only [Fintype.card_fin] using Finset.card_le_univ i.selected

theorem length_sum (i : Index K c Z T) (sector : SixthUnitClasses K (places K c)) :
    (∑ j, ((data K c i sector).geometry.slots j).length) = selectedLengthFor i :=
  (actualRecipeMoment_geometry K c i sector).1

theorem length_pos (i : Index K c Z T) (sector : SixthUnitClasses K (places K c))
    (j : Fin (data K c i sector).geometry.slotCount) :
    0 < ((data K c i sector).geometry.slots j).length :=
  ((data K c i sector).geometry.slots j).length_pos

theorem slot_length (i : Index K c Z T) (sector : SixthUnitClasses K (places K c))
    (j : Fin (data K c i sector).geometry.slotCount) :
    ((data K c i sector).geometry.slots j).length =
      ((1 / 6 : ℝ) / c.geometry.slots) / (momentBlockFor i).shell := rfl

theorem slot_profile (i : Index K c Z T) (sector : SixthUnitClasses K (places K c))
    (j : Fin (data K c i sector).geometry.slotCount) (t y : ℝ) :
    ((data K c i sector).geometry.slots j).profile t y =
      (c.geometry.weight (selectedSlotIndex i.selected j)).toFun y *
        profilePower (conj ((17 / 50 : ℂ) +
          (((recipeMomentModels K c (expansionRecipeRaw K c)).heights Z T i 2 : ℝ) : ℂ) *
            Complex.I) - 1) y := rfl

theorem slot_scale (i : Index K c Z T) (sector : SixthUnitClasses K (places K c))
    (j : Fin (data K c i sector).geometry.slotCount) :
    momentBaseFor i ^ ((data K c i sector).geometry.slots j).length =
      primeScale c.geometry Z := by
  have hZ : 0 < Z := (by norm_num : (0 : ℝ) < 2 ^ (16 : ℕ)).trans_le
    (recipeMoment_scale_of_index i).1
  exact rpow_changeBaseSlot (recipeMoment_shell_pos i) hZ
    ((1 / 6 : ℝ) / c.geometry.slots)

theorem lists_eq (i : Index K c Z T) (sector : SixthUnitClasses K (places K c))
    (j : Fin (data K c i sector).geometry.slotCount) :
    ProviderMarkedOriginal.lists (data K c i sector) (momentBaseFor i) 0 j =
      analyticPrimeSupport K (c.geometry.weight (selectedSlotIndex i.selected j)).toFun
        (primeScale c.geometry Z) := by
  change analyticPrimeSupport K
      (c.geometry.weight (selectedSlotIndex i.selected j)).toFun
      (momentBaseFor i ^ ((data K c i sector).geometry.slots j).length) = _
  exact congrArg (analyticPrimeSupport K
    (c.geometry.weight (selectedSlotIndex i.selected j)).toFun) (slot_scale K c i sector j)

theorem lists_norm_bounds (i : Index K c Z T)
    (sector : SixthUnitClasses K (places K c))
    (j : Fin (data K c i sector).geometry.slotCount) (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∈ ProviderMarkedOriginal.lists (data K c i sector) (momentBaseFor i) 0 j) :
    momentBaseFor i ^ ((data K c i sector).geometry.slots j).length <
        (p.asIdeal.absNorm : ℝ) ∧
      (p.asIdeal.absNorm : ℝ) <
        2 * momentBaseFor i ^ ((data K c i sector).geometry.slots j).length := by
  have hP : 0 < momentBaseFor i ^ ((data K c i sector).geometry.slots j).length :=
    Real.rpow_pos_of_pos ((by norm_num : (0 : ℝ) < 2).trans_le
      (recipeMomentBase_ge_two i)) _
  have hprof := (((data K c i sector).geometry.slots j).support_spec 0 _ p).mp hp
  rw [slot_profile] at hprof
  have hy := c.geometry.support_annular (selectedSlotIndex i.selected j)
    (left_ne_zero_of_mul hprof)
  exact ⟨by simpa only [one_mul] using (lt_div_iff₀ hP).mp hy.1,
    (div_lt_iff₀ hP).mp hy.2⟩

theorem lists_disjoint (i : Index K c Z T)
    (sector : SixthUnitClasses K (places K c))
    (j k : Fin (data K c i sector).geometry.slotCount) (hjk : j ≠ k) :
    Disjoint (ProviderMarkedOriginal.lists (data K c i sector) (momentBaseFor i) 0 j)
      (ProviderMarkedOriginal.lists (data K c i sector) (momentBaseFor i) 0 k) := by
  have hidx : selectedSlotIndex i.selected j ≠ selectedSlotIndex i.selected k := by
    intro heq
    apply hjk
    apply i.selected.equivFin.symm.injective
    exact Subtype.ext heq
  rw [lists_eq, lists_eq]
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact Set.disjoint_left.mp (c.geometry.disjoint _ _ hidx)
    ((analyticPrimeSupport_spec K _ (c.geometry.support_annular _) _ p).mp hp)
    ((analyticPrimeSupport_spec K _ (c.geometry.support_annular _) _ p).mp hq)

/-- The threshold is in the original external scale, before every
source selection.  The shell change leaves each actual prime scale exact. -/
theorem exists_lists_exterior :
    ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ {Z T : ℝ}, Z₀ ≤ Z → ∀ i : Index K c Z T,
      ∀ (sector : SixthUnitClasses K (places K c))
        (j : Fin (data K c i sector).geometry.slotCount)
        (p : HeightOneSpectrum (𝓞 K)),
      p ∈ ProviderMarkedOriginal.lists (data K c i sector) (momentBaseFor i) 0 j →
        p ∉ places K c := by
  let N : ℕ := (excludedPlaces K c).sup (fun p => p.asIdeal.absNorm)
  have he : 0 < (1 / 6 : ℝ) / c.geometry.slots :=
    div_pos (by norm_num) (by exact_mod_cast c.geometry.slots_pos)
  obtain ⟨Zh, hZh⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop he).eventually (eventually_ge_atTop (N : ℝ)))
  refine ⟨max 2 Zh, le_max_left _ _, ?_⟩
  intro Z T hZ i sector j p hp hpS
  have hN : (N : ℝ) ≤ primeScale c.geometry Z :=
    hZh Z ((le_max_right _ _).trans hZ)
  have hnorm : (p.asIdeal.absNorm : ℝ) ≤ N := by
    exact_mod_cast (Finset.le_sup (f := fun p : HeightOneSpectrum (𝓞 K) =>
      p.asIdeal.absNorm) hpS : p.asIdeal.absNorm ≤ N)
  have hlower := (lists_norm_bounds K c i sector j p hp).1
  rw [slot_scale] at hlower
  exact (not_lt_of_ge (hnorm.trans hN)) hlower

theorem shell_le_one (i : Index K c Z T) : (momentBlockFor i).shell ≤ 1 := by
  have hs := ((expansionRecipeRaw K c).shell_range Z T i.block).2
  change (momentBlockFor i).shell < 13 / 16 + expansionShellAllowance K c at hs
  have ha : expansionShellAllowance K c < 1 / 48 :=
    (ExpansionInterfaces.shellAllowance_spec c.family.lamA_pos).2.1
  linarith

theorem base_le_outer (i : Index K c Z T) : momentBaseFor i ≤ Z := by
  have hZ1 : 1 ≤ Z := (by norm_num : (1 : ℝ) ≤ 2 ^ (16 : ℕ)).trans
    (recipeMoment_scale_of_index i).1
  calc
    momentBaseFor i ≤ Z ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hZ1 (shell_le_one K c i)
    _ = Z := Real.rpow_one Z

/-- The same exterior cutoff can be required of the internal base.
The actual shell is at most one, so this implies the external cutoff. -/
theorem lists_exterior_of_base :
    ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ {Z T : ℝ} (i : Index K c Z T), U₀ ≤ momentBaseFor i →
      ∀ (sector : SixthUnitClasses K (places K c))
        (j : Fin (data K c i sector).geometry.slotCount)
        (p : HeightOneSpectrum (𝓞 K)),
      p ∈ ProviderMarkedOriginal.lists (data K c i sector) (momentBaseFor i) 0 j →
        p ∉ places K c := by
  obtain ⟨U₀, hU₀, hb⟩ := exists_lists_exterior K c
  refine ⟨U₀, hU₀, ?_⟩
  intro Z T i hi sector j p hp
  exact hb (hi.trans (base_le_outer K c i)) i sector j p hp

private theorem fixed_prime_power_norm_le_one (t y : ℝ) (hy : 1 ≤ y) :
    ‖profilePower (conj ((17 / 50 : ℂ) + (t : ℂ) * Complex.I) - 1) y‖ ≤ 1 := by
  have hre : (conj ((17 / 50 : ℂ) + (t : ℂ) * Complex.I) - 1).re =
      -(33 / 50 : ℝ) := by norm_num [Complex.conj_ofNat]
  rw [profilePower, Complex.norm_exp, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hre]
  exact Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonneg_of_nonpos (Real.log_nonneg hy) (by norm_num))

/-- A single finite maximum of the original smooth windows controls
all frozen physical powers.  The bound is independent of height. -/
theorem exists_slot_profile_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Z T : ℝ} (i : Index K c Z T)
      (sector : SixthUnitClasses K (places K c))
      (j : Fin (data K c i sector).geometry.slotCount) (t y : ℝ),
      ‖((data K c i sector).geometry.slots j).profile t y‖ ≤ C := by
  have hbounds (j : Fin c.geometry.slots) :
      ∃ C : ℝ, ∀ y ∈ Set.Icc (1 : ℝ) 2, ‖(c.geometry.weight j).toFun y‖ ≤ C :=
    isCompact_Icc.exists_bound_of_continuousOn (c.geometry.weight j).smooth.continuous.continuousOn
  choose B hB using hbounds
  let C : ℝ := 1 + ∑ j : Fin c.geometry.slots, max 0 (B j)
  have hsum : 0 ≤ ∑ j : Fin c.geometry.slots, max 0 (B j) :=
    Finset.sum_nonneg (fun j _ => le_max_left _ _)
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hBC (j : Fin c.geometry.slots) : B j ≤ C := by
    have hj : max 0 (B j) ≤ ∑ k : Fin c.geometry.slots, max 0 (B k) :=
      Finset.single_le_sum (fun k _ => le_max_left _ _) (Finset.mem_univ j)
    exact (le_max_right 0 (B j)).trans (hj.trans (by dsimp [C]; linarith))
  refine ⟨C, hC, ?_⟩
  intro Z T i sector j t y
  rw [slot_profile]
  by_cases hw : (c.geometry.weight (selectedSlotIndex i.selected j)).toFun y = 0
  · rw [hw, zero_mul, norm_zero]
    exact zero_le_one.trans hC
  · have hy := c.geometry.support_annular (selectedSlotIndex i.selected j) hw
    rw [norm_mul]
    calc
      _ ≤ ‖(c.geometry.weight (selectedSlotIndex i.selected j)).toFun y‖ * 1 :=
        mul_le_mul_of_nonneg_left (fixed_prime_power_norm_le_one _ _ hy.1.le) (norm_nonneg _)
      _ ≤ C := by
        rw [mul_one]
        exact (hB _ y ⟨hy.1.le, hy.2.le⟩).trans (hBC _)

theorem relative_coefficient_norm (i : Index K c Z T)
    (sector : SixthUnitClasses K (places K c))
    (j : Fin (data K c i sector).geometry.slotCount) (p : HeightOneSpectrum (𝓞 K)) :
    ‖inverseRelativeSlotCoefficient (data K c i sector) j p‖ ≤ 1 := by
  by_cases hν : UnramifiedAt K (data K c i sector).inverseBackground p
  · exact inverseRelativeSlotCoefficient_norm_le_one _ _ _ hν
  · rw [inverseRelativeSlotCoefficient,
      primeCoefficient_of_ramified K _ p hν, inv_zero, zero_mul, norm_zero]
    norm_num

theorem exists_prime_weight_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Z T : ℝ} (i : Index K c Z T)
      (sector : SixthUnitClasses K (places K c))
      (j : Fin (data K c i sector).geometry.slotCount) (p : HeightOneSpectrum (𝓞 K)),
      ‖ProviderMarkedOriginal.primeWeight (data K c i sector) (momentBaseFor i) 0
        j p.asIdeal‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_slot_profile_bound K c
  refine ⟨C, hC, ?_⟩
  intro Z T i sector j p
  rw [ProviderMarkedOriginal.primeWeight_asIdeal, norm_mul]
  exact (mul_le_mul (relative_coefficient_norm K c i sector j p)
    (hb i sector j 0 _) (norm_nonneg _) (by linarith)).trans_eq (one_mul C)

/-- The same scalar divides every original slot, including the slots
subsequently selected in the common prime product. -/
def normalizedPrimeWeight (C : ℝ) (i : Index K c Z T)
    (sector : SixthUnitClasses K (places K c))
    (j : Fin (data K c i sector).geometry.slotCount) (I : Ideal (𝓞 K)) : ℂ :=
  (C : ℂ)⁻¹ * ProviderMarkedOriginal.primeWeight (data K c i sector)
    (momentBaseFor i) 0 j I

theorem normalized_prime_weight_norm (C : ℝ) (hC : 0 < C)
    (i : Index K c Z T) (sector : SixthUnitClasses K (places K c))
    (j : Fin (data K c i sector).geometry.slotCount) (p : HeightOneSpectrum (𝓞 K))
    (hw : ‖ProviderMarkedOriginal.primeWeight (data K c i sector)
      (momentBaseFor i) 0 j p.asIdeal‖ ≤ C) :
    ‖normalizedPrimeWeight K c C i sector j p.asIdeal‖ ≤ 1 := by
  rw [normalizedPrimeWeight, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg hC.le]
  exact (mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr hC.le)).trans_eq
    (inv_mul_cancel₀ hC.ne')

theorem prime_weight_eq_scalar (C : ℝ) (hC : C ≠ 0)
    (i : Index K c Z T) (sector : SixthUnitClasses K (places K c))
    (j : Fin (data K c i sector).geometry.slotCount) (I : Ideal (𝓞 K)) :
    ProviderMarkedOriginal.primeWeight (data K c i sector) (momentBaseFor i) 0 j I =
      (C : ℂ) * normalizedPrimeWeight K c C i sector j I := by
  rw [normalizedPrimeWeight, ← mul_assoc,
    mul_inv_cancel₀ (by exact_mod_cast hC : (C : ℂ) ≠ 0), one_mul]

theorem prime_weight_product_eq_scalar (C : ℝ) (hC : C ≠ 0)
    (i : Index K c Z T) (sector : SixthUnitClasses K (places K c))
    (J : Finset (Fin (data K c i sector).geometry.slotCount))
    (p : Fin (data K c i sector).geometry.slotCount → HeightOneSpectrum (𝓞 K)) :
    (∏ j ∈ J, ProviderMarkedOriginal.primeWeight (data K c i sector)
      (momentBaseFor i) 0 j (p j).asIdeal) =
      (C : ℂ) ^ J.card * ∏ j ∈ J, normalizedPrimeWeight K c C i sector j (p j).asIdeal := by
  calc
    _ = ∏ j ∈ J, (C : ℂ) * normalizedPrimeWeight K c C i sector j (p j).asIdeal :=
      Finset.prod_congr rfl (fun j _ => prime_weight_eq_scalar K c C hC i sector j _)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]

theorem prime_weight_product_norm_sq (C : ℝ) (hC : 0 < C)
    (i : Index K c Z T) (sector : SixthUnitClasses K (places K c))
    (J : Finset (Fin (data K c i sector).geometry.slotCount))
    (p : Fin (data K c i sector).geometry.slotCount → HeightOneSpectrum (𝓞 K)) :
    ‖∏ j ∈ J, ProviderMarkedOriginal.primeWeight (data K c i sector)
      (momentBaseFor i) 0 j (p j).asIdeal‖ ^ 2 =
      C ^ (2 * J.card) * ‖∏ j ∈ J,
        normalizedPrimeWeight K c C i sector j (p j).asIdeal‖ ^ 2 := by
  rw [prime_weight_product_eq_scalar K c C hC.ne', norm_mul, mul_pow, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg hC.le, ← pow_mul, Nat.mul_comm J.card 2]

theorem normalization_factor_le (C : ℝ) (hC : 1 ≤ C)
    (i : Index K c Z T) (sector : SixthUnitClasses K (places K c)) :
    C ^ (2 * (data K c i sector).geometry.slotCount) ≤ C ^ (2 * c.geometry.slots) :=
  pow_le_pow_right₀ hC (Nat.mul_le_mul_left 2 (slot_count K c i sector))

theorem inverse_length_nonneg (i : Index K c Z T) :
    0 ≤ (momentWitnessFor i).inverseLength := ((actualRecipeSourceGeometry K c).1 Z T i).1

theorem row_width_bounds (i : Index K c Z T) : 0 ≤ rowWidthFor i ∧ rowWidthFor i ≤ 2 :=
  ⟨zero_le_one.trans (recipeMoment_rowWidth_spec i).1.le, (recipeMoment_rowWidth_spec i).2.1⟩

theorem selected_length_bounds (i : Index K c Z T) (hcap : inverseCapacityFor i) :
    0 ≤ selectedLengthFor i ∧ selectedLengthFor i ≤ 1 := by
  have hr := inverse_length_nonneg K c i
  have hc := hcap.1
  have hlambda := c.family.lamA_pos
  exact ⟨actualRecipeMoment_selectedLength_nonneg K c i, by linarith⟩

theorem capacity_margins (i : Index K c Z T) (hcap : inverseCapacityFor i) :
    (momentWitnessFor i).inverseLength + 2 * selectedLengthFor i ≤
        rowWidthFor i - 2 * c.family.lamA ∧
      2 * (momentWitnessFor i).inverseLength + 8 * selectedLengthFor i ≤
        3 * rowWidthFor i - 2 * c.family.lamA := by
  have hm := (recipeMoment_rowWidth_spec i).1
  constructor <;> linarith [hcap.1, hcap.2]

/-- A fixed cutoff for the shell base can be imposed by a fixed cutoff
for the original scale, uniformly in every later source index. -/
theorem exists_base_threshold (B₀ : ℝ) :
    ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ {Z T : ℝ}, Z₀ ≤ Z → ∀ i : Index K c Z T,
      B₀ ≤ momentBaseFor i := by
  obtain ⟨Zh, hZh⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 16)).eventually
      (eventually_ge_atTop B₀))
  refine ⟨max 2 Zh, le_max_left _ _, ?_⟩
  intro Z T hZ i
  have hZ1 : 1 ≤ Z := (by norm_num : (1 : ℝ) ≤ 2).trans
    ((le_max_left _ _).trans hZ)
  exact (hZh Z ((le_max_right _ _).trans hZ)).trans
    (Real.rpow_le_rpow_of_exponent_le hZ1 (recipeMoment_shell_lower i))

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceMarkedActual

end
