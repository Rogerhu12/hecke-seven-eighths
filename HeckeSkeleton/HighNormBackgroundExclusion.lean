import HeckeGeneral.Analysis.PhysicalProbeRows
import HeckeGeneral.Characters.InfinityPacket
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
An explicit finite obstruction to pure norm twists in high physical rows.
For each fixed background there is at most ONE finite-order row character
that can turn it into a norm twist. Its conjugate orientation adds only the
inverse character. Finite fibers therefore give a common actual-row norm
cutoff, uniform over every exponent above a fixed positive lower exponent.

The fiber hypothesis is deliberately explicit. RowCharacterInput supplies
finite order but does not assert finite fibers for an arbitrary constructor.
The cached arithmetic Kummer fiber theorem is a candidate provider only for
its actual arithmetic row constructor after calibration. No norm-pole
exclusion, asymptotic estimate, or large COMPLETE-ideal norm is assumed.
-/
set_option autoImplicit false

noncomputable section

namespace HeckeSkeleton.HighNormBackgroundExclusion

open NumberField IsDedekindDomain Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- The only possible finite-order character correcting this background
to a pure norm twist, as detected at the fixed infinite place. This
character is defined explicitly; no assertion of its finite order is made. -/
def normCompatibleCharacter (v : InfinitePlace K) (β : HeckeCharacter K) :
    HeckeCharacter K :=
  β⁻¹ * heckeNormTwist K (-heckeRadialParameter K v β)

/-- A finite-order factor cannot change the background's radial parameter.
Thus the entire real family of possible norm twists collapses to one t. -/
theorem norm_twist_parameter_forced
    (v : InfinitePlace K) (β χ : HeckeCharacter K) (hχ : FiniteOrder χ)
    (t : ℝ) (h : β * χ = heckeNormTwist K t) :
    t = -heckeRadialParameter K v β := by
  have hp := congrArg (heckeRadialParameter K v) h
  rw [heckeRadialParameter_mul, heckeRadialParameter_finiteOrder K v hχ,
    heckeRadialParameter_normTwist] at hp
  linarith

theorem character_eq_normCompatible_of_mul_norm_twist
    (v : InfinitePlace K) (β χ : HeckeCharacter K) (hχ : FiniteOrder χ)
    (t : ℝ) (h : β * χ = heckeNormTwist K t) :
    χ = normCompatibleCharacter K v β := by
  have ht := norm_twist_parameter_forced K v β χ hχ t h
  calc
    χ = β⁻¹ * (β * χ) := by simp only [inv_mul_cancel_left]
    _ = β⁻¹ * heckeNormTwist K t := congrArg (fun η => β⁻¹ * η) h
    _ = normCompatibleCharacter K v β := by rw [ht]; rfl

theorem character_eq_inv_normCompatible_of_mul_conjugate_norm_twist
    (v : InfinitePlace K) (β χ : HeckeCharacter K) (hχ : FiniteOrder χ)
    (t : ℝ) (h : β * conjugate χ = heckeNormTwist K t) :
    χ = (normCompatibleCharacter K v β)⁻¹ := by
  have hc := character_eq_normCompatible_of_mul_norm_twist K v β (conjugate χ)
    hχ.inv t h
  simpa only [conjugate, inv_inv] using congrArg (fun η : HeckeCharacter K => η⁻¹) hc

/-- Two explicit possible row characters per background, including both
orientations. The background itself may have arbitrary infinite order. -/
def normBackgroundTargets (v : InfinitePlace K) (B : Finset (HeckeCharacter K)) :
    Finset (HeckeCharacter K) :=
  B.biUnion fun β => {normCompatibleCharacter K v β, (normCompatibleCharacter K v β)⁻¹}

theorem mem_targets_of_mul_norm_twist
    (v : InfinitePlace K) (B : Finset (HeckeCharacter K))
    (β χ : HeckeCharacter K) (hβ : β ∈ B) (hχ : FiniteOrder χ)
    (t : ℝ) (h : β * χ = heckeNormTwist K t) :
    χ ∈ normBackgroundTargets K v B := by
  apply Finset.mem_biUnion.mpr
  refine ⟨β, hβ, ?_⟩
  rw [character_eq_normCompatible_of_mul_norm_twist K v β χ hχ t h]
  simp

theorem mem_targets_of_mul_conjugate_norm_twist
    (v : InfinitePlace K) (B : Finset (HeckeCharacter K))
    (β χ : HeckeCharacter K) (hβ : β ∈ B) (hχ : FiniteOrder χ)
    (t : ℝ) (h : β * conjugate χ = heckeNormTwist K t) :
    χ ∈ normBackgroundTargets K v B := by
  apply Finset.mem_biUnion.mpr
  refine ⟨β, hβ, ?_⟩
  rw [character_eq_inv_normCompatible_of_mul_conjugate_norm_twist K v β χ hχ t h]
  simp

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (R : RowCharacterInput K S P)

/-- Finite single-character fibers imply a finite preimage of each finite
target family. This uses actual FrequencyRows, including their sectors. -/
theorem finite_target_rows
    (hFib : ∀ χ : HeckeCharacter K, Finite {u : FrequencyRow K S // R.character u = χ})
    (T : Finset (HeckeCharacter K)) :
    Finite {u : FrequencyRow K S // R.character u ∈ T} := by
  letI : ∀ χ : T, Finite {u : FrequencyRow K S // R.character u = χ.val} :=
    fun χ => hFib χ.val
  let encode : {u : FrequencyRow K S // R.character u ∈ T} →
      (Σ χ : T, {u : FrequencyRow K S // R.character u = χ.val}) :=
    fun u => ⟨⟨R.character u.val, u.property⟩, ⟨u.val, rfl⟩⟩
  apply Finite.of_injective encode
  intro u w h
  apply Subtype.ext
  exact congrArg (fun z : Σ χ : T, {u : FrequencyRow K S // R.character u = χ.val} =>
    z.2.val) h

/-- A cutoff is constructed from all rows in the finite preimage; it is
not supplied as an extra exclusion hypothesis. -/
def targetNormCutoff
    (hFib : ∀ χ : HeckeCharacter K, Finite {u : FrequencyRow K S // R.character u = χ})
    (T : Finset (HeckeCharacter K)) : ℝ := by
  let Bad := {u : FrequencyRow K S // R.character u ∈ T}
  letI : Finite Bad := finite_target_rows K S P R hFib T
  letI : Fintype Bad := Fintype.ofFinite Bad
  exact (∑ u : Bad, |frequencyRowNorm K S u.val|) + 1

theorem targetNormCutoff_pos
    (hFib : ∀ χ : HeckeCharacter K, Finite {u : FrequencyRow K S // R.character u = χ})
    (T : Finset (HeckeCharacter K)) :
    0 < targetNormCutoff K S P R hFib T := by
  let Bad := {u : FrequencyRow K S // R.character u ∈ T}
  letI : Finite Bad := finite_target_rows K S P R hFib T
  letI : Fintype Bad := Fintype.ofFinite Bad
  change 0 < (∑ u : Bad, |frequencyRowNorm K S u.val|) + 1
  have hs : 0 ≤ ∑ u : Bad, |frequencyRowNorm K S u.val| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  exact hs.trans_lt (lt_add_one _)

theorem norm_lt_cutoff_of_character_mem
    (hFib : ∀ χ : HeckeCharacter K, Finite {u : FrequencyRow K S // R.character u = χ})
    (T : Finset (HeckeCharacter K)) (u : FrequencyRow K S) (hu : R.character u ∈ T) :
    frequencyRowNorm K S u < targetNormCutoff K S P R hFib T := by
  let Bad := {w : FrequencyRow K S // R.character w ∈ T}
  letI : Finite Bad := finite_target_rows K S P R hFib T
  letI : Fintype Bad := Fintype.ofFinite Bad
  change frequencyRowNorm K S u < (∑ w : Bad, |frequencyRowNorm K S w.val|) + 1
  have hsingle : |frequencyRowNorm K S u| ≤ ∑ w : Bad, |frequencyRowNorm K S w.val| :=
    Finset.single_le_sum
      (f := fun w : Bad => |frequencyRowNorm K S w.val|)
      (s := (Finset.univ : Finset Bad)) (a := (⟨u, hu⟩ : Bad))
      (fun w _ => abs_nonneg (frequencyRowNorm K S w.val))
      (Finset.mem_univ (⟨u, hu⟩ : Bad))
  exact (le_abs_self _).trans_lt (hsingle.trans_lt (lt_add_one _))

/-- Above this constructed cutoff every fixed background, in both row
orientations, is excluded from ALL pure norm twists. -/
theorem cutoff_excludes_background_norm_twists
    (hFib : ∀ χ : HeckeCharacter K, Finite {u : FrequencyRow K S // R.character u = χ})
    (v : InfinitePlace K) (B : Finset (HeckeCharacter K)) (u : FrequencyRow K S)
    (hu : targetNormCutoff K S P R hFib (normBackgroundTargets K v B) ≤
      frequencyRowNorm K S u) :
    ∀ β ∈ B,
      (∀ t : ℝ, β * R.character u ≠ heckeNormTwist K t) ∧
      (∀ t : ℝ, β * conjugate (R.character u) ≠ heckeNormTwist K t) := by
  have hnotmem : R.character u ∉ normBackgroundTargets K v B := by
    intro hmem
    exact (not_lt_of_ge hu)
      (norm_lt_cutoff_of_character_mem K S P R hFib _ u hmem)
  intro β hβ
  constructor
  · intro t h
    exact hnotmem (mem_targets_of_mul_norm_twist K v B β (R.character u)
      hβ (R.finite_order u) t h)
  · intro t h
    exact hnotmem (mem_targets_of_mul_conjugate_norm_twist K v B β (R.character u)
      hβ (R.finite_order u) t h)

/-- The threshold is selected after the fixed backgrounds and dmin, and
before Z,d and the row. The lower bound is on the ACTUAL sixth-power-free
FrequencyRow norm, not on an arbitrary complete ideal representing it. -/
theorem eventually_excludes_background_norm_twists
    (hFib : ∀ χ : HeckeCharacter K, Finite {u : FrequencyRow K S // R.character u = χ})
    (v : InfinitePlace K) (B : Finset (HeckeCharacter K))
    (dmin : ℝ) (hdmin : 0 < dmin) :
    ∃ Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ∀ d : ℝ, dmin ≤ d → ∀ u : FrequencyRow K S,
        Z ^ d ≤ frequencyRowNorm K S u → ∀ β ∈ B,
          (∀ t : ℝ, β * R.character u ≠ heckeNormTwist K t) ∧
          (∀ t : ℝ, β * conjugate (R.character u) ≠ heckeNormTwist K t) := by
  obtain ⟨Z₁, hZ₁⟩ := (tendsto_atTop_atTop.mp (tendsto_rpow_atTop hdmin))
    (targetNormCutoff K S P R hFib (normBackgroundTargets K v B))
  refine ⟨max 1 Z₁, le_max_left _ _, ?_⟩
  intro Z hZ d hd u hu
  apply cutoff_excludes_background_norm_twists K S P R hFib v B u
  have hZ1 : 1 ≤ Z := (le_max_left 1 Z₁).trans hZ
  exact (hZ₁ Z ((le_max_right 1 Z₁).trans hZ)).trans
    ((Real.rpow_le_rpow_of_exponent_le hZ1 hd).trans hu)

/-- The physical moderate/high lower exponent is 1/16; all original sixth
unit sectors and every later shell exponent d>=1/16 are covered uniformly. -/
theorem high_rows_exclude_background_norm_twists
    (hFib : ∀ χ : HeckeCharacter K, Finite {u : FrequencyRow K S // R.character u = χ})
    (v : InfinitePlace K) (B : Finset (HeckeCharacter K)) :
    ∃ Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → ∀ u : FrequencyRow K S,
        Z ^ d ≤ frequencyRowNorm K S u → ∀ β ∈ B,
          (∀ t : ℝ, β * R.character u ≠ heckeNormTwist K t) ∧
          (∀ t : ℝ, β * conjugate (R.character u) ≠ heckeNormTwist K t) :=
  eventually_excludes_background_norm_twists K S P R hFib v B (1 / 16) (by norm_num)

end HeckeSkeleton.HighNormBackgroundExclusion
