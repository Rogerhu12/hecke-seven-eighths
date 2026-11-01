import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderAtoms
import DedekindZetaZeroFree.Arithmetic.Ideals.DivisorEpsilonBounds

/-!
# The actual finite frozen-state mass

An active radical divides the frozen row times the puncture. Every
minimum numerator has exponents 0, 1, or 3, so it divides the cube of
that same ideal. These two divisors and the original finite frequency
unit class determine the frozen state injectively. The ordinary ideal
divisor estimate therefore gives a uniform small-power state count.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalStates

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.IdealRows HeckeSkeleton.LowEnergy.FrozenIdealRows
open HeckeSkeleton.LowEnergy.ActualReflection HeckeSkeleton.LowEnergy.ActualFrozenCharges
  HeckeSkeleton.LowEnergy.ActualReflectionReindex
open DedekindZetaZeroFree.LargeSieve
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local notation "Ext" => ExteriorIdeal K S

theorem active_prime_dvd (f r : Ext) (s : FrozenState K S f r)
    (p : ExteriorPrime K S) (hp : p ∈ s.active) :
    p.val.asIdeal ∣ f.val.val * r.val.val := by
  rcases Finset.mem_union.mp (s.active_subset hp) with hf | hr
  · exact dvd_mul_of_dvd_left ((mem_exteriorSupport_iff K S f p).mp hf) _
  · exact dvd_mul_of_dvd_right ((mem_exteriorSupport_iff K S r p).mp hr) _

theorem active_divides (f r : Ext) (s : FrozenState K S f r) :
    (primeSetIdeal K S s.active).val.val ∣ f.val.val * r.val.val := by
  apply dvd_of_exponents_le (primeSetIdeal K S s.active).val (f.val * r.val)
  intro q
  by_cases hq : primeExponents (primeSetIdeal K S s.active).val q = 0
  · rw [hq]
    exact Nat.zero_le _
  let p : ExteriorPrime K S := ⟨q, (primeSetIdeal K S s.active).property q
    ((exponent_ne_zero_iff_dvd _ q).mp hq)⟩
  have hp : p ∈ s.active := (prime_dvd_primeSetIdeal_iff K S s.active p).mp
    ((exponent_ne_zero_iff_dvd _ q).mp hq)
  have he : primeExponents (primeSetIdeal K S s.active).val q = 1 := by
    change primeExponents (primeSetIdeal K S s.active).val p.val = 1
    rw [ProviderTerminalConductor.exponent_primeSetIdeal, if_pos hp]
  rw [he]
  exact Nat.one_le_iff_ne_zero.mpr
    ((exponent_ne_zero_iff_dvd (f.val * r.val) q).mpr (active_prime_dvd K S f r s p hp))

theorem minimum_divides_cube (f r : Ext) (s : FrozenState K S f r) :
    s.minimum.val.val ∣ (f.val.val * r.val.val) ^ 3 := by
  suffices h : s.minimum.val.val ∣ ((f.val * r.val) ^ 3).val by
    simpa only [SubmonoidClass.coe_pow, Submonoid.coe_mul] using h
  apply dvd_of_exponents_le s.minimum.val ((f.val * r.val) ^ 3)
  intro q
  by_cases hq : primeExponents s.minimum.val q = 0
  · rw [hq]
    exact Nat.zero_le _
  let p : ExteriorPrime K S := ⟨q, s.minimum.property q
    ((exponent_ne_zero_iff_dvd _ q).mp hq)⟩
  have hp : p ∈ s.active := s.minimum_support
    ((mem_exteriorSupport_iff K S s.minimum p).mpr
      ((exponent_ne_zero_iff_dvd _ q).mp hq))
  have hR : primeExponents (f.val * r.val) q ≠ 0 :=
    (exponent_ne_zero_iff_dvd _ q).mpr (active_prime_dvd K S f r s p hp)
  have hm := s.minimum_values q
  rw [exponent_pow]
  omega

def encode (f r : Ext) (s : FrozenState K S f r) :
    idealDivisors (f.val.val * r.val.val) ×
      idealDivisors ((f.val.val * r.val.val) ^ 3) × SixthUnitClasses K S :=
  (⟨(primeSetIdeal K S s.active).val.val,
      (mem_idealDivisors (mul_ne_zero (nonZeroDivisors.coe_ne_zero f.val)
        (nonZeroDivisors.coe_ne_zero r.val))).mpr (active_divides K S f r s)⟩,
    ⟨s.minimum.val.val,
      (mem_idealDivisors (pow_ne_zero 3 (mul_ne_zero
        (nonZeroDivisors.coe_ne_zero f.val) (nonZeroDivisors.coe_ne_zero r.val)))).mpr
          (minimum_divides_cube K S f r s)⟩,
    s.unitSector)

theorem encode_injective (f r : Ext) : Function.Injective (encode K S f r) := by
  intro s t h
  have hA : (primeSetIdeal K S s.active).val.val = (primeSetIdeal K S t.active).val.val :=
    congrArg (fun x => x.1.val) h
  have hm : s.minimum.val.val = t.minimum.val.val := congrArg (fun x => x.2.1.val) h
  have hu : s.unitSector = t.unitSector := congrArg (fun x => x.2.2) h
  apply FrozenState.ext K S
  · ext p
    rw [← prime_dvd_primeSetIdeal_iff, ← prime_dvd_primeSetIdeal_iff, hA]
  · exact Subtype.ext (Subtype.ext hm)
  · exact hu

instance frozenState_finite (f r : Ext) : Finite (FrozenState K S f r) :=
  Finite.of_injective (encode K S f r) (encode_injective K S f r)

theorem card_le_divisors (f r : Ext) :
    Nat.card (FrozenState K S f r) ≤
      (idealDivisors (f.val.val * r.val.val)).card *
        (idealDivisors ((f.val.val * r.val.val) ^ 3)).card * Nat.card (SixthUnitClasses K S) := by
  letI := Fintype.ofFinite (FrozenState K S f r)
  letI := Fintype.ofFinite (SixthUnitClasses K S)
  have h := Fintype.card_le_of_injective (encode K S f r) (encode_injective K S f r)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_coe,
    Nat.mul_assoc] using h

/-- The constant is selected before the frozen ideal and puncture.
No row norm or final canonical exponent is an input to this estimate. -/
theorem exists_state_mass_bound (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ f r : Ext,
      (Nat.card (FrozenState K S f r) : ℝ) ≤
        C * (exteriorNorm K S f * exteriorNorm K S r) ^ eps := by
  obtain ⟨B, hB, hb⟩ := ideal_divisor_count_le_rpow K (eps / 4) (by positivity)
  let C := (Nat.card (SixthUnitClasses K S) : ℝ) * B ^ 2
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro f r
  let I := f.val.val * r.val.val
  let N : ℝ := (I.absNorm : ℝ)
  have hN : 0 < N := by
    dsimp only [N, I]
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors (f.val * r.val)
  have h₁ : ((idealDivisors I).card : ℝ) ≤ B * N ^ (eps / 4) := hb I
  have h₃ : ((idealDivisors (I ^ 3)).card : ℝ) ≤ B * (N ^ 3) ^ (eps / 4) := by
    have hb₃ := hb (I ^ 3)
    change ((idealDivisors (I ^ 3)).card : ℝ) ≤
      B * (Ideal.absNorm (I ^ 3) : ℝ) ^ (eps / 4) at hb₃
    rw [map_pow, Nat.cast_pow] at hb₃
    exact hb₃
  have hpow : (N ^ 3) ^ (eps / 4) = N ^ (3 * (eps / 4)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    norm_num
  have hc : (Nat.card (FrozenState K S f r) : ℝ) ≤
      ((idealDivisors I).card : ℝ) * ((idealDivisors (I ^ 3)).card : ℝ) *
        (Nat.card (SixthUnitClasses K S) : ℝ) := by
    exact_mod_cast card_le_divisors K S f r
  have hm : (Nat.card (FrozenState K S f r) : ℝ) ≤ C * N ^ eps := by
    calc
      _ ≤ (((idealDivisors I).card : ℝ) * ((idealDivisors (I ^ 3)).card : ℝ)) *
          (Nat.card (SixthUnitClasses K S) : ℝ) := hc
      _ ≤ ((B * N ^ (eps / 4)) * (B * (N ^ 3) ^ (eps / 4))) *
          (Nat.card (SixthUnitClasses K S) : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul h₁ h₃ (Nat.cast_nonneg _) (by positivity)) (Nat.cast_nonneg _)
      _ = C * (N ^ (eps / 4) * N ^ (3 * (eps / 4))) := by rw [hpow]; dsimp [C]; ring
      _ = C * N ^ eps := by
        rw [← Real.rpow_add hN]
        congr 2
        ring
  have hnorm : N = exteriorNorm K S f * exteriorNorm K S r := by
    simp only [N, I, exteriorNorm, map_mul, Nat.cast_mul]
  rw [← hnorm]
  exact hm.trans (mul_le_mul_of_nonneg_right (le_max_right 1 C) (Real.rpow_nonneg hN.le _))

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalStates

end
