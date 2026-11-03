import HeckeSkeleton.LowEnergy.ActualReflectionReindex
import HeckeSkeleton.LowEnergy.IdealSupportPowers
import Mathlib.Data.Fintype.Pi
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Counting the literal frozen reflection states

The actual state is encoded by one activity bit and one minimum exponent
in `{0,1,2,3}` at each prime of the fixed support, together with its finite
unit sector.  Exponent two is harmless overcounting; the actual minima are
only zero, one and three.  Injectivity uses ideal factorization, including
the fact that every exponent outside the fixed support is zero.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.ActualFrozenStateCount

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.IdealRows HeckeSkeleton.LowEnergy.ActualReflection
open HeckeSkeleton.LowEnergy.ActualReflectionReindex
open scoped Classical BigOperators nonZeroDivisors NumberField

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def fixedSupport (frozen puncture : ExteriorIdeal K S) : Finset (ExteriorPrime K S) :=
  exteriorSupport K S frozen ∪ exteriorSupport K S puncture

def stateCode {frozen puncture : ExteriorIdeal K S}
    (s : FrozenState K S frozen puncture) :
    (fixedSupport K S frozen puncture → Bool × Fin 4) × SixthUnitClasses K S :=
  (fun p => (decide (p.val ∈ s.active),
    ⟨primeExponents s.minimum.val p.val.val, by
      rcases s.minimum_values p.val.val with h | h | h <;> omega⟩),
    s.unitSector)

theorem nonzero_exponent_in_fixedSupport {frozen puncture : ExteriorIdeal K S}
    (s : FrozenState K S frozen puncture) (p : HeightOneSpectrum (𝓞 K))
    (hp : primeExponents s.minimum.val p ≠ 0) :
    ∃ q : fixedSupport K S frozen puncture, q.val.val = p := by
  have hd := (exponent_ne_zero_iff_dvd s.minimum.val p).mp hp
  let q : ExteriorPrime K S := ⟨p, s.minimum.property p hd⟩
  have hq : q ∈ fixedSupport K S frozen puncture :=
    s.active_subset (s.minimum_support ((mem_exteriorSupport_iff K S _ q).mpr hd))
  exact ⟨⟨q, hq⟩, rfl⟩

theorem stateCode_injective {frozen puncture : ExteriorIdeal K S} :
    Function.Injective (stateCode K S (frozen := frozen) (puncture := puncture)) := by
  intro s t h
  have hfun := congrArg Prod.fst h
  have hu : s.unitSector = t.unitSector := congrArg Prod.snd h
  have ha : s.active = t.active := by
    ext p
    by_cases hp : p ∈ fixedSupport K S frozen puncture
    · have hb : decide (p ∈ s.active) = decide (p ∈ t.active) :=
        congrArg (fun f => (f ⟨p, hp⟩).1) hfun
      exact decide_eq_decide.mp hb
    · have hs : p ∉ s.active := fun hm => hp (s.active_subset hm)
      have ht : p ∉ t.active := fun hm => hp (t.active_subset hm)
      simp only [hs, ht]
  have he (q : fixedSupport K S frozen puncture) :
      primeExponents s.minimum.val q.val.val = primeExponents t.minimum.val q.val.val :=
    congrArg (fun f => (f q).2.val) hfun
  have hm : s.minimum = t.minimum := by
    apply Subtype.ext
    apply primeExponentEquiv.injective
    ext p
    change primeExponents s.minimum.val p = primeExponents t.minimum.val p
    by_cases hs : primeExponents s.minimum.val p = 0
    · by_cases ht : primeExponents t.minimum.val p = 0
      · exact hs.trans ht.symm
      · obtain ⟨q, rfl⟩ := nonzero_exponent_in_fixedSupport K S t p ht
        exact he q
    · obtain ⟨q, rfl⟩ := nonzero_exponent_in_fixedSupport K S s p hs
      exact he q
  exact FrozenState.ext K S ha hm hu

instance frozenStateFinite (frozen puncture : ExteriorIdeal K S) :
    Finite (FrozenState K S frozen puncture) :=
  Finite.of_injective (stateCode K S) (stateCode_injective K S)

/-- This cardinality is that of the literal state type used by the exact
reflection-index equivalence, not of an auxiliary overcounting surrogate. -/
theorem frozenState_card (frozen puncture : ExteriorIdeal K S) :
    Nat.card (FrozenState K S frozen puncture) ≤
      8 ^ (fixedSupport K S frozen puncture).card * Nat.card (SixthUnitClasses K S) := by
  letI : Fintype (SixthUnitClasses K S) := Fintype.ofFinite _
  letI : Fintype (FrozenState K S frozen puncture) := Fintype.ofFinite _
  have h := Fintype.card_le_of_injective (stateCode K S (frozen := frozen)
    (puncture := puncture)) (stateCode_injective K S)
  simpa [Nat.card_eq_fintype_card, Fintype.card_fun] using h

theorem exteriorSupport_mul (I J : ExteriorIdeal K S) :
    exteriorSupport K S (exteriorMul K S I J) =
      exteriorSupport K S I ∪ exteriorSupport K S J := by
  ext p
  simp only [Finset.mem_union, mem_exteriorSupport_iff]
  change p.val.asIdeal ∣ I.val.val * J.val.val ↔ _
  exact p.val.prime.dvd_mul

theorem exteriorSupport_image (I : ExteriorIdeal K S) :
    (exteriorSupport K S I).image Subtype.val = (primeExponents I.val).support := by
  ext p
  rw [Finsupp.mem_support_iff, exponent_ne_zero_iff_dvd]
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact (mem_exteriorSupport_iff K S I q).mp hq
  · intro hp
    let q : ExteriorPrime K S := ⟨p, I.property p hp⟩
    exact Finset.mem_image.mpr ⟨q, (mem_exteriorSupport_iff K S I q).mpr hp, rfl⟩

theorem fixedSupport_card (frozen puncture : ExteriorIdeal K S) :
    (fixedSupport K S frozen puncture).card =
      (primeExponents (frozen.val * puncture.val)).support.card := by
  change (exteriorSupport K S frozen ∪ exteriorSupport K S puncture).card = _
  rw [← exteriorSupport_mul]
  have h := Finset.card_image_of_injective (exteriorSupport K S
    (exteriorMul K S frozen puncture)) Subtype.val_injective
  rw [exteriorSupport_image] at h
  exact h.symm

/-- The complete number of actual frozen states is an arbitrary small
power of the norm of the fixed frozen and puncture ideals. -/
theorem frozenState_count_small_power (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ frozen puncture : ExteriorIdeal K S,
      (Nat.card (FrozenState K S frozen puncture) : ℝ) ≤
        C * (((frozen.val * puncture.val).val.absNorm : ℝ) ^ eps) := by
  obtain ⟨C0, hC0, hbound⟩ := IdealSupportPowers.prime_support_states_small_power
    K 8 eps (by norm_num) heps
  let U : ℝ := Nat.card (SixthUnitClasses K S)
  let C : ℝ := 1 + C0 * U
  have hU : 0 ≤ U := Nat.cast_nonneg _
  have hC : 0 < C := by
    have : 0 ≤ C0 * U := mul_nonneg (zero_le_one.trans hC0) hU
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro frozen puncture
  have hc : (Nat.card (FrozenState K S frozen puncture) : ℝ) ≤
      (8 : ℝ) ^ (primeExponents (frozen.val * puncture.val)).support.card * U := by
    dsimp only [U]
    have hcard := frozenState_card K S frozen puncture
    rw [fixedSupport_card K S frozen puncture] at hcard
    exact_mod_cast hcard
  calc
    _ ≤ (8 : ℝ) ^ (primeExponents (frozen.val * puncture.val)).support.card * U := hc
    _ ≤ (C0 * (((frozen.val * puncture.val).val.absNorm : ℝ) ^ eps)) * U :=
      mul_le_mul_of_nonneg_right (hbound (frozen.val * puncture.val)) hU
    _ ≤ C * (((frozen.val * puncture.val).val.absNorm : ℝ) ^ eps) := by
      have hp : 0 ≤ (((frozen.val * puncture.val).val.absNorm : ℝ) ^ eps) :=
        Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hcoeff : C0 * U ≤ C := by
        dsimp only [C]
        exact le_add_of_nonneg_left zero_le_one
      calc
        _ = (C0 * U) * (((frozen.val * puncture.val).val.absNorm : ℝ) ^ eps) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff hp

theorem squared_frozenState_count_small_power (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ frozen puncture : ExteriorIdeal K S,
      (Nat.card (FrozenState K S frozen puncture) : ℝ) ^ 2 ≤
        C * (((frozen.val * puncture.val).val.absNorm : ℝ) ^ eps) := by
  obtain ⟨C, hC, hbound⟩ := frozenState_count_small_power K S (eps / 2) (by positivity)
  refine ⟨C ^ 2, pow_pos hC 2, ?_⟩
  intro frozen puncture
  calc
    _ ≤ (C * (((frozen.val * puncture.val).val.absNorm : ℝ) ^ (eps / 2))) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hbound frozen puncture) 2
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
      congr 1
      congr 1
      ring

#print axioms stateCode_injective
#print axioms frozenState_card
#print axioms frozenState_count_small_power
#print axioms squared_frozenState_count_small_power

end HeckeSkeleton.LowEnergy.ActualFrozenStateCount
