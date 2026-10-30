import HeckeGeneral.Arithmetic.ResidueFourier
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Fourier transforms of actual ideals in a finite ring

The annihilator is the ideal of ring elements killing every element of
the given ideal. A primitive ring pairing proves that its character
orthogonal is exactly this algebraic annihilator. The finite Fourier
transform of ideal membership is therefore computed without a chosen
principal generator. This is the general-ideal alternative to the
nonunit multiplication-kernel formula.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic.IdealFourierOrthogonality

open PeriodicFourier IdealMobiusMask
open scoped BigOperators Classical

variable {R : Type*} [CommRing R]

def annihilatorIdeal (I : Ideal R) : Ideal R where
  carrier := {h | ∀ a ∈ I, h * a = 0}
  zero_mem' := by simp
  add_mem' := by
    intro h k hh hk a ha
    rw [add_mul, hh a ha, hk a ha, add_zero]
  smul_mem' := by
    intro c h hh a ha
    change (c * h) * a = 0
    rw [mul_assoc, hh a ha, mul_zero]

@[simp] theorem mem_annihilatorIdeal (I : Ideal R) (h : R) :
    h ∈ annihilatorIdeal I ↔ ∀ a ∈ I, h * a = 0 := Iff.rfl

theorem annihilator_antitone {I J : Ideal R} (hIJ : I ≤ J) :
    annihilatorIdeal J ≤ annihilatorIdeal I := by
  intro h hh a ha
  exact hh a (hIJ ha)

theorem le_double_annihilator (I : Ideal R) : I ≤ annihilatorIdeal (annihilatorIdeal I) := by
  intro a ha h hh
  rw [mul_comm]
  exact hh a ha

def restrictedCharacter (ψ : AddChar R ℂ) (I : Ideal R) (h : R) : AddChar I ℂ :=
  (ψ.mulShift h).compAddMonoidHom I.toAddSubgroup.subtype

@[simp] theorem restrictedCharacter_apply (ψ : AddChar R ℂ) (I : Ideal R)
    (h : R) (a : I) : restrictedCharacter ψ I h a = ψ (h * a.val) := rfl

theorem restrictedCharacter_eq_one_of_mem (ψ : AddChar R ℂ) (I : Ideal R)
    (h : R) (hh : h ∈ annihilatorIdeal I) : restrictedCharacter ψ I h = 1 := by
  ext a
  simp only [restrictedCharacter_apply, hh a.val a.property, AddChar.map_zero_eq_one, AddChar.one_apply]

theorem restrictedCharacter_eq_one_iff (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (I : Ideal R) (h : R) : restrictedCharacter ψ I h = 1 ↔ h ∈ annihilatorIdeal I := by
  constructor
  · intro he a ha
    by_contra hzero
    obtain ⟨b, hb⟩ := AddChar.ne_one_iff.mp (hψ hzero)
    have hab : a * b ∈ I := I.mul_mem_right b ha
    have heval := congrArg (fun φ : AddChar I ℂ => φ ⟨a * b, hab⟩) he
    apply hb
    simpa only [restrictedCharacter_apply, AddChar.one_apply, AddChar.mulShift_apply,
      mul_assoc] using heval
  · exact restrictedCharacter_eq_one_of_mem ψ I h

section Finite

variable [Fintype R]

instance fintypeIdeal (I : Ideal R) : Fintype I := Fintype.ofFinite _

def idealCard (I : Ideal R) : ℕ := Fintype.card I

theorem idealCard_pos (I : Ideal R) : 0 < idealCard I := Fintype.card_pos

theorem sum_membershipIndicator (I : Ideal R) (f : R → ℂ) :
    ∑ a : R, f a * membershipIndicator I a = ∑ a : I, f a.val := by
  simp only [membershipIndicator, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simpa only [Finset.subtype_univ] using
    (Finset.sum_subtype_eq_sum_filter (s := Finset.univ) (p := fun a : R => a ∈ I) f).symm

theorem fourier_indicator (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (I : Ideal R) (h : R) :
    fourier ψ (membershipIndicator I) h =
      if h ∈ annihilatorIdeal I then (idealCard I : ℂ) else 0 := by
  have hs : fourier ψ (membershipIndicator I) h = ∑ a : I, restrictedCharacter ψ I h a := by
    unfold fourier
    simpa only [mul_comm, restrictedCharacter_apply] using sum_membershipIndicator I (fun a => ψ (h * a))
  rw [hs]
  split_ifs with hh
  · exact AddChar.sum_eq_card_of_eq_one (restrictedCharacter_eq_one_of_mem ψ I h hh)
  · exact AddChar.sum_eq_zero_of_ne_one (fun he => hh ((restrictedCharacter_eq_one_iff ψ hψ I h).mp he))

theorem energy_indicator (I : Ideal R) : energy (membershipIndicator I) = (idealCard I : ℝ) := by
  unfold energy membershipIndicator idealCard
  have hpoint (a : R) : ‖(if a ∈ I then 1 else 0 : ℂ)‖ ^ 2 =
      if a ∈ I then (1 : ℝ) else 0 := by split_ifs <;> norm_num
  simp only [hpoint]
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  exact (Fintype.card_subtype (fun a : R => a ∈ I)).symm

theorem fourier_indicator_eq_const_mul (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (I : Ideal R) :
    fourier ψ (membershipIndicator I) =
      fun h => (idealCard I : ℂ) * membershipIndicator (annihilatorIdeal I) h := by
  funext h
  rw [fourier_indicator ψ hψ]
  simp only [membershipIndicator, mul_ite, mul_one, mul_zero]

theorem idealCard_mul_annihilator (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (I : Ideal R) :
    (idealCard I : ℝ) * idealCard (annihilatorIdeal I) = (Fintype.card R : ℝ) := by
  have he := energy_fourier ψ hψ (membershipIndicator I)
  rw [fourier_indicator_eq_const_mul ψ hψ, energy_const_mul, energy_indicator,
    energy_indicator] at he
  have hn : ‖(idealCard I : ℂ)‖ = (idealCard I : ℝ) := by simp
  rw [hn] at he
  have hp : (0 : ℝ) < idealCard I := by exact_mod_cast idealCard_pos I
  nlinarith

theorem idealCard_mul_annihilator_nat (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (I : Ideal R) :
    idealCard I * idealCard (annihilatorIdeal I) = Fintype.card R := by
  exact_mod_cast idealCard_mul_annihilator ψ hψ I

end Finite

end HeckeGeneral.Arithmetic.IdealFourierOrthogonality
