import HeckeGeneral.Characters.LocalResidueDual
import Mathlib.Algebra.Group.AddChar

/-! Local Gauss sums detect the least conductor depth of the multiplicative character. -/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

local instance gaussResidueUnitFintype (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Fintype (LocalResidueRing K v n)ˣ := Fintype.ofFinite _

/-- The unit-group Gauss sum; no finite-field or squarefree hypothesis is used. -/
def localResidueGauss (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (χ : LocalResidueDual K v n) (η : AddChar (LocalResidueRing K v n) Circle) : ℂ :=
  ∑ u : (LocalResidueRing K v n)ˣ, (χ u : ℂ) * (η u.val : ℂ)

theorem localResidueGauss_norm_bound (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (χ : LocalResidueDual K v n) (η : AddChar (LocalResidueRing K v n) Circle) :
    ‖localResidueGauss K v n χ η‖ ≤ Nat.card (LocalResidueRing K v n)ˣ := by
  unfold localResidueGauss
  calc
    _ ≤ ∑ u : (LocalResidueRing K v n)ˣ, ‖(χ u : ℂ) * (η u.val : ℂ)‖ := norm_sum_le _ _
    _ = Nat.card (LocalResidueRing K v n)ˣ := by simp [Nat.card_eq_fintype_card]

theorem localResidueGauss_uniform_bound (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (χ : LocalResidueDual K v n) (η : AddChar (LocalResidueRing K v n) Circle) :
    ‖localResidueGauss K v n χ η‖ ≤ (residueCard K v : ℝ) ^ n := by
  apply (localResidueGauss_norm_bound K v n χ η).trans
  exact_mod_cast (show Nat.card (LocalResidueRing K v n)ˣ ≤ residueCard K v ^ n from by
    rw [← natCard_localResidueRing]
    exact Nat.card_le_card_of_injective Units.val Units.val_injective)

theorem localResidueGauss_mulShift (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (χ : LocalResidueDual K v n) (η : AddChar (LocalResidueRing K v n) Circle)
    (a : (LocalResidueRing K v n)ˣ) :
    (χ a : ℂ) * localResidueGauss K v n χ (η.mulShift a.val) =
      localResidueGauss K v n χ η := by
  simp only [localResidueGauss, AddChar.mulShift_apply, Finset.mul_sum]
  have hs := (Group.mulLeft_bijective a).sum_comp
    (fun u : (LocalResidueRing K v n)ˣ => (χ u : ℂ) * (η u.val : ℂ))
  simpa only [map_mul, Circle.coe_mul, Units.val_mul, mul_assoc] using hs

theorem localResidueGauss_mulShift_eq (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (χ : LocalResidueDual K v n) (η : AddChar (LocalResidueRing K v n) Circle)
    (a : (LocalResidueRing K v n)ˣ) :
    localResidueGauss K v n χ (η.mulShift a.val) =
      (χ a : ℂ)⁻¹ * localResidueGauss K v n χ η := by
  rw [← localResidueGauss_mulShift K v n χ η a, ← mul_assoc,
    inv_mul_cancel₀ (Circle.coe_ne_zero _), one_mul]

theorem localResidueGauss_eq_zero_of_shift_invariant (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (χ : LocalResidueDual K v n) (η : AddChar (LocalResidueRing K v n) Circle)
    (a : (LocalResidueRing K v n)ˣ) (hχ : χ a ≠ 1) (hη : η.mulShift a.val = η) :
    localResidueGauss K v n χ η = 0 := by
  apply eq_zero_of_mul_eq_self_left (Circle.coe_eq_one.not.mpr hχ)
  simpa only [hη] using localResidueGauss_mulShift K v n χ η a

def localResidueAddInflation (v : HeightOneSpectrum (𝓞 K)) {m n : ℕ} (hmn : m ≤ n)
    (η : AddChar (LocalResidueRing K v m) Circle) : AddChar (LocalResidueRing K v n) Circle :=
  η.compAddMonoidHom (localResidueTransition K v hmn).toAddMonoidHom

@[simp] theorem localResidueAddInflation_apply (v : HeightOneSpectrum (𝓞 K)) {m n : ℕ}
    (hmn : m ≤ n) (η : AddChar (LocalResidueRing K v m) Circle) (x : LocalResidueRing K v n) :
    localResidueAddInflation K v hmn η x = η (localResidueTransition K v hmn x) := rfl

theorem localResidueAddInflation_injective (v : HeightOneSpectrum (𝓞 K)) {m n : ℕ}
    (hmn : m ≤ n) : Function.Injective (localResidueAddInflation K v hmn) :=
  AddChar.compAddMonoidHom_injective_left _ (localResidueTransition_surjective K v hmn)

theorem localResidueAddInflation_shift_kernel (v : HeightOneSpectrum (𝓞 K)) {m n : ℕ}
    (hmn : m ≤ n) (η : AddChar (LocalResidueRing K v m) Circle)
    (a : (LocalResidueRing K v n)ˣ) (ha : a ∈ (localResidueUnitTransition K v hmn).ker) :
    (localResidueAddInflation K v hmn η).mulShift a.val = localResidueAddInflation K v hmn η := by
  apply AddChar.ext
  intro x
  change η (localResidueTransition K v hmn (a.val * x)) =
    η (localResidueTransition K v hmn x)
  have hav : localResidueTransition K v hmn a.val = 1 := congrArg Units.val ha
  rw [map_mul, hav, one_mul]

theorem primitiveLocalResidueCharacter_detects_kernel (v : HeightOneSpectrum (𝓞 K))
    {n m : ℕ} {χ : LocalResidueDual K v n} (hχ : PrimitiveLocalResidueCharacter K v n χ)
    (hm : m < n) : ∃ a : (LocalResidueRing K v n)ˣ,
      a ∈ (localResidueUnitTransition K v hm.le).ker ∧ χ a ≠ 1 := by
  have hn : ¬ (localResidueUnitTransition K v hm.le).ker ≤ χ.ker := by
    intro hk
    obtain ⟨θ, hθ⟩ := (localResidueDualInflation_range_iff_kernel K v hm.le χ).mpr hk
    exact hχ m hm ⟨θ, hθ⟩
  change ¬ ((localResidueUnitTransition K v hm.le).ker : Set (LocalResidueRing K v n)ˣ) ⊆
    (χ.ker : Set (LocalResidueRing K v n)ˣ) at hn
  obtain ⟨a, ha, hna⟩ := Set.not_subset.mp hn
  exact ⟨a, ha, hna⟩

/-- An additive character of smaller depth cannot pair with a primitive multiplicative one. -/
theorem localResidueGauss_primitive_lower_additive (v : HeightOneSpectrum (𝓞 K))
    {n m : ℕ} (χ : LocalResidueDual K v n) (hχ : PrimitiveLocalResidueCharacter K v n χ)
    (hm : m < n) (η : AddChar (LocalResidueRing K v m) Circle) :
    localResidueGauss K v n χ (localResidueAddInflation K v hm.le η) = 0 := by
  obtain ⟨a, ha, hχa⟩ := primitiveLocalResidueCharacter_detects_kernel K v hχ hm
  exact localResidueGauss_eq_zero_of_shift_invariant K v n χ _ a hχa
    (localResidueAddInflation_shift_kernel K v hm.le η a ha)

theorem conductorResidueGauss_lower_additive (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) {m : ℕ} (hm : m < localConductorExponent K χ v)
    (η : AddChar (LocalResidueRing K v m) Circle) :
    localResidueGauss K v (localConductorExponent K χ v) (conductorResidueCharacter K v χ)
      (localResidueAddInflation K v hm.le η) = 0 :=
  localResidueGauss_primitive_lower_additive K v _
    (conductorResidueCharacter_isPrimitive K v χ) hm η

theorem localResidueGauss_one_additive (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (χ : LocalResidueDual K v n) :
    localResidueGauss K v n χ (1 : AddChar (LocalResidueRing K v n) Circle) =
      if χ = 1 then (Nat.card (LocalResidueRing K v n)ˣ : ℂ) else 0 := by
  classical
  simpa only [localResidueGauss, AddChar.one_apply, Circle.coe_one, mul_one] using
    sum_circleCharacter (LocalResidueRing K v n)ˣ χ

theorem localResidueGauss_conj (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (χ : LocalResidueDual K v n) (η : AddChar (LocalResidueRing K v n) Circle) :
    star (localResidueGauss K v n χ η) = localResidueGauss K v n χ⁻¹ η⁻¹ := by
  simp only [localResidueGauss, star_sum, star_mul, MonoidHom.inv_apply, AddChar.inv_apply]
  apply Finset.sum_congr rfl
  intro u _
  have hc (z : Circle) : star (z : ℂ) = (z⁻¹ : Circle) := (Circle.coe_inv_eq_conj z).symm
  rw [hc, hc, AddChar.map_neg_eq_inv, Circle.coe_inv, Circle.coe_inv, mul_comm]

end HeckeGeneral.Characters
