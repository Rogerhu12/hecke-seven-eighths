import HeckePort.Moments.Canonical
import HeckePort.Moments.FullCorrelation
import HeckePort.Moments.Fourier

/-!
# Correlations of unequal moduli

Port of the generic part of openai/math `OAI/NumberTheory/DirichletL/Moments/Unequal.lean`
(revision `fd4aeeb2`).  The `Domain` section (statements about full-modulus correlations over an
arbitrary integral domain: the divisor congruence, the constant-character reduction, the vanishing
for a nontrivial lifted character) is verbatim.

The `Eisenstein` section specializes to a prime `p` of `ℤ[ω]` with the sextic residue
character `actualSextic (span {p})` (`unequal_prime_power_zero_of_not_six`, `_factor`,
`_zero_of_nonunit`, `_norm_le`, `_support`): it uses the order-six statement
`actualSextic_order_six`, the supported-modulus characters `supportedModulusCharacter` and
principal prime generators.  The prime-power content is therefore stated for abstract characters
below (`unequal_prime_power_zero_of_nontrivial`, `unequal_norm_le`): the order-six / sextic
input becomes the hypothesis `hψ : ψv ≠ 1`, and the lifting to a prime `p` is `hu`, `hv'`.
-/

noncomputable section
open scoped BigOperators Classical
namespace HeckePort.Moments.Unequal
open HeckePort.Moments HeckePort.Moments.CommonSupport

section Domain
variable {A : Type*} [CommRing A] [IsDomain A]

theorem divisor_congruence (v t k : A) (hv : v ≠ 0)
    (x : Residue (v * t)) (y : Residue v) :
    scaledResidue (v * t) v ((v * t) * v) rfl x -
      scaledResidue v (v * t) ((v * t) * v) (mul_comm _ _) y =
      Ideal.Quotient.mk _ (v * k) ↔
      x = scaledResidue v t (v * t) rfl y + Ideal.Quotient.mk _ k := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_congruence, scaledResidue_mk, ← map_add, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  change (v * t) * v ∣ v * x - (v * t) * y - v * k ↔ v * t ∣ x - (t * y + k)
  rw [show (v * t) * v = v * (v * t) by ring,
    show v * x - (v * t) * y - v * k = v * (x - (t * y + k)) by ring]
  exact mul_dvd_mul_iff_left hv

theorem fullCorrelation_divisor (v t k : A) (hv : v ≠ 0)
    [Fintype (Residue (v * t))] [Fintype (Residue v)]
    (χu : MulChar (Residue (v * t)) ℂ) (χv : MulChar (Residue v) ℂ) :
    fullModulusCorrelation (v * t) v χu χv (v * k) =
      ∑ y : Residue v, χu (scaledResidue v t (v * t) rfl y + Ideal.Quotient.mk _ k) *
        star (χv y) := by
  unfold fullModulusCorrelation fullCorrelation
  simp_rw [divisor_congruence v t k hv]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem fullCorrelation_divisor_constant (v t k : A) (hv : v ≠ 0)
    [Fintype (Residue (v * t))] [Fintype (Residue v)]
    (χu : MulChar (Residue (v * t)) ℂ) (χv : MulChar (Residue v) ℂ)
    (hχ : ∀ y : Residue v,
      χu (scaledResidue v t (v * t) rfl y + Ideal.Quotient.mk _ k) = χu (Ideal.Quotient.mk _ k)) :
    fullModulusCorrelation (v * t) v χu χv (v * k) =
      χu (Ideal.Quotient.mk _ k) * star (∑ y : Residue v, χv y) := by
  rw [fullCorrelation_divisor v t k hv χu χv]
  simp_rw [hχ]
  rw [← Finset.mul_sum, star_sum]

omit [IsDomain A] in
theorem divisor_lift_constant (p v t k : A) (hpt : p ∣ t)
    (χu : MulChar (Residue (v * t)) ℂ) (χ : MulChar (Residue p) ℂ)
    (hχ : ∀ x : A, χu (Ideal.Quotient.mk _ x) = χ (Ideal.Quotient.mk _ x)) :
    ∀ y : Residue v, χu (scaledResidue v t (v * t) rfl y + Ideal.Quotient.mk _ k) =
      χu (Ideal.Quotient.mk _ k) := by
  intro y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_mk, ← map_add, hχ, hχ, map_add, map_mul]
  have ht : Ideal.Quotient.mk (Ideal.span {p}) t = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hpt)
  rw [ht, zero_mul, zero_add]

omit [IsDomain A] in
theorem lifted_character_sum_zero (p v : A) (hpv : p ∣ v)
    [Fintype (Residue p)] [Fintype (Residue v)]
    (χv : MulChar (Residue v) ℂ) (χ : MulChar (Residue p) ℂ) (hχ : χ ≠ 1)
    (hlift : ∀ x : A, χv (Ideal.Quotient.mk _ x) = χ (Ideal.Quotient.mk _ x)) :
    (∑ y : Residue v, χv y) = 0 := by
  let π : Residue v →+* Residue p :=
    Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr hpv)
  have hπ : Function.Surjective π := Ideal.Quotient.factor_surjective _
  have he (y : Residue v) : χv y = χ (π y) := by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact hlift y
  simp_rw [he]
  rw [sum_reduction π hπ χ, MulChar.sum_eq_zero_of_ne_one hχ, mul_zero]

theorem fullCorrelation_divisor_eq_zero (p v t k : A) (hv : v ≠ 0)
    (hpv : p ∣ v) (hpt : p ∣ t)
    [Fintype (Residue p)] [Fintype (Residue (v * t))] [Fintype (Residue v)]
    (χu : MulChar (Residue (v * t)) ℂ) (χv : MulChar (Residue v) ℂ)
    (ψu ψv : MulChar (Residue p) ℂ) (hψv : ψv ≠ 1)
    (hu : ∀ x : A, χu (Ideal.Quotient.mk _ x) = ψu (Ideal.Quotient.mk _ x))
    (hv' : ∀ x : A, χv (Ideal.Quotient.mk _ x) = ψv (Ideal.Quotient.mk _ x)) :
    fullModulusCorrelation (v * t) v χu χv (v * k) = 0 := by
  rw [fullCorrelation_divisor_constant v t k hv χu χv
    (divisor_lift_constant p v t k hpt χu ψu hu),
    lifted_character_sum_zero p v hpv χv ψv hψv hv', star_zero, mul_zero]

end Domain

/-- The abstract form of `unequal_prime_power_zero_of_not_six`: for `v = q ^ j`, `t = q ^ d` the
vanishing needs a nontrivial lifted character `ψv ≠ 1` on the residue ring of a common divisor `p`
of `v` and `t`; that `actualSextic ^ j ≠ 1` when `6 ∤ j` is the order-six fact. -/
theorem unequal_prime_power_zero_of_nontrivial {A : Type*} [CommRing A] [IsDomain A]
    (p v t k : A) (hv : v ≠ 0) (hpv : p ∣ v) (hpt : p ∣ t)
    [Fintype (Residue p)] [Fintype (Residue (v * t))] [Fintype (Residue v)]
    (χu : MulChar (Residue (v * t)) ℂ) (χv : MulChar (Residue v) ℂ)
    (ψu ψv : MulChar (Residue p) ℂ) (hψv : ψv ≠ 1)
    (hu : ∀ x : A, χu (Ideal.Quotient.mk _ x) = ψu (Ideal.Quotient.mk _ x))
    (hv' : ∀ x : A, χv (Ideal.Quotient.mk _ x) = ψv (Ideal.Quotient.mk _ x)) :
    fullModulusCorrelation (v * t) v χu χv (v * k) = 0 :=
  fullCorrelation_divisor_eq_zero p v t k hv hpv hpt χu χv ψu ψv hψv hu hv'

/-- The abstract form of `unequal_prime_power_norm_le`: when `χu` is constant along the lift of
the residue ring of `v` (the case of a prime-power modulus), the correlation is bounded by the
number of residues of `v`, for characters bounded by one. -/
theorem unequal_norm_le {A : Type*} [CommRing A] [IsDomain A] (v t k : A) (hv : v ≠ 0)
    [Fintype (Residue (v * t))] [Fintype (Residue v)]
    (χu : MulChar (Residue (v * t)) ℂ) (χv : MulChar (Residue v) ℂ)
    (hχ : ∀ y : Residue v,
      χu (scaledResidue v t (v * t) rfl y + Ideal.Quotient.mk _ k) = χu (Ideal.Quotient.mk _ k))
    (hu1 : ‖χu (Ideal.Quotient.mk _ k)‖ ≤ 1) (hv1 : ∀ y, ‖χv y‖ ≤ 1) :
    ‖fullModulusCorrelation (v * t) v χu χv (v * k)‖ ≤ (Fintype.card (Residue v) : ℝ) := by
  rw [fullCorrelation_divisor_constant v t k hv χu χv hχ, norm_mul, norm_star]
  calc
    _ ≤ 1 * ‖∑ y : Residue v, χv y‖ := mul_le_mul_of_nonneg_right hu1 (norm_nonneg _)
    _ = ‖∑ y : Residue v, χv y‖ := one_mul _
    _ ≤ ∑ y : Residue v, ‖χv y‖ := norm_sum_le _ _
    _ ≤ ∑ _y : Residue v, (1 : ℝ) := Finset.sum_le_sum (fun y _ => hv1 y)
    _ = _ := by simp

end HeckePort.Moments.Unequal

end
