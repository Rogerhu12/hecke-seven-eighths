import HeckeGeneral.Characters.PrincipalUnitFiltration
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! Actual reduction of the local integer unit group and its principal-unit kernels. -/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

abbrev LocalIntegerRing (v : HeightOneSpectrum (𝓞 K)) := v.adicCompletionIntegers K

def localMaximalIdeal (v : HeightOneSpectrum (𝓞 K)) : Ideal (LocalIntegerRing K v) :=
  IsLocalRing.maximalIdeal (LocalIntegerRing K v)

abbrev LocalResidueRing (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :=
  LocalIntegerRing K v ⧸ localMaximalIdeal K v ^ n

/-- Reduction modulo the actual `n`th power of the local maximal ideal. -/
def localUnitReduction (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (LocalIntegerRing K v)ˣ →* (LocalResidueRing K v n)ˣ :=
  Units.map (Ideal.Quotient.mk (localMaximalIdeal K v ^ n)).toMonoidHom

def principalUnits (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Subgroup (LocalIntegerRing K v)ˣ := (localUnitReduction K v n).ker

theorem mem_principalUnits_iff (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (u : (LocalIntegerRing K v)ˣ) :
    u ∈ principalUnits K v n ↔ u.val - 1 ∈ localMaximalIdeal K v ^ n := by
  change localUnitReduction K v n u = 1 ↔ _
  rw [Units.ext_iff]
  change Ideal.Quotient.mk (localMaximalIdeal K v ^ n) u.val =
    Ideal.Quotient.mk (localMaximalIdeal K v ^ n) 1 ↔ _
  exact Ideal.Quotient.mk_eq_mk_iff_sub_mem u.val 1

theorem mem_principalUnits_iff_norm (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (u : (LocalIntegerRing K v)ˣ) :
    u ∈ principalUnits K v n ↔
      ‖(u.val : v.adicCompletion K) - 1‖ ≤ (residueCard K v : ℝ)⁻¹ ^ n := by
  rw [mem_principalUnits_iff]
  exact integral_principalUnit_iff_maximalIdeal_pow K v u n

theorem mem_principalUnits_iff_valuation (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (u : (LocalIntegerRing K v)ˣ) :
    u ∈ principalUnits K v n ↔
      (Valued.v ((u.val : v.adicCompletion K) - 1) : WithZero (Multiplicative ℤ)) ≤
        WithZero.exp (-(n : ℤ)) := by
  rw [mem_principalUnits_iff_norm]
  exact localNorm_le_inv_residueCard_pow_iff K v _ n

@[simp] theorem principalUnits_zero (v : HeightOneSpectrum (𝓞 K)) :
    principalUnits K v 0 = ⊤ := by
  ext u
  simp [mem_principalUnits_iff]

theorem principalUnits_antitone (v : HeightOneSpectrum (𝓞 K)) :
    Antitone (principalUnits K v) := by
  intro n m hnm u hu
  rw [mem_principalUnits_iff] at hu ⊢
  exact Ideal.pow_le_pow_right hnm hu

theorem principalUnits_succ_le (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    principalUnits K v (n + 1) ≤ principalUnits K v n :=
  principalUnits_antitone K v n.le_succ

theorem principalUnits_mul_mem (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    {u w : (LocalIntegerRing K v)ˣ} (hu : u ∈ principalUnits K v n)
    (hw : w ∈ principalUnits K v n) : u * w ∈ principalUnits K v n :=
  (principalUnits K v n).mul_mem hu hw

theorem principalUnits_inv_mem (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    {u : (LocalIntegerRing K v)ˣ} (hu : u ∈ principalUnits K v n) :
    u⁻¹ ∈ principalUnits K v n := (principalUnits K v n).inv_mem hu

theorem principalUnits_pow_mem (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    {u : (LocalIntegerRing K v)ˣ} (hu : u ∈ principalUnits K v n) (r : ℕ) :
    u ^ r ∈ principalUnits K v n := (principalUnits K v n).pow_mem hu r

theorem principalUnits_zpow_mem (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    {u : (LocalIntegerRing K v)ˣ} (hu : u ∈ principalUnits K v n) (r : ℤ) :
    u ^ r ∈ principalUnits K v n := (principalUnits K v n).zpow_mem hu r

theorem principalUnits_inter (v : HeightOneSpectrum (𝓞 K)) (n m : ℕ) :
    principalUnits K v n ⊓ principalUnits K v m = principalUnits K v (max n m) := by
  rcases le_total n m with hnm | hmn
  · rw [max_eq_right hnm, inf_eq_right.mpr (principalUnits_antitone K v hnm)]
  · rw [max_eq_left hmn, inf_eq_left.mpr (principalUnits_antitone K v hmn)]

theorem principalUnits_sup (v : HeightOneSpectrum (𝓞 K)) (n m : ℕ) :
    principalUnits K v n ⊔ principalUnits K v m = principalUnits K v (min n m) := by
  rcases le_total n m with hnm | hmn
  · rw [min_eq_left hnm, sup_eq_left.mpr (principalUnits_antitone K v hnm)]
  · rw [min_eq_right hmn, sup_eq_right.mpr (principalUnits_antitone K v hmn)]

theorem localMaximalIdeal_pow_ne_top (v : HeightOneSpectrum (𝓞 K))
    {n : ℕ} (hn : 0 < n) : localMaximalIdeal K v ^ n ≠ ⊤ := by
  exact ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    (Ideal.pow_le_self hn.ne')

theorem localUnitReduction_surjective (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Function.Surjective (localUnitReduction K v n) := by
  cases n with
  | zero =>
    intro u
    have : Subsingleton (LocalResidueRing K v 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by simp)
    refine ⟨1, ?_⟩
    apply Units.ext
    exact Subsingleton.elim _ _
  | succ n =>
    have : Nontrivial (LocalResidueRing K v (n + 1)) :=
      Ideal.Quotient.nontrivial_iff.mpr (localMaximalIdeal_pow_ne_top K v (Nat.succ_pos n))
    exact IsLocalRing.surjective_units_map_of_local_ringHom
      (Ideal.Quotient.mk (localMaximalIdeal K v ^ (n + 1))) Ideal.Quotient.mk_surjective
      (IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective)

/-- The quotient by the principal units is the actual unit group of the residue ring. -/
def principalUnitsQuotientEquiv (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    ((LocalIntegerRing K v)ˣ ⧸ principalUnits K v n) ≃* (LocalResidueRing K v n)ˣ :=
  QuotientGroup.quotientKerEquivOfSurjective (localUnitReduction K v n)
    (localUnitReduction_surjective K v n)

theorem principalUnits_error_product_mem (v : HeightOneSpectrum (𝓞 K))
    {n m : ℕ} {u w : (LocalIntegerRing K v)ˣ}
    (hu : u ∈ principalUnits K v n) (hw : w ∈ principalUnits K v m) :
    (u.val - 1) * (w.val - 1) ∈ localMaximalIdeal K v ^ (n + m) := by
  rw [pow_add]
  exact Ideal.mul_mem_mul ((mem_principalUnits_iff K v n u).mp hu)
    ((mem_principalUnits_iff K v m w).mp hw)

theorem principalUnits_product_linear_mod (v : HeightOneSpectrum (𝓞 K))
    {n m : ℕ} {u w : (LocalIntegerRing K v)ˣ}
    (hu : u ∈ principalUnits K v n) (hw : w ∈ principalUnits K v m) :
    Ideal.Quotient.mk (localMaximalIdeal K v ^ (n + m)) ((u * w).val - 1) =
      Ideal.Quotient.mk (localMaximalIdeal K v ^ (n + m)) (u.val - 1) +
      Ideal.Quotient.mk (localMaximalIdeal K v ^ (n + m)) (w.val - 1) := by
  rw [← map_add]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  have he : (u * w).val - 1 - (u.val - 1 + (w.val - 1)) =
      (u.val - 1) * (w.val - 1) := by simp only [Units.val_mul]; ring
  rw [he]
  exact principalUnits_error_product_mem K v hu hw

end HeckeGeneral.Characters
