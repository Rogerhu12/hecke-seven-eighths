module

public import DedekindZetaZeroFree.CharacterSums.Gauss.ResidueRowFourierTransform
public import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# The complete finite coefficient on the actual coprime support

The old common modulus is retained.  On the coprime support enforced by
the original mask, its finite coefficient is a Gauss column multiplied
by the old row character and two unit phases.  In particular, the old
row character is not replaced by a unit phase: it can vanish.

This is proved directly from the defining finite sum, including the
congruence condition and all residue classes.  There is no primitivity
assumption, no restriction to squarefree moduli and no assumed Fourier
transform identity.
-/

@[expose] public section

noncomputable section
open scoped Classical BigOperators
open DedekindZetaZeroFree FiniteTransform

namespace HeckeSkeleton.Moments.EngineStep

variable {F : Type*} [Field F]

theorem coprime_residue_isUnit (R : Subring F) (s a : R)
    (hcop : IsCoprime s a) : IsUnit (residueMap R s a) := by
  obtain ⟨u, v, huv⟩ := hcop
  have hs : residueMap R s s = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have h := congrArg (residueMap R s) huv
  simp only [map_add, map_mul, map_one, hs, mul_zero, zero_add] at h
  exact isUnit_iff_exists_inv'.mpr ⟨residueMap R s v, h⟩

theorem actual_gauss_frequency_congr (R : Subring F) (a : R) (ha : a ≠ 0)
    [Fintype (Residue R a)] (χ : MulChar (Residue R a) ℂ)
    (e : AddChar F ℂ) (he : IsTrivialOn R e) (k l : R)
    (hkl : residueMap R a k = residueMap R a l) :
    FiniteTransform.gaussSum R a χ e k = FiniteTransform.gaussSum R a χ e l := by
  unfold FiniteTransform.gaussSum gaussSumWithLifts
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  rw [mul_comm (k : F), mul_comm (l : F)]
  exact linear_phase_eq R a ha e he k l ((canonicalLifts R a).val v) hkl

/-- Reindex the complete Gauss sum by a genuine residue unit. -/
theorem actual_gauss_coprime_dilate (R : Subring F) (a s k : R) (ha : a ≠ 0)
    (hcop : IsCoprime a s) [Fintype (Residue R a)]
    (χ : MulChar (Residue R a) ℂ) (e : AddChar F ℂ) (he : IsTrivialOn R e) :
    FiniteTransform.gaussSum R a χ e k =
      χ (residueMap R a s) * FiniteTransform.gaussSum R a χ e (s * k) := by
  let u : (Residue R a)ˣ := (coprime_residue_isUnit R a s hcop).unit
  have hu : (u : Residue R a) = residueMap R a s := IsUnit.unit_spec _
  let lifts := canonicalLifts R a
  change (∑ v : Residue R a, χ v * e ((k : F) * (lifts.val v : F) / (a : F))) = _
  calc
    _ = ∑ v : Residue R a, χ ((u : Residue R a) * v) *
        e ((k : F) * (lifts.val ((u : Residue R a) * v) : F) / (a : F)) :=
      (Fintype.sum_equiv u.mulLeft _ _ (fun _ => rfl)).symm
    _ = χ (residueMap R a s) * FiniteTransform.gaussSum R a χ e (s * k) := by
      unfold FiniteTransform.gaussSum gaussSumWithLifts
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      rw [map_mul, hu, mul_assoc]
      congr 1
      congr 1
      have hp := linear_phase_eq R a ha e he
        (lifts.val ((u : Residue R a) * v)) (s * lifts.val v) k (by
          rw [lifts.property, map_mul, lifts.property, hu])
      rw [hu] at hp
      rw [hp]
      congr 1
      push_cast
      ring

/-- The old row character is explicit, including its nonunit zero values. -/
theorem finiteCoefficient_coprime_factor (R : Subring F) (s a h : R)
    (hs : s ≠ 0) (ha : a ≠ 0) (hcop : IsCoprime s a)
    [Fintype (Residue R s)] [Fintype (Residue R a)]
    (χs : MulChar (Residue R s) ℂ) (χa : MulChar (Residue R a) ℂ)
    (e : AddChar F ℂ) (he : IsTrivialOn R e) :
    finiteCoefficient R s a h χs χa e =
      χs (residueMap R s h) * star (χs (residueMap R s a)) *
        χa (residueMap R a s) * FiniteTransform.gaussSum R a χa e h := by
  let u : (Residue R s)ˣ := (coprime_residue_isUnit R s a hcop).unit
  have hu : (u : Residue R s) = residueMap R s a := IsUnit.unit_spec _
  let d₀ : Residue R s := (↑u⁻¹ : Residue R s) * residueMap R s h
  have hcondition (d : Residue R s) :
      residueMap R s h = residueMap R s a * d ↔ d = d₀ := by
    rw [← hu]
    constructor
    · intro hd
      have hh := congrArg (fun x : Residue R s => (↑u⁻¹ : Residue R s) * x) hd
      simpa only [d₀, ← mul_assoc, Units.inv_mul, one_mul] using hh.symm
    · rintro rfl
      dsimp only [d₀]
      simp only [← mul_assoc, Units.mul_inv, one_mul]
  have hd₀ : residueMap R s h = residueMap R s (a * (canonicalLifts R s).val d₀) := by
    rw [map_mul, (canonicalLifts R s).property]
    exact (hcondition d₀).mpr rfl
  obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hd₀)
  have hk' : (h : F) - (a : F) * ((canonicalLifts R s).val d₀ : F) =
      (s : F) * (k : F) := by exact_mod_cast hk
  have hs' : (s : F) ≠ 0 := by exact_mod_cast hs
  have hinner :
      (∑ v : Residue R a, χa v *
        e (((h : F) - (a : F) * ((canonicalLifts R s).val d₀ : F)) *
          ((canonicalLifts R a).val v : F) / ((s : F) * (a : F)))) =
      χa (residueMap R a s) * FiniteTransform.gaussSum R a χa e h := by
    calc
      _ = FiniteTransform.gaussSum R a χa e k := by
        unfold FiniteTransform.gaussSum gaussSumWithLifts
        apply Finset.sum_congr rfl
        intro v _
        congr 1
        congr 1
        rw [hk']
        field_simp
      _ = χa (residueMap R a s) * FiniteTransform.gaussSum R a χa e (s * k) :=
        actual_gauss_coprime_dilate R a s k ha hcop.symm χa e he
      _ = _ := by
        congr 1
        apply actual_gauss_frequency_congr R a ha χa e he
        have hzero : residueMap R a a = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
        have hh := congrArg (residueMap R a) hk
        simpa only [map_sub, map_mul, hzero, zero_mul, sub_zero] using hh.symm
  have hchar : χs d₀ = χs (residueMap R s h) * star (χs (residueMap R s a)) := by
    have hi : χs (↑u⁻¹ : Residue R s) = (χs (u : Residue R s))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, Units.inv_mul, map_one]
    rw [MulChar.star_apply', MulChar.inv_apply_eq_inv']
    dsimp only [d₀]
    rw [map_mul, hi, hu, mul_comm]
  unfold finiteCoefficient finiteCoefficientWithLifts
  simp only [hcondition, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hinner, hchar]
  ring

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.finiteCoefficient_coprime_factor
