import CubicSieve.Gauss

/-!
Generic Chinese-remainder algebra for actual pair Gauss sums.
Adapted from the read-only OAI GaussSum/ChineseRemainder.lean cache.
The arithmetic specialization supplies its literal principal-phase characters.
-/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.GaussPairCRT
open scoped Classical BigOperators


variable {T R S : Type*} [CommRing T] [CommRing R] [CommRing S]

def leftAddChar (e : T ≃+* R × S) (ψ : AddChar T ℂ) : AddChar R ℂ where
  toFun z := ψ (e.symm (z, 0))
  map_zero_eq_one' := by
    change ψ (e.symm (0 : R × S)) = 1
    rw [map_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' z w := by
    change ψ (e.symm (z + w, 0)) = ψ (e.symm (z, 0)) * ψ (e.symm (w, 0))
    rw [show (z + w, (0 : S)) = (z, 0) + (w, 0) by ext <;> simp,
      map_add, AddChar.map_add_eq_mul]

def rightAddChar (e : T ≃+* R × S) (ψ : AddChar T ℂ) : AddChar S ℂ where
  toFun z := ψ (e.symm (0, z))
  map_zero_eq_one' := by
    change ψ (e.symm (0 : R × S)) = 1
    rw [map_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' z w := by
    change ψ (e.symm (0, z + w)) = ψ (e.symm (0, z)) * ψ (e.symm (0, w))
    rw [show ((0 : R), z + w) = (0, z) + (0, w) by ext <;> simp,
      map_add, AddChar.map_add_eq_mul]

theorem addChar_crt_factor (e : T ≃+* R × S) (ψ : AddChar T ℂ) (x : T) :
    ψ x = leftAddChar e ψ (e x).1 * rightAddChar e ψ (e x).2 := by
  let z := e x
  have hz : (z.1, (0 : S)) + ((0 : R), z.2) = z := by ext <;> simp
  calc
    ψ x = ψ (e.symm z) := by simp [z]
    _ = ψ (e.symm (z.1, 0) + e.symm (0, z.2)) := by rw [← map_add, hz]
    _ = _ := by rw [AddChar.map_add_eq_mul]; rfl

theorem gauss_sum_crt [Fintype T] [Fintype R] [Fintype S]
    (e : T ≃+* R × S) (χR : MulChar R ℂ) (χS : MulChar S ℂ)
    (ψ : AddChar T ℂ) :
    (∑ x : T, χR (e x).1 * χS (e x).2 * ψ x) =
      gaussSum χR (leftAddChar e ψ) * gaussSum χS (rightAddChar e ψ) := by
  simp_rw [addChar_crt_factor e ψ]
  let F : R × S → ℂ := fun z =>
    χR z.1 * χS z.2 * leftAddChar e ψ z.1 * rightAddChar e ψ z.2
  calc
    (∑ x : T,
      χR (e x).1 * χS (e x).2 *
        (leftAddChar e ψ (e x).1 * rightAddChar e ψ (e x).2)) =
        ∑ x : T, F (e x) := by congr 1; ext x; simp [F]; ring
    _ = ∑ z : R × S, F z := Equiv.sum_comp e.toEquiv F
    _ = ∑ z : R, ∑ w : S, F (z, w) := Fintype.sum_prod_type F
    _ = gaussSum χR (leftAddChar e ψ) * gaussSum χS (rightAddChar e ψ) := by
      simp only [F, gaussSum]
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro w hw
      ring

theorem gauss_sum_ideal_crt {A : Type*} [CommRing A]
    (I J : Ideal A) (h : IsCoprime I J)
    [Fintype (A ⧸ I * J)] [Fintype (A ⧸ I)] [Fintype (A ⧸ J)]
    (χI : MulChar (A ⧸ I) ℂ) (χJ : MulChar (A ⧸ J) ℂ)
    (ψ : AddChar (A ⧸ I * J) ℂ) :
    (∑ x : A ⧸ I * J,
      χI (Ideal.Quotient.factor (Ideal.mul_le_left : I * J ≤ I) x) *
      χJ (Ideal.Quotient.factor (Ideal.mul_le_right : I * J ≤ J) x) * ψ x) =
      gaussSum χI (leftAddChar (Ideal.quotientMulEquivQuotientProd I J h) ψ) *
      gaussSum χJ (rightAddChar (Ideal.quotientMulEquivQuotientProd I J h) ψ) := by
  let e := Ideal.quotientMulEquivQuotientProd I J h
  convert gauss_sum_crt e χI χJ ψ using 1
  congr 1
  ext x
  simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
    Ideal.quotientMulEquivQuotientProd_snd]

noncomputable def quotientAddChar {A : Type*} [CommRing A]
    (I : Ideal A) (ψ : AddChar A ℂ)
    (hper : ∀ a : A, a ∈ I → ψ a = 1) : AddChar (A ⧸ I) ℂ where
  toFun := fun x => Quotient.liftOn' x ψ (by
    intro a b hab
    have hsub : a - b ∈ I := I.quotientRel_def.mp hab
    have h := ψ.map_add_eq_mul (a - b) b
    rw [sub_add_cancel] at h
    rw [hper _ hsub, one_mul] at h
    exact h)
  map_zero_eq_one' := by
    change ψ 0 = 1
    exact AddChar.map_zero_eq_one ψ
  map_add_eq_mul' := by
    intro x y
    refine Quotient.inductionOn₂' x y ?_
    intro a b
    exact AddChar.map_add_eq_mul ψ a b

@[simp] theorem quotientAddChar_mk {A : Type*} [CommRing A]
    (I : Ideal A) (ψ : AddChar A ℂ)
    (hper : ∀ a : A, a ∈ I → ψ a = 1) (a : A) :
    quotientAddChar I ψ hper (Ideal.Quotient.mk I a) = ψ a := rfl

theorem principal_coprime_of_bezout {A : Type*} [CommRing A]
    {a b u v : A} (h : u * a + v * b = 1) :
    IsCoprime (Ideal.span {a}) (Ideal.span {b}) := by
  apply Ideal.isCoprime_iff_exists.mpr
  refine ⟨u * a, ?_, v * b, ?_, h⟩
  · exact Ideal.mem_span_singleton.mpr ⟨u, by ring⟩
  · exact Ideal.mem_span_singleton.mpr ⟨v, by ring⟩

theorem bezout_of_principal_coprime {A : Type*} [CommRing A]
    {a b : A} (h : IsCoprime (Ideal.span {a}) (Ideal.span {b})) :
    ∃ u v : A, u * a + v * b = 1 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Ideal.isCoprime_iff_exists.mp h
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp hy
  refine ⟨u, v, ?_⟩
  rw [hu, hv] at hxy
  convert hxy using 1; ring

theorem crt_left_inverse_coordinate {A : Type*} [CommRing A]
    {a b u v : A} (hbez : u * a + v * b = 1) (x : A) :
    (Ideal.quotientMulEquivQuotientProd
      (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)).symm
        (Ideal.Quotient.mk (Ideal.span {a}) x, 0) =
      Ideal.Quotient.mk ((Ideal.span {a}) * (Ideal.span {b})) (x * v * b) := by
  let I : Ideal A := Ideal.span {a}
  let J : Ideal A := Ideal.span {b}
  let e := Ideal.quotientMulEquivQuotientProd I J
    (principal_coprime_of_bezout hbez)
  apply e.injective
  apply Prod.ext
  · change (e (e.symm (Ideal.Quotient.mk I x, 0))).1 =
      (e (Ideal.Quotient.mk (I * J) (x * v * b))).1
    rw [e.apply_symm_apply]
    simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
      Ideal.Quotient.factor_mk]
    apply Ideal.Quotient.eq.mpr
    change x - x * v * b ∈ I
    rw [Ideal.mem_span_singleton]
    refine ⟨x * u, ?_⟩
    calc
      x - x * v * b = x * (u * a + v * b) - x * v * b := by rw [hbez]; ring
      _ = a * (x * u) := by ring
  · change (e (e.symm (Ideal.Quotient.mk I x, 0))).2 =
      (e (Ideal.Quotient.mk (I * J) (x * v * b))).2
    rw [e.apply_symm_apply]
    simp only [e, Ideal.quotientMulEquivQuotientProd_snd,
      Ideal.Quotient.factor_mk]
    symm
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    exact Ideal.mem_span_singleton.mpr ⟨x * v, by ring⟩

theorem crt_right_inverse_coordinate {A : Type*} [CommRing A]
    {a b u v : A} (hbez : u * a + v * b = 1) (y : A) :
    (Ideal.quotientMulEquivQuotientProd
      (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)).symm
        (0, Ideal.Quotient.mk (Ideal.span {b}) y) =
      Ideal.Quotient.mk ((Ideal.span {a}) * (Ideal.span {b})) (y * u * a) := by
  let I : Ideal A := Ideal.span {a}
  let J : Ideal A := Ideal.span {b}
  let e := Ideal.quotientMulEquivQuotientProd I J
    (principal_coprime_of_bezout hbez)
  apply e.injective
  apply Prod.ext
  · change (e (e.symm (0, Ideal.Quotient.mk J y))).1 =
      (e (Ideal.Quotient.mk (I * J) (y * u * a))).1
    rw [e.apply_symm_apply]
    simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
      Ideal.Quotient.factor_mk]
    symm
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    exact Ideal.mem_span_singleton.mpr ⟨y * u, by ring⟩
  · change (e (e.symm (0, Ideal.Quotient.mk J y))).2 =
      (e (Ideal.Quotient.mk (I * J) (y * u * a))).2
    rw [e.apply_symm_apply]
    simp only [e, Ideal.quotientMulEquivQuotientProd_snd,
      Ideal.Quotient.factor_mk]
    apply Ideal.Quotient.eq.mpr
    change y - y * u * a ∈ J
    rw [Ideal.mem_span_singleton]
    refine ⟨y * v, ?_⟩
    calc
      y - y * u * a = y * (u * a + v * b) - y * u * a := by rw [hbez]; ring
      _ = b * (y * v) := by ring


theorem gauss_shift_cross {A : Type*} [CommRing A] [Fintype A]
    (χ : MulChar A ℂ) (ψ : AddChar A ℂ) (b v : A) (h : b * v = 1) :
    gaussSum χ (ψ.mulShift v) = χ b * gaussSum χ ψ := by
  have hv : IsUnit v := IsUnit.of_mul_eq_one_right b h
  have hprod : χ b * χ v = 1 := by rw [← map_mul, h, map_one]
  have hs : χ v * gaussSum χ (ψ.mulShift v) = gaussSum χ ψ := by
    simpa only [hv.unit_spec] using gaussSum_mulShift χ ψ hv.unit
  calc
    _ = (χ b * χ v) * gaussSum χ (ψ.mulShift v) := by rw [hprod, one_mul]
    _ = χ b * (χ v * gaussSum χ (ψ.mulShift v)) := by ring
    _ = _ := by rw [hs]

theorem gauss_add_inv_even {A : Type*} [CommRing A] [Fintype A]
    (χ : MulChar A ℂ) (ψ : AddChar A ℂ) (hχ : χ (-1) = 1) :
    gaussSum χ ψ⁻¹ = gaussSum χ ψ := by
  have h := gaussSum_mulShift χ ψ (-1 : Aˣ)
  simpa only [Units.coe_neg_one, hχ, one_mul, ← ψ.inv_mulShift] using h

/-- Conjugating an even Gauss character retains the original positive phase. -/
theorem gauss_inverse_even {A : Type*} [CommRing A] [Fintype A]
    (χ : MulChar A ℂ) (ψ : AddChar A ℂ) (hχ : χ (-1) = 1) :
    gaussSum χ⁻¹ ψ = star (gaussSum χ ψ) := by
  rw [star_gaussSum_eq]
  symm
  apply gauss_add_inv_even
  rw [MulChar.inv_apply_eq_inv', hχ, inv_one]

section PrincipalPhase
variable {A E : Type*} [CommRing A] [Field E]
variable (ι : A →+* E) (Φ : E → ℂ)
variable {a b u v : A} (hbez : u * a + v * b = 1)
variable (ha : ι a ≠ 0) (hb : ι b ≠ 0)
variable (ψa : AddChar (A ⧸ Ideal.span {a}) ℂ)
variable (ψb : AddChar (A ⧸ Ideal.span {b}) ℂ)
variable (ψab : AddChar (A ⧸ (Ideal.span {a}) * (Ideal.span {b})) ℂ)
variable (hea : ∀ x : A, ψa (Ideal.Quotient.mk _ x) = Φ (ι x / ι a))
variable (heb : ∀ x : A, ψb (Ideal.Quotient.mk _ x) = Φ (ι x / ι b))
variable (heab : ∀ x : A, ψab (Ideal.Quotient.mk _ x) = Φ (ι x / (ι a * ι b)))

include ι Φ ha hb hea heab in
/-- The left axis is the actual principal character shifted by b inverse. -/
theorem leftAddChar_principal :
    leftAddChar (Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)) ψab =
        ψa.mulShift (Ideal.Quotient.mk (Ideal.span {a}) v) := by
  ext z
  refine Quotient.inductionOn' z ?_
  intro x
  change ψab ((Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
    (principal_coprime_of_bezout hbez)).symm (Ideal.Quotient.mk _ x, 0)) =
      ψa (Ideal.Quotient.mk (Ideal.span {a}) v * Ideal.Quotient.mk _ x)
  rw [crt_left_inverse_coordinate hbez, heab,
    ← map_mul (Ideal.Quotient.mk (Ideal.span {a})) v x, hea]
  congr 1
  simp only [map_mul]
  field_simp [ha, hb]

include ι Φ ha hb heb heab in
/-- The right axis is the actual principal character shifted by a inverse. -/
theorem rightAddChar_principal :
    rightAddChar (Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)) ψab =
        ψb.mulShift (Ideal.Quotient.mk (Ideal.span {b}) u) := by
  ext z
  refine Quotient.inductionOn' z ?_
  intro y
  change ψab ((Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
    (principal_coprime_of_bezout hbez)).symm (0, Ideal.Quotient.mk _ y)) =
      ψb (Ideal.Quotient.mk (Ideal.span {b}) u * Ideal.Quotient.mk _ y)
  rw [crt_right_inverse_coordinate hbez, heab,
    ← map_mul (Ideal.Quotient.mk (Ideal.span {b})) u y, heb]
  congr 1
  simp only [map_mul]
  field_simp [ha, hb]

include ι Φ hbez ha hb hea heb heab in
/-- Principal-phase CRT, with its two actual reciprocal cross factors. -/
theorem gauss_sum_principal_crt
    [Fintype (A ⧸ (Ideal.span {a}) * (Ideal.span {b}))]
    [Fintype (A ⧸ Ideal.span {a})] [Fintype (A ⧸ Ideal.span {b})]
    (χa : MulChar (A ⧸ Ideal.span {a}) ℂ) (χb : MulChar (A ⧸ Ideal.span {b}) ℂ) :
    (∑ x : A ⧸ (Ideal.span {a}) * (Ideal.span {b}),
      χa (Ideal.Quotient.factor (Ideal.mul_le_left : Ideal.span {a} * Ideal.span {b} ≤ Ideal.span {a}) x) *
      χb (Ideal.Quotient.factor (Ideal.mul_le_right : Ideal.span {a} * Ideal.span {b} ≤ Ideal.span {b}) x) * ψab x) =
        χa (Ideal.Quotient.mk _ b) * χb (Ideal.Quotient.mk _ a) *
          gaussSum χa ψa * gaussSum χb ψb := by
  have ha0 : Ideal.Quotient.mk (Ideal.span {a}) a = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self a)
  have hb0 : Ideal.Quotient.mk (Ideal.span {b}) b = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self b)
  have hav : Ideal.Quotient.mk (Ideal.span {a}) b * Ideal.Quotient.mk _ v = 1 := by
    have h := congrArg (Ideal.Quotient.mk (Ideal.span {a})) hbez
    simpa only [map_add, map_mul, map_one, ha0, mul_zero, zero_mul, zero_add, mul_comm] using h
  have hbu : Ideal.Quotient.mk (Ideal.span {b}) a * Ideal.Quotient.mk _ u = 1 := by
    have h := congrArg (Ideal.Quotient.mk (Ideal.span {b})) hbez
    simpa only [map_add, map_mul, map_one, hb0, mul_zero, zero_mul, add_zero, mul_comm] using h
  rw [gauss_sum_ideal_crt _ _ (principal_coprime_of_bezout hbez),
    leftAddChar_principal ι Φ hbez ha hb ψa ψab hea heab,
    rightAddChar_principal ι Φ hbez ha hb ψb ψab heb heab,
    gauss_shift_cross χa ψa _ _ hav, gauss_shift_cross χb ψb _ _ hbu]
  ring

end PrincipalPhase
end CubicSieve.GaussPairCRT

