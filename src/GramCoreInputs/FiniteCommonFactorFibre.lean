import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic
import FiniteAffineCorrelationBound

/-! SOURCE ONLY, UNRUN. An explicit common-factor fibre equivalence over
an arbitrary commutative ring and arbitrary ideal C. No coprimality of C
with the residual columns is imposed. Frequency zero is included. -/
noncomputable section
namespace HeckeGeneral.Arithmetic.PeriodicFourier
open scoped Classical
variable {R : Type*} [CommRing R]

private def quotientMultiplier (I J : Ideal R) (s : R)
    (h : ∀ x ∈ I, s * x ∈ J) : R ⧸ I →ₗ[R] R ⧸ J :=
  Submodule.mapQ I J
    { toFun := fun x => s * x
      map_add' := fun x y => mul_add s x y
      map_smul' := fun r x => by simp only [smul_eq_mul, RingHom.id_apply]; ring }
    (fun x hx => h x hx)

@[simp] private theorem quotientMultiplier_mk (I J : Ideal R) (s : R)
    (h : ∀ x ∈ I, s * x ∈ J) (x : R) :
    quotientMultiplier I J s h (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk J (s * x) := rfl

def commonFactorColumnIdeal (C : Ideal R) (n : R) : Ideal R :=
  C * Ideal.span ({n} : Set R)

def commonFactorTotalIdeal (C : Ideal R) (n₁ n₂ : R) : Ideal R :=
  (C * Ideal.span ({n₁} : Set R)) * Ideal.span ({n₂} : Set R)

private theorem total_le_first (C : Ideal R) (n₁ n₂ : R) :
    commonFactorTotalIdeal C n₁ n₂ ≤ commonFactorColumnIdeal C n₁ :=
  Ideal.mul_le_left

private theorem total_le_second (C : Ideal R) (n₁ n₂ : R) :
    commonFactorTotalIdeal C n₁ n₂ ≤ commonFactorColumnIdeal C n₂ := by
  unfold commonFactorTotalIdeal commonFactorColumnIdeal
  rw [mul_assoc, mul_comm (Ideal.span ({n₁} : Set R)), ← mul_assoc]
  exact Ideal.mul_le_left

def commonFactorFirstMultiplier (C : Ideal R) (n₁ n₂ : R) :
    R ⧸ commonFactorColumnIdeal C n₁ →ₗ[R]
      R ⧸ commonFactorTotalIdeal C n₁ n₂ :=
  quotientMultiplier _ _ n₂ fun x hx => by
    change n₂ * x ∈ commonFactorColumnIdeal C n₁ * Ideal.span ({n₂} : Set R)
    rw [mul_comm n₂ x]
    exact Ideal.mul_mem_mul hx (Ideal.subset_span (Set.mem_singleton n₂))

def commonFactorSecondMultiplier (C : Ideal R) (n₁ n₂ : R) :
    R ⧸ commonFactorColumnIdeal C n₂ →ₗ[R]
      R ⧸ commonFactorTotalIdeal C n₁ n₂ :=
  quotientMultiplier _ _ n₁ fun x hx => by
    have h := Ideal.mul_mem_mul hx (Ideal.subset_span (Set.mem_singleton n₁))
    simpa only [commonFactorColumnIdeal, commonFactorTotalIdeal,
      mul_assoc, mul_comm, mul_left_comm] using h

def commonFactorFullFibre (C : Ideal R) (n₁ n₂ k : R) :=
  {p : (R ⧸ commonFactorColumnIdeal C n₁) ×
      (R ⧸ commonFactorColumnIdeal C n₂) //
    commonFactorFirstMultiplier C n₁ n₂ p.1 -
      commonFactorSecondMultiplier C n₁ n₂ p.2 =
        Ideal.Quotient.mk (commonFactorTotalIdeal C n₁ n₂) k}

private def commonFactorParameterColumn (C : Ideal R) (n : R) :
    R ⧸ C →ₗ[R] R ⧸ commonFactorColumnIdeal C n :=
  quotientMultiplier _ _ n fun x hx => by
    change n * x ∈ C * Ideal.span ({n} : Set R)
    rw [mul_comm n x]
    exact Ideal.mul_mem_mul hx (Ideal.subset_span (Set.mem_singleton n))

def commonFactorReduce (C : Ideal R) (n : R) :
    R ⧸ commonFactorColumnIdeal C n →ₗ[R] R ⧸ C :=
  quotientMultiplier _ _ 1 fun x hx => by
    simpa only [one_mul] using (Ideal.mul_le_left hx : x ∈ C)

@[simp] theorem commonFactorReduce_mk (C : Ideal R) (n x : R) :
    commonFactorReduce C n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk C x := by
  simp only [commonFactorReduce, quotientMultiplier_mk, one_mul]

/-- The full fibre has exactly one parameter modulo C, without cancellation
or a domain hypothesis. Its two quotient multipliers define the original
congruence modulo C*(n1)*(n2), rather than a weakened congruence modulo C. -/
def commonFactorFullFibreEquiv (C : Ideal R) (n₁ n₂ a b k : R)
    (hab : a * n₂ - b * n₁ = 1) :
    (R ⧸ C) ≃ commonFactorFullFibre C n₁ n₂ k where
  toFun t := ⟨(Ideal.Quotient.mk _ (a * k) + commonFactorParameterColumn C n₁ t,
    Ideal.Quotient.mk _ (b * k) + commonFactorParameterColumn C n₂ t), by
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
      change commonFactorFirstMultiplier C n₁ n₂ _ -
        commonFactorSecondMultiplier C n₁ n₂ _ = _
      simp only [commonFactorFirstMultiplier, commonFactorSecondMultiplier,
        commonFactorParameterColumn, ← map_add, quotientMultiplier_mk, ← map_sub]
      congr 1
      calc
        n₂ * (a * k + n₁ * t) - n₁ * (b * k + n₂ * t) =
            (a * n₂ - b * n₁) * k := by ring
        _ = k := by rw [hab, one_mul]⟩
  invFun p := Ideal.Quotient.mk C a * commonFactorReduce C n₂ p.val.2 -
    Ideal.Quotient.mk C b * commonFactorReduce C n₁ p.val.1
  left_inv t := by
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
    simp only [commonFactorParameterColumn, commonFactorReduce,
      ← map_add, quotientMultiplier_mk, one_mul, smul_eq_mul, ← map_mul, ← map_sub]
    congr 1
    calc
      a * (b * k + n₂ * t) - b * (a * k + n₁ * t) =
          (a * n₂ - b * n₁) * t := by ring
      _ = t := by rw [hab, one_mul]
  right_inv p := by
    obtain ⟨⟨x, y⟩, hp⟩ := p
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have herr : n₂ * x - n₁ * y - k ∈ commonFactorTotalIdeal C n₁ n₂ := by
      apply Ideal.Quotient.eq.mp
      simpa only [commonFactorFirstMultiplier, commonFactorSecondMultiplier,
        quotientMultiplier_mk, map_sub] using hp
    apply Subtype.ext
    apply Prod.ext
    · simp only [commonFactorReduce, commonFactorParameterColumn,
        quotientMultiplier_mk, one_mul, smul_eq_mul, ← map_mul, ← map_sub, ← map_add]
      apply Ideal.Quotient.eq.mpr
      have hmem := (commonFactorColumnIdeal C n₁).mul_mem_left (-a)
        (total_le_first C n₁ n₂ herr)
      convert hmem using 1
      calc
        a * k + n₁ * (a * y - b * x) - x =
          -a * (n₂ * x - n₁ * y - k) + (a * n₂ - b * n₁ - 1) * x := by ring
        _ = -a * (n₂ * x - n₁ * y - k) := by rw [hab]; ring
    · simp only [commonFactorReduce, commonFactorParameterColumn,
        quotientMultiplier_mk, one_mul, smul_eq_mul, ← map_mul, ← map_sub, ← map_add]
      apply Ideal.Quotient.eq.mpr
      have hmem := (commonFactorColumnIdeal C n₂).mul_mem_left (-b)
        (total_le_second C n₁ n₂ herr)
      convert hmem using 1
      calc
        b * k + n₂ * (a * y - b * x) - y =
          -b * (n₂ * x - n₁ * y - k) + (a * n₂ - b * n₁ - 1) * y := by ring
        _ = -b * (n₂ * x - n₁ * y - k) := by rw [hab]; ring

/-- Direct comparison with the genuine affine-correlation fibre modulo C.
No finite-cardinality or analytic hypothesis is needed for the bijection. -/
def commonFactorFullToAffineFibreEquiv (C : Ideal R) (n₁ n₂ a b k : R)
    (hab : a * n₂ - b * n₁ = 1) :
    commonFactorFullFibre C n₁ n₂ k ≃
      {p : (R ⧸ C) × (R ⧸ C) //
        Ideal.Quotient.mk C n₂ * p.1 - Ideal.Quotient.mk C n₁ * p.2 =
          Ideal.Quotient.mk C k} := by
  have hq : Ideal.Quotient.mk C a * Ideal.Quotient.mk C n₂ -
      Ideal.Quotient.mk C b * Ideal.Quotient.mk C n₁ = 1 := by
    rw [← map_mul, ← map_mul, ← map_sub, hab, map_one]
  exact (commonFactorFullFibreEquiv C n₁ n₂ a b k hab).symm.trans
    (affineCorrelationFibreEquiv (Ideal.Quotient.mk C n₁)
      (Ideal.Quotient.mk C n₂) (Ideal.Quotient.mk C a)
      (Ideal.Quotient.mk C b) hq (Ideal.Quotient.mk C k))

theorem commonFactorFullToAffineFibreEquiv_fst
    (C : Ideal R) (n₁ n₂ a b k : R) (hab : a * n₂ - b * n₁ = 1)
    (p : commonFactorFullFibre C n₁ n₂ k) :
    (commonFactorFullToAffineFibreEquiv C n₁ n₂ a b k hab p).val.1 =
      commonFactorReduce C n₁ p.val.1 := by
  obtain ⟨t, rfl⟩ := (commonFactorFullFibreEquiv C n₁ n₂ a b k hab).surjective p
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
  simp only [commonFactorFullToAffineFibreEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  change Ideal.Quotient.mk C (a * k) + Ideal.Quotient.mk C n₁ * Ideal.Quotient.mk C t =
    commonFactorReduce C n₁ (Ideal.Quotient.mk _ (a * k) +
      commonFactorParameterColumn C n₁ (Ideal.Quotient.mk C t))
  simp only [map_add, commonFactorParameterColumn, quotientMultiplier_mk,
    commonFactorReduce_mk, ← map_mul]

theorem commonFactorFullToAffineFibreEquiv_snd
    (C : Ideal R) (n₁ n₂ a b k : R) (hab : a * n₂ - b * n₁ = 1)
    (p : commonFactorFullFibre C n₁ n₂ k) :
    (commonFactorFullToAffineFibreEquiv C n₁ n₂ a b k hab p).val.2 =
      commonFactorReduce C n₂ p.val.2 := by
  obtain ⟨t, rfl⟩ := (commonFactorFullFibreEquiv C n₁ n₂ a b k hab).surjective p
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
  simp only [commonFactorFullToAffineFibreEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  change Ideal.Quotient.mk C (b * k) + Ideal.Quotient.mk C n₂ * Ideal.Quotient.mk C t =
    commonFactorReduce C n₂ (Ideal.Quotient.mk _ (b * k) +
      commonFactorParameterColumn C n₂ (Ideal.Quotient.mk C t))
  simp only [map_add, commonFactorParameterColumn, quotientMultiplier_mk,
    commonFactorReduce_mk, ← map_mul]

/-- The full congruence implies both genuine residual congruences. -/
theorem commonFactorFullFibre_residual_congruences
    (C : Ideal R) (n₁ n₂ k x y : R)
    (hp : commonFactorFirstMultiplier C n₁ n₂ (Ideal.Quotient.mk _ x) -
      commonFactorSecondMultiplier C n₁ n₂ (Ideal.Quotient.mk _ y) =
        Ideal.Quotient.mk _ k) :
    n₂ * x - k ∈ Ideal.span ({n₁} : Set R) ∧
      n₁ * y - (-k) ∈ Ideal.span ({n₂} : Set R) := by
  have herr : n₂ * x - n₁ * y - k ∈ commonFactorTotalIdeal C n₁ n₂ := by
    apply Ideal.Quotient.eq.mp
    simpa only [commonFactorFirstMultiplier, commonFactorSecondMultiplier,
      quotientMultiplier_mk, map_sub] using hp
  have h₁ : n₂ * x - n₁ * y - k ∈ Ideal.span ({n₁} : Set R) :=
    Ideal.mul_le_right (total_le_first C n₁ n₂ herr)
  have h₂ : n₂ * x - n₁ * y - k ∈ Ideal.span ({n₂} : Set R) :=
    Ideal.mul_le_right (total_le_second C n₁ n₂ herr)
  constructor
  · convert (Ideal.span ({n₁} : Set R)).add_mem h₁
      ((Ideal.span ({n₁} : Set R)).mul_mem_right y
        (Ideal.subset_span (Set.mem_singleton n₁))) using 1 <;> ring
  · convert (Ideal.span ({n₂} : Set R)).sub_mem
      ((Ideal.span ({n₂} : Set R)).mul_mem_right x
        (Ideal.subset_span (Set.mem_singleton n₂))) h₂ using 1 <;> ring

/-- The cancellation needed before calling the reduced fibre the original
principal-modulus F. This is separate from the arbitrary-ideal bijection. -/
theorem commonFactor_principal_cancel [IsDomain R] (c z d : R) (hc : c ≠ 0) :
    c * z ∈ Ideal.span ({c * d} : Set R) ↔ z ∈ Ideal.span ({d} : Set R) := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp h
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨t, ?_⟩
    apply mul_left_cancel₀ hc
    calc
      c * (t * d) = t * (c * d) := by ring
      _ = c * z := ht
  · intro h
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp h
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨t, ?_⟩
    calc
      t * (c * d) = c * (t * d) := by ring
      _ = c * z := by rw [ht]

theorem commonFactor_original_congruence_iff [IsDomain R]
    (c n₁ n₂ k x y : R) (hc : c ≠ 0) :
    (c * n₂) * x - (c * n₁) * y - c * k ∈
        Ideal.span ({(c * n₁) * (c * n₂)} : Set R) ↔
      n₂ * x - n₁ * y - k ∈ Ideal.span ({c * (n₁ * n₂)} : Set R) := by
  have hl : (c * n₂) * x - (c * n₁) * y - c * k =
      c * (n₂ * x - n₁ * y - k) := by ring
  have hr : (c * n₁) * (c * n₂) = c * (c * (n₁ * n₂)) := by ring
  rw [hl, hr]
  exact commonFactor_principal_cancel c _ _ hc
end HeckeGeneral.Arithmetic.PeriodicFourier
