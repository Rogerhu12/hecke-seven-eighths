module

public import Mathlib.NumberTheory.GaussSum
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Tactic

/-!
# Gauss bounds on an actual finite product of fields

An arbitrary primitive additive character is decomposed along the
coordinate embeddings.  Its coordinate characters are proved primitive.
The full finite sum is then factored by a ring equivalence; no CRT Gauss
identity or conductor estimate is assumed.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Classical ComplexConjugate

namespace HeckeSkeleton.Moments.EngineStep.FiniteProductGauss

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K : ι → Type*} [∀ i, Field (K i)] [∀ i, Fintype (K i)]

def coordinatePhase (ψ : AddChar (∀ i, K i) ℂ) (i : ι) : AddChar (K i) ℂ where
  toFun x := ψ (Pi.single i x)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    rw [Pi.single_add, AddChar.map_add_eq_mul]

private theorem phase_sum {R : Type*} [AddCommMonoid R]
    (ψ : AddChar R ℂ) (s : Finset ι) (x : ι → R) :
    ψ (∑ i ∈ s, x i) = ∏ i ∈ s, ψ (x i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, AddChar.map_add_eq_mul, ih, Finset.prod_insert hi]

theorem phase_product (ψ : AddChar (∀ i, K i) ℂ) (x : ∀ i, K i) :
    ψ x = ∏ i, coordinatePhase ψ i (x i) := by
  have hx : (∑ i, Pi.single i (x i)) = x := by
    ext i
    simp
  calc
    ψ x = ψ (∑ i, Pi.single i (x i)) := congrArg ψ hx.symm
    _ = _ := phase_sum ψ Finset.univ (fun i => Pi.single i (x i))

theorem coordinatePhase_primitive (ψ : AddChar (∀ i, K i) ℂ)
    (hψ : ψ.IsPrimitive) (i : ι) : (coordinatePhase ψ i).IsPrimitive := by
  apply AddChar.IsPrimitive.of_ne_one
  intro htriv
  have hi : (Pi.single i 1 : ∀ i, K i) ≠ 0 := by
    intro he
    have he' := congrArg (fun x : ∀ i, K i => x i) he
    simpa using he'
  apply hψ hi
  ext x
  have hm : (Pi.single i 1 : ∀ i, K i) * x = Pi.single i (x i) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Pi.single_eq_of_ne hji]
  have hv := congrArg (fun φ : AddChar (K i) ℂ => φ (x i)) htriv
  simpa only [AddChar.mulShift_apply, AddChar.one_apply, hm, coordinatePhase] using hv

theorem field_gauss_norm_sq {L : Type*} [Field L] [Fintype L]
    (ψ : AddChar L ℂ) (hψ : ψ.IsPrimitive)
    (χ : MulChar L ℂ) (hχ : χ ≠ 1) :
    ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card L : ℝ) := by
  have hh := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq] at hh
  have hr := congrArg Complex.re hh
  simpa [Complex.mul_conj', pow_two] using hr

theorem field_fourier_norm_sq_le {L : Type*} [Field L] [Fintype L]
    (ψ : AddChar L ℂ) (hψ : ψ.IsPrimitive)
    (χ : MulChar L ℂ) (hχ : χ ≠ 1) (h : L) :
    ‖∑ x : L, χ x * ψ (h * x)‖ ^ 2 ≤ (Fintype.card L : ℝ) := by
  by_cases hh : h = 0
  · simp only [hh, zero_mul, AddChar.map_zero_eq_one, mul_one,
      MulChar.sum_eq_zero_of_ne_one hχ, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    positivity
  · have hp := AddChar.IsPrimitive.of_ne_one (hψ hh)
    exact (field_gauss_norm_sq (ψ.mulShift h) hp χ hχ).le

section Transport

variable {R : Type*} [CommRing R] [Fintype R]

def pulledPhase (e : R ≃+* ∀ i, K i) (ψ : AddChar R ℂ) :
    AddChar (∀ i, K i) ℂ :=
  ψ.compAddMonoidHom e.symm.toAddMonoidHom

theorem pulledPhase_primitive (e : R ≃+* ∀ i, K i)
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    (pulledPhase e ψ).IsPrimitive := by
  intro a ha hh
  have hea : e.symm a ≠ 0 := by
    intro hz
    apply ha
    apply e.symm.injective
    simpa only [map_zero] using hz
  apply hψ hea
  ext b
  have hv := congrArg (fun φ : AddChar (∀ i, K i) ℂ => φ (e b)) hh
  change ψ (e.symm (a * e b)) = 1 at hv
  simpa only [map_mul, e.symm_apply_apply] using hv

theorem crt_gauss_factorization (e : R ≃+* ∀ i, K i)
    (ψ : AddChar R ℂ) (χ : ∀ i, MulChar (K i) ℂ) (h : R) :
    (∑ x : R, (∏ i, χ i (e x i)) * ψ (h * x)) =
      ∏ i, ∑ y : K i, χ i y *
        coordinatePhase (pulledPhase e ψ) i (e h i * y) := by
  have hphase (x : R) :
      ψ (h * x) = ∏ i, coordinatePhase (pulledPhase e ψ) i (e h i * e x i) := by
    have hs : pulledPhase e ψ (e (h * x)) = ψ (h * x) :=
      congrArg ψ (e.symm_apply_apply (h * x))
    have hp := hs.symm.trans (phase_product (pulledPhase e ψ) (e (h * x)))
    simpa only [map_mul, Pi.mul_apply] using hp
  calc
    _ = ∑ x : R, ∏ i, χ i (e x i) *
        coordinatePhase (pulledPhase e ψ) i (e h i * e x i) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [hphase, ← Finset.prod_mul_distrib]
    _ = ∑ x : ∀ i, K i, ∏ i, χ i (x i) *
        coordinatePhase (pulledPhase e ψ) i (e h i * x i) :=
      e.toEquiv.sum_comp _
    _ = _ := (Fintype.prod_sum _).symm

theorem crt_gauss_norm_sq_le (e : R ≃+* ∀ i, K i)
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (χ : ∀ i, MulChar (K i) ℂ) (hχ : ∀ i, χ i ≠ 1) (h : R) :
    ‖∑ x : R, (∏ i, χ i (e x i)) * ψ (h * x)‖ ^ 2 ≤
      (Fintype.card R : ℝ) := by
  rw [crt_gauss_factorization, norm_prod, ← Finset.prod_pow]
  calc
    _ ≤ ∏ i, (Fintype.card (K i) : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro i _
        positivity
      · intro i _
        exact field_fourier_norm_sq_le _ (coordinatePhase_primitive _
          (pulledPhase_primitive e ψ hψ) i) (χ i) (hχ i) (e h i)
    _ = (Fintype.card R : ℝ) := by
      have hc := Fintype.card_congr e.toEquiv
      rw [Fintype.card_pi] at hc
      exact_mod_cast hc.symm

theorem crt_gauss_norm_le_sqrt (e : R ≃+* ∀ i, K i)
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (χ : ∀ i, MulChar (K i) ℂ) (hχ : ∀ i, χ i ≠ 1) (h : R) :
    ‖∑ x : R, (∏ i, χ i (e x i)) * ψ (h * x)‖ ≤
      Real.sqrt (Fintype.card R) := by
  have hb := crt_gauss_norm_sq_le e ψ hψ χ hχ h
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ Fintype.card R by positivity)
  have hn := norm_nonneg (∑ x : R, (∏ i, χ i (e x i)) * ψ (h * x))
  have hr := Real.sqrt_nonneg (Fintype.card R : ℝ)
  nlinarith

end Transport
end HeckeSkeleton.Moments.EngineStep.FiniteProductGauss

#print axioms HeckeSkeleton.Moments.EngineStep.FiniteProductGauss.crt_gauss_factorization
#print axioms HeckeSkeleton.Moments.EngineStep.FiniteProductGauss.crt_gauss_norm_le_sqrt
