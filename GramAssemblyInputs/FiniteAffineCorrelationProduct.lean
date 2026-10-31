import FiniteAffineCorrelation
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Source-only, uncompiled. Genuine affine correlation under ring equivalences
and finite products. No coprimality, nonzero-frequency or nontrivial-ring
hypothesis is used, and no artificial extension is defined. -/
noncomputable section
namespace HeckeGeneral.Arithmetic.PeriodicFourier
open scoped Classical BigOperators ComplexConjugate

theorem affineCorrelation_ringEquiv
    {R T : Type*} [CommRing R] [CommRing T] [Fintype R] [Fintype T]
    (e : R ≃+* T) (f : T → ℂ) (n₁ n₂ k : R) :
    affineCorrelation (fun x => f (e x)) n₁ n₂ k =
      affineCorrelation f (e n₁) (e n₂) (e k) := by
  unfold affineCorrelation
  refine Fintype.sum_equiv (e.toEquiv.prodCongr e.toEquiv) _ _ (fun p => ?_)
  have he : e n₂ * e p.1 - e n₁ * e p.2 = e k ↔
      n₂ * p.1 - n₁ * p.2 = k := by
    rw [← map_mul, ← map_mul, ← map_sub, e.injective.eq_iff]
  change (if n₂ * p.1 - n₁ * p.2 = k then f (e p.1) * conj (f (e p.2)) else 0) =
    if e n₂ * e p.1 - e n₁ * e p.2 = e k then f (e p.1) * conj (f (e p.2)) else 0
  by_cases h : n₂ * p.1 - n₁ * p.2 = k
  · rw [if_pos h, if_pos (he.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (he.mp h'))]

private def affinePairPiEquiv {ι : Type*} {A : ι → Type*} :
    ((∀ i, A i) × (∀ i, A i)) ≃ (∀ i, A i × A i) where
  toFun p i := (p.1 i, p.2 i)
  invFun p := (fun i => (p i).1, fun i => (p i).2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem affineCorrelation_pi
    {ι : Type*} [Fintype ι] {A : ι → Type*}
    [∀ i, CommRing (A i)] [∀ i, Fintype (A i)]
    (f : ∀ i, A i → ℂ) (n₁ n₂ k : ∀ i, A i) :
    affineCorrelation (fun x => ∏ i, f i (x i)) n₁ n₂ k =
      ∏ i, affineCorrelation (f i) (n₁ i) (n₂ i) (k i) := by
  have hterm (p : (∀ i, A i) × (∀ i, A i)) :
      (if n₂ * p.1 - n₁ * p.2 = k then
        (∏ i, f i (p.1 i)) * conj (∏ i, f i (p.2 i)) else 0) =
      ∏ i, if n₂ i * p.1 i - n₁ i * p.2 i = k i then
        f i (p.1 i) * conj (f i (p.2 i)) else 0 := by
    by_cases h : ∀ i, n₂ i * p.1 i - n₁ i * p.2 i = k i
    · have hall : n₂ * p.1 - n₁ * p.2 = k := funext h
      simp [hall, h, map_prod, Finset.prod_mul_distrib]
    · have hall : ¬ n₂ * p.1 - n₁ * p.2 = k := by
        intro he
        apply h
        intro i
        exact congrFun he i
      obtain ⟨i, hi⟩ := not_forall.mp h
      rw [if_neg hall]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  unfold affineCorrelation
  simp_rw [hterm]
  calc
    _ = ∑ p : ∀ i, A i × A i,
        ∏ i, if n₂ i * (p i).1 - n₁ i * (p i).2 = k i then
          f i (p i).1 * conj (f i (p i).2) else 0 :=
      Fintype.sum_equiv affinePairPiEquiv _ _ (fun _ => rfl)
    _ = _ := (Fintype.prod_sum (fun i (q : A i × A i) =>
      if n₂ i * q.1 - n₁ i * q.2 = k i then f i q.1 * conj (f i q.2) else 0)).symm

/-- Direct CRT interface: supplying the actual ring equivalence suffices. -/
theorem affineCorrelation_ringEquiv_pi
    {R ι : Type*} [CommRing R] [Fintype R] [Fintype ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Fintype (A i)]
    (e : R ≃+* (∀ i, A i)) (f : ∀ i, A i → ℂ) (n₁ n₂ k : R) :
    affineCorrelation (fun x => ∏ i, f i (e x i)) n₁ n₂ k =
      ∏ i, affineCorrelation (f i) (e n₁ i) (e n₂ i) (e k i) := by
  exact (affineCorrelation_ringEquiv e (fun y : ∀ i, A i => ∏ i, f i (y i)) n₁ n₂ k).trans
    (affineCorrelation_pi f (e n₁) (e n₂) (e k))

end HeckeGeneral.Arithmetic.PeriodicFourier
