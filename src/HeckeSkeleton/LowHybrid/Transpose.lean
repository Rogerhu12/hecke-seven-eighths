import HeckeSkeleton.LowHybrid.SieveBounds

/-!
# Finite complex operator transposition

The quadratic sieve in the supplied project has denominator in its column.
The quadratic character in the hybrid row has denominator in its row.
Finite complex Hilbert-space duality reverses this orientation with the same
operator constant. No reciprocity hypothesis or additional analytic input is
used. The cubic sieve is left in its original orientation.
-/

namespace HeckeSkeleton.LowHybrid

open scoped BigOperators ComplexConjugate

noncomputable section

/-- Complex finite Cauchy, with unrestricted coefficients in both factors. -/
theorem finite_complex_sum_mul_sq_le {I : Type*}
    (s : Finset I) (x y : I → ℂ) :
    ‖∑ i ∈ s, x i * y i‖ ^ 2 ≤
      (∑ i ∈ s, ‖x i‖ ^ 2) * (∑ i ∈ s, ‖y i‖ ^ 2) := by
  have hn : ‖∑ i ∈ s, x i * y i‖ ≤ ∑ i ∈ s, ‖x i‖ * ‖y i‖ := by
    simpa only [norm_mul] using norm_sum_le s (fun i => x i * y i)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖x i‖) (fun i => ‖y i‖))

/-- A finite complex matrix and its transpose have the same squared
operator bound. The proof retains arbitrary complex coefficients throughout. -/
theorem finite_operator_bound_transpose {I J : Type*}
    (rows : Finset I) (columns : Finset J) (matrix : I → J → ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ z : J → ℂ,
      (∑ i ∈ rows, ‖∑ j ∈ columns, matrix i j * z j‖ ^ 2) ≤
        C * ∑ j ∈ columns, ‖z j‖ ^ 2)
    (x : I → ℂ) :
    (∑ j ∈ columns, ‖∑ i ∈ rows, x i * matrix i j‖ ^ 2) ≤
      C * ∑ i ∈ rows, ‖x i‖ ^ 2 := by
  classical
  let y : J → ℂ := fun j => ∑ i ∈ rows, x i * matrix i j
  let adj : I → ℂ := fun i => ∑ j ∈ columns, matrix i j * conj (y j)
  let E : ℝ := ∑ j ∈ columns, ‖y j‖ ^ 2
  let X : ℝ := ∑ i ∈ rows, ‖x i‖ ^ 2
  change E ≤ C * X
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hX : 0 ≤ X := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have heq : (E : ℂ) = ∑ i ∈ rows, x i * adj i := by
    calc
      (E : ℂ) = ∑ j ∈ columns, y j * conj (y j) := by
        dsimp only [E]
        push_cast
        apply Finset.sum_congr rfl
        intro j hj
        exact (Complex.mul_conj' (y j)).symm
      _ = ∑ j ∈ columns, ∑ i ∈ rows, x i * matrix i j * conj (y j) := by
        apply Finset.sum_congr rfl
        intro j hj
        change (∑ i ∈ rows, x i * matrix i j) * conj (y j) = _
        rw [Finset.sum_mul]
      _ = ∑ i ∈ rows, ∑ j ∈ columns, x i * matrix i j * conj (y j) :=
        Finset.sum_comm
      _ = ∑ i ∈ rows, x i * adj i := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp only [adj]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hadj : (∑ i ∈ rows, ‖adj i‖ ^ 2) ≤ C * E := by
    simpa only [adj, E, Complex.norm_conj] using hbound (fun j => conj (y j))
  have henergy : E ^ 2 ≤ X * (C * E) := by
    calc
      E ^ 2 = ‖(E : ℂ)‖ ^ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE]
      _ = ‖∑ i ∈ rows, x i * adj i‖ ^ 2 := by rw [heq]
      _ ≤ X * (∑ i ∈ rows, ‖adj i‖ ^ 2) :=
        finite_complex_sum_mul_sq_le rows x adj
      _ ≤ _ := mul_le_mul_of_nonneg_left hadj hX
  by_cases hzero : E = 0
  · rw [hzero]
    exact mul_nonneg hC hX
  · have hEpos : 0 < E := lt_of_le_of_ne hE (Ne.symm hzero)
    have hcancel : E * E ≤ (C * X) * E := by
      calc
        E * E = E ^ 2 := by ring
        _ ≤ X * (C * E) := henergy
        _ = (C * X) * E := by ring
    by_contra h
    have hlt : C * X < E := lt_of_not_ge h
    have hpos := mul_pos (sub_pos.mpr hlt) hEpos
    nlinarith

/-- The same quadratic sieve holds with the two symbol arguments exchanged.
The parameters X,Y are swapped before transposing the finite operator.
The symmetric quadratic sieve factor is therefore unchanged. -/
theorem quadratic_sieve_input_transpose {I : Type*}
    (normI : I → ℝ) (sf : I → Prop) (symbol : I → I → ℂ)
    (hq : QuadraticSieveInput normI sf symbol) :
    QuadraticSieveInput normI sf (fun a b => symbol b a) := by
  intro eps heps
  obtain ⟨C, hC, hoperator⟩ := hq eps heps
  refine ⟨C, hC, ?_⟩
  intro X Y hX hY rows columns hrows hcolumns a
  let bound : ℝ := C * (X * Y) ^ eps * (X + Y)
  have hbound : 0 ≤ bound := by
    dsimp only [bound]
    positivity
  have horiginal : ∀ z : I → ℂ,
      (∑ j ∈ columns, ‖∑ i ∈ rows, symbol i j ^ 3 * z i‖ ^ 2) ≤
        bound * ∑ i ∈ rows, ‖z i‖ ^ 2 := by
    intro z
    simpa only [bound, mul_comm, add_comm] using
      hoperator Y X hY hX columns rows hcolumns hrows z
  simpa only [bound] using
    finite_operator_bound_transpose columns rows (fun j i => symbol i j ^ 3)
      bound hbound horiginal a

#print axioms finite_complex_sum_mul_sq_le
#print axioms finite_operator_bound_transpose
#print axioms quadratic_sieve_input_transpose

end
end HeckeSkeleton.LowHybrid

