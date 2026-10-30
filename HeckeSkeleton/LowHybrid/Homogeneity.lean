import HeckeSkeleton.LowHybrid.Rows
import HeckeSkeleton.LowHybrid.CommonTactics

/-!
# Arbitrary beta coefficient mass in the literal hybrid energy

The hybrid row is linear in beta, and its energy is homogeneous of degree
two. Consequently every uniform estimate for coefficients of norm at most
one extends to arbitrary coefficients with the exact squared coefficient
bound as a multiplicative factor. Empty supports and a zero coefficient
bound are included explicitly.
-/

namespace HeckeSkeleton.LowHybrid

open scoped BigOperators Classical
noncomputable section

variable {I : Type*} [CommMonoid I]

theorem hybridRow_beta_congr
    (symbol : I → I → ℂ) (cop : I → I → Prop) (normI : I → ℝ)
    (a : I → ℂ) (beta gamma : I → I → ℂ)
    (marks columns cubes : Finset I) (k : I)
    (hbeta : ∀ n ∈ columns, ∀ b ∈ cubes, beta n b = gamma n b) :
    hybridRow symbol cop normI a beta marks columns cubes k =
      hybridRow symbol cop normI a gamma marks columns cubes k := by
  unfold hybridRow
  apply Finset.sum_congr rfl
  intro P hP
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro b hb
  rw [hbeta n hn b hb]

theorem hybridRow_beta_mul
    (symbol : I → I → ℂ) (cop : I → I → Prop) (normI : I → ℝ)
    (a : I → ℂ) (beta : I → I → ℂ) (z : ℂ)
    (marks columns cubes : Finset I) (k : I) :
    hybridRow symbol cop normI a (fun n b => z * beta n b) marks columns cubes k =
      z * hybridRow symbol cop normI a beta marks columns cubes k := by
  unfold hybridRow
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  have hinner :
      (∑ n ∈ columns, ∑ b ∈ cubes, (z * beta n b) *
        (symbol k (n * b) ^ 3 * symbol P n ^ (-2 : ℤ) *
          (if cop P b then (1 : ℂ) else 0))) =
      z * (∑ n ∈ columns, ∑ b ∈ cubes, beta n b *
        (symbol k (n * b) ^ 3 * symbol P n ^ (-2 : ℤ) *
          (if cop P b then (1 : ℂ) else 0))) := by
    simp only [Finset.mul_sum, mul_assoc]
  rw [hinner]
  ring

theorem hybridEnergy_beta_mul
    (symbol : I → I → ℂ) (cop : I → I → Prop) (normI : I → ℝ)
    (a : I → ℂ) (beta : I → I → ℂ) (z : ℂ)
    (rows marks columns cubes : Finset I) :
    hybridEnergy symbol cop normI a (fun n b => z * beta n b) rows marks columns cubes =
      ‖z‖ ^ 2 * hybridEnergy symbol cop normI a beta rows marks columns cubes := by
  unfold hybridEnergy
  simp only [hybridRow_beta_mul, norm_mul, mul_pow, Finset.mul_sum]

theorem hybridEnergy_eq_zero_of_beta_zero
    (symbol : I → I → ℂ) (cop : I → I → Prop) (normI : I → ℝ)
    (a : I → ℂ) (beta : I → I → ℂ)
    (rows marks columns cubes : Finset I)
    (hbeta : ∀ n ∈ columns, ∀ b ∈ cubes, beta n b = 0) :
    hybridEnergy symbol cop normI a beta rows marks columns cubes = 0 := by
  unfold hybridEnergy
  apply Finset.sum_eq_zero
  intro k hk
  rw [hybridRow_beta_congr symbol cop normI a beta (fun _ _ => 0)
    marks columns cubes k hbeta]
  simp [hybridRow]

/-- Scale an arbitrary coefficient family by its uniform norm bound. The
unit-coefficient estimate is reusable without changing its constant. -/
theorem hybridEnergy_beta_bound_of_unit
    (symbol : I → I → ℂ) (cop : I → I → Prop) (normI : I → ℝ)
    (a : I → ℂ) (beta : I → I → ℂ)
    (rows marks columns cubes : Finset I) (U R : ℝ) (hU : 0 ≤ U)
    (hbeta : ∀ n ∈ columns, ∀ b ∈ cubes, ‖beta n b‖ ≤ U)
    (hunit : ∀ gamma : I → I → ℂ,
      (∀ n ∈ columns, ∀ b ∈ cubes, ‖gamma n b‖ ≤ 1) →
      hybridEnergy symbol cop normI a gamma rows marks columns cubes ≤ R) :
    hybridEnergy symbol cop normI a beta rows marks columns cubes ≤ U ^ 2 * R := by
  by_cases hUzero : U = 0
  · have hzero : ∀ n ∈ columns, ∀ b ∈ cubes, beta n b = 0 := by
      intro n hn b hb
      apply norm_eq_zero.mp
      exact le_antisymm (by simpa only [hUzero] using hbeta n hn b hb) (norm_nonneg _)
    rw [hybridEnergy_eq_zero_of_beta_zero symbol cop normI a beta
      rows marks columns cubes hzero, hUzero]
    simp
  · have hUpos : 0 < U := lt_of_le_of_ne hU (Ne.symm hUzero)
    have hUC : (U : ℂ) ≠ 0 := by exact_mod_cast hUzero
    let gamma : I → I → ℂ := fun n b => beta n b / (U : ℂ)
    have hgamma : ∀ n ∈ columns, ∀ b ∈ cubes, ‖gamma n b‖ ≤ 1 := by
      intro n hn b hb
      dsimp only [gamma]
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hU]
      exact (div_le_one hUpos).mpr (hbeta n hn b hb)
    have hscale : (fun n b => (U : ℂ) * gamma n b) = beta := by
      funext n b
      dsimp only [gamma]
      field_simp [hUC] <;> ring
    calc
      _ = hybridEnergy symbol cop normI a (fun n b => (U : ℂ) * gamma n b)
          rows marks columns cubes := by rw [hscale]
      _ = ‖(U : ℂ)‖ ^ 2 * hybridEnergy symbol cop normI a gamma
          rows marks columns cubes :=
        hybridEnergy_beta_mul symbol cop normI a gamma (U : ℂ) rows marks columns cubes
      _ ≤ _ := by
        rw [Complex.norm_real, Real.norm_of_nonneg hU]
        exact mul_le_mul_of_nonneg_left (hunit gamma hgamma) (sq_nonneg U)

/-- The exact coefficient-mass version: any upper bound for |beta|²
appears once in the energy estimate, including the zero-mass case. -/
theorem hybridEnergy_beta_squared_bound_of_unit
    (symbol : I → I → ℂ) (cop : I → I → Prop) (normI : I → ℝ)
    (a : I → ℂ) (beta : I → I → ℂ)
    (rows marks columns cubes : Finset I) (V R : ℝ) (hV : 0 ≤ V)
    (hbeta : ∀ n ∈ columns, ∀ b ∈ cubes, ‖beta n b‖ ^ 2 ≤ V)
    (hunit : ∀ gamma : I → I → ℂ,
      (∀ n ∈ columns, ∀ b ∈ cubes, ‖gamma n b‖ ≤ 1) →
      hybridEnergy symbol cop normI a gamma rows marks columns cubes ≤ R) :
    hybridEnergy symbol cop normI a beta rows marks columns cubes ≤ V * R := by
  have hroot := Real.sqrt_nonneg V
  have hsquare := Real.sq_sqrt hV
  have hbeta' : ∀ n ∈ columns, ∀ b ∈ cubes, ‖beta n b‖ ≤ Real.sqrt V := by
    intro n hn b hb
    have h := hbeta n hn b hb
    nlinarith [norm_nonneg (beta n b)]
  have h := hybridEnergy_beta_bound_of_unit symbol cop normI a beta rows marks columns cubes
    (Real.sqrt V) R hroot hbeta' hunit
  simpa only [hsquare] using h

/-- The actual maximum squared beta coefficient on its finite support;
the value is zero if either support is empty. -/
def betaSquaredMass (beta : I → I → ℂ) (columns cubes : Finset I) : ℝ :=
  (((columns ×ˢ cubes).sup (fun u : I × I => ‖beta u.1 u.2‖₊ ^ 2) : NNReal) : ℝ)

theorem betaSquaredMass_nonneg (beta : I → I → ℂ) (columns cubes : Finset I) :
    0 ≤ betaSquaredMass beta columns cubes :=
  NNReal.coe_nonneg _

theorem norm_sq_le_betaSquaredMass (beta : I → I → ℂ) (columns cubes : Finset I)
    (n : I) (hn : n ∈ columns) (b : I) (hb : b ∈ cubes) :
    ‖beta n b‖ ^ 2 ≤ betaSquaredMass beta columns cubes := by
  have h := Finset.le_sup (s := columns ×ˢ cubes) (b := (n, b))
    (f := fun u : I × I => ‖beta u.1 u.2‖₊ ^ 2)
    (Finset.mem_product.mpr ⟨hn, hb⟩)
  unfold betaSquaredMass
  exact_mod_cast h

@[simp] theorem betaSquaredMass_empty_columns (beta : I → I → ℂ) (cubes : Finset I) :
    betaSquaredMass beta ∅ cubes = 0 := by simp [betaSquaredMass]

@[simp] theorem betaSquaredMass_empty_cubes (beta : I → I → ℂ) (columns : Finset I) :
    betaSquaredMass beta columns ∅ = 0 := by simp [betaSquaredMass]

/-- The coefficient mass is constructed from beta itself, so this version
has no coefficient-size hypothesis. -/
theorem hybridEnergy_beta_mass_of_unit
    (symbol : I → I → ℂ) (cop : I → I → Prop) (normI : I → ℝ)
    (a : I → ℂ) (beta : I → I → ℂ)
    (rows marks columns cubes : Finset I) (R : ℝ)
    (hunit : ∀ gamma : I → I → ℂ,
      (∀ n ∈ columns, ∀ b ∈ cubes, ‖gamma n b‖ ≤ 1) →
      hybridEnergy symbol cop normI a gamma rows marks columns cubes ≤ R) :
    hybridEnergy symbol cop normI a beta rows marks columns cubes ≤
      betaSquaredMass beta columns cubes * R :=
  hybridEnergy_beta_squared_bound_of_unit symbol cop normI a beta rows marks columns cubes
    (betaSquaredMass beta columns cubes) R (betaSquaredMass_nonneg beta columns cubes)
    (norm_sq_le_betaSquaredMass beta columns cubes) hunit

#print axioms hybridRow_beta_mul
#print axioms hybridEnergy_beta_squared_bound_of_unit
#print axioms hybridEnergy_beta_mass_of_unit

end
end HeckeSkeleton.LowHybrid
