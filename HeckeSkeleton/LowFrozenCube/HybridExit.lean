import HeckeSkeleton.LowFrozenCube.Assembly
import HeckeSkeleton.LowHybrid.Rows

/-!
# The frozen-cube exit is the literal normalized hybrid energy

This bridge uses the negative cubic exponent and the explicit square-root
normalization of the requested LOW-HYBRID expression. It assumes no energy
bound. The supported cube stays inside the sum throughout.
-/

namespace HeckeSkeleton.LowFrozenCube

open scoped BigOperators Classical
noncomputable section

variable {A : Type*} [CommMonoid A]

theorem hybridSeparatedRow_eq_normalizedRow
    (chi : A → A →* ℂ) (cop : A → A → Prop)
    (h6 : ∀ a b, (chi a b) ^ 6 = if cop a b then (1 : ℂ) else 0)
    (normI : A → ℝ) (a : A → ℂ) (beta : A → A → ℂ)
    (marks columns cubes : Finset A) (k : A) :
    hybridSeparatedRow chi cop (fun P => a P / (Real.sqrt (normI P) : ℂ))
      beta marks columns cubes k =
    HeckeSkeleton.LowHybrid.hybridRow (fun i j => chi i j) cop normI a beta
      marks columns cubes k := by
  unfold hybridSeparatedRow fullCubeInner HeckeSkeleton.LowHybrid.hybridRow
  simp_rw [symbol_zpow_neg_two chi cop h6]

/-- The actual normalized hybrid energy is the exact finite exit of the
frozen row. Both moving masks and the zero values of the inverse power are
retained. All coefficient and support data are fixed before the row varies. -/
theorem frozen_energy_eq_hybridEnergy
    (chi : A → A →* ℂ) (cop : A → A → Prop)
    (h6 : ∀ a b, (chi a b) ^ 6 = if cop a b then (1 : ℂ) else 0)
    (normI : A → ℝ) (rows marks columns : Finset A) (t : Finset (A × A))
    (split : A → A × A) (hsplit : ∀ q ∈ t, split (cubeProduct q) = q)
    (a : A → ℂ) (B : A → A → A → ℂ)
    (hPx : ∀ P ∈ marks, ∀ q ∈ t, cop P q.1)
    (rho : A → ℂ) (hrho : ∀ k ∈ rows, ‖rho k‖ = 1) :
    (∑ k ∈ rows, ‖rho k * frozenSeparatedRow chi cop
      (fun P => a P / (Real.sqrt (normI P) : ℂ)) B marks columns t k‖ ^ 2) =
      HeckeSkeleton.LowHybrid.hybridEnergy (fun i j => chi i j) cop normI
        a (fullCubeCoefficient split B) rows marks columns (t.image cubeProduct) := by
  rw [frozenSeparatedRow_energy_eq_hybrid chi cop h6 rows marks columns t split
    hsplit (fun P => a P / (Real.sqrt (normI P) : ℂ)) B hPx rho hrho]
  unfold HeckeSkeleton.LowHybrid.hybridEnergy
  apply Finset.sum_congr rfl
  intro k hk
  rw [hybridSeparatedRow_eq_normalizedRow chi cop h6 normI a]

#print axioms hybridSeparatedRow_eq_normalizedRow
#print axioms frozen_energy_eq_hybridEnergy

end
end HeckeSkeleton.LowFrozenCube
