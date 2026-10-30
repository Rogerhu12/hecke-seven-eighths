import HeckeSkeleton.HighBinSupport.ActualGaussPhases

/-!
The actual prime coefficient can vanish at a ramified target prime.  The
finite Gauss table therefore needs the contractive case, including θ=0,
and must not impose an unramifiedness assumption merely to prove a bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HighBin.ActualGaussPhases

open HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds

variable {F : Type*} [Field F] [Fintype F]

/-- Actual finite Gauss phases with a possibly zero theta coefficient.
All coefficient bounds follow from finite-field Gauss orthogonality and
the unitary-character bound ‖θ‖≤1. -/
def contractivePhaseData (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (θ : ℂ) (hθ : ‖θ‖ ≤ 1)
    (u : Fˣ) : PhaseData := by
  let B := phaseData χ hχ ψ hψ 1 (by simp) u
  have hp (n : ℕ) : ‖θ ^ n‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg θ) hθ
  have hm (n : ℕ) (c : ℂ) (hc : ‖c‖ ≤ 1) : ‖θ ^ n * c‖ ≤ 1 := by
    rw [norm_mul]
    exact mul_le_one₀ (hp n) (norm_nonneg _) hc
  refine {
    eta := θ * B.eta
    alpha := θ ^ 3 * B.alpha
    c2 := θ ^ 3 * B.c2
    c31 := θ ^ 3 * B.c31
    c32 := θ ^ 4 * B.c32
    c4 := θ ^ 4 * B.c4
    eta_bound := ?_
    alpha_bound := hm 3 _ B.alpha_bound
    c2_bound := hm 3 _ B.c2_bound
    c31_bound := hm 3 _ B.c31_bound
    c32_bound := hm 4 _ B.c32_bound
    c4_bound := hm 4 _ B.c4_bound }
  simpa only [pow_one] using hm 1 _ B.eta_bound

/-- With norm-one θ, this is literally the earlier table. Thus the new
construction extends it without selecting replacement values at θ=0. -/
theorem contractivePhaseData_eq_phaseData
    (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (θ : ℂ) (hθ : ‖θ‖ = 1)
    (u : Fˣ) :
    contractivePhaseData χ hχ ψ hψ θ hθ.le u = phaseData χ hχ ψ hψ θ hθ u := by
  simp only [contractivePhaseData, phaseData]
  congr 1 <;> ring

#print axioms contractivePhaseData
#print axioms contractivePhaseData_eq_phaseData

end HighBin.ActualGaussPhases
