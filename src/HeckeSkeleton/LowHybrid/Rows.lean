import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The literal normalized hybrid row

The coefficient signatures enforce exactly the two independence conditions:
`a` has only a mark argument, and `beta` only squarefree and cube arguments.
The two moving collision masks remain explicit. The definition specializes
to the exterior-ideal expression after supplying the natural multiplication
and the allowed-generator symbol.
-/

namespace HeckeSkeleton.LowHybrid

open scoped BigOperators Classical
noncomputable section

variable {I : Type*} [CommMonoid I]

def hybridRow (symbol : I → I → ℂ) (cop : I → I → Prop)
    (normI : I → ℝ) (a : I → ℂ) (beta : I → I → ℂ)
    (marks columns cubes : Finset I) (k : I) : ℂ :=
  ∑ P ∈ marks, (a P / (Real.sqrt (normI P) : ℂ)) *
    (if cop P k then (1 : ℂ) else 0) *
    ∑ n ∈ columns, ∑ b ∈ cubes, beta n b *
      (symbol k (n * b) ^ 3 * symbol P n ^ (-2 : ℤ) *
        (if cop P b then (1 : ℂ) else 0))

def hybridEnergy (symbol : I → I → ℂ) (cop : I → I → Prop)
    (normI : I → ℝ) (a : I → ℂ) (beta : I → I → ℂ)
    (rows marks columns cubes : Finset I) : ℝ :=
  ∑ k ∈ rows, ‖hybridRow symbol cop normI a beta marks columns cubes k‖ ^ 2

theorem hybridEnergy_nonneg (symbol : I → I → ℂ) (cop : I → I → Prop)
    (normI : I → ℝ) (a : I → ℂ) (beta : I → I → ℂ)
    (rows marks columns cubes : Finset I) :
    0 ≤ hybridEnergy symbol cop normI a beta rows marks columns cubes :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

end
end HeckeSkeleton.LowHybrid
