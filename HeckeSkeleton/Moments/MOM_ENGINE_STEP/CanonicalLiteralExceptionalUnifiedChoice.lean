import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalPaidRightSource

set_option linter.unusedSectionVars false

/-!
# One original choice for all literal exceptional terminals

The original single-character volume primitive fixes one union of
orders, one height degree and one positive constant before any moving
source or Fourier mode. The left cancellation, right cancellation and
ordinary absolute estimates all use this same choice. Restriction of
the finite seminorm set applies to the existing model itself; no new
profile, source, allocation or divisor is introduced.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalUnifiedChoice

open NumberField DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open CanonicalLiteralExceptionalPaidSource CanonicalLiteralExceptionalPaidRightSource

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ψ : HeckeCharacter K} {theta : Finset (HeckeCharacter K)} {window : Set ℝ}
variable (primitive : VolumePrimitive ψ theta window)
variable (ε maskExponent : ℝ) (hε : 0 < ε) (hmask : 0 ≤ maskExponent)

local notation "leftOrders" => centeredOrders (A := A) (σ := σ) (η := η) (hS := hS)
  primitive ε maskExponent hε hmask
local notation "rightOrders" => CanonicalLiteralExceptionalPaidRightSource.rightOrders
  (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExponent hε hmask
local notation "ordinaryOrders" => CanonicalLiteralExceptionalPaidSource.ordinaryOrders
  (A := A) (σ := σ) (η := η) (hS := hS) primitive
local notation "leftOrder" => centeredOrder (A := A) (σ := σ) (η := η) (hS := hS)
  primitive ε maskExponent hε hmask
local notation "rightOrder" => CanonicalLiteralExceptionalPaidRightSource.rightOrder
  (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExponent hε hmask
local notation "leftConstant" => centeredConstant (A := A) (σ := σ) (η := η) (hS := hS)
  primitive ε maskExponent hε hmask
local notation "rightConstant" => CanonicalLiteralExceptionalPaidRightSource.rightConstant
  (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExponent hε hmask
local notation "ordinaryConstant" => CanonicalLiteralExceptionalPaidSource.ordinaryConstant
  (A := A) (σ := σ) (η := η) (hS := hS) primitive

/-- These orders are chosen entirely from the fixed primitive. -/
def orders : Finset (ℕ × ℕ) := (leftOrders ∪ rightOrders) ∪ ordinaryOrders

def heightOrder : ℕ := max leftOrder rightOrder

def constant : ℝ := leftConstant + rightConstant + ordinaryConstant

local notation "allOrders" => orders (A := A) (σ := σ) (η := η) (hS := hS)
  primitive ε maskExponent hε hmask
local notation "allOrder" => heightOrder (A := A) (σ := σ) (η := η) (hS := hS)
  primitive ε maskExponent hε hmask
local notation "allConstant" => constant (A := A) (σ := σ) (η := η) (hS := hS)
  primitive ε maskExponent hε hmask

theorem orders_contain :
    leftOrders ⊆ allOrders ∧ rightOrders ⊆ allOrders ∧ ordinaryOrders ⊆ allOrders := by
  sorry

theorem orders_zero : (0, 0) ∈ allOrders := by
  sorry

theorem heightOrders_le : leftOrder ≤ allOrder ∧ rightOrder ≤ allOrder := by
  sorry

theorem constant_pos : 0 < allConstant := by
  sorry

theorem constants_le :
    leftConstant ≤ allConstant ∧ rightConstant ≤ allConstant ∧
      ordinaryConstant ≤ allConstant := by
  sorry

/-- All three estimates hold for the same original representative. -/
theorem profile_bounds (W : 𝓢(ℝ, ℂ)) (amplitude : ℝ)
    (hW : (allOrders).sup (schwartzSeminormFamily ℂ ℝ ℂ) W ≤ amplitude) :
    (leftOrders).sup (schwartzSeminormFamily ℂ ℝ ℂ) W ≤ amplitude ∧
      (rightOrders).sup (schwartzSeminormFamily ℂ ℝ ℂ) W ≤ amplitude ∧
      (ordinaryOrders).sup (schwartzSeminormFamily ℂ ℝ ℂ) W ≤ amplitude := by
  sorry

/-- The atomic zero-order input is already present in the same set. -/
theorem zero_order_bound (W : 𝓢(ℝ, ℂ)) (amplitude : ℝ)
    (hW : (allOrders).sup (schwartzSeminormFamily ℂ ℝ ℂ) W ≤ amplitude) :
    SchwartzMap.seminorm ℂ 0 0 W ≤ amplitude := by
  sorry

/-- The same height degree and constant dominate the three original
terminal coefficients. This comparison does not change either side's
actual divisor loss or removed-slot sum. -/
theorem growth_le (height : ℝ) (hheight : 0 ≤ height) :
    leftConstant * (1 + height) ^ leftOrder ≤ allConstant * (1 + height) ^ allOrder ∧
      rightConstant * (1 + height) ^ rightOrder ≤ allConstant * (1 + height) ^ allOrder ∧
      ordinaryConstant ≤ allConstant * (1 + height) ^ allOrder := by
  sorry

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalUnifiedChoice

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalUnifiedChoice.orders_zero
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalUnifiedChoice.constant_pos
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalUnifiedChoice.profile_bounds
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalUnifiedChoice.growth_le
