import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalPaidRightSource

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
  exact ⟨Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left,
    Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left,
    Finset.subset_union_right⟩

theorem orders_zero : (0, 0) ∈ allOrders :=
  (orders_contain (A := A) (σ := σ) (η := η) (hS := hS)
    primitive ε maskExponent hε hmask).1
    (centeredOrders_zero (A := A) (σ := σ) (η := η) (hS := hS)
      primitive ε maskExponent hε hmask)

theorem heightOrders_le : leftOrder ≤ allOrder ∧ rightOrder ≤ allOrder :=
  ⟨le_max_left _ _, le_max_right _ _⟩

theorem constant_pos : 0 < allConstant :=
  add_pos (add_pos
    (centeredConstant_pos (A := A) (σ := σ) (η := η) (hS := hS)
      primitive ε maskExponent hε hmask)
    (CanonicalLiteralExceptionalPaidRightSource.rightConstant_pos
      (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExponent hε hmask))
    (ordinaryConstant_pos (A := A) (σ := σ) (η := η) (hS := hS) primitive)

theorem constants_le :
    leftConstant ≤ allConstant ∧ rightConstant ≤ allConstant ∧
      ordinaryConstant ≤ allConstant := by
  have hl := (centeredConstant_pos (A := A) (σ := σ) (η := η) (hS := hS)
    primitive ε maskExponent hε hmask).le
  have hr := (CanonicalLiteralExceptionalPaidRightSource.rightConstant_pos
    (A := A) (σ := σ) (η := η) (hS := hS) primitive ε maskExponent hε hmask).le
  have ho := (ordinaryConstant_pos (A := A) (σ := σ) (η := η) (hS := hS) primitive).le
  dsimp only [constant]
  constructor
  · linarith
  constructor <;> linarith

/-- All three estimates hold for the same original representative. -/
theorem profile_bounds (W : 𝓢(ℝ, ℂ)) (amplitude : ℝ)
    (hW : (allOrders).sup (schwartzSeminormFamily ℂ ℝ ℂ) W ≤ amplitude) :
    (leftOrders).sup (schwartzSeminormFamily ℂ ℝ ℂ) W ≤ amplitude ∧
      (rightOrders).sup (schwartzSeminormFamily ℂ ℝ ℂ) W ≤ amplitude ∧
      (ordinaryOrders).sup (schwartzSeminormFamily ℂ ℝ ℂ) W ≤ amplitude := by
  have hsub := orders_contain (A := A) (σ := σ) (η := η) (hS := hS)
    primitive ε maskExponent hε hmask
  have restrict (s : Finset (ℕ × ℕ)) (hs : s ⊆ allOrders) :
      s.sup (schwartzSeminormFamily ℂ ℝ ℂ) W ≤ amplitude :=
    (Seminorm.finset_sup_apply_le (apply_nonneg _ _)
      (fun p hp => Seminorm.le_finset_sup_apply (hs hp))).trans hW
  exact ⟨restrict _ hsub.1, restrict _ hsub.2.1, restrict _ hsub.2.2⟩

/-- The atomic zero-order input is already present in the same set. -/
theorem zero_order_bound (W : 𝓢(ℝ, ℂ)) (amplitude : ℝ)
    (hW : (allOrders).sup (schwartzSeminormFamily ℂ ℝ ℂ) W ≤ amplitude) :
    SchwartzMap.seminorm ℂ 0 0 W ≤ amplitude :=
  (Seminorm.le_finset_sup_apply
    (orders_zero (A := A) (σ := σ) (η := η) (hS := hS)
      primitive ε maskExponent hε hmask)).trans hW

/-- The same height degree and constant dominate the three original
terminal coefficients. This comparison does not change either side's
actual divisor loss or removed-slot sum. -/
theorem growth_le (height : ℝ) (hheight : 0 ≤ height) :
    leftConstant * (1 + height) ^ leftOrder ≤ allConstant * (1 + height) ^ allOrder ∧
      rightConstant * (1 + height) ^ rightOrder ≤ allConstant * (1 + height) ^ allOrder ∧
      ordinaryConstant ≤ allConstant * (1 + height) ^ allOrder := by
  have hc := constants_le (A := A) (σ := σ) (η := η) (hS := hS)
    primitive ε maskExponent hε hmask
  have ho := heightOrders_le (A := A) (σ := σ) (η := η) (hS := hS)
    primitive ε maskExponent hε hmask
  have hC := (constant_pos (A := A) (σ := σ) (η := η) (hS := hS)
    primitive ε maskExponent hε hmask).le
  have hbase : 1 ≤ 1 + height := le_add_of_nonneg_right hheight
  have hpower : 1 ≤ (1 + height) ^ allOrder := by
    simpa only [pow_zero] using pow_le_pow_right₀ hbase (Nat.zero_le allOrder)
  refine ⟨mul_le_mul hc.1 (pow_le_pow_right₀ hbase ho.1) (by positivity) hC,
    mul_le_mul hc.2.1 (pow_le_pow_right₀ hbase ho.2) (by positivity) hC, ?_⟩
  exact hc.2.2.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpower hC)

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalUnifiedChoice

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalUnifiedChoice.orders_zero
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalUnifiedChoice.constant_pos
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalUnifiedChoice.profile_bounds
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalUnifiedChoice.growth_le
