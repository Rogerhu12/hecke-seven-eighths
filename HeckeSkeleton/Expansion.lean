import HeckeSkeleton.HighBin

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton
open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open scoped BigOperators
variable (K : Type) [Field K] [NumberField K]
variable (c : TargetContext K)

-- OBLIGATION EX-HEIGHT-BUDGET | revised Proposition 6.3, §8 (pp.41–42,49–51).
-- Internal degree and ceiling are selected before tau or the external tail order.
def expansionBudget (c : TargetContext K) : {b : ℝ × ℝ // 0 ≤ b.1 ∧ 0 < b.2} := by
  sorry

-- OBLIGATION EX-CUTOFFS | revised Proposition 6.3, §8 (pp.41–42,49–51).
-- One constant/threshold for the complete moving label and contour family.
def expansionCutoffs (c : TargetContext K) (τ : ℝ) : {b : ℝ × ℝ // 2 ≤ b.1 ∧ 0 ≤ b.2} := by
  sorry

-- OBLIGATION EX-IDENTITY | revised Proposition 6.3, §7 (pp.41–49).
-- Blocks are the shifted fixed-bin contributions. The whole-bin contour
-- differences are part of this SAME expansion's tail, before label splitting.
theorem expansion_identity (τ Z : ℝ)
    (hτ : 0 < τ) (hceiling : τ ≤ (expansionBudget K c).val.2)
    (hZ : (expansionCutoffs K c τ).val.1 ≤ Z) :
    (targetData K c).probeFunction (targetCharacter K c) Z -
      (targetData K c).signal (targetCharacter K c) Z =
    (highExpansion K c Z (Z ^ τ)).principal + (highExpansion K c Z (Z ^ τ)).small +
      (highExpansion K c Z (Z ^ τ)).large +
      (∑ b, ((highExpansion K c Z (Z ^ τ)).block b).value) +
      (highExpansion K c Z (Z ^ τ)).tail := by
  sorry

-- OBLIGATION EX-PRINCIPAL | revised Proposition 6.3, §7 (pp.41–49).
theorem expansion_principal (τ Z : ℝ)
    (hτ : 0 < τ) (hceiling : τ ≤ (expansionBudget K c).val.2)
    (hZ : (expansionCutoffs K c τ).val.1 ≤ Z) :
    ‖(highExpansion K c Z (Z ^ τ)).principal‖ ≤
    (expansionCutoffs K c τ).val.2 *
      (Z ^ (c.family.B - 11 / 16 - 23 / 960 + c.lamB) +
       Z ^ (c.family.B - 11 / 16 - 13 / 9600 + c.lamB) +
       Z ^ (c.family.B - 11 / 16 - principalSlotSaving c.geometry + c.lamB)) *
      (1 + Z ^ τ) ^ (expansionBudget K c).val.1 := by
  sorry

-- OBLIGATION EX-SMALL | revised Proposition 6.3, §7 (pp.41–49).
theorem expansion_small (τ Z : ℝ)
    (hτ : 0 < τ) (hceiling : τ ≤ (expansionBudget K c).val.2)
    (hZ : (expansionCutoffs K c τ).val.1 ≤ Z) :
    ‖(highExpansion K c Z (Z ^ τ)).small‖ ≤
    (expansionCutoffs K c τ).val.2 * Z ^ (c.family.B - 11 / 16 - 1 / 50 + c.lamB) *
      (1 + Z ^ τ) ^ (expansionBudget K c).val.1 := by
  sorry

-- OBLIGATION EX-LARGE | revised Proposition 6.3, §7 (pp.41–49).
theorem expansion_large (τ Z : ℝ)
    (hτ : 0 < τ) (hceiling : τ ≤ (expansionBudget K c).val.2)
    (hZ : (expansionCutoffs K c τ).val.1 ≤ Z) :
    ‖(highExpansion K c Z (Z ^ τ)).large‖ ≤
    (expansionCutoffs K c τ).val.2 * Z ^ (c.family.B - 11 / 16 - 63 / 800 + c.lamB) *
      (1 + Z ^ τ) ^ (expansionBudget K c).val.1 := by
  sorry

-- OBLIGATION EX-BLOCK-COUNT | revised Proposition 6.3, §7 (pp.41–49).
theorem expansion_blockCount (τ Z : ℝ)
    (hτ : 0 < τ) (hceiling : τ ≤ (expansionBudget K c).val.2)
    (hZ : (expansionCutoffs K c τ).val.1 ≤ Z) :
    ((highExpansion K c Z (Z ^ τ)).blockCount : ℝ) ≤
    (expansionCutoffs K c τ).val.2 * Z ^ c.lamB := by
  sorry

-- OBLIGATION EX-DETECTOR-WITNESSES | revised Proposition 6.3, §7 (pp.41–49).
theorem expansion_blocks (τ Z : ℝ)
    (hτ : 0 < τ) (hceiling : τ ≤ (expansionBudget K c).val.2)
    (hZ : (expansionCutoffs K c τ).val.1 ≤ Z) :
    ∀ b, BlockSource c.geometry ((highExpansion K c Z (Z ^ τ)).block b)
    c.family.B c.family.lamA (expansionCutoffs K c τ).val.2 Z := by
  sorry

-- OBLIGATION EX-TAIL | revised Proposition 6.3, §8 (pp.41–42,49–51).
-- Arbitrary external tail order, AFTER the internal height budget.
theorem expansion_tail
    (hmove : HighBoundaryControl K c (actualHighPresentation K c)) :
    PowerHeightTailBound (fun Z T₁ => (highExpansion K c Z T₁).tail) := by
  sorry

theorem expansionSource :
    ∃ A ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ ceiling → ∃ Z₀ k : ℝ, 2 ≤ Z₀ ∧ 0 ≤ k ∧
        ∀ Z : ℝ, Z₀ ≤ Z → ExpansionSource c.geometry (targetCharacter K c)
          (targetData K c) c.family.B c.family.lamA c.lamB k A Z (Z ^ τ) := by
  refine ⟨(expansionBudget K c).val.1, (expansionBudget K c).val.2,
    (expansionBudget K c).property.1, (expansionBudget K c).property.2, ?_⟩
  intro τ hτ hc
  refine ⟨(expansionCutoffs K c τ).val.1, (expansionCutoffs K c τ).val.2,
    (expansionCutoffs K c τ).property.1, (expansionCutoffs K c τ).property.2, ?_⟩
  intro Z hZ
  exact ⟨expansion_identity K c τ Z hτ hc hZ,
    expansion_principal K c τ Z hτ hc hZ,
    expansion_small K c τ Z hτ hc hZ,
    expansion_large K c τ Z hτ hc hZ,
    expansion_blockCount K c τ Z hτ hc hZ,
    expansion_blocks K c τ Z hτ hc hZ⟩

end HeckeSkeleton
