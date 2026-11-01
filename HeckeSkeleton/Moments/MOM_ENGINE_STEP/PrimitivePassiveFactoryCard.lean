import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassivePairCard
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActualCharacters

/-!
# Fixed constants for the actual passive factory labels

The constants precede every moving source and every analytic input.
The two occurrence bounds are read from the original slot embeddings,
while the two independent passive divisors and rectangle choices remain
in the actual label type.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep.PrimitivePassiveFactoryCard

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open CanonicalLiteralPassiveNormalizedFamily CanonicalLiteralPassiveLabelMass

variable (K : Type) [Field K] [NumberField K]

def directConstant (cap : ℕ) (columnBound ε : ℝ)
    (hcolumnBound : 0 ≤ columnBound) (hε : 0 < ε) : ℝ :=
  Classical.choose (direct_pair_card (K := K) cap columnBound ε hcolumnBound hε)

theorem directConstant_pos (cap : ℕ) (columnBound ε : ℝ)
    (hcolumnBound : 0 ≤ columnBound) (hε : 0 < ε) :
    0 < directConstant K cap columnBound ε hcolumnBound hε :=
  (Classical.choose_spec (direct_pair_card (K := K) cap columnBound ε hcolumnBound hε)).1

def poolConstant (cap : ℕ) (columnBound primeBound ε : ℝ)
    (hcolumnBound : 0 ≤ columnBound) (hprimeBound : 0 ≤ primeBound)
    (hε : 0 < ε) : ℝ :=
  Classical.choose (pool_pair_card (K := K) cap columnBound primeBound ε
    hcolumnBound hprimeBound hε)

theorem poolConstant_pos (cap : ℕ) (columnBound primeBound ε : ℝ)
    (hcolumnBound : 0 ≤ columnBound) (hprimeBound : 0 ≤ primeBound)
    (hε : 0 < ε) :
    0 < poolConstant K cap columnBound primeBound ε hcolumnBound hprimeBound hε :=
  (Classical.choose_spec (pool_pair_card (K := K) cap columnBound primeBound ε
    hcolumnBound hprimeBound hε)).1

variable {K}
variable {A : SArithmeticData K} {ω ψ : HeckeCharacter K}
variable {parent : MomentData K ω ψ} {k l : ℕ}
variable {leftAtoms : CanonicalLiteralRectangles.Atoms (K := K) k}
variable {rightAtoms : CanonicalLiteralRectangles.Atoms (K := K) l}
variable {left : leftAtoms.ProfileData} {right : rightAtoms.ProfileData}
variable {BL : ActualColumnAllocation K k} {BR : ActualColumnAllocation K l}

/-- The actual embeddings include all preceding extraction maps. No
cardinality estimate or analytic certificate is supplied. -/
theorem direct_bound (cap : ℕ) (columnBound ε : ℝ)
    (hcolumnBound : 0 ≤ columnBound) (hε : 0 < ε)
    (Z : ℝ) (hZ : 1 < Z) (D : Ideal (𝓞 K)) (hD : D ≠ 0)
    (hDN : (Ideal.absNorm D : ℝ) ≤ Z ^ columnBound)
    (leftSlots : OriginalSlotDictionary parent leftAtoms.length)
    (rightSlots : OriginalSlotDictionary parent rightAtoms.length)
    (hcap : parent.geometry.slotCount ≤ cap) :
    (Fintype.card (PairLabel (A := A) left right BL BR (firstMask D) (firstMask D)) : ℝ) ≤
      directConstant K cap columnBound ε hcolumnBound hε * Z ^ ε := by
  have hk : k ≤ parent.geometry.slotCount := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective leftSlots.index leftSlots.index.injective
  have hl : l ≤ parent.geometry.slotCount := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective rightSlots.index rightSlots.index.injective
  exact (Classical.choose_spec
    (direct_pair_card (K := K) cap columnBound ε hcolumnBound hε)).2
      Z hZ A D hD hDN k l leftAtoms rightAtoms left right BL BR
      (hk.trans hcap) (hl.trans hcap)

/-- The pool mask keeps the extra copy of the prime at valuation six.
The prime window and first common ideal pay their own factors. -/
theorem pool_bound (cap : ℕ) (columnBound primeBound ε : ℝ)
    (hcolumnBound : 0 ≤ columnBound) (hprimeBound : 0 ≤ primeBound)
    (hε : 0 < ε) (Z : ℝ) (hZ : 1 < Z) (D : Ideal (𝓞 K)) (hD : D ≠ 0)
    (hDN : (Ideal.absNorm D : ℝ) ≤ Z ^ columnBound)
    (p : ExteriorPrime A) (hp : (Ideal.absNorm p.val.asIdeal : ℝ) ≤ Z ^ primeBound)
    (e : AmplifierValuation)
    (leftSlots : OriginalSlotDictionary parent leftAtoms.length)
    (rightSlots : OriginalSlotDictionary parent rightAtoms.length)
    (hcap : parent.geometry.slotCount ≤ cap) :
    (Fintype.card (PairLabel (A := A) left right BL BR
      (poolMask D p e) (poolMask D p e)) : ℝ) ≤
      poolConstant K cap columnBound primeBound ε hcolumnBound hprimeBound hε * Z ^ ε := by
  have hk : k ≤ parent.geometry.slotCount := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective leftSlots.index leftSlots.index.injective
  have hl : l ≤ parent.geometry.slotCount := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective rightSlots.index rightSlots.index.injective
  exact (Classical.choose_spec (pool_pair_card (K := K) cap columnBound primeBound ε
    hcolumnBound hprimeBound hε)).2 Z hZ A D hD hDN p hp e k l
      leftAtoms rightAtoms left right BL BR (hk.trans hcap) (hl.trans hcap)

end HeckeSkeleton.Moments.EngineStep.PrimitivePassiveFactoryCard

#print axioms HeckeSkeleton.Moments.EngineStep.PrimitivePassiveFactoryCard.directConstant_pos
#print axioms HeckeSkeleton.Moments.EngineStep.PrimitivePassiveFactoryCard.poolConstant_pos
#print axioms HeckeSkeleton.Moments.EngineStep.PrimitivePassiveFactoryCard.direct_bound
#print axioms HeckeSkeleton.Moments.EngineStep.PrimitivePassiveFactoryCard.pool_bound
