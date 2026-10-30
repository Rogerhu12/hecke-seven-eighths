import ThetaGlobal.GlobalIdealCoordinates
import DedekindZetaZeroFree.Theta.Digits.Exterior.FiniteRowProducts

/-!
# An auxiliary row with exactly the requested exterior digit places

The digit support is independent of the arithmetic row's multiplicities.
For an arbitrary finite exterior support T, use the fixed allowed generator
of its squarefree prime-set ideal.  No new arithmetic context, generator
recipe, or global identity is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GlobalSupportRow

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.ThetaBranch
open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]
  (A : SArithmeticData F) (G : AllowedRecipe A)

def row (T : Finset (ExteriorPrime A)) : ThetaReflectionData.Row A :=
  ⟨Classical.choose (G.generates (GlobalIdealCoordinates.primeSetIdeal A T)),
    (Classical.choose_spec (G.generates
      (GlobalIdealCoordinates.primeSetIdeal A T))).1.1⟩

theorem row_generates (T : Finset (ExteriorPrime A)) :
    A.Generates (GlobalIdealCoordinates.primeSetIdeal A T) (row A G T).val :=
  (Classical.choose_spec (G.generates
    (GlobalIdealCoordinates.primeSetIdeal A T))).1

theorem rowUnit_eq (T : Finset (ExteriorPrime A)) :
    ThetaReflectionData.rowUnit A (row A G T) =
      G.generator (GlobalIdealCoordinates.primeSetIdeal A T) := by
  apply Units.ext
  exact (Classical.choose_spec (G.generates
    (GlobalIdealCoordinates.primeSetIdeal A T))).2.symm

theorem mem_rowPrimes (T : Finset (ExteriorPrime A)) (p : ExteriorPrime A) :
    p.val ∈ ThetaDigitAverage.rowPrimes A (row A G T).val (row A G T).property ↔
      p ∈ T := by
  simp only [ThetaDigitAverage.rowPrimes, Set.Finite.mem_toFinset,
    ThetaDigitAverage.RowPrimes, Set.mem_setOf_eq, p.property,
    not_false_eq_true, true_and]
  rw [SIntegerLocalization.generator_valuation A.Sf
    (GlobalIdealCoordinates.primeSetIdeal A T).val
    (GlobalIdealCoordinates.primeSetIdeal A T).property.1
    (row A G T).val (row_generates A G T).1 (row_generates A G T).2 p.val p.property,
    ← WithZero.exp_zero, WithZero.exp_lt_exp]
  change -(GlobalIdealCoordinates.exponent A
    (GlobalIdealCoordinates.primeSetIdeal A T) p : ℤ) < 0 ↔ p ∈ T
  rw [GlobalIdealCoordinates.exponent_primeSetIdeal]
  by_cases hp : p ∈ T <;> simp [hp]

def primeEmbedding : ExteriorPrime A ↪ KPFinitePlace F :=
  ⟨Subtype.val, Subtype.val_injective⟩

theorem rowPrimes_eq (T : Finset (ExteriorPrime A)) :
    ThetaDigitAverage.rowPrimes A (row A G T).val (row A G T).property =
      T.map (primeEmbedding A) := by
  ext p
  by_cases hp : p ∈ A.Sf
  · have hn : p ∉ ThetaDigitAverage.rowPrimes A
        (row A G T).val (row A G T).property := by
      simp [ThetaDigitAverage.rowPrimes, ThetaDigitAverage.RowPrimes, hp]
    have hm : p ∉ T.map (primeEmbedding A) := by
      intro h
      obtain ⟨q, _, hq⟩ := Finset.mem_map.mp h
      exact q.property (by simpa [primeEmbedding] using hq.symm ▸ hp)
    simp only [hn, hm]
  · have hm : p ∈ T.map (primeEmbedding A) ↔ (⟨p, hp⟩ : ExteriorPrime A) ∈ T := by
      constructor
      · intro h
        obtain ⟨q, hq, he⟩ := Finset.mem_map.mp h
        have heq : q = ⟨p, hp⟩ := Subtype.ext he
        simpa only [heq] using hq
      · intro h
        exact Finset.mem_map.mpr ⟨⟨p, hp⟩, h, rfl⟩
    rw [hm]
    exact mem_rowPrimes A G T ⟨p, hp⟩

variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)

theorem exteriorRows_eq (T : Finset (ExteriorPrime R.A)) :
    OrbitExpansion.ExteriorDigits.exteriorRows R (row R.A R.probe.allowed T) = T := by
  ext p
  rw [OrbitExpansion.ExteriorDigits.mem_exteriorRows]
  exact mem_rowPrimes R.A R.probe.allowed T p

end ThetaGlobal.GlobalSupportRow
