import RowCharacterCanonicalUniqueness
import ActualHighRowLRatio
import actualConductorTransfer

/-!
The original Euler provider's characters are forced by its existing
finite-order and whole-ideal coefficient-calibration fields. These consumers
apply the resulting global uniqueness theorem to that same provider.
No character identification, row-input equality, finite-fiber, or conductor
bound is supplied as an additional premise. The L-ratio statement retains
the original detector, heights, conductor scales and every quantifier.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.ActualCanonicalRowConsumers

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Bridge HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Arithmetic.ConductorNormDraft
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem rowCharacter_eq_arithmetic (P : ProbeData K S) (E : RowEulerData K S P)
    (u : FrequencyRow K S) :
    E.rows.character u = arithmeticRowCharacter K S P u :=
  rowCharacterInput_character_eq_arithmetic K S P E.rows u

/-- The identity on the original rows is an equivalence of the full fibers;
no ideal or unit sector is removed. -/
def rowCharacterFiberEquiv (P : ProbeData K S) (E : RowEulerData K S P)
    (χ : HeckeCharacter K) :
    {u : FrequencyRow K S // E.rows.character u = χ} ≃
      {u : FrequencyRow K S // arithmeticRowCharacter K S P u = χ} where
  toFun u := ⟨u.val, (rowCharacter_eq_arithmetic K S P E u.val).symm.trans u.property⟩
  invFun u := ⟨u.val, (rowCharacter_eq_arithmetic K S P E u.val).trans u.property⟩
  left_inv u := by apply Subtype.ext; rfl
  right_inv u := by apply Subtype.ext; rfl

theorem rowCharacter_fiber_finite (P : ProbeData K S) (E : RowEulerData K S P)
    (χ : HeckeCharacter K) :
    Finite {u : FrequencyRow K S // E.rows.character u = χ} :=
  HeckeSkeleton.ActualHighRowLRatio.rowCharacter_fiber_finite_of_actual_calibration
    K S P E (rowCharacter_eq_arithmetic K S P E) χ

theorem rowCharacter_fiber_card_le (P : ProbeData K S) (E : RowEulerData K S P)
    (χ : HeckeCharacter K) :
    Nat.card {u : FrequencyRow K S // E.rows.character u = χ} ≤
      Nat.card (SixthUnitClasses K S) := by
  calc
    Nat.card {u : FrequencyRow K S // E.rows.character u = χ} =
        Nat.card {u : FrequencyRow K S // arithmeticRowCharacter K S P u = χ} :=
      Nat.card_congr (rowCharacterFiberEquiv K S P E χ)
    _ ≤ Nat.card (SixthUnitClasses K S) := arithmeticRowCharacter_fiber_card_le K S P χ

/-- The exact previous high-row L-ratio conclusion for every original
provider, with its former character-identification premise now proved. -/
theorem exists_uniform_actual_high_row_LRatio_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K)) (hΘ : 1 ∈ Θ)
    (P : ProbeData K S) (E : RowEulerData K S P)
    {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000)
    (hesmall : e ≤ 1 / 10000) (hε : 0 < ε) :
    ∃ C Z₀ : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → ∀ u : FrequencyRow K S,
      Z ^ d ≤ frequencyRowNorm K S u → ∀ a H Hupper : ℝ,
      51 / 100 ≤ a → a ≤ 1 → 0 ≤ H → H + 3 / 2 ≤ Hupper →
      rowZeroBelow K S ψ Θ P E u Hupper (a + 2 * e) →
      ∀ s w : ℂ, s.re = a + 16 * e → w.re = 1 - a - 6 * e →
      |s.im| ≤ H → |w.im| ≤ H →
        ‖heckeContinuation K (E.rows.character u) w‖ *
          ‖(heckeContinuation K (ψ * conjugate (E.rows.character u)) s)⁻¹‖ ≤
            C * heckeConductorScale K (E.rows.character u) ^ (a - 1 / 2 + 6 * e) *
              heckeConductorScale K ((E.rows.character u)⁻¹) ^ ε *
              heckeConductorScale K (ψ * conjugate (E.rows.character u)) ^ ε *
              (2 + Hupper) ^
                (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) +
                  2 * ((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * ε) := by
  exact HeckeSkeleton.ActualHighRowLRatio.exists_uniform_actual_high_row_LRatio_bound
    K S hcomplex ψ Θ hΘ P E (rowCharacter_eq_arithmetic K S P E)
    he he' hesmall hε

theorem natural_radical_bound (P : ProbeData K S) (E : RowEulerData K S P)
    (u : FrequencyRow K S) :
    (finiteConductor K (E.rows.character u)).val.absNorm ≤
      sexticSConductorNormConstant K S * u.ideal.val.val.radical.absNorm :=
  HeckeGeneral.ThetaSkeleton.Physical.ActualConductorTransfer.natural_radical_bound_of_actual_calibration
    K S P E (rowCharacter_eq_arithmetic K S P E) u

/-- One constant is fixed from K and S before every original P, E and row. -/
theorem exists_fixed_real_radical_bound_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ProbeData K S) (E : RowEulerData K S P),
      ∀ u : FrequencyRow K S,
        ((finiteConductor K (E.rows.character u)).val.absNorm : ℝ) ≤
          C * (u.ideal.val.val.radical.absNorm : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := HeckeGeneral.ThetaSkeleton.Physical.ActualConductorTransfer.exists_fixed_real_radical_bound_constant K S
  exact ⟨C, hC, fun P E u => hbound P E (rowCharacter_eq_arithmetic K S P E) u⟩

theorem highRadicalBound_for_every_provider (P : ProbeData K S) (E : RowEulerData K S P) :
    HeckeGeneral.ThetaSkeleton.Physical.ActualConductorTransfer.HighRadicalBound K S P E :=
  HeckeGeneral.ThetaSkeleton.Physical.ActualConductorTransfer.highRadicalBound_of_actual_calibration
    K S P E (rowCharacter_eq_arithmetic K S P E)

end HeckeSkeleton.ActualCanonicalRowConsumers
