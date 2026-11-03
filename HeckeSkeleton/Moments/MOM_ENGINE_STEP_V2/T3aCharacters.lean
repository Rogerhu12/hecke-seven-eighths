import HeckeGeneral.Analysis.DecomposedZeroSlotMomentData
import ArithmeticFrequencyRowCharacterFibers
import RowCharacterCanonicalUniqueness

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Sixth-free bases are detected by the actual finite row character

The fixed multiplier may be any Hecke character. Equality of the actual
complete row characters detects the complete sixth-free ideal, by the
proved local Kummer character formula. No injectivity of chosen generators
or of unit sectors is assumed.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3a

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (R : RowCharacterInput K S P)

theorem sixthBase_eq_of_completeCharacter_eq
    (I J : ExteriorIdeal K S) (u v : SixthUnitClasses K S)
    (hχ : completeIdealRowCharacter K S P R u I.val =
      completeIdealRowCharacter K S P R v J.val) :
    sixthPowerFreePart I.val = sixthPowerFreePart J.val := by
  simp only [completeIdealRowCharacter_exterior,
    rowCharacterInput_character_eq_arithmetic] at hχ
  have he := arithmeticRowCharacter_ideal_eq_of_eq K S P
    (decomposedFrequencyRow K S I u) (decomposedFrequencyRow K S J v) hχ
  exact congrArg (fun I : ExteriorIdeal K S => I.val) he

/-- A common finite-character multiplier does not create additional
sixth-free bases in an exceptional theta sector. -/
theorem sixthBases_card_le_theta {H : Type*} (rows : Finset H)
    (I : H → ExteriorIdeal K S) (sector : H → SixthUnitClasses K S)
    (preχ : HeckeCharacter K) (theta : Finset (HeckeCharacter K))
    (hmem : ∀ h ∈ rows,
      preχ * completeIdealRowCharacter K S P R (sector h) (I h).val ∈ theta) :
    (rows.image (fun h => sixthPowerFreePart (I h).val)).card ≤ theta.card := by
  let bases := rows.image (fun h => sixthPowerFreePart (I h).val)
  have hexists (b : bases) : ∃ h ∈ rows, sixthPowerFreePart (I h).val = b.val :=
    Finset.mem_image.mp b.property
  choose representative hrepresentative hbase using hexists
  let sectorMap : bases → theta := fun b =>
    ⟨preχ * completeIdealRowCharacter K S P R
      (sector (representative b)) (I (representative b)).val,
      hmem _ (hrepresentative b)⟩
  have hinj : Function.Injective sectorMap := by
    intro b b' he
    have hχ : completeIdealRowCharacter K S P R
        (sector (representative b)) (I (representative b)).val =
        completeIdealRowCharacter K S P R
          (sector (representative b')) (I (representative b')).val :=
      mul_left_cancel (congrArg (fun t : theta => t.val) he)
    have hideal := sixthBase_eq_of_completeCharacter_eq S P R
      (I (representative b)) (I (representative b'))
      (sector (representative b)) (sector (representative b')) hχ
    exact Subtype.ext ((hbase b).symm.trans (hideal.trans (hbase b')))
  have hc := Nat.card_le_card_of_injective sectorMap hinj
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hc

/-- The blueprint's explicit finite unit-sector allowance is retained;
the preceding injection in fact gives the stronger theta-only bound. -/
theorem sixthBases_card_le_theta_unitSectors {H : Type*} (rows : Finset H)
    (I : H → ExteriorIdeal K S) (sector : H → SixthUnitClasses K S)
    (preχ : HeckeCharacter K) (theta : Finset (HeckeCharacter K))
    (hmem : ∀ h ∈ rows,
      preχ * completeIdealRowCharacter K S P R (sector h) (I h).val ∈ theta) :
    (rows.image (fun h => sixthPowerFreePart (I h).val)).card ≤
      theta.card * Nat.card (SixthUnitClasses K S) := by
  have hsector : 1 ≤ Nat.card (SixthUnitClasses K S) := by
    have hinj : Function.Injective (fun _ : PUnit.{1} => (1 : SixthUnitClasses K S)) := by
      intro a b _
      cases a
      cases b
      rfl
    simpa using Nat.card_le_card_of_injective
      (fun _ : PUnit.{1} => (1 : SixthUnitClasses K S)) hinj
  exact (sixthBases_card_le_theta S P R rows I sector preχ theta hmem).trans
    (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left theta.card hsector)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3a

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3a.sixthBases_card_le_theta
