import DedekindZetaZeroFree.Theta.Whittaker.ExteriorFrequencyBranchCoordinates

/-!
# The actual unit sector left after reconstructing exterior valuations

Equal exterior orders imply that the ratio is an S-unit.  Passing to
sixth powers gives exactly one sector in the recipe's stored unit
representatives.  This proves the remaining arithmetic step after the
numerical valuation reconstruction; it does not assume a global
frequency bijection or any reflection identity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.GlobalUnitCoordinates

open NumberField DedekindZetaZeroFree DedekindZetaZeroFree.ThetaBranch
open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]
  (A : SArithmeticData F) (U : UnitRepresentatives A)

def frequency (y : Fˣ) (ε : A.UnitQuotient) : ThetaReflectionData.Frequency A :=
  QuotientGroup.mk ((U.representative ε).val * y)

theorem frequency_injective (y : Fˣ) : Function.Injective (frequency A U y) := by
  intro ε δ h
  have hr := Quotient.exact h
  change QuotientGroup.leftRel (ThetaReflectionData.rationalGamma A)
    ((U.representative ε).val * y) ((U.representative δ).val * y) at hr
  rw [QuotientGroup.leftRel_apply] at hr
  have he : ((U.representative ε).val * y)⁻¹ * ((U.representative δ).val * y) =
      (U.representative ε).val⁻¹ * (U.representative δ).val := by
    simp [mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
  rw [he] at hr
  obtain ⟨u, hu, he⟩ := Subgroup.mem_map.mp hr
  have hh : (U.representative ε)⁻¹ * U.representative δ ∈ A.unitSixthPowers := by
    refine ⟨⟨u, hu⟩, ?_⟩
    apply Subtype.ext
    exact he
  have hq : (QuotientGroup.mk (U.representative ε) : A.UnitQuotient) =
      QuotientGroup.mk (U.representative δ) := by
    apply Quotient.sound
    change QuotientGroup.leftRel A.unitSixthPowers _ _
    rwa [QuotientGroup.leftRel_apply]
  simpa only [U.represents] using hq

/-- The representative is taken from the fixed `U`; no fresh choice of
unit representatives or allowed generators is made. -/
theorem exists_unit_sector (x y : Fˣ)
    (horders : ∀ p : ExteriorPrime A, order p.val x = order p.val y) :
    ∃ ε : A.UnitQuotient, frequency A U y ε = QuotientGroup.mk x := by
  let u : A.U := ⟨x / y, CanonicalCoordinateProof.ratio_mem_sunit A x y horders⟩
  let ε : A.UnitQuotient := QuotientGroup.mk u
  refine ⟨ε, ?_⟩
  have he : (QuotientGroup.mk (U.representative ε) : A.UnitQuotient) =
      QuotientGroup.mk u := U.represents ε
  have hr := Quotient.exact he
  change QuotientGroup.leftRel A.unitSixthPowers _ _ at hr
  rw [QuotientGroup.leftRel_apply] at hr
  obtain ⟨t, ht⟩ := hr
  have ht' : (U.representative ε).val⁻¹ * u.val ∈
      ThetaReflectionData.rationalGamma A := by
    apply Subgroup.mem_map.mpr
    exact ⟨t.val, t.property, congrArg Subtype.val ht⟩
  apply Quotient.sound
  change QuotientGroup.leftRel (ThetaReflectionData.rationalGamma A)
    ((U.representative ε).val * y) x
  rw [QuotientGroup.leftRel_apply]
  have hx : x = u.val * y := by simp [u]
  rw [hx]
  convert ht' using 1
  simp [mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]

theorem existsUnique_unit_sector (x y : Fˣ)
    (horders : ∀ p : ExteriorPrime A, order p.val x = order p.val y) :
    ∃! ε : A.UnitQuotient, frequency A U y ε = QuotientGroup.mk x := by
  obtain ⟨ε, hε⟩ := exists_unit_sector A U x y horders
  exact ⟨ε, hε, fun δ hδ => frequency_injective A U y (hδ.trans hε.symm)⟩

end ThetaGlobal.GlobalUnitCoordinates
