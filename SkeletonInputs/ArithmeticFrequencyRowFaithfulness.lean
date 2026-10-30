import ArithmeticSexticKummerFaithfulness
import SUnitPowerSaturation
import ArithmeticFrequencyRowRamification
import HeckeGeneral.Analysis.PrincipalGeneratorCalibration
import HeckeGeneral.Characters.InfinityPacket
import Mathlib.Tactic

/-!
Global principal-row detection for the actual arithmetic Kummer constructor.
Nonunit exterior ideals are handled by actual ramification. For unit-ideal
rows the allowed generator is an S-unit sixth power. Triviality of the
actual Artin/Kummer character gives a field sixth root of the chosen
integral representative; dividing by the two known sixth powers gives a
field root of the original unit sector. Power saturation of the original
S-unit group then makes that sector trivial in SixthUnitClasses.

No arbitrary row-character faithfulness hypothesis is assumed. Transport to
an arbitrary RowCharacterInput uses the separate global uniqueness theorem.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Arithmetic.RowFaithfulnessDraft
open HeckeGeneral.Characters HeckeGeneral.Characters.ArithmeticKummerDraft
open HeckeGeneral.Characters.ArithmeticKummerFaithfulness
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem principalFrequencyRow_of_arithmeticRowCharacter_eq_one
    (hAllowed : AllowedGeneratorInput K S P.arithmetic)
    (u : FrequencyRow K S) (hχ : arithmeticRowCharacter K S P u = 1) :
    principalFrequencyRow K S u := by
  have hI : u.ideal.val = 1 := by
    by_contra hI
    exact arithmeticRowCharacter_ne_one_of_ideal_ne_one K S P u hI hχ
  refine ⟨hI, ?_⟩
  obtain ⟨δ, hδ⟩ := AllowedGeneratorInput.generator_eq_sixth_power_of_ideal_eq_one
    K S P.arithmetic hAllowed u.ideal hI
  let b := arithmeticRowIntegralRepresentative K S P u
  obtain ⟨γ, hrep⟩ := b.property.2
  have htriv : arithmeticSexticKummerCharacter K P.arithmetic.embedding
      ⟨P.arithmetic.root6, (mem_primitiveRoots (by norm_num)).mpr P.arithmetic.primitive6⟩
      (GlobalClassFieldTheory.Reciprocity.nonzeroIntegralFieldUnit K b.val b.property.1) = 1 := hχ
  obtain ⟨x, hx⟩ := exists_field_sixthRoot_of_arithmeticSexticKummerCharacter_eq_one
    K P.arithmetic.embedding
      ⟨P.arithmetic.root6, (mem_primitiveRoots (by norm_num)).mpr P.arithmetic.primitive6⟩
      (GlobalClassFieldTheory.Reciprocity.nonzeroIntegralFieldUnit K b.val b.property.1) htriv
  change x ^ 6 = (b.val : K) at hx
  let εu : S.unit K := Quotient.out u.sector
  have hgen := congrArg (fun z : S.integer K =>
    (S.unitEquivUnitsInteger K γ).val ^ 6 *
      ((S.unitEquivUnitsInteger K εu).val * z)) hδ
  have hrepK := congrArg (fun t : S.integer K => (t : K)) (hrep.trans hgen)
  change (b.val : K) = ((γ : Kˣ) : K) ^ 6 *
    (((εu : Kˣ) : K) * ((δ : Kˣ) : K) ^ 6) at hrepK
  let c : K := ((γ : Kˣ) : K) * ((δ : Kˣ) : K)
  have hroot : (x / c) ^ 6 = ((εu : Kˣ) : K) := by
    rw [div_pow, hx, hrepK]
    dsimp [c]
    rw [mul_pow]
    field_simp [γ.val.ne_zero, δ.val.ne_zero] <;> ring
  obtain ⟨v, hv⟩ := exists_sUnit_root_of_field_power K S εu (x / c) 6 (by norm_num) hroot
  have hmem : Quotient.out u.sector ∈ (powMonoidHom 6 : S.unit K →* S.unit K).range :=
    ⟨v, hv⟩
  have hmk : QuotientGroup.mk' (powMonoidHom 6 : S.unit K →* S.unit K).range
      (Quotient.out u.sector) = 1 :=
    (QuotientGroup.eq_one_iff (Quotient.out u.sector)).mpr hmem
  exact (Quotient.out_eq u.sector).symm.trans hmk

theorem arithmeticRowCharacter_ne_one_of_not_principal
    (hAllowed : AllowedGeneratorInput K S P.arithmetic)
    (u : FrequencyRow K S) (hu : ¬ principalFrequencyRow K S u) :
    arithmeticRowCharacter K S P u ≠ 1 := by
  intro hχ
  exact hu (principalFrequencyRow_of_arithmeticRowCharacter_eq_one K S P hAllowed u hχ)

/-- This covers every nonprincipal row, not only sufficiently large rows.
Finite order forces any putative pure norm twist to have parameter zero. -/
theorem arithmeticRowCharacter_ne_normTwist_of_not_principal
    (hAllowed : AllowedGeneratorInput K S P.arithmetic)
    (u : FrequencyRow K S) (hu : ¬ principalFrequencyRow K S u) (t : ℝ) :
    arithmeticRowCharacter K S P u ≠ heckeNormTwist K t := by
  intro hχ
  let v : InfinitePlace K := Classical.choice inferInstance
  have hp := congrArg (heckeRadialParameter K v) hχ
  rw [heckeRadialParameter_finiteOrder K v (arithmeticRowCharacter_finiteOrder K S P u),
    heckeRadialParameter_normTwist] at hp
  have ht : t = 0 := by linarith
  have hone : arithmeticRowCharacter K S P u = 1 := by
    simpa only [ht, heckeNormTwist, normTwist_zero] using hχ
  exact arithmeticRowCharacter_ne_one_of_not_principal K S P hAllowed u hu hone

end HeckeGeneral.ThetaSkeleton.Physical
