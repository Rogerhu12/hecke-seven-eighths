import DiscreteCompactPowerRange
import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.FinitePlaceCompletionInstances
import ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitStructure
import ValuedFieldTheory.LocalField.DiscreteValuationField.PadicPowerIndex
import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.LocallyConstant.Basic

/-!
UNCOMPILED / native 0. Deep principal units in the actual finite completion
are sixth powers. The topology used by the structure theorem is explicitly
identified with the original completion topology; no topology comparison,
power-index finiteness, openness, or depth assertion is a mathematical input.

The local-field structure and power-index APIs are from CFT commit
2eb22d6485af45f29c5219de6c49f196a61c4f49 (Naganori Yamaguchi,
Apache 2.0). This file is a new consumer, not a copy of those proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped NumberField ValuativeRel
open NumberField IsDedekindDomain
open HeckeGeneral.Analysis.DiscreteCompactPowerRangeDraft
open LocalFieldTheory.DiscreteValuationField.LocalField

namespace HeckeGeneral.Arithmetic.ActualAdicSixthPowerDraft

variable (K : Type) [Field K] [NumberField K]
variable (v : HeightOneSpectrum (𝓞 K))

/-- The original higher units, defined by reduction in the ACTUAL completion
integer ring, with no change of valuation relation or topology. -/
def adicPrincipalUnits (n : ℕ) : Subgroup (v.adicCompletion K)ˣ :=
  RayClass.localHigherUnitGroup v n

/-- The structure theorem's valuation topology is the original uniform topology. -/
theorem adicCompletion_uniformSpace_eq_mk :
    (inferInstance : UniformSpace (v.adicCompletion K)) =
      (Valued.mk' (Valued.v :
        Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)))).toUniformSpace := by
  exact Valued.toUniformSpace_eq (v.adicCompletion K) (WithZero (Multiplicative ℤ))

/-- Both the finite index and the closedness are obtained from the actual
discrete-times-compact local-field structure. No primitive root is needed. -/
theorem sixthPowerRange_finite_and_closed :
    Finite ((v.adicCompletion K)ˣ ⧸
      (powMonoidHom 6 : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range) ∧
    IsClosed ((powMonoidHom 6 :
      (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range :
        Set (v.adicCompletion K)ˣ) := by
  let E := v.adicCompletion K
  let ν : Valuation E (WithZero (Multiplicative ℤ)) := Valued.v
  have ht : (inferInstance : TopologicalSpace E) =
      (Valued.mk' ν).toTopologicalSpace :=
    congrArg (fun u => @UniformSpace.toTopologicalSpace E u)
      (adicCompletion_uniformSpace_eq_mk K v)
  have hT2original : @T2Space Eˣ
      (@Units.instTopologicalSpaceUnits E (inferInstance : TopologicalSpace E)
        (inferInstance : Monoid E)) := inferInstance
  have hm :
      Finite (Eˣ ⧸ (powMonoidHom 6 : Eˣ →* Eˣ).range) ∧
        @IsClosed Eˣ
          (@Units.instTopologicalSpaceUnits E (Valued.mk' ν).toTopologicalSpace
            (inferInstance : Monoid E))
          ((powMonoidHom 6 : Eˣ →* Eˣ).range : Set Eˣ) := by
    let F := ofWithZeroValuation ν
    letI : MixedWithZeroValuationContext ν := mixedWithZeroValuationContext ν
    letI : Valued E (WithZero (Multiplicative ℤ)) := Valued.mk' ν
    letI : TopologicalSpace Eˣ :=
      @Units.instTopologicalSpaceUnits E (Valued.mk' ν).toTopologicalSpace
        (inferInstance : Monoid E)
    letI : T2Space Eˣ := by
      change @T2Space Eˣ
        (@Units.instTopologicalSpaceUnits E (Valued.mk' ν).toTopologicalSpace
          (inferInstance : Monoid E))
      rw [← ht]
      exact hT2original
    let d := Module.finrank ℚ_[F.residueCharacteristic] E
    obtain ⟨a, e⟩ := chosenFieldUnitsStructure_mixedCharacteristic ν
      (v.valuedAdicCompletion_surjective K)
    letI : Fact F.residueCharacteristic.Prime := ⟨F.residueCharacteristic_prime⟩
    letI : Fintype F.residueField := Fintype.ofFinite _
    letI : Fintype F.residueFieldˣ := Fintype.ofFinite _
    have hunitpos : 0 < Fintype.card F.residueFieldˣ :=
      Fintype.card_pos_iff.mpr ⟨1⟩
    have hcard : 0 < Nat.card F.residueField - 1 := by
      calc
        0 < Fintype.card F.residueFieldˣ := hunitpos
        _ = Nat.card F.residueFieldˣ :=
          (@Nat.card_eq_fintype_card F.residueFieldˣ
            (inferInstance : Fintype F.residueFieldˣ)).symm
        _ = Nat.card F.residueField - 1 := Nat.card_units F.residueField
    letI : NeZero (Nat.card F.residueField - 1) :=
      ⟨hcard.ne'⟩
    letI : NeZero (F.residueCharacteristic ^ a) :=
      ⟨pow_ne_zero _ F.residueCharacteristic_prime.ne_zero⟩
    let C := Multiplicative (ZMod (Nat.card F.residueField - 1)) ×
      Multiplicative (ZMod (F.residueCharacteristic ^ a) ×
        (Fin d → ℤ_[F.residueCharacteristic]))
    letI : CompactSpace C := by dsimp only [C]; infer_instance
    letI : T2Space (Multiplicative ℤ × C) := e.toHomeomorph.isEmbedding.t2Space
    letI : T2Space C := (isEmbedding_prodMkRight (1 : Multiplicative ℤ)).t2Space
    letI : ContinuousMul C := by dsimp only [C]; infer_instance
    letI : Finite (Multiplicative ℤ ⧸
        (powMonoidHom 6 : Multiplicative ℤ →* Multiplicative ℤ).range) :=
      LocalFieldTheory.finite_multiplicativeInt_nthPowerQuotient (by decide : 6 ≠ 0)
    letI : Finite (C ⧸ (powMonoidHom 6 : C →* C).range) := by
      dsimp only [C]
      infer_instance
    have hf : Finite (Eˣ ⧸ (powMonoidHom 6 : Eˣ →* Eˣ).range) :=
      LocalFieldTheory.finite_nthPowerQuotient_of_mulEquiv
        Eˣ (Multiplicative ℤ × C) 6 e.symm.toMulEquiv
    have hc : IsClosed (Set.range (fun x : Eˣ => x ^ 6)) :=
      isClosed_range_pow_of_discrete_compact e.symm 6
    exact ⟨hf, hc⟩
  refine ⟨hm.1, ?_⟩
  change @IsClosed Eˣ
    (@Units.instTopologicalSpaceUnits E (inferInstance : TopologicalSpace E)
      (inferInstance : Monoid E)) _
  rw [ht]
  exact hm.2

/-- In the original completion topology the sixth-power subgroup is open. -/
theorem isOpen_sixthPowerRange :
    IsOpen ((powMonoidHom 6 :
      (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range :
        Set (v.adicCompletion K)ˣ) := by
  let H := (powMonoidHom 6 :
    (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range
  letI : Finite ((v.adicCompletion K)ˣ ⧸ H) :=
    (sixthPowerRange_finite_and_closed K v).1
  letI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact H.isOpen_of_isClosed_of_finiteIndex
    (sixthPowerRange_finite_and_closed K v).2

/-- Discreteness follows from proved openness, rather than from finiteness alone. -/
theorem discrete_sixthPowerQuotient :
    DiscreteTopology ((v.adicCompletion K)ˣ ⧸
      (powMonoidHom 6 : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range) :=
  QuotientGroup.discreteTopology_iff.mpr (isOpen_sixthPowerRange K v)

/-- The ACTUAL sextic class map is locally constant on the local unit group.
This does not extend it across the field's zero element. -/
theorem isLocallyConstant_sixthPowerClassMap :
    IsLocallyConstant (QuotientGroup.mk'
      (powMonoidHom 6 : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range) := by
  letI := discrete_sixthPowerQuotient K v
  apply (IsLocallyConstant.iff_continuous _).mpr
  exact QuotientGroup.continuous_mk

/-- A genuinely positive depth in the canonical principal-unit filtration
is contained in the sixth powers of the original completion's unit group. -/
theorem exists_adicPrincipalUnits_le_sixthPowerRange :
    ∃ n : ℕ, 1 ≤ n ∧ adicPrincipalUnits K v n ≤
      (powMonoidHom 6 : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range := by
  let H := (powMonoidHom 6 :
    (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range
  obtain ⟨n, hn⟩ := RayClass.exists_localHigherUnitGroup_subset v
    ((isOpen_sixthPowerRange K v).mem_nhds H.one_mem)
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  exact (RayClass.localHigherUnitGroup_antitone v (Nat.le_succ n)).trans hn

/-- Literal sixth roots, for every unit in one fixed positive principal depth. -/
theorem exists_adicPrincipalUnits_sixth_roots :
    ∃ n : ℕ, 1 ≤ n ∧ ∀ u ∈ adicPrincipalUnits K v n,
      ∃ z : (v.adicCompletion K)ˣ, z ^ 6 = u := by
  obtain ⟨n, hn, hle⟩ := exists_adicPrincipalUnits_le_sixthPowerRange K v
  exact ⟨n, hn, fun u hu => hle hu⟩

end HeckeGeneral.Arithmetic.ActualAdicSixthPowerDraft
