import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CompleteRowAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentColumnPhaseBinding
import HeckeSkeleton.Base
import HeckeAxiom.SexticSymbolDictionary

/-!
# The actual source probe supplies the individual periodic atom phases

The source uses its one original arithmetic choice. Its zero-extended
orbital sextic evaluation agrees, at every original quotient element,
with the complete residue value used by the canonical step dictionary.
The proof covers all nonzero ideals, including the exceptional zero
support; it is not restricted to the original row-map image.

The last theorem supplies exactly the three individual-atom hypotheses
of MOM_ENGINE_STEP `ParentColumnPhaseBinding` at immutable commit
`8de8efb608fd1bb46f3f63ad75f23fac7c326a8d`. That owner module proves the
whole Cartesian-column identity and the exterior-column zero filter.
The actual positive orbital chart is a separate source construction.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

/-- The original probe's actual phase equals the complete residue
value on every original quotient element, with all ramification zeros.
No phase calibration is an input. -/
theorem actualProbeOrbitSexticEvaluation_eq_actualIdealResidue
    (c : TargetContext K) (I : NonzeroIdeal K)
    (q : ActualSIntegerOrbit K (places K c)) :
    actualOrbitSexticEvaluation K (places K c)
        (probeData K c).arithmetic.root6 (probeData K c).arithmetic.primitive6
        (probeData K c).arithmetic.embedding I q =
      EngineStep.actualIdealResidue (A := (axiomChoice K c).A)
        (σ := complexEmbedding K c) I.val q.out.val := by
  rw [← actualOrbitSexticEvaluation_out]
  by_cases hgood : sexticIdealOutsideS K (places K c) I
  · let J : ExteriorIdeal K (places K c) := ⟨I, fun p hp => (hgood p hp).1⟩
    calc
      zeroExtendedSexticIdealEvaluation K (places K c)
          (probeData K c).arithmetic.root6 (probeData K c).arithmetic.primitive6
          (probeData K c).arithmetic.embedding I q.out.val =
        idealSymbol K (places K c) (probeData K c).arithmetic J q.out.val := by
          rw [zeroExtendedSexticIdealEvaluation, dif_pos hgood]
          rfl
      _ = complexEmbedding K c
          ((axiomChoice K c).A.sexticResidue
            ((HeckeAxiom.exteriorEquiv (axiomChoice K c).A).symm J) q.out.val) :=
        (axiomChoice K c).idealSymbol_eq J q.out.val
      _ = EngineStep.actualIdealResidue (A := (axiomChoice K c).A)
          (σ := complexEmbedding K c) I.val q.out.val := by
        exact (EngineStep.actualIdealResidue_exterior
          (σ := complexEmbedding K c)
          ((HeckeAxiom.exteriorEquiv (axiomChoice K c).A).symm J) q.out.val).symm
  · have hnot : ¬(I.val ≠ 0 ∧ IsCoprime I.val (axiomChoice K c).A.cS) := by
      intro hI
      apply hgood
      have hout := (HeckeAxiom.sup_cS_eq_top_iff (axiomChoice K c).A I.val
        (by simpa only [Ideal.zero_eq_bot] using hI.1)).mp hI.2.sup_eq
      intro p hp
      have hpS : p ∉ places K c := hout p hp
      refine ⟨hpS, fun h6 => hpS ?_⟩
      exact Finset.mem_coe.mpr ((axiomChoice K c).A.above_six p h6)
    simp only [zeroExtendedSexticIdealEvaluation, dif_neg hgood,
      EngineStep.actualIdealResidue, dif_neg hnot]

/-- The literal constant atoms from a complete-row model satisfy the
canonical per-atom phase dictionaries at every q. Their arithmetic
coefficients may include any fixed remaining ideal and any actual slot
background; neither changes these phase arrays. -/
theorem completeIdealRawAtoms_actual_phase_dictionary
    (c : TargetContext K) {omegaCharacter psiCharacter : HeckeCharacter K}
    (R : RowCharacterInput K (places K c) (probeData K c))
    (sector : NonzeroIdeal K → SixthUnitClasses K (places K c))
    (d : MomentData K omegaCharacter psiCharacter) (remaining : NonzeroIdeal K)
    (hallowed : ∀ u, d.allowedRow u → completeIdealIsExterior K (places K c) u)
    (hrow : ∀ u, d.allowedRow u → d.rowCharacter u =
      completeIdealRowCharacter K (places K c) (probeData K c) R (sector u) u)
    (hmask : ∀ u I, d.commonMask u I =
      (completeIdealCommonMask K (places K c) u I &&
        decide (IsCoprime I remaining.val)))
    (W : EngineStep.NormProfileRecipe (fun _ : PUnit => d))
    (a : RealParameters) (U t Y₁ Y₂ : ℝ) :
    let atoms := completeIdealArithmeticAtoms (places K c) (probeData K c) R
      sector d remaining hallowed hrow hmask
    let raw := (atoms.constantAtoms W a U t).raw Y₁ Y₂
    (∀ I ∈ raw.leftColumns, ∀ q : ActualSIntegerOrbit K (places K c),
      raw.leftPhase q I = EngineStep.actualIdealResidue (A := (axiomChoice K c).A)
        (σ := complexEmbedding K c) I.val q.out.val) ∧
    (∀ I ∈ raw.rightColumns, ∀ q : ActualSIntegerOrbit K (places K c),
      raw.rightPhase q I = EngineStep.actualIdealResidue (A := (axiomChoice K c).A)
        (σ := complexEmbedding K c) I.val q.out.val) ∧
    (∀ i, ∀ p ∈ raw.slotColumns i, ∀ q : ActualSIntegerOrbit K (places K c),
      raw.primePhase q i p = EngineStep.actualIdealResidue (A := (axiomChoice K c).A)
        (σ := complexEmbedding K c) p.asIdeal q.out.val) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro I _ q
    exact actualProbeOrbitSexticEvaluation_eq_actualIdealResidue c I q
  · intro I _ q
    exact actualProbeOrbitSexticEvaluation_eq_actualIdealResidue c I q
  · intro i p _ q
    exact actualProbeOrbitSexticEvaluation_eq_actualIdealResidue c (momentPrimeIdeal K p) q

/-- A fixed moving character remains in the arithmetic coefficients of
the actual atoms. Their original orbital phases still satisfy the same
all-quotient dictionary, without any membership premise on that character
in the fixed exceptional set and without changing the complete row map. -/
theorem completeIdealFixedTwistRawAtoms_actual_phase_dictionary
    (c : TargetContext K) {omegaCharacter psiCharacter : HeckeCharacter K}
    (R : RowCharacterInput K (places K c) (probeData K c))
    (sector : NonzeroIdeal K → SixthUnitClasses K (places K c))
    (d : MomentData K omegaCharacter psiCharacter) (remaining : NonzeroIdeal K)
    (Γ : HeckeCharacter K)
    (hallowed : ∀ u, d.allowedRow u → completeIdealIsExterior K (places K c) u)
    (hrow : ∀ u, d.allowedRow u → d.rowCharacter u =
      Γ * completeIdealRowCharacter K (places K c) (probeData K c) R (sector u) u)
    (hmask : ∀ u I, d.commonMask u I =
      (completeIdealCommonMask K (places K c) u I &&
        decide (IsCoprime I remaining.val)))
    (W : EngineStep.NormProfileRecipe (fun _ : PUnit => d))
    (a : RealParameters) (U t Y₁ Y₂ : ℝ) :
    let atoms := completeIdealFixedTwistArithmeticAtoms (places K c) (probeData K c) R
      sector d remaining Γ hallowed hrow hmask
    let raw := (atoms.constantAtoms W a U t).raw Y₁ Y₂
    (∀ I ∈ raw.leftColumns, ∀ q : ActualSIntegerOrbit K (places K c),
      raw.leftPhase q I = EngineStep.actualIdealResidue (A := (axiomChoice K c).A)
        (σ := complexEmbedding K c) I.val q.out.val) ∧
    (∀ I ∈ raw.rightColumns, ∀ q : ActualSIntegerOrbit K (places K c),
      raw.rightPhase q I = EngineStep.actualIdealResidue (A := (axiomChoice K c).A)
        (σ := complexEmbedding K c) I.val q.out.val) ∧
    (∀ i, ∀ p ∈ raw.slotColumns i, ∀ q : ActualSIntegerOrbit K (places K c),
      raw.primePhase q i p = EngineStep.actualIdealResidue (A := (axiomChoice K c).A)
        (σ := complexEmbedding K c) p.asIdeal q.out.val) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro I _ q
    exact actualProbeOrbitSexticEvaluation_eq_actualIdealResidue c I q
  · intro I _ q
    exact actualProbeOrbitSexticEvaluation_eq_actualIdealResidue c I q
  · intro i p _ q
    exact actualProbeOrbitSexticEvaluation_eq_actualIdealResidue c (momentPrimeIdeal K p) q

end HeckeSkeleton.Moments.EngineInduction
