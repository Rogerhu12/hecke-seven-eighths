module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassivePhaseCore
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveMask

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original phase with the paid residual mask

The complete original phase identities are proved in PassivePhaseCore.
This compatibility module applies the same paid-carrier coprimality
identity to obtain the three original residual-mask statements.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassivePhaseBridge

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open CanonicalOriginalPhaseCalibration (originalCoprimeMask)

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p} (P : OriginalPhaseData packet)

/-- On the actual paid carrier, the complete original deletion has
exactly the residual mask used by N2's finite allocation. -/
theorem coefficient_residual (O : OrdinaryData packet) (χ : HeckeCharacter K)
    (hpassive : (poolPassiveIdeal P).val ∣ P.deletionIdeal.val)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K) (hJ : IsCoprime J.val (Arithmetic.data c).cS)
    (hpaid : IsCoprime J.val packet.second.physical.first.paidSupport.val) :
    heckeIdealCoefficient K (χ * (P.moving false).character) J *
        originalCoprimeMask (P.mask false) J.val =
      (heckeIdealCoefficient K (χ * (P.moving true).character) J *
        originalCoprimeMask (P.mask true) J.val) *
          (if IsCoprime J.val O.passiveMask then 1 else 0) := by
  rw [coefficient_fullDeletion P χ hpassive J hJ]
  change _ * (if IsCoprime J.val
    (∏ I ∈ packet.second.physical.first.fullDeletion, I) then 1 else 0) = _
  rw [O.residual_coprime_iff J.val hpaid]

variable {k : ℕ} (index : Fin k → Fin call.localizedData.geometry.slotCount)

theorem plain_term_residual (O : OrdinaryData packet)
    (hpassive : (poolPassiveIdeal P).val ∣ P.deletionIdeal.val)
    (g h : (Arithmetic.data c).R) (w : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (N : ℝ) (J : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hpaid : IsCoprime J.val packet.second.physical.first.paidSupport.val) :
    sourcePlainTerm (σ := Arithmetic.embedding c) (P.characters false index).plain
        (P.characters false index).plainTwist (P.characters false index).mask g h w N J =
      sourcePlainTerm (σ := Arithmetic.embedding c) (P.characters true index).plain
        (P.characters true index).plainTwist (P.characters true index).mask g h w N J *
          (if IsCoprime J.val O.passiveMask then 1 else 0) := by
  rw [plain_term P index hpassive g h w N J]
  change _ * (if IsCoprime J.val
    (∏ I ∈ packet.second.physical.first.fullDeletion, I) then 1 else 0) = _
  rw [O.residual_coprime_iff J.val hpaid]

theorem prime_term_residual (O : OrdinaryData packet)
    (hpassive : (poolPassiveIdeal P).val ∣ P.deletionIdeal.val)
    (g h : (Arithmetic.data c).R) (w : HeightOneSpectrum (𝓞 K) → ℂ)
    (N : ℝ) (i : Fin k) (q : HeightOneSpectrum (𝓞 K))
    (hpaid : IsCoprime q.asIdeal packet.second.physical.first.paidSupport.val) :
    sourcePrimeTerm (σ := Arithmetic.embedding c) ((P.characters false index).slot i)
        ((P.characters false index).slotTwist i) (P.characters false index).mask g h w N q =
      sourcePrimeTerm (σ := Arithmetic.embedding c) ((P.characters true index).slot i)
        ((P.characters true index).slotTwist i) (P.characters true index).mask g h w N q *
          (if IsCoprime q.asIdeal O.passiveMask then 1 else 0) := by
  rw [prime_term P index hpassive g h w N i q]
  change _ * (if IsCoprime q.asIdeal
    (∏ I ∈ packet.second.physical.first.fullDeletion, I) then 1 else 0) = _
  rw [O.residual_coprime_iff q.asIdeal hpaid]

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassivePhaseBridge

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassivePhaseBridge.coefficient_residual
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassivePhaseBridge.plain_term_residual
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassivePhaseBridge.prime_term_residual
