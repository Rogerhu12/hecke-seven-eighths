module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryCharacterFacts
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryMultiplierTransport

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual first, pool and unit phases in the original Euler atoms

Each appended singleton uses its genuine generated ideal and complete
coprimality mask. The old effective support agrees with the original
remaining mask on exterior columns. The literal first deletion is
removed only where the actual reconstructed residual column is coprime
to it. All three original residue factors, including their zeros, are
therefore the same phases as in the source multiplier.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]

namespace OrdinaryCharacters

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ω ψ : HeckeCharacter K} {k : ℕ}

def effectiveCharacters (parent : MomentData K ω ψ) (correction : HeckeCharacter K)
    (moving : OriginalMovingFactors A P R)
    (remaining deletion : HeckeGeneral.Analysis.NonzeroIdeal K)
    (index : Fin k → Fin parent.geometry.slotCount) : FixedChildCharacters K k :=
  CanonicalOriginalPhaseCalibration.sourceCharacters parent (correction * moving.character)
    (exteriorMomentIdeal (moving.effectiveFullSupport remaining) * deletion) index

theorem effectiveCharacters_append_singleton
    (parent : MomentData K ω ψ) (correction : HeckeCharacter K)
    (moving : OriginalMovingFactors A P R)
    (remaining deletion : HeckeGeneral.Analysis.NonzeroIdeal K)
    (index : Fin k → Fin parent.geometry.slotCount)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a) :
    effectiveCharacters P R parent correction
        (moving.append (OriginalMovingFactors.singleton ⟨a, ha.1⟩ 1)) remaining deletion index =
      twist P R (effectiveCharacters P R parent correction moving remaining deletion index)
        I a ha := by
  have hm := effectiveMask_append_singleton P R moving remaining deletion I a ha
  dsimp only [effectiveCharacters, twist, CanonicalOriginalPhaseCalibration.sourceCharacters]
  simp only [OriginalMovingFactors.append_character, mul_assoc, hm]

theorem effectiveCharacters_append_bare
    (parent : MomentData K ω ψ) (correction : HeckeCharacter K)
    (moving : OriginalMovingFactors A P R)
    (remaining deletion : HeckeGeneral.Analysis.NonzeroIdeal K)
    (index : Fin k → Fin parent.geometry.slotCount)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (i : AllocationColumn K k) (J : A.Exterior) (hJ : J.val = allocationColumnIdeal i) :
    rawBareSourceCoefficient
        (effectiveCharacters P R parent correction
          (moving.append (OriginalMovingFactors.singleton ⟨a, ha.1⟩ 1)) remaining deletion index)
        N₁ N₂ Z length w₁ w₂ w i =
      rawBareSourceCoefficient
        (effectiveCharacters P R parent correction moving remaining deletion index)
        N₁ N₂ Z length w₁ w₂ w i * actualIdealResidue (A := A) (σ := σ) J.val a := by
  rw [effectiveCharacters_append_singleton]
  exact twist_bare P R _ hroot hemb I a ha N₁ N₂ Z length w₁ w₂ w i J hJ

/-- The mask occurs once on the complete product, even when a prime
is repeated in several original slots. -/
theorem bare_eq_unmasked (T : FixedChildCharacters K k)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (i : AllocationColumn K k) (J : A.Exterior) (hJ : J.val = allocationColumnIdeal i) :
    rawBareSourceCoefficient T N₁ N₂ Z length w₁ w₂ w i =
      rawBareSourceCoefficient { T with mask := 1 } N₁ N₂ Z length w₁ w₂ w i * T.mask J.val := by
  have hn : allocationColumnIdeal i ≠ 0 := hJ ▸ J.property.1
  have h₁ : i.1.1 ≠ 0 := by
    intro hz
    exact hn (by simp only [allocationColumnIdeal, hz, zero_mul])
  have h₂ : i.1.2 ≠ 0 := by
    intro hz
    exact hn (by simp only [allocationColumnIdeal, hz, mul_zero, zero_mul])
  simp only [rawBareSourceCoefficient, FixedChildCharacters.bareCoefficient,
    childCartesianCoefficient, sourcePlainCoefficient, sourcePrimeCoefficient,
    MonoidHom.one_apply, mul_one, sourceMomentIdeal_val_of_ne_zero _ h₁,
    sourceMomentIdeal_val_of_ne_zero _ h₂, hJ, allocationColumnIdeal,
    map_mul, map_prod, Finset.prod_mul_distrib]
  ring

theorem sourceCharacters_bare_mask_congr
    (parent : MomentData K ω ψ) (correction : HeckeCharacter K)
    (M N : HeckeGeneral.Analysis.NonzeroIdeal K)
    (index : Fin k → Fin parent.geometry.slotCount)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (i : AllocationColumn K k) (J : A.Exterior) (hJ : J.val = allocationColumnIdeal i)
    (hmask : CanonicalOriginalPhaseCalibration.originalCoprimeMask M J.val =
      CanonicalOriginalPhaseCalibration.originalCoprimeMask N J.val) :
    rawBareSourceCoefficient
        (CanonicalOriginalPhaseCalibration.sourceCharacters parent correction M index)
        N₁ N₂ Z length w₁ w₂ w i =
      rawBareSourceCoefficient
        (CanonicalOriginalPhaseCalibration.sourceCharacters parent correction N index)
        N₁ N₂ Z length w₁ w₂ w i := by
  rw [bare_eq_unmasked
      (CanonicalOriginalPhaseCalibration.sourceCharacters parent correction M index)
      N₁ N₂ Z length w₁ w₂ w i J hJ,
    bare_eq_unmasked
      (CanonicalOriginalPhaseCalibration.sourceCharacters parent correction N index)
      N₁ N₂ Z length w₁ w₂ w i J hJ]
  change _ * CanonicalOriginalPhaseCalibration.originalCoprimeMask M J.val =
    _ * CanonicalOriginalPhaseCalibration.originalCoprimeMask N J.val
  rw [hmask]
  rfl

/-- Effective support removes only inside-`S` prime factors. Such
factors are already absent from every exterior column here. -/
theorem effectiveCharacters_bare_original
    (parent : MomentData K ω ψ) (correction : HeckeCharacter K)
    (moving : OriginalMovingFactors A P R)
    (remaining deletion : HeckeGeneral.Analysis.NonzeroIdeal K)
    (index : Fin k → Fin parent.geometry.slotCount)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (i : AllocationColumn K k) (J : A.Exterior) (hJ : J.val = allocationColumnIdeal i)
    (hdelete : IsCoprime J.val deletion.val) :
    rawBareSourceCoefficient
        (effectiveCharacters P R parent correction moving remaining deletion index)
        N₁ N₂ Z length w₁ w₂ w i =
      rawBareSourceCoefficient
        (CanonicalOriginalPhaseCalibration.sourceCharacters parent
          (correction * moving.character) (exteriorMomentIdeal moving.support * remaining) index)
        N₁ N₂ Z length w₁ w₂ w i := by
  apply sourceCharacters_bare_mask_congr parent (correction * moving.character)
    (exteriorMomentIdeal (moving.effectiveFullSupport remaining) * deletion)
    (exteriorMomentIdeal moving.support * remaining) index N₁ N₂ Z length w₁ w₂ w i J hJ
  have heff : IsCoprime J.val (moving.effectiveFullSupport remaining).val ↔
      IsCoprime J.val moving.support.val ∧ IsCoprime J.val remaining.val := by
    change IsCoprime J.val (moving.fullMaskSupport (remainingMaskIdeal A remaining)).val ↔ _
    rw [moving.fullMaskSupport_coprime_iff, remainingMaskIdeal_val,
      ← remainingMaskRadical_coprime_iff A remaining J.val
        (Ideal.isCoprime_iff_sup_eq.mpr J.property.2)]
  change (if IsCoprime J.val ((moving.effectiveFullSupport remaining).val * deletion.val)
    then (1 : ℂ) else 0) =
    (if IsCoprime J.val (moving.support.val * remaining.val) then 1 else 0)
  simp only [IsCoprime.mul_right_iff, hdelete, and_true, heff]

end OrdinaryCharacters

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace OriginalPhaseData

variable {packet : RawLeafPacket call p} (phases : OriginalPhaseData packet)

def firstIdeal : (Arithmetic.data c).Exterior := phases.firstMoving.factorIdeal (0 : Fin 1)

theorem first_generates : (Arithmetic.data c).Generates phases.firstIdeal
    packet.second.physical.first.firstElement :=
  phases.firstMoving.factorIdeal_generates (0 : Fin 1)

theorem firstMoving_eq_singleton :
    phases.firstMoving = OriginalMovingFactors.singleton
      ⟨packet.second.physical.first.firstElement, phases.first_generates.1⟩ 1 := rfl

/-- This ideal belongs to the phase element, so its exponent is twice
the literal pool valuation; it is not the removed physical pool power. -/
def poolPhaseIdeal : (Arithmetic.data c).Exterior :=
  match phases.pool with
  | none => unitExterior (Arithmetic.data c)
  | some (e, q) => powerIdeal q (2 * e.multiplicity)

def poolElement : (Arithmetic.data c).R :=
  OrdinaryMultiplierTransport.poolElement (Arithmetic.context c) phases.pool

theorem pool_generates : (Arithmetic.data c).Generates phases.poolPhaseIdeal phases.poolElement := by
  cases hp : phases.pool with
  | none =>
    simp only [poolPhaseIdeal, poolElement, OrdinaryMultiplierTransport.poolElement, hp]
    exact unitExterior_generates (Arithmetic.data c)
  | some eq =>
    rcases eq with ⟨e, q⟩
    simp only [poolPhaseIdeal, poolElement, OrdinaryMultiplierTransport.poolElement, hp]
    exact generator_power_generates (Arithmetic.context c) q (2 * e.multiplicity)

theorem poolMoving_false_eq_singleton :
    phases.poolMoving false = OriginalMovingFactors.singleton
      ⟨phases.poolElement, phases.pool_generates.1⟩ 1 := by
  cases hp : phases.pool with
  | none =>
    simp only [OriginalPhaseData.poolMoving, poolElement,
      OrdinaryMultiplierTransport.poolElement, hp]
  | some eq =>
    rcases eq with ⟨e, q⟩
    simp only [OriginalPhaseData.poolMoving, poolElement,
      OrdinaryMultiplierTransport.poolElement, hp, Bool.false_eq_true, if_false]

/-- At a genuine exterior residual tuple, the full fixed-character
dictionary is the original Euler atoms times the three actual residues.
The assertion is uniform in every scale, weight and occurrence index. -/
theorem characters_false_bare {k : ℕ}
    (index : Fin k → Fin call.localizedData.geometry.slotCount)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (i : AllocationColumn K k) (J : (Arithmetic.data c).Exterior)
    (hJ : J.val = allocationColumnIdeal i) (hdelete : IsCoprime J.val phases.deletionIdeal.val) :
    rawBareSourceCoefficient (phases.characters false index) N₁ N₂ Z length w₁ w₂ w i =
      rawBareSourceCoefficient
        (CanonicalOriginalPhaseCalibration.sourceCharacters call.localizedData
          (call.localizedSource.source.recipe.correction *
            call.localizedSource.source.recipe.moving.character)
          call.localizedSource.source.recipe.arithmeticMask index)
        N₁ N₂ Z length w₁ w₂ w i *
        actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
          J.val packet.second.physical.first.firstElement *
        actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
          J.val phases.poolElement *
        actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
          J.val (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := Arithmetic.data c)) := by
  have hroot : (probeData K c).arithmetic.root6 = (Arithmetic.data c).zeta12 ^ 2 := rfl
  have hemb : (probeData K c).arithmetic.embedding = Arithmetic.embedding c := rfl
  have hadd (moving : OriginalMovingFactors (Arithmetic.data c)
      (probeData K c) (momentRowCharacters K c))
      (I : (Arithmetic.data c).Exterior) (a : (Arithmetic.data c).R)
      (ha : (Arithmetic.data c).Generates I a) :=
    OrdinaryCharacters.effectiveCharacters_append_bare (probeData K c) (momentRowCharacters K c)
      call.localizedData call.localizedSource.source.recipe.correction moving
      call.localizedSource.source.recipe.remaining phases.deletionIdeal index hroot hemb I a ha
      N₁ N₂ Z length w₁ w₂ w i J hJ
  change rawBareSourceCoefficient
      (OrdinaryCharacters.effectiveCharacters (probeData K c) (momentRowCharacters K c)
        call.localizedData call.localizedSource.source.recipe.correction
        (phases.moving false) call.localizedSource.source.recipe.remaining phases.deletionIdeal index)
      N₁ N₂ Z length w₁ w₂ w i = _
  unfold OriginalPhaseData.moving
  rw [phases.firstMoving_eq_singleton, phases.poolMoving_false_eq_singleton]
  unfold CanonicalLiteralFixedPhases.emptyDivisorMoving
  rw [hadd _ (unitExterior (Arithmetic.data c))
      (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := Arithmetic.data c))
      (CanonicalLiteralFixedPhases.emptyDivisorInverse_generates (A := Arithmetic.data c)),
    hadd _ phases.poolPhaseIdeal phases.poolElement phases.pool_generates,
    hadd _ phases.firstIdeal packet.second.physical.first.firstElement phases.first_generates]
  rw [OrdinaryCharacters.effectiveCharacters_bare_original
    (probeData K c) (momentRowCharacters K c) call.localizedData
    call.localizedSource.source.recipe.correction call.localizedSource.source.recipe.moving
    call.localizedSource.source.recipe.remaining phases.deletionIdeal index
    N₁ N₂ Z length w₁ w₂ w i J hJ hdelete]
  rfl

end OriginalPhaseData
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryCharacters.effectiveCharacters_append_bare
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OriginalPhaseData.characters_false_bare
