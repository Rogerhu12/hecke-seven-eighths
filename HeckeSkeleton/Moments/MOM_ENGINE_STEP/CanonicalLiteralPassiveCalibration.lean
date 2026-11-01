import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveFrameEnergy
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPaidRowCharacters
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFrameCalibration

/-!
# Calibration of the paid passive-allocation frames

The paid source uses the original moving recipe after its passive
ideal factors have been separated into the finite allocation sum.
Its arithmetic dictionary is the original appended dictionary.  The
new divisor is squarefree because its actual Moebius sign is nonzero;
the frozen scalar is bounded from its individual original atoms.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckePort.Moments
open HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}

namespace CanonicalLiteralPaidCharacters

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ω ψ : HeckeCharacter K} {k : ℕ}
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (index : Fin k → Fin parent.geometry.slotCount)

theorem paidSourceCharacters_maskIndicator :
    (paidSourceCharacters P R F parent oldMoving correction remaining index).MaskIndicator := by
  intro I
  change (if IsCoprime I
      ((F.moving P R oldMoving).effectiveFullSupport remaining).val then (1 : ℂ) else 0) = 0 ∨
    (if IsCoprime I
      ((F.moving P R oldMoving).effectiveFullSupport remaining).val then (1 : ℂ) else 0) = 1
  split_ifs <;> simp

variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k)
variable (hcorr : correction ∈ parent.theta)
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS)
variable (S : ActualSecondCorrelationRows A σ H ι) (pattern : ι → Bool)
variable (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (m q : ℝ) (inverse : IdealTest K)
variable (rectangle : Bool) (firstSign : ℝ) (negative : Bool)
variable (hone : (1 : HeckeCharacter K) ∈ parent.theta)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)

/-- The paid source and its actual child are calibrated directly by
the existing appended recipe. No whole-character equality is supplied. -/
def actualPaidDictionary
    (row : CanonicalOriginalPhaseCalibration.PatternSector P S C pattern sector)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    ((paidSourceCharacters P R F parent oldMoving correction remaining index).restrictSlots
      B.keep).Calibration (σ := σ)
      (CanonicalLiteralAllocatedData.data P R W B F parent oldMoving correction hcorr C
        S.primes S.leftMultiplicity S.rightMultiplicity pattern sector remaining 1 m q inverse
        index rectangle firstSign negative ξ) rfl
      (S.extractedRow C row.val.val).momentIdeal
      (if negative then -(S.factor C row.val.val.val) else S.factor C row.val.val.val)
      (S.extractedRow C row.val.val).element := by
  cases negative with
  | false =>
      simpa only [CanonicalLiteralAllocatedData.data, mul_one, paidSourceCharacters] using
        CanonicalAppendedPhaseCalibration.actualAllocatedCalibration P R parent
          (F.moving P R oldMoving) correction hcorr C pattern sector remaining
          (d.base ^ (m + q)) inverse (W.fourierLeft rectangle firstSign false ξ)
          (W.fourierRight rectangle firstSign false ξ)
          (CanonicalLiteralAllocatedData.preGeometry W firstSign false ξ) index
          S B hone hroot hemb row
  | true =>
      simpa only [CanonicalLiteralAllocatedData.data, mul_one, paidSourceCharacters] using
        CanonicalAppendedPhaseCalibration.actualNegativeAllocatedCalibration P R parent
          (F.moving P R oldMoving) correction hcorr C pattern sector remaining
          (d.base ^ (m + q)) inverse (W.fourierLeft rectangle firstSign true ξ)
          (W.fourierRight rectangle firstSign true ξ)
          (CanonicalLiteralAllocatedData.preGeometry W firstSign true ξ) index
          S B hone hroot hemb row

end CanonicalLiteralPaidCharacters

namespace CanonicalLiteralPassiveFrames

open CanonicalLiteralPassiveSource CanonicalLiteralPassiveNonzero

variable {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k)
variable (paid : FixedChildCharacters K B.keep.card)
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS)
variable (S : ActualSecondCorrelationRows A σ H ι) (side : SecondColumnSide)
variable (M : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W B A M })
variable (firstSign : ℝ) (rectangle : Bool)

local notation "f" => frame W B A paid C S side M a firstSign rectangle
local notation "t" => table W B A paid

/-- Individual original atom bounds on this exact passive allocation.
The independent divisor norm is retained by `scalarBound`. -/
def frozenBounds (hmask : paid.MaskIndicator) (ha : a ∈ nonzeroLabels W B A M) :
    f.source.FrozenAtomBounds where
  annulus i := (Ideal.absNorm ((branch W B A M a).witness.2 i).asIdeal : ℝ) /
    t.base ^ t.length i
  profile i := ‖t.slotWeight i ((branch W B A M a).witness.2 i)‖ ^ 2
  annulus_nonneg i := div_nonneg (Nat.cast_nonneg _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans t.base_gt_one) _).le
  profile_nonneg i := sq_nonneg _
  plain₁_bound h _ := by
    cases side <;> exact OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one
      paid.plain paid.plainTwist paid.mask _ (hmask _)
  plain₂_bound h _ := by
    cases side <;> exact OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one
      paid.plain paid.plainTwist paid.mask _ (hmask _)
  prime_bound h _ i _ := by
    cases side <;> exact OriginalProfileAtomBounds.sourcePrimeCoefficient_norm_le_one
      (paid.slot i) (paid.slotTwist i) paid.mask _ (hmask _)
  prime_annulus i _ := by
    cases side <;> exact le_of_eq (div_mul_cancel₀ _
      (Real.rpow_pos_of_pos (zero_lt_one.trans t.base_gt_one) _).ne').symm
  slot_bound h _ i _ := by cases side <;> exact le_rfl
  divisor_squarefree := by
    cases side <;> exact divisor_squarefree W B A M a ha
  allocation_mem := by
    cases side <;> exact selection_mem W B A M a

theorem frozenBounds_scalarBound (hmask : paid.MaskIndicator)
    (ha : a ∈ nonzeroLabels W B A M) :
    (frozenBounds W B paid C S side M a firstSign rectangle hmask ha).scalarBound =
      (∏ i ∈ Finset.univ \ (branch W B A M a).keep,
        (((Ideal.absNorm ((branch W B A M a).witness.2 i).asIdeal : ℝ) /
            t.base ^ t.length i) *
          ‖t.slotWeight i ((branch W B A M a).witness.2 i)‖ ^ 2)) /
        (Ideal.absNorm a.val.1 : ℝ) := by
  cases side <;> rfl

end CanonicalLiteralPassiveFrames

namespace CanonicalLiteralPassiveSource.PhaseChoice

variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {F : CanonicalLiteralPhaseCalibration.FixedPhases A}
variable {C : A.GeneralArithmeticContext σ η hS}
variable (choice : PhaseChoice F C)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]

theorem literalCharacter_eq (S : ActualSecondCorrelationRows A σ H ι)
    (oldMoving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
    (pattern : ι → Bool)
    (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) (h : H) :
    S.literalCharacter C P R F oldMoving correction pattern sector h =
      S.literalCharacter C P R choice.phases oldMoving correction pattern sector h := by
  cases choice with
  | unamplified => rfl
  | amplified p e hp =>
      exact CanonicalLiteralPaidRowCharacters.literalCharacter_eq P R S F C p e hp
        oldMoving correction pattern sector h

end CanonicalLiteralPassiveSource.PhaseChoice

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidCharacters.actualPaidDictionary
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveFrames.frozenBounds
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveFrames.frozenBounds_scalarBound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveSource.PhaseChoice.literalCharacter_eq
