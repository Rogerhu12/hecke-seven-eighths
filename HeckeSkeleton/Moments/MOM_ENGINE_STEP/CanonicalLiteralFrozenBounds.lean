import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPhaseCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualChildMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCommonAtomBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalProfileAtomBounds

/-!
# The original frozen costs of a literal rectangle frame

The arithmetic mask is proved to take only the values zero and one.
Every frozen arithmetic coefficient is therefore bounded by one using
the original Hecke coefficients. The annulus and profile costs are read
from the actual allocated prime occurrences, before either Fourier
variable. The resulting scalar retains the genuine inverse norm of the
same second divisor.

This constructor does not accept a frozen-scalar estimate. Its final
specialization accepts the literal character-field identity of the
original table, whose phase calibration already computes all three
fixed moving factors and the complete first deletion.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

private theorem literal_indicator_mul (x y : ℂ)
    (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) :
    x * y = 0 ∨ x * y = 1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp

namespace FixedChildCharacters

variable {k : ℕ} (T : FixedChildCharacters K k)

/-- A property proved from the original mask operations, not a new
bound on a column or a polynomial. -/
def MaskIndicator : Prop := ∀ I : Ideal (𝓞 K), T.mask I = 0 ∨ T.mask I = 1

variable {T}

theorem MaskIndicator.restrictSlots (h : T.MaskIndicator) (keep : Finset (Fin k)) :
    (T.restrictSlots keep).MaskIndicator := h

theorem MaskIndicator.deleteMask (h : T.MaskIndicator)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K) : (T.deleteMask M).MaskIndicator := by
  intro I
  apply literal_indicator_mul _ _ (h I)
  change (if IsCoprime I M.val then (1 : ℂ) else 0) = 0 ∨
    (if IsCoprime I M.val then (1 : ℂ) else 0) = 1
  split_ifs <;> simp

variable {A : SArithmeticData K}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

theorem MaskIndicator.movingSingleton (h : T.MaskIndicator)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a) :
    (T.movingSingleton P R I a ha).MaskIndicator := by
  intro J
  apply literal_indicator_mul _ _ (h J)
  change (if IsCoprime J I.val then (1 : ℂ) else 0) = 0 ∨
    (if IsCoprime J I.val then (1 : ℂ) else 0) = 1
  split_ifs <;> simp

end FixedChildCharacters

namespace CanonicalLiteralPhaseCalibration

variable {A : SArithmeticData K}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ω ψ : HeckeCharacter K}

/-- The original source mask is binary without any coprimality
assumption on its argument; all ramification zeros remain present. -/
theorem sourceCharacters_maskIndicator (F : FixedPhases A)
    (parent : MomentData K ω ψ) (D : OriginalMovingFactors A P R)
    (correction : HeckeCharacter K)
    (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) {k : ℕ}
    (index : Fin k → Fin parent.geometry.slotCount) :
    (sourceCharacters P R F parent D correction remaining extra index).MaskIndicator := by
  let T := CanonicalOriginalPhaseCalibration.sourceCharacters parent
    (correction * D.character) (exteriorMomentIdeal D.support * remaining) index
  have hT : T.MaskIndicator := by
    intro I
    change (if IsCoprime I (D.support.val * remaining.val) then (1 : ℂ) else 0) = 0 ∨
      (if IsCoprime I (D.support.val * remaining.val) then (1 : ℂ) else 0) = 1
    split_ifs <;> simp
  exact (((hT.movingSingleton P R F.firstIdeal F.firstElement F.first_generates)
    .movingSingleton P R F.poolIdeal F.poolElement F.pool_generates)
    .movingSingleton P R F.unitIdeal F.unitElement F.unit_generates).deleteMask extra

end CanonicalLiteralPhaseCalibration

namespace CanonicalLiteralRectangles.Atoms

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
variable (d : CanonicalLiteralRectangles.Atoms (K := K) k)

/-- The same original atom calculation also pays the common-support
extraction. Its witnesses and deleted occurrences are those of the
stored original support branch. -/
def commonAtomBounds {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
    (hmask : d.characters.MaskIndicator) :
    b.CommonAtomBounds d.characters d.base d.length d.slotWeight where
  base_pos := zero_lt_one.trans d.base_gt_one
  annulus i := (Ideal.absNorm (b.witness.2 i).asIdeal : ℝ) / d.base ^ d.length i
  profile i := ‖d.slotWeight i (b.witness.2 i)‖ ^ 2
  annulus_nonneg i := div_nonneg (Nat.cast_nonneg _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _).le
  profile_nonneg i := sq_nonneg _
  plain₁ := OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one
    d.characters.plain d.characters.plainTwist d.characters.mask _ (hmask _)
  plain₂ := OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one
    d.characters.plain d.characters.plainTwist d.characters.mask _ (hmask _)
  prime i _ := OriginalProfileAtomBounds.sourcePrimeCoefficient_norm_le_one
    (d.characters.slot i) (d.characters.slotTwist i) d.characters.mask _ (hmask _)
  prime_annulus i _ := le_of_eq (div_mul_cancel₀ _
    (Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _).ne').symm
  slot i _ := le_rfl

variable (S : ActualSecondCorrelationRows A σ H ι)
variable (C : A.GeneralArithmeticContext σ η htrace)
variable (side : SecondColumnSide) (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
variable (ideal : AllocationColumn K k → A.Exterior)
variable (hideal : ∀ i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots,
  (ideal i).val = allocationColumnIdeal i)
variable (firstSign : ℝ) (rectangle : Bool)
variable (L : Ideal (𝓞 K)) (selection : primeSupport L → Finset (Fin (k + 2)))
variable (hne : (pairedAllocatedColumns L selection d.plain₁ d.plain₂ d.slots
  id id HeightOneSpectrum.asIdeal).Nonempty)

local notation "f" => (d.factors S side χ ideal hideal firstSign rectangle).frame C L selection hne

/-- Costs are computed on the very witness of the original
allocation. The original finite prime window subsequently bounds
these per-prime values uniformly; it need not be assumed here. -/
def frozenBounds (hmask : d.characters.MaskIndicator)
    (hL : Squarefree L)
    (hselection : selection ∈ AllocationMass.idealAllocations L (k + 2)) :
    f.source.FrozenAtomBounds where
  annulus i := (Ideal.absNorm (f.allocation.witness.2 i).asIdeal : ℝ) / d.base ^ d.length i
  profile i := ‖d.slotWeight i (f.allocation.witness.2 i)‖ ^ 2
  annulus_nonneg i := div_nonneg (Nat.cast_nonneg _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _).le
  profile_nonneg i := sq_nonneg _
  plain₁_bound h _ := by
    cases side <;>
      exact OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one
        d.characters.plain d.characters.plainTwist d.characters.mask _ (hmask _)
  plain₂_bound h _ := by
    cases side <;>
      exact OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one
        d.characters.plain d.characters.plainTwist d.characters.mask _ (hmask _)
  prime_bound h _ i _ := by
    cases side <;>
      exact OriginalProfileAtomBounds.sourcePrimeCoefficient_norm_le_one
        (d.characters.slot i) (d.characters.slotTwist i) d.characters.mask _ (hmask _)
  prime_annulus i _ := by
    cases side <;>
      exact le_of_eq (div_mul_cancel₀ _
        (Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _).ne').symm
  slot_bound h _ i _ := by cases side <;> exact le_rfl
  divisor_squarefree := hL
  allocation_mem := hselection

theorem frozenBounds_scalarBound (hmask : d.characters.MaskIndicator)
    (hL : Squarefree L)
    (hselection : selection ∈ AllocationMass.idealAllocations L (k + 2)) :
    (d.frozenBounds S C side χ ideal hideal firstSign rectangle L selection hne
      hmask hL hselection).scalarBound =
      (∏ i ∈ Finset.univ \ f.allocation.keep,
        (((Ideal.absNorm (f.allocation.witness.2 i).asIdeal : ℝ) / d.base ^ d.length i) *
          ‖d.slotWeight i (f.allocation.witness.2 i)‖ ^ 2)) /
        (Ideal.absNorm L : ℝ) := by
  cases side <;> rfl

variable {ω ψ : HeckeCharacter K}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

/-- On the actual table the binary-mask proof is produced from its
literal original character recipe. The table identity is per field,
not a whole-coefficient or energy hypothesis. -/
def frozenBounds_of_originalCharacters
    (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
    (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
    (correction : HeckeCharacter K)
    (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
    (index : Fin k → Fin parent.geometry.slotCount)
    (hcharacters : d.characters = CanonicalLiteralPhaseCalibration.sourceCharacters
      P R F parent oldMoving correction remaining extra index)
    (hL : Squarefree L)
    (hselection : selection ∈ AllocationMass.idealAllocations L (k + 2)) :
    f.source.FrozenAtomBounds :=
  d.frozenBounds S C side χ ideal hideal firstSign rectangle L selection hne
    (by rw [hcharacters]; exact CanonicalLiteralPhaseCalibration.sourceCharacters_maskIndicator
      P R F parent oldMoving correction remaining extra index) hL hselection

end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPhaseCalibration.sourceCharacters_maskIndicator
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.frozenBounds
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.frozenBounds_of_originalCharacters
