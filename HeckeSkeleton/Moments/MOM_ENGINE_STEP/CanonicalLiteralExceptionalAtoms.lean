import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFrameCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFrozenBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSchwartzProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralScaleProduct
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalExceptionalPlainWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OrdinarySecondExceptionalBinding

/-!
# The actual exceptional atom controls on a literal side frame

The allocation, frozen witness, retained prime sets and original slot
weights are those of the literal frame. The original prime annulus and
the zero-order seminorm of its constructed Schwartz representative fill
all individual atom fields. The frozen norm, formal rectangle product
and central square-root denominators are proved by the original-window
constructor, and no raw-mass or polynomial bound is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalAtoms

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable {W : d.ProfileData} {window : Set ℝ} (E : W.SchwartzModel window)

private theorem witness_slot_mem (B : ActualColumnAllocation K k) (i : Fin k) :
    B.witness.2 i ∈ B.slots i := by
  have h := B.witness_mem
  rw [WholeAllocation.paired_allocated_columns_eq_filter] at h
  exact Fintype.mem_piFinset.mp (Finset.mem_product.mp (Finset.mem_filter.mp h).1).2 i

/-- The real slot weight is evaluated on its original scale. -/
theorem slot_norm_le (amplitude : ℝ)
    (hprofile : ∀ i, SchwartzMap.seminorm ℂ 0 0 (E.slot i) ≤ amplitude)
    (i : Fin k) (p : HeightOneSpectrum (𝓞 K)) :
    ‖d.slotWeight i p‖ ≤ amplitude := by
  rw [← W.slot_eval i 0 p, E.slot_eq]
  exact (SchwartzMap.norm_le_seminorm ℂ (E.slot i) _).trans (hprofile i)

variable (S : ActualSecondCorrelationRows A σ H ι)
variable (C : A.GeneralArithmeticContext σ η hS)
variable (side : SecondColumnSide) (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
variable (ideal : AllocationColumn K k → A.Exterior)
variable (hideal : ∀ i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots,
  (ideal i).val = allocationColumnIdeal i)
variable (firstSign : ℝ) (L : Ideal (𝓞 K))
variable (selection : primeSupport L → Finset (Fin (k + 2)))
variable (hne : (pairedAllocatedColumns L selection d.plain₁ d.plain₂ d.slots
  id id HeightOneSpectrum.asIdeal).Nonempty)

local notation "Joint" => WithLp 2 (ℝ × ℝ)
local notation "frame" =>
  (d.factors S side χ ideal hideal firstSign false).frame C L selection hne

/-- The exponent dictionary is computed from the same allocation and
the exact original main-rectangle product. -/
def scales (annulus amplitude : ℝ) (hannulus : 1 ≤ annulus) (hamplitude : 0 ≤ amplitude) :
    ExceptionalAtomicScales (frame).allocation :=
  (frame).allocation.originalAtomicScales d.base
    (Real.log (d.scale₁ false * d.scale₂ false) / Real.log d.base)
    d.length (fun i => (d.length_pos i).le)
    (fun _ => annulus) (fun _ => amplitude) (fun _ => hannulus) (fun _ => hamplitude)

theorem scales_exponent (annulus amplitude : ℝ)
    (hannulus : 1 ≤ annulus) (hamplitude : 0 ≤ amplitude) :
    (scales d S C side χ ideal hideal firstSign L selection hne
      annulus amplitude hannulus hamplitude).exponent =
      (Real.log (d.scale₁ false * d.scale₂ false) / Real.log d.base +
        ∑ i, d.length i) / 2 - (frame).allocation.rawExtractionLength d.base d.length :=
  (frame).allocation.originalAtomicScales_exponent d.base _ d.length
    (fun i => (d.length_pos i).le) (fun _ => annulus) (fun _ => amplitude)
    (fun _ => hannulus) (fun _ => hamplitude)

variable (annulus amplitude : ℝ) (hannulus : 1 ≤ annulus) (hamplitude : 0 ≤ amplitude)
variable (hmask : d.characters.MaskIndicator) (hprime : d.PrimeNormWindow annulus)
variable (hprofile : ∀ i, SchwartzMap.seminorm ℂ 0 0 (E.slot i) ≤ amplitude)

include hprime in
private theorem frozen_annulus (i : Fin k) :
    (Ideal.absNorm ((frame).allocation.witness.2 i).asIdeal : ℝ) ≤
      annulus * d.base ^ d.length i :=
  hprime i _ (witness_slot_mem (frame).allocation i)

variable {Ψ : Ideal (𝓞 K) →* ℂ} {W₁ W₂ : ℝ → ℂ}
variable {ξ : Joint} {row : S.live}
variable {Y₁ Y₂ : ℝ} {v₁ v₂ : S.live → HeckeGeneral.Analysis.NonzeroIdeal K → ℂ}

/-- This fills the atomic control of the already constructed centered
source on either original side. The character norm bounds are proved
from its genuine indicator mask. -/
include hmask hprime hprofile in
def centeredControl
    (T : (frame).source.ExceptionalAt (σ := σ) Y₁ Y₂ v₁ v₂ Ψ W₁ W₂ ξ row) :
    T.source.AtomicControl d.base
      (scales d S C side χ ideal hideal firstSign L selection hne
        annulus amplitude hannulus hamplitude) := by
  have hp (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
      ‖sourcePlainCoefficient d.characters.plain d.characters.plainTwist
        d.characters.mask I‖ ≤ 1 :=
    OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one
      d.characters.plain d.characters.plainTwist d.characters.mask I (hmask _)
  have hs (i : Fin k) (p : HeightOneSpectrum (𝓞 K)) :
      ‖sourcePrimeCoefficient (d.characters.slot i) (d.characters.slotTwist i)
        d.characters.mask p‖ ≤ 1 :=
    OriginalProfileAtomBounds.sourcePrimeCoefficient_norm_le_one
      (d.characters.slot i) (d.characters.slotTwist i) d.characters.mask p (hmask _)
  have ha (i : Fin k) := frozen_annulus d S C side χ ideal hideal firstSign
    L selection hne annulus hprime i
  have hw := slot_norm_le d E amplitude hprofile
  cases side <;>
    exact T.source.atomicControlOfOriginalWindows C d.base d.base_gt_one rfl
      (d.scale₁_pos false) (d.scale₂_pos false) (fun i => (d.length_pos i).le)
      (fun _ => annulus) (fun _ => amplitude) (fun _ => hannulus) (fun _ => hamplitude)
      (hp _) (hp _) (fun i _ => hs i _) (fun i _ => ha i) (fun i _ => hw i _)
      (fun j p hp => hprime _ p hp) (fun j p _ => hs _ p) (fun j p _ => hw _ p)

/-- Ordinary exceptional charts inherit the very same allocation and
main rectangle. No comparison-scale estimate is needed. -/
include hmask hprime hprofile in
def ordinaryControl
    (T : (frame).source.OrdinaryExceptionalAt (σ := σ) Ψ W₁ W₂ ξ row) :
    T.source.AtomicControl d.base
      (scales d S C side χ ideal hideal firstSign L selection hne
        annulus amplitude hannulus hamplitude) := by
  have hp (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
      ‖sourcePlainCoefficient d.characters.plain d.characters.plainTwist
        d.characters.mask I‖ ≤ 1 :=
    OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one
      d.characters.plain d.characters.plainTwist d.characters.mask I (hmask _)
  have hs (i : Fin k) (p : HeightOneSpectrum (𝓞 K)) :
      ‖sourcePrimeCoefficient (d.characters.slot i) (d.characters.slotTwist i)
        d.characters.mask p‖ ≤ 1 :=
    OriginalProfileAtomBounds.sourcePrimeCoefficient_norm_le_one
      (d.characters.slot i) (d.characters.slotTwist i) d.characters.mask p (hmask _)
  have ha (i : Fin k) := frozen_annulus d S C side χ ideal hideal firstSign
    L selection hne annulus hprime i
  have hw := slot_norm_le d E amplitude hprofile
  cases side <;>
    exact T.source.atomicControlOfOriginalWindows C d.base d.base_gt_one rfl
      (d.scale₁_pos false) (d.scale₂_pos false) (fun i => (d.length_pos i).le)
      (fun _ => annulus) (fun _ => amplitude) (fun _ => hannulus) (fun _ => hamplitude)
      (hp _) (hp _) (fun i _ => hs i _) (fun i _ => ha i) (fun i _ => hw i _)
      (fun j p hp => hprime _ p hp) (fun j p _ => hs _ p) (fun j p _ => hw _ p)

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalAtoms

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalAtoms.scales_exponent
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalAtoms.centeredControl
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalAtoms.ordinaryControl
