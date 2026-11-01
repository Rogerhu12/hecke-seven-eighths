import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualExceptionalBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ReductionOutput

/-!
# The exceptional remainder from the original parent domain

The padded core belongs to the original parent, before either transform
or any choice of child. It controls the positive part of the original
total-length excess for every slot count. The remaining individual
dyadic, width, atomic and frozen-slot errors are assigned fixed portions
of the requested loss. No final exceptional-energy bound is an input.

The arithmetic index sum adds its three fixed small powers, the one pool
loss when present and the actual divisor mesh. The direct entrance uses
the same numerical ledger with pool loss zero.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStep

open NumberField HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

namespace PairedEngineDomain

variable {centered : Bool} {d : MomentData K ω ψ} {a : RealParameters}
variable {Z Y₁ Y₂ floor padding : ℝ}
variable (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding)

/-- The exact original total length, including every original slot,
has padded excess at most the original padding. -/
theorem original_total_excess_le (hpadding : 0 ≤ padding) :
    max (a.n₁ + a.n₂ + a.z - (a.m + a.q)) 0 ≤ padding := by
  exact max_le (by linarith [domain.padded_core]) hpadding

/-- A numerical label which records that same original total length
inherits the bound without a case split on the number of slots. -/
theorem labelled_total_excess_le (Aexp : ℝ)
    (hA : Aexp = a.n₁ + a.n₂ + a.z) (hpadding : 0 ≤ padding) :
    max (Aexp - (a.m + a.q)) 0 ≤ padding := by
  rw [hA]
  exact domain.original_total_excess_le hpadding

end PairedEngineDomain

namespace ExceptionalOriginalNumbers

/-- The `final_remainder` field of the original atom datum is obtained
from the original parent domain and five separate original error
windows. The margin reserves half the requested loss for the subsequent
actual arithmetic index sum. -/
theorem remainder_from_original_parent
    (n : ExceptionalOriginalNumbers)
    {centered : Bool} {d : MomentData K ω ψ} {a : RealParameters}
    {Z Y₁ Y₂ floor padding : ℝ}
    (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding)
    (hA : n.Aexp = a.n₁ + a.n₂ + a.z) (hpadding : 0 ≤ padding)
    (step loss volumeLoss movingLength : ℝ) (hloss : 0 ≤ loss)
    (hremaining : n.remaining ≤ movingLength + loss / 16)
    (hwidth : n.widthError ≤ loss / 16)
    (hstep : n.stepσ ≤ step) (hdyadic : n.δ ≤ loss / 16)
    (hvolume : volumeLoss ≤ loss / 16) (hslot : n.slotError ≤ loss / 16) :
    n.remaining + n.widthError +
      (max (n.Aexp - (a.m + a.q)) 0 + 3 * n.stepσ +
        5 * n.δ / 6 + volumeLoss + n.slotError) ≤
      (padding + 3 * step + loss / 2) + movingLength := by
  have htotal := domain.labelled_total_excess_le n.Aexp hA hpadding
  linarith

end ExceptionalOriginalNumbers

/-- The actual image-fibre, harmonic and divisor-mesh errors all use
fixed portions of the requested loss. The one amplifier density loss
is counted once. This is the exponent produced by the literal full
exceptional-budget theorem. -/
theorem original_exceptional_global_exponent
    (padding step loss δ₁ δ₂ δ₃ poolLoss mesh : ℝ) (hloss : 0 ≤ loss)
    (h₁ : δ₁ ≤ loss / 16) (h₂ : δ₂ ≤ loss / 16) (h₃ : δ₃ ≤ loss / 16)
    (hpool : poolLoss ≤ loss / 16) (hmesh : mesh ≤ loss / 16) :
    (padding + 3 * step + loss / 2) + δ₁ + δ₂ + δ₃ + poolLoss + mesh ≤
      padding + 3 * step + loss := by
  linarith

/-- The pool-free source has precisely the same original error budget;
no positive auxiliary pool is introduced to obtain its exponent. -/
theorem original_direct_exceptional_global_exponent
    (padding step loss δ₁ δ₂ δ₃ mesh : ℝ) (hloss : 0 ≤ loss)
    (h₁ : δ₁ ≤ loss / 16) (h₂ : δ₂ ≤ loss / 16) (h₃ : δ₃ ≤ loss / 16)
    (hmesh : mesh ≤ loss / 16) :
    (padding + 3 * step + loss / 2) + δ₁ + δ₂ + δ₃ + mesh ≤
      padding + 3 * step + loss := by
  simpa only [add_zero] using
    original_exceptional_global_exponent padding step loss δ₁ δ₂ δ₃ 0 mesh hloss
      h₁ h₂ h₃ (by linarith) hmesh

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.PairedEngineDomain.original_total_excess_le
#print axioms HeckeSkeleton.Moments.EngineStep.ExceptionalOriginalNumbers.remainder_from_original_parent
#print axioms HeckeSkeleton.Moments.EngineStep.original_exceptional_global_exponent
#print axioms HeckeSkeleton.Moments.EngineStep.original_direct_exceptional_global_exponent
