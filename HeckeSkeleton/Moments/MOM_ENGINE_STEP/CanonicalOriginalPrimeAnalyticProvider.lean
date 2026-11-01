import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalNormalizedPrimeAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalHeckePrimeAnalytic

/-!
# Original single-character analytic input

The independent prime input is quantified over the original moving
elements, correction, slot character, sector and complete deletion mask.
Its height constant is chosen before the scale and all of these data.
It supplies analytic data for the actual Hecke continuation, without a
prime-sum, source, descendant or moment estimate.

The actual-row adapter uses the original paired-row exclusion. Only the
inverse of the displayed slot must belong to the original finite set;
closure of that whole set under inversion is unnecessary. At kappa one
the existing absolute prime estimate applies, so this input is used only
when kappa is strictly below one.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open PrimeCancellation.Analytic

namespace CanonicalOriginalPrimeAnalyticProvider

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

/-- The raw analytic window precedes every source and allocation. The
complete original mask, including the remaining ideal, pays the height
of the displayed nonprincipal character. -/
def Window (theta : Finset (HeckeCharacter K)) (normBox heightC : ℝ) : Prop :=
  ∀ κ : ℝ, 3 / 4 ≤ κ → κ < 1 →
    ∀ Z : ℝ, 1 < Z → FiniteOrderBoundary (K := K) ((κ + 1) / 2) →
    ∀ (moving : OriginalMovingFactors A P R) (correction slot : HeckeCharacter K)
      (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (remaining u : HeckeGeneral.Analysis.NonzeroIdeal K),
    (correction = 1 ∨ correction ∈ theta) → slot ∈ theta →
    completeIdealIsExterior K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u →
    CanonicalNormalizedPrimeAtoms.originalCharacter moving correction slot sector u ≠ 1 →
    idealNorm K u * idealNorm K (moving.fullMaskSupport remaining) ≤ Z ^ normBox →
    ∃ analytic : ZeroFreeData
        (heckeContinuation K
          (CanonicalNormalizedPrimeAtoms.originalCharacter moving correction slot sector u))
        ((κ + 1) / 2),
      heightConstant analytic + 3 * (analytic.k : ℝ) ≤ heightC * (1 + Real.log Z)

/-- The independent MOM_PRIME analytic input. Its constant is chosen
after the fixed norm box and before kappa, scale and moving arithmetic. -/
def Provider (theta : Finset (HeckeCharacter K)) : Prop :=
  ∀ normBox : ℝ, 0 ≤ normBox →
    ∃ heightC : ℝ, 0 < heightC ∧
      Window (A := A) (P := P) (R := R) theta normBox heightC

/-- Positive slot length selects the actual theta exclusion in
`pairedRows`; only this slot's inverse membership is needed. -/
theorem slot_character_ne_one_of_inverse_mem {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (a : RealParameters) (Z : ℝ)
    (hz : a.z = d.geometry.totalLength)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (hu : u ∈ pairedRows d a Z)
    (i : Fin d.geometry.slotCount) (hinverse : (d.slotCoefficient i)⁻¹ ∈ d.theta) :
    d.rowCharacter u * d.slotCoefficient i ≠ 1 := by
  have hi : (d.geometry.slots i).length ≤ d.geometry.totalLength :=
    Finset.single_le_sum (fun j _ => (d.geometry.slots j).length_pos.le)
      (Finset.mem_univ i)
  have hzpos : 0 < a.z := by
    rw [hz]
    exact (d.geometry.slots i).length_pos.trans_le hi
  have hnot : d.rowCharacter u ∉ d.theta := by
    have h := (Finset.mem_filter.mp hu).2
    simpa only [if_neg hzpos.ne'] using h
  intro hone
  have heq : d.rowCharacter u = (d.slotCoefficient i)⁻¹ := by
    calc
      d.rowCharacter u = (d.rowCharacter u * d.slotCoefficient i) *
          (d.slotCoefficient i)⁻¹ := by simp only [mul_assoc, mul_inv_cancel, mul_one]
      _ = (d.slotCoefficient i)⁻¹ := by rw [hone, one_mul]
  exact hnot (heq.symm ▸ hinverse)

namespace Window

variable {theta : Finset (HeckeCharacter K)} {normBox heightC : ℝ}
variable {ω ψ : HeckeCharacter K} {X : Type*}
variable {data : X → MomentData K ω ψ}

/-- The actual slot certificate follows from the original row and full
mask budget. No analytic certificate for a constructed source is a
premise of this adapter. -/
theorem exists_certificate
    (window : Window (A := A) (P := P) (R := R) theta normBox heightC)
    (recipe : CompleteMovingRowRecipe A P R data)
    (a : RealParameters) (Z : ℝ)
    (hκlo : 3 / 4 ≤ a.κ) (hκlt : a.κ < 1) (hZ : 1 < Z)
    (boundary : FiniteOrderBoundary (K := K) ((a.κ + 1) / 2))
    (htheta : ∀ ξ, (data ξ).theta = theta)
    (hslot : ∀ ξ i, (data ξ).slotCoefficient i ∈ theta)
    (hinverse : ∀ ξ i, ((data ξ).slotCoefficient i)⁻¹ ∈ theta)
    (hz : ∀ ξ, a.z = (data ξ).geometry.totalLength)
    (hjoint : recipe.FullJointBudget Z normBox)
    (ξ : X) (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hu : u ∈ pairedRows (data ξ) a Z) (i : Fin (data ξ).geometry.slotCount) :
    ∃ analytic : ZeroFreeData
        (heckeContinuation K ((data ξ).rowCharacter u * (data ξ).slotCoefficient i))
        ((a.κ + 1) / 2),
      heightConstant analytic + 3 * (analytic.k : ℝ) ≤ heightC * (1 + Real.log Z) := by
  have hallowed : (data ξ).allowedRow u :=
    (((data ξ).rows_spec _ u).mp (Finset.mem_filter.mp hu).1).1
  have hcorrection : recipe.correction = 1 ∨ recipe.correction ∈ theta := by
    simpa only [htheta ξ] using recipe.correction_mem ξ
  have hslotInverse : ((data ξ).slotCoefficient i)⁻¹ ∈ (data ξ).theta := by
    rw [htheta ξ]
    exact hinverse ξ i
  have hcharacter :
      CanonicalNormalizedPrimeAtoms.originalCharacter recipe.moving recipe.correction
          ((data ξ).slotCoefficient i) (recipe.sector u) u =
        (data ξ).rowCharacter u * (data ξ).slotCoefficient i := by
    rw [CanonicalNormalizedPrimeAtoms.originalCharacter, ← recipe.character ξ u hallowed]
  have hnonprincipal :
      CanonicalNormalizedPrimeAtoms.originalCharacter recipe.moving recipe.correction
        ((data ξ).slotCoefficient i) (recipe.sector u) u ≠ 1 := by
    rw [hcharacter]
    exact slot_character_ne_one_of_inverse_mem (data ξ) a Z (hz ξ) u hu i hslotInverse
  have h := window a.κ hκlo hκlt Z hZ boundary recipe.moving recipe.correction
    ((data ξ).slotCoefficient i) (recipe.sector u) recipe.remaining u
    hcorrection (hslot ξ i) (recipe.exterior ξ u hallowed) hnonprincipal
    (hjoint ξ u hallowed)
  simpa only [hcharacter] using h

/-- A selected single-character certificate with its height bound. The
selection ranges only over the raw analytic input, not over children. -/
def certificate
    (window : Window (A := A) (P := P) (R := R) theta normBox heightC)
    (recipe : CompleteMovingRowRecipe A P R data)
    (a : RealParameters) (Z : ℝ)
    (hκlo : 3 / 4 ≤ a.κ) (hκlt : a.κ < 1) (hZ : 1 < Z)
    (boundary : FiniteOrderBoundary (K := K) ((a.κ + 1) / 2))
    (htheta : ∀ ξ, (data ξ).theta = theta)
    (hslot : ∀ ξ i, (data ξ).slotCoefficient i ∈ theta)
    (hinverse : ∀ ξ i, ((data ξ).slotCoefficient i)⁻¹ ∈ theta)
    (hz : ∀ ξ, a.z = (data ξ).geometry.totalLength)
    (hjoint : recipe.FullJointBudget Z normBox)
    (ξ : X) (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hu : u ∈ pairedRows (data ξ) a Z) (i : Fin (data ξ).geometry.slotCount) :
    {analytic : ZeroFreeData
        (heckeContinuation K ((data ξ).rowCharacter u * (data ξ).slotCoefficient i))
        ((a.κ + 1) / 2) //
      heightConstant analytic + 3 * (analytic.k : ℝ) ≤ heightC * (1 + Real.log Z)} :=
  Classical.indefiniteDescription _
    (window.exists_certificate recipe a Z hκlo hκlt hZ boundary
      htheta hslot hinverse hz hjoint ξ u hu i)

end Window
end CanonicalOriginalPrimeAnalyticProvider
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalPrimeAnalyticProvider.slot_character_ne_one_of_inverse_mem
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalPrimeAnalyticProvider.Window.exists_certificate
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalPrimeAnalyticProvider.Window.certificate
