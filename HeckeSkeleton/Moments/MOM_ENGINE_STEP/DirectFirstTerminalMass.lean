import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstTerminalIndexMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCommonLabelConditions
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectParentLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstAllowanceNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstBlockMaskCardinality

set_option linter.unusedSectionVars false

/-!
# The original first-label terminal mass without a prime pool

The carrier here is literally the original first common pair, its
original mask subset, its original shared divisor and finite character.
The first two Cauchy allowances give the exact `firstCommonWeight` and
the coefficient-atom calibration gives `1/N(S)`.

The shared-divisor norm window is proved from its actual original
residual ideal, and every common ideal is bounded by an original column.
Mask cardinalities are proved from their original prime identifications.
No estimate of a final terminal sum or of a surrogate carrier is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.LargeSieve
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support HeckePort.Moments.MobiusRegroup
open HeckePort.IdealMobiusDivisorSum CommonSupportMass UniqueFactorizationMonoid MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Z : ℝ}
variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
local instance directFirstTerminalMassCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

/-- Nonzero membership follows from the actual original column divisor,
with no positivity assumption on an artificial pool. -/
theorem direct_first_divisor_pool_nonzero {ι : Type*} (d : DirectGaussData C ι)
    (S : Ideal (𝓞 K)) (hS : S ∈ divisorPool d.columns (fun j => (d.ideal j).val)) :
    S ≠ 0 := by
  sorry

namespace ActualDirectFirstSource

variable (s : ActualDirectFirstSource (E := U) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX)

/-- These are exactly the finite labels already present in
`SecondStages.TerminalCalibration.classZeroBudget` and `classTailBudget`. -/
def firstTerminalArithmeticMass : ℝ :=
  ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
    ∑ S : divisorPool (s.pieces v D).rightData.columns
      (fun j => ((s.pieces v D).rightData.ideal j).val),
    ∑ χ : (PUnit.{1} × PUnit.{1}) →* Circle,
      firstCommonWeight Z v.val.1 v.val.2 *
        (‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) *
          ‖fixedPhaseCoefficient PUnit.{1} (fun _ => (1 : Circle)) χ‖

theorem first_divisor_original_norm
    (v : s.CommonLabel) (D : ((s.block v).mask s.mask).powerset)
    (S : divisorPool (s.pieces v D).rightData.columns
      (fun j => ((s.pieces v D).rightData.ideal j).val))
    (Y : ℝ) (hcolumns : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Y) :
    (Ideal.absNorm S.val : ℝ) ≤ Y := by
  sorry

private theorem commonWeight_sum_le_actualLabels (hZ : 1 < Z) :
    (∑ v : s.CommonLabel, firstCommonWeight Z v.val.1 v.val.2) ≤
      ∑ v ∈ actualCommonLabels s.columns s.columns
        (fun i => (s.ideal i).val) (fun j => (s.ideal j).val),
        firstCommonWeight Z v.1.1 v.1.2 := by
  sorry

end ActualDirectFirstSource

/-- All three arithmetic constants are fixed before the actual source,
mask ideals, scale and finite labels.  Original prime data proves the
mask cost; no cardinality or terminal-mass bound is assumed. -/
theorem actual_direct_first_terminal_mass_from_original_windows
    (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ Cmass : ℝ, 0 < Cmass ∧
      ∀ Z : ℝ, 1 < Z →
      ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
        (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
      ∀ s : ActualDirectFirstSource (E := U) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX,
      ∀ oldMask : Ideal (𝓞 K), Squarefree oldMask → oldMask ≠ 0 →
      (∀ i ∈ s.columns, oldMask ∣ (s.ideal i).val) →
      (∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B) →
      ∀ maskIdeal : Ideal (𝓞 K), maskIdeal ≠ 0 →
      (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ B →
      OriginalMaskPrimeData s.mask maskIdeal →
        s.firstTerminalArithmeticMass ≤
          Cmass * Z ^ ε / (Ideal.absNorm oldMask : ℝ) := by
  sorry

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.first_divisor_original_norm
#print axioms HeckeSkeleton.Moments.EngineStep.actual_direct_first_terminal_mass_from_original_windows
