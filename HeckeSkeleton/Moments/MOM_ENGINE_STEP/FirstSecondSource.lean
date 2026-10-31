import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualFirstSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.GaussStageKernelIntegral

/-!
# The actual parent through both transforms

Every second stage is attached to an actual first common-support,
mask-divisor, residual-divisor and finite phase label. All stages and
their raw profile calibrations precede the continuous parameters. The
first whole-polynomial reduction and the one-pool second reduction are
applied internally, and their integrals are compared using the proved
actual finite-source integrability.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup MeasureTheory

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
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {W E : Type*}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local instance firstSecondSourceCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}

namespace FirstBlockPoolData

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}

def leftDivisorCoefficient (p : FirstBlockPoolData chart P M X hX)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) (i : ι) : ℂ :=
  if S.val ∣ (p.leftData.ideal i).val then
    p.originalLeftCoefficient i * (fixedLeftPhase PUnit χ PUnit.unit : ℂ) else 0

def rightDivisorCoefficient (p : FirstBlockPoolData chart P M X hX)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) (j : κ) : ℂ :=
  if S.val ∣ (p.rightData.ideal j).val then
    p.originalRightCoefficient j * (fixedRightPhase PUnit χ PUnit.unit : ℂ) else 0

/-- Literal main/error stages at every actual first divisor and phase.
There is no bound field; each stage contains only original charts. -/
structure SecondStages (p : FirstBlockPoolData chart P M X hX) where
  left : ∀ S χ, ActualPoolStages (E := E) hΓ μv hDiff
    (p.divisorPools.leftData S) (p.leftDivisorCoefficient S χ) finiteTest
  right : ∀ S χ, ActualPoolStages (E := E) hΓ μv hDiff
    (p.divisorPools.rightData S) (p.rightDivisorCoefficient S χ) finiteTest

namespace SecondStages

variable {p : FirstBlockPoolData chart P M X hX}

structure TerminalCalibration (s : p.SecondStages (E := E) (hDiff := hDiff))
    (sTail sZero : Finset (ℕ × ℕ)) (k : ℕ) (Lmax Nsave decay : ℝ) where
  left : ∀ S χ, (s.left S χ).TerminalCalibration sTail sZero k Lmax Nsave decay
  right : ∀ S χ, (s.right S χ).TerminalCalibration sTail sZero k Lmax Nsave decay

namespace TerminalCalibration

variable {s : p.SecondStages (E := E) (hDiff := hDiff)}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def cost (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ) (ε Cerror Czero : ℝ) : ℝ :=
  ∑ S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val), ‖(moebius S.val : ℂ)‖ *
    ∑ χ : (PUnit × PUnit) →* Circle, ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖ *
      (p.rowBound * Real.sqrt (NL S χ) * Real.sqrt (NR S χ) / 2) *
      ((∫ ξ, (T.left S χ).phaseCost chart.leftPoint ξ ε Cerror Czero / NL S χ
          ∂actualFourierMeasure chart.kernel) +
        ∫ ξ, (T.right S χ).phaseCost (fun j => -chart.rightPoint j) ξ ε Cerror Czero / NR S χ
          ∂actualFourierMeasure chart.kernel)

/-- This substitution lemma is used with the engine's proved universal
pool-stage theorem. The final parent theorem constructs that theorem;
it is not an extra source calibration field. -/
theorem linearized_le_cost
    (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)
    (ε Cerror Czero : ℝ)
    (hstage : ∀ {j : Type*} (d : FirstGaussPoolData C P j) (c : j → ℂ) (x : j → W)
      (s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest)
      (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay) (ξ : W),
      d.energy (FirstGaussPoolData.twistedCoefficient c x ξ) ≤
        T.phaseCost x ξ ε Cerror Czero) :
    p.linearizedCost NL NR ≤ T.cost NL NR ε Cerror Czero := by
  unfold FirstBlockPoolData.linearizedCost firstDivisorLinearizedCost cost
  apply Finset.sum_le_sum
  intro S hS
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro χ hχ
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (norm_nonneg _) (div_nonneg
      (mul_nonneg (mul_nonneg p.rowBound_nonneg (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
      (by norm_num)))
  apply add_le_add
  · apply integral_mono
      ((p.divisorPools.leftData S).normalized_twisted_integrable chart.kernel
        (p.leftDivisorCoefficient S χ) chart.leftPoint (NL S χ))
      (((T.left S χ).phaseCost_integrable chart.kernel chart.leftPoint ε Cerror Czero).div_const _)
    intro ξ
    exact div_le_div_of_nonneg_right
      (hstage _ _ chart.leftPoint (s.left S χ) (T.left S χ) ξ) (hNL S χ).le
  · apply integral_mono
      ((p.divisorPools.rightData S).normalized_twisted_integrable chart.kernel
        (p.rightDivisorCoefficient S χ) (fun j => -chart.rightPoint j) (NR S χ))
      (((T.right S χ).phaseCost_integrable chart.kernel
        (fun j => -chart.rightPoint j) ε Cerror Czero).div_const _)
    intro ξ
    exact div_le_div_of_nonneg_right
      (hstage _ _ (fun j => -chart.rightPoint j) (s.right S χ) (T.right S χ) ξ) (hNR S χ).le

end TerminalCalibration
end SecondStages
end FirstBlockPoolData

variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}

namespace ActualFirstSource

variable (s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX)

abbrev SecondStages := ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
  (s.pools v D).SecondStages (E := E) (hDiff := hDiff)

namespace SecondStages

variable {s} (R : s.SecondStages (E := E) (hDiff := hDiff))

abbrev TerminalCalibration (sTail sZero : Finset (ℕ × ℕ))
    (k : ℕ) (Lmax Nsave decay : ℝ) :=
  ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    (R v D).TerminalCalibration sTail sZero k Lmax Nsave decay

variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def cost (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (N : s.Normalization) (ε Cerror Czero : ℝ) : ℝ :=
  ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
    (T v D).cost (N.left v D) (N.right v D) ε Cerror Czero

end SecondStages
end ActualFirstSource

variable (hΓ μv hDiff)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]
local notation "Lattice" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

include ν μ in
/-- Both actual transforms of the original parent. The constants and
seminorms precede all moving scales, original sources, pool labels and
Fourier variables. Every remaining cost is a genuine second kernel or
one of the two original zero/tail terms. -/
theorem actual_parent_two_stage_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) (Lmax Nsave ξmax : ℝ) (hξmax : 0 < ξmax) :
    ∃ (decay : ℝ) (hdecay : 1 < decay),
      decay = tailDecayForWidth Lmax Nsave ξmax ∧
      firstTailCutoffExponent Lmax Nsave decay ≤ ξmax ∧
    ∃ sFirst sTail sZero : Finset (ℕ × ℕ), ∃ Cfirst Cerror Czero : ℝ,
      0 ≤ Cfirst ∧ 0 ≤ Cerror ∧ 0 < Czero ∧
    ∀ (Z ell eps : ℝ) (bad : Finset (HeightOneSpectrum (𝓞 K)))
      (P : PowerScaleExteriorPool A bad Z ell eps),
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX,
    ∀ N : s.Normalization,
    ∀ R : s.SecondStages (E := E) (hDiff := hDiff),
    ∀ T : R.TerminalCalibration sTail sZero k Lmax Nsave decay,
      pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
        (s.fiber : ℝ) * (s.zeroCost hDiff + R.cost T N ε Cerror Czero +
          Cfirst * X ^ (1 - decay) * s.tailCost sFirst) := by
  obtain ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero, hCerror, hCzero, hpool⟩ :=
    actual_pool_fourier_stage_bound (W := W) (E := E) (ν := ν) (μ := μ) hΓ μv hDiff
      C Drecipe hD finiteTest hlc hcs k ε hε Lmax Nsave ξmax hξmax
  obtain ⟨order, horder⟩ := exists_nat_gt
    (max (Module.finrank ℤ Lattice : ℝ) ((Module.finrank ℚ K : ℝ) * decay))
  have hlattice : Module.finrank ℤ Lattice < order := by
    exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) horder)
  have hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ order :=
    (lt_of_le_of_lt (le_max_right _ _) horder).le
  obtain ⟨sFirst, Cfirst, hCfirst, hparent⟩ :=
    actual_parent_first_linearized (E := W) (ν := ν) (μ := μ) hΓ μv
      C hDiff finiteTest hlc hcs decay hdecay order hlattice hdegree
  refine ⟨decay, hdecay, hchoice, hq, sFirst, sTail, sZero,
    Cfirst, Cerror, Czero, hCfirst, hCerror, hCzero, ?_⟩
  intro Z ell eps bad P ω ψ centered d a t Y₁ Y₂ X hX s N R T
  apply (hparent Z ell eps bad P centered d a t Y₁ Y₂ X hX s N).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg s.fiber)
  apply add_le_add _ le_rfl
  apply add_le_add le_rfl
  unfold ActualFirstSource.linearizedCost ActualFirstSource.SecondStages.cost
  apply Finset.sum_le_sum
  intro v hv
  apply Finset.sum_le_sum
  intro D hD
  exact (T v D).linearized_le_cost (N.left v D) (N.right v D)
    (N.left_pos v D) (N.right_pos v D) ε Cerror Czero
    (fun {j} d c x s T ξ => hpool Z ell eps bad P d c x s T ξ)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_parent_two_stage_bound
