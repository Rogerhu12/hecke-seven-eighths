import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualFirstTerminalBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.RawSourcePhaseIntegral

/-!
# The actual parent reaches both raw Poisson sources

The original whole parent is reduced internally through the first
common-support transform, the one original prime pool, and every genuine
second transform.  Physical zero and tail terms are paid from their
original individual profiles and factor windows.  The remaining finite
second row sums are retained before Cauchy, so actual exceptional rows
and occurrence-support branches may be separated correctly.

The statements introduce no whole-source inequality or two-transform
identity as calibration data.
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
local instance : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}

namespace FirstBlockPoolData

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap V ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}

namespace SecondStages
namespace TerminalCalibration

variable {p : FirstBlockPoolData chart P M X hX}
variable {s : p.SecondStages (E := E) (hDiff := hDiff)}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def rawCost (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ) (ε Cerror Czero : ℝ) : ℝ :=
  ∑ S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val), ‖(moebius S.val : ℂ)‖ *
    ∑ χ : (PUnit × PUnit) →* Circle, ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖ *
      (p.rowBound * Real.sqrt (NL S χ) * Real.sqrt (NR S χ) / 2) *
      ((∫ ξ, (T.left S χ).rawPhaseCost chart.leftPoint ξ ε Cerror Czero / NL S χ
          ∂actualFourierMeasure chart.kernel) +
        ∫ ξ, (T.right S χ).rawPhaseCost (fun j => -chart.rightPoint j) ξ ε Cerror Czero / NR S χ
          ∂actualFourierMeasure chart.kernel)

/-- This substitution lemma is used with the engine's proved universal
pool-stage theorem. The final parent theorem constructs that theorem;
it is not an extra source calibration field. -/
theorem linearized_le_rawCost
    (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)
    (ε Cerror Czero : ℝ)
    (hstage : ∀ {j : Type*} (d : FirstGaussPoolData C P j) (c : j → ℂ) (x : j → W)
      (s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest)
      (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay) (ξ : W),
      d.energy (FirstGaussPoolData.twistedCoefficient c x ξ) ≤
        T.rawPhaseCost x ξ ε Cerror Czero) :
    p.linearizedCost NL NR ≤ T.rawCost NL NR ε Cerror Czero := by
  unfold FirstBlockPoolData.linearizedCost firstDivisorLinearizedCost rawCost
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
      (((T.left S χ).rawPhaseCost_integrable chart.kernel chart.leftPoint ε Cerror Czero).div_const _)
    intro ξ
    exact div_le_div_of_nonneg_right
      (hstage _ _ chart.leftPoint (s.left S χ) (T.left S χ) ξ) (hNL S χ).le
  · apply integral_mono
      ((p.divisorPools.rightData S).normalized_twisted_integrable chart.kernel
        (p.rightDivisorCoefficient S χ) (fun j => -chart.rightPoint j) (NR S χ))
      (((T.right S χ).rawPhaseCost_integrable chart.kernel
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

namespace ActualFirstSource.SecondStages

variable {s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}
variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def rawCost (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (N : s.Normalization) (ε Cerror Czero : ℝ) : ℝ :=
  ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
    (T v D).rawCost (N.left v D) (N.right v D) ε Cerror Czero

end ActualFirstSource.SecondStages

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
Fourier variables. Every remaining cost is a literal second finite row sum or
one of the two original zero/tail terms. -/
theorem actual_parent_two_stage_raw_bound
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
        (s.fiber : ℝ) * (s.zeroCost hDiff + R.rawCost T N ε Cerror Czero +
          Cfirst * X ^ (1 - decay) * s.tailCost sFirst) := by
  obtain ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero, hCerror, hCzero, hpool⟩ :=
    actual_pool_raw_fourier_stage_bound (W := W) (E := E) (ν := ν) (μ := μ) hΓ μv hDiff
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
  apply add_le_add_right
  apply add_le_add_left
  unfold ActualFirstSource.linearizedCost ActualFirstSource.SecondStages.rawCost
  apply Finset.sum_le_sum
  intro v hv
  apply Finset.sum_le_sum
  intro D hD
  exact (T v D).linearized_le_rawCost (N.left v D) (N.right v D)
    (N.left_pos v D) (N.right_pos v D) ε Cerror Czero
    (fun {j} d c x s T ξ => hpool Z ell eps bad P d c x s T ξ)


include ν μ in
/-- Both actual zero terms and both physical tails are paid internally,
while the genuine nonzero second source remains before row Cauchy.  The
same small cutoff is used by the subsequent actual hybrid reduction. -/
theorem actual_parent_two_stage_raw_terminal_bound
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
    ∃ sFirst sFirstZero sTail sZero : Finset (ℕ × ℕ),
    ∃ CfirstError CfirstZero Cerror Czero : ℝ,
      0 ≤ CfirstError ∧ 0 < CfirstZero ∧ 0 ≤ Cerror ∧ 0 < Czero ∧
    ∀ (Z ell eps : ℝ) (bad : Finset (HeightOneSpectrum (𝓞 K)))
      (P : PowerScaleExteriorPool A bad Z ell eps),
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX,
    ∀ N : s.Normalization,
    ∀ R : s.SecondStages (E := E) (hDiff := hDiff),
    ∀ T : R.TerminalCalibration sTail sZero k Lmax Nsave decay,
    ∀ F : s.TerminalCalibration sFirst sFirstZero k Lmax Nsave decay,
      X ≤ Z ^ ξmax ∧
      pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
        (s.fiber : ℝ) * (F.cost ε CfirstError CfirstZero + R.rawCost T N ε Cerror Czero) := by
  obtain ⟨decay, hdecay, hchoice, hq, sFirst, sTail, sZero,
    Cfirst, Cerror, Czero, hCfirst, hCerror, hCzero, hparent⟩ :=
    actual_parent_two_stage_raw_bound (W := W) (E := E) (ν := ν) (μ := μ)
      hΓ μv hDiff C Drecipe hD finiteTest hlc hcs k ε hε Lmax Nsave ξmax hξmax
  obtain ⟨sFirstZero, CfirstZero, hCfirstZero, hterminal⟩ :=
    actual_first_terminal_cost_bound (E := W) (C := C) (hΓ := hΓ) (μv := μv)
      finiteTest k ε hε
  let Cnum := 2 * firstTailFieldConstant K * HeckePort.CenteredMomentCounting.idealCountConstant K ^ k
  have hCnum : 0 ≤ Cnum := mul_nonneg
    (mul_nonneg (by norm_num) firstTailFieldConstant_nonneg)
    (pow_nonneg (zero_le_one.trans (HeckePort.CenteredMomentCounting.one_le_idealCountConstant K)) k)
  refine ⟨decay, hdecay, hchoice, hq, sFirst, sFirstZero, sTail, sZero,
    Cfirst * Cnum, CfirstZero, Cerror, Czero, mul_nonneg hCfirst hCnum,
    hCfirstZero, hCerror, hCzero, ?_⟩
  intro Z ell eps bad P ω ψ centered d a t Y₁ Y₂ X hX s N R T F
  have hp := hparent Z ell eps bad P centered d a t Y₁ Y₂ X hX s N R T
  have ht := hterminal sFirst Cfirst hCfirst Z ell eps bad P
    centered d a t Y₁ Y₂ X hX s Lmax Nsave decay hdecay F hDiff
  refine ⟨?_, hp.trans ?_⟩
  · rw [F.cutoff_eq]
    exact Real.rpow_le_rpow_of_exponent_le F.windows.base_ge_one hq
  · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg s.fiber)
    convert add_le_add_right ht (R.rawCost T N ε Cerror Czero) using 1 <;> ring

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_parent_two_stage_raw_bound
#print axioms HeckeSkeleton.Moments.EngineStep.actual_parent_two_stage_raw_terminal_bound
