import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualDirectFirstSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondTailBudget

/-!
# Original direct first-source zero and tail terms

The original source supplies the same physical mask, rows and cutoff
as the pooled entrance. Its two terminal bounds use only the original
per-pair profiles and raw norm/tuple windows, independently of any
prime pool or of the number of surviving slots.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckePort.CenteredMomentCounting

set_option maxHeartbeats 2000000

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Z : ℝ}
variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters} {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

namespace ActualDirectFirstSource

variable (s : ActualDirectFirstSource (E := E) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX)

/-- Only the original, pointwise terminal data. In particular the zero
profile condition and its scalar normalization apply before summing over
the common labels or mask divisors. -/
structure TerminalCalibration (sTail sZero : Finset (ℕ × ℕ))
    (k : ℕ) (Lmax Nsave decay : ℝ) where
  productExponent : ℝ
  profileExponent : ℝ
  maskExponent : ℝ
  modulusExponent : ℝ
  tailAmplitude : ℝ
  zeroAmplitude : ℝ
  zeroAmplitude_nonneg : 0 ≤ zeroAmplitude
  windows : FirstTailWindows hΓ C s.columns s.columns s.ideal s.ideal s.block
    sTail s.profiles s.radius s.mask k Z productExponent profileExponent maskExponent
    modulusExponent tailAmplitude
  exponent_bound : firstTailExponent k productExponent profileExponent maskExponent
    modulusExponent ≤ Lmax
  cutoff_eq : X = Z ^ firstTailCutoffExponent Lmax Nsave decay
  profile_zero : ∀ i ∈ s.columns, ∀ j ∈ s.columns, s.profiles i j 0 = 0
  zero_normalization : ∀ v ∈ firstZeroPairs s.columns s.columns s.ideal s.ideal,
    sZero.sup (schwartzSeminormFamily ℂ V ℂ) (s.profiles v.2.1 v.2.2) *
      (∑ D ∈ ((s.block v.1).mask s.mask).powerset, firstZeroDivisorWeight s.radius D) ≤
        zeroAmplitude / Real.sqrt (Z ^ productExponent)

namespace TerminalCalibration

variable {s} {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def cost (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (ε Cerror Czero : ℝ) : ℝ :=
  Czero * T.zeroAmplitude * Z ^ (T.productExponent * ε) +
    Cerror * T.tailAmplitude * Z ^ (-Nsave)

/-- The raw tail windows pay the actual source's computed error mass.
No aggregate tail premise is present. -/
theorem tailCost_bound
    (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (hdecay : 1 < decay) (Ctail : ℝ) (hCtail : 0 ≤ Ctail) :
    Ctail * X ^ (1 - decay) * s.tailCost sTail ≤
      (Ctail * (2 * firstTailFieldConstant K * idealCountConstant K ^ k)) *
        T.tailAmplitude * Z ^ (-Nsave) := by
  let Cnum := 2 * firstTailFieldConstant K * idealCountConstant K ^ k
  let L := firstTailExponent k T.productExponent T.profileExponent T.maskExponent T.modulusExponent
  have hZ0 : 0 ≤ Z := zero_le_one.trans T.windows.base_ge_one
  have hCnum : 0 ≤ Cnum := mul_nonneg
    (mul_nonneg (by norm_num) firstTailFieldConstant_nonneg)
    (pow_nonneg (zero_le_one.trans (one_le_idealCountConstant K)) k)
  have hw := T.windows.power_bound
  change s.tailCost sTail ≤ Cnum * T.tailAmplitude * Z ^ L at hw
  calc
    _ ≤ Ctail * X ^ (1 - decay) * (Cnum * T.tailAmplitude * Z ^ L) :=
      mul_le_mul_of_nonneg_left hw (mul_nonneg hCtail (Real.rpow_nonneg (zero_le_one.trans hX) _))
    _ = (Ctail * Cnum) * T.tailAmplitude * (X ^ (1 - decay) * Z ^ L) := by ring
    _ ≤ (Ctail * Cnum) * T.tailAmplitude * Z ^ (-Nsave) := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (mul_nonneg hCtail hCnum) T.windows.amplitude_nonneg)
      rw [T.cutoff_eq]
      exact first_tail_cutoff_power_of_le Z L Lmax Nsave decay
        T.windows.base_ge_one hdecay T.exponent_bound

end TerminalCalibration
end ActualDirectFirstSource

/-- Uniform control of the literal first zero and tail costs.  The
finite zero seminorms and constant precede every moving first source;
the first-tail seminorms may be those already selected by Poisson. -/
theorem actual_direct_first_terminal_cost_bound
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ sZero : Finset (ℕ × ℕ), ∃ Czero : ℝ, 0 < Czero ∧
    ∀ (sTail : Finset (ℕ × ℕ)) (Ctail : ℝ), 0 ≤ Ctail →
    ∀ (Z : ℝ),
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ (s : ActualDirectFirstSource (E := E) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX)
      (Lmax Nsave decay : ℝ), 1 < decay →
    ∀ (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
      (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
        HeckeGeneral.Characters.localDifferentExponent K v = 0),
      s.zeroCost hDiff + Ctail * X ^ (1 - decay) * s.tailCost sTail ≤
        T.cost ε (Ctail * (2 * firstTailFieldConstant K * idealCountConstant K ^ k)) Czero := by
  obtain ⟨sZero, Czero, hCzero, hz⟩ :=
    first_zero_diagonal_normalized (σ := σ) (η := η) (hS := hS)
      (hΓ := hΓ) (μv := μv) finiteTest k ε hε
  refine ⟨sZero, Czero, hCzero, ?_⟩
  intro sTail Ctail hCtail Z ω ψ centered d a t Y₁ Y₂ X hX s
    Lmax Nsave decay hdecay T hDiff
  have hzero := hz C s.columns s.columns s.ideal s.ideal s.block s.profiles hDiff
    s.radius s.mask X hX T.windows.factors T.windows.factors_injective T.windows.factor_product
    (Z ^ T.productExponent) T.zeroAmplitude
    (Real.one_le_rpow T.windows.base_ge_one T.windows.productExponent_nonneg)
    T.zeroAmplitude_nonneg T.windows.product_norm T.profile_zero T.zero_normalization
  change s.zeroCost hDiff ≤ Czero * T.zeroAmplitude * (Z ^ T.productExponent) ^ ε at hzero
  rw [← Real.rpow_mul (zero_le_one.trans T.windows.base_ge_one)] at hzero
  exact add_le_add hzero (T.tailCost_bound hdecay Ctail hCtail)


end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.TerminalCalibration.tailCost_bound
#print axioms HeckeSkeleton.Moments.EngineStep.actual_direct_first_terminal_cost_bound
