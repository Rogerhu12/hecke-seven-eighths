import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolSecondStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.StageTerminalBudget

/-!
# Terminal budgets for every output of the same actual pool

Each terminal calibration consists of original pointwise profile bounds,
the actual whole-factor encoding, and the prescribed common cutoff.
The main source and the three valuation sources are those constructed by
`FirstGaussPoolData`; their energies are never assumed bounded.

The final theorem applies the actual second source separately and then
uses the proved exact one-pool identity. It retains one density, one main
fiber factor, and the literal local weights for valuations 1, 6, and 7.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory HeckePort.Moments

set_option maxHeartbeats 3000000

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K

namespace ActualGaussStage

variable {hΓ μv hDiff}
variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

/-- Raw, per-source terminal data. `windows` supplies individual
seminorm and norm bounds with a proved finite whole-factor fibre.
Residual sources use the actual valuation-allocation multiplicity.
`zero_normalization` is an original pair scalar bound. Neither field
asserts an energy, transformed-source, or summed-terminal estimate. -/
structure TerminalCalibration
    (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
    (sTail sZero : Finset (ℕ × ℕ)) (k : ℕ) (Z Lmax Nsave decay : ℝ) where
  productExponent : ℝ
  profileExponent : ℝ
  maskExponent : ℝ
  inverseRadiusExponent : ℝ
  tailAmplitude : ℝ
  zeroAmplitude : ℝ
  zeroAmplitude_nonneg : 0 ≤ zeroAmplitude
  windows : SecondTailWindows C G.columns G.columns G.ideal G.ideal
    (fun DE : FirstZeroLabel G.columns G.columns G.ideal G.ideal =>
      canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property)
    sTail (fun i j => (G.coefficient i * star (G.coefficient j)) • s.profile)
    s.radius s.mask k Z productExponent profileExponent maskExponent inverseRadiusExponent
    tailAmplitude
  exponent_bound : secondTailExponent k productExponent profileExponent maskExponent
    inverseRadiusExponent ≤ Lmax
  cutoff_eq : s.cutoff = Z ^ firstTailCutoffExponent Lmax Nsave decay
  profile_zero : s.profile 0 = 0
  zero_normalization : ∀ v ∈ firstZeroPairs G.columns G.columns G.ideal G.ideal,
    sZero.sup (schwartzSeminormFamily ℂ V ℂ)
      ((G.coefficient v.2.1 * star (G.coefficient v.2.2)) • s.profile) *
      A.exteriorNorm (G.ideal v.2.1) *
      (∑ D ∈ s.mask.powerset, firstZeroDivisorWeight s.radius D) ≤
        zeroAmplitude / Real.sqrt (Z ^ productExponent)

namespace TerminalCalibration

variable {s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Z Lmax Nsave decay : ℝ}

/-- Only the genuine nonzero kernel sum remains after both terminal
terms have been bounded. The individual normalization amplitudes stay
visible for the outer common-measure budget. -/
def cost (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (ε Cerror Czero : ℝ) : ℝ :=
  (s.fiber : ℝ) * (Czero * (T.windows.multiplicity * T.zeroAmplitude) * Z ^ (T.productExponent * ε) +
    (∑ DE, ∑ D : s.mask.powerset, (s.charts DE D).kernelCost s.mask s.cutoff s.cutoff_one) +
    Cerror * (T.windows.multiplicity * T.tailAmplitude) * Z ^ (-Nsave))

end TerminalCalibration
end ActualGaussStage

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- Uniform terminal control of every genuine Gauss source, with a
fixed small physical cutoff chosen before all moving source data. -/
theorem actual_gauss_stage_terminal_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) (Lmax Nsave ξ : ℝ) (hξ : 0 < ξ) :
    ∃ (decay : ℝ) (hdecay : 1 < decay),
      decay = tailDecayForWidth Lmax Nsave ξ ∧
      firstTailCutoffExponent Lmax Nsave decay ≤ ξ ∧
    ∃ sTail sZero : Finset (ℕ × ℕ), ∃ Cerror Czero : ℝ, 0 ≤ Cerror ∧ 0 < Czero ∧
    ∀ (Z : ℝ) {ι : Type*} (G : ActualGaussSource C ι)
      (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
      (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay),
      s.cutoff ≤ Z ^ ξ ∧ G.energy hDiff ≤ T.cost ε Cerror Czero := by
  obtain ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero, hCerror, hCzero, hbound⟩ :=
    gauss_second_stage_terminal_bound (E := E) (hΓ := hΓ) (μv := μv) (ν := ν) (μ := μ)
      C hDiff Drecipe hD finiteTest hlc hcs k ε hε Lmax Nsave ξ hξ
  refine ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero, hCerror, hCzero, ?_⟩
  intro Z ι G s T
  have hb := hbound Z G.rows (engineElementOrbit (Γ := Γ)) (fun _ => 1)
    G.columns G.coefficient G.ideal G.generator G.generates
    (fun i hi => ⟨Units.mk0 (G.generator i : K) (by exact_mod_cast (G.generates i).1),
      rfl, G.allowed i hi⟩)
    s.profile s.radius s.mask T.productExponent T.profileExponent T.maskExponent
    T.inverseRadiusExponent T.tailAmplitude T.windows T.exponent_bound s.charts
    T.zeroAmplitude T.zeroAmplitude_nonneg T.profile_zero T.zero_normalization
    s.fiber s.calibration
  refine ⟨?_, ?_⟩
  · simpa only [T.cutoff_eq] using hb.1
  · rw [G.energy_eq_orbital hΓ hDiff]
    simpa only [ActualGaussStage.TerminalCalibration.cost, T.cutoff_eq] using hb.2

include ν μ in
/-- The actual main and 1/6/7 errors use exactly the original pool and
one density. Each summand's zero and tail are discharged from its own
raw original profile data, never from an assumed aggregate budget. -/
theorem pool_second_stage_terminal_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) (Lmax Nsave ξ : ℝ) (hξ : 0 < ξ) :
    ∃ (decay : ℝ) (hdecay : 1 < decay),
      decay = tailDecayForWidth Lmax Nsave ξ ∧
      firstTailCutoffExponent Lmax Nsave decay ≤ ξ ∧
    ∃ sTail sZero : Finset (ℕ × ℕ), ∃ Cerror Czero : ℝ, 0 ≤ Cerror ∧ 0 < Czero ∧
    ∀ (Z ell eps : ℝ) (bad : Finset (HeightOneSpectrum (𝓞 K)))
      (P : PowerScaleExteriorPool A bad Z ell eps),
    ∀ {ι : Type*} (d : FirstGaussPoolData C P ι) (c : ι → ℂ),
    ∀ main : ActualGaussStage (E := E) hΓ μv hDiff (d.mainSource c) finiteTest,
    ∀ errorOne : ∀ p : P.primes,
      ActualGaussStage (E := E) hΓ μv hDiff (d.residualSource p.val 1 c) finiteTest,
    ∀ errorSix : ∀ p : P.primes,
      ActualGaussStage (E := E) hΓ μv hDiff (d.residualSource p.val 6 c) finiteTest,
    ∀ errorSeven : ∀ p : P.primes,
      ActualGaussStage (E := E) hΓ μv hDiff (d.residualSource p.val 7 c) finiteTest,
    ∀ mainT : main.TerminalCalibration sTail sZero k Z Lmax Nsave decay,
    ∀ oneT : ∀ p : P.primes, (errorOne p).TerminalCalibration sTail sZero k Z Lmax Nsave decay,
    ∀ sixT : ∀ p : P.primes, (errorSix p).TerminalCalibration sTail sZero k Z Lmax Nsave decay,
    ∀ sevenT : ∀ p : P.primes, (errorSeven p).TerminalCalibration sTail sZero k Z Lmax Nsave decay,
    d.energy c ≤ (4 / d.density) *
      (d.multiplicity * mainT.cost ε Cerror Czero +
        (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 1 *
          (oneT p).cost ε Cerror Czero) +
        (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 6 *
          (sixT p).cost ε Cerror Czero) +
        (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 7 *
          (sevenT p).cost ε Cerror Czero)) := by
  obtain ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero, hCerror, hCzero, hbound⟩ :=
    actual_gauss_stage_terminal_bound (E := E) (ν := ν) (μ := μ) hΓ μv hDiff
      C Drecipe hD finiteTest hlc hcs k ε hε Lmax Nsave ξ hξ
  refine ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero, hCerror, hCzero, ?_⟩
  intro Z ell eps bad P ι d c main errorOne errorSix errorSeven mainT oneT sixT sevenT
  rw [d.energy_eq_sources hDiff Drecipe hD c]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) d.density_pos.le)
  apply add_le_add
  · apply add_le_add
    · apply add_le_add
      · exact mul_le_mul_of_nonneg_left (hbound Z _ main mainT).2 d.multiplicity_nonneg
      · exact Finset.sum_le_sum fun p _ =>
          mul_le_mul_of_nonneg_left (hbound Z _ (errorOne p) (oneT p)).2
            (FirstGaussPoolData.localErrorWeight_nonneg p.val 1)
    · exact Finset.sum_le_sum fun p _ =>
        mul_le_mul_of_nonneg_left (hbound Z _ (errorSix p) (sixT p)).2
          (FirstGaussPoolData.localErrorWeight_nonneg p.val 6)
  · exact Finset.sum_le_sum fun p _ =>
      mul_le_mul_of_nonneg_left (hbound Z _ (errorSeven p) (sevenT p)).2
        (FirstGaussPoolData.localErrorWeight_nonneg p.val 7)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_gauss_stage_terminal_bound
#print axioms HeckeSkeleton.Moments.EngineStep.pool_second_stage_terminal_bound
