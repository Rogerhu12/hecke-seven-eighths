import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualGaussRawTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolFourierStage

/-!
# One-pool Fourier reduction retaining the raw second source

The actual main source and all valuation 1/6/7 sources have their zero
and tail terms paid before any Cauchy step on the second rows.  The same
original pool, density and local difference weights remain explicit.
Every source is fixed before the first Fourier variable; its terminal
calibration is transported by the genuine unit Gram multiplier.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory

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
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}

variable {hΓ μv hDiff}
variable {d : FirstGaussPoolData C P ι} {c : ι → ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

namespace ActualPoolStages.TerminalCalibration

variable {s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

/-- The same original pool and exact local error weights, retaining the
raw nonzero second source for its subsequent hybrid row partition. -/
def rawPhaseCost
    (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (x : ι → W) (ξ : W) (ε Cerror Czero : ℝ) : ℝ :=
  (4 / d.density) *
    (d.multiplicity * (T.main.fourierPhase x ξ).rawCost ε Cerror Czero +
      (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 1 *
        ((T.one p).fourierPhase (fun i => x i.val) ξ).rawCost ε Cerror Czero) +
      (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 6 *
        ((T.six p).fourierPhase (fun i => x i.val) ξ).rawCost ε Cerror Czero) +
      (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 7 *
        ((T.seven p).fourierPhase (fun i => x i.val) ξ).rawCost ε Cerror Czero))

end ActualPoolStages.TerminalCalibration

variable (hΓ μv hDiff)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- All constants and raw stages precede the two continuous parameters.
The first phase is then transported exactly, and the actual second
transform proves the bound for the whole pooled energy. -/
theorem actual_pool_raw_fourier_stage_bound
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
    ∃ sTail sZero : Finset (ℕ × ℕ), ∃ Cerror Czero : ℝ, 0 ≤ Cerror ∧ 0 < Czero ∧
    ∀ (Z ell eps : ℝ) (bad : Finset (HeightOneSpectrum (𝓞 K)))
      (P : PowerScaleExteriorPool A bad Z ell eps),
    ∀ {ι : Type*} (d : FirstGaussPoolData C P ι) (c : ι → ℂ) (x : ι → W),
    ∀ s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest,
    ∀ T : s.TerminalCalibration sTail sZero k Lmax Nsave decay,
    ∀ ξ : W,
      d.energy (FirstGaussPoolData.twistedCoefficient c x ξ) ≤
        T.rawPhaseCost x ξ ε Cerror Czero := by
  obtain ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero, hCerror, hCzero, hb⟩ :=
    actual_gauss_raw_terminal_bound (E := E) (ν := ν) (μ := μ) hΓ μv hDiff
      C Drecipe hD finiteTest hlc hcs k ε hε Lmax Nsave ξmax hξmax
  refine ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero, hCerror, hCzero, ?_⟩
  intro Z ell eps bad P ι d c x s T ξ
  rw [d.energy_eq_sources hDiff Drecipe hD,
    d.mainSource_twisted c x ξ]
  simp_rw [d.residualSource_twisted _ _ c x ξ]
  unfold ActualPoolStages.TerminalCalibration.rawPhaseCost
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) d.density_pos.le)
  apply add_le_add
  · apply add_le_add
    · apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (hb Z _ (s.main.withMultiplier (fun i => jointPhase ξ (x i)))
            (T.main.fourierPhase x ξ)).2 d.multiplicity_nonneg
      · exact Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left
          (hb Z _ ((s.one p).withMultiplier (fun i => jointPhase ξ (x i.val)))
            ((T.one p).fourierPhase (fun i => x i.val) ξ)).2
          (FirstGaussPoolData.localErrorWeight_nonneg p.val 1)
    · exact Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left
        (hb Z _ ((s.six p).withMultiplier (fun i => jointPhase ξ (x i.val)))
          ((T.six p).fourierPhase (fun i => x i.val) ξ)).2
        (FirstGaussPoolData.localErrorWeight_nonneg p.val 6)
  · exact Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left
      (hb Z _ ((s.seven p).withMultiplier (fun i => jointPhase ξ (x i.val)))
        ((T.seven p).fourierPhase (fun i => x i.val) ξ)).2
      (FirstGaussPoolData.localErrorWeight_nonneg p.val 7)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_pool_raw_fourier_stage_bound

