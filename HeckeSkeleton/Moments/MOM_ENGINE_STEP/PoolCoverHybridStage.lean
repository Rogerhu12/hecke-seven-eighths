import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CoverHybridPhaseIntegral

/-!
# The original one-pool source reaches genuine covered hybrid branches

The main source and the three valuation-error sources retain the same
prime pool, one density and their exact local difference weights.
Their finite Cartesian covers are constructed from the original
EXPANSION atlas and the literal first support quotient, before the
continuous Fourier parameters.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory
open HeckePort.Moments

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
variable {E W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
local notation "Arch" => mixedEmbedding.euclidean.mixedSpace K
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ



variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}

namespace FirstGaussPoolData

/-- Individual finite source labels and their actual Cartesian
dictionaries.  There is no source inequality among these fields. -/
structure SourceCovers (d : FirstGaussPoolData C P ι) (c : ι → ℂ) where
  main : SourceCartesianCover (d.mainSource c).columns (d.mainSource c).ideal
  residual : ∀ p : P.primes, ∀ n : ℕ,
    SourceCartesianCover (d.residualSource p.val n c).columns
      (d.residualSource p.val n c).ideal

def sourceCoversOfOriginal
    (d : FirstGaussPoolData C P ι) (c : ι → ℂ)
    {originalColumns : Finset ι} {originalIdeal : ι → A.Exterior}
    (T : SourceCartesianAtlas originalColumns originalIdeal)
    (S : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
    (hcolumns : d.columns = originalColumns.filter
      (fun i => HeckePort.Moments.Support.supportExtract (originalIdeal i).val S = D))
    (hideal : ∀ i, (d.ideal i).val =
      HeckePort.Moments.Support.supportResidual (originalIdeal i).val S) :
    d.SourceCovers c where
  main := d.mainSourceCartesianCover T S D hcolumns hideal c
  residual p n := d.residualSourceCartesianCover T S D hcolumns hideal p.val n c

end FirstGaussPoolData

variable {d : FirstGaussPoolData C P ι} {c : ι → ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

namespace ActualPoolStages

structure CoverHybridPredicates
    (s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest)
    (B : d.SourceCovers c) where
  main : s.main.CoverHybridPredicates B.main B.main
  one : ∀ p : P.primes,
    (s.one p).CoverHybridPredicates (B.residual p 1) (B.residual p 1)
  six : ∀ p : P.primes,
    (s.six p).CoverHybridPredicates (B.residual p 6) (B.residual p 6)
  seven : ∀ p : P.primes,
    (s.seven p).CoverHybridPredicates (B.residual p 7) (B.residual p 7)

namespace TerminalCalibration

variable {s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def coverHybridPhaseCost
    (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (B : d.SourceCovers c) (exceptional : s.CoverHybridPredicates B)
    (x : ι → W) (ξ : W) (ε Cerror Czero : ℝ) : ℝ :=
  (4 / d.density) *
    (d.multiplicity *
        (T.main.fourierPhase x ξ).coverHybridCost B.main B.main exceptional.main ε Cerror Czero +
      (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 1 *
        ((T.one p).fourierPhase (fun i => x i.val) ξ).coverHybridCost
          (B.residual p 1) (B.residual p 1) (exceptional.one p) ε Cerror Czero) +
      (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 6 *
        ((T.six p).fourierPhase (fun i => x i.val) ξ).coverHybridCost
          (B.residual p 6) (B.residual p 6) (exceptional.six p) ε Cerror Czero) +
      (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 7 *
        ((T.seven p).fourierPhase (fun i => x i.val) ξ).coverHybridCost
          (B.residual p 7) (B.residual p 7) (exceptional.seven p) ε Cerror Czero))

theorem rawPhaseCost_le_coverHybrid
    (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (B : d.SourceCovers c) (exceptional : s.CoverHybridPredicates B)
    (x : ι → W) (ξ : W) (ε Cerror Czero : ℝ) :
    T.rawPhaseCost x ξ ε Cerror Czero ≤
      T.coverHybridPhaseCost B exceptional x ξ ε Cerror Czero := by
  unfold rawPhaseCost coverHybridPhaseCost
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) d.density_pos.le)
  apply add_le_add
  · apply add_le_add
    · apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          ((T.main.fourierPhase x ξ).rawCost_le_coverHybrid
            exceptional.main ε Cerror Czero) d.multiplicity_nonneg
      · exact Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left
          (((T.one p).fourierPhase (fun i => x i.val) ξ).rawCost_le_coverHybrid
            (exceptional.one p) ε Cerror Czero)
          (FirstGaussPoolData.localErrorWeight_nonneg p.val 1)
    · exact Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left
        (((T.six p).fourierPhase (fun i => x i.val) ξ).rawCost_le_coverHybrid
          (exceptional.six p) ε Cerror Czero)
        (FirstGaussPoolData.localErrorWeight_nonneg p.val 6)
  · exact Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left
      (((T.seven p).fourierPhase (fun i => x i.val) ξ).rawCost_le_coverHybrid
        (exceptional.seven p) ε Cerror Czero)
      (FirstGaussPoolData.localErrorWeight_nonneg p.val 7)

theorem coverHybridPhaseCost_integrable
    (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (B : d.SourceCovers c) (exceptional : s.CoverHybridPredicates B)
    (F : SchwartzMap W ℂ) (x : ι → W) (ε Cerror Czero : ℝ) :
    Integrable (fun ξ => T.coverHybridPhaseCost B exceptional x ξ ε Cerror Czero)
      (actualFourierMeasure F) := by
  unfold coverHybridPhaseCost
  apply Integrable.const_mul
  apply Integrable.add
  · apply Integrable.add
    · apply Integrable.add
      · exact (T.main.coverHybridPhaseCost_integrable B.main B.main
          exceptional.main F x ε Cerror Czero).const_mul d.multiplicity
      · exact integrable_finsetSum _ (fun p _ =>
          ((T.one p).coverHybridPhaseCost_integrable (B.residual p 1) (B.residual p 1)
            (exceptional.one p) F (fun i => x i.val) ε Cerror Czero).const_mul _)
    · exact integrable_finsetSum _ (fun p _ =>
        ((T.six p).coverHybridPhaseCost_integrable (B.residual p 6) (B.residual p 6)
          (exceptional.six p) F (fun i => x i.val) ε Cerror Czero).const_mul _)
  · exact integrable_finsetSum _ (fun p _ =>
      ((T.seven p).coverHybridPhaseCost_integrable (B.residual p 7) (B.residual p 7)
        (exceptional.seven p) F (fun i => x i.val) ε Cerror Czero).const_mul _)

theorem integral_rawPhaseCost_le_coverHybrid
    (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (B : d.SourceCovers c) (exceptional : s.CoverHybridPredicates B)
    (F : SchwartzMap W ℂ) (x : ι → W) (ε Cerror Czero : ℝ) :
    (∫ ξ, T.rawPhaseCost x ξ ε Cerror Czero ∂actualFourierMeasure F) ≤
      ∫ ξ, T.coverHybridPhaseCost B exceptional x ξ ε Cerror Czero
        ∂actualFourierMeasure F := by
  apply integral_mono (T.rawPhaseCost_integrable F x ε Cerror Czero)
    (T.coverHybridPhaseCost_integrable B exceptional F x ε Cerror Czero)
  intro ξ
  exact T.rawPhaseCost_le_coverHybrid B exceptional x ξ ε Cerror Czero

end TerminalCalibration
end ActualPoolStages

variable (hΓ μv hDiff)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- A complete actual one-pool stage, with all genuine zero and tail
terms paid and all nonzero sources in covered pre-Cauchy hybrid form.
The constants, source covers and exceptional tests precede the first
Fourier variable. -/
theorem actual_pool_cover_hybrid_fourier_stage_bound
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
    ∀ (B : d.SourceCovers c) (exceptional : s.CoverHybridPredicates B), ∀ ξ : W,
      d.energy (FirstGaussPoolData.twistedCoefficient c x ξ) ≤
        T.coverHybridPhaseCost B exceptional x ξ ε Cerror Czero := by
  obtain ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero, hCerror, hCzero, hb⟩ :=
    actual_pool_raw_fourier_stage_bound (W := W) (E := E) (ν := ν) (μ := μ) hΓ μv hDiff
      C Drecipe hD finiteTest hlc hcs k ε hε Lmax Nsave ξmax hξmax
  refine ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero, hCerror, hCzero, ?_⟩
  intro Z ell eps bad P ι d c x s T B exceptional ξ
  exact (hb Z ell eps bad P d c x s T ξ).trans
    (T.rawPhaseCost_le_coverHybrid B exceptional x ξ ε Cerror Czero)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.sourceCoversOfOriginal
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.TerminalCalibration.integral_rawPhaseCost_le_coverHybrid
#print axioms HeckeSkeleton.Moments.EngineStep.actual_pool_cover_hybrid_fourier_stage_bound

