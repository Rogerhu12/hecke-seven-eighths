import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualGaussRawTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondHybridCoverSource

/-!
# Complete second terminal exit with actual source covers

The main and valuation-error Gauss sources use their computed finite
Cartesian covers.  The original second physical cutoff and tail are
retained throughout.  Every exceptional test occurs inside the same
second Fourier measure before the ordinary row Cauchy estimate.

The only cover inputs describe the finite original column labels and
their individual Cartesian dictionaries.  The actual constructors in
SourceCartesianCover derive them from the original EXPANSION atlas.
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
variable {hΓ μv hDiff}

namespace ActualGaussStage

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
variable (LC RC : SourceCartesianCover G.columns G.ideal)

abbrev CoverHybridPredicates :=
  ∀ DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
    ∀ D : s.mask.powerset, (s.charts DE D).CoverHybridPredicates LC RC

def coverHybridNonzeroCost (exceptional : s.CoverHybridPredicates LC RC) : ℝ :=
  ∑ DE, ∑ D : s.mask.powerset,
    (s.charts DE D).coverHybridCost LC RC s.mask s.cutoff s.cutoff_one
      (exceptional DE D)

/-- The literal nonzero second source reaches the actual finite hybrid
branches.  The residual Cartesian dictionaries are constructed inside
the support partition, not supplied for an unsplit common source. -/
theorem rawNonzeroCost_le_coverHybrid (exceptional : s.CoverHybridPredicates LC RC) :
    s.rawNonzeroCost ≤ s.coverHybridNonzeroCost LC RC exceptional := by
  unfold rawNonzeroCost coverHybridNonzeroCost
  apply Finset.sum_le_sum
  intro DE _
  apply Finset.sum_le_sum
  intro D _
  exact (s.charts DE D).cover_hybrid_bound LC RC
    (commonSupportPool_support_eq G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val) DE.val DE.property)
    (canonicalFirstCommonBlock_allowed C G.columns G.columns G.ideal G.ideal
      DE.val DE.property).1
    (canonicalFirstCommonBlock_allowed C G.columns G.columns G.ideal G.ideal
      DE.val DE.property).2
    s.mask s.cutoff s.cutoff_one (exceptional DE D)

namespace TerminalCalibration

variable {s LC RC}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Z Lmax Nsave decay : ℝ}

def coverHybridCost (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (LC RC : SourceCartesianCover G.columns G.ideal)
    (exceptional : s.CoverHybridPredicates LC RC) (ε Cerror Czero : ℝ) : ℝ :=
  (s.fiber : ℝ) * (Czero * (T.windows.multiplicity * T.zeroAmplitude) *
      Z ^ (T.productExponent * ε) + s.coverHybridNonzeroCost LC RC exceptional +
    Cerror * (T.windows.multiplicity * T.tailAmplitude) * Z ^ (-Nsave))

theorem rawCost_le_coverHybrid
    (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (exceptional : s.CoverHybridPredicates LC RC) (ε Cerror Czero : ℝ) :
    T.rawCost ε Cerror Czero ≤ T.coverHybridCost LC RC exceptional ε Cerror Czero := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg s.fiber)
  exact add_le_add_right
    (add_le_add_left (s.rawNonzeroCost_le_coverHybrid LC RC exceptional) _) _

end TerminalCalibration
end ActualGaussStage

variable (hΓ μv hDiff)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- A uniform complete second-source exit with genuine zero/tail
budgets and pre-Cauchy exceptional/ordinary branches.  All constants and
the small physical-cutoff exponent precede the moving original sources. -/
theorem actual_gauss_cover_hybrid_terminal_bound
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
      (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)
      (LC RC : SourceCartesianCover G.columns G.ideal)
      (exceptional : s.CoverHybridPredicates LC RC),
      s.cutoff ≤ Z ^ ξ ∧
        G.energy hDiff ≤ T.coverHybridCost LC RC exceptional ε Cerror Czero := by
  obtain ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero, hCerror, hCzero, hb⟩ :=
    actual_gauss_raw_terminal_bound (E := E) (ν := ν) (μ := μ) hΓ μv hDiff
      C Drecipe hD finiteTest hlc hcs k ε hε Lmax Nsave ξ hξ
  refine ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero, hCerror, hCzero, ?_⟩
  intro Z ι G s T LC RC exceptional
  obtain ⟨hcutoff, henergy⟩ := hb Z G s T
  exact ⟨hcutoff, henergy.trans (T.rawCost_le_coverHybrid exceptional ε Cerror Czero)⟩

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.rawNonzeroCost_le_coverHybrid
#print axioms HeckeSkeleton.Moments.EngineStep.actual_gauss_cover_hybrid_terminal_bound

