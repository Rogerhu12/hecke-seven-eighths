import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualGaussHybridTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCoveredLabels

/-!
# Pure-dual terminal calibrations on the original one-pool source

The stage objects are the original main and valuation-one, -six and
-seven sources. Their new calibration records contain only the actual
pure-dual zero and tail data. The original source tag retains its prime,
column type, coefficients, charts, and first Fourier location.

Every cost uses the one existing tag sum, with exactly one factor
`4 / density`, the original main multiplicity, and the original local
error weights. The source energy identity and the phase transport are
proved on those same tags before applying the uniform second transform.
No whole-source or aggregate terminal estimate is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory HeckePort.Moments

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
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}

namespace FirstGaussPoolData

variable (d : FirstGaussPoolData C P ι)

/-- The exact one-pool identity with the already existing physical
source tags. The prime index is retained inside each error tag. -/
theorem energy_eq_tag_sources
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
    (c : ι → ℂ) :
    d.energy c = (4 / d.density) * ∑ b : PoolSourceTag P,
      d.tagWeight b * (d.tagSource c b).energy hDiff := by
  rw [d.energy_eq_sources hDiff Drecipe hD c]
  simp only [PoolSourceTag, Fintype.sum_sum_type, Fintype.sum_unique,
    tagWeight, tagSource]
  ring

/-- The same original first phase on every physical tag. Residual
columns use their original valuation subtype and its original index. -/
theorem tagSource_twisted (c : ι → ℂ) (x : ι → W) (ξ : W) (b : PoolSourceTag P) :
    d.tagSource (twistedCoefficient c x ξ) b =
      (d.tagSource c b).withMultiplier (fun i => jointPhase ξ (d.tagPoint x b i)) := by
  rcases b with u | p | p | p
  · exact d.mainSource_twisted c x ξ
  · exact d.residualSource_twisted p.val 1 c x ξ
  · exact d.residualSource_twisted p.val 6 c x ξ
  · exact d.residualSource_twisted p.val 7 c x ξ

end FirstGaussPoolData

variable {d : FirstGaussPoolData C P ι} {c : ι → ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

namespace ActualPoolStages

/-- These are the original per-stage signed-origin conditions. They
involve only the actual mask and tensor value, and hold internally for
the canonical unmasked row-ball stages. -/
structure DualSourceConditions
    (s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest) : Prop where
  mask : ∀ b : PoolSourceTag P, (s.tag b).mask = ∅
  origin_nonneg : ∀ b : PoolSourceTag P,
    0 ≤ (sIntegerTensorTerm K A.Sf
      (traceSchwartzToMixed K (s.tag b).profile) finiteTest 0).re

namespace DualSourceConditions

variable {s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest}

/-- The original empty mask survives the literal first Fourier phase. -/
theorem tag_fourierPhase_mask (hs : s.DualSourceConditions)
    (x : ι → W) (ξ : W) (b : PoolSourceTag P) :
    ((s.tag b).withMultiplier (fun i => jointPhase ξ (d.tagPoint x b i))).mask = ∅ :=
  hs.mask b

/-- The signed-origin condition depends on the unchanged test profile,
so the coefficient phase requires no new positivity hypothesis. -/
theorem tag_fourierPhase_origin_nonneg (hs : s.DualSourceConditions)
    (x : ι → W) (ξ : W) (b : PoolSourceTag P) :
    0 ≤ (sIntegerTensorTerm K A.Sf
      (traceSchwartzToMixed K
        ((s.tag b).withMultiplier (fun i => jointPhase ξ (d.tagPoint x b i))).profile)
      finiteTest 0).re :=
  hs.origin_nonneg b

end DualSourceConditions

/-- New terminal data on precisely the four old source sorts. No stage,
pool, prime, coefficient, or profile is reconstructed by this record. -/
structure DualTerminalCalibration
    (s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest)
    (sTail sZero : Finset (ℕ × ℕ)) (k : ℕ) (Lmax Nsave decay : ℝ) where
  main : s.main.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay
  one : ∀ p : P.primes, (s.one p).DualTerminalCalibration sTail sZero k Z Lmax Nsave decay
  six : ∀ p : P.primes, (s.six p).DualTerminalCalibration sTail sZero k Z Lmax Nsave decay
  seven : ∀ p : P.primes, (s.seven p).DualTerminalCalibration sTail sZero k Z Lmax Nsave decay

namespace DualTerminalCalibration

variable {s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def tag (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay) :
    ∀ b : PoolSourceTag P, (s.tag b).DualTerminalCalibration sTail sZero k Z Lmax Nsave decay
  | .inl _ => T.main
  | .inr (.inl p) => T.one p
  | .inr (.inr (.inl p)) => T.six p
  | .inr (.inr (.inr p)) => T.seven p

def ofTag (T : ∀ b : PoolSourceTag P,
    (s.tag b).DualTerminalCalibration sTail sZero k Z Lmax Nsave decay) :
    s.DualTerminalCalibration sTail sZero k Lmax Nsave decay where
  main := T (.inl ())
  one p := T (.inr (.inl p))
  six p := T (.inr (.inr (.inl p)))
  seven p := T (.inr (.inr (.inr p)))

@[simp] theorem ofTag_tag (T : ∀ b : PoolSourceTag P,
    (s.tag b).DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (b : PoolSourceTag P) : (ofTag T).tag b = T b := by
  rcases b with u | p | p | p
  · cases u
    rfl
  · rfl
  · rfl
  · rfl

/-- The one density is outside the complete original tag sum. -/
def rawPhaseCost (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (x : ι → W) (ξ : W) (ε Cerror Czero : ℝ) : ℝ :=
  (4 / d.density) * ∑ b : PoolSourceTag P, d.tagWeight b *
    ((T.tag b).fourierPhase (d.tagPoint x b) ξ).rawCost ε Cerror Czero

def coverHybridPhaseCost (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (B : d.SourceCovers c) (r : s.CoverHybridPredicates B)
    (x : ι → W) (ξ : W) (ε Cerror Czero : ℝ) : ℝ :=
  (4 / d.density) * ∑ b : PoolSourceTag P, d.tagWeight b *
    ((T.tag b).fourierPhase (d.tagPoint x b) ξ).coverHybridCost
      (B.tag b) (B.tag b) (r.tag b) ε Cerror Czero

theorem rawPhaseCost_le_coverHybrid
    (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (B : d.SourceCovers c) (r : s.CoverHybridPredicates B)
    (x : ι → W) (ξ : W) (ε Cerror Czero : ℝ) :
    T.rawPhaseCost x ξ ε Cerror Czero ≤
      T.coverHybridPhaseCost B r x ξ ε Cerror Czero := by
  unfold rawPhaseCost coverHybridPhaseCost
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) d.density_pos.le)
  exact Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left
    (((T.tag b).fourierPhase (d.tagPoint x b) ξ).rawCost_le_coverHybrid
      (r.tag b) ε Cerror Czero) (d.tagWeight_nonneg b)

theorem rawPhaseCost_integrable
    (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (F : SchwartzMap W ℂ) (x : ι → W) (ε Cerror Czero : ℝ) :
    Integrable (fun ξ => T.rawPhaseCost x ξ ε Cerror Czero) (actualFourierMeasure F) := by
  unfold rawPhaseCost
  apply Integrable.const_mul
  exact integrable_finsetSum _ (fun b _ =>
    ((T.tag b).rawPhaseCost_integrable F (d.tagPoint x b) ε Cerror Czero).const_mul _)

theorem coverHybridPhaseCost_integrable
    (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (B : d.SourceCovers c) (r : s.CoverHybridPredicates B)
    (F : SchwartzMap W ℂ) (x : ι → W) (ε Cerror Czero : ℝ) :
    Integrable (fun ξ => T.coverHybridPhaseCost B r x ξ ε Cerror Czero)
      (actualFourierMeasure F) := by
  unfold coverHybridPhaseCost
  apply Integrable.const_mul
  exact integrable_finsetSum _ (fun b _ =>
    ((T.tag b).coverHybridPhaseCost_integrable (B.tag b) (B.tag b) (r.tag b)
      F (d.tagPoint x b) ε Cerror Czero).const_mul _)

theorem integral_rawPhaseCost_le_coverHybrid
    (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (B : d.SourceCovers c) (r : s.CoverHybridPredicates B)
    (F : SchwartzMap W ℂ) (x : ι → W) (ε Cerror Czero : ℝ) :
    (∫ ξ, T.rawPhaseCost x ξ ε Cerror Czero ∂actualFourierMeasure F) ≤
      ∫ ξ, T.coverHybridPhaseCost B r x ξ ε Cerror Czero ∂actualFourierMeasure F :=
  integral_mono (T.rawPhaseCost_integrable F x ε Cerror Czero)
    (T.coverHybridPhaseCost_integrable B r F x ε Cerror Czero)
    (fun ξ => T.rawPhaseCost_le_coverHybrid B r x ξ ε Cerror Czero)

theorem integral_coverHybridPhaseCost_eq_sum
    (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (B : d.SourceCovers c) (r : s.CoverHybridPredicates B)
    (F : SchwartzMap W ℂ) (x : ι → W) (ε Cerror Czero : ℝ) :
    (∫ ξ, T.coverHybridPhaseCost B r x ξ ε Cerror Czero ∂actualFourierMeasure F) =
      (4 / d.density) * ∑ b : PoolSourceTag P, d.tagWeight b *
        ∫ ξ, ((T.tag b).fourierPhase (d.tagPoint x b) ξ).coverHybridCost
          (B.tag b) (B.tag b) (r.tag b) ε Cerror Czero ∂actualFourierMeasure F := by
  unfold coverHybridPhaseCost
  rw [integral_const_mul, integral_finsetSum _ (fun b _ =>
    ((T.tag b).coverHybridPhaseCost_integrable (B.tag b) (B.tag b) (r.tag b)
      F (d.tagPoint x b) ε Cerror Czero).const_mul (d.tagWeight b))]
  simp_rw [integral_const_mul]

end DualTerminalCalibration
end ActualPoolStages

variable (hΓ μv hDiff)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ

/-- Uniform pure-dual terminal control of every tag of the one original
pool. The actual energy equality is applied before the original first
phase, and each signed-origin condition survives that coefficient phase. -/
theorem actual_pool_dual_raw_fourier_stage_bound
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
    ∀ hs : s.DualSourceConditions,
    ∀ T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay, ∀ ξ : W,
      d.energy (FirstGaussPoolData.twistedCoefficient c x ξ) ≤
        T.rawPhaseCost x ξ ε Cerror Czero := by
  obtain ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero, hCerror, hCzero, hb⟩ :=
    actual_gauss_raw_dual_terminal_bound (E := E) (ν := ν) (μ := μ) hΓ μv hDiff
      C Drecipe hD finiteTest hlc hcs k ε hε Lmax Nsave ξmax hξmax
  refine ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero, hCerror, hCzero, ?_⟩
  intro Z ell eps bad P ι d c x s hs T ξ
  rw [d.energy_eq_tag_sources hDiff Drecipe hD]
  simp_rw [d.tagSource_twisted c x ξ]
  unfold ActualPoolStages.DualTerminalCalibration.rawPhaseCost
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) d.density_pos.le)
  exact Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left
    (hb Z _ ((s.tag b).withMultiplier (fun i => jointPhase ξ (d.tagPoint x b i)))
      (hs.tag_fourierPhase_mask x ξ b) (hs.tag_fourierPhase_origin_nonneg x ξ b)
      ((T.tag b).fourierPhase (d.tagPoint x b) ξ)).2
    (d.tagWeight_nonneg b)

/-- The same original pool now reaches its actual covered hybrid
branches, with all local weights and one density left literal. -/
theorem actual_pool_dual_cover_hybrid_fourier_stage_bound
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
    ∀ hs : s.DualSourceConditions,
    ∀ T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay,
    ∀ (B : d.SourceCovers c) (r : s.CoverHybridPredicates B), ∀ ξ : W,
      d.energy (FirstGaussPoolData.twistedCoefficient c x ξ) ≤
        T.coverHybridPhaseCost B r x ξ ε Cerror Czero := by
  obtain ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero, hCerror, hCzero, hb⟩ :=
    actual_pool_dual_raw_fourier_stage_bound (W := W) (E := E) (ν := ν) (μ := μ) hΓ μv hDiff
      C Drecipe hD finiteTest hlc hcs k ε hε Lmax Nsave ξmax hξmax
  refine ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero, hCerror, hCzero, ?_⟩
  intro Z ell eps bad P ι d c x s hs T B r ξ
  exact (hb Z ell eps bad P d c x s hs T ξ).trans
    (T.rawPhaseCost_le_coverHybrid B r x ξ ε Cerror Czero)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.energy_eq_tag_sources
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.tagSource_twisted
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.DualTerminalCalibration.integral_rawPhaseCost_le_coverHybrid
#print axioms HeckeSkeleton.Moments.EngineStep.actual_pool_dual_raw_fourier_stage_bound
#print axioms HeckeSkeleton.Moments.EngineStep.actual_pool_dual_cover_hybrid_fourier_stage_bound
