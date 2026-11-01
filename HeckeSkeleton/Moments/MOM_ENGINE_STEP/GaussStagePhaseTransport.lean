import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolSecondStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstGaussPoolKernel

/-!
# The second original kernel is fixed before the first Fourier variable

The first Fourier parameter multiplies individual whole coefficients.
Complex linearity of the actual trace Fourier transform and of the
original orbital Haar profile moves these multipliers into the two
coefficient arrays of the second profile chart. Its Schwartz kernel,
physical cutoff, rows, common supports, mask and radius do not change.

Consequently the eventual positive kernel is the product of the two
actual Fourier measures. No finite Fourier support or profile equality
after an absolute-value estimate is assumed.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors FourierTransform SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory

variable {K : Type} [Field K] [NumberField K]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

theorem engine_traceSchwartzFourier_smul (a : ℂ) (φ : SchwartzMap V ℂ) :
    traceSchwartzFourier K (a • φ) = a • traceSchwartzFourier K φ := by
  unfold traceSchwartzFourier
  change ((((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K)⁻¹ : ℝ) : ℂ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (traceConjugation K).toContinuousLinearEquiv
      (SchwartzMap.fourierTransformCLM ℂ (a • φ)) =
    a • (((((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K)⁻¹ : ℝ) : ℂ) •
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (traceConjugation K).toContinuousLinearEquiv
      (SchwartzMap.fourierTransformCLM ℂ φ))
  rw [map_smul, map_smul, smul_comm]

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

local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

theorem OrbitalGaussColumn.secondProfile_smul
    (c d : OrbitalGaussColumn K A.Sf Γ) (a : ℂ) (φ : SchwartzMap V ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (r : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R)) (q : Q) :
    c.secondProfile μv hDiff d (a • φ) finiteTest r D q =
      a * c.secondProfile μv hDiff d φ finiteTest r D q := by
  unfold OrbitalGaussColumn.secondProfile
  dsimp only [ParentPeriodicPair.dualRadius, OrbitalGaussColumn.pair]
  rw [engine_traceSchwartzFourier_smul,
    sUnitOrbitalProfile_tensor_smul, smul_eq_mul]

variable {hΓ μv hDiff}

namespace ActualGaussSource

variable {ι : Type*}

/-- A coefficient multiplier does not alter the underlying source. -/
def withMultiplier (G : ActualGaussSource C ι) (u : ι → ℂ) : ActualGaussSource C ι :=
  { G with coefficient := fun i => u i * G.coefficient i }

end ActualGaussSource

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace ActualGaussStage

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

/-- Both actual trace transforms and the orbital integral are linear,
so the chart for every moving coefficient is constructed from one
earlier chart. In particular the second Schwartz kernel is unchanged. -/
def withMultiplier (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
    (u : ι → ℂ) :
    ActualGaussStage (E := E) hΓ μv hDiff (G.withMultiplier u) finiteTest where
  profile := s.profile
  radius := s.radius
  mask := s.mask
  cutoff := s.cutoff
  cutoff_one := s.cutoff_one
  fiber := s.fiber
  calibration := s.calibration
  charts DE D :=
    { s.charts DE D with
      leftCoefficient := fun i => u i * (s.charts DE D).leftCoefficient i
      rightCoefficient := fun j => u j * (s.charts DE D).rightCoefficient j
      profile := by
        intro q i hi j hj hcop
        dsimp only [ActualGaussSource.withMultiplier] at hi hj hcop ⊢
        have hscale :
            ((u i * G.coefficient i) * star (u j * G.coefficient j)) • s.profile =
              (u i * star (u j)) •
                ((G.coefficient i * star (G.coefficient j)) • s.profile) := by
          rw [smul_smul, star_mul]
          congr 1
          ring
        change OrbitalGaussColumn.secondProfile μv hDiff _ _
            (((u i * G.coefficient i) * star (u j * G.coefficient j)) • s.profile)
            finiteTest s.radius D.val q = _
        rw [hscale, OrbitalGaussColumn.secondProfile_smul,
          (s.charts DE D).profile q i hi j hj hcop]
        simp only [star_mul]
        ring }

theorem withMultiplier_kernel
    (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest) (u : ι → ℂ)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val)) (D : s.mask.powerset) :
    ((s.withMultiplier u).charts DE D).kernel = (s.charts DE D).kernel := rfl

/-- Unit phases preserve the nonzero pair profiles used by the physical
cutoff. An arbitrary complex multiplier need not preserve these rows:
the zero multiplier deletes every active pair profile. -/
theorem withMultiplier_rows
    (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest) (u : ι → Circle)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val)) :
    ((s.withMultiplier (fun i => (u i : ℂ))).sources DE).rows =
      (s.sources DE).rows := by
  let v : ι → ℂ := fun i => (u i : ℂ)
  have hv (i : ι) : v i ≠ 0 := Circle.coe_ne_zero (u i)
  let s' := s.withMultiplier v
  have hprofile (i j : ι) :
      ((s'.sources DE).pairs i j).profile ≠ 0 ↔
        ((s.sources DE).pairs i j).profile ≠ 0 := by
    change ((v i * G.coefficient i) *
        star (v j * G.coefficient j)) • s.profile ≠ 0 ↔
      (G.coefficient i * star (G.coefficient j)) • s.profile ≠ 0
    simp only [smul_eq_zero, mul_eq_zero, star_eq_zero,
      hv, false_or]
  have hbranches : (s'.sources DE).branches = (s.sources DE).branches := rfl
  have hfilter :
      ((s'.sources DE).branches.filter
        (fun e => ((s'.sources DE).pairs e.1.1 e.1.2).profile ≠ 0)) =
      ((s.sources DE).branches.filter
        (fun e => ((s.sources DE).pairs e.1.1 e.1.2).profile ≠ 0)) := by
    ext e
    simp only [Finset.mem_filter, hbranches, hprofile]
  have hinverse : (s'.sources DE).inverseRadii = (s.sources DE).inverseRadii := by
    unfold FirstFiniteSource.inverseRadii
    rw [hfilter]
    apply congrArg (fun t : Finset ℝ => insert 0 t)
    apply Finset.image_congr
    intro e _
    rfl
  have hbound : (s'.sources DE).inverseRadiusBound =
      (s.sources DE).inverseRadiusBound := by
    exact Finset.sup'_congr hinverse (fun _ _ => rfl)
  have hcutoff : (s'.sources DE).physicalCutoff = (s.sources DE).physicalCutoff := by
    change s.cutoff * (s'.sources DE).inverseRadiusBound =
      s.cutoff * (s.sources DE).inverseRadiusBound
    exact congrArg (fun x => s.cutoff * x) hbound
  change (s'.sources DE).rows = (s.sources DE).rows
  unfold FirstFiniteSource.rows
  rw [hcutoff]

end ActualGaussStage

namespace FirstGaussPoolData

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The literal first Fourier coefficient is precisely a multiplier of
the original whole main source. -/
theorem mainSource_twisted (d : FirstGaussPoolData C P ι)
    (c : ι → ℂ) (x : ι → W) (ξ : W) :
    d.mainSource (twistedCoefficient c x ξ) =
      (d.mainSource c).withMultiplier (fun i => jointPhase ξ (x i)) := by
  unfold mainSource ActualGaussSource.withMultiplier
  congr 1
  funext i
  exact mul_comm _ _

/-- The same statement holds after the genuine valuation extraction:
the residual scalar is independent of the first Fourier parameter. -/
theorem residualSource_twisted (d : FirstGaussPoolData C P ι)
    (p : ExteriorPrime A) (n : ℕ) (c : ι → ℂ) (x : ι → W) (ξ : W) :
    d.residualSource p n (twistedCoefficient c x ξ) =
      (d.residualSource p n c).withMultiplier (fun i => jointPhase ξ (x i.val)) := by
  unfold residualSource ActualGaussSource.withMultiplier
  congr 1
  funext i
  simp only [residualCoefficient, adjustedCoefficient, twistedCoefficient]
  ring

end FirstGaussPoolData

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OrbitalGaussColumn.secondProfile_smul
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.withMultiplier
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.withMultiplier_rows
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.residualSource_twisted
