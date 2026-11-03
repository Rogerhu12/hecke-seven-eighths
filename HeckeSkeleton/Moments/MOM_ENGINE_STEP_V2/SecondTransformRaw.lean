import HeckeSkeleton.Moments.MOM_ENGINE_STEP.RawSourcePhaseIntegral

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual second source with its exact truncation discrepancy

The positive orbital majorant is split into the full zero term, the
norm of its genuine masked truncation difference, and the full finite
nonzero correlation. This step introduces no numerical tail majorant
and does not perform a Cauchy inequality on the second correlation.

Paper: Section 4.8, lines 2883--2894 and 3004--3010.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.SecondTransformPrivate

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments MeasureTheory

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Both terms use the mask and radius of the same actual finite source. -/
def rawTailCost {ι : Type*} {G : ActualGaussSource C ι}
    {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
    (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest) : ℝ :=
  ∑ DE,
    ‖(∑ i ∈ (s.sources DE).leftColumns,
        ∑ j ∈ (s.sources DE).rightColumns,
          ((s.sources DE).pairs i j).maskedSeries
            (sIntegerFiniteTestFunction K A.Sf finiteTest) s.radius s.mask) -
      (s.sources DE).transform μv hDiff finiteTest‖

/-- The original positive-source theorem and the finite Poisson identity
give this decomposition before any estimate of the tail. -/
theorem raw_energy_le
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    {ι : Type*} (G : ActualGaussSource C ι)
    (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest) :
    G.energy hDiff ≤
      (s.fiber : ℝ) * (s.rawZeroCost + rawTailCost s + s.rawNonzeroCost) := by
  let series := fun DE =>
    ∑ i ∈ (s.sources DE).leftColumns, ∑ j ∈ (s.sources DE).rightColumns,
      ((s.sources DE).pairs i j).maskedSeries
        (sIntegerFiniteTestFunction K A.Sf finiteTest) s.radius s.mask
  have hfull (i : ι) (hi : i ∈ G.columns) :
      ∃ u : Kˣ, (u : K) = (G.generator i : K) ∧ A.IsAllowed C.correction.B u :=
    ⟨Units.mk0 (G.generator i : K) (by exact_mod_cast (G.generates i).1),
      rfl, G.allowed i hi⟩
  have hp := gauss_energy_orbital_source_bound hDiff G.rows
    (engineElementOrbit (Γ := Γ)) (fun _ => 1) G.columns G.coefficient
    (fun i => generatedOriginalColumn (σ := σ) hΓ (G.ideal i)
      (G.generator i) (G.generates i))
    s.profile (sIntegerFiniteTestFunction K A.Sf finiteTest)
    (continuous_sIntegerFiniteTestFunction K A.Sf finiteTest hlc)
    (hasCompactSupport_sIntegerFiniteTestFunction K A.Sf finiteTest hcs)
    s.radius s.mask s.fiber s.calibration
  rw [common_support_gauss_sources hΓ hDiff C Drecipe hD
    G.columns G.columns G.ideal G.ideal G.generator G.generator
    G.generates G.generates hfull hfull] at hp
  change _ ≤ (s.fiber : ℝ) * (∑ DE, series DE).re at hp
  rw [G.energy_eq_orbital hΓ hDiff]
  apply hp.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg s.fiber)
  rw [Complex.re_sum]
  have hpoint (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val)) :
      (series DE).re ≤
        ‖(s.sources DE).zeroTerm μv hDiff finiteTest‖ +
        ‖series DE - (s.sources DE).transform μv hDiff finiteTest‖ +
        ∑ D : s.mask.powerset,
          ‖∑ t ∈ (s.sources DE).rows,
            ∑ i ∈ (s.sources DE).leftColumns,
              ∑ j ∈ (s.sources DE).rightColumns,
                ((s.sources DE).pairs i j).transformedRow
                  μv hDiff finiteTest s.radius D.val t‖ := by
    have hre := Complex.re_le_norm
      (series DE - (s.sources DE).transform μv hDiff finiteTest)
    rw [Complex.sub_re] at hre
    have hfinite :=
      (Complex.re_le_norm ((s.sources DE).transform μv hDiff finiteTest)).trans
        (s.transform_norm_le_raw_rows DE)
    linarith
  simpa only [ActualGaussStage.rawZeroCost, ActualGaussStage.rawNonzeroCost,
    rawTailCost, Finset.sum_add_distrib] using
    Finset.sum_le_sum (s := Finset.univ) (fun DE _ => hpoint DE)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.SecondTransformPrivate

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.SecondTransformPrivate.raw_energy_le
