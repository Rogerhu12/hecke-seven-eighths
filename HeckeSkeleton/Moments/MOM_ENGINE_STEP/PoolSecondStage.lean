import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolGaussDecomposition
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondStage

/-!
# All outputs of the one prime pool undergo the actual second transform

The main source and each valuation 1/6/7 source below are constructed
from the earlier pool data. The extra inputs are only the original
positive row profile and its individual Fourier profile charts. Each
source uses its genuine subgroup orbits, complete common supports,
nonprimitive correlations, original mask, and common physical cutoff.

One choice of the tail seminorms and constant works for every such
source, coefficient and Fourier parameter. In particular no bound on
an entire Gauss energy or transformed source is an input to this step.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}

/-- Literal arithmetic data for one of the Gauss polynomials produced
by the earlier pool. There are no analytic estimates among these fields. -/
structure ActualGaussSource (C : A.GeneralArithmeticContext σ η hS) (ι : Type*) where
  rows : Finset A.R
  row_nonzero : ∀ h ∈ rows, h ≠ 0
  columns : Finset ι
  ideal : ι → A.Exterior
  generator : ι → A.R
  generates : ∀ i, A.Generates (ideal i) (generator i)
  allowed : ∀ i ∈ columns, A.IsAllowed C.correction.B
    (Units.mk0 (generator i : K) (by exact_mod_cast (generates i).1))
  coefficient : ι → ℂ

namespace ActualGaussSource

variable {ι : Type*}

def energy (G : ActualGaussSource C ι)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0) : ℝ :=
  ∑ h ∈ G.rows, ‖∑ i ∈ G.columns, G.coefficient i *
    actualSIntegerGauss K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hDiff
      (G.generator i) (G.generates i).1
      (generatedIdealCharacter (σ := σ) (G.ideal i) (G.generator i) (G.generates i)) h‖ ^ 2

theorem energy_eq_orbital (G : ActualGaussSource C ι)
    {Γ : Subgroup A.U} (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0) :
    G.energy hDiff = weightedEnergy G.rows (fun _ => 1) (fun h =>
      ∑ i ∈ G.columns, G.coefficient i *
        (generatedOriginalColumn (σ := σ) hΓ (G.ideal i) (G.generator i)
          (G.generates i)).orbit hDiff (engineElementOrbit h)) := by
  unfold energy weightedEnergy
  apply Finset.sum_congr rfl
  intro h hh
  simp only [one_mul]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  rw [generatedColumn_orbit_element hΓ hDiff _ _ _ h (G.row_nonzero h hh)]

end ActualGaussSource

namespace FirstGaussPoolData

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}

def mainSource (d : FirstGaussPoolData C P ι) (c : ι → ℂ) : ActualGaussSource C ι where
  rows := d.mainRows
  row_nonzero h hh := by
    obtain ⟨hp, hmem, rfl⟩ := Finset.mem_image.mp hh
    have hr := (Finset.mem_product.mp (Finset.mem_filter.mp hmem).1).1
    exact mul_ne_zero (d.row_generates hp.1 hr).1 (generator_power_generates C hp.2 6).1
  columns := d.columns
  ideal := d.ideal
  generator := d.generator
  generates := d.generates
  allowed := d.allowed
  coefficient := c

def residualSource (d : FirstGaussPoolData C P ι) (p : ExteriorPrime A)
    (n : ℕ) (c : ι → ℂ) : ActualGaussSource C (d.valuationColumns p n) where
  rows := d.errorRows p
  row_nonzero h hh := (d.row_generates h (Finset.mem_filter.mp hh).1).1
  columns := Finset.univ
  ideal i := (d.residualPresentation p n i).residual
  generator i := (d.residualPresentation p n i).generator
  generates i := (d.residualPresentation p n i).generates
  allowed i _ := (d.residualPresentation p n i).allowed
  coefficient := d.residualCoefficient p n c

theorem residualSource_energy (d : FirstGaussPoolData C P ι)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (p : ExteriorPrime A) (n : ℕ) (c : ι → ℂ) :
    (d.residualSource p n c).energy hDiff = d.residualEnergy hDiff p n c := rfl

theorem energy_eq_sources (d : FirstGaussPoolData C P ι)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (D : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B D)
    (c : ι → ℂ) :
    d.energy c = (4 / d.density) *
      (d.multiplicity * (d.mainSource c).energy hDiff +
        (∑ p : P.primes, localErrorWeight p.val 1 * (d.residualSource p.val 1 c).energy hDiff) +
        (∑ p : P.primes, localErrorWeight p.val 6 * (d.residualSource p.val 6 c).energy hDiff) +
        (∑ p : P.primes, localErrorWeight p.val 7 * (d.residualSource p.val 7 c).energy hDiff)) := by
  rw [d.energy_eq_residual_sources hDiff D hD c]
  have hsum (n : ℕ) :
      (∑ p : P.primes, localErrorWeight p.val n * (d.residualSource p.val n c).energy hDiff) =
        ∑ p ∈ P.primes, localErrorWeight p n * d.residualEnergy hDiff p n c := by
    change (∑ p : P.primes, localErrorWeight p.val n * d.residualEnergy hDiff p.val n c) = _
    exact Finset.sum_coe_sort P.primes (fun p => localErrorWeight p n * d.residualEnergy hDiff p n c)
  rw [hsum 1, hsum 6, hsum 7]
  rfl

end FirstGaussPoolData

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
local notation "L" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- Only original profile data and individual source-profile identities
are supplied for a genuine second source. The common-support partition,
full source and all transforms are constructed by the engine. -/
structure ActualGaussStage {ι : Type*} (G : ActualGaussSource C ι)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) where
  profile : SchwartzMap V ℂ
  radius : {r : ℝ // 0 < r}
  mask : Finset (HeightOneSpectrum A.R)
  cutoff : ℝ
  cutoff_one : 1 ≤ cutoff
  fiber : ℕ
  calibration : GaussEnergyChart G.rows (engineElementOrbit (Γ := Γ)) (fun _ => 1)
    profile (sIntegerFiniteTestFunction K A.Sf finiteTest) radius mask fiber
  charts : ∀ DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val), ∀ D : mask.powerset,
    SecondBlockProfileChart (E := E) hΓ μv hDiff
      (canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property)
      C G.columns G.columns (fun i j => (G.coefficient i * star (G.coefficient j)) • profile)
      finiteTest radius D.val

variable {hΓ μv hDiff}

namespace ActualGaussStage

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

def sources (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val)) :=
  (canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property).secondFiniteSource
      hΓ hDiff C G.columns G.columns
      (fun i j => (G.coefficient i * star (G.coefficient j)) • s.profile)
      s.mask s.radius s.cutoff s.cutoff_one

def cost (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
    (seminorms : Finset (ℕ × ℕ)) (Ctail decay : ℝ) : ℝ :=
  (s.fiber : ℝ) * ∑ DE,
    (‖(s.sources DE).zeroTerm μv hDiff finiteTest‖ +
      (∑ D : s.mask.powerset, (s.charts DE D).kernelCost s.mask s.cutoff s.cutoff_one) +
      Ctail * s.cutoff ^ (1 - decay) *
        ∑ i ∈ (s.sources DE).leftColumns, ∑ j ∈ (s.sources DE).rightColumns,
          seminorms.sup (schwartzSeminormFamily ℂ V ℂ) ((s.sources DE).pairs i j).profile *
            ((s.sources DE).pairs i j).truncationMass s.mask s.radius)

end ActualGaussStage

variable (hΓ μv hDiff)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- A single choice of original-profile seminorms controls the genuine
second transform of every moving Gauss source. -/
theorem actual_gauss_stage_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (decay : ℝ) (hdecay : 1 < decay) (order : ℕ)
    (horder : Module.finrank ℤ L < order)
    (hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ order) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ Ctail : ℝ, 0 ≤ Ctail ∧
    ∀ {ι : Type*} (G : ActualGaussSource C ι)
      (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest),
      G.energy hDiff ≤ s.cost seminorms Ctail decay := by
  obtain ⟨seminorms, Ctail, hC, hbound⟩ :=
    gauss_second_stage_bound (E := E) (ν := ν) (μ := μ) hΓ μv hDiff C Drecipe hD
      finiteTest hlc hcs decay hdecay order horder hdegree
  refine ⟨seminorms, Ctail, hC, ?_⟩
  intro ι G s
  rw [G.energy_eq_orbital hΓ hDiff]
  exact hbound G.rows (engineElementOrbit (Γ := Γ)) (fun _ => 1) G.columns G.coefficient
    G.ideal G.generator G.generates
    (fun i hi => ⟨Units.mk0 (G.generator i : K) (by exact_mod_cast (G.generates i).1),
      rfl, G.allowed i hi⟩)
    s.profile s.radius s.mask s.cutoff s.cutoff_one s.charts s.fiber s.calibration

include ν μ in
/-- The one pool and all three errors pass to the complete second
source. The local 1/6/7 factors, single density, and single main-fiber
factor remain explicit. Every displayed cost is a constructed actual
zero term, correlation kernel, or original common-cutoff tail. -/
theorem pool_second_stage_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (decay : ℝ) (hdecay : 1 < decay) (order : ℕ)
    (horder : Module.finrank ℤ L < order)
    (hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ order) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ Ctail : ℝ, 0 ≤ Ctail ∧
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
    d.energy c ≤ (4 / d.density) *
      (d.multiplicity * main.cost seminorms Ctail decay +
        (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 1 *
          (errorOne p).cost seminorms Ctail decay) +
        (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 6 *
          (errorSix p).cost seminorms Ctail decay) +
        (∑ p : P.primes, FirstGaussPoolData.localErrorWeight p.val 7 *
          (errorSeven p).cost seminorms Ctail decay)) := by
  obtain ⟨seminorms, Ctail, hC, hbound⟩ :=
    actual_gauss_stage_bound (E := E) (ν := ν) (μ := μ) hΓ μv hDiff C Drecipe hD
      finiteTest hlc hcs decay hdecay order horder hdegree
  refine ⟨seminorms, Ctail, hC, ?_⟩
  intro Z ell eps bad P ι d c main errorOne errorSix errorSeven
  rw [d.energy_eq_sources hDiff Drecipe hD c]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) d.density_pos.le)
  apply add_le_add
  · apply add_le_add
    · apply add_le_add
      · exact mul_le_mul_of_nonneg_left (hbound _ main) d.multiplicity_nonneg
      · exact Finset.sum_le_sum fun p _ =>
          mul_le_mul_of_nonneg_left (hbound _ (errorOne p))
            (FirstGaussPoolData.localErrorWeight_nonneg p.val 1)
    · exact Finset.sum_le_sum fun p _ =>
        mul_le_mul_of_nonneg_left (hbound _ (errorSix p))
          (FirstGaussPoolData.localErrorWeight_nonneg p.val 6)
  · exact Finset.sum_le_sum fun p _ =>
      mul_le_mul_of_nonneg_left (hbound _ (errorSeven p))
        (FirstGaussPoolData.localErrorWeight_nonneg p.val 7)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_gauss_stage_bound
#print axioms HeckeSkeleton.Moments.EngineStep.pool_second_stage_bound
