import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ResidualZeroBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstPooledStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondZeroDiagonal

/-!
# Actual zero-terminal budgets for the two source stages

Both the original parent stage and the whole-Gauss second stage below use
their genuine finite sources. Their complete sums of zero terms are
replaced by the proved global whole-index diagonal estimates.

The zero seminorms and constants, together with the tail seminorms and
constants, are chosen before all moving columns, coefficients, scales,
masks and physical cutoffs. Only original pair normalization and whole
factor encodings occur among the extra inputs.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments MeasureTheory UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
local notation "L" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

include ν μ in
/-- The actual first stage with its total powerful zero diagonal already
paid. The only remaining nonterminal expression is the exact one-pool
cost, with the internal divisor frozen on both sides. -/
theorem parent_first_stage_zero_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (decay : ℝ) (hdecay : 1 < decay) (order : ℕ)
    (horder : Module.finrank ℤ L < order)
    (hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ order) :
    ∃ sTail sZero : Finset (ℕ × ℕ), ∃ Ctail Czero : ℝ, 0 ≤ Ctail ∧ 0 < Czero ∧
    ∀ (Zpool ell eps : ℝ) (bad : Finset (HeightOneSpectrum (𝓞 K)))
      (P : PowerScaleExteriorPool A bad Zpool ell eps),
    ∀ {ι : Type*} (columns : Finset ι) (fullI : ι → A.Exterior)
      (afull : ι → A.R) (hafull : ∀ i, A.Generates (fullI i) (afull i))
      (profiles : ι → ι → SchwartzMap V ℂ) (radius : {r : ℝ // 0 < r})
      (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X),
    let blocks := fun DE : FirstZeroLabel columns columns fullI fullI =>
      canonicalFirstCommonBlock C columns columns fullI fullI DE.val DE.property
    let sources := fun DE => (blocks DE).finiteSource hΓ C columns columns profiles M radius X hX
    ∀ charts : ∀ DE, ∀ D : ((blocks DE).mask M).powerset,
      FirstBlockProfileChart (E := E) hΓ μv (blocks DE) C columns columns profiles
        finiteTest radius D.val,
    ∀ pools : ∀ DE, ∀ D : ((blocks DE).mask M).powerset,
      FirstBlockPoolData (charts DE D) P M X hX,
    ∀ factors : ι × ι → Fin k → Ideal (𝓞 K),
    Set.InjOn factors (columns ×ˢ columns : Set (ι × ι)) →
    (∀ ij ∈ columns ×ˢ columns, PowerfulDiagonal.tupleIdeal (factors ij) =
      (fullI ij.1).val * (fullI ij.2).val) →
    ∀ N Amp : ℝ, 1 ≤ N → 0 ≤ Amp →
    (∀ ij ∈ columns ×ˢ columns,
      (Ideal.absNorm ((fullI ij.1).val * (fullI ij.2).val) : ℝ) ≤ N) →
    (∀ i ∈ columns, ∀ j ∈ columns, profiles i j 0 = 0) →
    (∀ v ∈ firstZeroPairs columns columns fullI fullI,
      sZero.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
        (∑ D ∈ ((blocks v.1).mask M).powerset, firstZeroDivisorWeight radius D) ≤
          Amp / Real.sqrt N) →
    ∀ {ω ψ₀ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ₀)
      (a : RealParameters) (t Y₁ Y₂ : ℝ) (B : ℕ),
    ParentSourceCalibration centered d a Zpool t Y₁ Y₂ columns
      (fun i j => (generatedOriginalColumn (σ := σ) hΓ (fullI i) (afull i) (hafull i)).originalPair
        (generatedOriginalColumn (σ := σ) hΓ (fullI j) (afull j) (hafull j)) (profiles i j))
      (sIntegerFiniteTestFunction K A.Sf finiteTest) radius M B →
    pairedStageEnergy centered d a Zpool t Y₁ Y₂ ≤
      (B : ℝ) * (Czero * Amp * N ^ ε +
        (∑ DE, ∑ D : ((blocks DE).mask M).powerset, (pools DE D).pooledCost) +
        Ctail * X ^ (1 - decay) *
          ∑ DE, ∑ i ∈ (sources DE).leftColumns, ∑ j ∈ (sources DE).rightColumns,
            sTail.sup (schwartzSeminormFamily ℂ V ℂ) ((sources DE).pairs i j).profile *
              ((sources DE).pairs i j).truncationMass (sources DE).mask radius) := by
  obtain ⟨sTail, Ctail, hCtail, hstage⟩ :=
    parent_first_stage_pool_bound (E := E) (hΓ := hΓ) (μv := μv) (ν := ν) (μ := μ)
      C hDiff finiteTest hlc hcs decay hdecay order horder hdegree
  obtain ⟨sZero, Czero, hCzero, hzero⟩ :=
    first_zero_diagonal_normalized (σ := σ) (η := η) (hS := hS)
      (hΓ := hΓ) (μv := μv) finiteTest k ε hε
  refine ⟨sTail, sZero, Ctail, Czero, hCtail, hCzero, ?_⟩
  intro Zpool ell eps bad P ι columns fullI afull hafull profiles radius M X hX
  dsimp only
  intro charts pools factors hinj hproduct N Amp hN hAmp hnorm hannular hprofile
    ω ψ₀ centered d a t Y₁ Y₂ B cal
  let blocks := fun DE : FirstZeroLabel columns columns fullI fullI =>
    canonicalFirstCommonBlock C columns columns fullI fullI DE.val DE.property
  have hz := hzero C columns columns fullI fullI blocks profiles hDiff radius M X hX
    factors hinj hproduct N Amp hN hAmp hnorm hannular hprofile
  have hp := hstage Zpool ell eps bad P columns fullI afull hafull profiles radius M X hX
    charts pools centered d a t Y₁ Y₂ B cal
  apply hp.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  exact add_le_add_right (add_le_add_right hz _) _

include ν μ in
/-- The complete second stage with the actual equal-original-ideal zero
diagonal paid globally. Its mask coprimality is read from the same
individual profile charts used by the genuine nonzero source estimate. -/
theorem gauss_second_stage_zero_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (decay : ℝ) (hdecay : 1 < decay) (order : ℕ)
    (horder : Module.finrank ℤ L < order)
    (hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ order) :
    ∃ sTail sZero : Finset (ℕ × ℕ), ∃ Ctail Czero : ℝ, 0 ≤ Ctail ∧ 0 < Czero ∧
    ∀ {H ι : Type*} (rows : Finset H) (rowMap : H → Q) (weight : H → ℝ)
      (columns : Finset ι) (c : ι → ℂ) (fullI : ι → A.Exterior)
      (afull : ι → A.R) (hafull : ∀ i, A.Generates (fullI i) (afull i))
      (hfull : ∀ i ∈ columns, ∃ u : Kˣ, (u : K) = (afull i : K) ∧ A.IsAllowed C.correction.B u)
      (φ : SchwartzMap V ℂ) (radius : {r : ℝ // 0 < r})
      (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X),
    let profiles := fun i j => (c i * star (c j)) • φ
    let blocks := fun DE : FirstZeroLabel columns columns fullI fullI =>
      canonicalFirstCommonBlock C columns columns fullI fullI DE.val DE.property
    let sources := fun DE => (blocks DE).secondFiniteSource hΓ hDiff C
      columns columns profiles M radius X hX
    ∀ charts : ∀ DE, ∀ D : M.powerset,
      SecondBlockProfileChart (E := E) hΓ μv hDiff (blocks DE) C columns columns profiles
        finiteTest radius D.val,
    ∀ (factors : ι × ι → Fin k → Ideal (𝓞 K)) (multiplicity : ℕ),
    (∀ v, ((columns ×ˢ columns).filter (fun ij => factors ij = v)).card ≤ multiplicity) →
    (∀ ij ∈ columns ×ˢ columns, PowerfulDiagonal.tupleIdeal (factors ij) =
      (fullI ij.1).val * (fullI ij.2).val) →
    ∀ N Amp : ℝ, 1 ≤ N → 0 ≤ Amp →
    (∀ ij ∈ columns ×ˢ columns,
      (Ideal.absNorm ((fullI ij.1).val * (fullI ij.2).val) : ℝ) ≤ N) →
    φ 0 = 0 →
    (∀ v ∈ firstZeroPairs columns columns fullI fullI,
      sZero.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
        A.exteriorNorm (fullI v.2.1) *
        (∑ D ∈ M.powerset, firstZeroDivisorWeight radius D) ≤ Amp / Real.sqrt N) →
    ∀ B : ℕ, GaussEnergyChart rows rowMap weight φ
      (sIntegerFiniteTestFunction K A.Sf finiteTest) radius M B →
    weightedEnergy rows weight
      (fun h => ∑ i ∈ columns, c i *
        (generatedOriginalColumn (σ := σ) hΓ (fullI i) (afull i) (hafull i)).orbit hDiff (rowMap h)) ≤
      (B : ℝ) * (Czero * (multiplicity * Amp) * N ^ ε +
        (∑ DE, ∑ D : M.powerset, (charts DE D).kernelCost M X hX) +
        Ctail * X ^ (1 - decay) *
          ∑ DE, ∑ i ∈ (sources DE).leftColumns, ∑ j ∈ (sources DE).rightColumns,
            sTail.sup (schwartzSeminormFamily ℂ V ℂ) ((sources DE).pairs i j).profile *
              ((sources DE).pairs i j).truncationMass M radius) := by
  obtain ⟨sTail, Ctail, hCtail, hstage⟩ :=
    gauss_second_stage_bound (E := E) (hΓ := hΓ) (μv := μv) (ν := ν) (μ := μ)
      (hDiff := hDiff) C Drecipe hD finiteTest hlc hcs decay hdecay order horder hdegree
  obtain ⟨sZero, Czero, hCzero, hzero⟩ :=
    second_zero_diagonal_normalized_of_fibers (σ := σ) (η := η) (hS := hS)
      (hΓ := hΓ) (μv := μv) finiteTest k ε hε
  refine ⟨sTail, sZero, Ctail, Czero, hCtail, hCzero, ?_⟩
  intro H ι rows rowMap weight columns c fullI afull hafull hfull φ radius M X hX
  dsimp only
  intro charts factors multiplicity hfiber hproduct N Amp hN hAmp hnorm hannular hprofile B cal
  let profiles := fun i j => (c i * star (c j)) • φ
  let blocks := fun DE : FirstZeroLabel columns columns fullI fullI =>
    canonicalFirstCommonBlock C columns columns fullI fullI DE.val DE.property
  have hz := hzero C columns columns fullI fullI blocks profiles hDiff radius M X hX
    factors multiplicity hfiber hproduct N Amp hN hAmp hnorm
    (by
      intro i hi j hj
      change (c i * star (c j)) • φ 0 = 0
      rw [hannular, smul_zero])
    (fun DE i hi D hD => (charts DE ⟨D, hD⟩).left_mask i hi)
    (fun DE j hj D hD => (charts DE ⟨D, hD⟩).right_mask j hj)
    hprofile
  have hp := hstage rows rowMap weight columns c fullI afull hafull hfull
    φ radius M X hX charts B cal
  apply hp.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  simpa only [mul_assoc] using add_le_add_right (add_le_add_right hz _) _

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.parent_first_stage_zero_bound
#print axioms HeckeSkeleton.Moments.EngineStep.gauss_second_stage_zero_bound

