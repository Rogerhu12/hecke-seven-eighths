import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SignedSecondStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondActiveDualZeroDiagonal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondDivisorDualZeroDiagonal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualTerminalCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.TerminalPowerBudget

/-!
# Pure-dual zero and tail budgets for the signed complete source

The two terminal estimates use the original individual profile
seminorms and the genuine whole-factor tuple fibres. The original
origin is handled by the signed whole-Gram theorem, so the fixed
row-ball profile is not required to vanish at zero. The cutoff,
seminorm orders, and constants precede all moving source data.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments MeasureTheory UniqueFactorizationMonoid
open HeckePort.CenteredMomentCounting

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
/-- The complete second stage with the actual equal-original-ideal zero
diagonal paid globally. Its mask coprimality is read from the same
individual profile charts used by the genuine nonzero source estimate. -/
theorem gauss_second_stage_dual_zero_bound
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
      (φ : SchwartzMap V ℂ)
      (hpositive : 0 ≤ (sIntegerTensorTerm K A.Sf (traceSchwartzToMixed K φ) finiteTest 0).re)
      (radius : {r : ℝ // 0 < r})
      (M : Finset (HeightOneSpectrum A.R)) (hmask : M = ∅) (X : ℝ) (hX : 1 ≤ X),
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
    ∀ (Dzero : Ideal (𝓞 K)) (N Amp : ℝ), Dzero ≠ 0 → 1 ≤ N → 0 ≤ Amp →
    (∀ ij ∈ columns ×ˢ columns, profiles ij.1 ij.2 ≠ 0 →
      (Ideal.absNorm ((fullI ij.1).val * (fullI ij.2).val) : ℝ) ≤ N) →
    (∀ ij ∈ columns ×ˢ columns, profiles ij.1 ij.2 ≠ 0 →
      (fullI ij.1).val = (fullI ij.2).val → Dzero ∣ (fullI ij.1).val) →
    (∀ v ∈ firstZeroPairs columns columns fullI fullI,
      sZero.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
        A.exteriorNorm (fullI v.2.1) *
        (∑ D ∈ M.powerset, firstZeroDivisorWeight radius D) ≤ Amp * (Ideal.absNorm Dzero : ℝ) / Real.sqrt N) →
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
    gauss_second_stage_dual_bound (E := E) (hΓ := hΓ) (μv := μv) (ν := ν) (μ := μ)
      (hDiff := hDiff) C Drecipe hD finiteTest hlc hcs decay hdecay order horder hdegree
  obtain ⟨sZero, Czero, hCzero, hzero⟩ :=
    second_dualZero_diagonal_supported_of_divisor (σ := σ) (η := η) (hS := hS)
      (hΓ := hΓ) (μv := μv) finiteTest k ε hε
  refine ⟨sTail, sZero, Ctail, Czero, hCtail, hCzero, ?_⟩
  intro H ι rows rowMap weight columns c fullI afull hafull hfull φ hpositive radius M hmask X hX
  dsimp only
  intro charts factors multiplicity hfiber hproduct Dzero N Amp hDzero hN hAmp hnorm
    hdivides hprofile B cal
  let profiles := fun i j => (c i * star (c j)) • φ
  let blocks := fun DE : FirstZeroLabel columns columns fullI fullI =>
    canonicalFirstCommonBlock C columns columns fullI fullI DE.val DE.property
  have hz := hzero C columns columns fullI fullI blocks profiles hDiff radius M X hX
    factors multiplicity hfiber hproduct Dzero N (Amp * (Ideal.absNorm Dzero : ℝ))
    hDzero hN (mul_nonneg hAmp (Nat.cast_nonneg _)) hnorm hdivides
    (fun DE i hi D hD => (charts DE ⟨D, hD⟩).left_mask i hi)
    (fun DE j hj D hD => (charts DE ⟨D, hD⟩).right_mask j hj)
    hprofile
  have hND : (Ideal.absNorm Dzero : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hDzero)
  have hz' : (∑ DE, ‖((blocks DE).secondFiniteSource hΓ hDiff C columns
      columns profiles M radius X hX).dualZeroTerm μv hDiff finiteTest‖) ≤
      Czero * (multiplicity * Amp) * N ^ ε := by
    apply hz.trans_eq
    field_simp [hND] <;> ring
  have hp := hstage rows rowMap weight columns c fullI afull hafull hfull
    φ hpositive radius M hmask X hX charts B cal
  apply hp.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  refine add_le_add (add_le_add ?_ le_rfl) le_rfl
  simpa only [mul_assoc] using hz'

include ν μ in
/-- The genuine whole-Gauss second source with its equal-original-ideal
diagonal and complete Gauss tail both paid. It retains the common-kernel
nonzero costs without replacing them by an assumed child inequality. -/
theorem gauss_second_stage_dual_terminal_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (Lmax Nsave ξ : ℝ) (hξ : 0 < ξ) :
    ∃ (decay : ℝ) (hdecay : 1 < decay),
      decay = tailDecayForWidth Lmax Nsave ξ ∧
      firstTailCutoffExponent Lmax Nsave decay ≤ ξ ∧
    ∃ sTail sZero : Finset (ℕ × ℕ), ∃ Cerror Czero : ℝ, 0 ≤ Cerror ∧ 0 < Czero ∧
    ∀ (Z : ℝ) {H ι : Type*} (rows : Finset H) (rowMap : H → Q) (weight : H → ℝ)
      (columns : Finset ι) (c : ι → ℂ) (fullI : ι → A.Exterior)
      (afull : ι → A.R) (hafull : ∀ i, A.Generates (fullI i) (afull i))
      (hfull : ∀ i ∈ columns, ∃ u : Kˣ, (u : K) = (afull i : K) ∧ A.IsAllowed C.correction.B u)
      (φ : SchwartzMap V ℂ)
      (hpositive : 0 ≤ (sIntegerTensorTerm K A.Sf (traceSchwartzToMixed K φ) finiteTest 0).re)
      (radius : {r : ℝ // 0 < r})
      (M : Finset (HeightOneSpectrum A.R)) (hmask : M = ∅)
      (prodExp profileExp maskExp inverseRadiusExp AmpTail : ℝ),
    let profiles := fun i j => (c i * star (c j)) • φ
    let blocks := fun DE : FirstZeroLabel columns columns fullI fullI =>
      canonicalFirstCommonBlock C columns columns fullI fullI DE.val DE.property
    ∀ W : SecondTailWindows C columns columns fullI fullI blocks sTail profiles radius M
      k Z prodExp profileExp maskExp inverseRadiusExp AmpTail,
    secondTailExponent k prodExp profileExp maskExp inverseRadiusExp ≤ Lmax →
    let X := Z ^ firstTailCutoffExponent Lmax Nsave decay
    let hX : 1 ≤ X := Real.one_le_rpow W.base_ge_one
      (firstTailCutoffExponent_nonneg Lmax Nsave decay hdecay)
    ∀ charts : ∀ DE, ∀ D : M.powerset,
      SecondBlockProfileChart (E := E) hΓ μv hDiff (blocks DE) C columns columns profiles
        finiteTest radius D.val,
    ∀ (Dzero : Ideal (𝓞 K)) (zeroProdExp AmpZero : ℝ), Dzero ≠ 0 →
      0 ≤ zeroProdExp → 0 ≤ AmpZero →
    (∀ ij ∈ columns ×ˢ columns, profiles ij.1 ij.2 ≠ 0 →
      (Ideal.absNorm ((fullI ij.1).val * (fullI ij.2).val) : ℝ) ≤ Z ^ zeroProdExp) →
    (∀ ij ∈ columns ×ˢ columns, profiles ij.1 ij.2 ≠ 0 →
      (fullI ij.1).val = (fullI ij.2).val → Dzero ∣ (fullI ij.1).val) →
    (∀ v ∈ firstZeroPairs columns columns fullI fullI,
      sZero.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
        A.exteriorNorm (fullI v.2.1) *
        (∑ D ∈ M.powerset, firstZeroDivisorWeight radius D) ≤
          AmpZero * (Ideal.absNorm Dzero : ℝ) / Real.sqrt (Z ^ zeroProdExp)) →
    ∀ B : ℕ, GaussEnergyChart rows rowMap weight φ
      (sIntegerFiniteTestFunction K A.Sf finiteTest) radius M B →
    X ≤ Z ^ ξ ∧
    weightedEnergy rows weight
      (fun h => ∑ i ∈ columns, c i *
        (generatedOriginalColumn (σ := σ) hΓ (fullI i) (afull i) (hafull i)).orbit hDiff (rowMap h)) ≤
      (B : ℝ) * (Czero * (W.multiplicity * AmpZero) * Z ^ (zeroProdExp * ε) +
        (∑ DE, ∑ D : M.powerset, (charts DE D).kernelCost M X hX) +
        Cerror * (W.multiplicity * AmpTail) * Z ^ (-Nsave)) := by
  let decay := tailDecayForWidth Lmax Nsave ξ
  have hdecay : 1 < decay := tailDecayForWidth_gt_one Lmax Nsave ξ hξ
  have hq : firstTailCutoffExponent Lmax Nsave decay ≤ ξ :=
    firstTailCutoffExponent_le_width Lmax Nsave ξ Lmax hξ le_rfl
  obtain ⟨order, hord⟩ := exists_nat_gt
    (max (Module.finrank ℤ L : ℝ) ((Module.finrank ℚ K : ℝ) * decay))
  have horder : Module.finrank ℤ L < order := by
    exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hord)
  have hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ (order : ℝ) :=
    (lt_of_le_of_lt (le_max_right _ _) hord).le
  obtain ⟨sTail, sZero, Ctail, Czero, hCtail, hCzero, hstage⟩ :=
    gauss_second_stage_dual_zero_bound (E := E) (hΓ := hΓ) (μv := μv) (ν := ν) (μ := μ)
      C hDiff Drecipe hD finiteTest hlc hcs k ε hε decay hdecay order horder hdegree
  let Cnum := 2 * firstTailFieldConstant K * idealCountConstant K ^ k
  have hCnum : 0 ≤ Cnum := mul_nonneg
    (mul_nonneg (by norm_num) firstTailFieldConstant_nonneg)
    (pow_nonneg (zero_le_one.trans (one_le_idealCountConstant K)) k)
  refine ⟨decay, hdecay, rfl, hq, sTail, sZero, Ctail * Cnum, Czero,
    mul_nonneg hCtail hCnum, hCzero, ?_⟩
  intro Z H ι rows rowMap weight columns c fullI afull hafull hfull φ hpositive radius M hmask
    prodExp profileExp maskExp inverseRadiusExp AmpTail
  dsimp only
  intro W hL charts Dzero zeroProdExp AmpZero hDzero hzeroProd hAmpZero hzeroNorm
    hdivides hprofile B cal
  let profiles := fun i j => (c i * star (c j)) • φ
  let blocks := fun DE : FirstZeroLabel columns columns fullI fullI =>
    canonicalFirstCommonBlock C columns columns fullI fullI DE.val DE.property
  let X := Z ^ firstTailCutoffExponent Lmax Nsave decay
  have hX : 1 ≤ X := Real.one_le_rpow W.base_ge_one
    (firstTailCutoffExponent_nonneg Lmax Nsave decay hdecay)
  have hp := hstage rows rowMap weight columns c fullI afull hafull hfull
    φ hpositive radius M hmask X hX charts W.factors W.multiplicity W.factors_fiber_card W.factor_product Dzero (Z ^ zeroProdExp) AmpZero
    hDzero (Real.one_le_rpow W.base_ge_one hzeroProd) hAmpZero hzeroNorm
    hdivides hprofile B cal
  change weightedEnergy rows weight
      (fun h => ∑ i ∈ columns, c i *
        (generatedOriginalColumn (σ := σ) hΓ (fullI i) (afull i) (hafull i)).orbit hDiff (rowMap h)) ≤
    (B : ℝ) * (Czero * (W.multiplicity * AmpZero) * (Z ^ zeroProdExp) ^ ε +
      (∑ DE, ∑ D : M.powerset, (charts DE D).kernelCost M X hX) +
      Ctail * X ^ (1 - decay) *
        secondBlockTailMass hΓ hDiff C columns columns fullI fullI blocks sTail profiles radius M) at hp
  have htail := terminal_tail_power_bound
    (secondBlockTailMass hΓ hDiff C columns columns fullI fullI blocks sTail profiles radius M)
    Cnum (W.multiplicity * AmpTail) Z (secondTailExponent k prodExp profileExp maskExp inverseRadiusExp)
    Lmax Nsave Ctail decay W.base_ge_one hdecay hL hCtail hCnum (mul_nonneg (Nat.cast_nonneg _) W.amplitude_nonneg) W.power_bound
  refine ⟨Real.rpow_le_rpow_of_exponent_le W.base_ge_one hq, ?_⟩
  rw [← Real.rpow_mul (zero_le_one.trans W.base_ge_one)] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl htail)
    (Nat.cast_nonneg B))

include ν μ in
/-- Uniform terminal control of every genuine Gauss source, with a
fixed small physical cutoff chosen before all moving source data. -/
theorem actual_gauss_stage_dual_terminal_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
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
      (hmask : s.mask = ∅)
      (hpositive : 0 ≤ (sIntegerTensorTerm K A.Sf
        (traceSchwartzToMixed K s.profile) finiteTest 0).re)
      (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay),
      s.cutoff ≤ Z ^ ξ ∧ G.energy hDiff ≤ T.cost ε Cerror Czero := by
  obtain ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero, hCerror, hCzero, hbound⟩ :=
    gauss_second_stage_dual_terminal_bound (E := E) (hΓ := hΓ) (μv := μv) (ν := ν) (μ := μ)
      C hDiff Drecipe hD finiteTest hlc hcs k ε hε Lmax Nsave ξ hξ
  refine ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero, hCerror, hCzero, ?_⟩
  intro Z ι G s hmask hpositive T
  have hb := hbound Z G.rows (engineElementOrbit (Γ := Γ)) (fun _ => 1)
    G.columns G.coefficient G.ideal G.generator G.generates
    (fun i hi => ⟨Units.mk0 (G.generator i : K) (by exact_mod_cast (G.generates i).1),
      rfl, G.allowed i hi⟩)
    s.profile hpositive s.radius s.mask hmask T.productExponent T.profileExponent T.maskExponent
    T.inverseRadiusExponent T.tailAmplitude T.windows T.exponent_bound s.charts
    T.zeroDivisor T.zeroProductExponent T.zeroAmplitude T.zeroDivisor_ne_zero
    T.zeroProductExponent_nonneg T.zeroAmplitude_nonneg T.zero_product_norm
    T.zero_divisor_dvd T.zero_normalization
    s.fiber s.calibration
  refine ⟨?_, ?_⟩
  · simpa only [T.cutoff_eq] using hb.1
  · rw [G.energy_eq_orbital hΓ hDiff]
    simpa only [ActualGaussStage.DualTerminalCalibration.cost, T.cutoff_eq] using hb.2


end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.gauss_second_stage_dual_zero_bound
#print axioms HeckeSkeleton.Moments.EngineStep.gauss_second_stage_dual_terminal_bound
#print axioms HeckeSkeleton.Moments.EngineStep.actual_gauss_stage_dual_terminal_bound
