import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ZeroTerminalBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondTailBudget

/-!
# Actual source exits with both terminal terms paid

The original zero terms are bounded by the genuine powerful/equal-ideal
diagonals. The tails are bounded from individual original profiles,
generator windows, and injective whole-factor encodings. Neither an
aggregate zero estimate nor an aggregate tail estimate is an input.

The real decay, integer differentiability order, finite seminorm sets,
constants, and one common physical cutoff exponent are chosen before
every moving scale and original source. The same cutoff is at most
`Z ^ ξ`, regardless of the actual exponent inside the fixed box.
The only remaining terms are the actual nonzero pooled/kernel costs.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments MeasureTheory UniqueFactorizationMonoid
open HeckePort.CenteredMomentCounting

set_option maxHeartbeats 3000000

private theorem terminal_tail_of_power
    (mass Cnum Amp Z L Lmax N Ctail decay : ℝ)
    (hZ : 1 ≤ Z) (hdecay : 1 < decay) (hL : L ≤ Lmax)
    (hCtail : 0 ≤ Ctail) (hCnum : 0 ≤ Cnum) (hAmp : 0 ≤ Amp)
    (hmass : mass ≤ Cnum * Amp * Z ^ L) :
    Ctail * (Z ^ firstTailCutoffExponent Lmax N decay) ^ (1 - decay) * mass ≤
      (Ctail * Cnum) * Amp * Z ^ (-N) := by
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
  calc
    _ ≤ Ctail * (Z ^ firstTailCutoffExponent Lmax N decay) ^ (1 - decay) *
        (Cnum * Amp * Z ^ L) :=
      mul_le_mul_of_nonneg_left hmass
        (mul_nonneg hCtail (Real.rpow_nonneg (Real.rpow_nonneg hZ0 _) _))
    _ = (Ctail * Cnum) * Amp *
        ((Z ^ firstTailCutoffExponent Lmax N decay) ^ (1 - decay) * Z ^ L) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (first_tail_cutoff_power_of_le Z L Lmax N decay hZ hdecay hL)
      (mul_nonneg (mul_nonneg hCtail hCnum) hAmp)

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
local notation "Lattice" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

include ν μ in
/-- The actual first parent source exits into its genuine one-pool
nonzero cost plus two proved terminal budgets. The original whole
factor encoding in `W` also supplies the global zero-diagonal count. -/
theorem parent_first_stage_terminal_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (Lmax Nsave ξ : ℝ) (hξ : 0 < ξ) :
    ∃ (decay : ℝ) (hdecay : 1 < decay),
      decay = tailDecayForWidth Lmax Nsave ξ ∧
      firstTailCutoffExponent Lmax Nsave decay ≤ ξ ∧
    ∃ sTail sZero : Finset (ℕ × ℕ), ∃ Cerror Czero : ℝ, 0 ≤ Cerror ∧ 0 < Czero ∧
    ∀ (Z ell eps : ℝ) (bad : Finset (HeightOneSpectrum (𝓞 K)))
      (P : PowerScaleExteriorPool A bad Z ell eps),
    ∀ {ι : Type*} (columns : Finset ι) (fullI : ι → A.Exterior)
      (afull : ι → A.R) (hafull : ∀ i, A.Generates (fullI i) (afull i))
      (profiles : ι → ι → SchwartzMap V ℂ) (radius : {r : ℝ // 0 < r})
      (M : Finset (HeightOneSpectrum A.R))
      (prodExp profileExp maskExp modulusExp AmpTail : ℝ),
    let blocks := fun DE : FirstZeroLabel columns columns fullI fullI =>
      canonicalFirstCommonBlock C columns columns fullI fullI DE.val DE.property
    ∀ W : FirstTailWindows hΓ C columns columns fullI fullI blocks sTail profiles radius M
      k Z prodExp profileExp maskExp modulusExp AmpTail,
    firstTailExponent k prodExp profileExp maskExp modulusExp ≤ Lmax →
    let X := Z ^ firstTailCutoffExponent Lmax Nsave decay
    let hX : 1 ≤ X := Real.one_le_rpow W.base_ge_one
      (firstTailCutoffExponent_nonneg Lmax Nsave decay hdecay)
    ∀ charts : ∀ DE, ∀ D : ((blocks DE).mask M).powerset,
      FirstBlockProfileChart (E := E) hΓ μv (blocks DE) C columns columns profiles
        finiteTest radius D.val,
    ∀ pools : ∀ DE, ∀ D : ((blocks DE).mask M).powerset,
      FirstBlockPoolData (charts DE D) P M X hX,
    ∀ AmpZero : ℝ, 0 ≤ AmpZero →
    (∀ i ∈ columns, ∀ j ∈ columns, profiles i j 0 = 0) →
    (∀ v ∈ firstZeroPairs columns columns fullI fullI,
      sZero.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
        (∑ D ∈ ((blocks v.1).mask M).powerset, firstZeroDivisorWeight radius D) ≤
          AmpZero / Real.sqrt (Z ^ prodExp)) →
    ∀ {ω ψ₀ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ₀)
      (a : RealParameters) (t Y₁ Y₂ : ℝ) (B : ℕ),
    ParentSourceCalibration centered d a Z t Y₁ Y₂ columns
      (fun i j => (generatedOriginalColumn (σ := σ) hΓ (fullI i) (afull i) (hafull i)).originalPair
        (generatedOriginalColumn (σ := σ) hΓ (fullI j) (afull j) (hafull j)) (profiles i j))
      (sIntegerFiniteTestFunction K A.Sf finiteTest) radius M B →
    X ≤ Z ^ ξ ∧
    pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
      (B : ℝ) * (Czero * AmpZero * Z ^ (prodExp * ε) +
        (∑ DE, ∑ D : ((blocks DE).mask M).powerset, (pools DE D).pooledCost) +
        Cerror * AmpTail * Z ^ (-Nsave)) := by
  let decay := tailDecayForWidth Lmax Nsave ξ
  have hdecay : 1 < decay := tailDecayForWidth_gt_one Lmax Nsave ξ hξ
  have hq : firstTailCutoffExponent Lmax Nsave decay ≤ ξ :=
    firstTailCutoffExponent_le_width Lmax Nsave ξ Lmax hξ le_rfl
  obtain ⟨order, hord⟩ := exists_nat_gt
    (max (Module.finrank ℤ Lattice : ℝ) ((Module.finrank ℚ K : ℝ) * decay))
  have horder : Module.finrank ℤ Lattice < order := by
    exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hord)
  have hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ (order : ℝ) :=
    (lt_of_le_of_lt (le_max_right _ _) hord).le
  obtain ⟨sTail, sZero, Ctail, Czero, hCtail, hCzero, hstage⟩ :=
    parent_first_stage_zero_bound (E := E) (hΓ := hΓ) (μv := μv) (ν := ν) (μ := μ)
      C hDiff finiteTest hlc hcs k ε hε decay hdecay order horder hdegree
  let Cnum := 2 * firstTailFieldConstant K * idealCountConstant K ^ k
  have hCnum : 0 ≤ Cnum := mul_nonneg
    (mul_nonneg (by norm_num) firstTailFieldConstant_nonneg)
    (pow_nonneg (zero_le_one.trans (one_le_idealCountConstant K)) k)
  refine ⟨decay, hdecay, rfl, hq, sTail, sZero, Ctail * Cnum, Czero,
    mul_nonneg hCtail hCnum, hCzero, ?_⟩
  intro Z ell eps bad P ι columns fullI afull hafull profiles radius M
    prodExp profileExp maskExp modulusExp AmpTail
  dsimp only
  intro W hL charts pools AmpZero hAmpZero hannular hprofile
    ω ψ₀ centered d a t Y₁ Y₂ B cal
  let blocks := fun DE : FirstZeroLabel columns columns fullI fullI =>
    canonicalFirstCommonBlock C columns columns fullI fullI DE.val DE.property
  let X := Z ^ firstTailCutoffExponent Lmax Nsave decay
  have hX : 1 ≤ X := Real.one_le_rpow W.base_ge_one
    (firstTailCutoffExponent_nonneg Lmax Nsave decay hdecay)
  have hp := hstage Z ell eps bad P columns fullI afull hafull profiles radius M X hX
    charts pools W.factors W.factors_injective W.factor_product (Z ^ prodExp) AmpZero
    (Real.one_le_rpow W.base_ge_one W.productExponent_nonneg) hAmpZero W.product_norm
    hannular hprofile centered d a t Y₁ Y₂ B cal
  change pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
    (B : ℝ) * (Czero * AmpZero * (Z ^ prodExp) ^ ε +
      (∑ DE, ∑ D : ((blocks DE).mask M).powerset, (pools DE D).pooledCost) +
      Ctail * X ^ (1 - decay) *
        firstBlockTailMass hΓ C columns columns fullI fullI blocks sTail profiles radius M) at hp
  have htail := terminal_tail_of_power
    (firstBlockTailMass hΓ C columns columns fullI fullI blocks sTail profiles radius M)
    Cnum AmpTail Z (firstTailExponent k prodExp profileExp maskExp modulusExp)
    Lmax Nsave Ctail decay W.base_ge_one hdecay hL hCtail hCnum W.amplitude_nonneg W.power_bound
  refine ⟨Real.rpow_le_rpow_of_exponent_le W.base_ge_one hq, ?_⟩
  rw [← Real.rpow_mul (zero_le_one.trans W.base_ge_one)] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl htail)
    (Nat.cast_nonneg B))

include ν μ in
/-- The genuine whole-Gauss second source with its equal-original-ideal
diagonal and complete Gauss tail both paid. It retains the common-kernel
nonzero costs without replacing them by an assumed child inequality. -/
theorem gauss_second_stage_terminal_bound
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
      (φ : SchwartzMap V ℂ) (radius : {r : ℝ // 0 < r})
      (M : Finset (HeightOneSpectrum A.R))
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
    ∀ AmpZero : ℝ, 0 ≤ AmpZero → φ 0 = 0 →
    (∀ v ∈ firstZeroPairs columns columns fullI fullI,
      sZero.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
        A.exteriorNorm (fullI v.2.1) *
        (∑ D ∈ M.powerset, firstZeroDivisorWeight radius D) ≤
          AmpZero / Real.sqrt (Z ^ prodExp)) →
    ∀ B : ℕ, GaussEnergyChart rows rowMap weight φ
      (sIntegerFiniteTestFunction K A.Sf finiteTest) radius M B →
    X ≤ Z ^ ξ ∧
    weightedEnergy rows weight
      (fun h => ∑ i ∈ columns, c i *
        (generatedOriginalColumn (σ := σ) hΓ (fullI i) (afull i) (hafull i)).orbit hDiff (rowMap h)) ≤
      (B : ℝ) * (Czero * (W.multiplicity * AmpZero) * Z ^ (prodExp * ε) +
        (∑ DE, ∑ D : M.powerset, (charts DE D).kernelCost M X hX) +
        Cerror * (W.multiplicity * AmpTail) * Z ^ (-Nsave)) := by
  let decay := tailDecayForWidth Lmax Nsave ξ
  have hdecay : 1 < decay := tailDecayForWidth_gt_one Lmax Nsave ξ hξ
  have hq : firstTailCutoffExponent Lmax Nsave decay ≤ ξ :=
    firstTailCutoffExponent_le_width Lmax Nsave ξ Lmax hξ le_rfl
  obtain ⟨order, hord⟩ := exists_nat_gt
    (max (Module.finrank ℤ Lattice : ℝ) ((Module.finrank ℚ K : ℝ) * decay))
  have horder : Module.finrank ℤ Lattice < order := by
    exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hord)
  have hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ (order : ℝ) :=
    (lt_of_le_of_lt (le_max_right _ _) hord).le
  obtain ⟨sTail, sZero, Ctail, Czero, hCtail, hCzero, hstage⟩ :=
    gauss_second_stage_zero_bound (E := E) (hΓ := hΓ) (μv := μv) (ν := ν) (μ := μ)
      C hDiff Drecipe hD finiteTest hlc hcs k ε hε decay hdecay order horder hdegree
  let Cnum := 2 * firstTailFieldConstant K * idealCountConstant K ^ k
  have hCnum : 0 ≤ Cnum := mul_nonneg
    (mul_nonneg (by norm_num) firstTailFieldConstant_nonneg)
    (pow_nonneg (zero_le_one.trans (one_le_idealCountConstant K)) k)
  refine ⟨decay, hdecay, rfl, hq, sTail, sZero, Ctail * Cnum, Czero,
    mul_nonneg hCtail hCnum, hCzero, ?_⟩
  intro Z H ι rows rowMap weight columns c fullI afull hafull hfull φ radius M
    prodExp profileExp maskExp inverseRadiusExp AmpTail
  dsimp only
  intro W hL charts AmpZero hAmpZero hannular hprofile B cal
  let profiles := fun i j => (c i * star (c j)) • φ
  let blocks := fun DE : FirstZeroLabel columns columns fullI fullI =>
    canonicalFirstCommonBlock C columns columns fullI fullI DE.val DE.property
  let X := Z ^ firstTailCutoffExponent Lmax Nsave decay
  have hX : 1 ≤ X := Real.one_le_rpow W.base_ge_one
    (firstTailCutoffExponent_nonneg Lmax Nsave decay hdecay)
  have hp := hstage rows rowMap weight columns c fullI afull hafull hfull
    φ radius M X hX charts W.factors W.multiplicity W.factors_fiber_card W.factor_product (Z ^ prodExp) AmpZero
    (Real.one_le_rpow W.base_ge_one W.productExponent_nonneg) hAmpZero W.product_norm
    hannular hprofile B cal
  change weightedEnergy rows weight
      (fun h => ∑ i ∈ columns, c i *
        (generatedOriginalColumn (σ := σ) hΓ (fullI i) (afull i) (hafull i)).orbit hDiff (rowMap h)) ≤
    (B : ℝ) * (Czero * (W.multiplicity * AmpZero) * (Z ^ prodExp) ^ ε +
      (∑ DE, ∑ D : M.powerset, (charts DE D).kernelCost M X hX) +
      Ctail * X ^ (1 - decay) *
        secondBlockTailMass hΓ hDiff C columns columns fullI fullI blocks sTail profiles radius M) at hp
  have htail := terminal_tail_of_power
    (secondBlockTailMass hΓ hDiff C columns columns fullI fullI blocks sTail profiles radius M)
    Cnum (W.multiplicity * AmpTail) Z (secondTailExponent k prodExp profileExp maskExp inverseRadiusExp)
    Lmax Nsave Ctail decay W.base_ge_one hdecay hL hCtail hCnum (mul_nonneg (Nat.cast_nonneg _) W.amplitude_nonneg) W.power_bound
  refine ⟨Real.rpow_le_rpow_of_exponent_le W.base_ge_one hq, ?_⟩
  rw [← Real.rpow_mul (zero_le_one.trans W.base_ge_one)] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl htail)
    (Nat.cast_nonneg B))

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.parent_first_stage_terminal_bound
#print axioms HeckeSkeleton.Moments.EngineStep.gauss_second_stage_terminal_bound
