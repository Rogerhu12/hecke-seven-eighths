import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualGaussRawTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualStageTerminalBudget

/-!
# Signed complete second source before its ordinary/exceptional split

The nonzero source is the literal original finite row sum. Its pure
dual zero is estimated only after the whole original-origin square
has been kept with its negative Poisson sign. The same original
profile, finite cutoff, row mask, and all tuple fibres are retained.
The constructed terminal cost is therefore ready for the actual
hybrid row partition without a profile-zero assumption.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments MeasureTheory
open HeckePort.CenteredMomentCounting

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
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Lattice" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

namespace ActualGaussStage

variable {hΓ μv hDiff}
variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)

def rawDualZeroCost : ℝ :=
  ∑ DE, ‖(s.sources DE).dualZeroTerm μv hDiff finiteTest‖

def rawDualFiniteCost (seminorms : Finset (ℕ × ℕ)) (Ctail decay : ℝ) : ℝ :=
  (s.fiber : ℝ) * (s.rawDualZeroCost + s.rawNonzeroCost +
    Ctail * s.cutoff ^ (1 - decay) * s.rawTailMass seminorms)

namespace DualTerminalCalibration

variable {s} {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Z Lmax Nsave decay : ℝ}

def rawCost (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (ε Cerror Czero : ℝ) : ℝ :=
  (s.fiber : ℝ) * (Czero * (T.windows.multiplicity * T.zeroAmplitude) *
      Z ^ (T.zeroProductExponent * ε) + s.rawNonzeroCost +
    Cerror * (T.windows.multiplicity * T.tailAmplitude) * Z ^ (-Nsave))

end DualTerminalCalibration
end ActualGaussStage

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- Uniform genuine second Poisson, retaining the raw nonzero finite
source for the later hybrid exceptional/ordinary decomposition. -/
theorem actual_gauss_raw_dual_finite_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (decay : ℝ) (hdecay : 1 < decay) (order : ℕ)
    (horder : Module.finrank ℤ Lattice < order)
    (hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ order) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ Ctail : ℝ, 0 ≤ Ctail ∧
    ∀ {ι : Type*} (G : ActualGaussSource C ι)
      (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
      (hmask : s.mask = ∅)
      (hpositive : 0 ≤ (sIntegerTensorTerm K A.Sf
        (traceSchwartzToMixed K s.profile) finiteTest 0).re),
      G.energy hDiff ≤ s.rawDualFiniteCost seminorms Ctail decay := by
  obtain ⟨seminorms, Ctail, hCtail, htail⟩ := finite_source_uniform_bound
    (K := K) (S := A.Sf) (Γ := Γ) ν μv μ hDiff finiteTest hlc hcs
    decay hdecay order horder hdegree
  refine ⟨seminorms, Ctail, hCtail, ?_⟩
  intro ι G s hmask hpositive
  let series := fun DE =>
    ∑ i ∈ (s.sources DE).leftColumns, ∑ j ∈ (s.sources DE).rightColumns,
      ((s.sources DE).pairs i j).maskedSeries
        (sIntegerFiniteTestFunction K A.Sf finiteTest) s.radius s.mask
  have hfull (i : ι) (hi : i ∈ G.columns) :
      ∃ u : Kˣ, (u : K) = (G.generator i : K) ∧ A.IsAllowed C.correction.B u :=
    ⟨Units.mk0 (G.generator i : K) (by exact_mod_cast (G.generates i).1),
      rfl, G.allowed i hi⟩
  have hp := gauss_energy_orbital_source_bound hDiff G.rows (engineElementOrbit (Γ := Γ))
    (fun _ => 1) G.columns G.coefficient
    (fun i => generatedOriginalColumn (σ := σ) hΓ (G.ideal i) (G.generator i) (G.generates i))
    s.profile (sIntegerFiniteTestFunction K A.Sf finiteTest)
    (continuous_sIntegerFiniteTestFunction K A.Sf finiteTest hlc)
    (hasCompactSupport_sIntegerFiniteTestFunction K A.Sf finiteTest hcs)
    s.radius s.mask s.fiber s.calibration
  rw [common_support_gauss_sources hΓ hDiff C Drecipe hD G.columns G.columns G.ideal G.ideal
    G.generator G.generator G.generates G.generates hfull hfull] at hp
  change _ ≤ (s.fiber : ℝ) * (∑ DE, series DE).re at hp
  rw [G.energy_eq_orbital hΓ hDiff]
  apply hp.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg s.fiber)
  rw [Complex.re_sum]
  have hpoint (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val)) :
      (series DE).re ≤ (‖(s.sources DE).dualZeroTerm μv hDiff finiteTest‖ +
        (∑ D : s.mask.powerset,
          ‖∑ t ∈ (s.sources DE).rows,
            ∑ i ∈ (s.sources DE).leftColumns, ∑ j ∈ (s.sources DE).rightColumns,
              ((s.sources DE).pairs i j).transformedRow μv hDiff finiteTest s.radius D.val t‖) +
        Ctail * s.cutoff ^ (1 - decay) *
          ∑ i ∈ (s.sources DE).leftColumns, ∑ j ∈ (s.sources DE).rightColumns,
            seminorms.sup (schwartzSeminormFamily ℂ V ℂ) ((s.sources DE).pairs i j).profile *
              ((s.sources DE).pairs i j).truncationMass (s.sources DE).mask s.radius) -
                ((s.sources DE).originZeroTerm finiteTest).re := by
    have ht := htail (s.sources DE)
    have hre := Complex.re_le_norm (series DE - (s.sources DE).transform μv hDiff finiteTest)
    rw [Complex.sub_re] at hre
    have hfinite := (s.sources DE).transform_re_le_dual_rows μv hDiff finiteTest
    change ‖series DE - (s.sources DE).transform μv hDiff finiteTest‖ ≤ _ at ht
    exact ((sub_le_iff_le_add.mp (hre.trans ht)).trans
      (add_le_add le_rfl hfinite)).trans_eq (by ring)
  have ho : 0 ≤ (∑ DE, (s.sources DE).originZeroTerm finiteTest).re := by
    simpa only [ActualGaussStage.sources, hmask] using
      common_support_gauss_origin_nonneg hΓ hDiff C G.columns G.coefficient
        G.ideal G.generator G.generates s.profile finiteTest hpositive
        s.radius s.cutoff s.cutoff_one
  rw [Complex.re_sum] at ho
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun DE _ => hpoint DE)
  rw [Finset.sum_sub_distrib] at hsum
  have hdrop := hsum.trans (sub_le_self _ ho)
  simpa only [ActualGaussStage.rawDualZeroCost, ActualGaussStage.rawNonzeroCost,
    ActualGaussStage.rawTailMass, Finset.sum_add_distrib, Finset.mul_sum] using hdrop

include ν μ in
/-- Zero and tail constants are fixed before every moving source.  The
remaining expression is its literal nonzero second finite source, ready
for the proved actual support partition and pre-Cauchy hybrid estimate. -/
theorem actual_gauss_raw_dual_terminal_bound
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
      (hmask : s.mask = ∅)
      (hpositive : 0 ≤ (sIntegerTensorTerm K A.Sf
        (traceSchwartzToMixed K s.profile) finiteTest 0).re)
      (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay),
      s.cutoff ≤ Z ^ ξ ∧ G.energy hDiff ≤ T.rawCost ε Cerror Czero := by
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
  obtain ⟨sTail, Ctail, hCtail, hraw⟩ :=
    actual_gauss_raw_dual_finite_bound (E := E) (ν := ν) (μ := μ) hΓ μv hDiff C Drecipe hD
      finiteTest hlc hcs decay hdecay order horder hdegree
  obtain ⟨sZero, Czero, hCzero, hzero⟩ :=
    second_dualZero_diagonal_supported_of_divisor (σ := σ) (η := η) (hS := hS)
      (hΓ := hΓ) (μv := μv) finiteTest k ε hε
  let Cnum := 2 * firstTailFieldConstant K * idealCountConstant K ^ k
  have hCnum : 0 ≤ Cnum := mul_nonneg
    (mul_nonneg (by norm_num) firstTailFieldConstant_nonneg)
    (pow_nonneg (zero_le_one.trans (one_le_idealCountConstant K)) k)
  refine ⟨decay, hdecay, rfl, hq, sTail, sZero, Ctail * Cnum, Czero,
    mul_nonneg hCtail hCnum, hCzero, ?_⟩
  intro Z ι G s hmask hpositive T
  let profiles := fun i j => (G.coefficient i * star (G.coefficient j)) • s.profile
  let blocks := fun DE : FirstZeroLabel G.columns G.columns G.ideal G.ideal =>
    canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property
  have hz := hzero C G.columns G.columns G.ideal G.ideal blocks profiles hDiff s.radius s.mask
    s.cutoff s.cutoff_one T.windows.factors T.windows.multiplicity T.windows.factors_fiber_card
    T.windows.factor_product T.zeroDivisor (Z ^ T.zeroProductExponent)
    (T.zeroAmplitude * (Ideal.absNorm T.zeroDivisor : ℝ)) T.zeroDivisor_ne_zero
    (Real.one_le_rpow T.windows.base_ge_one T.zeroProductExponent_nonneg)
    (mul_nonneg T.zeroAmplitude_nonneg (Nat.cast_nonneg _))
    T.zero_product_norm T.zero_divisor_dvd
    (fun DE i hi D hD => (s.charts DE ⟨D, hD⟩).left_mask i hi)
    (fun DE j hj D hD => (s.charts DE ⟨D, hD⟩).right_mask j hj)
    T.zero_normalization
  change s.rawDualZeroCost ≤ Czero * T.windows.multiplicity *
    (T.zeroAmplitude * (Ideal.absNorm T.zeroDivisor : ℝ)) *
      (Z ^ T.zeroProductExponent) ^ ε / (Ideal.absNorm T.zeroDivisor : ℝ) at hz
  rw [← Real.rpow_mul (zero_le_one.trans T.windows.base_ge_one)] at hz
  have hND : (Ideal.absNorm T.zeroDivisor : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr T.zeroDivisor_ne_zero)
  have hz' : s.rawDualZeroCost ≤ Czero * (T.windows.multiplicity * T.zeroAmplitude) *
      Z ^ (T.zeroProductExponent * ε) := by
    apply hz.trans_eq
    field_simp [hND] <;> ring
  have hmass := T.windows.power_bound (hΓ := hΓ) (hDiff := hDiff)
  change s.rawTailMass sTail ≤ Cnum * (T.windows.multiplicity * T.tailAmplitude) *
    Z ^ secondTailExponent k T.productExponent T.profileExponent T.maskExponent
      T.inverseRadiusExponent at hmass
  have ht := terminal_tail_power_bound (s.rawTailMass sTail) Cnum
    (T.windows.multiplicity * T.tailAmplitude) Z
    (secondTailExponent k T.productExponent T.profileExponent T.maskExponent T.inverseRadiusExponent)
    Lmax Nsave Ctail decay T.windows.base_ge_one hdecay T.exponent_bound hCtail hCnum
    (mul_nonneg (Nat.cast_nonneg _) T.windows.amplitude_nonneg) hmass
  rw [← T.cutoff_eq] at ht
  refine ⟨?_, ?_⟩
  · rw [T.cutoff_eq]
    exact Real.rpow_le_rpow_of_exponent_le T.windows.base_ge_one hq
  · apply (hraw G s hmask hpositive).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg s.fiber)
    exact add_le_add (add_le_add hz' le_rfl) ht

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_gauss_raw_dual_finite_bound
#print axioms HeckeSkeleton.Moments.EngineStep.actual_gauss_raw_dual_terminal_bound
