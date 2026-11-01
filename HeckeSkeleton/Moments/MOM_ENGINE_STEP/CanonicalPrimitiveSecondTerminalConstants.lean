import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualDirectSecondStages
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualPoolTerminal

/-!
# One fixed second-terminal choice for both original sources

The raw second-stage theorem chooses its integer decay order and both
finite seminorm sets before the source. This file selects that theorem
once at the fixed numerical box. The direct Fourier estimate and every
tag of the original pool use the same two seminorm sets and constants.
No stage, calibration, source or chosen child is reconstructed here.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

universe u

namespace HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveSecondTerminalConstants

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments MeasureTheory
open CanonicalPrimitiveEngineChoices

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
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)

/-- All analytic choices precede the scale and the moving source.
The full pre-removal tuple length is `2 * (cap + 2)`. -/
structure Fixed (C : A.GeneralArithmeticContext σ η hS)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (b : Box) where
  sTail : Finset (ℕ × ℕ)
  sZero : Finset (ℕ × ℕ)
  Cerror : ℝ
  Czero : ℝ
  Cerror_nonneg : 0 ≤ Cerror
  Czero_pos : 0 < Czero
  raw_bound : ∀ (Z : ℝ) {ι : Type u} (G : ActualGaussSource C ι)
    (s : ActualGaussStage (E := ℝ) hΓ μv hDiff G finiteTest)
    (hmask : s.mask = ∅)
    (hpositive : 0 ≤ (sIntegerTensorTerm K A.Sf
      (traceSchwartzToMixed K s.profile) finiteTest 0).re)
    (T : s.DualTerminalCalibration sTail sZero (2 * (b.cap + 2))
      Z b.secondDegree b.saving b.secondDecay),
    s.cutoff ≤ Z ^ b.loss ∧ G.energy hDiff ≤ T.rawCost b.tilt Cerror Czero

namespace Fixed

variable {hΓ μv hDiff}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {b : Box}
variable (F : Fixed.{u} hΓ μv hDiff C finiteTest b)

/-- The original first Fourier multiplier preserves the source profile
and uses precisely the selected raw second-stage constants. -/
theorem direct_bound (Z : ℝ) {ι : Type u} (G : ActualGaussSource C ι)
    (s : ActualGaussStage (E := ℝ) hΓ μv hDiff G finiteTest)
    (hmask : s.mask = ∅)
    (hpositive : 0 ≤ (sIntegerTensorTerm K A.Sf
      (traceSchwartzToMixed K s.profile) finiteTest 0).re)
    (T : s.DualTerminalCalibration F.sTail F.sZero (2 * (b.cap + 2))
      Z b.secondDegree b.saving b.secondDecay)
    (x : ι → ℝ) (ξ : ℝ) :
    G.phaseEnergy (hDiff := hDiff) x ξ ≤
      (T.fourierPhase x ξ).rawCost b.tilt F.Cerror F.Czero := by
  exact (F.raw_bound Z (G.withMultiplier (fun i => jointPhase ξ (x i)))
    (s.withMultiplier (fun i => jointPhase ξ (x i))) hmask hpositive
      (T.fourierPhase x ξ)).2

/-- The same choice controls all four genuine pool tags. Their actual
prime, valuation, density and local weights remain in `rawPhaseCost`. -/
theorem pool_bound
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
    (Z ell eps : ℝ) (bad : Finset (HeightOneSpectrum (𝓞 K)))
    (P : PowerScaleExteriorPool A bad Z ell eps)
    {ι : Type u} (d : FirstGaussPoolData C P ι) (c : ι → ℂ) (x : ι → ℝ)
    (s : ActualPoolStages (E := ℝ) hΓ μv hDiff d c finiteTest)
    (hs : s.DualSourceConditions)
    (T : s.DualTerminalCalibration F.sTail F.sZero (2 * (b.cap + 2))
      b.secondDegree b.saving b.secondDecay) (ξ : ℝ) :
    d.energy (FirstGaussPoolData.twistedCoefficient c x ξ) ≤
      T.rawPhaseCost x ξ b.tilt F.Cerror F.Czero := by
  rw [d.energy_eq_tag_sources hDiff Drecipe hD]
  simp_rw [d.tagSource_twisted c x ξ]
  unfold ActualPoolStages.DualTerminalCalibration.rawPhaseCost
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) d.density_pos.le)
  exact Finset.sum_le_sum fun tag _ => mul_le_mul_of_nonneg_left
    (F.raw_bound Z _ ((s.tag tag).withMultiplier (fun i => jointPhase ξ (d.tagPoint x tag i)))
      (hs.tag_fourierPhase_mask x ξ tag) (hs.tag_fourierPhase_origin_nonneg x ξ tag)
      ((T.tag tag).fourierPhase (d.tagPoint x tag) ξ)).2
    (d.tagWeight_nonneg tag)

end Fixed

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
variable (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- The original raw terminal theorem supplies one common choice. Its
internal integer order already exceeds the lattice dimension and the
field degree times the chosen decay. -/
theorem exists_fixed
    (C : A.GeneralArithmeticContext σ η hS)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (b : Box) : Nonempty (Fixed.{u} hΓ μv hDiff C finiteTest b) := by
  obtain ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero,
      hCerror, hCzero, hraw⟩ :=
    actual_gauss_raw_dual_terminal_bound (E := ℝ) (ν := ν) (μ := μ)
      hΓ μv hDiff C Drecipe hD finiteTest hlc hcs (2 * (b.cap + 2))
      b.tilt b.tilt_pos b.secondDegree b.saving b.loss b.loss_pos
  have he : decay = b.secondDecay := hchoice
  rw [he] at hraw
  exact ⟨{
    sTail := sTail
    sZero := sZero
    Cerror := Cerror
    Czero := Czero
    Cerror_nonneg := hCerror
    Czero_pos := hCzero
    raw_bound := hraw }⟩

/-- This selection depends only on fixed arithmetic and analytic data,
before every parent, scale, allocation and individual character input. -/
def choose
    (C : A.GeneralArithmeticContext σ η hS)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (b : Box) : Fixed.{u} hΓ μv hDiff C finiteTest b :=
  Classical.choice (exists_fixed (ν := ν) (μ := μ) hΓ μv hDiff
    C Drecipe hD finiteTest hlc hcs b)

end HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveSecondTerminalConstants

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveSecondTerminalConstants.exists_fixed
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveSecondTerminalConstants.choose
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveSecondTerminalConstants.Fixed.direct_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveSecondTerminalConstants.Fixed.pool_bound
