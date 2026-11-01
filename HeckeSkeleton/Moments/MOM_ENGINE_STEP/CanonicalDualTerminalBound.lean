import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalDualTerminalWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualGaussDualRawTerminal

/-!
# Actual canonical second terminals from the original coefficient atoms

This is the concrete row-ball entry. It constructs the signed source,
pure-dual zero normalization, and tail windows from the same original
Gauss source and its per-column arithmetic data. The original tensor
at zero and the empty additional mask are established internally.
There is no whole-source, terminal, or profile-zero bound among the
inputs. The literal nonzero finite source remains for the actual
ordinary/exceptional row split and the two Fourier kernels.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

variable {K : Type} [Field K] [NumberField K]

variable {A : SArithmeticData K} {Γ : Subgroup A.U}
variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {htrace : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η htrace}
variable [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]

variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
variable (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- Uniform actual zero and tail bounds, with every amplitude computed
from the original frozen atoms and raw individual coefficient bounds. -/
theorem canonical_second_terminals_from_original_atoms
    (C : A.GeneralArithmeticContext σ η htrace)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ htrace C.correction.B Drecipe)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) (Lmax Nsave ξ : ℝ) (hξ : 0 < ξ) :
    ∃ (decay : ℝ) (hdecay : 1 < decay),
      decay = tailDecayForWidth Lmax Nsave ξ ∧
      firstTailCutoffExponent Lmax Nsave decay ≤ ξ ∧
    ∃ sTail sZero : Finset (ℕ × ℕ), ∃ Cerror Czero : ℝ, 0 ≤ Cerror ∧ 0 < Czero ∧
    ∀ (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2),
    ∀ {ι : Type*} (G : ActualGaussSource C ι),
    ∀ retainedScale Z g : ℝ, ∀ (hscale : 0 < retainedScale) (hZ : 0 < Z),
    ∀ cutoff : ℝ, ∀ hcutoff : 1 ≤ cutoff,
    ∀ hnorm : ∀ h ∈ G.rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g,
    ∀ {Θ : Type*} [Fintype Θ], ∀ dimension width : ℕ,
    ∀ character : ∀ DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
      SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ,
    ∀ dyad : ∀ DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
      SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
        Fin dimension → Fin (width + 1),
    ∀ {raw : ι → ℂ} {Sdiv : Ideal (𝓞 K)} {slots : ℕ} {B : ℝ},
    ∀ W : FirstDivisorCoefficientAtoms (A := A) (σ := σ) G.columns raw Sdiv slots B,
    ∀ hcoefficient : ∀ i ∈ G.columns,
      G.coefficient i = raw i / (A.exteriorNorm (G.ideal i) : ℂ),
    ∀ a₀ productExponent Krow radiusError columnError pairBound : ℝ,
    ∀ (hbase : 1 ≤ Z) (hproduct : 0 ≤ productExponent) (hpairBound : 0 ≤ pairBound),
    ∀ (factors : ι × ι → Fin k → Ideal (𝓞 K)) (multiplicity : ℕ),
    ∀ hfibers : ∀ v,
      ((G.columns ×ˢ G.columns).filter (fun ij => factors ij = v)).card ≤ multiplicity,
    ∀ hfactor : ∀ ij ∈ G.columns ×ˢ G.columns,
      PowerfulDiagonal.tupleIdeal (factors ij) = (G.ideal ij.1).val * (G.ideal ij.2).val,
    ∀ hproductNorm : ∀ ij ∈ G.columns ×ˢ G.columns,
      (Ideal.absNorm ((G.ideal ij.1).val * (G.ideal ij.2).val) : ℝ) ≤ Z ^ productExponent,
    ∀ hpair : ∀ i ∈ G.columns, ∀ j ∈ G.columns, W.active i → W.active j →
      ‖W.rawResidualCoefficient i‖ * ‖W.rawResidualCoefficient j‖ ≤ pairBound,
    ∀ hretained : retainedScale ≤ Z ^ (Krow + radiusError),
    ∀ hlower : ∀ i ∈ G.columns, Z ^ a₀ ≤ A.exteriorNorm (G.ideal i),
    ∀ hupper : ∀ i ∈ G.columns, A.exteriorNorm (G.ideal i) ≤ Z ^ (a₀ + columnError),
    ∀ hdegree : secondTailExponent k productExponent (-2 * a₀) 0
      (Krow + g + radiusError) ≤ Lmax,
    ∀ hcutoff_eq : cutoff = Z ^ firstTailCutoffExponent Lmax Nsave decay,
    let T := ActualGaussStage.canonicalDualResidualWindows
      (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
      dimension width character dyad W hcoefficient sTail sZero k Lmax Nsave decay
      a₀ productExponent Krow radiusError columnError pairBound
      hbase hproduct hpairBound factors multiplicity hfibers hfactor hproductNorm
      hpair hretained hlower hupper hdegree hcutoff_eq
    cutoff ≤ Z ^ ξ ∧ G.energy hDiff ≤ T.calibration.rawCost ε Cerror Czero := by
  obtain ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero, hCerror, hCzero, hbound⟩ :=
    actual_gauss_raw_dual_terminal_bound (E := ℝ) (ν := ν) (μ := μ) hΓ μv hDiff
      C Drecipe hD (rowBallFiniteFamily K A.Sf 1)
      (rowBallFiniteFamily_locallyConstant K A.Sf 1)
      (rowBallFiniteFamily_compactSupport K A.Sf 1) k ε hε Lmax Nsave ξ hξ
  refine ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero, hCerror, hCzero, ?_⟩
  intro δ hδ hδhalf ι G retainedScale Z g hscale hZ cutoff hcutoff hnorm
    Θ _ dimension width character dyad raw Sdiv slots B W hcoefficient
    a₀ productExponent Krow radiusError columnError pairBound
    hbase hproduct hpairBound factors multiplicity hfibers hfactor hproductNorm
    hpair hretained hlower hupper hdegree hcutoff_eq
  let stage := ActualGaussStage.canonicalUnmaskedRowBallByBlock
    (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
    dimension width character dyad
  let T := ActualGaussStage.canonicalDualResidualWindows
    (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
    dimension width character dyad W hcoefficient sTail sZero k Lmax Nsave decay
    a₀ productExponent Krow radiusError columnError pairBound
    hbase hproduct hpairBound factors multiplicity hfibers hfactor hproductNorm
    hpair hretained hlower hupper hdegree hcutoff_eq
  have hpositive : 0 ≤ (sIntegerTensorTerm K A.Sf
      (traceSchwartzToMixed K stage.profile) (rowBallFiniteFamily K A.Sf 1) 0).re := by
    change 0 ≤ (sIntegerTensorTerm K A.Sf
      (traceSchwartzToMixed K (CanonicalRowBall.archTest K A.Sf 1))
        (rowBallFiniteFamily K A.Sf 1) 0).re
    rw [CanonicalRowBall.originalTensor_zero, Complex.ofReal_re]
    exact inv_nonneg.mpr (CanonicalRowBall.mass_pos K A.Sf).le
  exact hbound Z G stage rfl hpositive T.calibration

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.canonical_second_terminals_from_original_atoms
