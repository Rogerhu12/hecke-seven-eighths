import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualTerminalCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalUnmaskedBlockStage

/-!
# Pure-dual terminal windows for the actual canonical second stage

The source is the existing canonical blockwise row-ball stage.  Its
profile is fixed, its additional row mask is empty, and its inverse
radius is exactly the retained original scale times the prescribed
enlargement power.  These facts are used internally.

The remaining inputs are the original coefficient factorization and
frozen atoms, individual active raw-coefficient pair bounds, original
column norm windows, and the genuine whole-factor tuple dictionary.
The tuple multiplicity is retained, so amplified residual columns are
not assumed injective.  Both resulting amplitudes keep the original
first-divisor denominator, and no whole terminal normalization is an
input.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}

namespace FirstDivisorCoefficientAtoms

variable {ι : Type*} {columns : Finset ι} {raw : ι → ℂ}
variable {Sdiv : Ideal (𝓞 K)} {slots : ℕ} {B : ℝ}
variable (W : FirstDivisorCoefficientAtoms (A := A) (σ := σ) columns raw Sdiv slots B)

/-- The actual active gates are kept.  Inactive raw coefficients need
no bound, and the individual active pair is the only scalar input. -/
theorem rawResidual_pair_gram_seminorm_le
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (p : Seminorm ℂ V) (φ : V) (i j : ι) (pairBound : ℝ) (hbound : 0 ≤ pairBound)
    (hpair : W.active i → W.active j →
      ‖W.rawResidualCoefficient i‖ * ‖W.rawResidualCoefficient j‖ ≤ pairBound) :
    p ((W.residualCoefficient i * star (W.residualCoefficient j)) • φ) ≤
      pairBound * p φ := by
  rw [map_smul_eq_mul, norm_mul, norm_star]
  apply mul_le_mul_of_nonneg_right _ (apply_nonneg _ _)
  by_cases hi : W.active i
  · by_cases hj : W.active j
    · simpa only [residualCoefficient, if_pos hi, if_pos hj] using hpair hi hj
    · simpa only [residualCoefficient, if_pos hi, if_neg hj, norm_zero, mul_zero]
        using hbound
  · simpa only [residualCoefficient, if_neg hi, norm_zero, zero_mul] using hbound

/-- A per-column raw bound supplies the active pair bound without
altering the actual residual coefficient. -/
theorem rawResidual_pair_bound_of_columns
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hraw : ∀ i ∈ columns, W.active i → ‖W.rawResidualCoefficient i‖ ≤ bound)
    (i j : ι) (hi : i ∈ columns) (hj : j ∈ columns)
    (hai : W.active i) (haj : W.active j) :
    ‖W.rawResidualCoefficient i‖ * ‖W.rawResidualCoefficient j‖ ≤ bound ^ 2 := by
  simpa only [pow_two] using
    mul_le_mul (hraw i hi hai) (hraw j hj haj) (norm_nonneg _) hbound

end FirstDivisorCoefficientAtoms

variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable {ν : Measure (FiniteAdeleRing (𝓞 K) K)} [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]

namespace CanonicalRowBall

/-- A fixed value on the original row-ball test, before the moving
source, retained scale, cutoff, and Fourier parameters. -/
def terminalSeminorm (A : SArithmeticData K)
    [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
    [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
    (orders : Finset (ℕ × ℕ)) : ℝ :=
  orders.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (archTest K A.Sf 1)

theorem terminalSeminorm_nonneg (orders : Finset (ℕ × ℕ)) :
    0 ≤ terminalSeminorm A orders := apply_nonneg _ _

end CanonicalRowBall

namespace ActualGaussStage

variable (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
variable {ι : Type*} (G : ActualGaussSource C ι)
variable (retainedScale Z g : ℝ) (hscale : 0 < retainedScale) (hZ : 0 < Z)
variable (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
variable (hnorm : ∀ h ∈ G.rows,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable {Θ : Type*} [Fintype Θ] (dimension width : ℕ)
variable (character : ∀ DE : commonSupportPool G.columns G.columns
  (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ DE : commonSupportPool G.columns G.columns
  (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))

/-- Original factor and coefficient dictionaries construct all
terminal windows of this same canonical source.  The empty mask and
the exact inverse radius are proved, not supplied as calibration. -/
def canonicalDualResidualWindows
    {raw : ι → ℂ} {Sdiv : Ideal (𝓞 K)} {slots : ℕ} {B : ℝ}
    (W : FirstDivisorCoefficientAtoms (A := A) (σ := σ)
      G.columns raw Sdiv slots B)
    (hcoefficient : ∀ i ∈ G.columns,
      G.coefficient i = raw i / (A.exteriorNorm (G.ideal i) : ℂ))
    (sTail sZero : Finset (ℕ × ℕ))
    (k : ℕ) (Lmax Nsave decay a₀ productExponent Krow radiusError columnError pairBound : ℝ)
    (hbase : 1 ≤ Z) (hproduct : 0 ≤ productExponent) (hpairBound : 0 ≤ pairBound)
    (factors : ι × ι → Fin k → Ideal (𝓞 K)) (multiplicity : ℕ)
    (hfibers : ∀ v,
      ((G.columns ×ˢ G.columns).filter (fun ij => factors ij = v)).card ≤ multiplicity)
    (hfactor : ∀ ij ∈ G.columns ×ˢ G.columns,
      PowerfulDiagonal.tupleIdeal (factors ij) = (G.ideal ij.1).val * (G.ideal ij.2).val)
    (hproductNorm : ∀ ij ∈ G.columns ×ˢ G.columns,
      (Ideal.absNorm ((G.ideal ij.1).val * (G.ideal ij.2).val) : ℝ) ≤ Z ^ productExponent)
    (hpair : ∀ i ∈ G.columns, ∀ j ∈ G.columns, W.active i → W.active j →
      ‖W.rawResidualCoefficient i‖ * ‖W.rawResidualCoefficient j‖ ≤ pairBound)
    (hretained : retainedScale ≤ Z ^ (Krow + radiusError))
    (hlower : ∀ i ∈ G.columns, Z ^ a₀ ≤ A.exteriorNorm (G.ideal i))
    (hupper : ∀ i ∈ G.columns, A.exteriorNorm (G.ideal i) ≤ Z ^ (a₀ + columnError))
    (hdegree : secondTailExponent k productExponent (-2 * a₀) 0
      (Krow + g + radiusError) ≤ Lmax)
    (hcutoff_eq : cutoff = Z ^ firstTailCutoffExponent Lmax Nsave decay) :
    (canonicalUnmaskedRowBallByBlock (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
      dimension width character dyad).DualResidualTerminalWindows
        (W.withInverseNorm G.ideal G.coefficient hcoefficient)
        sTail sZero k Z Lmax Nsave decay := by
  let stage := canonicalUnmaskedRowBallByBlock
    (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
    dimension width character dyad
  have htail : 0 ≤ pairBound * CanonicalRowBall.terminalSeminorm A sTail :=
    mul_nonneg hpairBound (CanonicalRowBall.terminalSeminorm_nonneg sTail)
  have hzero : 0 ≤ pairBound * CanonicalRowBall.terminalSeminorm A sZero :=
    mul_nonneg hpairBound (CanonicalRowBall.terminalSeminorm_nonneg sZero)
  have hprofile (orders : Finset (ℕ × ℕ))
      (v : FirstZeroLabel G.columns G.columns G.ideal G.ideal × (ι × ι))
      (hv : v ∈ firstZeroPairs G.columns G.columns G.ideal G.ideal) :
      orders.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
        ((W.residualCoefficient v.2.1 * star (W.residualCoefficient v.2.2)) • stage.profile) ≤
          pairBound * CanonicalRowBall.terminalSeminorm A orders := by
    have hm := (mem_firstZeroPairs G.columns G.columns G.ideal G.ideal v).mp hv
    exact W.rawResidual_pair_gram_seminorm_le
      (orders.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ))
      (CanonicalRowBall.archTest K A.Sf 1) v.2.1 v.2.2 pairBound hpairBound
      (hpair v.2.1 hm.1 v.2.2 hm.2.1)
  let rawWindows : SecondTailWindows C G.columns G.columns G.ideal G.ideal
      (fun DE : FirstZeroLabel G.columns G.columns G.ideal G.ideal =>
        canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property)
      sTail (fun i j => (W.residualCoefficient i * star (W.residualCoefficient j)) • stage.profile)
      stage.radius stage.mask k Z productExponent 0 0 (Krow + g + radiusError)
      (pairBound * CanonicalRowBall.terminalSeminorm A sTail) := {
    base_ge_one := hbase
    productExponent_nonneg := hproduct
    amplitude_nonneg := htail
    factors := factors
    multiplicity := multiplicity
    factors_fiber_card := hfibers
    factor_product := hfactor
    product_norm := hproductNorm
    profile_seminorm := by
      intro v hv
      simpa only [Real.rpow_zero, mul_one] using hprofile sTail v hv
    mask_norm := by
      change (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅)).val ≤ Z ^ (0 : ℝ)
      rw [sIntegerMaskGenerator_empty_norm K A.Sf, Real.rpow_zero]
    inverse_radius := by
      change ((retainedScale * Z ^ g)⁻¹)⁻¹ ≤ Z ^ (Krow + g + radiusError)
      rw [inv_inv]
      calc
        _ ≤ Z ^ (Krow + radiusError) * Z ^ g :=
          mul_le_mul_of_nonneg_right hretained (Real.rpow_nonneg hZ.le _)
        _ = _ := by
          rw [← Real.rpow_add hZ]
          congr 1
          ring }
  exact DualResidualTerminalWindows.ofOriginalInverseNorm stage W hcoefficient
    sTail sZero k Z Lmax Nsave decay a₀ productExponent 0 0
    (Krow + g + radiusError)
    (pairBound * CanonicalRowBall.terminalSeminorm A sTail)
    (pairBound * CanonicalRowBall.terminalSeminorm A sZero) columnError
    hzero rawWindows (by simpa only [zero_sub, neg_mul] using hdegree)
    hcutoff_eq hlower hupper (hprofile sZero)

end ActualGaussStage

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstDivisorCoefficientAtoms.rawResidual_pair_gram_seminorm_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalDualResidualWindows
