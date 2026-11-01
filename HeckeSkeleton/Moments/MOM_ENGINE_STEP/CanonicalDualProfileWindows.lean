import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalDualTerminalWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstLogBounds

/-!
# Original Mellin powers in the canonical pure-dual terminal windows

The genuine first logarithmic chart has numerator `c * Norm(I)^δ`.
Its moving power is retained in both the zero and tail exponents.
The numerical constants remain the fixed row-ball seminorms times
the original coefficient bound. Neither the scale nor a maximum over
the moving columns is inserted into such a constant.

The constructors preserve the same original frozen atoms, actual
inverse column norms, common-support factor tuple, multiplicity,
radius, complete source and physical cutoff. The earlier constructor
with a constant raw numerator remains available unchanged.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory

namespace CanonicalFirstLog

/-- Both literal numerator tilts are paid from their individual
original ideal windows. The two original coefficient constants are
fixed independently of the ideals and the scale. -/
theorem scaledTiltScalar_pair_norm_le_of_windows
    {N₁ N₂ Z B₁ B₂ δ C₁ C₂ : ℝ}
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hZ : 0 < Z) (hδ : 0 ≤ δ)
    (hwindow₁ : N₁ ≤ Z ^ B₁) (hwindow₂ : N₂ ≤ Z ^ B₂)
    (c₁ c₂ : ℂ) (hc₁ : ‖c₁‖ ≤ C₁) (hc₂ : ‖c₂‖ ≤ C₂) :
    ‖c₁ * ((N₁ ^ δ : ℝ) : ℂ)‖ * ‖c₂ * ((N₂ ^ δ : ℝ) : ℂ)‖ ≤
      (C₁ * C₂) * Z ^ ((B₁ + B₂) * δ) := by
  have h₁ : ‖c₁‖ * N₁ ^ δ ≤ C₁ * Z ^ (B₁ * δ) :=
    mul_le_mul hc₁ (tilt_le_of_norm_window hN₁ hZ hδ hwindow₁)
      (Real.rpow_nonneg hN₁.le _) ((norm_nonneg c₁).trans hc₁)
  have h₂ : ‖c₂‖ * N₂ ^ δ ≤ C₂ * Z ^ (B₂ * δ) :=
    mul_le_mul hc₂ (tilt_le_of_norm_window hN₂ hZ hδ hwindow₂)
      (Real.rpow_nonneg hN₂.le _) ((norm_nonneg c₂).trans hc₂)
  rw [scaledTiltScalar_norm hN₁, scaledTiltScalar_norm hN₂]
  calc
    _ ≤ (C₁ * Z ^ (B₁ * δ)) * (C₂ * Z ^ (B₂ * δ)) :=
      mul_le_mul h₁ h₂ (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hN₂.le _))
        (mul_nonneg ((norm_nonneg c₁).trans hc₁) (Real.rpow_nonneg hZ.le _))
    _ = _ := by rw [add_mul, Real.rpow_add hZ]; ring

/-- The reciprocal column phases in each real amplifier residual
presentation do not change the original numerator bound. -/
theorem scaledTiltScalar_phase_pair_norm_le_of_windows
    {N₁ N₂ Z B₁ B₂ δ C₁ C₂ : ℝ}
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hZ : 0 < Z) (hδ : 0 ≤ δ)
    (hwindow₁ : N₁ ≤ Z ^ B₁) (hwindow₂ : N₂ ≤ Z ^ B₂)
    (c₁ c₂ u₁ u₂ : ℂ) (hc₁ : ‖c₁‖ ≤ C₁) (hc₂ : ‖c₂‖ ≤ C₂)
    (hu₁ : ‖u₁‖ = 1) (hu₂ : ‖u₂‖ = 1) :
    ‖(c₁ * ((N₁ ^ δ : ℝ) : ℂ)) * u₁‖ *
        ‖(c₂ * ((N₂ ^ δ : ℝ) : ℂ)) * u₂‖ ≤
      (C₁ * C₂) * Z ^ ((B₁ + B₂) * δ) := by
  simpa only [norm_mul, hu₁, hu₂, mul_one] using
    scaledTiltScalar_pair_norm_le_of_windows hN₁ hN₂ hZ hδ hwindow₁ hwindow₂
      c₁ c₂ hc₁ hc₂

end CanonicalFirstLog

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
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace ActualGaussStage.DualResidualTerminalWindows

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
variable {raw : ι → ℂ} {Sdiv : Ideal (𝓞 K)} {slots : ℕ} {B : ℝ}

/-- Both raw profile powers are preserved when the two actual
inverse norms are installed. The coefficient atoms and their original
first-divisor denominator are unchanged. -/
def ofOriginalInverseNormWithProfileExponents
    (W : FirstDivisorCoefficientAtoms (A := A) (σ := σ) G.columns raw Sdiv slots B)
    (hcoefficient : ∀ i ∈ G.columns,
      G.coefficient i = raw i / (A.exteriorNorm (G.ideal i) : ℂ))
    (sTail sZero : Finset (ℕ × ℕ))
    (k : ℕ) (Z Lmax Nsave decay a₀ productExponent rawTailExponent rawZeroExponent
      maskExponent inverseRadiusExponent tailConstant zeroConstant columnError : ℝ)
    (hzeroConstant : 0 ≤ zeroConstant)
    (rawWindows : SecondTailWindows C G.columns G.columns G.ideal G.ideal
      (fun DE : FirstZeroLabel G.columns G.columns G.ideal G.ideal =>
        canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property)
      sTail (fun i j => (W.residualCoefficient i * star (W.residualCoefficient j)) • s.profile)
      s.radius s.mask k Z productExponent rawTailExponent maskExponent inverseRadiusExponent
      tailConstant)
    (hdegree : secondTailExponent k productExponent (rawTailExponent - 2 * a₀)
      maskExponent inverseRadiusExponent ≤ Lmax)
    (hcutoff : s.cutoff = Z ^ firstTailCutoffExponent Lmax Nsave decay)
    (hlower : ∀ i ∈ G.columns, Z ^ a₀ ≤ A.exteriorNorm (G.ideal i))
    (hupper : ∀ i ∈ G.columns, A.exteriorNorm (G.ideal i) ≤ Z ^ (a₀ + columnError))
    (hrawZero : ∀ v ∈ firstZeroPairs G.columns G.columns G.ideal G.ideal,
      sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
        ((W.residualCoefficient v.2.1 * star (W.residualCoefficient v.2.2)) • s.profile) ≤
          zeroConstant * Z ^ rawZeroExponent) :
    s.DualResidualTerminalWindows (W.withInverseNorm G.ideal G.coefficient hcoefficient)
      sTail sZero k Z Lmax Nsave decay where
  productExponent := productExponent
  profileExponent := rawTailExponent - 2 * a₀
  maskExponent := maskExponent
  inverseRadiusExponent := inverseRadiusExponent
  tailProfileConstant := tailConstant
  zeroProfileConstant := zeroConstant
  zeroProfileConstant_nonneg := hzeroConstant
  zeroProfileExponent := rawZeroExponent - 2 * a₀
  zeroColumnExponent := a₀ + columnError
  windows :=
    { rawWindows with
      profile_seminorm := by
        intro v hv
        have hm := (mem_firstZeroPairs G.columns G.columns G.ideal G.ideal v).mp hv
        exact W.withInverseNorm_gram_le G.ideal G.coefficient hcoefficient
          (sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ))
          s.profile v.2.1 v.2.2 Z a₀ rawTailExponent tailConstant
          (zero_lt_one.trans_le rawWindows.base_ge_one) rawWindows.amplitude_nonneg
          (hlower _ hm.1) (hlower _ hm.2.1) (rawWindows.profile_seminorm v hv) }
  exponent_bound := hdegree
  cutoff_eq := hcutoff
  residual_zero_profile := by
    intro v hv
    have hm := (mem_firstZeroPairs G.columns G.columns G.ideal G.ideal v).mp hv
    exact W.withInverseNorm_gram_le G.ideal G.coefficient hcoefficient
      (sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ))
      s.profile v.2.1 v.2.2 Z a₀ rawZeroExponent zeroConstant
      (zero_lt_one.trans_le rawWindows.base_ge_one) hzeroConstant
      (hlower _ hm.1) (hlower _ hm.2.1) (hrawZero v hv)
  column_norm := hupper

/-- The same original enlargement ledger retains the complete raw
pair exponent as an explicit small-power payment. -/
theorem zero_ledger_withProfileExponent
    {W : FirstDivisorCoefficientAtoms (A := A) (σ := σ)
      G.columns G.coefficient Sdiv slots B}
    {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Z Lmax Nsave decay : ℝ}
    (T : s.DualResidualTerminalWindows W sTail sZero k Z Lmax Nsave decay)
    (Aexp M c d qtilde K₀ Krow w wold g step padding
      boundary columnError productError radiusError a₀ allowanceExtra pairExponent
      εzero εpool ε : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hw : 0 ≤ w) (hwo : wold ≤ w)
    (hboundary : 0 ≤ boundary) (hallowance : 0 ≤ allowanceExtra)
    (hK₀ : K₀ = 2 * Aexp - c - d + qtilde - M)
    (hKrow : Krow - K₀ ≤ boundary)
    (hg : g ≤ max (d - c + (K₀ - Krow) - 2 * w + wold) 0 + 2 * step)
    (hprofile : T.zeroProfileExponent = pairExponent - 2 * a₀)
    (hcolumn : T.zeroColumnExponent ≤ a₀ + columnError)
    (hproduct : T.productExponent / 2 ≤ a₀ + productError)
    (hradius : T.inverseRadiusExponent ≤ Krow + g + radiusError)
    (hpayment : pairExponent + boundary + columnError + productError + radiusError +
      T.productExponent * εzero + εpool ≤ step + 5 * padding / 6 + ε) :
    T.zeroProfileExponent + T.zeroColumnExponent + T.inverseRadiusExponent +
        T.productExponent / 2 + T.productExponent * εzero ≤
      (Aexp - c + qtilde + allowanceExtra) +
        (max (Aexp - M) 0 + 3 * step + 5 * padding / 6 + ε) - εpool := by
  have hrow := second_zero_enlargement_allowance
    Aexp M c d qtilde K₀ Krow w wold g step boundary allowanceExtra
    hc hd hw hwo hboundary hallowance hK₀ hKrow hg
  linarith

end ActualGaussStage.DualResidualTerminalWindows

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

/-- The same canonical source with the explicit original numerator
power. Both profile exponents are `pairExponent - 2*a₀`; the constants
are the fixed row-ball seminorms multiplied by `pairBound`. -/
def canonicalDualResidualWindowsWithPairExponent
    {raw : ι → ℂ} {Sdiv : Ideal (𝓞 K)} {slots : ℕ} {B : ℝ}
    (W : FirstDivisorCoefficientAtoms (A := A) (σ := σ) G.columns raw Sdiv slots B)
    (hcoefficient : ∀ i ∈ G.columns,
      G.coefficient i = raw i / (A.exteriorNorm (G.ideal i) : ℂ))
    (sTail sZero : Finset (ℕ × ℕ))
    (k : ℕ) (Lmax Nsave decay a₀ productExponent Krow radiusError columnError
      pairBound pairExponent : ℝ)
    (hbase : 1 ≤ Z) (hproduct : 0 ≤ productExponent) (hpairBound : 0 ≤ pairBound)
    (factors : ι × ι → Fin k → Ideal (𝓞 K)) (multiplicity : ℕ)
    (hfibers : ∀ v,
      ((G.columns ×ˢ G.columns).filter (fun ij => factors ij = v)).card ≤ multiplicity)
    (hfactor : ∀ ij ∈ G.columns ×ˢ G.columns,
      PowerfulDiagonal.tupleIdeal (factors ij) = (G.ideal ij.1).val * (G.ideal ij.2).val)
    (hproductNorm : ∀ ij ∈ G.columns ×ˢ G.columns,
      (Ideal.absNorm ((G.ideal ij.1).val * (G.ideal ij.2).val) : ℝ) ≤ Z ^ productExponent)
    (hpair : ∀ i ∈ G.columns, ∀ j ∈ G.columns, W.active i → W.active j →
      ‖W.rawResidualCoefficient i‖ * ‖W.rawResidualCoefficient j‖ ≤
        pairBound * Z ^ pairExponent)
    (hretained : retainedScale ≤ Z ^ (Krow + radiusError))
    (hlower : ∀ i ∈ G.columns, Z ^ a₀ ≤ A.exteriorNorm (G.ideal i))
    (hupper : ∀ i ∈ G.columns, A.exteriorNorm (G.ideal i) ≤ Z ^ (a₀ + columnError))
    (hdegree : secondTailExponent k productExponent (pairExponent - 2 * a₀) 0
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
          (pairBound * CanonicalRowBall.terminalSeminorm A orders) * Z ^ pairExponent := by
    have hm := (mem_firstZeroPairs G.columns G.columns G.ideal G.ideal v).mp hv
    exact (W.rawResidual_pair_gram_seminorm_le
      (orders.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ))
      (CanonicalRowBall.archTest K A.Sf 1) v.2.1 v.2.2 (pairBound * Z ^ pairExponent)
      (mul_nonneg hpairBound (Real.rpow_nonneg hZ.le _))
      (hpair v.2.1 hm.1 v.2.2 hm.2.1)).trans_eq (by
        dsimp only [CanonicalRowBall.terminalSeminorm]
        ring)
  let rawWindows : SecondTailWindows C G.columns G.columns G.ideal G.ideal
      (fun DE : FirstZeroLabel G.columns G.columns G.ideal G.ideal =>
        canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property)
      sTail (fun i j => (W.residualCoefficient i * star (W.residualCoefficient j)) • stage.profile)
      stage.radius stage.mask k Z productExponent pairExponent 0 (Krow + g + radiusError)
      (pairBound * CanonicalRowBall.terminalSeminorm A sTail) := {
    base_ge_one := hbase
    productExponent_nonneg := hproduct
    amplitude_nonneg := htail
    factors := factors
    multiplicity := multiplicity
    factors_fiber_card := hfibers
    factor_product := hfactor
    product_norm := hproductNorm
    profile_seminorm := hprofile sTail
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
        _ = _ := by rw [← Real.rpow_add hZ]; congr 1; ring }
  exact DualResidualTerminalWindows.ofOriginalInverseNormWithProfileExponents stage
    W hcoefficient sTail sZero k Z Lmax Nsave decay a₀ productExponent
    pairExponent pairExponent 0 (Krow + g + radiusError)
    (pairBound * CanonicalRowBall.terminalSeminorm A sTail)
    (pairBound * CanonicalRowBall.terminalSeminorm A sZero) columnError
    hzero rawWindows hdegree hcutoff_eq hlower hupper (hprofile sZero)

end ActualGaussStage

namespace FirstBlockProfileChart

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable (b : FirstCommonCharacterBlock fullI fullJ DE)
variable (C : A.GeneralArithmeticContext σ η hS) (left : Finset ι) (right : Finset κ)
variable (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
variable (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
variable (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
variable (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
variable (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
variable (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)

/-- The actual left-column numerators of the first log chart supply
the new terminal constructor with the complete pair tilt. -/
theorem canonicalLogWithCoefficients_left_raw_pair_bound
    (c : ι → ℂ) (e : κ → ℂ) (i j : ι) {Z B₁ B₂ C₁ C₂ : ℝ} (hZ : 0 < Z)
    (hwindow₁ : A.exteriorNorm (b.leftResidual i) ≤ Z ^ B₁)
    (hwindow₂ : A.exteriorNorm (b.leftResidual j) ≤ Z ^ B₂)
    (hc₁ : ‖c i‖ ≤ C₁) (hc₂ : ‖c j‖ ≤ C₂) :
    let chart := canonicalLogWithCoefficients hΓ μv ν b C left right φ c e
      finiteTest hlc hcs radius D δ hδ hδhalf
    ‖chart.leftCoefficient i * (A.exteriorNorm (b.leftResidual i) : ℂ)‖ *
        ‖chart.leftCoefficient j * (A.exteriorNorm (b.leftResidual j) : ℂ)‖ ≤
      (C₁ * C₂) * Z ^ ((B₁ + B₂) * δ) := by
  dsimp only
  rw [canonicalLogWithCoefficients_left_raw_norm,
    canonicalLogWithCoefficients_left_raw_norm]
  have h := CanonicalFirstLog.scaledTiltScalar_pair_norm_le_of_windows
    (A.exteriorNorm_pos (b.leftResidual i)) (A.exteriorNorm_pos (b.leftResidual j))
    hZ hδ.le hwindow₁ hwindow₂ (c i) (c j) hc₁ hc₂
  rw [CanonicalFirstLog.scaledTiltScalar_norm (A.exteriorNorm_pos (b.leftResidual i)),
    CanonicalFirstLog.scaledTiltScalar_norm (A.exteriorNorm_pos (b.leftResidual j))] at h
  exact h

/-- The right original chart has its own two norm windows, with the
same exact exponent formula and no orientation symmetry assumption. -/
theorem canonicalLogWithCoefficients_right_raw_pair_bound
    (c : ι → ℂ) (e : κ → ℂ) (i j : κ) {Z B₁ B₂ C₁ C₂ : ℝ} (hZ : 0 < Z)
    (hwindow₁ : A.exteriorNorm (b.rightResidual i) ≤ Z ^ B₁)
    (hwindow₂ : A.exteriorNorm (b.rightResidual j) ≤ Z ^ B₂)
    (hc₁ : ‖e i‖ ≤ C₁) (hc₂ : ‖e j‖ ≤ C₂) :
    let chart := canonicalLogWithCoefficients hΓ μv ν b C left right φ c e
      finiteTest hlc hcs radius D δ hδ hδhalf
    ‖chart.rightCoefficient i * (A.exteriorNorm (b.rightResidual i) : ℂ)‖ *
        ‖chart.rightCoefficient j * (A.exteriorNorm (b.rightResidual j) : ℂ)‖ ≤
      (C₁ * C₂) * Z ^ ((B₁ + B₂) * δ) := by
  dsimp only
  rw [canonicalLogWithCoefficients_right_raw_norm,
    canonicalLogWithCoefficients_right_raw_norm]
  have h := CanonicalFirstLog.scaledTiltScalar_pair_norm_le_of_windows
    (A.exteriorNorm_pos (b.rightResidual i)) (A.exteriorNorm_pos (b.rightResidual j))
    hZ hδ.le hwindow₁ hwindow₂ (e i) (e j) hc₁ hc₂
  rw [CanonicalFirstLog.scaledTiltScalar_norm (A.exteriorNorm_pos (b.rightResidual i)),
    CanonicalFirstLog.scaledTiltScalar_norm (A.exteriorNorm_pos (b.rightResidual j))] at h
  exact h

end FirstBlockProfileChart
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalFirstLog.scaledTiltScalar_pair_norm_le_of_windows
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.DualResidualTerminalWindows.ofOriginalInverseNormWithProfileExponents
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.DualResidualTerminalWindows.zero_ledger_withProfileExponent
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalDualResidualWindowsWithPairExponent
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockProfileChart.canonicalLogWithCoefficients_left_raw_pair_bound
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockProfileChart.canonicalLogWithCoefficients_right_raw_pair_bound
