import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDivisorNormCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.GaussPhaseTerminal

/-!
# Original terminal amplitudes for the pure dual zero

The fixed row-ball profile may be nonzero at the additive origin.
These records retain every original terminal window and scalar while
omitting the false profile-zero requirement.  The zero normalization
is used for the pure dual-frequency zero; the signed original-origin
term is handled separately by the whole Gram source.

Both amplitudes are constructed from the original frozen coefficient
atoms.  Their factor `B^slots / Norm(S)` is retained exactly.  The two
inverse column norms are proved by the existing raw seminorm lemma,
without improving the raw residual coefficient bounds.  Fourier
phases of norm one preserve these same amplitudes.

No bound for the whole transformed source or the final engine output
is supplied or proved here.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory HeckePort.Moments

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
  {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace ActualGaussStage

variable {hΓ μv hDiff}
variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

/-- Raw, per-source terminal data. `windows` supplies individual
seminorm and norm bounds with a proved finite whole-factor fibre.
Residual sources use the actual valuation-allocation multiplicity.
`zero_normalization` is the original pair scalar bound for the pure
dual-frequency zero. Neither field
asserts an energy, transformed-source, or summed-terminal estimate. -/
structure DualTerminalCalibration
    (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
    (sTail sZero : Finset (ℕ × ℕ)) (k : ℕ) (Z Lmax Nsave decay : ℝ) where
  productExponent : ℝ
  profileExponent : ℝ
  maskExponent : ℝ
  inverseRadiusExponent : ℝ
  tailAmplitude : ℝ
  zeroAmplitude : ℝ
  zeroAmplitude_nonneg : 0 ≤ zeroAmplitude
  windows : SecondTailWindows C G.columns G.columns G.ideal G.ideal
    (fun DE : FirstZeroLabel G.columns G.columns G.ideal G.ideal =>
      canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property)
    sTail (fun i j => (G.coefficient i * star (G.coefficient j)) • s.profile)
    s.radius s.mask k Z productExponent profileExponent maskExponent inverseRadiusExponent
    tailAmplitude
  exponent_bound : secondTailExponent k productExponent profileExponent maskExponent
    inverseRadiusExponent ≤ Lmax
  cutoff_eq : s.cutoff = Z ^ firstTailCutoffExponent Lmax Nsave decay
  zero_normalization : ∀ v ∈ firstZeroPairs G.columns G.columns G.ideal G.ideal,
    sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
      ((G.coefficient v.2.1 * star (G.coefficient v.2.2)) • s.profile) *
      A.exteriorNorm (G.ideal v.2.1) *
      (∑ D ∈ s.mask.powerset, firstZeroDivisorWeight s.radius D) ≤
        zeroAmplitude / Real.sqrt (Z ^ productExponent)

namespace DualTerminalCalibration

variable {s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Z Lmax Nsave decay : ℝ}

/-- Only the genuine nonzero kernel sum remains after both terminal
terms have been bounded. The individual normalization amplitudes stay
visible for the outer common-measure budget. -/
def cost (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (ε Cerror Czero : ℝ) : ℝ :=
  (s.fiber : ℝ) * (Czero * (T.windows.multiplicity * T.zeroAmplitude) * Z ^ (T.productExponent * ε) +
    (∑ DE, ∑ D : s.mask.powerset, (s.charts DE D).kernelCost s.mask s.cutoff s.cutoff_one) +
    Cerror * (T.windows.multiplicity * T.tailAmplitude) * Z ^ (-Nsave))

end DualTerminalCalibration
end ActualGaussStage

namespace ActualGaussStage

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest}
variable {Sdiv : Ideal (𝓞 K)} {slots : ℕ} {B : ℝ}

/-- Raw windows for the actual residual profiles.  The tail record
retains the original ideal-factor tuple and its proved finite fibres.
For the zero term only individual residual seminorms and individual
original ideal norms are supplied. -/
structure DualResidualTerminalWindows
    (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
    (W : FirstDivisorCoefficientAtoms (A := A) (σ := σ)
      G.columns G.coefficient Sdiv slots B)
    (sTail sZero : Finset (ℕ × ℕ))
    (k : ℕ) (Z Lmax Nsave decay : ℝ) where
  productExponent : ℝ
  profileExponent : ℝ
  maskExponent : ℝ
  inverseRadiusExponent : ℝ
  tailProfileConstant : ℝ
  zeroProfileConstant : ℝ
  zeroProfileConstant_nonneg : 0 ≤ zeroProfileConstant
  zeroProfileExponent : ℝ
  zeroColumnExponent : ℝ
  windows : SecondTailWindows C G.columns G.columns G.ideal G.ideal
    (fun DE : FirstZeroLabel G.columns G.columns G.ideal G.ideal =>
      canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property)
    sTail (fun i j => (W.residualCoefficient i * star (W.residualCoefficient j)) • s.profile)
    s.radius s.mask k Z productExponent profileExponent maskExponent inverseRadiusExponent
    tailProfileConstant
  exponent_bound : secondTailExponent k productExponent profileExponent maskExponent
    inverseRadiusExponent ≤ Lmax
  cutoff_eq : s.cutoff = Z ^ firstTailCutoffExponent Lmax Nsave decay
  residual_zero_profile : ∀ v ∈ firstZeroPairs G.columns G.columns G.ideal G.ideal,
    sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
      ((W.residualCoefficient v.2.1 * star (W.residualCoefficient v.2.2)) • s.profile) ≤
        zeroProfileConstant * Z ^ zeroProfileExponent
  column_norm : ∀ i ∈ G.columns, A.exteriorNorm (G.ideal i) ≤ Z ^ zeroColumnExponent

namespace DualResidualTerminalWindows

variable {W : FirstDivisorCoefficientAtoms (A := A) (σ := σ)
  G.columns G.coefficient Sdiv slots B}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Z Lmax Nsave decay : ℝ}
variable (T : s.DualResidualTerminalWindows W sTail sZero k Z Lmax Nsave decay)

def tailAmplitude : ℝ := W.scalarCost * T.tailProfileConstant

def zeroAmplitude : ℝ :=
  W.scalarCost * T.zeroProfileConstant * Z ^ T.zeroProfileExponent *
    Z ^ T.zeroColumnExponent * ((2 : ℝ) ^ s.mask.card * Z ^ T.inverseRadiusExponent) *
      Real.sqrt (Z ^ T.productExponent)

theorem zeroAmplitude_nonneg : 0 ≤ T.zeroAmplitude := by
  have hz : 0 ≤ Z := zero_le_one.trans T.windows.base_ge_one
  have hscalar := W.scalarCost_nonneg
  have hprofile := T.zeroProfileConstant_nonneg
  unfold zeroAmplitude
  positivity

/-- This constructs the original calibration with both amplitudes
computed from genuine frozen atoms and original residual windows. -/
def calibration : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay where
  productExponent := T.productExponent
  profileExponent := T.profileExponent
  maskExponent := T.maskExponent
  inverseRadiusExponent := T.inverseRadiusExponent
  tailAmplitude := T.tailAmplitude
  zeroAmplitude := T.zeroAmplitude
  zeroAmplitude_nonneg := T.zeroAmplitude_nonneg
  windows :=
    { T.windows with
      amplitude_nonneg := mul_nonneg W.scalarCost_nonneg T.windows.amplitude_nonneg
      profile_seminorm := by
        intro v hv
        have hmem := (mem_firstZeroPairs G.columns G.columns G.ideal G.ideal v).mp hv
        have hp := W.gram_seminorm_le (C := C) v.2.1 v.2.2 hmem.1 hmem.2.1
          (sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)) s.profile
        exact (hp.trans (mul_le_mul_of_nonneg_left
          (T.windows.profile_seminorm v hv) W.scalarCost_nonneg)).trans_eq (by
            dsimp only [tailAmplitude]
            ring) }
  exponent_bound := T.exponent_bound
  cutoff_eq := T.cutoff_eq
  zero_normalization := by
    intro v hv
    have hmem := (mem_firstZeroPairs G.columns G.columns G.ideal G.ideal v).mp hv
    have hz : 0 < Z := zero_lt_one.trans_le T.windows.base_ge_one
    have hsqrt : Real.sqrt (Z ^ T.productExponent) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (Real.rpow_pos_of_pos hz _))
    have hp := (W.gram_seminorm_le (C := C) v.2.1 v.2.2 hmem.1 hmem.2.1
      (sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)) s.profile).trans
        (mul_le_mul_of_nonneg_left (T.residual_zero_profile v hv) W.scalarCost_nonneg)
    have hm : (∑ D ∈ s.mask.powerset, firstZeroDivisorWeight s.radius D) ≤
        (2 : ℝ) ^ s.mask.card * Z ^ T.inverseRadiusExponent :=
      (sum_firstZeroDivisorWeight_le s.radius s.mask).trans
        (mul_le_mul_of_nonneg_left T.windows.inverse_radius (by positivity))
    have hnorm : 0 ≤ A.exteriorNorm (G.ideal v.2.1) :=
      (A.exteriorNorm_pos _).le
    have hmask : 0 ≤ ∑ D ∈ s.mask.powerset, firstZeroDivisorWeight s.radius D :=
      Finset.sum_nonneg fun D _ => firstZeroDivisorWeight_nonneg s.radius D
    have hprofile : 0 ≤ W.scalarCost *
        (T.zeroProfileConstant * Z ^ T.zeroProfileExponent) :=
      mul_nonneg W.scalarCost_nonneg
        (mul_nonneg T.zeroProfileConstant_nonneg (Real.rpow_nonneg hz.le _))
    have hbound := mul_le_mul
      (mul_le_mul hp (T.column_norm v.2.1 hmem.1) hnorm hprofile)
      hm hmask (mul_nonneg hprofile (Real.rpow_nonneg hz.le _))
    apply hbound.trans_eq
    dsimp only [zeroAmplitude]
    rw [mul_div_cancel_right₀ _ hsqrt]
    ring

theorem calibration_tailAmplitude : T.calibration.tailAmplitude =
    (B ^ slots / (Ideal.absNorm Sdiv : ℝ)) * T.tailProfileConstant := rfl

theorem calibration_zeroAmplitude : T.calibration.zeroAmplitude =
    (B ^ slots / (Ideal.absNorm Sdiv : ℝ)) * T.zeroProfileConstant *
      Z ^ T.zeroProfileExponent * Z ^ T.zeroColumnExponent *
        ((2 : ℝ) ^ s.mask.card * Z ^ T.inverseRadiusExponent) *
          Real.sqrt (Z ^ T.productExponent) := rfl

/-- The numerical ledger receives the genuine first-divisor factor,
the actual mask cardinality, and only the primitive profile exponents. -/
theorem calibration_zeroAmplitude_power : T.calibration.zeroAmplitude =
    (B ^ slots * T.zeroProfileConstant * (2 : ℝ) ^ s.mask.card /
      (Ideal.absNorm Sdiv : ℝ)) *
      Z ^ (T.zeroProfileExponent + T.zeroColumnExponent + T.inverseRadiusExponent +
        T.productExponent / 2) := by
  have hz : 0 < Z := zero_lt_one.trans_le T.windows.base_ge_one
  have hsqrt : Real.sqrt (Z ^ T.productExponent) = Z ^ (T.productExponent / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hz.le]
    congr 1
    ring
  rw [T.calibration_zeroAmplitude, hsqrt]
  simp only [Real.rpow_add hz]
  ring

end DualResidualTerminalWindows
end ActualGaussStage

namespace ActualGaussStage.DualResidualTerminalWindows

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
variable {raw : ι → ℂ} {Sdiv : Ideal (𝓞 K)} {slots : ℕ} {B : ℝ}

/-- Construct the existing terminal windows from the original raw
atom record and its individual profiles.  The zero exponent is fixed
to `-2*a₀`; it is a conclusion of the two actual column norm divisions.
The tail uses the same factor tuple, the same fibre multiplicity, and
the same physical cutoff. -/
def ofOriginalInverseNorm
    (W : FirstDivisorCoefficientAtoms (A := A) (σ := σ)
      G.columns raw Sdiv slots B)
    (hcoefficient : ∀ i ∈ G.columns,
      G.coefficient i = raw i / (A.exteriorNorm (G.ideal i) : ℂ))
    (sTail sZero : Finset (ℕ × ℕ))
    (k : ℕ) (Z Lmax Nsave decay a₀ productExponent rawProfileExponent
      maskExponent inverseRadiusExponent tailConstant zeroConstant columnError : ℝ)
    (hzeroConstant : 0 ≤ zeroConstant)
    (rawWindows : SecondTailWindows C G.columns G.columns G.ideal G.ideal
      (fun DE : FirstZeroLabel G.columns G.columns G.ideal G.ideal =>
        canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property)
      sTail (fun i j => (W.residualCoefficient i * star (W.residualCoefficient j)) • s.profile)
      s.radius s.mask k Z productExponent rawProfileExponent maskExponent inverseRadiusExponent
      tailConstant)
    (hdegree : secondTailExponent k productExponent (rawProfileExponent - 2 * a₀)
      maskExponent inverseRadiusExponent ≤ Lmax)
    (hcutoff : s.cutoff = Z ^ firstTailCutoffExponent Lmax Nsave decay)
    (hlower : ∀ i ∈ G.columns, Z ^ a₀ ≤ A.exteriorNorm (G.ideal i))
    (hupper : ∀ i ∈ G.columns, A.exteriorNorm (G.ideal i) ≤ Z ^ (a₀ + columnError))
    (hrawZero : ∀ v ∈ firstZeroPairs G.columns G.columns G.ideal G.ideal,
      sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
        ((W.residualCoefficient v.2.1 * star (W.residualCoefficient v.2.2)) • s.profile) ≤
          zeroConstant) :
    s.DualResidualTerminalWindows (W.withInverseNorm G.ideal G.coefficient hcoefficient)
      sTail sZero k Z Lmax Nsave decay where
  productExponent := productExponent
  profileExponent := rawProfileExponent - 2 * a₀
  maskExponent := maskExponent
  inverseRadiusExponent := inverseRadiusExponent
  tailProfileConstant := tailConstant
  zeroProfileConstant := zeroConstant
  zeroProfileConstant_nonneg := hzeroConstant
  zeroProfileExponent := -2 * a₀
  zeroColumnExponent := a₀ + columnError
  windows :=
    { rawWindows with
      profile_seminorm := by
        intro v hv
        have hm := (mem_firstZeroPairs G.columns G.columns G.ideal G.ideal v).mp hv
        exact W.withInverseNorm_gram_le G.ideal G.coefficient hcoefficient
          (sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)) s.profile v.2.1 v.2.2
          Z a₀ rawProfileExponent tailConstant (zero_lt_one.trans_le rawWindows.base_ge_one)
          rawWindows.amplitude_nonneg (hlower _ hm.1) (hlower _ hm.2.1)
          (rawWindows.profile_seminorm v hv) }
  exponent_bound := hdegree
  cutoff_eq := hcutoff
  residual_zero_profile := by
    intro v hv
    have hm := (mem_firstZeroPairs G.columns G.columns G.ideal G.ideal v).mp hv
    have h := W.withInverseNorm_gram_le G.ideal G.coefficient hcoefficient
      (sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)) s.profile v.2.1 v.2.2
      Z a₀ 0 zeroConstant (zero_lt_one.trans_le rawWindows.base_ge_one)
      hzeroConstant (hlower _ hm.1) (hlower _ hm.2.1)
      (by simpa only [Real.rpow_zero, mul_one] using hrawZero v hv)
    simpa only [zero_sub, neg_mul] using h
  column_norm := hupper

/-- The actual displayed exponent after the two inverse column norms,
the zero Gauss norm and the powerful-tuple square root have been paid.
The two column-scale terms cancel against the product window. -/
theorem inverseNorm_zero_exponent
    (a₀ columnError inverseRadiusExponent productExponent productError : ℝ)
    (hproduct : productExponent / 2 ≤ a₀ + productError) :
    -2 * a₀ + (a₀ + columnError) + inverseRadiusExponent + productExponent / 2 ≤
      inverseRadiusExponent + columnError + productError := by
  linarith

/-- The ledger required by the original pooled zero-budget theorem is
derived from the actual inverse-norm profile, norm/radius windows and
the prescribed enlargement.  Its terminal exponent is the fixed target.
Only the explicitly displayed boundary and small-power payments enter
the final numerical budget. -/
theorem zero_ledger_of_inverseNorm
    {W : FirstDivisorCoefficientAtoms (A := A) (σ := σ)
      G.columns G.coefficient Sdiv slots B}
    {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Z Lmax Nsave decay : ℝ}
    (T : s.DualResidualTerminalWindows W sTail sZero k Z Lmax Nsave decay)
    (Aexp M c d qtilde K₀ Krow w wold g step padding
      boundary columnError productError radiusError a₀ allowanceExtra
      εzero εpool ε : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hw : 0 ≤ w) (hwo : wold ≤ w)
    (hboundary : 0 ≤ boundary) (hallowance : 0 ≤ allowanceExtra)
    (hK₀ : K₀ = 2 * Aexp - c - d + qtilde - M)
    (hKrow : Krow - K₀ ≤ boundary)
    (hg : g ≤ max (d - c + (K₀ - Krow) - 2 * w + wold) 0 + 2 * step)
    (hprofile : T.zeroProfileExponent = -2 * a₀)
    (hcolumn : T.zeroColumnExponent ≤ a₀ + columnError)
    (hproduct : T.productExponent / 2 ≤ a₀ + productError)
    (hradius : T.inverseRadiusExponent ≤ Krow + g + radiusError)
    (hpayment : boundary + columnError + productError + radiusError +
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

namespace ActualGaussStage.DualTerminalCalibration

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Z Lmax Nsave decay : ℝ}

/-- The terminal calibration for every first Fourier phase is built
from the one original calibration. Its amplitudes are unchanged. -/
def withUnitMultiplier
    (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (u : ι → ℂ) (hu : ∀ i, ‖u i‖ = 1) :
    (s.withMultiplier u).DualTerminalCalibration sTail sZero k Z Lmax Nsave decay where
  productExponent := T.productExponent
  profileExponent := T.profileExponent
  maskExponent := T.maskExponent
  inverseRadiusExponent := T.inverseRadiusExponent
  tailAmplitude := T.tailAmplitude
  zeroAmplitude := T.zeroAmplitude
  zeroAmplitude_nonneg := T.zeroAmplitude_nonneg
  windows :=
    { T.windows with
      profile_seminorm := by
        intro v hv
        change sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
          (((u v.2.1 * G.coefficient v.2.1) * star (u v.2.2 * G.coefficient v.2.2)) •
            s.profile) ≤ _
        rw [original_gram_seminorm_unit_multipliers sTail _ _ _ _
          (hu v.2.1) (hu v.2.2)]
        exact T.windows.profile_seminorm v hv }
  exponent_bound := T.exponent_bound
  cutoff_eq := T.cutoff_eq
  zero_normalization := by
    intro v hv
    change sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
      (((u v.2.1 * G.coefficient v.2.1) * star (u v.2.2 * G.coefficient v.2.2)) •
        s.profile) * A.exteriorNorm (G.ideal v.2.1) *
      (∑ D ∈ s.mask.powerset, firstZeroDivisorWeight s.radius D) ≤ _
    rw [original_gram_seminorm_unit_multipliers sZero _ _ _ _
      (hu v.2.1) (hu v.2.2)]
    exact T.zero_normalization v hv

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

def fourierPhase
    (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (x : ι → W) (ξ : W) :
    (s.withMultiplier (fun i => jointPhase ξ (x i))).DualTerminalCalibration
      sTail sZero k Z Lmax Nsave decay :=
  T.withUnitMultiplier (fun i => jointPhase ξ (x i)) (fun i => norm_jointPhase ξ (x i))

end ActualGaussStage.DualTerminalCalibration

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.DualResidualTerminalWindows.calibration
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.DualResidualTerminalWindows.ofOriginalInverseNorm
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.DualTerminalCalibration.fourierPhase
