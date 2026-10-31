import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstPoissonColumnNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDivisorTerminalCalibration

/-!
# Original divisor atoms with the genuine first Poisson norm factors

The raw atom record is unchanged.  Dividing the actual column by its
ideal norm divides only its residual coefficient; it does not improve
the assumed bound on the raw numerator.  The resulting negative column
exponent in the individual Gram profile is proved from the original
norm window.  This supplies the existing terminal calibration with a
computed zero-profile exponent, rather than an arbitrary zero exponent.

The source identity used by this construction is provided by
`FirstBlockProfileChart.ofUnscaledProfile` and is preserved through the
actual pool by `residualCoefficient_inverseNorm`.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}

namespace FirstDivisorCoefficientAtoms

variable {ι : Type*} {columns : Finset ι} {raw : ι → ℂ}
variable {Sdiv : Ideal (𝓞 K)} {slots : ℕ} {B : ℝ}
variable (W : FirstDivisorCoefficientAtoms (A := A) (σ := σ) columns raw Sdiv slots B)

/-- Preserve the actual frozen atoms, including their original profile
bounds.  Only the displayed source norm is put into the residual part. -/
def withInverseNorm (ideal : ι → A.Exterior) (coefficient : ι → ℂ)
    (hcoefficient : ∀ i ∈ columns,
      coefficient i = raw i / (A.exteriorNorm (ideal i) : ℂ)) :
    FirstDivisorCoefficientAtoms (A := A) (σ := σ) columns coefficient Sdiv slots B where
  divisor_ne_zero := W.divisor_ne_zero
  bound_ge_one := W.bound_ge_one
  active := W.active
  atoms := W.atoms
  rawResidualCoefficient i := W.rawResidualCoefficient i / (A.exteriorNorm (ideal i) : ℂ)
  coefficient_eq i hi := by
    rw [hcoefficient i hi, W.coefficient_eq i hi]
    by_cases ha : W.active i
    · simp only [if_pos ha]
      ring
    · simp only [if_neg ha, zero_div]
  divisor_dvd := W.divisor_dvd
  atom_bound := W.atom_bound

theorem withInverseNorm_residualCoefficient
    (ideal : ι → A.Exterior) (coefficient : ι → ℂ)
    (hcoefficient : ∀ i ∈ columns,
      coefficient i = raw i / (A.exteriorNorm (ideal i) : ℂ)) (i : ι) :
    (W.withInverseNorm ideal coefficient hcoefficient).residualCoefficient i =
      W.residualCoefficient i / (A.exteriorNorm (ideal i) : ℂ) := by
  by_cases ha : W.active i <;>
    simp only [withInverseNorm, residualCoefficient, ha, if_true, if_false, zero_div]

/-- Exact seminorm homogeneity with both actual norm denominators.
No raw coefficient is replaced by a better bounded coefficient. -/
theorem withInverseNorm_gram_seminorm
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (ideal : ι → A.Exterior) (coefficient : ι → ℂ)
    (hcoefficient : ∀ i ∈ columns,
      coefficient i = raw i / (A.exteriorNorm (ideal i) : ℂ))
    (p : Seminorm ℂ V) (φ : V) (i j : ι) :
    p (((W.withInverseNorm ideal coefficient hcoefficient).residualCoefficient i *
      star ((W.withInverseNorm ideal coefficient hcoefficient).residualCoefficient j)) • φ) =
      p ((W.residualCoefficient i * star (W.residualCoefficient j)) • φ) /
        (A.exteriorNorm (ideal i) * A.exteriorNorm (ideal j)) := by
  rw [W.withInverseNorm_residualCoefficient ideal coefficient hcoefficient i,
    W.withInverseNorm_residualCoefficient ideal coefficient hcoefficient j]
  simp only [map_smul_eq_mul, norm_mul, norm_star, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (A.exteriorNorm_pos _)]
  ring

/-- Lower norm windows pay the two inverse norms separately.  The raw
profile window on the right is exactly the original one. -/
theorem withInverseNorm_gram_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (ideal : ι → A.Exterior) (coefficient : ι → ℂ)
    (hcoefficient : ∀ i ∈ columns,
      coefficient i = raw i / (A.exteriorNorm (ideal i) : ℂ))
    (p : Seminorm ℂ V) (φ : V) (i j : ι)
    (Z a₀ profileExponent amplitude : ℝ) (hZ : 0 < Z) (hAmp : 0 ≤ amplitude)
    (hi : Z ^ a₀ ≤ A.exteriorNorm (ideal i))
    (hj : Z ^ a₀ ≤ A.exteriorNorm (ideal j))
    (hraw : p ((W.residualCoefficient i * star (W.residualCoefficient j)) • φ) ≤
      amplitude * Z ^ profileExponent) :
    p (((W.withInverseNorm ideal coefficient hcoefficient).residualCoefficient i *
      star ((W.withInverseNorm ideal coefficient hcoefficient).residualCoefficient j)) • φ) ≤
      amplitude * Z ^ (profileExponent - 2 * a₀) := by
  have hden : Z ^ (2 * a₀) ≤
      A.exteriorNorm (ideal i) * A.exteriorNorm (ideal j) := by
    rw [show 2 * a₀ = a₀ + a₀ by ring, Real.rpow_add hZ]
    exact mul_le_mul hi hj (Real.rpow_nonneg hZ.le _) (A.exteriorNorm_pos _).le
  rw [W.withInverseNorm_gram_seminorm ideal coefficient hcoefficient p φ i j]
  calc
    _ ≤ (amplitude * Z ^ profileExponent) /
        (A.exteriorNorm (ideal i) * A.exteriorNorm (ideal j)) :=
      div_le_div_of_nonneg_right hraw (mul_nonneg
        (A.exteriorNorm_pos _).le (A.exteriorNorm_pos _).le)
    _ ≤ (amplitude * Z ^ profileExponent) / Z ^ (2 * a₀) :=
      div_le_div_of_nonneg_left (mul_nonneg hAmp (Real.rpow_nonneg hZ.le _))
        (Real.rpow_pos_of_pos hZ _) hden
    _ = _ := by rw [Real.rpow_sub hZ]; ring

end FirstDivisorCoefficientAtoms

/-- The actual first nominal row length and the prescribed enlargement
leave at most two steps above the first side allowance.  This includes
the one-step direct/error choice by its weaker displayed upper bound.
The removed length is kept in the enlargement parameter. -/
theorem second_zero_enlargement_allowance
    (Aexp M c d qtilde K₀ Krow w wold g step boundary allowanceExtra : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hw : 0 ≤ w) (hwo : wold ≤ w)
    (hboundary : 0 ≤ boundary) (hallowance : 0 ≤ allowanceExtra)
    (hK₀ : K₀ = 2 * Aexp - c - d + qtilde - M)
    (hKrow : Krow - K₀ ≤ boundary)
    (hg : g ≤ max (d - c + (K₀ - Krow) - 2 * w + wold) 0 + 2 * step) :
    Krow + g - (Aexp - c + qtilde + allowanceExtra) ≤
      max (Aexp - M) 0 + 2 * step + boundary := by
  have hmax : max (d - c + (K₀ - Krow) - 2 * w + wold) 0 ≤
      d - (Krow - K₀) + boundary :=
    max_le (by linarith) (by linarith)
  have hA : Aexp - M ≤ max (Aexp - M) 0 := le_max_left _ _
  linarith

section Terminal

variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K

namespace ActualGaussStage.ResidualTerminalWindows

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
    (hzero : s.profile 0 = 0)
    (hlower : ∀ i ∈ G.columns, Z ^ a₀ ≤ A.exteriorNorm (G.ideal i))
    (hupper : ∀ i ∈ G.columns, A.exteriorNorm (G.ideal i) ≤ Z ^ (a₀ + columnError))
    (hrawZero : ∀ v ∈ firstZeroPairs G.columns G.columns G.ideal G.ideal,
      sZero.sup (schwartzSeminormFamily ℂ V ℂ)
        ((W.residualCoefficient v.2.1 * star (W.residualCoefficient v.2.2)) • s.profile) ≤
          zeroConstant) :
    s.ResidualTerminalWindows (W.withInverseNorm G.ideal G.coefficient hcoefficient)
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
          (sTail.sup (schwartzSeminormFamily ℂ V ℂ)) s.profile v.2.1 v.2.2
          Z a₀ rawProfileExponent tailConstant (zero_lt_one.trans_le rawWindows.base_ge_one)
          rawWindows.amplitude_nonneg (hlower _ hm.1) (hlower _ hm.2.1)
          (rawWindows.profile_seminorm v hv) }
  exponent_bound := hdegree
  cutoff_eq := hcutoff
  profile_zero := hzero
  residual_zero_profile := by
    intro v hv
    have hm := (mem_firstZeroPairs G.columns G.columns G.ideal G.ideal v).mp hv
    have h := W.withInverseNorm_gram_le G.ideal G.coefficient hcoefficient
      (sZero.sup (schwartzSeminormFamily ℂ V ℂ)) s.profile v.2.1 v.2.2
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
    (T : s.ResidualTerminalWindows W sTail sZero k Z Lmax Nsave decay)
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

end ActualGaussStage.ResidualTerminalWindows
end Terminal

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstDivisorCoefficientAtoms.withInverseNorm_gram_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.ResidualTerminalWindows.ofOriginalInverseNorm
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.ResidualTerminalWindows.zero_ledger_of_inverseNorm
