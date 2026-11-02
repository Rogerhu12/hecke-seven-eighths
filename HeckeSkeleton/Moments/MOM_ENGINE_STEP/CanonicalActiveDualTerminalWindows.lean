import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalDualProfileWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalActiveGaussLower

set_option linter.unusedSectionVars false

/-!
# Same-source dual terminal calibration on the actual Gram support

The full Cartesian factor tuple and its multiplicity are retained for
the tail. The pure dual zero has its own supported product window.
Both inverse column norms are literal. In the zero normalization the
first of these cancels the displayed column norm before any estimate.

Sharp lower windows and residual numerator estimates are needed only
when the actual complete source coefficients are nonzero. In particular
no nonvanishing is inferred from an extracted residual coefficient.
The first divisor is paid once by the original frozen atom record.
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

namespace FirstDivisorCoefficientAtoms

variable {ι : Type*} {columns : Finset ι} {raw : ι → ℂ}
variable {Sdiv : Ideal (𝓞 K)} {slots : ℕ} {B : ℝ}
variable (W : FirstDivisorCoefficientAtoms (A := A) (σ := σ) columns raw Sdiv slots B)
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Nonzero actual coefficients imply that the original atom gate is
open. The two exact norm denominators remain in the conclusion. -/
theorem activeInverseNorm_gram_div_le
    (C : A.GeneralArithmeticContext σ η hS)
    (ideal : ι → A.Exterior) (coefficient : ι → ℂ)
    (hcoefficient : ∀ i ∈ columns,
      coefficient i = raw i / (A.exteriorNorm (ideal i) : ℂ))
    (p : Seminorm ℂ V) (φ : V) (i j : ι)
    (hi : i ∈ columns) (hj : j ∈ columns)
    (hci : coefficient i ≠ 0) (hcj : coefficient j ≠ 0)
    (pairBound : ℝ)
    (hpair : ‖W.rawResidualCoefficient i‖ * ‖W.rawResidualCoefficient j‖ ≤ pairBound) :
    p ((coefficient i * star (coefficient j)) • φ) ≤
      W.scalarCost * (pairBound * p φ) /
        (A.exteriorNorm (ideal i) * A.exteriorNorm (ideal j)) := by
  sorry

/-- Zero actual coefficients are handled before using the sharp lower
window. The original frozen atom cost occurs once. -/
theorem activeInverseNorm_gram_le
    (C : A.GeneralArithmeticContext σ η hS)
    (ideal : ι → A.Exterior) (coefficient : ι → ℂ)
    (hcoefficient : ∀ i ∈ columns,
      coefficient i = raw i / (A.exteriorNorm (ideal i) : ℂ))
    (p : Seminorm ℂ V) (φ : V) (i j : ι)
    (hi : i ∈ columns) (hj : j ∈ columns)
    (Z a₀ pairExponent pairBound : ℝ) (hZ : 0 < Z) (hpairBound : 0 ≤ pairBound)
    (hlower : ∀ i ∈ columns, coefficient i ≠ 0 → Z ^ a₀ ≤ A.exteriorNorm (ideal i))
    (hpair : coefficient i ≠ 0 → coefficient j ≠ 0 →
      ‖W.rawResidualCoefficient i‖ * ‖W.rawResidualCoefficient j‖ ≤
        pairBound * Z ^ pairExponent) :
    p ((coefficient i * star (coefficient j)) • φ) ≤
      (W.scalarCost * pairBound * p φ) * Z ^ (pairExponent - 2 * a₀) := by
  sorry

/-- In the pure dual-zero term the first exact inverse norm cancels
the displayed original column norm. No upper bound for that norm is
used or required. -/
theorem activeInverseNorm_gram_mul_norm_le
    (C : A.GeneralArithmeticContext σ η hS)
    (ideal : ι → A.Exterior) (coefficient : ι → ℂ)
    (hcoefficient : ∀ i ∈ columns,
      coefficient i = raw i / (A.exteriorNorm (ideal i) : ℂ))
    (p : Seminorm ℂ V) (φ : V) (i j : ι)
    (hi : i ∈ columns) (hj : j ∈ columns)
    (Z a₀ pairExponent pairBound : ℝ) (hZ : 0 < Z) (hpairBound : 0 ≤ pairBound)
    (hlower : ∀ i ∈ columns, coefficient i ≠ 0 → Z ^ a₀ ≤ A.exteriorNorm (ideal i))
    (hpair : coefficient i ≠ 0 → coefficient j ≠ 0 →
      ‖W.rawResidualCoefficient i‖ * ‖W.rawResidualCoefficient j‖ ≤
        pairBound * Z ^ pairExponent) :
    p ((coefficient i * star (coefficient j)) • φ) * A.exteriorNorm (ideal i) ≤
      (W.scalarCost * pairBound * p φ) * Z ^ (pairExponent - a₀) := by
  sorry

end FirstDivisorCoefficientAtoms

section Terminal

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
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace ActualGaussStage

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)

/-- A direct constructor into the existing calibration, retaining its
actual source and tuple fibres. The numerator hypothesis is a pair of
individual original residual coefficients, never a terminal estimate.
The coarse tail product and supported zero product are independent. -/
def dualCalibrationOfActiveInverseNorm
    {raw : ι → ℂ} {Sdiv : Ideal (𝓞 K)} {slots : ℕ} {B : ℝ}
    (W : FirstDivisorCoefficientAtoms (A := A) (σ := σ) G.columns raw Sdiv slots B)
    (hcoefficient : ∀ i ∈ G.columns,
      G.coefficient i = raw i / (A.exteriorNorm (G.ideal i) : ℂ))
    (sTail sZero : Finset (ℕ × ℕ)) (k : ℕ)
    (Z Lmax Nsave decay a₀ tailProduct zeroProduct pairExponent pairBound
      maskExponent inverseRadiusExponent : ℝ)
    (hbase : 1 ≤ Z) (htailProduct : 0 ≤ tailProduct) (hzeroProduct : 0 ≤ zeroProduct)
    (hpairBound : 0 ≤ pairBound)
    (factors : ι × ι → Fin k → Ideal (𝓞 K)) (multiplicity : ℕ)
    (hfibers : ∀ v,
      ((G.columns ×ˢ G.columns).filter (fun ij => factors ij = v)).card ≤ multiplicity)
    (hfactor : ∀ ij ∈ G.columns ×ˢ G.columns,
      PowerfulDiagonal.tupleIdeal (factors ij) = (G.ideal ij.1).val * (G.ideal ij.2).val)
    (htailNorm : ∀ ij ∈ G.columns ×ˢ G.columns,
      (Ideal.absNorm ((G.ideal ij.1).val * (G.ideal ij.2).val) : ℝ) ≤ Z ^ tailProduct)
    (hzeroNorm : ∀ ij ∈ G.columns ×ˢ G.columns,
      (G.coefficient ij.1 * star (G.coefficient ij.2)) • s.profile ≠ 0 →
      (Ideal.absNorm ((G.ideal ij.1).val * (G.ideal ij.2).val) : ℝ) ≤ Z ^ zeroProduct)
    (hlower : ∀ i ∈ G.columns, G.coefficient i ≠ 0 →
      Z ^ a₀ ≤ A.exteriorNorm (G.ideal i))
    (hpair : ∀ i ∈ G.columns, ∀ j ∈ G.columns,
      G.coefficient i ≠ 0 → G.coefficient j ≠ 0 →
      ‖W.rawResidualCoefficient i‖ * ‖W.rawResidualCoefficient j‖ ≤
        pairBound * Z ^ pairExponent)
    (hmask : (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) s.mask)).val ≤
        Z ^ maskExponent)
    (hradius : s.radius.val⁻¹ ≤ Z ^ inverseRadiusExponent)
    (hdegree : secondTailExponent k tailProduct (pairExponent - 2 * a₀)
      maskExponent inverseRadiusExponent ≤ Lmax)
    (hcutoff : s.cutoff = Z ^ firstTailCutoffExponent Lmax Nsave decay) :
    s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay where
  productExponent := tailProduct
  profileExponent := pairExponent - 2 * a₀
  maskExponent := maskExponent
  inverseRadiusExponent := inverseRadiusExponent
  tailAmplitude := W.scalarCost * pairBound *
    sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) s.profile
  zeroAmplitude := (W.scalarCost * pairBound *
    sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) s.profile) *
      Z ^ (pairExponent - a₀) *
        ((2 : ℝ) ^ s.mask.card * Z ^ inverseRadiusExponent) * Real.sqrt (Z ^ zeroProduct)
  zeroAmplitude_nonneg := by
    have hs : 0 ≤ sZero.sup
        (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) s.profile :=
      apply_nonneg _ _
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (mul_nonneg W.scalarCost_nonneg hpairBound) hs)
      (Real.rpow_nonneg (zero_le_one.trans hbase) _))
      (mul_nonneg (pow_nonneg (by norm_num) _) (Real.rpow_nonneg (zero_le_one.trans hbase) _)))
      (Real.sqrt_nonneg _)
  windows := {
    base_ge_one := hbase
    productExponent_nonneg := htailProduct
    amplitude_nonneg := mul_nonneg (mul_nonneg W.scalarCost_nonneg hpairBound) (apply_nonneg _ _)
    factors := factors
    multiplicity := multiplicity
    factors_fiber_card := hfibers
    factor_product := hfactor
    product_norm := htailNorm
    profile_seminorm := by
      intro v hv
      have hm := (mem_firstZeroPairs G.columns G.columns G.ideal G.ideal v).mp hv
      exact W.activeInverseNorm_gram_le C G.ideal G.coefficient hcoefficient
        (sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ))
        s.profile v.2.1 v.2.2 hm.1 hm.2.1 Z a₀ pairExponent pairBound
        (zero_lt_one.trans_le hbase) hpairBound hlower (hpair _ hm.1 _ hm.2.1)
    mask_norm := hmask
    inverse_radius := hradius }
  exponent_bound := hdegree
  cutoff_eq := hcutoff
  zeroProductExponent := zeroProduct
  zeroProductExponent_nonneg := hzeroProduct
  zero_product_norm := hzeroNorm
  zeroDivisor := 1
  zeroDivisor_ne_zero := one_ne_zero
  zero_divisor_dvd := by intro ij hij hgram heq; exact one_dvd _
  zero_normalization := by
    intro v hv
    simp only [map_one, Nat.cast_one, mul_one]
    have hm := (mem_firstZeroPairs G.columns G.columns G.ideal G.ideal v).mp hv
    have hz : 0 < Z := zero_lt_one.trans_le hbase
    have hp := W.activeInverseNorm_gram_mul_norm_le C G.ideal G.coefficient hcoefficient
      (sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ))
      s.profile v.2.1 v.2.2 hm.1 hm.2.1 Z a₀ pairExponent pairBound hz hpairBound
      hlower (hpair _ hm.1 _ hm.2.1)
    have hmaskSum : (∑ D ∈ s.mask.powerset, firstZeroDivisorWeight s.radius D) ≤
        (2 : ℝ) ^ s.mask.card * Z ^ inverseRadiusExponent :=
      (sum_firstZeroDivisorWeight_le s.radius s.mask).trans
        (mul_le_mul_of_nonneg_left hradius (pow_nonneg (by norm_num) _))
    have hmaskNonneg : 0 ≤ ∑ D ∈ s.mask.powerset, firstZeroDivisorWeight s.radius D :=
      Finset.sum_nonneg fun D _ => firstZeroDivisorWeight_nonneg s.radius D
    have hnum : 0 ≤ (W.scalarCost * pairBound *
        sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) s.profile) *
          Z ^ (pairExponent - a₀) :=
      mul_nonneg (mul_nonneg (mul_nonneg W.scalarCost_nonneg hpairBound)
        (apply_nonneg _ _)) (Real.rpow_nonneg hz.le _)
    have hsqrt : Real.sqrt (Z ^ zeroProduct) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (Real.rpow_pos_of_pos hz _))
    exact (mul_le_mul hp hmaskSum hmaskNonneg hnum).trans_eq
      (by rw [mul_div_cancel_right₀ _ hsqrt])

end ActualGaussStage
end Terminal
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstDivisorCoefficientAtoms.activeInverseNorm_gram_div_le
#print axioms HeckeSkeleton.Moments.EngineStep.FirstDivisorCoefficientAtoms.activeInverseNorm_gram_le
#print axioms HeckeSkeleton.Moments.EngineStep.FirstDivisorCoefficientAtoms.activeInverseNorm_gram_mul_norm_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.dualCalibrationOfActiveInverseNorm
