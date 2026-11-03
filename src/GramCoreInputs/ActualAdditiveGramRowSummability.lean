import ActualAdditiveGramResidueExpansion
import ActualProbePairPointwisePoisson
import HeckeGeneral.Bridge.SIntegerPeriodicAdelicTest
import HeckeGeneral.Bridge.SIntegerScaledSchwartzModel
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
UNCOMPILED / native 0. Actual negative Gauss pairs times the original
physical additive test are absolutely summable at every local base. The
existing periodic scaled Schwartz theorem supplies summability on the
whole S-integer ring; restriction to nonzero rows is then identified with
the literal P.additive test. The finite ideal-pair expansion may therefore
be interchanged with the infinite row sum without a summability input.

S is a finite set of primes, as in the existing adelic/scaled Poisson API.
The extension of P.additive.finiteTest to all primes changes no factor on
S. No orbital Poisson identity, fixed-ray shape of c, or Gram bound is
assumed or asserted. The exact central factor Y^(-3) remains explicit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualAdditiveGramDraft

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Bridge
open HeckeGeneral.ThetaSkeleton.Global
open ActualProbeGaussFourierDraft ActualProbePairFourierDraft ActualProbePairPoissonDraft
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

local notation "SF" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer SF K
local notation "NZ" => NonzeroRingElements OS
local notation "G" => sLocalMultiplicativeGroup K SF
local notation "T" => sLocalNormOneGroup K SF

/-- Actual periodic summability, including the zero S-integer. The modulus
is the product of the same two P generators used in the original Am. -/
theorem summable_probeNegativeGaussPair_scaledTensor (P : ProbeData K SF)
    (I J : ExteriorIdeal K SF) (p : G) :
    Summable (fun m : OS =>
      probeNegativeGaussPairResidue K SF P I J (Ideal.Quotient.mk _ m) *
        sIntegerScaledTensorTerm K S
          (traceSchwartzToMixed K P.additive.infiniteTest)
          (probeFiniteFamily K S P) p m.val) := by
  have hs := summable_sIntegerPeriodicScaledTensor K S
    ((probeGenerator K SF P.arithmetic I).val * (probeGenerator K SF P.arithmetic J).val)
    (mul_ne_zero (probeGenerator K SF P.arithmetic I).property
      (probeGenerator K SF P.arithmetic J).property)
    (traceSchwartzToMixed K P.additive.infiniteTest) (probeFiniteFamily K S P)
    (probeFiniteFamily_locallyConstant K S P)
    (probeFiniteFamily_compactSupport K S P)
    (probeNegativeGaussPairResidue K SF P I J) 1 p
  simpa only [one_mul] using hs

/-- Every nonzero row is the literal original P.additive test. No compact
fundamental-domain restriction on the arbitrary base p is required. -/
theorem summable_probeNegativeGaussPair_mul_additiveTest (P : ProbeData K SF)
    (I J : ExteriorIdeal K SF) (p : G) :
    Summable (fun m : NZ =>
      probeNegativeGaussPairResidue K SF P I J (Ideal.Quotient.mk _ m.val) *
        additiveTest K SF P.additive (p * sLocalNonzeroIntegerDiagonal K SF m)) := by
  have hs := (summable_probeNegativeGaussPair_scaledTensor K S P I J p).subtype
    (fun m : OS => m ≠ 0)
  simpa only [Function.comp_def, sIntegerScaledTensorTerm_eq_sLocalTensor,
    probeFiniteTestFunction_eq, additiveTest] using hs

theorem summable_norm_probeNegativeGaussPair_mul_additiveTest (P : ProbeData K SF)
    (I J : ExteriorIdeal K SF) (p : G) :
    Summable (fun m : NZ =>
      ‖probeNegativeGaussPairResidue K SF P I J (Ideal.Quotient.mk _ m.val) *
        additiveTest K SF P.additive (p * sLocalNonzeroIntegerDiagonal K SF m)‖) :=
  (summable_probeNegativeGaussPair_mul_additiveTest K S P I J p).norm

/-- The same result in the original SchwartzTerm notation used by Poisson. -/
theorem summable_probeNegativeGaussPair_schwartzTerm (P : ProbeData K SF)
    (I J : ExteriorIdeal K SF) (r : {r : ℝ // 0 < r}) (x : T) :
    Summable (fun m : NZ =>
      probeNegativeGaussPairResidue K SF P I J (Ideal.Quotient.mk _ m.val) *
        sIntegerSchwartzTerm K SF P.additive.infiniteTest
          (fun z => ∏ v : SF, P.additive.finiteTest v (z v)) r m x) := by
  simpa only [sIntegerSchwartzTerm, additiveTest] using
    summable_probeNegativeGaussPair_mul_additiveTest K S P I J
      (sLocalNormSection K SF r * (x : G))

/-- The actual Am square times the original additive test is summable.
The finite ideal envelope and genuine pair-row summability prove this. -/
theorem summable_actualAdditiveGramAmplitude_norm_sq_mul_additiveTest
    (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ) (W : SmoothAnnularTest)
    (Y ν : ℝ) (hY : 0 < Y) (p : G) :
    Summable (fun m : NZ =>
      ((‖actualAdditiveGramAmplitude K SF P c W Y ν m.val‖ ^ 2 : ℝ) : ℂ) *
        additiveTest K SF P.additive (p * sLocalNonzeroIntegerDiagonal K SF m)) := by
  have hrow (I J : ExteriorIdeal K SF) :=
    (summable_probeNegativeGaussPair_mul_additiveTest K S P I J p).mul_left
      (actualAdditiveGramPairCoefficient K SF c W Y ν I J)
  have hs := summable_sum (s := additiveGramIdealSupport K SF W Y)
    (fun I _hI => summable_sum (s := additiveGramIdealSupport K SF W Y)
      (fun J _hJ => hrow I J))
  apply (hs.mul_left ((Y ^ (-3 : ℝ) : ℝ) : ℂ)).congr
  intro m
  symm
  rw [actualAdditiveGramAmplitude_norm_sq_eq_residue_double_sum K SF P c W Y ν hY m.val]
  simp only [Finset.sum_mul, mul_assoc]

theorem summable_norm_actualAdditiveGramAmplitude_norm_sq_mul_additiveTest
    (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ) (W : SmoothAnnularTest)
    (Y ν : ℝ) (hY : 0 < Y) (p : G) :
    Summable (fun m : NZ =>
      ‖((‖actualAdditiveGramAmplitude K SF P c W Y ν m.val‖ ^ 2 : ℝ) : ℂ) *
        additiveTest K SF P.additive (p * sLocalNonzeroIntegerDiagonal K SF m)‖) :=
  (summable_actualAdditiveGramAmplitude_norm_sq_mul_additiveTest K S P c W Y ν hY p).norm

/-- Exchange the actual infinite row sum with the finite ideal-pair sum.
Each inner periodic Schwartz series is proved summable above. This is the
literal identity prior to applying any Poisson theorem. -/
theorem tsum_actualAdditiveGramAmplitude_norm_sq_mul_additiveTest
    (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ) (W : SmoothAnnularTest)
    (Y ν : ℝ) (hY : 0 < Y) (p : G) :
    (∑' m : NZ,
      ((‖actualAdditiveGramAmplitude K SF P c W Y ν m.val‖ ^ 2 : ℝ) : ℂ) *
        additiveTest K SF P.additive (p * sLocalNonzeroIntegerDiagonal K SF m)) =
      ((Y ^ (-3 : ℝ) : ℝ) : ℂ) *
        ∑ I ∈ additiveGramIdealSupport K SF W Y,
          ∑ J ∈ additiveGramIdealSupport K SF W Y,
            actualAdditiveGramPairCoefficient K SF c W Y ν I J *
              ∑' m : NZ,
                probeNegativeGaussPairResidue K SF P I J (Ideal.Quotient.mk _ m.val) *
                  additiveTest K SF P.additive
                    (p * sLocalNonzeroIntegerDiagonal K SF m) := by
  have hrow (I J : ExteriorIdeal K SF) :=
    (summable_probeNegativeGaussPair_mul_additiveTest K S P I J p).mul_left
      (actualAdditiveGramPairCoefficient K SF c W Y ν I J)
  calc
    _ = ((Y ^ (-3 : ℝ) : ℝ) : ℂ) * ∑' m : NZ,
        ∑ I ∈ additiveGramIdealSupport K SF W Y,
          ∑ J ∈ additiveGramIdealSupport K SF W Y,
            actualAdditiveGramPairCoefficient K SF c W Y ν I J *
              (probeNegativeGaussPairResidue K SF P I J (Ideal.Quotient.mk _ m.val) *
                additiveTest K SF P.additive
                  (p * sLocalNonzeroIntegerDiagonal K SF m)) := by
      rewrite [← tsum_mul_left]
      apply tsum_congr
      intro m
      rw [actualAdditiveGramAmplitude_norm_sq_eq_residue_double_sum K SF P c W Y ν hY m.val]
      simp only [Finset.sum_mul, mul_assoc]
    _ = ((Y ^ (-3 : ℝ) : ℝ) : ℂ) *
        ∑ I ∈ additiveGramIdealSupport K SF W Y,
          ∑ J ∈ additiveGramIdealSupport K SF W Y,
            ∑' m : NZ, actualAdditiveGramPairCoefficient K SF c W Y ν I J *
              (probeNegativeGaussPairResidue K SF P I J (Ideal.Quotient.mk _ m.val) *
                additiveTest K SF P.additive
                  (p * sLocalNonzeroIntegerDiagonal K SF m)) := by
      congr 1
      rw [Summable.tsum_finsetSum (s := additiveGramIdealSupport K SF W Y)
        (fun I _hI => summable_sum (s := additiveGramIdealSupport K SF W Y)
          (fun J _hJ => hrow I J))]
      apply Finset.sum_congr rfl
      intro I _hI
      exact Summable.tsum_finsetSum (s := additiveGramIdealSupport K SF W Y)
        (fun J _hJ => hrow I J)
    _ = _ := by simp only [tsum_mul_left]

end HeckeGeneral.ThetaSkeleton.Physical.ActualAdditiveGramDraft
