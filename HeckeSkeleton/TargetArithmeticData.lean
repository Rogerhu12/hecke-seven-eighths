import HeckeSkeleton.BaseContext
import HeckeSkeleton.AllowedGeneratorNorm
import HeckeAxiom.LambdaInfinityType
import HeckeAxiom.SexticSymbolDictionary
import HeckeAxiom.GaussCalibration

/-!
The common target's allowed-generator and mixed-Gauss calibration data.

All twelve declarations below are moved verbatim from the arithmetic
prefix of `Theta`. They are derived from the same primitive target
choices and import no high-expansion construction. `Theta` reexports
this module, preserving the previous declaration names and statements.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace HeckeSkeleton
open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open scoped Classical BigOperators ComplexConjugate
variable (K : Type) [Field K] [NumberField K]
variable (c : TargetContext K)
local notation "S" => places K c
local notation "P" => probeData K c
local notation "D" => (probeData K c).arithmetic
local notation "θ" => thetaPeriod K S P (targetCharacter K c)

-- OBLIGATION AR-LAMBDA-UNRAMIFIED | revised Proposition 3.1(iv), p.4.
-- From the Axiom choice: the correction character is unramified outside S.
theorem calibration_lambda_unramified : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K (probeData K c).Lambda p :=
  fun p hp => (axiomChoice K c).Lambda_unramified p hp

-- OBLIGATION AR-G-UNRAMIFIED | revised Proposition 3.1(iv), p.4.
theorem calibration_G_unramified : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K (probeData K c).G p :=
  fun p hp => (axiomChoice K c).G_unramified p hp

-- OBLIGATION AR-G-FINITE-ORDER | revised Proposition 3.1(iv), p.4.
theorem calibration_G_finite_order : FiniteOrder (probeData K c).G :=
  (axiomChoice K c).G_finiteOrder

-- OBLIGATION AR-LAMBDA-ANGULAR | revised Proposition 3.1(iv), p.4.
-- The correction records Lambda at infinity as the inverse angular character.
theorem calibration_lambda_angular : ∀ (v : InfinitePlace K) (hv : v.IsComplex),
    heckeComplexWeight K v hv (probeData K c).Lambda = 1 ∨ heckeComplexWeight K v hv (probeData K c).Lambda = -1 :=
  fun v hv => (axiomChoice K c).Lambda_weight v hv

-- OBLIGATION AR-LAMBDA-RADIAL-ZERO | revised Proposition 3.1(iv), p.4.
theorem calibration_lambda_radial_zero : ∀ (v : InfinitePlace K) (hv : v.IsComplex),
    heckeComplexParameter K v hv (probeData K c).Lambda = 0 :=
  fun v hv => (axiomChoice K c).Lambda_parameter v hv

-- OBLIGATION AR-CUBE-CALIBRATION | revised Proposition 3.1(iv), p.4.
-- The context's prime cube identity, multiplied over coprime factors.
theorem calibration_cube_calibration : ∀ I : ExteriorIdeal K S, Squarefree I.val.val →
    thetaGamma K S D I 2 ^ 3 =
      (UniqueFactorizationMonoid.moebius I.val.val : ℂ) * heckeIdealCoefficient K (probeData K c).Lambda I.val :=
  fun I hI => (axiomChoice K c).cube_calibration I hI

-- OBLIGATION AR-MIXED-CALIBRATION | revised Proposition 3.1(iv), p.4.
-- The context's prime mixed identity; reciprocity cancels the CRT phases.
theorem calibration_mixed_calibration : ∀ I : ExteriorIdeal K S, Squarefree I.val.val →
    conj (heckeIdealCoefficient K (probeData K c).Lambda I.val) * thetaGamma K S D I 2 *
      thetaGamma K S D I 1 =
        (UniqueFactorizationMonoid.moebius I.val.val : ℂ) * heckeIdealCoefficient K (probeData K c).G I.val :=
  fun I hI => (axiomChoice K c).mixed_calibration I hI

theorem arithmeticCalibration : ThetaCalibrationInput K S D (probeData K c).Lambda (probeData K c).G where
  lambda_unramified := calibration_lambda_unramified K c
  G_unramified := calibration_G_unramified K c
  G_finite_order := calibration_G_finite_order K c
  lambda_angular := calibration_lambda_angular K c
  lambda_radial_zero := calibration_lambda_radial_zero K c
  cube_calibration := calibration_cube_calibration K c
  mixed_calibration := calibration_mixed_calibration K c

-- OBLIGATION AR-ALLOWED-MULTIPLICATIVE | revised Proposition 3.1(i–iii), pp.3–4.
theorem allowed_multiplicative : ∀ I J : ExteriorIdeal K S, ∃ u : (places K c).unit K,
    (arithmeticData K c).generator (exteriorMul K S I J) =
      ((places K c).unitEquivUnitsInteger K u).val ^ 6 * (arithmeticData K c).generator I * (arithmeticData K c).generator J :=
  fun I J => (axiomChoice K c).thetaData_multiplicative I J

-- OBLIGATION AR-ALLOWED-RECIPROCITY | revised Proposition 3.1(i–iii), pp.3–4.
-- Through the sextic symbol dictionary: the context's reciprocity for coprime
-- allowed generators; noncoprime pairs give zero on both sides.
theorem allowed_reciprocity : ∀ I J : ExteriorIdeal K S,
    idealSymbol K S D I ((arithmeticData K c).generator J) = idealSymbol K S D J ((arithmeticData K c).generator I) :=
  fun I J => (axiomChoice K c).idealSymbol_reciprocity I J

-- OBLIGATION AR-ALLOWED-GENERATOR-NORM | revised Proposition 3.1(i–iii), pp.3–4.
-- Migration: holds for every ThetaArithmeticData; audited GeneratorInputs source.
theorem allowed_generator_norm : ∀ I : ExteriorIdeal K S,
    sLocalProductNorm K S (sLocalNonzeroIntegerDiagonal K S
      ⟨(arithmeticData K c).generator I, (arithmeticData K c).generator_ne_zero I⟩) = exteriorNorm K S I :=
  thetaGenerator_productNorm K S (arithmeticData K c)

theorem allowedGenerators : AllowedGeneratorInput K S D where
  multiplicative := allowed_multiplicative K c
  reciprocity := allowed_reciprocity K c
  generator_norm := allowed_generator_norm K c

end HeckeSkeleton
