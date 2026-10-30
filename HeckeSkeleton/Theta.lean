import HeckeSkeleton.Base
import HeckeSkeleton.FiniteMellinFromValuation
import HeckeSkeleton.MarkedAnnularSupport
import HeckeSkeleton.AllowedGeneratorNorm
import HeckeAxiom.LambdaInfinityType
import HeckeAxiom.SexticSymbolDictionary
import HeckeAxiom.GaussCalibration
import HeckeSkeleton.ThetaKernel

/-! Explicit arithmetic and KP/theta frontiers for the named actual construction.
The statements are admitted only in this exploratory branch. -/
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

-- OBLIGATION TH-KP-DATA | revised §3.2–3.4, pp.5–13.
-- Actual rotated KP coefficient tables; NOT supplied by ordinary Poisson.
def finiteMellinData : FiniteMellinData K S := by
  sorry
local notation "F" => finiteMellinData K c

-- OBLIGATION TH-FINITE-VALUATION-CUTOFF | revised §3.2–3.4, pp.5–8.
theorem finite_valuation_cutoff : ∃ k₀ : ℤ, ∀ u κ l p k, k < k₀ → (finiteMellinData K c).coefficient u κ l p k = 0 := by
  sorry

-- OBLIGATION TH-FINITE-VALUATION-DECAY | revised §3.2–3.4, pp.5–8.
theorem finite_valuation_decay : ∀ δ : ℝ, δ < 1 / 3 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ u κ l p k, 0 ≤ k →
      ‖(finiteMellinData K c).coefficient u κ l p k‖ ≤ C * (p.val.asIdeal.absNorm : ℝ) ^ (-(k : ℝ) * δ) := by
  sorry

-- OBLIGATION TH-FINITE-ABSOLUTE-MELLIN | revised §3.2–3.4, pp.5–8.
theorem finite_absolute_mellin : ∀ u κ l p s, -(1 / 3 : ℝ) < s.re →
    Summable (fun k : ℤ => (finiteMellinData K c).coefficient u κ l p k *
      (p.val.asIdeal.absNorm : ℂ) ^ (-(k : ℂ) * s)) := by
  exact HeckeSkeleton.FiniteMellin.finite_absolute_mellin_of_valuation_cutoff_decay K S
    (finiteMellinData K c) (finite_valuation_cutoff K c) (finite_valuation_decay K c)

theorem finiteAdmissible : FiniteMellinAdmissible K S F where
  valuation_cutoff := finite_valuation_cutoff K c
  valuation_decay := finite_valuation_decay K c
  absolute_mellin := finite_absolute_mellin K c

-- TH-KERNEL-INTEGRABLE (proved in HeckeSkeleton.ThetaKernel) | revised §3.2–3.4, Lemma 3.3, pp.6–8.
theorem kernel_integrable : ∀ (V : SmoothAnnularTest) u κ σ y, -(1 / 3 : ℝ) < σ → 0 < y →
    Integrable (kernelIntegrand K S F θ u κ V.toFun σ y) :=
  HeckeSkeleton.ThetaKernel.kernel_integrable K S F θ (finiteAdmissible K c)

-- TH-KERNEL-LINE-INDEPENDENT (proved in HeckeSkeleton.ThetaKernel) | revised §3.2–3.4, Lemma 3.3, pp.6–8.
theorem kernel_line_independent : ∀ (V : SmoothAnnularTest) u κ σ σ' y,
    -(1 / 3 : ℝ) < σ → -(1 / 3 : ℝ) < σ' → 0 < y →
    mellinReflectionKernel K S F θ u κ V.toFun σ y =
      mellinReflectionKernel K S F θ u κ V.toFun σ' y :=
  HeckeSkeleton.ThetaKernel.kernel_line_independent K S F θ (finiteAdmissible K c)

-- OBLIGATION TH-SIXTH-LOCAL-FINITE | revised §3.2–3.4, pp.5–8.
-- The S-local sixth-power class group is finite (complex places are 6-divisible;
-- finite places by Hensel, including p | 6). Small (about 500 lines; Axiom V_finite).
instance sixthLocalClasses_finite : Finite (SixthLocalClasses K S) := by
  sorry

-- TH-KERNEL-DERIVATIVE-BOUND (proved from TH-SIXTH-LOCAL-FINITE in HeckeSkeleton.ThetaKernel) | revised §3.2–3.4, Lemma 3.3, pp.6–8.
theorem kernel_derivative_bound : ∀ (A : ℝ) (h J : ℕ), 0 ≤ A →
    4 * (Fintype.card {v : InfinitePlace K // v.IsComplex} : ℝ) * A + h + 1 < J →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : SmoothAnnularTest) u κ y, 0 < y →
      ‖eulerDerivativeOrder h
        (mellinReflectionKernel K S F θ u κ V.toFun 0) y‖ ≤
      C * testSeminorm V.toFun J A * min (y ^ (1 / 4 : ℝ)) (y ^ (-A)) :=
  HeckeSkeleton.ThetaKernel.kernel_derivative_bound K S F θ (finiteAdmissible K c)

theorem mellinKernel : MellinKernelInput K S F θ where
  finite_admissible := finiteAdmissible K c
  integrable := kernel_integrable K c
  line_independent := kernel_line_independent K c
  derivative_bound := kernel_derivative_bound K c

-- OBLIGATION TH-MARKED-EXTERIOR-UNRAMIFIED | revised §3.2–3.4, Theorem 3.5, pp.10–13.
-- The period is conj(Lambda) * conj(G) * psi; each factor is unramified outside S.
theorem marked_exterior_unramified : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p :=
  fun p hp => UnramifiedAt.mul K
    (UnramifiedAt.mul K (UnramifiedAt.inv K (calibration_lambda_unramified K c p hp))
      (UnramifiedAt.inv K (calibration_G_unramified K c p hp)))
    (target_unramified_outside K c p hp)

-- OBLIGATION TH-MARKED-ANGULAR-NONZERO | revised §3.2–3.4, Theorem 3.5, pp.10–13.
-- The representative's orientation (revised §3, before Proposition 3.2).
theorem marked_angular_nonzero : ∃ (v : InfinitePlace K) (hv : v.IsComplex),
    heckeComplexWeight K v hv θ ≠ 0 :=
  representative_angular K c (calibration_lambda_angular K c) (calibration_G_finite_order K c)

-- OBLIGATION TH-MARKED-COMPLETED-ABSOLUTE | revised §3.2–3.4, Theorem 3.5, pp.10–13.
theorem marked_completed_absolute : ∀ (d : MarkedDatum K S) (V : SmoothAnnularTest) X, 0 < X →
    Summable (completedTerm K S D θ (rowElement K S D d) d.puncture d.marks V.toFun X) := by
  intro d V X hX
  exact HeckeSkeleton.MarkedAnnularSupport.completedTerm_summable_of_annular K S D θ
    (rowElement K S D d) d.puncture d.marks V X hX

-- OBLIGATION TH-MARKED-REFLECTED-ABSOLUTE | revised §3.2–3.4, Theorem 3.5, pp.10–13.
theorem marked_reflected_absolute : ∀ (d : MarkedDatum K S) (V : SmoothAnnularTest) X, 0 < X →
    Summable (fun i : ReflectionIndex K S d => reflectedTerm K S D d i F θ V.toFun X) := by
  sorry

-- OBLIGATION TH-MARKED-REFLECTION | revised §3.2–3.4, Theorem 3.5, pp.10–13.
theorem marked_reflection (hkernel : MellinKernelInput K S F θ) : ∀ (d : MarkedDatum K S) (V : SmoothAnnularTest) X, 0 < X →
    completedThetaSum K S D θ (rowElement K S D d) d.puncture d.marks V.toFun X =
      ∑' i : ReflectionIndex K S d, reflectedTerm K S D d i F θ V.toFun X := by
  sorry

theorem markedReflection : MarkedCoefficientReflectionInput K S D F θ where
  allowed_generators := allowedGenerators K c
  exterior_unramified := marked_exterior_unramified K c
  angular_nonzero := marked_angular_nonzero K c
  kernel := mellinKernel K c
  completed_absolute := marked_completed_absolute K c
  reflected_absolute := marked_reflected_absolute K c
  reflection := marked_reflection K c (mellinKernel K c)

end HeckeSkeleton
