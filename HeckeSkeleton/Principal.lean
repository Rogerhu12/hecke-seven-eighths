import HeckeSkeleton.Theta
import HeckeSkeleton.Gram
import HeckeSkeleton.ActualProbeIntegralComplete
import HeckeSkeleton.ActualPrincipalWindowError
import HeckeSkeleton.PrimeNormalizer
import HeckeSkeleton.LowCauchy

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace HeckeSkeleton
open NumberField IsDedekindDomain MeasureTheory Filter Asymptotics
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open scoped Classical BigOperators Topology ComplexConjugate
variable (K : Type) [Field K] [NumberField K]
variable (c : TargetContext K)
local notation "S" => places K c
local notation "P" => probeData K c
local notation "ψ" => targetCharacter K c
local notation "g" => c.geometry
local notation "T" => rayFilter K c
local instance : MeasurableSpace (sLocalNormOneGroup K S) := (probeMeasures K c).normOneSpace
local instance : BorelSpace (sLocalNormOneGroup K S) := (probeMeasures K c).normOneBorel
local instance (p : S) : MeasurableSpace (p.val.adicCompletion K) := (probeMeasures K c).localSpace p
local instance (p : S) : BorelSpace (p.val.adicCompletion K) := (probeMeasures K c).localBorel p
local notation "μ" => (probeMeasures K c).haar
local instance (p : S) : (μ p).IsAddHaarMeasure := (probeMeasures K c).haar_isAddHaar p

-- OBLIGATION PR-INTEGRAL-THETA-ABSOLUTE | revised §6.1–6.2, pp.35–37.
-- Migration: proved by HeckeSkeleton.ActualProbeIntegralComplete (native certificate 2026-10-12).
theorem integral_theta_absolute : ∀ (m : (places K c).integer K) (Q : Finset (ExteriorPrime K S)) (Z : ℝ),
    0 < Z → Summable (completedTerm K S (probeData K c).arithmetic (thetaPeriod K S P ψ) m
      (primeSetIdeal K S ∅) Q logGaussianProfile Z) := by
  exact (actual_probeIntegralInput K S P ψ).theta_absolute

-- OBLIGATION PR-INTEGRAL-ROW-FINITE | revised §6.1–6.2, pp.35–37.
-- Migration: proved by HeckeSkeleton.ActualProbeIntegralComplete (native certificate 2026-10-12).
theorem integral_row_finite : ∀ (Q : Finset (ExteriorPrime K S)) (X Z : ℝ), 0 < X → 0 < Z →
    ∀ (t : sLocalNormOneGroup K S) (I : ExteriorIdeal K S),
      Set.Finite {m : NonzeroRingElements ((places K c).integer K) |
        probeRowTerm K S P ψ Q X Z t I m ≠ 0} := by
  exact (actual_probeIntegralInput K S P ψ).row_finite

-- OBLIGATION PR-INTEGRAL-DENOMINATOR-ABSOLUTE | revised §6.1–6.2, pp.35–37.
-- Migration: proved by HeckeSkeleton.ActualProbeIntegralComplete (native certificate 2026-10-12).
theorem integral_denominator_absolute : ∀ (Q : Finset (ExteriorPrime K S)) (X Y Z : ℝ),
    0 < X → 0 < Y → 0 < Z → ∀ t : sLocalNormOneGroup K S,
      Summable (probeDenominatorTerm K S P ψ Q X Y Z t) := by
  exact (actual_probeIntegralInput K S P ψ).denominator_absolute

-- OBLIGATION PR-INTEGRAL-INTEGRAL | revised §6.1–6.2, pp.35–37.
-- Migration: proved by HeckeSkeleton.ActualProbeIntegralComplete (native certificate 2026-10-12).
theorem integral_integral : ∀ (Q : Finset (ExteriorPrime K S)) (X Y Z : ℝ),
    0 < X → 0 < Y → 0 < Z →
    letI : (sixthPowerUnits K S).FiniteIndex :=
      sUnit_power_range_finiteIndex K S 6 (by decide)
    IntegrableOn (probeIntegrand K S P ψ Q X Y Z)
      (sUnitFundamentalDomain K S (sixthPowerUnits K S)) (sUnitHaarMeasure K S) := by
  exact (actual_probeIntegralInput K S P ψ).integral

-- OBLIGATION PR-INTEGRAL-SIXTH-UNIT-INVARIANT | revised §6.1–6.2, pp.35–37.
-- Migration: proved by HeckeSkeleton.ActualProbeIntegralComplete (native certificate 2026-10-12).
theorem integral_sixth_unit_invariant : ∀ (Q : Finset (ExteriorPrime K S)) (X Y Z : ℝ),
    0 < X → 0 < Y → 0 < Z → ∀ (u : (places K c).unit K) (t : sLocalNormOneGroup K S),
      probeIntegrand K S P ψ Q X Y Z (sLocalNormOneDiagonal K S (u ^ 6) * t) =
        probeIntegrand K S P ψ Q X Y Z t := by
  exact (actual_probeIntegralInput K S P ψ).sixth_unit_invariant

theorem probeIntegrals : ProbeIntegralInput K S P ψ where
  theta_absolute := integral_theta_absolute K c
  row_finite := integral_row_finite K c
  denominator_absolute := integral_denominator_absolute K c
  integral := integral_integral K c
  sixth_unit_invariant := integral_sixth_unit_invariant K c

-- OBLIGATION PR-TARGET-UNRAMIFIED | revised §6.1–6.4, pp.35–40.
-- The Axiom choice was made with the target's ramified primes inside S.
theorem principal_target_unramified : ∀ p : ExteriorPrime K S, UnramifiedAt K ψ p.val :=
  fun p => target_unramified_outside K c p.val p.property

-- OBLIGATION PR-PERIOD-UNRAMIFIED | revised §6.1–6.4, pp.35–40.
-- The period is conj(Lambda) * conj(G) * psi; each factor is unramified outside S.
theorem principal_period_unramified : ∀ p : ExteriorPrime K S, UnramifiedAt K (thetaPeriod K S P ψ) p.val :=
  fun p => UnramifiedAt.mul K
    (UnramifiedAt.mul K (UnramifiedAt.inv K (calibration_lambda_unramified K c p.val p.property))
      (UnramifiedAt.inv K (calibration_G_unramified K c p.val p.property)))
    (principal_target_unramified K c p)

-- OBLIGATION PR-RAY-FINITEORDER | revised §6.1–6.4, pp.35–40.
-- The filter is empty (revised §6.1: all primes outside S are allowed).
theorem principal_ray_finiteOrder : ∀ χ ∈ T, FiniteOrder χ := by
  intro χ hχ
  simp [rayFilter] at hχ

-- OBLIGATION PR-FOURIER-ZERO | revised §6.1–6.4, pp.35–40.
-- Axiom's tensor has zero integral; the skeleton's transform is a multiple of Axiom's.
theorem principal_fourier_zero : additiveFourierAtZero K S μ (probeData K c).additive = 0 :=
  (Classical.choose_spec (HeckeAxiom.ProbeTestChoice.exists_probeTest (axiomChoice K c).A
    (axiomChoice K c).hS)).1

/-- The probe test's additive Mellin value at `1/6` is a positive real. -/
theorem principal_mellin_positive :
    (additiveMellin K S μ (probeData K c).additive (1 / 6)).im = 0 ∧
      0 < (additiveMellin K S μ (probeData K c).additive (1 / 6)).re :=
  (Classical.choose_spec (HeckeAxiom.ProbeTestChoice.exists_probeTest (axiomChoice K c).A
    (axiomChoice K c).hS)).2

-- OBLIGATION PR-NORMALIZATION-REAL | revised §6.1–6.4, pp.35–40.
-- The residue, the Mellin values at 1/6 and at 1 are positive reals.
theorem principal_normalization_real : (physicalResidueNormalizer K S μ P).im = 0 :=
  (HeckeAxiom.ProbeNormalization.physicalResidueNormalizer_pos S μ P
    DedekindZetaZeroFree.probeRealBumpWeight rfl (principal_mellin_positive K c).1
    (principal_mellin_positive K c).2).1

-- OBLIGATION PR-NORMALIZATION-POSITIVE | revised §6.1–6.4, pp.35–40.
theorem principal_normalization_positive : 0 < (physicalResidueNormalizer K S μ P).re :=
  (HeckeAxiom.ProbeNormalization.physicalResidueNormalizer_pos S μ P
    DedekindZetaZeroFree.probeRealBumpWeight rfl (principal_mellin_positive K c).1
    (principal_mellin_positive K c).2).2

-- PR-NORMALIZER-POSITIVE | revised §6.1–6.4, pp.35–40.
-- Reduced to the window prime ideal theorem (PR-WINDOW-PIT) in HeckeSkeleton.PrimeNormalizer.
theorem principal_normalizer_positive : ∃ Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
    0 < (primeNormalizer K S g T Z).re :=
  PrimeNormalizer.normalizer_positive K S g

-- PR-NORMALIZER-SMALLPOWER | revised §6.1–6.4, pp.35–40.
-- Reduced to the window prime ideal theorem (PR-WINDOW-PIT) in HeckeSkeleton.PrimeNormalizer.
theorem principal_normalizer_smallPower : ∀ ε : ℝ, 0 < ε →
    (fun Z => (primeNormalizer K S g T Z)⁻¹) =O[atTop] (fun Z : ℝ => Z ^ ε) :=
  PrimeNormalizer.normalizer_smallPower K S g

-- OBLIGATION PR-PRINCIPAL-WINDOW-ERROR | revised §6.1–6.4, pp.35–40.
theorem principal_principal_window_error : ∃ C Z₀ : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧
    ∀ (Z : ℝ) (s : ℂ), Z₀ ≤ Z → 7 / 8 < s.re →
      ‖compensatedPrincipalCorrection K S P ψ g T Z s -
        principalCorrection K S P ψ s * (Z : ℂ) ^ (1 / 36 : ℂ) * primeNormalizer K S g T Z‖ ≤
      C * Z ^ (-principalSlotSaving g) *
        ‖principalCorrection K S P ψ s * (Z : ℂ) ^ (1 / 36 : ℂ) * primeNormalizer K S g T Z‖ :=
  ActualPrincipalWindowDraft.actual_principal_window_error K S P ψ g T
    (principal_target_unramified K c)

/-- Surviving marked slots are summed BEFORE taking the actual row norm.
Selected slots remain fixed, as in revised (6.22). -/
def completedMarkedRow (Z : ℝ) (p : Fin c.geometry.slots → ExteriorPrime K S)
    (J : Finset (Fin c.geometry.slots)) (m : NonzeroRingElements ((places K c).integer K)) : ℂ :=
  ∑ p' ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
    if ∀ i ∈ J, p' i = p i then
      (∏ i ∈ Finset.univ \ J, windowWeight K S g Z i (p' i)) *
      conj (heckeIdealCoefficient K ψ (subsetPrimeIdeal K S p' (Finset.univ \ J)).val) *
      completedThetaSum K S (probeData K c).arithmetic (thetaPeriod K S P ψ) m.val
        (primeSetIdeal K S ∅) ((Finset.univ \ J).image p') logGaussianProfile
        (Z * exteriorNorm K S (subsetPrimeIdeal K S p' (Finset.univ \ J)))
    else 0

/-- Precise rescaled row budget, with all original sixth-unit sectors. -/
def CompletedMarkedEnergy : Prop :=
  ∀ B ε : ℝ, 0 < B → 0 < ε → ∃ C Z₀ : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧
  ∀ Z : ℝ, Z₀ ≤ Z → ∀ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
  ∀ J : Finset (Fin c.geometry.slots),
    let q := exteriorNorm K S (subsetPrimeIdeal K S p J)
    (∑' u : Gram.Orbit K S,
      if (sIntegerOrbitNorm K S (sixthPowerUnits K S) u).val ≤ B * Z ^ (5 / 6 : ℝ) / q ^ 2
      then ‖completedMarkedRow K c Z p J u.out‖ ^ 2 else 0) ≤
      C * Z ^ (5 / 6 + ε) / q ^ 2

-- OBLIGATION LOW-REFLECTED-ENERGY | revised Lemma 4.8 and (6.22), pp.23–25,40.
-- Coarse frontier: powerful-row ledger, hybrid energy and Gaussian annuli.
theorem completedMarkedEnergy (L : LocalHighKMellinInput K c)
    (hreflection : MarkedCoefficientReflectionInput K S (probeData K c).arithmetic
      (finiteMellinData K c L) (thetaPeriod K S P ψ)) : CompletedMarkedEnergy K c := by
  sorry

-- LOW-CAUCHY-COMPENSATION | revised Proposition 6.2, pp.40–41.
-- Proved in HeckeSkeleton.LowCauchy (marked spectral Cauchy bound and assembly).
theorem low_of_gram_and_completedEnergy
    (hgram : Gram.GramBound K S P)
    (henergy : CompletedMarkedEnergy K c)
    (hnorm : ∀ ε : ℝ, 0 < ε →
      (fun Z => (primeNormalizer K S g T Z)⁻¹) =O[atTop] (fun Z : ℝ => Z ^ ε)) :
    ∀ ε : ℝ, 0 < ε →
      normalizedProbe K S μ P ψ g T =O[atTop] (fun Z : ℝ => Z ^ (3 / 16 + ε)) :=
  LowCauchy.low_of_gram_and_completedEnergy K c hgram henergy hnorm

theorem principalSource (L : LocalHighKMellinInput K c)
    (H : LocalExteriorDigitInput K c) :
    (probeMeasures K c).principalInput P ψ g T := by
  change TPrincipalInput K S μ P ψ g T
  exact {
    arithmetic_calibration := arithmeticCalibration K c
    allowed_generators := allowedGenerators K c
    integrals := probeIntegrals K c
    target_unramified := principal_target_unramified K c
    period_unramified := principal_period_unramified K c
    ray_finiteOrder := principal_ray_finiteOrder K c
    fourier_zero := principal_fourier_zero K c
    normalization_real := principal_normalization_real K c
    normalization_positive := principal_normalization_positive K c
    normalizer_positive := principal_normalizer_positive K c
    normalizer_smallPower := principal_normalizer_smallPower K c
    principal_window_error := principal_principal_window_error K c
    low := low_of_gram_and_completedEnergy K c
      (Gram.gramBound_of_calibrated K S P (allowedGenerators K c) (arithmeticCalibration K c))
      (completedMarkedEnergy K c L (markedReflection K c L H))
      (principal_normalizer_smallPower K c)
  }

end HeckeSkeleton
