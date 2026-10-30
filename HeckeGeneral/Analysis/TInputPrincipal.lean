import HeckeGeneral.Analysis.PhysicalProbePrincipal
import HeckeGeneral.Analysis.PrincipalEulerFactor

/-!
A precise PART of M's T, for the literal physical objects, not full T.
The low estimate and the primitive principal window error are source-level
inputs.  Convergence, analyticity and non-vanishing of the actual principal
correction are NOT inputs: `PrincipalEulerFactor` proves them on Re s > 2/3
from the literal local formula, and the prime normalizer is real at positive
scales by `primeNormalizer_im_eq_zero`. The final height comparison/high
estimate is NOT a field. Small/middle/moderate/large row contours and calibrated detector
coverage still have to be added with their actual summands.

Quantifiers: the geometric choices and requested loss precede the target.
The record below is for an already fixed target and allows its constants
and thresholds to depend on that target. No packet-uniform constant is
claimed. The corresponding packet wrapper must put `exists geometry`
before `forall target`, and cannot simply swap those quantifiers.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain MeasureTheory Set Filter Asymptotics
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators Topology ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

omit [Fintype S] in
/-- The prime normalizer is real at every positive scale: the window weights are
real-valued, and the norm powers and the scale power have positive real bases. -/
theorem primeNormalizer_im_eq_zero (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    {Z : ℝ} (hZ : 0 < Z) : (primeNormalizer K S g T Z).im = 0 := by
  have hZc : (Z : ℂ) ^ (-(1 / 36 : ℂ)) = ((Z ^ (-(1 / 36 : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hZ.le]
    push_cast
    rfl
  have hN : ∀ p : ExteriorPrime K S, (p.val.asIdeal.absNorm : ℂ) ^ (-(5 / 6 : ℂ)) =
      (((p.val.asIdeal.absNorm : ℝ) ^ (-(5 / 6 : ℝ)) : ℝ) : ℂ) := fun p => by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
    push_cast
    rfl
  rw [← Complex.conj_eq_iff_im]
  unfold primeNormalizer normalizerSlot
  simp only [map_mul, map_prod, map_sum, map_pow, map_neg, map_one]
  rw [hZc, Complex.conj_ofReal]
  congr 1
  refine Finset.prod_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => ?_
  have hw : conj (windowWeight K S g Z i p) = windowWeight K S g Z i p :=
    Complex.conj_eq_iff_im.mpr (g.real_valued i _)
  rw [hN, Complex.conj_ofReal, hw]

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : S, BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : S) → Measure (p.val.adicCompletion K))
variable [∀ p : S, (μ p).IsAddHaarMeasure]

/-- Analytic well-definedness of the actual probe. The Gaussian extension
of coefficient reflection and Poisson formula are not inferred from this.
In particular this is not a replacement for an automorphic realization. -/
structure ProbeIntegralInput (P : ProbeData K S) (ψ : HeckeCharacter K) : Prop where
  theta_absolute : ∀ (m : S.integer K) (Q : Finset (ExteriorPrime K S)) (Z : ℝ),
    0 < Z → Summable (completedTerm K S P.arithmetic (thetaPeriod K S P ψ) m
      (primeSetIdeal K S ∅) Q logGaussianProfile Z)
  row_finite : ∀ (Q : Finset (ExteriorPrime K S)) (X Z : ℝ), 0 < X → 0 < Z →
    ∀ (t : sLocalNormOneGroup K S) (I : ExteriorIdeal K S),
      Set.Finite {m : NonzeroRingElements (S.integer K) |
        probeRowTerm K S P ψ Q X Z t I m ≠ 0}
  denominator_absolute : ∀ (Q : Finset (ExteriorPrime K S)) (X Y Z : ℝ),
    0 < X → 0 < Y → 0 < Z → ∀ t : sLocalNormOneGroup K S,
      Summable (probeDenominatorTerm K S P ψ Q X Y Z t)
  integral : ∀ (Q : Finset (ExteriorPrime K S)) (X Y Z : ℝ),
    0 < X → 0 < Y → 0 < Z →
    letI : (sixthPowerUnits K S).FiniteIndex :=
      sUnit_power_range_finiteIndex K S 6 (by decide)
    IntegrableOn (probeIntegrand K S P ψ Q X Y Z)
      (sUnitFundamentalDomain K S (sixthPowerUnits K S)) (sUnitHaarMeasure K S)
  sixth_unit_invariant : ∀ (Q : Finset (ExteriorPrime K S)) (X Y Z : ℝ),
    0 < X → 0 < Y → 0 < Z → ∀ (u : S.unit K) (t : sLocalNormOneGroup K S),
      probeIntegrand K S P ψ Q X Y Z (sLocalNormOneDiagonal K S (u ^ 6) * t) =
        probeIntegrand K S P ψ Q X Y Z t

/-- Primitive principal and low inputs of M Sections 4--5, with every
quantity tied to its concrete arithmetic/Fourier definition. This is
deliberately not named TInput: the nonprincipal row transfer is absent. -/
structure TPrincipalInput (P : ProbeData K S) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) : Prop where
  arithmetic_calibration : ThetaCalibrationInput K S P.arithmetic P.Lambda P.G
  allowed_generators : AllowedGeneratorInput K S P.arithmetic
  integrals : ProbeIntegralInput K S P ψ
  target_unramified : ∀ p : ExteriorPrime K S, UnramifiedAt K ψ p.val
  period_unramified : ∀ p : ExteriorPrime K S, UnramifiedAt K (thetaPeriod K S P ψ) p.val
  ray_finiteOrder : ∀ χ ∈ T, FiniteOrder χ
  fourier_zero : additiveFourierAtZero K S μ P.additive = 0
  normalization_real : (physicalResidueNormalizer K S μ P).im = 0
  normalization_positive : 0 < (physicalResidueNormalizer K S μ P).re
  normalizer_positive : ∃ Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
    0 < (primeNormalizer K S g T Z).re
  normalizer_smallPower : ∀ ε : ℝ, 0 < ε →
    (fun Z => (primeNormalizer K S g T Z)⁻¹) =O[atTop] (fun Z : ℝ => Z ^ ε)
  principal_window_error : ∃ C Z₀ : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧
    ∀ (Z : ℝ) (s : ℂ), Z₀ ≤ Z → 7 / 8 < s.re →
      ‖compensatedPrincipalCorrection K S P ψ g T Z s -
        principalCorrection K S P ψ s * (Z : ℂ) ^ (1 / 36 : ℂ) * primeNormalizer K S g T Z‖ ≤
      C * Z ^ (-principalSlotSaving g) *
        ‖principalCorrection K S P ψ s * (Z : ℂ) ^ (1 / 36 : ℂ) * primeNormalizer K S g T Z‖
  low : ∀ ε : ℝ, 0 < ε →
    normalizedProbe K S μ P ψ g T =O[atTop] (fun Z : ℝ => Z ^ (3 / 16 + ε))

omit [∀ p : S, BorelSpace (p.val.adicCompletion K)]
    [∀ p : S, (μ p).IsAddHaarMeasure] in
theorem TPrincipalInput.principal_ne_zero
    {P : ProbeData K S} {ψ : HeckeCharacter K} {g : PrimeWindowGeometry}
    {T : Finset (HeckeCharacter K)} (_h : TPrincipalInput K S μ P ψ g T)
    {s : ℂ} (hs : 7 / 8 < s.re) : principalCorrection K S P ψ s ≠ 0 :=
  principalCorrection_ne_zero K S P ψ (by linarith)

end HeckeGeneral.ThetaSkeleton.Physical
