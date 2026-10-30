import HeckeSkeleton.HighBinSupport.ActualTupleAmplitudeBound
import HeckeSkeleton.HighBinSupport.ActualDenominatorMellin
import HeckeSkeleton.HighBinSupport.ActualAdditiveMellinRapidDecay
import HeckeSkeleton.HighBinSupport.BoundaryRectangle
import HeckeSkeleton.HeckeFiniteBackgroundControl
/-!
A pointwise envelope for the literal compensated physical kernel.

The actual positive window mass cancels against the actual prime
normalizer, including its zero case. The remaining geometry costs the
fixed power Z^5. Arbitrarily many horizontal powers then come from the
actual additive Mellin profile together with the Gaussian. The only
arithmetic size input below is a pointwise bound for the lower-level
marked row Euler continuations; neither a contour bound nor a high-bin
estimate is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace HighBinBoundary.ActualKernel

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators ComplexConjugate

/-- The Gaussian has a uniformly bounded real factor throughout the
whole swept s strip; its imaginary factor still couples s and z. -/
theorem gaussian_swept_bound (s z : ℂ)
    (hs0 : 1 / 2 ≤ s.re) (hs1 : s.re ≤ 2) (hz : z.re = 17 / 50) :
    ‖Complex.exp ((s + z - 1) ^ 2)‖ ≤
      Real.exp 4 * Real.exp (-((s.im + z.im) ^ 2)) := by
  have hlo : -2 ≤ s.re + 17 / 50 - 1 := by linarith
  have hhi : s.re + 17 / 50 - 1 ≤ 2 := by linarith
  have hsq : (s.re + 17 / 50 - 1) ^ 2 ≤ 4 := by
    nlinarith [mul_nonneg (show 0 ≤ 2 - (s.re + 17 / 50 - 1) by linarith)
      (show 0 ≤ 2 + (s.re + 17 / 50 - 1) by linarith)]
  have hre : ((s + z - 1) ^ 2).re =
      (s.re + 17 / 50 - 1) ^ 2 - (s.im + z.im) ^ 2 := by
    simp [pow_two, hz]
  rw [Complex.norm_exp, hre]
  calc
    _ ≤ Real.exp (4 - (s.im + z.im) ^ 2) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem frequencyRow_power_bound (u : FrequencyRow K S) (z : ℂ)
    (hz : z.re = 17 / 50) :
    ‖(frequencyRowNorm K S u : ℂ) ^ (-z)‖ ≤ 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (idealNorm_pos K u.ideal.val)]
  simp only [Complex.neg_re, hz]
  exact Real.rpow_le_one_of_one_le_of_nonpos (one_le_idealNorm K u.ideal.val)
    (by norm_num)

variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)]
  [∀ p : S, BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : S) → Measure (p.val.adicCompletion K))
variable [∀ p : S, (μ p).IsAddHaarMeasure]

/-- The fixed envelope is independent of rows, the ray filter, the
external height and every later derivative order. No nonzero-normalizer
premise is used: the original totalized division is preserved. -/
theorem exists_compensated_kernel_envelope
    (P : ProbeData K S) (g : PrimeWindowGeometry) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ψ : HeckeCharacter K) (E : RowEulerData K S P)
        (T : Finset (HeckeCharacter K)) (u : FrequencyRow K S)
        (Z : ℝ), 1 ≤ Z → ∀ s w z : ℂ,
        1 / 2 ≤ s.re → s.re ≤ 2 → -1 ≤ w.re → w.re ≤ 1 → z.re = 17 / 50 →
        ∀ M : ℝ, 0 ≤ M →
        (∀ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
          ∀ Q : Finset (ExteriorPrime K S), Q ⊆ Finset.univ.image p →
            ‖rowEulerContinuation K S P ψ E Q u s w z‖ ≤ M) →
        ‖compensatedRowMellinKernel K S μ P ψ E g T u Z s w z‖ ≤
          C * Z ^ 5 * M *
            (Real.exp (-((s.im + z.im) ^ 2)) * ‖additiveMellin K S μ P.additive z‖) := by
  obtain ⟨D, hD, hden⟩ :=
    ActualDenominator.exists_mellin_uniform_strip_bound P.denominator (-1) 1 0
  let C₀ : ℝ := Real.exp 4 * D * (‖(physicalResidueNormalizer K S μ P)⁻¹‖ + 1)
  let C₂ : ℝ := 2 ^ ((5 / 6 : ℝ) * (g.slots : ℝ))
  let C₃₂ : ℝ := (32 : ℝ) ^ g.slots
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hC₂ : 0 < C₂ := Real.rpow_pos_of_pos (by norm_num) _
  have hC₃₂ : 0 < C₃₂ := by dsimp [C₃₂]; positivity
  refine ⟨C₀ * C₂ * C₃₂, mul_pos (mul_pos hC₀ hC₂) hC₃₂, ?_⟩
  intro ψ E T u Z hZ s w z hs0 hs1 hw0 hw1 hz M hM hrow
  have hZ0 : 0 < Z := by linarith
  have htuple (p : Fin g.slots → ExteriorPrime K S)
      (hp : p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i)) :
      ‖ActualPrimeNormalizer.tupleMellinAmplitude K S P ψ E g u Z s w z p‖ ≤
        C₃₂ * Z ^ 4 * M :=
    ActualTuple.tupleMellinAmplitude_bound_of_rowEuler_bound K S P ψ E g T u Z hZ
      s w z hs1 hw0 hw1 hz M hM p hp (hrow p hp)
  have hraw := ActualPrimeNormalizer.compensatedRowMellinKernel_bound_of_tuple_bound
    K S μ P ψ E g T u Z hZ0 s w z (C₃₂ * Z ^ 4 * M) (by positivity) htuple
  have hw : ‖mellin P.denominator.toFun w‖ ≤ D := by
    simpa only [pow_zero, one_mul, Complex.re_add_im] using hden w.re w.im hw0 hw1
  have hG := gaussian_swept_bound s z hs0 hs1 hz
  have hN := frequencyRow_power_bound K S u z hz
  have hP : ‖(physicalResidueNormalizer K S μ P)⁻¹‖ ≤
      ‖(physicalResidueNormalizer K S μ P)⁻¹‖ + 1 := by linarith
  have hpref :
      ‖Complex.exp ((s + z - 1) ^ 2) * additiveMellin K S μ P.additive z *
        mellin P.denominator.toFun w * (frequencyRowNorm K S u : ℂ) ^ (-z) /
          physicalResidueNormalizer K S μ P‖ ≤
      C₀ * (Real.exp (-((s.im + z.im) ^ 2)) * ‖additiveMellin K S μ P.additive z‖) := by
    rw [div_eq_mul_inv]
    simp only [norm_mul]
    calc
      _ ≤ ((Real.exp 4 * Real.exp (-((s.im + z.im) ^ 2))) *
          ‖additiveMellin K S μ P.additive z‖ * D * 1) *
          (‖(physicalResidueNormalizer K S μ P)⁻¹‖ + 1) := by
        exact mul_le_mul
          (mul_le_mul
            (mul_le_mul
              (mul_le_mul_of_nonneg_right hG (norm_nonneg _)) hw
              (norm_nonneg _) (by positivity)) hN (norm_nonneg _) (by positivity))
          hP (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [C₀]; ring
  have hsmall : Z ^ (1 / 6 : ℝ) ≤ Z := by
    calc
      _ ≤ Z ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)
      _ = Z := Real.rpow_one _
  apply hraw.trans
  calc
    _ ≤ (C₀ * (Real.exp (-((s.im + z.im) ^ 2)) * ‖additiveMellin K S μ P.additive z‖)) *
        ((C₂ * Z) * (C₃₂ * Z ^ 4 * M)) := by
      exact mul_le_mul hpref
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsmall hC₂.le) (by positivity))
        (by positivity) (by positivity)
    _ = _ := by ring

#print axioms gaussian_swept_bound
#print axioms exists_compensated_kernel_envelope

end HighBinBoundary.ActualKernel

namespace HighBinBoundary.ActualKernelHorizontal

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S₀" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [MeasurableSpace (sLocalNormOneGroup K S₀)]
  [BorelSpace (sLocalNormOneGroup K S₀)]
variable [∀ p : S₀, MeasurableSpace (p.val.adicCompletion K)]
  [∀ p : S₀, BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : S₀) → Measure (p.val.adicCompletion K))
variable [∀ p : S₀, (μ p).IsAddHaarMeasure]

/-- Every horizontal decay order is obtained from the original additive
test and the coupled Gaussian. The fixed geometric degree stays 5. -/
theorem exists_compensated_kernel_horizontal_decay
    (P : ProbeData K S₀) (g : PrimeWindowGeometry) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ψ : HeckeCharacter K) (E : RowEulerData K S₀ P)
        (T : Finset (HeckeCharacter K)) (u : FrequencyRow K S₀)
        (Z : ℝ), 1 ≤ Z → ∀ s w z : ℂ,
        1 / 2 ≤ s.re → s.re ≤ 2 → -1 ≤ w.re → w.re ≤ 1 → z.re = 17 / 50 →
        ∀ M : ℝ, 0 ≤ M →
        (∀ p ∈ Fintype.piFinset (fun i => primeWindow K S₀ g T Z i),
          ∀ Q : Finset (ExteriorPrime K S₀), Q ⊆ Finset.univ.image p →
            ‖rowEulerContinuation K S₀ P ψ E Q u s w z‖ ≤ M) →
        (1 + |s.im|) ^ n *
          ‖compensatedRowMellinKernel K S₀ μ P ψ E g T u Z s w z‖ ≤
          C * Z ^ 5 * M := by
  letI : IsTotallyComplex K :=
    ⟨HeckeSkeleton.HeckeFiniteBackgroundControl.all_complex_of_primitive12
      K P.arithmetic.primitive12⟩
  obtain ⟨C₀, hC₀, henv⟩ := ActualKernel.exists_compensated_kernel_envelope K S₀ μ P g
  obtain ⟨D, hD, hprof⟩ := ActualAdditiveBorel.exists_additiveMellin_rapid_bound_actualBorel
    K S (fun p => inferInstance) (fun p => inferInstance) μ (fun p => inferInstance)
    P.additive (17 / 50) (by norm_num) (by norm_num) n
  refine ⟨C₀ * (gaussianMoment n * D), mul_pos hC₀ (mul_pos (gaussianMoment_pos n) hD), ?_⟩
  intro ψ E T u Z hZ s w z hs0 hs1 hw0 hw1 hz M hM hrow
  have hZ0 : 0 ≤ Z := le_trans (by norm_num) hZ
  have hkernel := henv ψ E T u Z hZ s w z hs0 hs1 hw0 hw1 hz M hM hrow
  have hzline : (17 / 50 : ℂ) + z.im * Complex.I = z := by
    simpa [hz] using Complex.re_add_im z
  have hcoupled := coupled_gaussian_profile_bound
    (fun t : ℝ => additiveMellin K S₀ μ P.additive ((17 / 50 : ℂ) + t * Complex.I))
    n D hprof s.im z.im
  rw [hzline] at hcoupled
  calc
    _ ≤ (1 + |s.im|) ^ n *
        (C₀ * Z ^ 5 * M *
          (Real.exp (-((s.im + z.im) ^ 2)) * ‖additiveMellin K S₀ μ P.additive z‖)) :=
      mul_le_mul_of_nonneg_left hkernel (by positivity)
    _ = (C₀ * Z ^ 5 * M) *
        ((1 + |s.im|) ^ n *
          (Real.exp (-((s.im + z.im) ^ 2)) * ‖additiveMellin K S₀ μ P.additive z‖)) := by ring
    _ ≤ (C₀ * Z ^ 5 * M) * (gaussianMoment n * D) :=
      mul_le_mul_of_nonneg_left hcoupled (by positivity)
    _ = _ := by ring

#print axioms exists_compensated_kernel_horizontal_decay

end HighBinBoundary.ActualKernelHorizontal
