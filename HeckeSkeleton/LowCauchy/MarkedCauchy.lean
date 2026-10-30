import HeckeSkeleton.GramDefinitions
import HeckeSkeleton.ActualProbeIntegralComplete
import HeckeGeneral.Arithmetic.SIntegerOrbitCounting
import ActualProbeSpectralOrbitSupport
import ActualProbeLogUniformFourier
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Marked spectral Cauchy bound (revised Proposition 6.2, analytic half)

A finite linear combination of the ORIGINAL probe integrands, all with the same
spectral parameters `X, Y` but arbitrary theta parameters, is expanded with the
core frequency expansion.  The spectral rows are summed BEFORE Cauchy--Schwarz,
so the row coefficient is the combined theta coefficient `Θ`.  Being a finite
combination of completed theta sums, `Θ` is invariant under the original sixth
power S-units.  One finite row set, chosen before the frequency and every theta
parameter, carries the separating Fourier factor; its original-Γ image lies in
the orbit norm ball `Cball * X * Y` and has uniformly bounded fibres.  Rapid
Fourier decay integrates the logarithmic frequency, and the Haar fundamental
domain has finite volume.

No Gram estimate and no theta energy estimate is proved here: both enter as
explicit hypotheses on the literal row energies over the same orbit box.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.LowCauchy

open NumberField IsDedekindDomain MeasureTheory Filter Asymptotics
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.ActualProbeLogDraft
open HeckeGeneral.ThetaSkeleton.Physical.ActualAdditiveGramDraft
open scoped Classical BigOperators Topology ComplexConjugate FourierTransform

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local notation "NZ" => NonzeroRingElements (S.integer K)
local notation "OQ" => SIntegerOrbits K S (sixthPowerUnits K S)

/-- One finite row set, chosen before the Fourier frequency and every theta
parameter, carries the separating Fourier factor.  Its original-Γ image lies
in the orbit norm ball and it has uniformly bounded original-Γ fibres. -/
theorem lc_exists_fourier_support (P : ProbeData K S) :
    ∃ Cball : ℝ, 0 < Cball ∧ ∃ B : ℕ,
      ∀ (t : sLocalNormOneGroup K S) (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y),
      ∃ M : Finset NZ,
        (∀ q ∈ M.image (probeSixthOrbit K S),
          (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val ≤ Cball * (X * Y)) ∧
        (∀ (ξ : ℝ) (m : NZ), m ∉ M →
          (𝓕 (probeLogSchwartz K S P (probeColumnBasePoint K S m t X Y hX hY))) ξ = 0) ∧
        ∀ f : OQ → ℝ, (∀ q, 0 ≤ f q) →
          (∑ m ∈ M, f (probeSixthOrbit K S m)) ≤
            (B : ℝ) * ∑ q ∈ M.image (probeSixthOrbit K S), f q := by
  obtain ⟨Cball, hCball, hnorm⟩ := exists_probeLogSchwartz_row_norm_envelope K S P
  obtain ⟨B, hB⟩ := sum_comp_probeSixthOrbit_le K S
    (probeLogSpatialSupport K S P) (isCompact_probeLogSpatialSupport K S P)
  refine ⟨Cball, hCball, B, ?_⟩
  intro t X Y hX hY
  let d : sLocalMultiplicativeGroup K S :=
    (t : sLocalMultiplicativeGroup K S) * sLocalNormSection K S ⟨X * Y, mul_pos hX hY⟩
  let M₀ := probeGeometricFrequencyFinset K S P d
  let M := M₀.filter (fun m => (sIntegerElementNorm K S m).val ≤ Cball * (X * Y))
  have hshape (m : NZ) (hm : m ∈ M) :
      sLocalNonzeroIntegerDiagonal K S m / d ∈ probeLogSpatialSupport K S P :=
    (mem_probeGeometricFrequencyFinset K S P d m).mp (Finset.mem_filter.mp hm).1
  refine ⟨M, ?_, ?_, hB d M hshape⟩
  · intro q hq
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hq
    exact (Finset.mem_filter.mp hm).2
  · intro ξ m hm
    by_cases hm₀ : m ∈ M₀
    · have hlarge : Cball * (X * Y) < (sIntegerElementNorm K S m).val := by
        by_contra h
        exact hm (Finset.mem_filter.mpr ⟨hm₀, le_of_not_gt h⟩)
      rw [(hnorm t X Y hX hY m hlarge).2]
      simp
    · have hout : probeColumnBasePoint K S m t X Y hX hY ∉
          probeLogSpatialSupport K S P := by
        intro hx
        exact hm₀ ((mem_probeGeometricFrequencyFinset K S P d m).mpr hx)
      rw [probeLogSchwartz_eq_zero_of_not_mem K S P _ hout]
      simp

/-- The separated spectral integrand with an ARBITRARY row coefficient `Θ`,
summed over a finite row set. -/
def lcSpectral (P : ProbeData K S) (t : sLocalNormOneGroup K S) (X Y : ℝ)
    (hX : 0 < X) (hY : 0 < Y) (M : Finset NZ) (Θ : NZ → ℂ) (ξ : ℝ) : ℂ :=
  ∑ m ∈ M, (𝓕 (probeLogSchwartz K S P (probeColumnBasePoint K S m t X Y hX hY))) ξ *
    actualAdditiveGramAmplitude K S P (fun _ => 1)
      P.denominator.toSmoothAnnularTest Y (2 * Real.pi * ξ) m.val * Θ m

/-- Cauchy--Schwarz for the separated rows with an arbitrary coefficient `Θ`.
The Fourier constant is chosen after `N` only. -/
theorem lc_exists_marked_finite_cauchy (P : ProbeData K S) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (t : sLocalNormOneGroup K S) (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y)
        (M : Finset NZ) (Θ : NZ → ℂ) (ξ : ℝ),
      (1 + |ξ|) ^ N * ‖lcSpectral K S P t X Y hX hY M Θ ξ‖ ≤
      C * Real.sqrt (∑ m ∈ M,
        ‖actualAdditiveGramAmplitude K S P (fun _ => 1)
          P.denominator.toSmoothAnnularTest Y (2 * Real.pi * ξ) m.val‖ ^ 2) *
        Real.sqrt (∑ m ∈ M, ‖Θ m‖ ^ 2) := by
  obtain ⟨C, hC, hFourier⟩ := exists_probeLogFourier_uniform_rapid_decay K S P N
  refine ⟨C, hC, ?_⟩
  intro t X Y hX hY M Θ ξ
  let F : NZ → ℂ := fun m =>
    (𝓕 (probeLogSchwartz K S P (probeColumnBasePoint K S m t X Y hX hY))) ξ
  let A : NZ → ℂ := fun m =>
    actualAdditiveGramAmplitude K S P (fun _ => 1)
      P.denominator.toSmoothAnnularTest Y (2 * Real.pi * ξ) m.val
  let a : NZ → ℝ := fun m => ‖A m‖
  let b : NZ → ℝ := fun m => ‖Θ m‖
  let w : ℝ := (1 + |ξ|) ^ N
  have hw : 0 ≤ w := pow_nonneg (by positivity) _
  have hrow (m : NZ) : w * ‖F m * A m * Θ m‖ ≤ C * (a m * b m) := by
    have hab : 0 ≤ a m * b m := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc
      w * ‖F m * A m * Θ m‖ = (w * ‖F m‖) * (a m * b m) := by
        simp only [norm_mul, a, b]
        ring
      _ ≤ C * (a m * b m) := mul_le_mul_of_nonneg_right (hFourier _ ξ) hab
  change w * ‖∑ m ∈ M, F m * A m * Θ m‖ ≤
    C * Real.sqrt (∑ m ∈ M, a m ^ 2) * Real.sqrt (∑ m ∈ M, b m ^ 2)
  calc
    w * ‖∑ m ∈ M, F m * A m * Θ m‖ ≤ w * (∑ m ∈ M, ‖F m * A m * Θ m‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hw
    _ = ∑ m ∈ M, w * ‖F m * A m * Θ m‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ m ∈ M, C * (a m * b m) := Finset.sum_le_sum (fun m _ => hrow m)
    _ = C * ∑ m ∈ M, a m * b m := (Finset.mul_sum _ _ _).symm
    _ ≤ C * (Real.sqrt (∑ m ∈ M, a m ^ 2) * Real.sqrt (∑ m ∈ M, b m ^ 2)) :=
      mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt M a b) hC
    _ = C * Real.sqrt (∑ m ∈ M, a m ^ 2) * Real.sqrt (∑ m ∈ M, b m ^ 2) := by ring

/-- The finite combination of the original integrands, with common `X, Y`, is
the separated spectral integral of the COMBINED theta coefficient.  All
interchanges are justified by the core finite support and integrability. -/
theorem lc_sum_mul_probeIntegrand_eq (P : ProbeData K S) (ψ : HeckeCharacter K)
    {ι : Type} (s : Finset ι) (a : ι → ℂ) (Qf : ι → Finset (ExteriorPrime K S))
    (Zf : ι → ℝ) (Θ : NZ → ℂ)
    (hΘ : ∀ m : NZ, Θ m = ∑ i ∈ s, a i *
      completedThetaSum K S P.arithmetic (thetaPeriod K S P ψ) m.val
        (primeSetIdeal K S ∅) (Qf i) logGaussianProfile (Zf i))
    (t : sLocalNormOneGroup K S) (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y) (M : Finset NZ)
    (hM : ∀ (ξ : ℝ) (m : NZ), m ∉ M →
      (𝓕 (probeLogSchwartz K S P (probeColumnBasePoint K S m t X Y hX hY))) ξ = 0) :
    ∑ i ∈ s, a i * probeIntegrand K S P ψ (Qf i) X Y (Zf i) t =
      (((X * Y) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∫ ξ : ℝ, lcSpectral K S P t X Y hX hY M Θ ξ := by
  have hrow (i : ι) (ξ : ℝ) :
      (∑' m : NZ, probeAmplitudeSpectralRow K S P ψ (Qf i) t X Y (Zf i) hX hY m ξ) =
        ∑ m ∈ M, probeAmplitudeSpectralRow K S P ψ (Qf i) t X Y (Zf i) hX hY m ξ :=
    tsum_eq_sum (fun m hm => by simp only [probeAmplitudeSpectralRow, hM ξ m hm, zero_mul])
  have hint (i : ι) : Integrable (fun ξ : ℝ =>
      a i * ∑' m : NZ, probeAmplitudeSpectralRow K S P ψ (Qf i) t X Y (Zf i) hX hY m ξ) :=
    (integrable_tsum_probeAmplitudeSpectralRow K S P ψ (Qf i) t X Y (Zf i) hX hY).const_mul
      (a i)
  have hfun : (fun ξ : ℝ => ∑ i ∈ s,
      a i * ∑' m : NZ, probeAmplitudeSpectralRow K S P ψ (Qf i) t X Y (Zf i) hX hY m ξ) =
      fun ξ : ℝ => lcSpectral K S P t X Y hX hY M Θ ξ := by
    funext ξ
    simp only [hrow]
    simp only [lcSpectral, hΘ, probeAmplitudeSpectralRow, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun i _ => ?_))
    ring
  calc ∑ i ∈ s, a i * probeIntegrand K S P ψ (Qf i) X Y (Zf i) t
      = ∑ i ∈ s, (((X * Y) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ∫ ξ : ℝ,
          a i * ∑' m : NZ, probeAmplitudeSpectralRow K S P ψ (Qf i) t X Y (Zf i) hX hY m ξ := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [probeIntegrand_eq_integral_tsum_amplitude K S P ψ (Qf i) t X Y (Zf i) hX hY,
          integral_const_mul]
        ring
    _ = (((X * Y) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ∑ i ∈ s, ∫ ξ : ℝ,
          a i * ∑' m : NZ, probeAmplitudeSpectralRow K S P ψ (Qf i) t X Y (Zf i) hX hY m ξ :=
        (Finset.mul_sum _ _ _).symm
    _ = (((X * Y) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ∫ ξ : ℝ, ∑ i ∈ s,
          a i * ∑' m : NZ, probeAmplitudeSpectralRow K S P ψ (Qf i) t X Y (Zf i) hX hY m ξ := by
        rw [integral_finsetSum s (fun i _ => hint i)]
    _ = (((X * Y) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∫ ξ : ℝ, lcSpectral K S P t X Y hX hY M Θ ξ := by
        rw [hfun]

/-- A finite set of orbits inside the norm box sums below the boxed series.
The box is finite, so the series is a genuine finite sum. -/
theorem lc_sum_le_tsum_orbit_box (Mi : Finset OQ) (R : ℝ) (f : OQ → ℝ)
    (hf : ∀ q, 0 ≤ f q)
    (hMi : ∀ q ∈ Mi, (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val ≤ R) :
    ∑ q ∈ Mi, f q ≤ ∑' u : OQ,
      if (sIntegerOrbitNorm K S (sixthPowerUnits K S) u).val ≤ R then f u else 0 := by
  letI : (sixthPowerUnits K S).FiniteIndex :=
    sUnit_power_range_finiteIndex K S 6 (by decide)
  have hfin : Set.Finite
      {u : OQ | (sIntegerOrbitNorm K S (sixthPowerUnits K S) u).val ≤ R} := by
    have h : Finite (BoundedSIntegerOrbits K S (sixthPowerUnits K S) R) := inferInstance
    exact Set.finite_coe_iff.mp h
  have hsum : Summable (fun u : OQ =>
      if (sIntegerOrbitNorm K S (sixthPowerUnits K S) u).val ≤ R then f u else 0) := by
    apply summable_of_ne_finset_zero (s := hfin.toFinset)
    intro u hu
    have hu' : ¬ (sIntegerOrbitNorm K S (sixthPowerUnits K S) u).val ≤ R := by
      intro h
      exact hu (hfin.mem_toFinset.mpr h)
    exact ite_eq_right hu'
  calc ∑ q ∈ Mi, f q
      = ∑ q ∈ Mi,
          (if (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val ≤ R then f q else 0) :=
        Finset.sum_congr rfl (fun q hq => (ite_eq_left (hMi q hq)).symm)
    _ ≤ _ := hsum.sum_le_tsum Mi (fun u _ => by
        by_cases h : (sIntegerOrbitNorm K S (sixthPowerUnits K S) u).val ≤ R <;>
          simp [h, hf u])

/-- The Gram definitions' amplitude is literally the core c = 1 orbit amplitude. -/
theorem lc_gram_orbitAmplitude_eq (P : ProbeData K S) (W : SmoothAnnularTest)
    (Y ν : ℝ) (q : OQ) :
    HeckeSkeleton.Gram.orbitAmplitude K S P W Y ν q =
      actualAdditiveGramOrbitAmplitude K S P (fun _ => 1) W Y ν q := by
  have h := actualAdditiveGramOrbitAmplitude_mk K S P (fun _ => 1) W Y ν q.out
  rw [Quotient.out_eq] at h
  rw [h]
  simp only [HeckeSkeleton.Gram.orbitAmplitude, HeckeSkeleton.Gram.amplitude,
    HeckeSkeleton.Gram.gramTerm, actualAdditiveGramAmplitude, actualAdditiveGramTerm,
    additiveGramCentralNormalization, one_mul]

/-- Completed theta sums only see the original sixth-power-unit orbit. -/
theorem lc_completedThetaSum_eq_of_orbit (D : ThetaArithmeticData K S)
    (θ : HeckeCharacter K) (r : ExteriorIdeal K S) (Q : Finset (ExteriorPrime K S))
    (V : ℝ → ℂ) (X : ℝ) (a b : NZ)
    (h : probeSixthOrbit K S a = probeSixthOrbit K S b) :
    completedThetaSum K S D θ a.val r Q V X = completedThetaSum K S D θ b.val r Q V X := by
  have hab : MulAction.orbitRel (sIntegerUnitSubgroup K S (sixthPowerUnits K S)) NZ a b :=
    Quotient.exact h
  obtain ⟨γ, hγ⟩ := (sIntegerOrbitRelation_iff K S (sixthPowerUnits K S) a b).mp hab
  have he : (S.unitEquivUnitsInteger K γ.val).val * b.val = a.val := Subtype.ext hγ
  rw [← he]
  exact completedThetaSum_mul_sixthPowerUnits K S D θ γ b.val r Q V X

theorem lc_rpow_neg_half_mul_sqrt {x : ℝ} (hx : 0 < x) :
    x ^ (-(1 / 2 : ℝ)) * Real.sqrt x = 1 := by
  rw [Real.rpow_neg hx.le, Real.sqrt_eq_rpow, inv_mul_cancel₀]
  exact (Real.rpow_pos_of_pos hx _).ne'

theorem lc_sqrt_le_self {y : ℝ} (hy : 1 ≤ y) : Real.sqrt y ≤ y := by
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]

/-- The marked physical Cauchy bound.  `Cball` precedes the Gram exponent `JG`,
and the constant `K₀` precedes all moving data.  For every finite combination
of physical probes with common `X, Y`, whose combined theta coefficient is `Θ`,
the combination is bounded by the square roots of a Gram row-energy budget
(with polynomial growth in the Mellin frequency) and of the theta energy over
the SAME orbit box `Cball * X * Y`, normalized by `X * Y`. -/
theorem lc_marked_physical_bound (P : ProbeData K S) (ψ : HeckeCharacter K) :
    ∃ Cball : ℝ, 0 < Cball ∧ ∀ JG : ℕ, ∃ K₀ : ℝ, 0 ≤ K₀ ∧
      ∀ (X Y : ℝ), 0 < X → 0 < Y →
      ∀ {ι : Type} (s : Finset ι) (a : ι → ℂ) (Qf : ι → Finset (ExteriorPrime K S))
        (Zf : ι → ℝ), (∀ i ∈ s, 0 < Zf i) →
      ∀ Θ : NZ → ℂ, (∀ m : NZ, Θ m = ∑ i ∈ s, a i *
          completedThetaSum K S P.arithmetic (thetaPeriod K S P ψ) m.val
            (primeSetIdeal K S ∅) (Qf i) logGaussianProfile (Zf i)) →
      ∀ EG ET : ℝ, 0 ≤ EG → 0 ≤ ET →
        (∀ ν : ℝ, HeckeSkeleton.Gram.rowEnergy K S P P.denominator.toSmoothAnnularTest
            Cball (X * Y) Y ν ≤ EG * (1 + |ν|) ^ JG) →
        (∑' u : OQ, if (sIntegerOrbitNorm K S (sixthPowerUnits K S) u).val ≤ Cball * (X * Y)
            then ‖Θ u.out‖ ^ 2 else 0) ≤ ET * (X * Y) →
        ‖∑ i ∈ s, a i * physicalProbe K S P ψ (Qf i) X Y (Zf i)‖ ≤
          K₀ * (Real.sqrt EG * Real.sqrt ET) := by
  obtain ⟨Cball, hCball, B, hsupp⟩ := lc_exists_fourier_support K S P
  refine ⟨Cball, hCball, fun JG => ?_⟩
  obtain ⟨CF, hCF, hcauchy⟩ := lc_exists_marked_finite_cauchy K S P (JG + 2)
  letI : (sixthPowerUnits K S).FiniteIndex :=
    sUnit_power_range_finiteIndex K S 6 (by decide)
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hint2 : Integrable (fun ξ : ℝ => (1 + ‖ξ‖) ^ (-(2 : ℝ))) := by
    apply integrable_one_add_norm
    norm_num [Module.finrank_self]
  set I₂ : ℝ := ∫ ξ : ℝ, (1 + ‖ξ‖) ^ (-(2 : ℝ)) with hI₂def
  have hI₂ : 0 ≤ I₂ := integral_nonneg (fun ξ => Real.rpow_nonneg (by positivity) _)
  set vol : ℝ :=
    (sUnitHaarMeasure K S).real (sUnitFundamentalDomain K S (sixthPowerUnits K S))
    with hvol_def
  have hvol : 0 ≤ vol := measureReal_nonneg
  refine ⟨CF * (B : ℝ) * 8 ^ JG * I₂ * vol, by positivity, ?_⟩
  intro X Y hX hY ι s a Qf Zf hZf Θ hΘ EG ET hEG hET hgramE hthetaE
  have hXY : 0 < X * Y := mul_pos hX hY
  -- the combined theta coefficient only sees original sixth-unit orbits
  have hΘinv : ∀ m : NZ, Θ (probeSixthOrbit K S m).out = Θ m := by
    intro m
    rw [hΘ, hΘ]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [lc_completedThetaSum_eq_of_orbit K S _ _ _ _ _ _ _ _
      (Quotient.out_eq (probeSixthOrbit K S m))]
  -- pointwise bound at every norm-one point
  have hpt : ∀ t : sLocalNormOneGroup K S,
      ‖∑ i ∈ s, a i * probeIntegrand K S P ψ (Qf i) X Y (Zf i) t‖ ≤
        CF * (B : ℝ) * 8 ^ JG * I₂ * (Real.sqrt EG * Real.sqrt ET) := by
    intro t
    obtain ⟨M, hMnorm, hMzero, hMfib⟩ := hsupp t X Y hX hY
    rw [lc_sum_mul_probeIntegrand_eq K S P ψ s a Qf Zf Θ hΘ t X Y hX hY M hMzero]
    set D : ℝ := CF * (Real.sqrt ((B : ℝ) * EG) * Real.sqrt ((B : ℝ) * (ET * (X * Y)))) *
      8 ^ JG with hD
    have hFbound : ∀ ξ : ℝ,
        ‖lcSpectral K S P t X Y hX hY M Θ ξ‖ ≤ D * (1 + ‖ξ‖) ^ (-(2 : ℝ)) := by
      intro ξ
      have hc := hcauchy t X Y hX hY M Θ ξ
      -- Gram energy on the same box
      have hEA : (∑ m ∈ M, ‖actualAdditiveGramAmplitude K S P (fun _ => 1)
          P.denominator.toSmoothAnnularTest Y (2 * Real.pi * ξ) m.val‖ ^ 2) ≤
          (B : ℝ) * (EG * (1 + |2 * Real.pi * ξ|) ^ JG) := by
        have h1 := hMfib (fun q => ‖actualAdditiveGramOrbitAmplitude K S P (fun _ => 1)
            P.denominator.toSmoothAnnularTest Y (2 * Real.pi * ξ) q‖ ^ 2)
          (fun q => sq_nonneg _)
        have h2 := lc_sum_le_tsum_orbit_box K S (M.image (probeSixthOrbit K S))
          (Cball * (X * Y))
          (fun q => ‖actualAdditiveGramOrbitAmplitude K S P (fun _ => 1)
            P.denominator.toSmoothAnnularTest Y (2 * Real.pi * ξ) q‖ ^ 2)
          (fun q => sq_nonneg _) hMnorm
        have hrowE : HeckeSkeleton.Gram.rowEnergy K S P P.denominator.toSmoothAnnularTest
            Cball (X * Y) Y (2 * Real.pi * ξ) =
            ∑' u : OQ, if (sIntegerOrbitNorm K S (sixthPowerUnits K S) u).val ≤
                Cball * (X * Y) then
              ‖actualAdditiveGramOrbitAmplitude K S P (fun _ => 1)
                P.denominator.toSmoothAnnularTest Y (2 * Real.pi * ξ) u‖ ^ 2 else 0 := by
          simp only [HeckeSkeleton.Gram.rowEnergy, lc_gram_orbitAmplitude_eq]
        calc _ ≤ _ := h1
          _ ≤ (B : ℝ) * HeckeSkeleton.Gram.rowEnergy K S P P.denominator.toSmoothAnnularTest
                Cball (X * Y) Y (2 * Real.pi * ξ) :=
              mul_le_mul_of_nonneg_left (h2.trans hrowE.ge) hB0
          _ ≤ _ := mul_le_mul_of_nonneg_left (hgramE (2 * Real.pi * ξ)) hB0
      -- theta energy on the same box
      have hET' : (∑ m ∈ M, ‖Θ m‖ ^ 2) ≤ (B : ℝ) * (ET * (X * Y)) := by
        have h1 := hMfib (fun q => ‖Θ q.out‖ ^ 2) (fun q => sq_nonneg _)
        have h2 := lc_sum_le_tsum_orbit_box K S (M.image (probeSixthOrbit K S))
          (Cball * (X * Y)) (fun q => ‖Θ q.out‖ ^ 2) (fun q => sq_nonneg _) hMnorm
        calc (∑ m ∈ M, ‖Θ m‖ ^ 2) = ∑ m ∈ M, ‖Θ (probeSixthOrbit K S m).out‖ ^ 2 :=
              Finset.sum_congr rfl (fun m _ => by rw [hΘinv m])
          _ ≤ _ := h1
          _ ≤ (B : ℝ) * (∑' u : OQ,
                if (sIntegerOrbitNorm K S (sixthPowerUnits K S) u).val ≤ Cball * (X * Y)
                then ‖Θ u.out‖ ^ 2 else 0) := mul_le_mul_of_nonneg_left h2 hB0
          _ ≤ _ := mul_le_mul_of_nonneg_left hthetaE hB0
      have hy1 : 1 ≤ (1 + |2 * Real.pi * ξ|) ^ JG :=
        one_le_pow₀ (by linarith [abs_nonneg (2 * Real.pi * ξ)])
      have hsq : Real.sqrt ((1 + |2 * Real.pi * ξ|) ^ JG) ≤ 8 ^ JG * (1 + |ξ|) ^ JG := by
        have h8 : 1 + |2 * Real.pi * ξ| ≤ 8 * (1 + |ξ|) := by
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
          nlinarith [Real.pi_le_four, abs_nonneg ξ]
        calc Real.sqrt ((1 + |2 * Real.pi * ξ|) ^ JG) ≤ (1 + |2 * Real.pi * ξ|) ^ JG :=
              lc_sqrt_le_self hy1
          _ ≤ (8 * (1 + |ξ|)) ^ JG :=
              pow_le_pow_left₀ (by positivity) h8 JG
          _ = 8 ^ JG * (1 + |ξ|) ^ JG := mul_pow _ _ _
      have hA : Real.sqrt (∑ m ∈ M, ‖actualAdditiveGramAmplitude K S P (fun _ => 1)
          P.denominator.toSmoothAnnularTest Y (2 * Real.pi * ξ) m.val‖ ^ 2) ≤
          Real.sqrt ((B : ℝ) * EG) * (8 ^ JG * (1 + |ξ|) ^ JG) := by
        calc _ ≤ Real.sqrt ((B : ℝ) * (EG * (1 + |2 * Real.pi * ξ|) ^ JG)) :=
              Real.sqrt_le_sqrt hEA
          _ = Real.sqrt ((B : ℝ) * EG) * Real.sqrt ((1 + |2 * Real.pi * ξ|) ^ JG) := by
              rw [← mul_assoc, Real.sqrt_mul (mul_nonneg hB0 hEG)]
          _ ≤ _ := mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
      have hT : Real.sqrt (∑ m ∈ M, ‖Θ m‖ ^ 2) ≤ Real.sqrt ((B : ℝ) * (ET * (X * Y))) :=
        Real.sqrt_le_sqrt hET'
      have hmain : (1 + |ξ|) ^ (JG + 2) * ‖lcSpectral K S P t X Y hX hY M Θ ξ‖ ≤
          D * (1 + |ξ|) ^ JG := by
        calc _ ≤ _ := hc
          _ ≤ CF * (Real.sqrt ((B : ℝ) * EG) * (8 ^ JG * (1 + |ξ|) ^ JG)) *
                Real.sqrt ((B : ℝ) * (ET * (X * Y))) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hA hCF) hT (Real.sqrt_nonneg _)
                (by positivity)
          _ = D * (1 + |ξ|) ^ JG := by rw [hD]; ring
      have hpos : 0 < (1 + |ξ|) ^ JG := by positivity
      have hdiv : ‖lcSpectral K S P t X Y hX hY M Θ ξ‖ ≤ D / (1 + |ξ|) ^ 2 := by
        rw [le_div_iff₀ (show (0 : ℝ) < (1 + |ξ|) ^ 2 by positivity)]
        have h' : (1 + |ξ|) ^ JG * ((1 + |ξ|) ^ 2 * ‖lcSpectral K S P t X Y hX hY M Θ ξ‖) ≤
            (1 + |ξ|) ^ JG * D := by
          calc (1 + |ξ|) ^ JG * ((1 + |ξ|) ^ 2 * ‖lcSpectral K S P t X Y hX hY M Θ ξ‖)
              = (1 + |ξ|) ^ (JG + 2) * ‖lcSpectral K S P t X Y hX hY M Θ ξ‖ := by ring
            _ ≤ D * (1 + |ξ|) ^ JG := hmain
            _ = (1 + |ξ|) ^ JG * D := by ring
        have h'' := le_of_mul_le_mul_left h' hpos
        exact (mul_comm _ _).trans_le h''
      calc ‖lcSpectral K S P t X Y hX hY M Θ ξ‖ ≤ D / (1 + |ξ|) ^ 2 := hdiv
        _ = D * (1 + ‖ξ‖) ^ (-(2 : ℝ)) := by
          rw [Real.norm_eq_abs, Real.rpow_neg (show (0 : ℝ) ≤ 1 + |ξ| by positivity),
            Real.rpow_two, div_eq_mul_inv]
    have hintF : ‖∫ ξ : ℝ, lcSpectral K S P t X Y hX hY M Θ ξ‖ ≤ D * I₂ := by
      rw [hI₂def, ← integral_const_mul]
      exact norm_integral_le_of_norm_le (hint2.const_mul D)
        (Filter.Eventually.of_forall hFbound)
    have h1 : (X * Y) ^ (-(1 / 2 : ℝ)) * Real.sqrt (X * Y) = 1 :=
      lc_rpow_neg_half_mul_sqrt hXY
    have h2 : Real.sqrt (B : ℝ) * Real.sqrt (B : ℝ) = (B : ℝ) := Real.mul_self_sqrt hB0
    calc ‖(((X * Y) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∫ ξ : ℝ, lcSpectral K S P t X Y hX hY M Θ ξ‖
        = (X * Y) ^ (-(1 / 2 : ℝ)) * ‖∫ ξ : ℝ, lcSpectral K S P t X Y hX hY M Θ ξ‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hXY.le _)]
      _ ≤ (X * Y) ^ (-(1 / 2 : ℝ)) * (D * I₂) :=
          mul_le_mul_of_nonneg_left hintF (Real.rpow_nonneg hXY.le _)
      _ = CF * (B : ℝ) * 8 ^ JG * I₂ * (Real.sqrt EG * Real.sqrt ET) := by
          rw [hD, Real.sqrt_mul hB0 EG, Real.sqrt_mul hB0 (ET * (X * Y)),
            Real.sqrt_mul hET (X * Y)]
          linear_combination
            (CF * Real.sqrt EG * Real.sqrt ET * 8 ^ JG * I₂ *
              (Real.sqrt (B : ℝ) * Real.sqrt (B : ℝ))) * h1 +
            (CF * Real.sqrt EG * Real.sqrt ET * 8 ^ JG * I₂) * h2
  -- integrate over the fundamental domain
  have hint : ∀ i ∈ s, IntegrableOn (probeIntegrand K S P ψ (Qf i) X Y (Zf i))
      (sUnitFundamentalDomain K S (sixthPowerUnits K S)) (sUnitHaarMeasure K S) :=
    fun i hi => (actual_probeIntegralInput K S P ψ).integral (Qf i) X Y (Zf i) hX hY (hZf i hi)
  have heq : (∫ t in sUnitFundamentalDomain K S (sixthPowerUnits K S),
      ∑ i ∈ s, a i * probeIntegrand K S P ψ (Qf i) X Y (Zf i) t ∂(sUnitHaarMeasure K S)) =
      ∑ i ∈ s, a i * physicalProbe K S P ψ (Qf i) X Y (Zf i) := by
    rw [integral_finsetSum s (fun i hi => Integrable.const_mul (hint i hi) (a i))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_const_mul]
    rfl
  rw [← heq]
  calc _ ≤ (CF * (B : ℝ) * 8 ^ JG * I₂ * (Real.sqrt EG * Real.sqrt ET)) * vol :=
        norm_setIntegral_le_of_norm_le_const
          (sUnitHaarCovolume_lt_top K S (sixthPowerUnits K S)) (fun t _ => hpt t)
    _ = CF * (B : ℝ) * 8 ^ JG * I₂ * vol * (Real.sqrt EG * Real.sqrt ET) := by ring

end HeckeSkeleton.LowCauchy
