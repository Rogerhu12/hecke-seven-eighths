import CubicSieve.OrbitKernel
import CubicSieve.ExteriorSieve
import HeckeGeneral.Analysis.SIntegerOrbitalSum
import HeckeGeneral.Arithmetic.SUnitFiniteGeneration

/-!
The full ideal cutoff embeds into the actual sixth-unit orbit space through
its chosen generators. A positive radial profile then majorizes every row
in the ball, and the sum retains all the other unit sectors. The Gaussian
profile lower bound is supplied separately from its pointwise contraction.
-/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.AnalyticSmoothing

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open CubicSieve.ExteriorKernel CubicSieve.OrbitRows CubicSieve.OrbitKernel
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

local instance gammaFiniteIndex : (Γ K S).FiniteIndex :=
  sUnit_power_range_finiteIndex K S 6 (by decide)

local notation "T₁" => sLocalNormOneGroup K S
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

def generatorOrbit (I : ExteriorIdeal K S) : Orbits K S := scalarOrbit K S D I 1

theorem generatorOrbit_injective : Function.Injective (generatorOrbit K S D) := by
  intro I J h
  have he := congrArg (orbitIdeal K S) h
  simpa only [generatorOrbit, orbitIdeal_scalarOrbit] using he

theorem generatorOrbit_norm (I : ExteriorIdeal K S) :
    (sIntegerOrbitNorm K S (Γ K S) (generatorOrbit K S D I)).val =
      exteriorNorm K S I := scalarOrbit_norm K S D I 1

theorem coefficient_generatorOrbit (I J : ExteriorIdeal K S) :
    coefficient K S D J (generatorOrbit K S D I) = positiveKernel K S D I J := by
  simp only [generatorOrbit, scalarOrbit, map_one, one_smul, coefficient_mk,
    positiveKernel, kernel, symbol, zpow_ofNat]

theorem coefficient_norm_le_one (J : ExteriorIdeal K S) (q : Orbits K S) :
    ‖coefficient K S D J q‖ ≤ 1 := by
  refine Quotient.inductionOn q (fun a => ?_)
  rw [coefficient_mk, norm_pow]
  apply pow_le_one₀ (norm_nonneg _) _
  exact norm_sIntegerSexticIdealEvaluation_le_one K S D.root6 D.primitive6 D.embedding
    J.val.val (nonZeroDivisors.coe_ne_zero J.val) J.property
    (fun p hp => D.away_six p (J.property p hp)) a.val

def orbitEnergy (T : Finset (ExteriorIdeal K S)) (z : ExteriorIdeal K S → ℂ)
    (q : Orbits K S) : ℝ := ‖∑ J ∈ T, coefficient K S D J q * z J‖ ^ 2

theorem orbitEnergy_bound (T : Finset (ExteriorIdeal K S)) (z : ExteriorIdeal K S → ℂ)
    (q : Orbits K S) : orbitEnergy K S D T z q ≤ (∑ J ∈ T, ‖z J‖) ^ 2 := by
  have hh : ‖∑ J ∈ T, coefficient K S D J q * z J‖ ≤ ∑ J ∈ T, ‖z J‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro J hJ
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (coefficient_norm_le_one K S D J q) (norm_nonneg (z J))
  exact pow_le_pow_left₀ (norm_nonneg _) hh 2

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]

def orbitRadius (M : ℝ) (hM : 0 < M) (q : Orbits K S) : {r : ℝ // 0 < r} :=
  ⟨M⁻¹ * (sIntegerOrbitNorm K S (Γ K S) q).val,
    mul_pos (inv_pos.mpr hM) (sIntegerOrbitNorm K S (Γ K S) q).property⟩

def smoothEnergy (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (M : ℝ) (hM : 0 < M) (T : Finset (ExteriorIdeal K S)) (z : ExteriorIdeal K S → ℂ) : ℝ :=
  ∑' q : Orbits K S,
    (sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
      (orbitRadius K S M hM q)).re * orbitEnergy K S D T z q

theorem smoothEnergy_summable (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (M : ℝ) (hM : 0 < M) (T : Finset (ExteriorIdeal K S)) (z : ExteriorIdeal K S → ℂ) :
    Summable (fun q : Orbits K S =>
      (sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
        (orbitRadius K S M hM q)).re * orbitEnergy K S D T z q) := by
  have hp := summable_norm_sIntegerOrbitalProfile K S (Γ K S) φ ψ hψ hψcs
    ⟨M⁻¹, inv_pos.mpr hM⟩
  apply (hp.mul_right ((∑ J ∈ T, ‖z J‖) ^ 2)).of_norm_bounded
  intro q
  have hE : 0 ≤ orbitEnergy K S D T z q := sq_nonneg _
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hE]
  apply mul_le_mul (Complex.abs_re_le_norm _) (orbitEnergy_bound K S D T z q)
    (sq_nonneg _) (norm_nonneg _)

theorem smooth_majorizes_cutoff (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (hP : ∀ r, 0 ≤ (sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) r).re)
    (c : ℝ) (hc : 0 < c)
    (hlower : ∀ r : {r : ℝ // 0 < r}, r.val ≤ 1 →
      c ≤ (sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) r).re)
    (M N : ℝ) (hM : 1 ≤ M) (T : Finset (ExteriorIdeal K S))
    (z : ExteriorIdeal K S → ℂ) :
    c * (∑ I ∈ ExteriorSieve.cutoff K S M,
      ‖∑ J ∈ T, positiveKernel K S D I J * z J‖ ^ 2) ≤
        smoothEnergy K S D φ ψ M (by linarith) T z := by
  have hM0 : 0 < M := by linarith
  let f : Orbits K S → ℝ := fun q =>
    (sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
      (orbitRadius K S M hM0 q)).re * orbitEnergy K S D T z q
  have hf0 : ∀ q, 0 ≤ f q := fun q => mul_nonneg (hP _) (sq_nonneg _)
  have hi (I : ExteriorIdeal K S) (hI : I ∈ ExteriorSieve.cutoff K S M) :
      c ≤ (sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
        (orbitRadius K S M hM0 (generatorOrbit K S D I))).re := by
    apply hlower
    change M⁻¹ * (sIntegerOrbitNorm K S (Γ K S) (generatorOrbit K S D I)).val ≤ 1
    rw [generatorOrbit_norm, inv_mul_eq_div]
    exact (div_le_one hM0).mpr ((ExteriorSieve.mem_cutoff K S M I).mp hI).2
  calc
    _ ≤ ∑ I ∈ ExteriorSieve.cutoff K S M, f (generatorOrbit K S D I) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro I hI
      have hh := mul_le_mul_of_nonneg_right (hi I hI)
        (sq_nonneg ‖∑ J ∈ T, positiveKernel K S D I J * z J‖)
      simpa only [f, orbitEnergy, coefficient_generatorOrbit] using hh
    _ = ∑ q ∈ (ExteriorSieve.cutoff K S M).image (generatorOrbit K S D), f q :=
      (Finset.sum_image (generatorOrbit_injective K S D).injOn).symm
    _ ≤ ∑' q, f q :=
      (smoothEnergy_summable K S D φ ψ hψ hψcs M hM0 T z).sum_le_tsum _
        (fun q hq => hf0 q)

/-- The full original operator follows from an estimate of the genuine all-sector
smooth sum. The profile lower bound must already have been proved. -/
theorem B_le_of_smoothEnergy_bound (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (hP : ∀ r, 0 ≤ (sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) r).re)
    (c : ℝ) (hc : 0 < c)
    (hlower : ∀ r : {r : ℝ // 0 < r}, r.val ≤ 1 →
      c ≤ (sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) r).re)
    (M N F : ℝ) (hM : 1 ≤ M) (hF : 0 ≤ F)
    (hb : ∀ z : ExteriorIdeal K S → ℂ,
      smoothEnergy K S D φ ψ M (by linarith) (ExteriorSieve.cutoff K S N) z ≤
        F * ∑ J ∈ ExteriorSieve.cutoff K S N, ‖z J‖ ^ 2) :
    ExteriorSieve.B K S D M N ≤ c⁻¹ * F := by
  apply (FiniteKernel.hasBound_iff_norm_sq_le _ _ _ _
    (mul_nonneg (inv_nonneg.mpr hc.le) hF)).mp
  intro z
  have hh := (smooth_majorizes_cutoff K S D φ ψ hψ hψcs hP c hc hlower M N hM
    (ExteriorSieve.cutoff K S N) z).trans (hb z)
  change (∑ I ∈ ExteriorSieve.cutoff K S M,
    ‖∑ J ∈ ExteriorSieve.cutoff K S N, positiveKernel K S D I J * z J‖ ^ 2) ≤ _
  dsimp only [FiniteKernel.energy]
  apply (mul_le_mul_iff_left₀ hc).mp
  convert hh using 1 <;> field_simp <;> ring

end CubicSieve.AnalyticSmoothing
