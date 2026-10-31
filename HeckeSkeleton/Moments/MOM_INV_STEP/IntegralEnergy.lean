module

public import HeckeSkeleton.Moments.MOM_INV_STEP.FixedTripleEnergy
public import HeckeSkeleton.Moments.MOM_INV_STEP.FourierSeparation
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic.FunProp

/-!
# Cauchy on the whole common Fourier integral

The finite reconstruction is estimated inside one common Fourier
integral. Holder's inequality then puts the entire positive frequency
measure inside the two square roots. Thus the spectral mass, just like
the distinct-triple mass, is paid once. The integrals have explicit
integrability proofs; a totalized Bochner integral is not used to assert
convergence.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOMInvStep.IntegralEnergy

open MeasureTheory NumberField IsDedekindDomain
open FixedTripleFibers FixedTripleEnergy
open HeckeSkeleton.Moments.MOM_INV_STEP.CommonKernel
open scoped BigOperators Classical NumberField FourierTransform

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]

/-- The integral Cauchy step, with the common weight inside both roots. -/
theorem weighted_integral_cauchy (μ : Measure Ω)
    (w L R : Ω → ℝ) (z : Ω → ℂ)
    (hw : ∀ t, 0 ≤ w t) (hL : ∀ t, 0 ≤ L t) (hR : ∀ t, 0 ≤ R t)
    (cw : Continuous w) (cL : Continuous L) (cR : Continuous R)
    (iL : Integrable (fun t => w t * L t) μ)
    (iR : Integrable (fun t => w t * R t) μ)
    (hz : ∀ t, ‖z t‖ ≤ w t * (Real.sqrt (L t) * Real.sqrt (R t))) :
    ‖∫ t, z t ∂μ‖ ≤ Real.sqrt (∫ t, w t * L t ∂μ) *
      Real.sqrt (∫ t, w t * R t ∂μ) := by
  let f := fun t => Real.sqrt (w t * L t)
  let g := fun t => Real.sqrt (w t * R t)
  have cf : Continuous f := Real.continuous_sqrt.comp (cw.mul cL)
  have cg : Continuous g := Real.continuous_sqrt.comp (cw.mul cR)
  have hfsq (t : Ω) : f t ^ 2 = w t * L t := Real.sq_sqrt (mul_nonneg (hw t) (hL t))
  have hgsq (t : Ω) : g t ^ 2 = w t * R t := Real.sq_sqrt (mul_nonneg (hw t) (hR t))
  have mf : MemLp f 2 μ := (memLp_two_iff_integrable_sq cf.aestronglyMeasurable).mpr
    (by simpa only [hfsq] using iL)
  have mg : MemLp g 2 μ := (memLp_two_iff_integrable_sq cg.aestronglyMeasurable).mpr
    (by simpa only [hgsq] using iR)
  have hfg (t : Ω) : f t * g t = w t * (Real.sqrt (L t) * Real.sqrt (R t)) := by
    dsimp only [f, g]
    rw [Real.sqrt_mul (hw t), Real.sqrt_mul (hw t)]
    calc
      _ = (Real.sqrt (w t)) ^ 2 * (Real.sqrt (L t) * Real.sqrt (R t)) := by ring
      _ = _ := by rw [Real.sq_sqrt (hw t)]
  have hi : ‖∫ t, z t ∂μ‖ ≤ ∫ t, f t * g t ∂μ := by
    apply norm_integral_le_of_norm_le (mf.integrable_mul mg)
    exact Filter.Eventually.of_forall fun t => by simpa only [Pi.mul_apply, hfg] using hz t
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun t => Real.sqrt_nonneg (w t * L t)))
    (Filter.Eventually.of_forall (fun t => Real.sqrt_nonneg (w t * R t)))
    (show MemLp f (ENNReal.ofReal (2 : ℝ)) μ by simpa using mf)
    (show MemLp g (ENNReal.ofReal (2 : ℝ)) μ by simpa using mg)
  have hfinal : (∫ t, f t * g t ∂μ) ≤ Real.sqrt (∫ t, w t * L t ∂μ) *
      Real.sqrt (∫ t, w t * R t ∂μ) := by
    simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hh
    change (∫ t, f t * g t ∂μ) ≤
      Real.sqrt (∫ t, f t ^ 2 ∂μ) * Real.sqrt (∫ t, g t ^ 2 ∂μ) at hh
    simpa only [hfsq, hgsq] using hh
  exact hi.trans hfinal

/-- The actual Fourier-separated finite column has a frequency-uniform
bound obtained directly from the norm-one phases. -/
theorem finite_column_bound {ι : Type*} (T : Finset ι) (a : ι → ℂ)
    (x : ι → ℝ) (ξ : ℝ) :
    ‖∑ i ∈ T, a i * columnPhase ξ (x i)‖ ≤ ∑ i ∈ T, ‖a i‖ := by
  apply (norm_sum_le _ _).trans_eq
  simp only [norm_mul, norm_columnPhase, mul_one]

theorem columnPhase_continuous (x : ℝ) : Continuous (fun ξ : ℝ => columnPhase ξ x) := by
  unfold columnPhase
  fun_prop

theorem finite_column_continuous {ι : Type*} (T : Finset ι) (a : ι → ℂ)
    (x : ι → ℝ) : Continuous (fun ξ : ℝ => ∑ i ∈ T, a i * columnPhase ξ (x i)) := by
  apply continuous_finsetSum
  intro i hi
  exact continuous_const.mul (columnPhase_continuous (x i))

theorem integrable_fourier_column_energy {ι : Type*} (T : Finset ι) (a : ι → ℂ)
    (x : ι → ℝ) (F : SchwartzMap LogPlane ℂ)
    (coordinate : LogPlane →L[ℝ] ℝ) :
    Integrable (fun ξ : LogPlane => ‖(𝓕 F) ξ‖ *
      ‖∑ i ∈ T, a i * columnPhase (coordinate ξ) (x i)‖ ^ 2) := by
  apply (𝓕 F).integrable.norm.mul_bdd
    (c := (∑ i ∈ T, ‖a i‖) ^ 2)
  · exact (((finite_column_continuous T a x).comp coordinate.continuous).norm.pow 2).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (finite_column_bound T a x (coordinate ξ)) 2

/-- A direct energy estimate for the genuinely separated common kernel.
The left side is the original finite bilinear expression, not a hypothesized
separated expression or a hypothesized energy bound. -/
theorem finite_bilinear_energy {ι κ : Type*} (T : Finset ι) (U : Finset κ)
    (F : SchwartzMap LogPlane ℂ) (x : ι → ℝ) (y : κ → ℝ)
    (a : ι → ℂ) (b : κ → ℂ) :
    ‖∑ i ∈ T, ∑ j ∈ U, a i * b j * F (logPoint (x i) (y j))‖ ≤
      Real.sqrt (∫ ξ : LogPlane, ‖(𝓕 F) ξ‖ *
        ‖∑ i ∈ T, a i * columnPhase ξ.fst (x i)‖ ^ 2) *
      Real.sqrt (∫ ξ : LogPlane, ‖(𝓕 F) ξ‖ *
        ‖∑ j ∈ U, b j * columnPhase ξ.snd (y j)‖ ^ 2) := by
  rw [finite_bilinear_separated]
  let fstL : LogPlane →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp logCoordinates.toContinuousLinearMap
  let sndL : LogPlane →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp logCoordinates.toContinuousLinearMap
  apply weighted_integral_cauchy volume (fun ξ => ‖(𝓕 F) ξ‖)
    (fun ξ => ‖∑ i ∈ T, a i * columnPhase ξ.fst (x i)‖ ^ 2)
    (fun ξ => ‖∑ j ∈ U, b j * columnPhase ξ.snd (y j)‖ ^ 2)
    _ (fun _ => norm_nonneg _) (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
  · exact (𝓕 F).continuous.norm
  · exact (((finite_column_continuous T a x).comp fstL.continuous).norm.pow 2)
  · exact (((finite_column_continuous U b y).comp sndL.continuous).norm.pow 2)
  · exact integrable_fourier_column_energy T a x F fstL
  · exact integrable_fourier_column_energy U b y F sndL
  · intro ξ
    simp only [norm_mul, Real.sqrt_sq (norm_nonneg _), mul_assoc, le_refl]

variable {K : Type*} [Field K] [NumberField K] {Sector : Type*}
variable {sectorTransport : Ideal (𝓞 K) → Ideal (𝓞 K) → (Sector ≃ Sector)}
variable {slotCap Jo Jn : ℕ}

/-- Pointwise smaller-child control can be integrated against one
common positive spectral measure. No duplicate spectral mass is paid. -/
theorem integral_packet_child_bound
    (P : ReconstructionPacket (K := K) (Sector := Sector) sectorTransport slotCap Jo Jn)
    (μ : Measure Ω) (b : Ω → ℂ) (F G : Ω → SecondChild K Sector → ℂ)
    (H : Ω → ℝ) (hH : ∀ ξ, 0 ≤ H ξ)
    (hF : ∀ ξ γ, γ ∈ P.triples → P.energy (F ξ) γ ≤ H ξ)
    (hG : ∀ ξ γ, γ ∈ P.triples → P.energy (G ξ) γ ≤ H ξ)
    (hmeas : AEStronglyMeasurable (fun ξ => b ξ * P.signedValue (F ξ) (G ξ)) μ)
    (hi : Integrable (fun ξ => ‖b ξ‖ * H ξ) μ) :
    Integrable (fun ξ => b ξ * P.signedValue (F ξ) (G ξ)) μ ∧
      ‖∫ ξ, b ξ * P.signedValue (F ξ) (G ξ) ∂μ‖ ≤
        P.tripleMass * ∫ ξ, ‖b ξ‖ * H ξ ∂μ := by
  have hb : ∀ ξ, ‖b ξ * P.signedValue (F ξ) (G ξ)‖ ≤
      P.tripleMass * (‖b ξ‖ * H ξ) := by
    intro ξ
    rw [norm_mul]
    have h := mul_le_mul_of_nonneg_left
      (P.signedValue_le (F ξ) (G ξ) (H ξ) (hH ξ) (hF ξ) (hG ξ)) (norm_nonneg (b ξ))
    convert h using 1 <;> ring
  refine ⟨(hi.const_mul P.tripleMass).mono' hmeas (Filter.Eventually.of_forall hb), ?_⟩
  calc
    _ ≤ ∫ ξ, P.tripleMass * (‖b ξ‖ * H ξ) ∂μ :=
      norm_integral_le_of_norm_le (hi.const_mul P.tripleMass) (Filter.Eventually.of_forall hb)
    _ = _ := integral_const_mul _ _

end HeckeSkeleton.Moments.MOMInvStep.IntegralEnergy

end
