import HeckeGeneral.Analysis.PhysicalProbeContours
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Integration of a FIXED finite set of actual physical rows. A proof of
the pointwise bound may use moving partitions; no such partition is
integrated. Explicit sequential integrability justifies exchanging the
fixed finite sum at each of the three line integrations.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : S, BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : S) → Measure (p.val.adicCompletion K))
variable [∀ p : S, (μ p).IsAddHaarMeasure]

/-- The actual compensated kernel on the three prescribed vertical lines. -/
def rowKernelOnLines (P : ProbeData K S) (ψ : HeckeCharacter K)
    (E : RowEulerData K S P) (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K S) (Z σ ν zLine ts tw tz : ℝ) : ℂ :=
  compensatedRowMellinKernel K S μ P ψ E g T u Z
    ((σ : ℂ) + (ts : ℂ) * Complex.I) ((ν : ℂ) + (tw : ℂ) * Complex.I)
    ((zLine : ℂ) + (tz : ℂ) * Complex.I)

variable (P : ProbeData K S) (ψ : HeckeCharacter K)
    (E : RowEulerData K S P) (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (R : Finset (FrequencyRow K S)) (Z H σ ν zLine : ℝ)

local notation "F" => rowKernelOnLines K S μ P ψ E g T
local notation "box" => Icc (-H) H

omit [∀ p : S, BorelSpace (p.val.adicCompletion K)] [∀ p : S, (μ p).IsAddHaarMeasure] in
/-- The volume and vertical-line normalization factors remain explicit.
Integrability is required only for slices whose outer parameters are in
the fixed box. No regularity of a moving partition is required. -/
theorem norm_fixedRowContourBox_sum_le (hH : 0 ≤ H) {B : ℝ}
    (hinner : ∀ u ∈ R, ∀ ts ∈ box, ∀ tw ∈ box,
      IntegrableOn (fun tz => F u Z σ ν zLine ts tw tz) box)
    (hmiddle : ∀ u ∈ R, ∀ ts ∈ box,
      IntegrableOn (fun tw => ∫ tz in box, F u Z σ ν zLine ts tw tz) box)
    (houter : ∀ u ∈ R,
      IntegrableOn (fun ts => ∫ tw in box, ∫ tz in box, F u Z σ ν zLine ts tw tz) box)
    (hpoint : ∀ ts ∈ box, ∀ tw ∈ box, ∀ tz ∈ box,
      ‖∑ u ∈ R, F u Z σ ν zLine ts tw tz‖ ≤ B) :
    ‖∑ u ∈ R, rowContourBox K S μ P ψ E g T u Z H σ ν zLine‖ ≤
      (2 * Real.pi) ^ (-(3 : ℤ)) * (2 * H) ^ 3 * B := by
  have hex :
      (∑ u ∈ R, ∫ ts in box, ∫ tw in box, ∫ tz in box, F u Z σ ν zLine ts tw tz) =
        ∫ ts in box, ∫ tw in box, ∫ tz in box, ∑ u ∈ R, F u Z σ ν zLine ts tw tz := by
    rw [← integral_finsetSum R houter]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with ts hts
    rw [← integral_finsetSum R (fun u hu => hmiddle u hu ts hts)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with tw htw
    rw [integral_finsetSum R (fun u hu => hinner u hu ts hts tw htw)]
  have heq :
      (∑ u ∈ R, rowContourBox K S μ P ψ E g T u Z H σ ν zLine) =
        (2 * (Real.pi : ℂ)) ^ (-(3 : ℤ)) *
          ∫ ts in box, ∫ tw in box, ∫ tz in box, ∑ u ∈ R, F u Z σ ν zLine ts tw tz := by
    simp only [rowContourBox, ← Finset.mul_sum]
    exact congrArg (fun z : ℂ => (2 * (Real.pi : ℂ)) ^ (-(3 : ℤ)) * z) hex
  have hfinite : volume box < ⊤ := isCompact_Icc.measure_lt_top
  have hvol : volume.real box = 2 * H := by
    rw [Real.volume_real_Icc_of_le (by linarith : -H ≤ H)]
    ring
  have htz : ∀ ts ∈ box, ∀ tw ∈ box,
      ‖∫ tz in box, ∑ u ∈ R, F u Z σ ν zLine ts tw tz‖ ≤ B * (2 * H) := by
    intro ts hts tw htw
    simpa only [hvol] using norm_setIntegral_le_of_norm_le_const hfinite (hpoint ts hts tw htw)
  have htw : ∀ ts ∈ box,
      ‖∫ tw in box, ∫ tz in box, ∑ u ∈ R, F u Z σ ν zLine ts tw tz‖ ≤
        (B * (2 * H)) * (2 * H) := by
    intro ts hts
    simpa only [hvol] using norm_setIntegral_le_of_norm_le_const hfinite (htz ts hts)
  have hts :
      ‖∫ ts in box, ∫ tw in box, ∫ tz in box, ∑ u ∈ R, F u Z σ ν zLine ts tw tz‖ ≤
        ((B * (2 * H)) * (2 * H)) * (2 * H) := by
    simpa only [hvol] using norm_setIntegral_le_of_norm_le_const hfinite htw
  have hnorm : ‖(2 * (Real.pi : ℂ)) ^ (-(3 : ℤ))‖ =
      (2 * Real.pi) ^ (-(3 : ℤ)) := by
    simp only [norm_zpow, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [heq, norm_mul]
  calc
    _ ≤ ‖(2 * (Real.pi : ℂ)) ^ (-(3 : ℤ))‖ * (((B * (2 * H)) * (2 * H)) * (2 * H)) :=
      mul_le_mul_of_nonneg_left hts (norm_nonneg _)
    _ = (2 * Real.pi) ^ (-(3 : ℤ)) * (2 * H) ^ 3 * B := by rw [hnorm]; ring

end HeckeGeneral.ThetaSkeleton.Physical
