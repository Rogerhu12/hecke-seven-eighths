import Expansion.PhysicalAmplitudeIntegral
import HeckeGeneral.Analysis.TInputFixedBinTransfer

/-!
# The original contour measure on the common physical parameter space

The amplitude construction uses three real coordinates indexed by `Fin 3`.
The original compensated contour uses the nested product `ℝ × ℝ × ℝ`.
This file identifies their measures and restricted integrals exactly, including
the contour normalization. Fubini is used only with absolute integrability of
the unchanged original kernel.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators Topology

namespace Expansion.Project

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global

/-- The three original Mellin heights, with their order preserved. -/
def physicalHeightEquiv : (ℝ × ℝ × ℝ) ≃ᵐ (Fin 3 → ℝ) where
  toFun t := ![t.1, t.2.1, t.2.2]
  invFun p := (p 0, p 1, p 2)
  left_inv t := by rcases t with ⟨s, w, z⟩; rfl
  right_inv p := by ext j; fin_cases j <;> rfl
  measurable_toFun := by
    change Measurable (fun t : ℝ × ℝ × ℝ => ![t.1, t.2.1, t.2.2])
    apply measurable_pi_iff.mpr
    intro j
    fin_cases j
    · exact measurable_fst
    · exact measurable_fst.comp measurable_snd
    · exact measurable_snd.comp measurable_snd
  measurable_invFun := by
    change Measurable (fun p : Fin 3 → ℝ => (p 0, p 1, p 2))
    exact (measurable_pi_apply 0).prodMk
      ((measurable_pi_apply 1).prodMk (measurable_pi_apply 2))

/-- Product Lebesgue measure in the actual three physical coordinates. -/
def physicalHeightVolume : Measure (Fin 3 → ℝ) :=
  Measure.map physicalHeightEquiv rowHeightVolume

theorem physicalHeightEquiv_preimage_box (T : ℝ) (hT : 0 ≤ T) :
    physicalHeightEquiv ⁻¹' {p : Fin 3 → ℝ | ‖p‖ ≤ T} = rowRetainedHeightBox T := by
  ext t
  simp [pi_norm_le_iff_of_nonneg hT, physicalHeightEquiv,
    rowRetainedHeightBox, Fin.forall_fin_succ, abs_le, Prod.le_def,
    and_assoc, and_left_comm, and_comm]

/-- Restriction to the physical box commutes with the coordinate change. -/
theorem physicalHeightVolume_restrict_box (T : ℝ) (hT : 0 ≤ T) :
    physicalHeightVolume.restrict {p : Fin 3 → ℝ | ‖p‖ ≤ T} =
      Measure.map physicalHeightEquiv (rowHeightVolume.restrict (rowRetainedHeightBox T)) := by
  rw [physicalHeightVolume, physicalHeightEquiv.restrict_map,
    physicalHeightEquiv_preimage_box T hT]

theorem integral_physicalHeight_box (T : ℝ) (hT : 0 ≤ T)
    (f : (Fin 3 → ℝ) → ℂ) :
    (∫ p in {p : Fin 3 → ℝ | ‖p‖ ≤ T}, f p ∂physicalHeightVolume) =
      ∫ t in rowRetainedHeightBox T, f (physicalHeightEquiv t) ∂rowHeightVolume := by
  rw [physicalHeightVolume_restrict_box T hT, integral_map_equiv]

theorem integrableOn_physicalHeight_box_iff (T : ℝ) (hT : 0 ≤ T)
    (f : (Fin 3 → ℝ) → ℂ) :
    IntegrableOn f {p : Fin 3 → ℝ | ‖p‖ ≤ T} physicalHeightVolume ↔
      IntegrableOn (fun t => f (physicalHeightEquiv t))
        (rowRetainedHeightBox T) rowHeightVolume := by
  unfold IntegrableOn
  rw [physicalHeightVolume_restrict_box T hT]
  exact integrable_map_equiv physicalHeightEquiv f

/-- Absolute integrability justifies the two original Fubini steps. -/
theorem integral_rowRetainedHeightBox (T : ℝ) (f : (ℝ × ℝ × ℝ) → ℂ)
    (hf : IntegrableOn f (rowRetainedHeightBox T) rowHeightVolume) :
    (∫ t in rowRetainedHeightBox T, f t ∂rowHeightVolume) =
      ∫ ts in Icc (-T) T, ∫ tw in Icc (-T) T, ∫ tz in Icc (-T) T,
        f (ts, tw, tz) := by
  let ν : Measure ℝ := volume.restrict (Icc (-T) T)
  have hf' : Integrable f (ν.prod (ν.prod ν)) := by
    simpa only [ν, IntegrableOn, rowRetainedHeightBox, rowHeightVolume,
      ← Measure.prod_restrict] using hf
  calc
    _ = ∫ ts in Icc (-T) T,
        ∫ p in Icc (-T) T ×ˢ Icc (-T) T, f (ts, p)
          ∂((volume : Measure ℝ).prod volume) := setIntegral_prod f hf
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf'.prod_right_ae] with ts hts
      have hts' : IntegrableOn (fun p : ℝ × ℝ => f (ts, p))
          (Icc (-T) T ×ˢ Icc (-T) T) ((volume : Measure ℝ).prod volume) := by
        simpa only [ν, IntegrableOn, ← Measure.prod_restrict] using hts
      exact setIntegral_prod (fun p : ℝ × ℝ => f (ts, p)) hts'

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : S, BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : S) → Measure (p.val.adicCompletion K))
variable [∀ p : S, (μ p).IsAddHaarMeasure]

/-- The original compensated kernel, in the coordinates used by every slot. -/
def physicalContourKernel (P : ProbeData K S) (ψ : HeckeCharacter K)
    (E : RowEulerData K S P) (g : PrimeWindowGeometry) (Γ : Finset (HeckeCharacter K))
    (Z σ ν zLine : ℝ) (u : FrequencyRow K S) (p : Fin 3 → ℝ) : ℂ :=
  (2 * (Real.pi : ℂ)) ^ (-(3 : ℤ)) *
    rowVerticalKernel K S μ P ψ E g Γ u Z σ ν zLine (physicalHeightEquiv.symm p)

theorem physicalContourKernel_integrable (P : ProbeData K S) (ψ : HeckeCharacter K)
    (E : RowEulerData K S P) (g : PrimeWindowGeometry) (Γ : Finset (HeckeCharacter K))
    (Z T σ ν zLine : ℝ) (hT : 0 ≤ T) (u : FrequencyRow K S)
    (hu : IntegrableOn (rowVerticalKernel K S μ P ψ E g Γ u Z σ ν zLine)
      (rowRetainedHeightBox T) rowHeightVolume) :
    IntegrableOn (physicalContourKernel K S μ P ψ E g Γ Z σ ν zLine u)
      {p : Fin 3 → ℝ | ‖p‖ ≤ T} physicalHeightVolume := by
  apply (integrableOn_physicalHeight_box_iff T hT _).mpr
  simpa only [IntegrableOn, physicalContourKernel, MeasurableEquiv.symm_apply_apply] using
    hu.const_mul ((2 * (Real.pi : ℂ)) ^ (-(3 : ℤ)))

/-- The exact row contour, with its original kernel and normalization. -/
theorem rowContourBox_eq_physicalHeight_integral (P : ProbeData K S) (ψ : HeckeCharacter K)
    (E : RowEulerData K S P) (g : PrimeWindowGeometry) (Γ : Finset (HeckeCharacter K))
    (Z T σ ν zLine : ℝ) (hT : 0 ≤ T) (u : FrequencyRow K S)
    (hu : IntegrableOn (rowVerticalKernel K S μ P ψ E g Γ u Z σ ν zLine)
      (rowRetainedHeightBox T) rowHeightVolume) :
    rowContourBox K S μ P ψ E g Γ u Z T σ ν zLine =
      ∫ p in {p : Fin 3 → ℝ | ‖p‖ ≤ T},
        physicalContourKernel K S μ P ψ E g Γ Z σ ν zLine u p ∂physicalHeightVolume := by
  rw [integral_physicalHeight_box T hT]
  simp only [physicalContourKernel, MeasurableEquiv.symm_apply_apply]
  rw [integral_const_mul, integral_rowRetainedHeightBox T _ hu]
  rfl

/-- The complete fixed arithmetic row set has the same physical integral. -/
theorem sum_rowContourBox_eq_physicalHeight_integral
    (P : ProbeData K S) (ψ : HeckeCharacter K) (E : RowEulerData K S P)
    (g : PrimeWindowGeometry) (Γ : Finset (HeckeCharacter K))
    (Z T σ ν zLine : ℝ) (hT : 0 ≤ T) (rows : Finset (FrequencyRow K S))
    (hrows : ∀ u ∈ rows,
      IntegrableOn (rowVerticalKernel K S μ P ψ E g Γ u Z σ ν zLine)
        (rowRetainedHeightBox T) rowHeightVolume) :
    (∑ u ∈ rows, rowContourBox K S μ P ψ E g Γ u Z T σ ν zLine) =
      ∫ p in {p : Fin 3 → ℝ | ‖p‖ ≤ T},
        ∑ u ∈ rows, physicalContourKernel K S μ P ψ E g Γ Z σ ν zLine u p
          ∂physicalHeightVolume := by
  rw [integral_finsetSum rows (fun u hu =>
    physicalContourKernel_integrable K S μ P ψ E g Γ Z T σ ν zLine hT u (hrows u hu))]
  exact Finset.sum_congr rfl (fun u hu =>
    rowContourBox_eq_physicalHeight_integral K S μ P ψ E g Γ Z T σ ν zLine hT u
      (hrows u hu))

end Expansion.Project

#print axioms Expansion.Project.integral_rowRetainedHeightBox
#print axioms Expansion.Project.rowContourBox_eq_physicalHeight_integral
#print axioms Expansion.Project.sum_rowContourBox_eq_physicalHeight_integral
