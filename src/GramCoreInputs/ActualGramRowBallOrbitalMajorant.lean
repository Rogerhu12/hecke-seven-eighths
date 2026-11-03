import ActualGramCompactShapeMajorant
import HeckeGeneral.Analysis.SIntegerOrbitUnfolding
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
UNCOMPILED / native0. A genuine fixed compact shape for all positive row
radii bounded above. Zero is admitted in the ADDITIVE shape, while every
orbital integral still has strictly positive radius. The actual original
sixth-power subgroup and its unnormalized Haar covolume are retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "SF" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Af" => gramFiniteAdditiveSpace K S
local notation "G" => sLocalMultiplicativeGroup K SF
local notation "T" => sLocalNormOneGroup K SF
local notation "Γ" => sixthPowerUnits K SF

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]

local instance rowBall_sixthUnits_finiteIndex : Subgroup.FiniteIndex Γ :=
  sUnit_power_range_finiteIndex K SF 6 (by decide)

/-- Continuous additive extension of the positive section acting on the
norm-one group. At scalar zero only the archimedean coordinate becomes zero. -/
def rowBallShapeMap (p : ℝ × T) : V × Af :=
  (p.1 • (traceToMixed K).symm (((p.2 : G).1 : mixedEmbedding.mixedSpace K)),
    fun v => ((p.2 : G).2 v).val)

theorem continuous_rowBallShapeMap : Continuous (rowBallShapeMap K S) := by
  have ht : Continuous (fun p : ℝ × T => (p.2 : G)) :=
    continuous_subtype_val.comp continuous_snd
  have hi : Continuous (fun p : ℝ × T =>
      (traceToMixed K).symm (((p.2 : G).1 : mixedEmbedding.mixedSpace K))) :=
    (traceToMixed K).symm.continuous.comp
      (Units.continuous_val.comp (continuous_fst.comp ht))
  have hf : Continuous (fun p : ℝ × T => fun v : SF => ((p.2 : G).2 v).val) := by
    apply continuous_pi
    intro v
    exact Units.continuous_val.comp ((continuous_apply v).comp (continuous_snd.comp ht))
  exact (continuous_fst.smul hi).prodMk hf

/-- The shape is fixed before the row or positive radius is selected. -/
def rowBallCompactShape (B : ℝ) : Set (V × Af) :=
  rowBallShapeMap K S ''
    (Icc 0 (B ^ ((Module.finrank ℚ K : ℝ)⁻¹)) ×ˢ
      closure (sUnitFundamentalDomain K SF Γ))

theorem isCompact_rowBallCompactShape (B : ℝ) :
    IsCompact (rowBallCompactShape K S B) :=
  (isCompact_Icc.prod (isCompact_closure_sUnitFundamentalDomain K SF Γ)).image
    (continuous_rowBallShapeMap K S)

def rowBallArchTest (B : ℝ) : SchwartzMap V ℂ :=
  compactShapeArchTest K S (rowBallCompactShape K S B)
    (isCompact_rowBallCompactShape K S B)

def rowBallFiniteFamily (B : ℝ) (v : HeightOneSpectrum (𝓞 K)) :
    v.adicCompletion K → ℂ :=
  compactShapeFiniteFamily K S (rowBallCompactShape K S B)
    (isCompact_rowBallCompactShape K S B) v

theorem rowBallFiniteFamily_locallyConstant (B : ℝ)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) :
    IsLocallyConstant (rowBallFiniteFamily K S B v) :=
  compactShapeFiniteFamily_locallyConstant K S _ _ v hv

theorem rowBallFiniteFamily_compactSupport (B : ℝ)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) :
    HasCompactSupport (rowBallFiniteFamily K S B v) :=
  compactShapeFiniteFamily_compactSupport K S _ _ v hv

/-- Literal section coordinates; in particular finite coordinates are not
dilated or dropped. -/
theorem rowBall_slice_coordinates (B : ℝ) (r : {r : ℝ // 0 < r}) (t : T) :
    sLocalSchwartzSlice K SF (rowBallArchTest K S B)
      (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S B)) r t =
    rowBallArchTest K S B (rowBallShapeMap K S
      (r.val ^ ((Module.finrank ℚ K : ℝ)⁻¹), t)).1 *
      ∏ v : SF, rowBallFiniteFamily K S B v.val
        ((rowBallShapeMap K S (r.val ^ ((Module.finrank ℚ K : ℝ)⁻¹), t)).2 v) := by
  simp [sLocalSchwartzSlice, sLocalTensorTestFunction, sIntegerFiniteTestFunction,
    sLocalNormSection, rowBallShapeMap, realScaleMixedUnit_val,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc]

theorem rowBall_slice_eq_one_on_domain (B : ℝ) (r : {r : ℝ // 0 < r})
    (hr : r.val ≤ B) (t : T) (ht : t ∈ sUnitFundamentalDomain K SF Γ) :
    sLocalSchwartzSlice K SF (rowBallArchTest K S B)
      (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S B)) r t = 1 := by
  rw [rowBall_slice_coordinates]
  have hz : rowBallShapeMap K S (r.val ^ ((Module.finrank ℚ K : ℝ)⁻¹), t) ∈
      rowBallCompactShape K S B := by
    refine ⟨_, ⟨⟨Real.rpow_nonneg r.property.le _, ?_⟩, subset_closure ht⟩, rfl⟩
    exact Real.rpow_le_rpow r.property.le hr (inv_nonneg.mpr (Nat.cast_nonneg _))
  rcases compactShapeMajorant_spec K S (rowBallCompactShape K S B)
    (isCompact_rowBallCompactShape K S B) with ⟨_, _, _, _, _, _, _, hone⟩
  simpa only [rowBallArchTest, rowBallFiniteFamily, compactShapeFiniteFamily,
    gramFiniteExtension_at] using hone _ hz

theorem rowBall_tensor_nonnegative (B : ℝ) (x : G) :
    (sLocalTensorTestFunction K SF (rowBallArchTest K S B)
      (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S B)) x).im = 0 ∧
    0 ≤ (sLocalTensorTestFunction K SF (rowBallArchTest K S B)
      (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S B)) x).re := by
  rcases compactShapeMajorant_spec K S (rowBallCompactShape K S B)
    (isCompact_rowBallCompactShape K S B) with ⟨_, _, _, _, _, _, hpos, _⟩
  simpa only [sLocalTensorTestFunction, sIntegerFiniteTestFunction, rowBallArchTest,
    rowBallFiniteFamily, compactShapeFiniteFamily, gramFiniteExtension_at] using
    hpos ((traceToMixed K).symm (x.1 : mixedEmbedding.mixedSpace K), fun v => (x.2 v).val)

/-- A strictly positive actual constant, not a probability normalization. -/
theorem rowBall_covolume_pos : 0 < (sUnitHaarCovolume K SF Γ).toReal :=
  ENNReal.toReal_pos (sUnitHaarCovolume_ne_zero K SF Γ)
    (sUnitHaarCovolume_lt_top K SF Γ).ne

theorem rowBall_slice_integrable (B : ℝ) (r : {r : ℝ // 0 < r}) :
    Integrable (sLocalSchwartzSlice K SF (rowBallArchTest K S B)
      (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S B)) r)
      (sUnitHaarMeasure K SF) :=
  integrable_sLocalTensorTestFunction_orbit K SF Γ _ _
    (continuous_sIntegerFiniteTestFunction K S _
      (rowBallFiniteFamily_locallyConstant K S B))
    (hasCompactSupport_sIntegerFiniteTestFunction K S _
      (rowBallFiniteFamily_compactSupport K S B)) (sLocalNormSection K SF r)

/-- Reality and nonnegativity hold at every positive radius, including
outside the ball where no lower bound by the covolume is asserted. -/
theorem rowBall_orbitalProfile_real_nonnegative (B : ℝ) (r : {r : ℝ // 0 < r}) :
    (sUnitOrbitalProfile K SF
      (sLocalTensorTestFunction K SF (rowBallArchTest K S B)
        (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S B))) r).im = 0 ∧
    0 ≤ (sUnitOrbitalProfile K SF
      (sLocalTensorTestFunction K SF (rowBallArchTest K S B)
        (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S B))) r).re := by
  let F := sLocalSchwartzSlice K SF (rowBallArchTest K S B)
    (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S B)) r
  have hF : Integrable F (sUnitHaarMeasure K SF) := rowBall_slice_integrable K S B r
  have hp (t : T) : (F t).im = 0 ∧ 0 ≤ (F t).re :=
    rowBall_tensor_nonnegative K S B (sLocalNormSection K SF r * (t : G))
  change (∫ t, F t ∂sUnitHaarMeasure K SF).im = 0 ∧
    0 ≤ (∫ t, F t ∂sUnitHaarMeasure K SF).re
  have him : (∫ t, (F t).im ∂sUnitHaarMeasure K SF) =
      (∫ t, F t ∂sUnitHaarMeasure K SF).im := integral_im hF
  have hre : (∫ t, (F t).re ∂sUnitHaarMeasure K SF) =
      (∫ t, F t ∂sUnitHaarMeasure K SF).re := integral_re hF
  constructor
  · rw [← him]
    simp only [fun t => (hp t).1, integral_zero]
  · rw [← hre]
    exact integral_nonneg fun t => (hp t).2

/-- Every small positive radial profile dominates the retained covolume.
Integrability follows from the proved Schwartz orbit theorem. -/
theorem rowBall_orbitalProfile_lower (B : ℝ) (r : {r : ℝ // 0 < r})
    (hr : r.val ≤ B) :
    (sUnitHaarCovolume K SF Γ).toReal ≤
      (sUnitOrbitalProfile K SF
        (sLocalTensorTestFunction K SF (rowBallArchTest K S B)
          (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S B))) r).re := by
  let F : T → ℂ := fun t => sLocalSchwartzSlice K SF (rowBallArchTest K S B)
    (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S B)) r t
  have hF : Integrable F (sUnitHaarMeasure K SF) := rowBall_slice_integrable K S B r
  have hn : 0 ≤ᵐ[sUnitHaarMeasure K SF] (fun t => (F t).re) :=
    Filter.Eventually.of_forall fun t => (rowBall_tensor_nonnegative K S B
      (sLocalNormSection K SF r * (t : G))).2
  have hd : (∫ t in sUnitFundamentalDomain K SF Γ, (F t).re
      ∂sUnitHaarMeasure K SF) = (sUnitHaarCovolume K SF Γ).toReal := by
    calc
      _ = ∫ _ in sUnitFundamentalDomain K SF Γ, (1 : ℝ) ∂sUnitHaarMeasure K SF := by
        apply setIntegral_congr_fun (measurableSet_sUnitFundamentalDomain K SF Γ)
        intro t ht
        change (sLocalSchwartzSlice K SF _ _ r t).re = 1
        rw [rowBall_slice_eq_one_on_domain K S B r hr t ht]
        rfl
      _ = _ := by simp only [setIntegral_const, smul_eq_mul, mul_one,
          sUnitHaarCovolume, Measure.real]
  calc
    _ = ∫ t in sUnitFundamentalDomain K SF Γ, (F t).re ∂sUnitHaarMeasure K SF := hd.symm
    _ ≤ ∫ t, (F t).re ∂sUnitHaarMeasure K SF := setIntegral_le_integral hF.re hn
    _ = _ := integral_re hF

/-- The original whole sixth-power-unit sector inherits the lower bound at
the actual row norm. No unit sector is discarded or selected anew. -/
theorem rowBall_original_sector_lower (B : ℝ) (r : {r : ℝ // 0 < r})
    (a : NonzeroRingElements (Set.integer SF K))
    (ha : r.val * (sIntegerElementNorm K SF a).val ≤ B) :
    (sUnitHaarCovolume K SF Γ).toReal ≤
      (∫ t in sUnitFundamentalDomain K SF Γ, ∑' u : Γ,
        sLocalTensorTestFunction K SF (rowBallArchTest K S B)
          (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S B))
          ((sLocalNormSection K SF r * sLocalNonzeroIntegerDiagonal K SF a) *
            (sLocalDiagonal K SF (u : Set.unit SF K) * (t : G)))
        ∂sUnitHaarMeasure K SF).re := by
  rw [setIntegral_tsum_sIntegerOrbit_eq_profile K SF Γ _ _
    (continuous_sIntegerFiniteTestFunction K S _
      (rowBallFiniteFamily_locallyConstant K S B))
    (hasCompactSupport_sIntegerFiniteTestFunction K S _
      (rowBallFiniteFamily_compactSupport K S B))]
  exact rowBall_orbitalProfile_lower K S B _ ha

/-- Direct orbit-indexed form, with the same radius as the weighted orbital
series. All original unit sectors are already contained in this index. -/
theorem rowBall_orbit_profile_lower (B : ℝ) (r : {r : ℝ // 0 < r})
    (q : SIntegerOrbits K SF Γ)
    (hq : r.val * (sIntegerOrbitNorm K SF Γ q).val ≤ B) :
    (sUnitHaarCovolume K SF Γ).toReal ≤
      (sUnitOrbitalProfile K SF
        (sLocalTensorTestFunction K SF (rowBallArchTest K S B)
          (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S B)))
        ⟨r.val * (sIntegerOrbitNorm K SF Γ q).val,
          mul_pos r.property (sIntegerOrbitNorm K SF Γ q).property⟩).re :=
  rowBall_orbitalProfile_lower K S B _ hq

end HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
