import ActualGramDualOrbitalScale
import HeckeGeneral.Analysis.SUnitTotalNormFourierBounds

/-!
UNCOMPILED source candidate. The columns are the actual supplied generators,
scaled by the genuine S-local norm section of Y inverse. Their archimedean
trace coordinates and finite coordinates together have norm q_I/Y. Thus
the actual dilated dual profile is the existing total-norm joint kernel at
these columns, including both finite norm factors. No normalized-generator
or profile-identification hypothesis is supplied.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualGramJointKernelDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
open HeckeGeneral.ThetaSkeleton.Global
open ActualProbeGaussFourierDraft ActualProbePairNormDraft ActualAdditiveGramDraft
open ActualGramDualScaleDraft
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

local notation "SS" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "G" => sLocalMultiplicativeGroup K SS
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "M" => mixedEmbedding.mixedSpace K
local notation "Z" => SFiniteLocalGroup K SS
local notation "Γ" => sixthPowerUnits K SS
local notation "O" => SIntegerOrbits K SS Γ

def additiveGramNormalizedColumn (D : ThetaArithmeticData K SS)
    (I : ExteriorIdeal K SS) (Y : ℝ) (hY : 0 < Y) : G :=
  sLocalNormSection K SS ⟨Y⁻¹, inv_pos.mpr hY⟩ *
    sLocalNonzeroIntegerDiagonal K SS (probeGenerator K SS D I)

theorem additiveGramNormalizedColumn_norm (D : ThetaArithmeticData K SS)
    (I : ExteriorIdeal K SS) (Y : ℝ) (hY : 0 < Y) :
    sLocalProductNorm K SS (additiveGramNormalizedColumn K S D I Y hY) =
      exteriorNorm K SS I / Y := by
  rw [additiveGramNormalizedColumn, sLocalProductNorm_mul, sLocalProductNorm_section]
  change Y⁻¹ * (sIntegerElementNorm K SS (probeGenerator K SS D I)).val = _
  rw [probeGenerator_norm_eq_exteriorNorm, div_eq_mul_inv, mul_comm]

def additiveGramColumnArch (D : ThetaArithmeticData K SS)
    (I : ExteriorIdeal K SS) (Y : ℝ) (hY : 0 < Y) : traceArchRegular K :=
  ⟨(traceToMixed K).symm ((additiveGramNormalizedColumn K S D I Y hY).1 : M),
    traceArchRegular_unit K (additiveGramNormalizedColumn K S D I Y hY).1⟩

def additiveGramColumnFinite (D : ThetaArithmeticData K SS)
    (I : ExteriorIdeal K SS) (Y : ℝ) (hY : 0 < Y) : Z :=
  (additiveGramNormalizedColumn K S D I Y hY).2

theorem additiveGramColumn_totalNorm (D : ThetaArithmeticData K SS)
    (I : ExteriorIdeal K SS) (Y : ℝ) (hY : 0 < Y) :
    traceArchProductNorm K (additiveGramColumnArch K S D I Y hY).val *
        sFiniteProductNorm K SS (additiveGramColumnFinite K S D I Y hY) =
      exteriorNorm K SS I / Y := by
  have h := sLocalProductNorm_eq_traceArchProductNorm K SS
    (additiveGramNormalizedColumn K S D I Y hY)
  change sLocalProductNorm K SS (additiveGramNormalizedColumn K S D I Y hY) =
    traceArchProductNorm K (additiveGramColumnArch K S D I Y hY).val *
      sFiniteProductNorm K SS (additiveGramColumnFinite K S D I Y hY) at h
  exact h.symm.trans (additiveGramNormalizedColumn_norm K S D I Y hY)

/-- The actual total Mellin phase on the two literal normalized columns. -/
theorem additiveGramColumn_mellinPhase (D : ThetaArithmeticData K SS)
    (I J : ExteriorIdeal K SS) (Y ν : ℝ) (hY : 0 < Y) :
    sUnitMellinPhase K SS ν
        (additiveGramColumnFinite K S D I Y hY)
        (additiveGramColumnFinite K S D J Y hY)
        ((additiveGramColumnArch K S D I Y hY).val,
          (additiveGramColumnArch K S D J Y hY).val) =
      traceRealMovingPhase ν
        (Real.log (exteriorNorm K SS I / Y) -
          Real.log (exteriorNorm K SS J / Y)) := by
  unfold sUnitMellinPhase
  rw [additiveGramColumn_totalNorm, additiveGramColumn_totalNorm]

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]

/-- The existing joint kernel evaluated on actual columns, with the finite
fibre correction in its parameter, is exactly the real orbital profile. -/
theorem additiveGramColumn_jointKernel (D : ThetaArithmeticData K SS)
    (I J : ExteriorIdeal K SS) (Y : ℝ) (hY : 0 < Y)
    (φ : SchwartzMap V ℂ) (ψ : ((v : SS) → v.val.adicCompletion K) → ℂ)
    (R : {r : ℝ // 0 < r}) :
    traceJointOrbitalKernel K SS φ ψ
        (sUnitTotalNormRadius K SS
          (additiveGramColumnFinite K S D I Y hY)
          (additiveGramColumnFinite K S D J Y hY) R)
        ((additiveGramColumnArch K S D I Y hY).val,
          (additiveGramColumnArch K S D J Y hY).val) =
      sUnitOrbitalProfile K SS
        (sLocalTensorTestFunction K SS (traceSchwartzFourier K φ) ψ)
        ⟨R.val / ((exteriorNorm K SS I / Y) * (exteriorNorm K SS J / Y)),
          div_pos R.property (mul_pos
            (div_pos (exteriorNorm_pos_of_probeGenerator K SS D I) hY)
            (div_pos (exteriorNorm_pos_of_probeGenerator K SS D J) hY))⟩ := by
  rw [traceJointOrbitalKernel_totalNormRadius]
  congr 1
  apply Subtype.ext
  simp only [additiveGramColumn_totalNorm]

/-- Actual first-Poisson profile after j=gen(C)*k, identified with the
total-norm two-column kernel for every original sixth-unit sector. -/
theorem additiveGram_dilated_dual_profile_eq_jointKernel (P : ProbeData K SS)
    (I J C : ExteriorIdeal K SS) (Q Y : ℝ) (hQ : 0 < Q) (hY : 0 < Y)
    (q : O) (φ : SchwartzMap V ℂ)
    (ψ : ((v : SS) → v.val.adicCompletion K) → ℂ) :
    sUnitOrbitalProfile K SS
        (sLocalTensorTestFunction K SS (traceSchwartzFourier K φ) ψ)
        ⟨(additiveGramPairDualRadius K S P I J ⟨Q⁻¹, inv_pos.mpr hQ⟩).val *
            (sIntegerOrbitNorm K SS Γ
              (sIntegerOrbitDilation K SS Γ (probeGenerator K SS P.arithmetic C) q)).val,
          mul_pos (additiveGramPairDualRadius K S P I J ⟨Q⁻¹, inv_pos.mpr hQ⟩).property
            (sIntegerOrbitNorm K SS Γ
              (sIntegerOrbitDilation K SS Γ (probeGenerator K SS P.arithmetic C) q)).property⟩ =
      traceJointOrbitalKernel K SS φ ψ
        (sUnitTotalNormRadius K SS
          (additiveGramColumnFinite K S P.arithmetic I Y hY)
          (additiveGramColumnFinite K S P.arithmetic J Y hY)
          (additiveGramRegroupedJointRadius K S P C Q Y hQ hY q))
        ((additiveGramColumnArch K S P.arithmetic I Y hY).val,
          (additiveGramColumnArch K S P.arithmetic J Y hY).val) :=
  (additiveGram_dilated_dual_profile_eq K S P I J C Q Y hQ hY q φ ψ).trans
    (additiveGramColumn_jointKernel K S P.arithmetic I J Y hY φ ψ
      (additiveGramRegroupedJointRadius K S P C Q Y hQ hY q)).symm

end HeckeGeneral.ThetaSkeleton.Physical.ActualGramJointKernelDraft
