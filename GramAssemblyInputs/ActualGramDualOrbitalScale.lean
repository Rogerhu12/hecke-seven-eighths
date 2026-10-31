import ActualAdditiveGramPoissonAssembly
import ActualProbePairModulusNorm
import HeckeGeneral.Arithmetic.SIntegerOrbitDilation

/-!
UNCOMPILED / native 0. Identify the literal first-Poisson dual radius and
the radius after multiplication of the original nonzero orbit by gen(C).
The result has exactly R/(y1*y2), where yi=q_Ii/Y and R=Q*q_C*q_k/Y^2.
All norms are the actual exterior or original-subgroup orbit norms.
This file identifies the profile argument; it does not supply its bounds.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualGramDualScaleDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
open HeckeGeneral.ThetaSkeleton.Global
open ActualProbeGaussFourierDraft ActualProbePairNormDraft ActualAdditiveGramDraft
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

local notation "SS" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Γ" => sixthPowerUnits K SS
local notation "O" => SIntegerOrbits K SS Γ
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

theorem additiveGramPairDualRadius_inv_val (P : ProbeData K SS)
    (I J : ExteriorIdeal K SS) (Q : ℝ) (hQ : 0 < Q) :
    (additiveGramPairDualRadius K S P I J ⟨Q⁻¹, inv_pos.mpr hQ⟩).val =
      Q / (exteriorNorm K SS I * exteriorNorm K SS J) := by
  exact probePair_dual_radius_eq K SS P.arithmetic I J Q

/-- The actual joint scale after the common generator is removed from
the row. No relation between the chosen generators of product ideals is used. -/
def additiveGramRegroupedJointRadius (P : ProbeData K SS)
    (C : ExteriorIdeal K SS) (Q Y : ℝ) (hQ : 0 < Q) (hY : 0 < Y) (q : O) :
    {r : ℝ // 0 < r} :=
  ⟨Q * exteriorNorm K SS C * (sIntegerOrbitNorm K SS Γ q).val / Y ^ 2,
    div_pos (mul_pos (mul_pos hQ
      (exteriorNorm_pos_of_probeGenerator K SS P.arithmetic C))
      (sIntegerOrbitNorm K SS Γ q).property) (pow_pos hY 2)⟩

/-- Exact scalar identification of the radius of the actual dilated row.
It holds for every original subgroup sector, with the genuine finite S norm. -/
theorem additiveGram_dilated_dual_radius_eq (P : ProbeData K SS)
    (I J C : ExteriorIdeal K SS) (Q Y : ℝ) (hQ : 0 < Q) (hY : 0 < Y) (q : O) :
    (additiveGramPairDualRadius K S P I J ⟨Q⁻¹, inv_pos.mpr hQ⟩).val *
        (sIntegerOrbitNorm K SS Γ
          (sIntegerOrbitDilation K SS Γ (probeGenerator K SS P.arithmetic C) q)).val =
      (additiveGramRegroupedJointRadius K S P C Q Y hQ hY q).val /
        ((exteriorNorm K SS I / Y) * (exteriorNorm K SS J / Y)) := by
  rw [additiveGramPairDualRadius_inv_val, sIntegerOrbitNorm_dilation,
    probeGenerator_norm_eq_exteriorNorm]
  exact joint_annular_radius_identity Q (exteriorNorm K SS C)
    (sIntegerOrbitNorm K SS Γ q).val (exteriorNorm K SS I) (exteriorNorm K SS J) Y hY
    (ne_of_gt (exteriorNorm_pos_of_probeGenerator K SS P.arithmetic I))
    (ne_of_gt (exteriorNorm_pos_of_probeGenerator K SS P.arithmetic J))
  exact hQ

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]

/-- The literal dual Fourier orbital profile at the radius above. Only a
proved equality of positive arguments is used; no replacement kernel enters. -/
theorem additiveGram_dilated_dual_profile_eq (P : ProbeData K SS)
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
      sUnitOrbitalProfile K SS
        (sLocalTensorTestFunction K SS (traceSchwartzFourier K φ) ψ)
        ⟨(additiveGramRegroupedJointRadius K S P C Q Y hQ hY q).val /
            ((exteriorNorm K SS I / Y) * (exteriorNorm K SS J / Y)),
          div_pos (additiveGramRegroupedJointRadius K S P C Q Y hQ hY q).property
            (mul_pos
              (div_pos (exteriorNorm_pos_of_probeGenerator K SS P.arithmetic I) hY)
              (div_pos (exteriorNorm_pos_of_probeGenerator K SS P.arithmetic J) hY))⟩ := by
  congr 1
  exact Subtype.ext (additiveGram_dilated_dual_radius_eq K S P I J C Q Y hQ hY q)

end HeckeGeneral.ThetaSkeleton.Physical.ActualGramDualScaleDraft
