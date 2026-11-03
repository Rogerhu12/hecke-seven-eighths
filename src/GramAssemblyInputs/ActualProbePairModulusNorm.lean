import ActualProbePairPeriodicFourier
import HeckeGeneral.Analysis.GlobalThetaData

/-!
SOURCE CANDIDATE / not compiled. The actual modulus in the first Poisson
identity has norm q_I*q_J. This is proved from generator_span, contraction
of exterior ideals, and the existing residue-cardinality/product-norm
identity; generator_norm is not added as an AllowedGeneratorInput premise.
The dual scale therefore is literally Q/(q_I*q_J).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualProbePairNormDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton.Global
open ActualProbeGaussFourierDraft ActualProbePairFourierDraft
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Norm of the actual single generator. No generator normalization field
is needed: its principal ideal and the exterior support already imply it. -/
theorem probeGenerator_norm_eq_exteriorNorm (D : ThetaArithmeticData K S)
    (I : ExteriorIdeal K S) :
    (sIntegerElementNorm K S (probeGenerator K S D I)).val = exteriorNorm K S I := by
  rw [← natCard_sIntegerPrincipalResidue_eq_productNorm K S
      (probeGenerator K S D I).val (probeGenerator K S D I).property,
    natCard_sIntegerPrincipalResidue K S (probeGenerator K S D I).val
      (probeGenerator K S D I).property, probeGenerator_contraction]
  rfl

/-- Contraction of the actual product generator is the product of the
original exterior ideals, including noncoprime pairs and the unit ideal. -/
theorem probePairGenerator_contraction (D : ThetaArithmeticData K S)
    (I J : ExteriorIdeal K S) :
    sIntegerModulusContraction K S (D.generator I * D.generator J) = I.val.val * J.val.val := by
  have houtside : ∀ p : HeightOneSpectrum (𝓞 K),
      p.asIdeal ∣ I.val.val * J.val.val → p ∉ S := by
    intro p hp
    rcases (p.prime.dvd_mul (a := I.val.val) (b := J.val.val)).mp hp with hI | hJ
    · exact I.property p hI
    · exact J.property p hJ
  unfold sIntegerModulusContraction
  rw [← Ideal.span_singleton_mul_span_singleton, D.generator_span, D.generator_span,
    ← Ideal.map_mul]
  exact under_map_coprime_sIntegerIdeal K S (I.val.val * J.val.val)
    (sexticIdeal_coprime_S K S (I.val.val * J.val.val) houtside)

/-- The complete pair modulus has the manuscript's exact q_I*q_J norm. -/
theorem probePairGenerator_norm_eq (D : ThetaArithmeticData K S)
    (I J : ExteriorIdeal K S) :
    (sIntegerElementNorm K S
      ⟨D.generator I * D.generator J,
        mul_ne_zero (D.generator_ne_zero I) (D.generator_ne_zero J)⟩).val =
      exteriorNorm K S I * exteriorNorm K S J := by
  rw [← natCard_sIntegerPrincipalResidue_eq_productNorm K S
      (D.generator I * D.generator J)
      (mul_ne_zero (D.generator_ne_zero I) (D.generator_ne_zero J)),
    natCard_sIntegerPrincipalResidue K S (D.generator I * D.generator J)
      (mul_ne_zero (D.generator_ne_zero I) (D.generator_ne_zero J)),
    probePairGenerator_contraction]
  simp only [map_mul, Nat.cast_mul, exteriorNorm]

theorem exteriorNorm_pos_of_probeGenerator (D : ThetaArithmeticData K S)
    (I : ExteriorIdeal K S) : 0 < exteriorNorm K S I := by
  rw [← probeGenerator_norm_eq_exteriorNorm K S D I]
  exact (sIntegerElementNorm K S (probeGenerator K S D I)).property

/-- This is the scalar dual radius in the real local orbital profile when
the original radius is Q^-1; it is valid before any row regrouping. -/
theorem probePair_dual_radius_eq (D : ThetaArithmeticData K S)
    (I J : ExteriorIdeal K S) (Q : ℝ) :
    (Q⁻¹ * (sIntegerElementNorm K S
      ⟨D.generator I * D.generator J,
        mul_ne_zero (D.generator_ne_zero I) (D.generator_ne_zero J)⟩).val)⁻¹ =
      Q / (exteriorNorm K S I * exteriorNorm K S J) := by
  rw [probePairGenerator_norm_eq, mul_inv_rev, inv_inv, div_eq_mul_inv, mul_comm]

/-- After the common factor and row regrouping, the exact argument has
the joint-annular shape R/(y1*y2), with R=Q*qC*qk/Y^2 and yi=qsi/Y.
Only the positive scale Y is cancelled; no asymptotic estimate is used. -/
theorem joint_annular_radius_identity (Q qC qk qI qJ Y : ℝ) (hY : 0 < Y)
    (hI : qI ≠ 0) (hJ : qJ ≠ 0) :
    (Q / (qI * qJ)) * (qC * qk) =
      (Q * qC * qk / Y ^ 2) / ((qI / Y) * (qJ / Y)) := by
  field_simp [ne_of_gt hY, hI, hJ] <;> ring

end HeckeGeneral.ThetaSkeleton.Physical.ActualProbePairNormDraft
