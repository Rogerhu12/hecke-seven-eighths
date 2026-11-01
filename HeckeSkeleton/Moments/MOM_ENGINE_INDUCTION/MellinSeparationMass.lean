import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MellinProfileNormalization

/-!
# The exact mass of the common normalized Mellin kernel

Two extra original Euler derivatives pay the two one-dimensional L1
tails after the fixed window envelopes have been inserted.  Every
remaining parent profile contributes only its original prime-slot
factor.  The common measure has an explicit mass proportional to
`P^(2*(cap+2))`, independent of the number of arithmetic rows.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open MeasureTheory Set Filter
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open scoped Classical BigOperators Topology

private def mellinDecay (frequency : ℝ) : ℝ := (1 + |frequency|) ^ (-(2 : ℝ))

private theorem mellinDecay_nonneg (frequency : ℝ) : 0 ≤ mellinDecay frequency :=
  Real.rpow_nonneg (by positivity) _

private theorem continuous_mellinDecay : Continuous mellinDecay :=
  (continuous_const.add continuous_abs).rpow_const
    (fun t => Or.inl (ne_of_gt (by positivity : 0 < (1 : ℝ) + |t|)))

private theorem integrable_mellinDecay : Integrable mellinDecay :=
  integrable_one_add_abs_rpow_neg (e := 2) (by norm_num)

/-- A deterministic common envelope after both window normalizers and
the original slot-profile factor have been inserted. -/
def mellinPairEnvelope (cap J : ℕ) (P E : ℝ) (frequency : ℝ × ℝ) : ℝ :=
  (mellinSeparationConstant (J + 2) * E) ^ 2 * P ^ (cap + 2) *
    (mellinDecay frequency.1 * mellinDecay frequency.2)

theorem mellinPairEnvelope_nonneg (cap J : ℕ) {P E : ℝ} (hP : 0 ≤ P)
    (frequency : ℝ × ℝ) : 0 ≤ mellinPairEnvelope cap J P E frequency := by
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hP _))
    (mul_nonneg (mellinDecay_nonneg _) (mellinDecay_nonneg _))

theorem measurable_mellinPairEnvelope (cap J : ℕ) (P E : ℝ) :
    Measurable (mellinPairEnvelope cap J P E) :=
  (continuous_const.mul ((continuous_mellinDecay.comp continuous_fst).mul
    (continuous_mellinDecay.comp continuous_snd))).measurable

theorem integrable_mellinPairEnvelope (cap J : ℕ) (P E : ℝ) :
    Integrable (mellinPairEnvelope cap J P E) ((volume : Measure ℝ).prod volume) :=
  (integrable_mellinDecay.mul_prod integrable_mellinDecay).const_mul _

/-- The scalar is fixed before the parent profile budget and every row. -/
def mellinKernelMassConstant (J : ℕ) (E : ℝ) : ℝ :=
  ((mellinSeparationConstant (J + 2) * E) * ∫ frequency : ℝ, mellinDecay frequency) ^ 4

theorem mellinPairEnvelope_kernel_mass (cap J : ℕ) {P E : ℝ} (hP : 0 ≤ P) :
    (rowEnergyKernel ((volume : Measure ℝ).prod volume)
      (mellinPairEnvelope cap J P E)).real Set.univ =
        mellinKernelMassConstant J E * P ^ (2 * (cap + 2)) := by
  rw [rowEnergyKernel_mass _ (measurable_mellinPairEnvelope cap J P E)
    (mellinPairEnvelope_nonneg cap J hP)]
  change (∫ frequency : ℝ × ℝ,
    ((mellinSeparationConstant (J + 2) * E) ^ 2 * P ^ (cap + 2)) *
      (mellinDecay frequency.1 * mellinDecay frequency.2)
      ∂((volume : Measure ℝ).prod volume)) ^ 2 = _
  rw [integral_const_mul, integral_prod_mul]
  unfold mellinKernelMassConstant
  rw [Nat.mul_comm 2 (cap + 2), pow_mul]
  ring

private theorem mellinCoefficient_windowEnvelope_bound (V : SmoothAnnularTest)
    (J : ℕ) {P E : ℝ} (hE : 0 ≤ E)
    (hV : testSeminorm V.toFun (J + 2) 0 ≤ P) (frequency : ℝ) :
    ordinaryProfileEnvelope E J frequency * ‖annularMellinCoefficient V frequency‖ ≤
      (mellinSeparationConstant (J + 2) * E * P) * mellinDecay frequency := by
  have ht : 0 < 1 + |frequency| := by positivity
  have hpow : (1 + |frequency|) ^ J * (1 + |frequency|) ^ (-((J + 2 : ℕ) : ℝ)) =
      (1 + |frequency|) ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht]
    congr 1
    push_cast
    ring
  have hcoefficient := (annularMellinCoefficient_norm_le V (J + 2) frequency).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hV (mellinSeparationConstant_pos _).le)
      (Real.rpow_nonneg ht.le _))
  apply (mul_le_mul_of_nonneg_left hcoefficient
    (mul_nonneg hE (pow_nonneg ht.le _))).trans_eq
  unfold mellinDecay
  calc
    _ = (mellinSeparationConstant (J + 2) * E * P) *
      ((1 + |frequency|) ^ J * (1 + |frequency|) ^ (-((J + 2 : ℕ) : ℝ))) := by ring
    _ = _ := by rw [hpow]

/-- The row-dependent Mellin scalar is bounded by one common envelope.
No supremum of row sums, or measure depending on a row, is used. -/
theorem normalizedMellinPairCoefficient_bound (cap J slots : ℕ)
    (hslots : slots ≤ cap) {P E : ℝ} (hP : 1 ≤ P) (hE : 1 ≤ E)
    (V₁ V₂ : SmoothAnnularTest)
    (hV₁ : testSeminorm V₁.toFun (J + 2) 0 ≤ P)
    (hV₂ : testSeminorm V₂.toFun (J + 2) 0 ≤ P)
    (frequency : ℝ × ℝ) :
    ‖(mellinNormalizationAmplitude slots P E J frequency : ℂ) *
      mellinPairCoefficient V₁ V₂ frequency‖ ≤ mellinPairEnvelope cap J P E frequency := by
  have h₁ := mellinCoefficient_windowEnvelope_bound V₁ J (zero_le_one.trans hE) hV₁ frequency.1
  have h₂ := mellinCoefficient_windowEnvelope_bound V₂ J (zero_le_one.trans hE) hV₂ frequency.2
  have hEn (t : ℝ) : 0 ≤ ordinaryProfileEnvelope E J t :=
    zero_le_one.trans (one_le_ordinaryProfileEnvelope hE J t)
  have hC : 0 ≤ mellinSeparationConstant (J + 2) * E * P :=
    mul_nonneg (mul_nonneg (mellinSeparationConstant_pos _).le (zero_le_one.trans hE))
      (zero_le_one.trans hP)
  have hpair := mul_le_mul h₁ h₂
    (mul_nonneg (hEn frequency.2) (norm_nonneg _))
    (mul_nonneg hC (mellinDecay_nonneg _))
  have hcharge := mul_le_mul (pow_le_pow_right₀ hP hslots) hpair
    (mul_nonneg (mul_nonneg (hEn frequency.1) (norm_nonneg _))
      (mul_nonneg (hEn frequency.2) (norm_nonneg _)))
    (pow_nonneg (zero_le_one.trans hP) cap)
  rw [norm_mul, Complex.norm_of_nonneg (zero_le_one.trans
    (one_le_mellinNormalizationAmplitude slots hP hE J frequency)),
    mellinPairCoefficient, norm_mul]
  unfold mellinNormalizationAmplitude mellinPairEnvelope
  calc
    _ = P ^ slots *
      ((ordinaryProfileEnvelope E J frequency.1 * ‖annularMellinCoefficient V₁ frequency.1‖) *
        (ordinaryProfileEnvelope E J frequency.2 * ‖annularMellinCoefficient V₂ frequency.2‖)) := by ring
    _ ≤ P ^ cap *
      (((mellinSeparationConstant (J + 2) * E * P) * mellinDecay frequency.1) *
        ((mellinSeparationConstant (J + 2) * E * P) * mellinDecay frequency.2)) := hcharge
    _ = _ := by rw [pow_add]; ring

end HeckeSkeleton.Moments.EngineInduction
