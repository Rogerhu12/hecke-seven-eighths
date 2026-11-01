import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalActualGaussNumerators
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalActiveDualTerminalWindows

/-!
# Sharp original numerator calibration for the same dual terminal

The pure dual zero uses the original central inverse square root and
gets its first-divisor density from equal-ideal counting. The tail buys
the same density with an explicit pre-pool norm exponent, which remains
in its cutoff degree. These are separate estimates on the same source.

An empty physical row carrier uses the unit counting divisor. Its
supported stage has zero fibre, without any false divisibility claim
about amplified residual columns.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}

namespace ActualGaussSource

variable {ι : Type*} (G : ActualGaussSource C ι)
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Both norm denominators are the actual source column norms. -/
theorem gram_numerator_eq (p : Seminorm ℂ V) (φ : V) (i j : ι) :
    p ((G.coefficient i * star (G.coefficient j)) • φ) =
      (‖G.coefficient i * (A.exteriorNorm (G.ideal i) : ℂ)‖ *
        ‖G.coefficient j * (A.exteriorNorm (G.ideal j) : ℂ)‖ * p φ) /
          (A.exteriorNorm (G.ideal i) * A.exteriorNorm (G.ideal j)) := by
  simp only [map_smul_eq_mul, norm_mul, norm_star, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (A.exteriorNorm_pos (G.ideal i)),
    abs_of_pos (A.exteriorNorm_pos (G.ideal j))]
  field_simp [(A.exteriorNorm_pos (G.ideal i)).ne',
    (A.exteriorNorm_pos (G.ideal j)).ne'] <;> ring

theorem gram_numerator_le (p : Seminorm ℂ V) (φ : V) (i j : ι)
    (hi : i ∈ G.columns) (hj : j ∈ G.columns)
    (Z lower power constant : ℝ) (hZ : 0 < Z) (hconstant : 0 ≤ constant)
    (hlower : ∀ i ∈ G.columns, G.coefficient i ≠ 0 →
      Z ^ lower ≤ A.exteriorNorm (G.ideal i))
    (hpair : G.coefficient i ≠ 0 → G.coefficient j ≠ 0 →
      ‖G.coefficient i * (A.exteriorNorm (G.ideal i) : ℂ)‖ *
        ‖G.coefficient j * (A.exteriorNorm (G.ideal j) : ℂ)‖ ≤ constant * Z ^ power) :
    p ((G.coefficient i * star (G.coefficient j)) • φ) ≤
      (constant * p φ) * Z ^ (power - 2 * lower) := by
  have hnonneg : 0 ≤ (constant * p φ) * Z ^ (power - 2 * lower) :=
    mul_nonneg (mul_nonneg hconstant (apply_nonneg _ _)) (Real.rpow_nonneg hZ.le _)
  by_cases hci : G.coefficient i = 0
  · simpa only [hci, zero_mul, zero_smul, map_zero] using hnonneg
  by_cases hcj : G.coefficient j = 0
  · simpa only [hcj, star_zero, mul_zero, zero_smul, map_zero] using hnonneg
  have hden : Z ^ (2 * lower) ≤
      A.exteriorNorm (G.ideal i) * A.exteriorNorm (G.ideal j) := by
    rw [show 2 * lower = lower + lower by ring, Real.rpow_add hZ]
    exact mul_le_mul (hlower i hi hci) (hlower j hj hcj)
      (Real.rpow_nonneg hZ.le _) (A.exteriorNorm_pos _).le
  rw [G.gram_numerator_eq p φ i j]
  calc
    _ ≤ (constant * Z ^ power * p φ) /
        (A.exteriorNorm (G.ideal i) * A.exteriorNorm (G.ideal j)) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hpair hci hcj) (apply_nonneg _ _))
        (mul_nonneg (A.exteriorNorm_pos _).le (A.exteriorNorm_pos _).le)
    _ ≤ (constant * Z ^ power * p φ) / Z ^ (2 * lower) :=
      div_le_div_of_nonneg_left
        (mul_nonneg (mul_nonneg hconstant (Real.rpow_nonneg hZ.le _)) (apply_nonneg _ _))
        (Real.rpow_pos_of_pos hZ _) hden
    _ = _ := by rw [Real.rpow_sub hZ]; ring

/-- The first inverse norm cancels before either lower window is
used. Only the actual second column's lower norm remains. -/
theorem gram_numerator_mul_norm_le (p : Seminorm ℂ V) (φ : V) (i j : ι)
    (hi : i ∈ G.columns) (hj : j ∈ G.columns)
    (Z lower power constant : ℝ) (hZ : 0 < Z) (hconstant : 0 ≤ constant)
    (hlower : ∀ i ∈ G.columns, G.coefficient i ≠ 0 →
      Z ^ lower ≤ A.exteriorNorm (G.ideal i))
    (hpair : G.coefficient i ≠ 0 → G.coefficient j ≠ 0 →
      ‖G.coefficient i * (A.exteriorNorm (G.ideal i) : ℂ)‖ *
        ‖G.coefficient j * (A.exteriorNorm (G.ideal j) : ℂ)‖ ≤ constant * Z ^ power) :
    p ((G.coefficient i * star (G.coefficient j)) • φ) * A.exteriorNorm (G.ideal i) ≤
      (constant * p φ) * Z ^ (power - lower) := by
  have hnonneg : 0 ≤ (constant * p φ) * Z ^ (power - lower) :=
    mul_nonneg (mul_nonneg hconstant (apply_nonneg _ _)) (Real.rpow_nonneg hZ.le _)
  by_cases hci : G.coefficient i = 0
  · simpa only [hci, zero_mul, zero_smul, map_zero] using hnonneg
  by_cases hcj : G.coefficient j = 0
  · simpa only [hcj, star_zero, mul_zero, zero_smul, map_zero, zero_mul] using hnonneg
  rw [G.gram_numerator_eq p φ i j]
  have hcancel :
      (‖G.coefficient i * (A.exteriorNorm (G.ideal i) : ℂ)‖ *
          ‖G.coefficient j * (A.exteriorNorm (G.ideal j) : ℂ)‖ * p φ) /
        (A.exteriorNorm (G.ideal i) * A.exteriorNorm (G.ideal j)) * A.exteriorNorm (G.ideal i) =
      (‖G.coefficient i * (A.exteriorNorm (G.ideal i) : ℂ)‖ *
          ‖G.coefficient j * (A.exteriorNorm (G.ideal j) : ℂ)‖ * p φ) /
        A.exteriorNorm (G.ideal j) := by
    field_simp [(A.exteriorNorm_pos (G.ideal i)).ne',
      (A.exteriorNorm_pos (G.ideal j)).ne'] <;> ring
  rw [hcancel]
  calc
    _ ≤ (constant * Z ^ power * p φ) / A.exteriorNorm (G.ideal j) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hpair hci hcj) (apply_nonneg _ _))
        (A.exteriorNorm_pos _).le
    _ ≤ (constant * Z ^ power * p φ) / Z ^ lower :=
      div_le_div_of_nonneg_left
        (mul_nonneg (mul_nonneg hconstant (Real.rpow_nonneg hZ.le _)) (apply_nonneg _ _))
        (Real.rpow_pos_of_pos hZ _) (hlower j hj hcj)
    _ = _ := by rw [Real.rpow_sub hZ]; ring

namespace OriginalNumerator

variable {G} {α : Type*} {columns : Finset α} {ideal : α → A.Exterior}
variable {coefficient : α → ℂ} {divisor : Ideal (𝓞 K)} {common : A.Exterior} {δ : ℝ}
/-- The actual divisor is used only when a genuine physical row
supplies the amplifier eligibility required for the post-pool gate. -/
def countingDivisor (_D : G.OriginalNumerator columns ideal coefficient divisor common δ) :
    Ideal (𝓞 K) := if G.rows.Nonempty then divisor else 1

variable (D : G.OriginalNumerator columns ideal coefficient divisor common δ)

theorem countingDivisor_ne_zero (hdivisor : divisor ≠ 0) : D.countingDivisor ≠ 0 := by
  unfold countingDivisor
  split_ifs
  · exact hdivisor
  · exact one_ne_zero

theorem countingDivisor_dvd (i : ι) (hi : i ∈ G.columns) (hc : G.coefficient i ≠ 0) :
    D.countingDivisor ∣ (G.ideal i).val := by
  unfold countingDivisor
  split_ifs with hrows
  · exact D.post_divisor_dvd hrows i hi hc
  · exact one_dvd _

theorem countingDivisor_eq (hrows : G.rows.Nonempty) : D.countingDivisor = divisor :=
  if_pos hrows

end OriginalNumerator
end ActualGaussSource

section Terminal

variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace ActualGaussStage

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)

/-- The computed six-source dictionary supplies both numerator
estimates and the conditional post-pool divisor gate. The original
central column bound has no first-divisor loss. Only the tail profile
exponent buys a density from the pre-pool upper window. -/
def dualCalibrationOfOriginalNumerator
    {α : Type*} {columns : Finset α} {ideal : α → A.Exterior}
    {coefficient : α → ℂ} {divisor : Ideal (𝓞 K)} {common : A.Exterior} {δ : ℝ}
    (D : G.OriginalNumerator columns ideal coefficient divisor common δ)
    (hdivisor : divisor ≠ 0)
    (sTail sZero : Finset (ℕ × ℕ)) (k : ℕ)
    (Z Lmax Nsave decay total upper constant lower tailProduct zeroProduct
      maskExponent inverseRadiusExponent : ℝ)
    (hZ : 1 < Z) (hconstant : 0 ≤ constant) (hδ : 0 ≤ δ)
    (hcentral : ∀ i ∈ columns, ‖coefficient i‖ ≤ constant * Z ^ (-total / 2))
    (hfull : ∀ i ∈ columns, coefficient i ≠ 0 → A.exteriorNorm (ideal i) ≤ Z ^ upper)
    (htailProduct : 0 ≤ tailProduct) (hzeroProduct : 0 ≤ zeroProduct)
    (factors : ι × ι → Fin k → Ideal (𝓞 K)) (multiplicity : ℕ)
    (hfibers : ∀ v,
      ((G.columns ×ˢ G.columns).filter (fun ij => factors ij = v)).card ≤ multiplicity)
    (hfactor : ∀ ij ∈ G.columns ×ˢ G.columns,
      PowerfulDiagonal.tupleIdeal (factors ij) = (G.ideal ij.1).val * (G.ideal ij.2).val)
    (htailNorm : ∀ ij ∈ G.columns ×ˢ G.columns,
      (Ideal.absNorm ((G.ideal ij.1).val * (G.ideal ij.2).val) : ℝ) ≤ Z ^ tailProduct)
    (hzeroNorm : ∀ ij ∈ G.columns ×ˢ G.columns,
      (G.coefficient ij.1 * star (G.coefficient ij.2)) • s.profile ≠ 0 →
      (Ideal.absNorm ((G.ideal ij.1).val * (G.ideal ij.2).val) : ℝ) ≤ Z ^ zeroProduct)
    (hlower : ∀ i ∈ G.columns, G.coefficient i ≠ 0 →
      Z ^ lower ≤ A.exteriorNorm (G.ideal i))
    (hmask : (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) s.mask)).val ≤
        Z ^ maskExponent)
    (hradius : s.radius.val⁻¹ ≤ Z ^ inverseRadiusExponent)
    (hdegree : secondTailExponent k tailProduct
      ((upper - idealLogLength Z common.val) - total +
        2 * (upper - idealLogLength Z common.val) * δ - 2 * lower)
      maskExponent inverseRadiusExponent ≤ Lmax)
    (hcutoff : s.cutoff = Z ^ firstTailCutoffExponent Lmax Nsave decay) :
    s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay where
  productExponent := tailProduct
  profileExponent := (upper - idealLogLength Z common.val) - total +
    2 * (upper - idealLogLength Z common.val) * δ - 2 * lower
  maskExponent := maskExponent
  inverseRadiusExponent := inverseRadiusExponent
  tailAmplitude := (constant ^ 2 / (Ideal.absNorm divisor : ℝ)) *
    sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) s.profile
  zeroAmplitude := ((constant ^ 2 *
    sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) s.profile) *
      Z ^ (-total + 2 * (upper - idealLogLength Z common.val) * δ - lower) *
        ((2 : ℝ) ^ s.mask.card * Z ^ inverseRadiusExponent) * Real.sqrt (Z ^ zeroProduct)) /
          (Ideal.absNorm D.countingDivisor : ℝ)
  zeroAmplitude_nonneg := by
    have hz : 0 ≤ Z := (zero_lt_one.trans hZ).le
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (sq_nonneg _) (apply_nonneg _ _)) (Real.rpow_nonneg hz _))
      (mul_nonneg (pow_nonneg (by norm_num) _) (Real.rpow_nonneg hz _)))
      (Real.sqrt_nonneg _)) (Nat.cast_nonneg _)
  windows := {
    base_ge_one := hZ.le
    productExponent_nonneg := htailProduct
    amplitude_nonneg := mul_nonneg
      (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) (apply_nonneg _ _)
    factors := factors
    multiplicity := multiplicity
    factors_fiber_card := hfibers
    factor_product := hfactor
    product_norm := htailNorm
    profile_seminorm := by
      intro v hv
      have hm := (mem_firstZeroPairs G.columns G.columns G.ideal G.ideal v).mp hv
      exact G.gram_numerator_le
        (sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ))
        s.profile v.2.1 v.2.2 hm.1 hm.2.1 Z lower
        ((upper - idealLogLength Z common.val) - total +
          2 * (upper - idealLogLength Z common.val) * δ)
        (constant ^ 2 / (Ideal.absNorm divisor : ℝ)) (zero_lt_one.trans hZ)
        (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) hlower
        (D.central_pair_le_divisor_for_tail Z total upper constant hZ hconstant hδ hdivisor
          hcentral hfull _ _ hm.1 hm.2.1)
    mask_norm := hmask
    inverse_radius := hradius }
  exponent_bound := hdegree
  cutoff_eq := hcutoff
  zeroProductExponent := zeroProduct
  zeroProductExponent_nonneg := hzeroProduct
  zero_product_norm := hzeroNorm
  zeroDivisor := D.countingDivisor
  zeroDivisor_ne_zero := D.countingDivisor_ne_zero hdivisor
  zero_divisor_dvd := by
    intro ij hij hgram _
    apply D.countingDivisor_dvd ij.1 (Finset.mem_product.mp hij).1
    intro hzero
    exact hgram (by simp only [hzero, zero_mul, zero_smul])
  zero_normalization := by
    intro v hv
    have hm := (mem_firstZeroPairs G.columns G.columns G.ideal G.ideal v).mp hv
    have hz : 0 < Z := zero_lt_one.trans hZ
    have hp := G.gram_numerator_mul_norm_le
      (sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ))
      s.profile v.2.1 v.2.2 hm.1 hm.2.1 Z lower
      (-total + 2 * (upper - idealLogLength Z common.val) * δ) (constant ^ 2) hz
      (sq_nonneg _) hlower
      (D.central_pair_le Z total upper constant hZ hconstant hδ hcentral hfull
        _ _ hm.1 hm.2.1)
    have hmaskSum : (∑ D ∈ s.mask.powerset, firstZeroDivisorWeight s.radius D) ≤
        (2 : ℝ) ^ s.mask.card * Z ^ inverseRadiusExponent :=
      (sum_firstZeroDivisorWeight_le s.radius s.mask).trans
        (mul_le_mul_of_nonneg_left hradius (pow_nonneg (by norm_num) _))
    have hmaskNonneg : 0 ≤ ∑ D ∈ s.mask.powerset, firstZeroDivisorWeight s.radius D :=
      Finset.sum_nonneg fun D _ => firstZeroDivisorWeight_nonneg s.radius D
    have hnum : 0 ≤ (constant ^ 2 *
        sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) s.profile) *
          Z ^ (-total + 2 * (upper - idealLogLength Z common.val) * δ - lower) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (apply_nonneg _ _)) (Real.rpow_nonneg hz.le _)
    have hsqrt : Real.sqrt (Z ^ zeroProduct) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (Real.rpow_pos_of_pos hz _))
    have hNorm : (Ideal.absNorm D.countingDivisor : ℝ) ≠ 0 := by
      exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (D.countingDivisor_ne_zero hdivisor)
    exact (mul_le_mul hp hmaskSum hmaskNonneg hnum).trans_eq
      (by field_simp [hsqrt, hNorm] <;> ring)


end ActualGaussStage
end Terminal

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussSource.gram_numerator_eq
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussSource.gram_numerator_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussSource.gram_numerator_mul_norm_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussSource.OriginalNumerator.countingDivisor_dvd
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.dualCalibrationOfOriginalNumerator
