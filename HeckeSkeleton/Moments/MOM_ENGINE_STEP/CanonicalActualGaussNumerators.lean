import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalActiveGaussLower
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalFirstWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SupportedGaussStages

/-!
# The literal six Gauss numerators and the original central scale

The source coefficients still contain their actual first-divisor gate,
finite phase and first logarithmic tilt. The pool's original norm
cancels exactly the new residual denominator. Its phase has norm one.
All estimates below use these exact original coefficients.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}

section PoolNumerator

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {htrace : A.ContainsTraceBadPlaces} {C : A.GeneralArithmeticContext σ η htrace}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {pool : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}

/-- Exact cancellation of the actual residual norm, with its original
unit phase. The full prime power has not been bounded or dropped. -/
theorem FirstGaussPoolData.residualCoefficient_raw_norm
    (d : FirstGaussPoolData C pool ι) (p : ExteriorPrime A) (n : ℕ)
    (c : ι → ℂ) (i : d.valuationColumns p n) :
    ‖d.residualCoefficient p n c i *
        (A.exteriorNorm (d.residualPresentation p n i).residual : ℂ)‖ =
      ‖c i.val * (A.exteriorNorm (d.ideal i.val) : ℂ)‖ := by
  have hnorm : (A.exteriorNorm (d.residualPresentation p n i).residual : ℂ) ≠ 0 := by
    exact_mod_cast (A.exteriorNorm_pos (d.residualPresentation p n i).residual).ne'
  unfold FirstGaussPoolData.residualCoefficient FirstGaussPoolData.adjustedCoefficient
  rw [div_mul_cancel₀ _ hnorm, norm_mul,
    (d.residualPresentation p n i).columnPhase_norm, mul_one]

end PoolNumerator

private theorem residue_numerator_norm_le
    {N : ℝ} (hN : 0 < N) (δ : ℝ) (c v : ℂ) (hv : ‖v‖ ≤ 1) :
    ‖((c * ((N ^ δ : ℝ) : ℂ) * v) / (N : ℂ)) * (N : ℂ)‖ ≤ ‖c‖ * N ^ δ := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [div_mul_cancel₀ _ hNc, norm_mul, CanonicalFirstLog.scaledTiltScalar_norm hN]
  exact (mul_le_mul_of_nonneg_left hv
    (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hN.le _))).trans_eq (mul_one _)

namespace ActualGaussSource

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {htrace : A.ContainsTraceBadPlaces} {C : A.GeneralArithmeticContext σ η htrace}
variable {ι α : Type*} (G : ActualGaussSource C ι)

/-- A computed dictionary of the same original column and its
pre-pool first residual. The first divisor always divides the pre-pool ideal. It divides the
post-pool quotient only when the actual physical row carrier is nonempty. -/
structure OriginalNumerator (columns : Finset α) (ideal : α → A.Exterior)
    (coefficient : α → ℂ) (divisor : Ideal (𝓞 K)) (common : A.Exterior) (δ : ℝ) where
  index : ι → α
  index_mem : ∀ i ∈ G.columns, index i ∈ columns
  preIdeal : ι → A.Exterior
  reconstructed : ∀ i ∈ G.columns,
    (ideal (index i)).val = common.val * (preIdeal i).val
  numerator_norm : ∀ i ∈ G.columns,
    ‖G.coefficient i * (A.exteriorNorm (G.ideal i) : ℂ)‖ ≤
      ‖coefficient (index i)‖ * A.exteriorNorm (preIdeal i) ^ δ
  divisor_dvd : ∀ i ∈ G.columns, G.coefficient i ≠ 0 → divisor ∣ (preIdeal i).val
  original_nonzero : ∀ i ∈ G.columns, G.coefficient i ≠ 0 → coefficient (index i) ≠ 0
  post_divisor_dvd : G.rows.Nonempty →
    ∀ i ∈ G.columns, G.coefficient i ≠ 0 → divisor ∣ (G.ideal i).val

namespace OriginalNumerator

variable {G}
variable {columns : Finset α} {ideal : α → A.Exterior} {coefficient : α → ℂ}
variable {divisor : Ideal (𝓞 K)} {common : A.Exterior} {δ : ℝ}
variable (D : G.OriginalNumerator columns ideal coefficient divisor common δ)

theorem pre_norm_window (Z upper : ℝ) (hZ : 1 < Z)
    (hfull : ∀ i ∈ columns, coefficient i ≠ 0 → A.exteriorNorm (ideal i) ≤ Z ^ upper)
    (i : ι) (hi : i ∈ G.columns) (hc : G.coefficient i ≠ 0) :
    A.exteriorNorm (D.preIdeal i) ≤ Z ^ (upper - idealLogLength Z common.val) :=
  reconstructed_exterior_norm_window (ideal (D.index i)) common (D.preIdeal i)
    (D.reconstructed i hi) Z upper hZ
    (hfull _ (D.index_mem i hi) (D.original_nonzero i hi hc))

include D in
/-- The central inverse square root is the original parent one.
Only the pre-pool ideal pays the actual first logarithmic tilt. -/
theorem central_norm_le (Z total upper constant : ℝ) (hZ : 1 < Z)
    (hconstant : 0 ≤ constant) (hδ : 0 ≤ δ)
    (hcentral : ∀ i ∈ columns, ‖coefficient i‖ ≤ constant * Z ^ (-total / 2))
    (hfull : ∀ i ∈ columns, coefficient i ≠ 0 → A.exteriorNorm (ideal i) ≤ Z ^ upper)
    (i : ι) (hi : i ∈ G.columns) (hc : G.coefficient i ≠ 0) :
    ‖G.coefficient i * (A.exteriorNorm (G.ideal i) : ℂ)‖ ≤
      constant * Z ^ (-total / 2 + (upper - idealLogLength Z common.val) * δ) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have htilt := CanonicalFirstLog.tilt_le_of_norm_window
    (A.exteriorNorm_pos (D.preIdeal i)) hz hδ (D.pre_norm_window Z upper hZ hfull i hi hc)
  exact ((D.numerator_norm i hi).trans
    (mul_le_mul (hcentral _ (D.index_mem i hi)) htilt
      (Real.rpow_nonneg (A.exteriorNorm_pos _).le _)
      (mul_nonneg hconstant (Real.rpow_nonneg hz.le _)))).trans_eq
        (by rw [Real.rpow_add hz]; ring)

include D in
/-- The sharp original pair bound. No first-divisor density is
purchased from a column norm: it is supplied later by the exact
square-diagonal count. -/
theorem central_pair_le (Z total upper constant : ℝ) (hZ : 1 < Z)
    (hconstant : 0 ≤ constant) (hδ : 0 ≤ δ)
    (hcentral : ∀ i ∈ columns, ‖coefficient i‖ ≤ constant * Z ^ (-total / 2))
    (hfull : ∀ i ∈ columns, coefficient i ≠ 0 → A.exteriorNorm (ideal i) ≤ Z ^ upper)
    (i j : ι) (hi : i ∈ G.columns) (hj : j ∈ G.columns)
    (hci : G.coefficient i ≠ 0) (hcj : G.coefficient j ≠ 0) :
    ‖G.coefficient i * (A.exteriorNorm (G.ideal i) : ℂ)‖ *
        ‖G.coefficient j * (A.exteriorNorm (G.ideal j) : ℂ)‖ ≤
      constant ^ 2 * Z ^ (-total + 2 * (upper - idealLogLength Z common.val) * δ) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hleft := D.central_norm_le Z total upper constant hZ hconstant hδ hcentral hfull i hi hci
  have hright := D.central_norm_le Z total upper constant hZ hconstant hδ hcentral hfull j hj hcj
  have hp := mul_le_mul hleft hright (norm_nonneg _)
    (mul_nonneg hconstant (Real.rpow_nonneg hz.le _))
  apply hp.trans_eq
  rw [pow_two, show -total + 2 * (upper - idealLogLength Z common.val) * δ =
    (-total / 2 + (upper - idealLogLength Z common.val) * δ) +
      (-total / 2 + (upper - idealLogLength Z common.val) * δ) by ring,
    Real.rpow_add hz (-total / 2 + (upper - idealLogLength Z common.val) * δ)
      (-total / 2 + (upper - idealLogLength Z common.val) * δ)]
  ring


include D in
/-- The genuine first divisor is bounded using its pre-pool ideal.
This is the only norm window used when buying its density for a tail. -/
theorem divisor_norm_window (Z upper : ℝ) (hZ : 1 < Z)
    (hfull : ∀ i ∈ columns, coefficient i ≠ 0 → A.exteriorNorm (ideal i) ≤ Z ^ upper)
    (i : ι) (hi : i ∈ G.columns) (hc : G.coefficient i ≠ 0) :
    (Ideal.absNorm divisor : ℝ) ≤ Z ^ (upper - idealLogLength Z common.val) :=
  (ideal_norm_le_of_dvd (D.preIdeal i).property.1 (D.divisor_dvd i hi hc)).trans
    (D.pre_norm_window Z upper hZ hfull i hi hc)

include D in
/-- A tail may buy the first-divisor density with the full explicit
pre-pool exponent. This extra exponent is paid by the chosen tail
cutoff, and is not used in the pure dual-zero calibration. -/
theorem central_pair_le_divisor_for_tail
    (Z total upper constant : ℝ) (hZ : 1 < Z)
    (hconstant : 0 ≤ constant) (hδ : 0 ≤ δ) (hdivisor : divisor ≠ 0)
    (hcentral : ∀ i ∈ columns, ‖coefficient i‖ ≤ constant * Z ^ (-total / 2))
    (hfull : ∀ i ∈ columns, coefficient i ≠ 0 → A.exteriorNorm (ideal i) ≤ Z ^ upper)
    (i j : ι) (hi : i ∈ G.columns) (hj : j ∈ G.columns)
    (hci : G.coefficient i ≠ 0) (hcj : G.coefficient j ≠ 0) :
    ‖G.coefficient i * (A.exteriorNorm (G.ideal i) : ℂ)‖ *
        ‖G.coefficient j * (A.exteriorNorm (G.ideal j) : ℂ)‖ ≤
      (constant ^ 2 / (Ideal.absNorm divisor : ℝ)) *
        Z ^ ((upper - idealLogLength Z common.val) - total +
          2 * (upper - idealLogLength Z common.val) * δ) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hN : 0 < (Ideal.absNorm divisor : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hdivisor))
  have hpair := D.central_pair_le Z total upper constant hZ hconstant hδ hcentral hfull
    i j hi hj hci hcj
  have hpaid := D.divisor_norm_window Z upper hZ hfull i hi hci
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hN).mpr
  calc
    _ ≤ (constant ^ 2 * Z ^ (-total + 2 * (upper - idealLogLength Z common.val) * δ)) *
        Z ^ (upper - idealLogLength Z common.val) :=
      mul_le_mul hpair hpaid hN.le
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hz.le _))
    _ = _ := by
      rw [show (upper - idealLogLength Z common.val) - total +
          2 * (upper - idealLogLength Z common.val) * δ =
        (-total + 2 * (upper - idealLogLength Z common.val) * δ) +
          (upper - idealLogLength Z common.val) by ring,
        Real.rpow_add hz (-total + 2 * (upper - idealLogLength Z common.val) * δ)
          (upper - idealLogLength Z common.val)]
      ring

end OriginalNumerator
end ActualGaussSource

section CanonicalFirst

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable (b : FirstCommonCharacterBlock fullI fullJ DE)
variable (C : A.GeneralArithmeticContext σ η htrace)
variable (left : Finset ι) (right : Finset κ)
variable (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
variable (c : ι → ℂ) (e : κ → ℂ)
variable (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
variable (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
variable (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
variable (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
variable (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}

local notation "chart" => FirstBlockProfileChart.canonicalLogWithCoefficients
  hΓ μv ν b C left right φ c e finiteTest hlc hcs radius D δ hδ hδhalf


namespace FirstBlockDirectData

variable (p : FirstBlockDirectData
  (FirstBlockProfileChart.canonicalLogWithCoefficients hΓ μv ν b C left right φ c e
    finiteTest hlc hcs radius D δ hδ hδhalf) M X hX)
variable (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)

theorem canonicalLeftDivisor_dvd_of_ne_zero (i : ι)
    (hc : p.leftDivisorCoefficient S χ i ≠ 0) :
    S.val ∣ (p.leftData.ideal i).val := by
  by_contra h
  exact hc (by simp only [leftDivisorCoefficient, if_neg h])

/-- The actual first phase is bounded only after its original residue
identity, and the first-divisor gate is kept in the coefficient. -/
theorem canonicalLeftDivisor_raw_norm_le (i : ι)
    (hi : i ∈ p.leftData.columns) :
    ‖p.leftDivisorCoefficient S χ i * (A.exteriorNorm (p.leftData.ideal i) : ℂ)‖ ≤
      ‖c i‖ * A.exteriorNorm (b.leftResidual i) ^ δ := by
  by_cases hSi : S.val ∣ (p.leftData.ideal i).val
  swap
  · simpa only [leftDivisorCoefficient, if_neg hSi, zero_mul, norm_zero] using
      (mul_nonneg (norm_nonneg (c i))
        (Real.rpow_nonneg (A.exteriorNorm_pos (b.leftResidual i)).le δ))
  have ha : A.IsAllowed C.correction.B
      (Units.mk0 (b.leftGenerator i : K)
        (by exact_mod_cast (b.left_generates i).1)) := by
    have hgen := p.leftData.allowed i hi
    simpa only [p.left_generator] using hgen
  have hχ : (fixedLeftPhase PUnit χ PUnit.unit : ℂ) = 1 := by
    change ((fixedLeftPhase PUnit χ) (1 : PUnit) : ℂ) = 1
    rw [map_one, Circle.coe_one]
  unfold leftDivisorCoefficient
  rw [if_pos hSi, hχ, mul_one]
  change ‖(FirstBlockProfileChart.canonicalLogWithCoefficients hΓ μv ν b C left right
      φ c e finiteTest hlc hcs radius D δ hδ hδhalf).leftCoefficient i *
    firstLeftDivisorFactor
      (generatedOriginalColumn (σ := σ) hΓ (b.leftResidual i)
        (b.leftGenerator i) (b.left_generates i))
      (actualActiveColumn hΓ C b.primes b.primes_injective
        b.leftMultiplicity b.rightMultiplicity)
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val *
    (A.exteriorNorm (p.leftData.ideal i) : ℂ)‖ ≤ _
  rw [FirstBlockProfileChart.canonicalLog_leftSourceCoefficient hΓ μv ν b C
    left right φ c e finiteTest hlc hcs radius δ hδ hδhalf D i ha, p.left_ideal]
  exact residue_numerator_norm_le (A.exteriorNorm_pos _) δ (c i) _
    (actualIdealResidue_norm_le_one C _ _)

theorem canonicalRightDivisor_dvd_of_ne_zero (j : κ)
    (hc : p.rightDivisorCoefficient S χ j ≠ 0) :
    S.val ∣ (p.rightData.ideal j).val := by
  by_contra h
  exact hc (by simp only [rightDivisorCoefficient, if_neg h])

/-- The actual first phase is bounded only after its original residue
identity, and the first-divisor gate is kept in the coefficient. -/
theorem canonicalRightDivisor_raw_norm_le (j : κ)
    (hi : j ∈ p.rightData.columns) :
    ‖p.rightDivisorCoefficient S χ j * (A.exteriorNorm (p.rightData.ideal j) : ℂ)‖ ≤
      ‖e j‖ * A.exteriorNorm (b.rightResidual j) ^ δ := by
  by_cases hSj : S.val ∣ (p.rightData.ideal j).val
  swap
  · simpa only [rightDivisorCoefficient, if_neg hSj, zero_mul, norm_zero] using
      (mul_nonneg (norm_nonneg (e j))
        (Real.rpow_nonneg (A.exteriorNorm_pos (b.rightResidual j)).le δ))
  have ha : A.IsAllowed C.correction.B
      (Units.mk0 (b.rightGenerator j : K)
        (by exact_mod_cast (b.right_generates j).1)) := by
    have hgen := p.rightData.allowed j hi
    simpa only [p.right_generator] using hgen
  have hχ : (fixedRightPhase PUnit χ PUnit.unit : ℂ) = 1 := by
    change ((fixedRightPhase PUnit χ) (1 : PUnit) : ℂ) = 1
    rw [map_one, Circle.coe_one]
  unfold rightDivisorCoefficient
  rw [if_pos hSj, hχ, mul_one]
  change ‖(FirstBlockProfileChart.canonicalLogWithCoefficients hΓ μv ν b C left right
      φ c e finiteTest hlc hcs radius D δ hδ hδhalf).rightCoefficient j *
    firstRightDivisorFactor
      (generatedOriginalColumn (σ := σ) hΓ (b.rightResidual j)
        (b.rightGenerator j) (b.right_generates j))
      (actualActiveColumn hΓ C b.primes b.primes_injective
        b.leftMultiplicity b.rightMultiplicity)
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val *
    (A.exteriorNorm (p.rightData.ideal j) : ℂ)‖ ≤ _
  rw [FirstBlockProfileChart.canonicalLog_rightSourceCoefficient hΓ μv ν b C
    left right φ c e finiteTest hlc hcs radius δ hδ hδhalf D j ha, p.right_ideal]
  exact residue_numerator_norm_le (A.exteriorNorm_pos _) δ (e j) _
    (actualIdealResidue_norm_le_one C _ _)

/-- The dictionary is computed from this exact source, including its
original divisor coefficient and finite phase. -/
def canonicalLeftOriginalNumerator :
    (p.leftData.directSource (p.leftDivisorCoefficient S χ)).OriginalNumerator
      left fullI c S.val (primePowerProduct b.primes b.leftMultiplicity) δ where
  index := id
  index_mem i hi := by
    have hi' : i ∈ b.leftColumns left := by simpa only [DirectGaussData.directSource, p.left_columns] using hi
    exact (Finset.mem_filter.mp hi').1
  preIdeal := b.leftResidual
  reconstructed i hi := by
    have hi' : i ∈ b.leftColumns left := by simpa only [DirectGaussData.directSource, p.left_columns] using hi
    exact b.left_reconstruct left i hi'
  numerator_norm i hi := by
    change ‖p.leftDivisorCoefficient S χ i *
      (A.exteriorNorm (p.leftData.ideal i) : ℂ)‖ ≤ _
    exact p.canonicalLeftDivisor_raw_norm_le hΓ μv ν b C left right φ c e finiteTest
      hlc hcs radius D δ hδ hδhalf S χ i
      (by simpa only [DirectGaussData.directSource] using hi)
  divisor_dvd i _ hc := by
    have h := p.canonicalLeftDivisor_dvd_of_ne_zero hΓ μv ν b C left right φ c e finiteTest
      hlc hcs radius D δ hδ hδhalf S χ i hc
    simpa only [p.left_ideal] using h
  post_divisor_dvd _ i _ hc :=
    p.canonicalLeftDivisor_dvd_of_ne_zero hΓ μv ν b C left right φ c e finiteTest
      hlc hcs radius D δ hδ hδhalf S χ i hc
  original_nonzero i _ hc := p.canonicalLeft_nonzero_original hΓ μv ν b C left right
    φ c e finiteTest hlc hcs radius D δ hδ hδhalf S χ i hc

/-- The dictionary is computed from this exact source, including its
original divisor coefficient and finite phase. -/
def canonicalRightOriginalNumerator :
    (p.rightData.directSource (p.rightDivisorCoefficient S χ)).OriginalNumerator
      right fullJ e S.val (primePowerProduct b.primes b.rightMultiplicity) δ where
  index := id
  index_mem j hi := by
    have hi' : j ∈ b.rightColumns right := by simpa only [DirectGaussData.directSource, p.right_columns] using hi
    exact (Finset.mem_filter.mp hi').1
  preIdeal := b.rightResidual
  reconstructed j hi := by
    have hi' : j ∈ b.rightColumns right := by simpa only [DirectGaussData.directSource, p.right_columns] using hi
    exact b.right_reconstruct right j hi'
  numerator_norm j hi := by
    change ‖p.rightDivisorCoefficient S χ j *
      (A.exteriorNorm (p.rightData.ideal j) : ℂ)‖ ≤ _
    exact p.canonicalRightDivisor_raw_norm_le hΓ μv ν b C left right φ c e finiteTest
      hlc hcs radius D δ hδ hδhalf S χ j
      (by simpa only [DirectGaussData.directSource] using hi)
  divisor_dvd j _ hc := by
    have h := p.canonicalRightDivisor_dvd_of_ne_zero hΓ μv ν b C left right φ c e finiteTest
      hlc hcs radius D δ hδ hδhalf S χ j hc
    simpa only [p.right_ideal] using h
  post_divisor_dvd _ j _ hc :=
    p.canonicalRightDivisor_dvd_of_ne_zero hΓ μv ν b C left right φ c e finiteTest
      hlc hcs radius D δ hδ hδhalf S χ j hc
  original_nonzero j _ hc := p.canonicalRight_nonzero_original hΓ μv ν b C left right
    φ c e finiteTest hlc hcs radius D δ hδ hδhalf S χ j hc

end FirstBlockDirectData

namespace FirstBlockPoolData

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {base ell eps : ℝ}
variable {pool : PowerScaleExteriorPool A bad base ell eps}
variable (p : FirstBlockPoolData
  (FirstBlockProfileChart.canonicalLogWithCoefficients hΓ μv ν b C left right φ c e
    finiteTest hlc hcs radius D δ hδ hδhalf) pool M X hX)
variable (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)

theorem canonicalLeftDivisor_dvd_of_ne_zero (i : ι)
    (hc : p.leftDivisorCoefficient S χ i ≠ 0) :
    S.val ∣ (p.leftData.ideal i).val := by
  by_contra h
  exact hc (by simp only [leftDivisorCoefficient, if_neg h])

/-- The actual first phase is bounded only after its original residue
identity, and the first-divisor gate is kept in the coefficient. -/
theorem canonicalLeftDivisor_raw_norm_le (i : ι)
    (hi : i ∈ p.leftData.columns) :
    ‖p.leftDivisorCoefficient S χ i * (A.exteriorNorm (p.leftData.ideal i) : ℂ)‖ ≤
      ‖c i‖ * A.exteriorNorm (b.leftResidual i) ^ δ := by
  by_cases hSi : S.val ∣ (p.leftData.ideal i).val
  swap
  · simpa only [leftDivisorCoefficient, if_neg hSi, zero_mul, norm_zero] using
      (mul_nonneg (norm_nonneg (c i))
        (Real.rpow_nonneg (A.exteriorNorm_pos (b.leftResidual i)).le δ))
  rw [p.canonicalLog_leftDivisorCoefficient hΓ μv ν b C left right φ c e
    finiteTest hlc hcs radius D δ hδ hδhalf S χ i hi hSi, p.left_ideal]
  exact residue_numerator_norm_le (A.exteriorNorm_pos _) δ (c i) _
    (actualIdealResidue_norm_le_one C _ _)

/-- The original pool phase has norm one. The numerator retains the
pre-pool logarithmic tilt, with no new profile or source. -/
theorem canonicalLeftPool_raw_norm_le
    (prime : ExteriorPrime A) (n : ℕ)
    (i : (p.divisorPools.leftData S).valuationColumns prime n) :
    ‖((p.divisorPools.leftData S).residualSource prime n
        (p.leftDivisorCoefficient S χ)).coefficient i *
      (A.exteriorNorm (((p.divisorPools.leftData S).residualSource prime n
        (p.leftDivisorCoefficient S χ)).ideal i) : ℂ)‖ ≤
      ‖c i.val‖ * A.exteriorNorm (b.leftResidual i.val) ^ δ := by
  change ‖(p.divisorPools.leftData S).residualCoefficient prime n
    (p.leftDivisorCoefficient S χ) i *
    (A.exteriorNorm ((p.divisorPools.leftData S).residualPresentation prime n i).residual : ℂ)‖ ≤ _
  rw [FirstGaussPoolData.residualCoefficient_raw_norm, p.divisorPools.left_ideal S]
  exact p.canonicalLeftDivisor_raw_norm_le hΓ μv ν b C left right φ c e finiteTest
    hlc hcs radius D δ hδ hδhalf S χ i.val
    (by simpa only [p.divisorPools.left_columns S] using
      (Finset.mem_filter.mp i.property).1)

theorem canonicalRightDivisor_dvd_of_ne_zero (j : κ)
    (hc : p.rightDivisorCoefficient S χ j ≠ 0) :
    S.val ∣ (p.rightData.ideal j).val := by
  by_contra h
  exact hc (by simp only [rightDivisorCoefficient, if_neg h])

/-- The actual first phase is bounded only after its original residue
identity, and the first-divisor gate is kept in the coefficient. -/
theorem canonicalRightDivisor_raw_norm_le (j : κ)
    (hi : j ∈ p.rightData.columns) :
    ‖p.rightDivisorCoefficient S χ j * (A.exteriorNorm (p.rightData.ideal j) : ℂ)‖ ≤
      ‖e j‖ * A.exteriorNorm (b.rightResidual j) ^ δ := by
  by_cases hSj : S.val ∣ (p.rightData.ideal j).val
  swap
  · simpa only [rightDivisorCoefficient, if_neg hSj, zero_mul, norm_zero] using
      (mul_nonneg (norm_nonneg (e j))
        (Real.rpow_nonneg (A.exteriorNorm_pos (b.rightResidual j)).le δ))
  rw [p.canonicalLog_rightDivisorCoefficient hΓ μv ν b C left right φ c e
    finiteTest hlc hcs radius D δ hδ hδhalf S χ j hi hSj, p.right_ideal]
  exact residue_numerator_norm_le (A.exteriorNorm_pos _) δ (e j) _
    (actualIdealResidue_norm_le_one C _ _)

/-- The original pool phase has norm one. The numerator retains the
pre-pool logarithmic tilt, with no new profile or source. -/
theorem canonicalRightPool_raw_norm_le
    (prime : ExteriorPrime A) (n : ℕ)
    (j : (p.divisorPools.rightData S).valuationColumns prime n) :
    ‖((p.divisorPools.rightData S).residualSource prime n
        (p.rightDivisorCoefficient S χ)).coefficient j *
      (A.exteriorNorm (((p.divisorPools.rightData S).residualSource prime n
        (p.rightDivisorCoefficient S χ)).ideal j) : ℂ)‖ ≤
      ‖e j.val‖ * A.exteriorNorm (b.rightResidual j.val) ^ δ := by
  change ‖(p.divisorPools.rightData S).residualCoefficient prime n
    (p.rightDivisorCoefficient S χ) j *
    (A.exteriorNorm ((p.divisorPools.rightData S).residualPresentation prime n j).residual : ℂ)‖ ≤ _
  rw [FirstGaussPoolData.residualCoefficient_raw_norm, p.divisorPools.right_ideal S]
  exact p.canonicalRightDivisor_raw_norm_le hΓ μv ν b C left right φ c e finiteTest
    hlc hcs radius D δ hδ hδhalf S χ j.val
    (by simpa only [p.divisorPools.right_columns S] using
      (Finset.mem_filter.mp j.property).1)

/-- The dictionary is computed from this exact source, including its
original divisor coefficient and finite phase. -/
def canonicalLeftMainOriginalNumerator :
    ((p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)).OriginalNumerator
      left fullI c S.val (primePowerProduct b.primes b.leftMultiplicity) δ where
  index := id
  index_mem i hi := by
    have hi' : i ∈ b.leftColumns left := by simpa only [FirstGaussPoolData.mainSource, p.divisorPools.left_columns S,
      p.left_columns] using hi
    exact (Finset.mem_filter.mp hi').1
  preIdeal := b.leftResidual
  reconstructed i hi := by
    have hi' : i ∈ b.leftColumns left := by simpa only [FirstGaussPoolData.mainSource, p.divisorPools.left_columns S,
      p.left_columns] using hi
    exact b.left_reconstruct left i hi'
  numerator_norm i hi := by
    change ‖p.leftDivisorCoefficient S χ i *
      (A.exteriorNorm ((p.divisorPools.leftData S).ideal i) : ℂ)‖ ≤ _
    rw [p.divisorPools.left_ideal S]
    exact p.canonicalLeftDivisor_raw_norm_le hΓ μv ν b C left right φ c e finiteTest
      hlc hcs radius D δ hδ hδhalf S χ i
      (by simpa only [FirstGaussPoolData.mainSource, p.divisorPools.left_columns S] using hi)
  divisor_dvd i _ hc := by
    have h := p.canonicalLeftDivisor_dvd_of_ne_zero hΓ μv ν b C left right φ c e finiteTest
      hlc hcs radius D δ hδ hδhalf S χ i hc
    simpa only [p.left_ideal] using h
  post_divisor_dvd _ i _ hc := by
    change S.val ∣ ((p.divisorPools.leftData S).ideal i).val
    rw [p.divisorPools.left_ideal S]
    exact p.canonicalLeftDivisor_dvd_of_ne_zero hΓ μv ν b C left right φ c e finiteTest
      hlc hcs radius D δ hδ hδhalf S χ i hc
  original_nonzero i _ hc := p.canonicalLeft_nonzero_original hΓ μv ν b C left right
    φ c e finiteTest hlc hcs radius D δ hδ hδhalf S χ i hc

theorem canonicalLeftPool_nonzero_pre (prime : ExteriorPrime A) (n : ℕ)
    (i : (p.divisorPools.leftData S).valuationColumns prime n)
    (hc : ((p.divisorPools.leftData S).residualSource prime n (p.leftDivisorCoefficient S χ)).coefficient i ≠ 0) :
    p.leftDivisorCoefficient S χ i.val ≠ 0 := by
  intro hz
  apply hc
  change (p.divisorPools.leftData S).residualCoefficient prime n
    (p.leftDivisorCoefficient S χ) i = 0
  rw [FirstGaussPoolData.residualCoefficient_eq, hz, zero_mul, zero_mul]

/-- The pool record remembers the ideal before removal of the full
prime power. The first divisor is also transported to the post-pool ideal only
when an actual error row proves the amplifier prime is eligible. -/
def canonicalLeftPoolOriginalNumerator (prime : ExteriorPrime A) (n : ℕ) :
    ((p.divisorPools.leftData S).residualSource prime n (p.leftDivisorCoefficient S χ)).OriginalNumerator
      left fullI c S.val (primePowerProduct b.primes b.leftMultiplicity) δ where
  index i := i.val
  index_mem i _ := by
    have hi' : i.val ∈ b.leftColumns left := by
      simpa only [p.divisorPools.left_columns S, p.left_columns] using
        (Finset.mem_filter.mp i.property).1
    exact (Finset.mem_filter.mp hi').1
  preIdeal i := b.leftResidual i.val
  reconstructed i _ := by
    have hi' : i.val ∈ b.leftColumns left := by
      simpa only [p.divisorPools.left_columns S, p.left_columns] using
        (Finset.mem_filter.mp i.property).1
    exact b.left_reconstruct left i.val hi'
  numerator_norm i _ := p.canonicalLeftPool_raw_norm_le hΓ μv ν b C left right φ c e
    finiteTest hlc hcs radius D δ hδ hδhalf S χ prime n i
  divisor_dvd i _ hc := by
    have hc' := p.canonicalLeftPool_nonzero_pre hΓ μv ν b C left right φ c e finiteTest
      hlc hcs radius D δ hδ hδhalf S χ prime n i hc
    have h := p.canonicalLeftDivisor_dvd_of_ne_zero hΓ μv ν b C left right φ c e finiteTest
      hlc hcs radius D δ hδ hδhalf S χ i.val hc'
    simpa only [p.left_ideal] using h
  post_divisor_dvd hrows i _ hc := by
    apply (p.divisorPools.leftData S).residualSource_nonzero_dvd prime n
      (p.leftDivisorCoefficient S χ) S.val
    · rw [p.divisorPools.left_frozen S]
      exact dvd_mul_left _ _
    · intro x _ hx
      rw [p.divisorPools.left_ideal S]
      exact p.canonicalLeftDivisor_dvd_of_ne_zero hΓ μv ν b C left right φ c e finiteTest
        hlc hcs radius D δ hδ hδhalf S χ x hx
    · exact hrows
    · exact hc
  original_nonzero i _ hc :=
    p.canonicalLeft_nonzero_original hΓ μv ν b C left right φ c e finiteTest hlc hcs
      radius D δ hδ hδhalf S χ i.val
      (p.canonicalLeftPool_nonzero_pre hΓ μv ν b C left right φ c e finiteTest
        hlc hcs radius D δ hδ hδhalf S χ prime n i hc)

/-- The dictionary is computed from this exact source, including its
original divisor coefficient and finite phase. -/
def canonicalRightMainOriginalNumerator :
    ((p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)).OriginalNumerator
      right fullJ e S.val (primePowerProduct b.primes b.rightMultiplicity) δ where
  index := id
  index_mem j hi := by
    have hi' : j ∈ b.rightColumns right := by simpa only [FirstGaussPoolData.mainSource, p.divisorPools.right_columns S,
      p.right_columns] using hi
    exact (Finset.mem_filter.mp hi').1
  preIdeal := b.rightResidual
  reconstructed j hi := by
    have hi' : j ∈ b.rightColumns right := by simpa only [FirstGaussPoolData.mainSource, p.divisorPools.right_columns S,
      p.right_columns] using hi
    exact b.right_reconstruct right j hi'
  numerator_norm j hi := by
    change ‖p.rightDivisorCoefficient S χ j *
      (A.exteriorNorm ((p.divisorPools.rightData S).ideal j) : ℂ)‖ ≤ _
    rw [p.divisorPools.right_ideal S]
    exact p.canonicalRightDivisor_raw_norm_le hΓ μv ν b C left right φ c e finiteTest
      hlc hcs radius D δ hδ hδhalf S χ j
      (by simpa only [FirstGaussPoolData.mainSource, p.divisorPools.right_columns S] using hi)
  divisor_dvd j _ hc := by
    have h := p.canonicalRightDivisor_dvd_of_ne_zero hΓ μv ν b C left right φ c e finiteTest
      hlc hcs radius D δ hδ hδhalf S χ j hc
    simpa only [p.right_ideal] using h
  post_divisor_dvd _ j _ hc := by
    change S.val ∣ ((p.divisorPools.rightData S).ideal j).val
    rw [p.divisorPools.right_ideal S]
    exact p.canonicalRightDivisor_dvd_of_ne_zero hΓ μv ν b C left right φ c e finiteTest
      hlc hcs radius D δ hδ hδhalf S χ j hc
  original_nonzero j _ hc := p.canonicalRight_nonzero_original hΓ μv ν b C left right
    φ c e finiteTest hlc hcs radius D δ hδ hδhalf S χ j hc

theorem canonicalRightPool_nonzero_pre (prime : ExteriorPrime A) (n : ℕ)
    (j : (p.divisorPools.rightData S).valuationColumns prime n)
    (hc : ((p.divisorPools.rightData S).residualSource prime n (p.rightDivisorCoefficient S χ)).coefficient j ≠ 0) :
    p.rightDivisorCoefficient S χ j.val ≠ 0 := by
  intro hz
  apply hc
  change (p.divisorPools.rightData S).residualCoefficient prime n
    (p.rightDivisorCoefficient S χ) j = 0
  rw [FirstGaussPoolData.residualCoefficient_eq, hz, zero_mul, zero_mul]

/-- The pool record remembers the ideal before removal of the full
prime power. The first divisor is also transported to the post-pool ideal only
when an actual error row proves the amplifier prime is eligible. -/
def canonicalRightPoolOriginalNumerator (prime : ExteriorPrime A) (n : ℕ) :
    ((p.divisorPools.rightData S).residualSource prime n (p.rightDivisorCoefficient S χ)).OriginalNumerator
      right fullJ e S.val (primePowerProduct b.primes b.rightMultiplicity) δ where
  index j := j.val
  index_mem j _ := by
    have hi' : j.val ∈ b.rightColumns right := by
      simpa only [p.divisorPools.right_columns S, p.right_columns] using
        (Finset.mem_filter.mp j.property).1
    exact (Finset.mem_filter.mp hi').1
  preIdeal j := b.rightResidual j.val
  reconstructed j _ := by
    have hi' : j.val ∈ b.rightColumns right := by
      simpa only [p.divisorPools.right_columns S, p.right_columns] using
        (Finset.mem_filter.mp j.property).1
    exact b.right_reconstruct right j.val hi'
  numerator_norm j _ := p.canonicalRightPool_raw_norm_le hΓ μv ν b C left right φ c e
    finiteTest hlc hcs radius D δ hδ hδhalf S χ prime n j
  divisor_dvd j _ hc := by
    have hc' := p.canonicalRightPool_nonzero_pre hΓ μv ν b C left right φ c e finiteTest
      hlc hcs radius D δ hδ hδhalf S χ prime n j hc
    have h := p.canonicalRightDivisor_dvd_of_ne_zero hΓ μv ν b C left right φ c e finiteTest
      hlc hcs radius D δ hδ hδhalf S χ j.val hc'
    simpa only [p.right_ideal] using h
  post_divisor_dvd hrows j _ hc := by
    apply (p.divisorPools.rightData S).residualSource_nonzero_dvd prime n
      (p.rightDivisorCoefficient S χ) S.val
    · rw [p.divisorPools.right_frozen S]
      exact dvd_mul_left _ _
    · intro x _ hx
      rw [p.divisorPools.right_ideal S]
      exact p.canonicalRightDivisor_dvd_of_ne_zero hΓ μv ν b C left right φ c e finiteTest
        hlc hcs radius D δ hδ hδhalf S χ x hx
    · exact hrows
    · exact hc
  original_nonzero j _ hc :=
    p.canonicalRight_nonzero_original hΓ μv ν b C left right φ c e finiteTest hlc hcs
      radius D δ hδ hδhalf S χ j.val
      (p.canonicalRightPool_nonzero_pre hΓ μv ν b C left right φ c e finiteTest
        hlc hcs radius D δ hδ hδhalf S χ prime n j hc)

end FirstBlockPoolData
end CanonicalFirst
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.residualCoefficient_raw_norm
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.canonicalLeftDivisor_raw_norm_le
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.canonicalRightDivisor_raw_norm_le
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.canonicalLeftDivisor_raw_norm_le
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.canonicalRightDivisor_raw_norm_le
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.canonicalLeftPool_raw_norm_le
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.canonicalRightPool_raw_norm_le

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussSource.OriginalNumerator.central_pair_le
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.canonicalLeftOriginalNumerator
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.canonicalRightOriginalNumerator
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.canonicalLeftMainOriginalNumerator
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.canonicalRightMainOriginalNumerator
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.canonicalLeftPoolOriginalNumerator
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.canonicalRightPoolOriginalNumerator

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussSource.OriginalNumerator.central_pair_le_divisor_for_tail
