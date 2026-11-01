import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalActiveSecondWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSourceCoefficients
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectSecondStages

/-!
# Sharp actual Gauss column windows on the original coefficient support

Every nonzero direct or main coefficient comes from the same nonzero
original whole coefficient. The actual first common ideal divides out
its complete norm. On a valuation error the actual pool prime power is
also divided out, with its full logarithmic length retained.

These are per-column consequences of the original atom window and
the actual reconstruction identities. The complete source carriers and
their zero coefficients are unchanged.
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

/-- The actual ideal product removes the displayed complete norm,
without a dyadic replacement or a per-column loss. -/
theorem reconstructed_exterior_norm_window
    (original frozen residual : A.Exterior)
    (hproduct : original.val = frozen.val * residual.val)
    (Z total : ℝ) (hZ : 1 < Z)
    (hwindow : A.exteriorNorm original ≤ Z ^ total) :
    A.exteriorNorm residual ≤ Z ^ (total - idealLogLength Z frozen.val) := by
  rw [Real.rpow_sub (zero_lt_one.trans hZ),
    rpow_idealLogLength Z hZ frozen.val frozen.property.1]
  apply (le_div_iff₀ (A.exteriorNorm_pos frozen)).mpr
  have hnorm : A.exteriorNorm original =
      A.exteriorNorm frozen * A.exteriorNorm residual := by
    change (Ideal.absNorm original.val : ℝ) = _
    rw [hproduct, map_mul, Nat.cast_mul] <;> rfl
  rw [hnorm] at hwindow
  simpa only [mul_comm] using hwindow

namespace FirstCommonCharacterBlock

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

theorem leftResidual_norm_window (b : FirstCommonCharacterBlock fullI fullJ DE)
    (left : Finset ι) (Z total : ℝ) (hZ : 1 < Z)
    (i : ι) (hi : i ∈ b.leftColumns left)
    (hwindow : A.exteriorNorm (fullI i) ≤ Z ^ total) :
    A.exteriorNorm (b.leftResidual i) ≤ Z ^ (total - idealLogLength Z DE.1) := by
  have h := reconstructed_exterior_norm_window (fullI i)
    (primePowerProduct b.primes b.leftMultiplicity) (b.leftResidual i)
    (b.left_reconstruct left i hi) Z total hZ hwindow
  simpa only [b.common_left] using h

theorem rightResidual_norm_window (b : FirstCommonCharacterBlock fullI fullJ DE)
    (right : Finset κ) (Z total : ℝ) (hZ : 1 < Z)
    (j : κ) (hj : j ∈ b.rightColumns right)
    (hwindow : A.exteriorNorm (fullJ j) ≤ Z ^ total) :
    A.exteriorNorm (b.rightResidual j) ≤ Z ^ (total - idealLogLength Z DE.2) := by
  have h := reconstructed_exterior_norm_window (fullJ j)
    (primePowerProduct b.primes b.rightMultiplicity) (b.rightResidual j)
    (b.right_reconstruct right j hj) Z total hZ hwindow
  simpa only [b.common_right] using h

end FirstCommonCharacterBlock

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

theorem canonicalLeft_nonzero_original (i : ι)
    (h : p.leftDivisorCoefficient S χ i ≠ 0) : c i ≠ 0 := by
  intro hc
  have hz : (chart).leftCoefficient i = 0 := by
    rw [FirstBlockProfileChart.canonicalLogWithCoefficients_leftCoefficient_eq,
      hc, zero_mul, zero_div]
  apply h
  simp only [leftDivisorCoefficient, originalLeftCoefficient, hz, zero_mul, ite_self]

theorem canonicalRight_nonzero_original (j : κ)
    (h : p.rightDivisorCoefficient S χ j ≠ 0) : e j ≠ 0 := by
  intro hc
  have hz : (chart).rightCoefficient j = 0 := by
    rw [FirstBlockProfileChart.canonicalLogWithCoefficients_rightCoefficient_eq,
      hc, zero_mul, zero_div]
  apply h
  simp only [rightDivisorCoefficient, originalRightCoefficient, hz, zero_mul, ite_self]

/-- The same direct left source, on its actual coefficient support. -/
theorem canonicalLeft_active_norm_window (Z total : ℝ) (hZ : 1 < Z)
    (hfull : ∀ i ∈ left, c i ≠ 0 → A.exteriorNorm (fullI i) ≤ Z ^ total)
    (i : ι) (hi : i ∈ (p.leftData.directSource (p.leftDivisorCoefficient S χ)).columns)
    (hc : (p.leftData.directSource (p.leftDivisorCoefficient S χ)).coefficient i ≠ 0) :
    A.exteriorNorm ((p.leftData.directSource (p.leftDivisorCoefficient S χ)).ideal i) ≤
      Z ^ (total - idealLogLength Z DE.1) := by
  have hi' : i ∈ b.leftColumns left := by
    simpa only [DirectGaussData.directSource, p.left_columns] using hi
  have hci := p.canonicalLeft_nonzero_original hΓ μv ν b C left right φ c e finiteTest
    hlc hcs radius D δ hδ hδhalf S χ i hc
  change A.exteriorNorm (p.leftData.ideal i) ≤ _
  rw [p.left_ideal]
  exact b.leftResidual_norm_window left Z total hZ i hi'
    (hfull i (Finset.mem_filter.mp hi').1 hci)

theorem canonicalRight_active_norm_window (Z total : ℝ) (hZ : 1 < Z)
    (hfull : ∀ j ∈ right, e j ≠ 0 → A.exteriorNorm (fullJ j) ≤ Z ^ total)
    (j : κ) (hj : j ∈ (p.rightData.directSource (p.rightDivisorCoefficient S χ)).columns)
    (hc : (p.rightData.directSource (p.rightDivisorCoefficient S χ)).coefficient j ≠ 0) :
    A.exteriorNorm ((p.rightData.directSource (p.rightDivisorCoefficient S χ)).ideal j) ≤
      Z ^ (total - idealLogLength Z DE.2) := by
  have hj' : j ∈ b.rightColumns right := by
    simpa only [DirectGaussData.directSource, p.right_columns] using hj
  have hcj := p.canonicalRight_nonzero_original hΓ μv ν b C left right φ c e finiteTest
    hlc hcs radius D δ hδ hδhalf S χ j hc
  change A.exteriorNorm (p.rightData.ideal j) ≤ _
  rw [p.right_ideal]
  exact b.rightResidual_norm_window right Z total hZ j hj'
    (hfull j (Finset.mem_filter.mp hj').1 hcj)

end FirstBlockDirectData

namespace FirstBlockPoolData

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {base ell eps : ℝ}
variable {pool : PowerScaleExteriorPool A bad base ell eps}
variable (p : FirstBlockPoolData
  (FirstBlockProfileChart.canonicalLogWithCoefficients hΓ μv ν b C left right φ c e
    finiteTest hlc hcs radius D δ hδ hδhalf) pool M X hX)
variable (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)

theorem canonicalLeft_nonzero_original (i : ι)
    (h : p.leftDivisorCoefficient S χ i ≠ 0) : c i ≠ 0 := by
  intro hc
  have hz : (chart).leftCoefficient i = 0 := by
    rw [FirstBlockProfileChart.canonicalLogWithCoefficients_leftCoefficient_eq,
      hc, zero_mul, zero_div]
  apply h
  simp only [leftDivisorCoefficient, originalLeftCoefficient, hz, zero_mul, ite_self]

theorem canonicalRight_nonzero_original (j : κ)
    (h : p.rightDivisorCoefficient S χ j ≠ 0) : e j ≠ 0 := by
  intro hc
  have hz : (chart).rightCoefficient j = 0 := by
    rw [FirstBlockProfileChart.canonicalLogWithCoefficients_rightCoefficient_eq,
      hc, zero_mul, zero_div]
  apply h
  simp only [rightDivisorCoefficient, originalRightCoefficient, hz, zero_mul, ite_self]

theorem canonicalLeftMain_active_norm_window (Z total : ℝ) (hZ : 1 < Z)
    (hfull : ∀ i ∈ left, c i ≠ 0 → A.exteriorNorm (fullI i) ≤ Z ^ total)
    (i : ι)
    (hi : i ∈ ((p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)).columns)
    (hc : ((p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)).coefficient i ≠ 0) :
    A.exteriorNorm (((p.divisorPools.leftData S).mainSource
      (p.leftDivisorCoefficient S χ)).ideal i) ≤ Z ^ (total - idealLogLength Z DE.1) := by
  have hi' : i ∈ b.leftColumns left := by
    simpa only [FirstGaussPoolData.mainSource, p.divisorPools.left_columns S,
      p.left_columns] using hi
  have hci := p.canonicalLeft_nonzero_original hΓ μv ν b C left right φ c e finiteTest
    hlc hcs radius D δ hδ hδhalf S χ i hc
  change A.exteriorNorm ((p.divisorPools.leftData S).ideal i) ≤ _
  rw [p.divisorPools.left_ideal S, p.left_ideal]
  exact b.leftResidual_norm_window left Z total hZ i hi'
    (hfull i (Finset.mem_filter.mp hi').1 hci)

theorem canonicalRightMain_active_norm_window (Z total : ℝ) (hZ : 1 < Z)
    (hfull : ∀ j ∈ right, e j ≠ 0 → A.exteriorNorm (fullJ j) ≤ Z ^ total)
    (j : κ)
    (hj : j ∈ ((p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)).columns)
    (hc : ((p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)).coefficient j ≠ 0) :
    A.exteriorNorm (((p.divisorPools.rightData S).mainSource
      (p.rightDivisorCoefficient S χ)).ideal j) ≤ Z ^ (total - idealLogLength Z DE.2) := by
  have hj' : j ∈ b.rightColumns right := by
    simpa only [FirstGaussPoolData.mainSource, p.divisorPools.right_columns S,
      p.right_columns] using hj
  have hcj := p.canonicalRight_nonzero_original hΓ μv ν b C left right φ c e finiteTest
    hlc hcs radius D δ hδ hδhalf S χ j hc
  change A.exteriorNorm ((p.divisorPools.rightData S).ideal j) ≤ _
  rw [p.divisorPools.right_ideal S, p.right_ideal]
  exact b.rightResidual_norm_window right Z total hZ j hj'
    (hfull j (Finset.mem_filter.mp hj').1 hcj)

/-- Every actual valuation error pays its entire original prime power,
including powers one, six and seven. No source-nonempty hypothesis is
needed for this single-column implication. -/
theorem canonicalLeftPool_active_norm_window (Z total : ℝ) (hZ : 1 < Z)
    (hfull : ∀ i ∈ left, c i ≠ 0 → A.exteriorNorm (fullI i) ≤ Z ^ total)
    (prime : ExteriorPrime A) (n : ℕ)
    (i : (p.divisorPools.leftData S).valuationColumns prime n)
    (hc : ((p.divisorPools.leftData S).residualSource prime n
      (p.leftDivisorCoefficient S χ)).coefficient i ≠ 0) :
    A.exteriorNorm (((p.divisorPools.leftData S).residualSource prime n
      (p.leftDivisorCoefficient S χ)).ideal i) ≤
      Z ^ (total - idealLogLength Z DE.1 - idealLogLength Z (powerIdeal prime n).val) := by
  have hci : p.leftDivisorCoefficient S χ i.val ≠ 0 := by
    intro hzero
    apply hc
    change (p.divisorPools.leftData S).residualCoefficient prime n
      (p.leftDivisorCoefficient S χ) i = 0
    rw [FirstGaussPoolData.residualCoefficient_eq, hzero, zero_mul, zero_mul]
  have hpre := p.canonicalLeftMain_active_norm_window hΓ μv ν b C left right φ c e
    finiteTest hlc hcs radius D δ hδ hδhalf S χ Z total hZ hfull i.val
    (Finset.mem_filter.mp i.property).1 hci
  let R := (p.divisorPools.leftData S).residualPresentation prime n i
  exact reconstructed_exterior_norm_window ((p.divisorPools.leftData S).ideal i.val)
    (powerIdeal prime n) R.residual R.reconstructed Z
    (total - idealLogLength Z DE.1) hZ hpre

theorem canonicalRightPool_active_norm_window (Z total : ℝ) (hZ : 1 < Z)
    (hfull : ∀ j ∈ right, e j ≠ 0 → A.exteriorNorm (fullJ j) ≤ Z ^ total)
    (prime : ExteriorPrime A) (n : ℕ)
    (j : (p.divisorPools.rightData S).valuationColumns prime n)
    (hc : ((p.divisorPools.rightData S).residualSource prime n
      (p.rightDivisorCoefficient S χ)).coefficient j ≠ 0) :
    A.exteriorNorm (((p.divisorPools.rightData S).residualSource prime n
      (p.rightDivisorCoefficient S χ)).ideal j) ≤
      Z ^ (total - idealLogLength Z DE.2 - idealLogLength Z (powerIdeal prime n).val) := by
  have hcj : p.rightDivisorCoefficient S χ j.val ≠ 0 := by
    intro hzero
    apply hc
    change (p.divisorPools.rightData S).residualCoefficient prime n
      (p.rightDivisorCoefficient S χ) j = 0
    rw [FirstGaussPoolData.residualCoefficient_eq, hzero, zero_mul, zero_mul]
  have hpre := p.canonicalRightMain_active_norm_window hΓ μv ν b C left right φ c e
    finiteTest hlc hcs radius D δ hδ hδhalf S χ Z total hZ hfull j.val
    (Finset.mem_filter.mp j.property).1 hcj
  let R := (p.divisorPools.rightData S).residualPresentation prime n j
  exact reconstructed_exterior_norm_window ((p.divisorPools.rightData S).ideal j.val)
    (powerIdeal prime n) R.residual R.reconstructed Z
    (total - idealLogLength Z DE.2) hZ hpre

end FirstBlockPoolData
end CanonicalFirst
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.reconstructed_exterior_norm_window
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.canonicalLeft_active_norm_window
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.canonicalLeftMain_active_norm_window
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.canonicalLeftPool_active_norm_window
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.canonicalRightPool_active_norm_window
