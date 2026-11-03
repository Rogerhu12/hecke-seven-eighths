import HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentCentering
import HeckeSkeleton.Moments.MOM_INV_STEP.JointMaskGeometry

/-!
# The common first Fourier envelope has a uniform small-power cost

The active cube conductor is a factor of the actual primitive conductor.
Its product with the actual mask divisor is bounded by one source
support. The original dyadic pool and the true residual scales then
bound the scalar multiplying the common Fourier envelope. No frequency,
old cube label, unit sector or reconstruction row enters the final cost.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentRadialBudget

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  MeasureTheory
open FirstPoissonNormalization FirstSourceColumns FirstNormPoolEnergy FirstExtractedGeometry
  FirstParentEnergy FirstParentCentering CanonicalNormPools PrimitivePoissonSource ConductorMasks
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset

theorem cubeNorm_le_primitiveNorm (r₁ r₂ b₁ b₂ : Ext) :
    cubeNorm K S D r₁ r₂ b₁ b₂ ≤
      ((primitiveIdeal (pairSupport K S D r₁ r₂ b₁ b₂).support
        (pairExponent K S r₁ r₂ b₁ b₂)).absNorm : ℝ) := by
  rw [conductorNorm]
  have h₁ := height_one_le K Sset (residualIdeal K S D r₁ r₂ b₁ b₂ false)
  have h₂ := height_one_le K Sset (residualIdeal K S D r₁ r₂ b₁ b₂ true)
  exact le_mul_of_one_le_left (cubeNorm_pos K S D r₁ r₂ b₁ b₂).le
    (one_le_mul_of_one_le_of_one_le h₁ h₂)

theorem mask_mul_cubeNorm_le (Q r₁ r₂ b₁ b₂ : Ext)
    (δ : Finset (HeightOneSpectrum OS))
    (hδ : δ ⊆ FirstMaskGeometry.actualMask K S D Q r₁ r₂ b₁ b₂) :
    (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val *
      cubeNorm K S D r₁ r₂ b₁ b₂ ≤
    (Q.val.val.absNorm : ℝ) * (b₁.val.val.absNorm : ℝ) * (b₂.val.val.absNorm : ℝ) *
      (r₁.val.val.absNorm : ℝ) * (r₂.val.val.absNorm : ℝ) :=
  (mul_le_mul_of_nonneg_left (cubeNorm_le_primitiveNorm K S D r₁ r₂ b₁ b₂)
    (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).property.le).trans
    (JointMaskGeometry.actual_norm_product_bound K S D Q r₁ r₂ b₁ b₂ δ hδ)

/-- The source's own annulus, rather than a separate radial-envelope
hypothesis, controls the scalar in the common Fourier density bound. -/
theorem radialScale_le_source (Q r₁ r₂ b₁ b₂ : Ext)
    (δ : Finset (HeightOneSpectrum OS))
    (hδ : δ ⊆ FirstMaskGeometry.actualMask K S D Q r₁ r₂ b₁ b₂)
    (r X : {r : ℝ // 0 < r})
    (hr₁ : r₁ ∈ dyadicPool K Sset X.val) (hr₂ : r₂ ∈ dyadicPool K Sset X.val) :
    FirstCommonEnvelope.radialScale K S D r (sIntegerMaskGenerator K Sset δ)
      r₁ r₂ b₁ b₂ (residualScale K S X r₁ r₂ b₁ b₂ false)
        (residualScale K S X r₁ r₂ b₁ b₂ true) ≤
      4 * r.val * (Q.val.val.absNorm : ℝ) * (b₁.val.val.absNorm : ℝ) *
        (b₂.val.val.absNorm : ℝ) * X.val ^ 4 := by
  have hn₁ : (r₁.val.val.absNorm : ℝ) ≤ 2 * X.val :=
    ((mem_dyadicPool K Sset X.val r₁).mp hr₁).2.2
  have hn₂ : (r₂.val.val.absNorm : ℝ) ≤ 2 * X.val :=
    ((mem_dyadicPool K Sset X.val r₂).mp hr₂).2.2
  have htwoX : (0 : ℝ) ≤ 2 * X.val :=
    mul_nonneg (by norm_num) X.property.le
  have hsrc : (Q.val.val.absNorm : ℝ) * (b₁.val.val.absNorm : ℝ) *
      (b₂.val.val.absNorm : ℝ) * (r₁.val.val.absNorm : ℝ) *
      (r₂.val.val.absNorm : ℝ) ≤
      (Q.val.val.absNorm : ℝ) * (b₁.val.val.absNorm : ℝ) *
        (b₂.val.val.absNorm : ℝ) * (2 * X.val) * (2 * X.val) := by
    gcongr
  have hmask := (mask_mul_cubeNorm_le K S D Q r₁ r₂ b₁ b₂ δ hδ).trans hsrc
  have hscales : (residualScale K S X r₁ r₂ b₁ b₂ false).val *
      (residualScale K S X r₁ r₂ b₁ b₂ true).val ≤ X.val ^ 2 := by
    simpa only [pow_two] using
      mul_le_mul (residualScale_le K S X r₁ r₂ b₁ b₂ false)
        (residualScale_le K S X r₁ r₂ b₁ b₂ true)
        (residualScale K S X r₁ r₂ b₁ b₂ true).property.le X.property.le
  calc
    _ = r.val * ((sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val *
        cubeNorm K S D r₁ r₂ b₁ b₂) *
        ((residualScale K S X r₁ r₂ b₁ b₂ false).val *
          (residualScale K S X r₁ r₂ b₁ b₂ true).val) := by
      unfold FirstCommonEnvelope.radialScale
      ring
    _ ≤ r.val * ((Q.val.val.absNorm : ℝ) * (b₁.val.val.absNorm : ℝ) *
        (b₂.val.val.absNorm : ℝ) * (2 * X.val) * (2 * X.val)) * X.val ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hmask r.property.le) hscales
        (mul_nonneg (residualScale K S X r₁ r₂ b₁ b₂ false).property.le
          (residualScale K S X r₁ r₂ b₁ b₂ true).property.le)
        (mul_nonneg r.property.le
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
                (Nat.cast_nonneg _)) htwoX) htwoX))
    _ = _ := by ring

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable {σ : Type*}

theorem selectedDivisor_mem (T : FirstParentEnergy.Data K S (σ := σ)) (Q : Ext)
    (hmask : T.mask = FirstMaskGeometry.externalMask K S Q)
    (i : FirstParentEnergy.Index K S D Γ T) :
    i.2.2.2.1.val ⊆ FirstMaskGeometry.actualMask K S D Q
      (selectedAnchor K S D Γ T i).1 (selectedAnchor K S D Γ T i).2 i.1.val i.2.1.val := by
  have hδ := Finset.mem_powerset.mp i.2.2.2.1.property
  change i.2.2.2.1.val ⊆ FirstParentRetained.actualMask K S D T.mask
    (selectedAnchor K S D Γ T i).1 (selectedAnchor K S D Γ T i).2 i.1.val i.2.1.val at hδ
  simpa only [FirstParentRetained.actualMask, hmask, FirstMaskGeometry.actualMask] using hδ

theorem parent_radialScale_le (T : FirstParentEnergy.Data K S (σ := σ)) (Q : Ext)
    (hmask : T.mask = FirstMaskGeometry.externalMask K S Q)
    (i : FirstParentEnergy.Index K S D Γ T) :
    FirstParentProduction.radialScale K S D Γ T i ≤
      4 * T.radius.val * (Q.val.val.absNorm : ℝ) * (i.1.val.val.val.absNorm : ℝ) *
        (i.2.1.val.val.val.absNorm : ℝ) * T.scale.val ^ 4 := by
  obtain ⟨h₁, h₂⟩ := FirstParentCentering.selectedAnchor_mem K S D Γ T i
  exact radialScale_le_source K S D Q _ _ _ _ i.2.2.2.1.val
    (selectedDivisor_mem K S D Γ T Q hmask i) T.radius T.scale h₁ h₂

theorem parent_radialScale_power_le (T : FirstParentEnergy.Data K S (σ := σ)) (Q : Ext)
    (hmask : T.mask = FirstMaskGeometry.externalMask K S Q)
    (Z R E B L ε : ℝ) (hZ : 0 < Z) (hε : 0 ≤ ε)
    (hr : T.radius.val ≤ Z ^ R) (hQ : (Q.val.val.absNorm : ℝ) ≤ Z ^ E)
    (hb : ∀ b ∈ T.cubes, (b.val.val.absNorm : ℝ) ≤ Z ^ B)
    (hX : T.scale.val ≤ Z ^ L) (i : FirstParentEnergy.Index K S D Γ T) :
    FirstParentProduction.radialScale K S D Γ T i ^ ε ≤
      4 ^ ε * Z ^ ((R + E + 2 * B + 4 * L) * ε) := by
  have h₁ := hb i.1.val i.1.property
  have h₂ := hb i.2.1.val i.2.1.property
  have hscale : 0 ≤ T.scale.val := T.scale.property.le
  have hbase : 4 * T.radius.val * (Q.val.val.absNorm : ℝ) *
      (i.1.val.val.val.absNorm : ℝ) * (i.2.1.val.val.val.absNorm : ℝ) * T.scale.val ^ 4 ≤
      4 * Z ^ (R + E + 2 * B + 4 * L) := by
    calc
      _ ≤ 4 * Z ^ R * Z ^ E * Z ^ B * Z ^ B * (Z ^ L) ^ 4 := by gcongr
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hZ.le]
        simp only [Nat.cast_ofNat]
        rw [show L * (4 : ℝ) = 4 * L by ring]
        simp only [Real.rpow_add hZ]
        rw [show (2 : ℝ) * B = B + B by ring, Real.rpow_add hZ]
        ring
  have hpos : 0 ≤ FirstParentProduction.radialScale K S D Γ T i :=
    (FirstCommonEnvelope.radialScale_pos K S D T.radius (selectedDivisor K S D Γ T i)
      _ _ _ _ _ _).le
  have hh := Real.rpow_le_rpow hpos
    ((parent_radialScale_le K S D Γ T Q hmask i).trans hbase) hε
  simpa only [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (Real.rpow_nonneg hZ.le _),
    ← Real.rpow_mul hZ.le] using hh

/-- A single arbitrarily small power pays for all first radial costs in
a bounded length range. Its epsilon and constant precede Z and every
original arithmetic source, coefficient family and final frequency. -/
theorem exists_uniform_small_power (lengthCap pi : ℝ)
    (hcap : 0 ≤ lengthCap) (hpi : 0 < pi) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ A : ℝ, 1 ≤ A ∧
      ∀ {σ₀ : Type*} (T : FirstParentEnergy.Data K S (σ := σ₀)) (Q : Ext),
      T.mask = FirstMaskGeometry.externalMask K S Q →
      ∀ Z R E B L : ℝ, 1 ≤ Z → R ≤ lengthCap → E ≤ lengthCap →
      B ≤ lengthCap → L ≤ lengthCap → T.radius.val ≤ Z ^ R →
      (Q.val.val.absNorm : ℝ) ≤ Z ^ E →
      (∀ b ∈ T.cubes, (b.val.val.absNorm : ℝ) ≤ Z ^ B) →
      T.scale.val ≤ Z ^ L → ∀ i : FirstParentEnergy.Index K S D Γ T,
        FirstParentProduction.radialScale K S D Γ T i ^ ε ≤ A * Z ^ pi := by
  let ε := pi / (8 * lengthCap + 1)
  have hden : 0 < 8 * lengthCap + 1 := by linarith
  have hε : 0 < ε := div_pos hpi hden
  refine ⟨ε, hε, 4 ^ ε, Real.one_le_rpow (by norm_num) hε.le, ?_⟩
  intro σ₀ T Q hmask Z R E B L hZ hR hE hB hL hr hQ hb hX i
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hexponent : (R + E + 2 * B + 4 * L) * ε ≤ pi := by
    have hsum : R + E + 2 * B + 4 * L ≤ 8 * lengthCap := by linarith
    have hratio : 8 * lengthCap / (8 * lengthCap + 1) ≤ 1 :=
      (div_le_iff₀ hden).mpr (by linarith)
    calc
      _ ≤ (8 * lengthCap) * ε := mul_le_mul_of_nonneg_right hsum hε.le
      _ = pi * (8 * lengthCap / (8 * lengthCap + 1)) := by dsimp only [ε]; ring
      _ ≤ pi * 1 := mul_le_mul_of_nonneg_left hratio hpi.le
      _ = pi := mul_one _
  exact (parent_radialScale_power_le K S D Γ T Q hmask Z R E B L ε hz hε.le
    hr hQ hb hX i).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hexponent)
      (Real.rpow_nonneg (by norm_num) ε))

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentRadialBudget

end
