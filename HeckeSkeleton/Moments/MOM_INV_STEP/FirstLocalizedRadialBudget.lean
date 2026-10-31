import HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentRadialBudget
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedEnergy

/-!
# Uniform radial cost for every actual frozen first-source index

This version uses no frequency membership or nonempty sector pool.
Consequently the same bound applies to every localized retained source,
to every old-label fiber and to its complete free row majorant.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedRadialBudget

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open CanonicalNormPools FirstParentRows FirstParentRadialBudget
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
variable {σ : Type*}

theorem selectedDivisor_mem (T : FirstParentEnergy.Data K S (σ := σ)) (Q : Ext)
    (hmask : T.mask = FirstMaskGeometry.externalMask K S Q)
    (o : OuterIndex K S D T) :
    o.2.2.2.val ⊆ FirstMaskGeometry.actualMask K S D Q
      (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val := by
  have hδ := Finset.mem_powerset.mp o.2.2.2.property
  change o.2.2.2.val ⊆ FirstParentRetained.actualMask K S D T.mask
    (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val at hδ
  simpa only [FirstParentRetained.actualMask, hmask, FirstMaskGeometry.actualMask] using hδ

theorem parent_radialScale_le (T : FirstParentEnergy.Data K S (σ := σ)) (Q : Ext)
    (hmask : T.mask = FirstMaskGeometry.externalMask K S Q)
    (o : OuterIndex K S D T) :
    FirstLocalizedEnergy.radialScale K S D T o ≤
      4 * T.radius.val * (Q.val.val.absNorm : ℝ) * (o.1.val.val.val.absNorm : ℝ) *
        (o.2.1.val.val.val.absNorm : ℝ) * T.scale.val ^ 4 := by
  obtain ⟨h₁, h₂⟩ := FirstOuterCenters.anchor_mem K S D T o
  exact radialScale_le_source K S D Q _ _ _ _ o.2.2.2.val
    (selectedDivisor_mem K S D T Q hmask o) T.radius T.scale h₁ h₂

theorem parent_radialScale_power_le (T : FirstParentEnergy.Data K S (σ := σ)) (Q : Ext)
    (hmask : T.mask = FirstMaskGeometry.externalMask K S Q)
    (Z R E B L ε : ℝ) (hZ : 0 < Z) (hε : 0 ≤ ε)
    (hr : T.radius.val ≤ Z ^ R) (hQ : (Q.val.val.absNorm : ℝ) ≤ Z ^ E)
    (hb : ∀ b ∈ T.cubes, (b.val.val.absNorm : ℝ) ≤ Z ^ B)
    (hX : T.scale.val ≤ Z ^ L) (i : OuterIndex K S D T) :
    FirstLocalizedEnergy.radialScale K S D T i ^ ε ≤
      4 ^ ε * Z ^ ((R + E + 2 * B + 4 * L) * ε) := by
  have h₁ := hb i.1.val i.1.property
  have h₂ := hb i.2.1.val i.2.1.property
  have hbase : 4 * T.radius.val * (Q.val.val.absNorm : ℝ) *
      (i.1.val.val.val.absNorm : ℝ) * (i.2.1.val.val.val.absNorm : ℝ) * T.scale.val ^ 4 ≤
      4 * Z ^ (R + E + 2 * B + 4 * L) := by
    calc
      _ ≤ 4 * Z ^ R * Z ^ E * Z ^ B * Z ^ B * (Z ^ L) ^ 4 := by
        have hscale : 0 ≤ T.scale.val := T.scale.property.le
        gcongr
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hZ.le]
        rw [show L * (4 : ℝ) = 4 * L by ring]
        simp only [Real.rpow_add hZ]
        rw [show (2 : ℝ) * B = B + B by ring, Real.rpow_add hZ]
        ring
  have hpos : 0 ≤ FirstLocalizedEnergy.radialScale K S D T i :=
    (FirstCommonEnvelope.radialScale_pos K S D T.radius (FirstLocalizedEnergy.divisor K S D T i)
      _ _ _ _ _ _).le
  have hh := Real.rpow_le_rpow hpos
    ((parent_radialScale_le K S D T Q hmask i).trans hbase) hε
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
      T.scale.val ≤ Z ^ L → ∀ i : OuterIndex K S D T,
        FirstLocalizedEnergy.radialScale K S D T i ^ ε ≤ A * Z ^ pi := by
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
  exact (parent_radialScale_power_le K S D T Q hmask Z R E B L ε hz hε.le
    hr hQ hb hX i).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hexponent)
      (Real.rpow_nonneg (by norm_num) ε))


end HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedRadialBudget

end

