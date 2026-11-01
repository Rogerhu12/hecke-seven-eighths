import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCappedProduction

/-!
# Restoring a common cube-coefficient normalization

A divisor-bounded cube coefficient is divided by one positive common
bound before applying the published provider. The operation changes
only the old cube/label weight. Its squared norm factor is restored
exactly outside the original orbital energy.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderHomogeneity

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOM_INV_STEP
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
variable {σ : Type*}

def scaleColumns (C : CanonicalBlock.ColumnData K S σ) (a : ℂ) :
    CanonicalBlock.ColumnData K S σ :=
  { C with labelWeight := fun b f => a * C.labelWeight b f }

def scaleParent (T : FirstParentEnergy.Data K S (σ := σ)) (a : ℂ) :
    FirstParentEnergy.Data K S (σ := σ) :=
  { T with columns := scaleColumns K S T.columns a }

variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

theorem canonicalColumn_scale (C : CanonicalBlock.ColumnData K S σ)
    (a : ℂ) (f b n : Ext) :
    CanonicalBlock.canonicalColumn K S D (scaleColumns K S C a) f b n =
      a * CanonicalBlock.canonicalColumn K S D C f b n := by
  unfold CanonicalBlock.canonicalColumn scaleColumns
  ring

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

/-- Scaling the actual old cube/label coefficient scales the entire
original orbital series by the squared norm, before any Poisson step. -/
theorem parent_scale (T : FirstParentEnergy.Data K S (σ := σ))
    (a : ℂ) (f : Ext) :
    FirstCappedProduction.parent K S D Γ (scaleParent K S T a) f =
      ((‖a‖ ^ 2 : ℝ) : ℂ) * FirstCappedProduction.parent K S D Γ T f := by
  unfold FirstCappedProduction.parent CanonicalBlock.canonicalCubeEnergy
    CanonicalPoissonSource.squaredRowOrbitalSeries sIntegerWeightedOrbitalSeries
  rw [← tsum_mul_left]
  apply tsum_congr
  intro q
  have hs :
      (∑ i ∈ T.cubes ×ˢ FirstParentEnergy.columnPool K S T,
        CanonicalBlock.canonicalColumn K S D (scaleColumns K S T.columns a) f i.1 i.2 *
          (idealSymbol K Sset D i.1 q.out.val ^ 3 *
            idealSymbol K Sset D i.2 q.out.val)) =
        a * ∑ i ∈ T.cubes ×ˢ FirstParentEnergy.columnPool K S T,
          CanonicalBlock.canonicalColumn K S D T.columns f i.1 i.2 *
            (idealSymbol K Sset D i.1 q.out.val ^ 3 *
              idealSymbol K Sset D i.2 q.out.val) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [canonicalColumn_scale]
    ring
  dsimp only [scaleParent, FirstParentEnergy.columnPool] at hs ⊢
  rw [hs, norm_mul, mul_pow, Complex.ofReal_mul]
  ring

theorem parent_norm_scale (T : FirstParentEnergy.Data K S (σ := σ))
    (a : ℂ) (f : Ext) :
    ‖FirstCappedProduction.parent K S D Γ (scaleParent K S T a) f‖ =
      ‖a‖ ^ 2 * ‖FirstCappedProduction.parent K S D Γ T f‖ := by
  rw [parent_scale, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]

/-- Dividing a common bound out of the cube coefficient makes the
provider's coefficient bound one; it is independent of the live row
and squarefree column. -/
theorem normalized_weight_le_one (T : FirstParentEnergy.Data K S (σ := σ))
    (B : ℝ) (hB : 0 < B) (b f : Ext) (hw : ‖T.columns.labelWeight b f‖ ≤ B) :
    ‖(scaleParent K S T (B : ℂ)⁻¹).columns.labelWeight b f‖ ≤ 1 := by
  change ‖(B : ℂ)⁻¹ * T.columns.labelWeight b f‖ ≤ 1
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hB.le]
  calc
    B⁻¹ * ‖T.columns.labelWeight b f‖ ≤ B⁻¹ * B :=
      mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr hB.le)
    _ = 1 := inv_mul_cancel₀ hB.ne'

/-- The original energy is recovered by exactly one square of the
common cube-weight bound. -/
theorem parent_norm_restore (T : FirstParentEnergy.Data K S (σ := σ))
    (B : ℝ) (hB : 0 < B) (f : Ext) :
    ‖FirstCappedProduction.parent K S D Γ T f‖ =
      B ^ 2 * ‖FirstCappedProduction.parent K S D Γ
        (scaleParent K S T (B : ℂ)⁻¹) f‖ := by
  rw [parent_norm_scale, norm_inv, Complex.norm_real, Real.norm_of_nonneg hB.le,
    inv_pow, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hB.ne'), one_mul]

theorem weighted_parent_restore (T : FirstParentEnergy.Data K S (σ := σ))
    (B : ℝ) (hB : 0 < B) (labels : Finset Ext) (w : Ext → ℝ) :
    (∑ f ∈ labels, w f * ‖FirstCappedProduction.parent K S D Γ T f‖) =
      B ^ 2 * ∑ f ∈ labels, w f * ‖FirstCappedProduction.parent K S D Γ
        (scaleParent K S T (B : ℂ)⁻¹) f‖ := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  rw [parent_norm_restore K S D Γ T B hB f]
  ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderHomogeneity

end
