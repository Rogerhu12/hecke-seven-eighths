import HeckeSkeleton.Moments.MOM_INV_STEP.FirstAdaptiveTruncation
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedEnergy

/-!
# Actual first-source cutoffs after extraction

The cutoff is frozen with the cube pair, the computed extraction key,
and the actual mask divisor. Its normalization is obtained from the
original dyadic columns and their exact ideal factorization.
-/

noncomputable section
namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedCutoff
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  MeasureTheory
open PrimitivePoissonSource ConductorMasks FirstSourceColumns FirstSourceFrozen
  FirstNormPoolEnergy FirstPoissonNormalization FirstCommonEnvelope ActualPoissonScale
  CanonicalNormPools FirstParentRows
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset

def fineCutoff (r X : {r : ℝ // 0 < r}) (Z tau : ℝ)
    (n₁ n₂ b₁ b₂ : Ext) (δ : Finset (HeightOneSpectrum OS)) : ℝ :=
  4 * FirstCommonEnvelope.radialScale K S D r (sIntegerMaskGenerator K Sset δ)
    n₁ n₂ b₁ b₂ (residualScale K S X n₁ n₂ b₁ b₂ false)
      (residualScale K S X n₁ n₂ b₁ b₂ true) * Z ^ tau

theorem fineCutoff_pos (r X : {r : ℝ // 0 < r}) (Z tau : ℝ) (hZ : 0 < Z)
    (n₁ n₂ b₁ b₂ : Ext) (δ : Finset (HeightOneSpectrum OS)) :
    0 < fineCutoff K S D r X Z tau n₁ n₂ b₁ b₂ δ :=
  mul_pos (mul_pos (by norm_num)
    (FirstCommonEnvelope.radialScale_pos K S D r (sIntegerMaskGenerator K Sset δ)
      n₁ n₂ b₁ b₂ _ _)) (Real.rpow_pos_of_pos hZ tau)

theorem fineCutoff_frozen (r X : {r : ℝ // 0 < r}) (Z tau : ℝ)
    (n₁ n₂ r₁ r₂ b₁ b₂ : Ext)
    (hs : SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂) :
    fineCutoff K S D r X Z tau n₁ n₂ b₁ b₂ =
      fineCutoff K S D r X Z tau r₁ r₂ b₁ b₂ := by
  funext δ
  unfold fineCutoff FirstCommonEnvelope.radialScale residualScale
  rw [cubeNorm_eq K S D n₁ n₂ r₁ r₂ b₁ b₂ hs]
  simp only [extractedFactor_eq K S n₁ n₂ r₁ r₂ b₁ b₂ hs false,
    extractedFactor_eq K S n₁ n₂ r₁ r₂ b₁ b₂ hs true]

theorem residual_height_le (X : {r : ℝ // 0 < r}) (n₁ n₂ r₁ r₂ b₁ b₂ : Ext)
    (hn₁ : n₁ ∈ dyadicPool K Sset X.val) (hn₂ : n₂ ∈ dyadicPool K Sset X.val)
    (hs : SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂) (side : Bool) :
    ((residualIdeal K S D n₁ n₂ b₁ b₂ side).val.val.absNorm : ℝ) ≤
      2 * (residualScale K S X r₁ r₂ b₁ b₂ side).val := by
  have hsf₁ := dyadicPool_squarefree K Sset hn₁
  have hsf₂ := dyadicPool_squarefree K Sset hn₂
  have he := congrArg (fun n : Ext => n.val.val.absNorm)
    (source_factorization K S D n₁ n₂ b₁ b₂ hsf₁ hsf₂ side)
  change ((extractedFactor K S n₁ n₂ b₁ b₂ side).val.val *
    (residualIdeal K S D n₁ n₂ b₁ b₂ side).val.val).absNorm =
      (sourceIdeal K S n₁ n₂ side).val.val.absNorm at he
  have heR := congrArg (fun n : ℕ => (n : ℝ)) he
  rw [map_mul, Nat.cast_mul,
    extractedFactor_eq K S n₁ n₂ r₁ r₂ b₁ b₂ hs side] at heR
  have hsrc : ((sourceIdeal K S n₁ n₂ side).val.val.absNorm : ℝ) ≤ 2 * X.val := by
    cases side
    · exact ((mem_dyadicPool K Sset X.val n₁).mp hn₁).2.2
    · exact ((mem_dyadicPool K Sset X.val n₂).mp hn₂).2.2
  have hE : 0 < ((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val.absNorm : ℝ) := by
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors
      (extractedFactor K S r₁ r₂ b₁ b₂ side).val
  change _ ≤ 2 * (X.val / _)
  rw [show 2 * (X.val /
    ((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val.absNorm : ℝ)) =
      (2 * X.val) / ((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val.absNorm : ℝ) by ring]
  apply (le_div_iff₀ hE).mpr
  rw [mul_comm, heR]
  exact hsrc

/-- The literal primitive dual radius sees at least the requested
large argument beyond this fixed arithmetic cutoff. -/
theorem fineCutoff_argument (r X : {r : ℝ // 0 < r}) (Z tau : ℝ) (hZ : 0 < Z)
    (n₁ n₂ r₁ r₂ b₁ b₂ : Ext)
    (hn₁ : n₁ ∈ dyadicPool K Sset X.val) (hn₂ : n₂ ∈ dyadicPool K Sset X.val)
    (hs : SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂)
    (δ : Finset (HeightOneSpectrum OS)) :
    Z ^ tau ≤
      (CanonicalAdaptiveTail.dualRadius K S D (pairSupport K S D n₁ n₂ b₁ b₂)
        (pairExponent K S n₁ n₂ b₁ b₂) r δ).val *
      fineCutoff K S D r X Z tau r₁ r₂ b₁ b₂ δ := by
  let d := sIntegerMaskGenerator K Sset δ
  let u := ((residualIdeal K S D n₁ n₂ b₁ b₂ false).val.val.absNorm : ℝ)
  let v := ((residualIdeal K S D n₁ n₂ b₁ b₂ true).val.val.absNorm : ℝ)
  let XL := (residualScale K S X r₁ r₂ b₁ b₂ false).val
  let XR := (residualScale K S X r₁ r₂ b₁ b₂ true).val
  let R := cubeNorm K S D r₁ r₂ b₁ b₂
  have hu : 0 < u := Nat.cast_pos.mpr (Ideal.absNorm_pos_of_nonZeroDivisors
      (residualIdeal K S D n₁ n₂ b₁ b₂ false).val)
  have hv : 0 < v := Nat.cast_pos.mpr (Ideal.absNorm_pos_of_nonZeroDivisors
      (residualIdeal K S D n₁ n₂ b₁ b₂ true).val)
  have hprod : u * v ≤ (2 * XL) * (2 * XR) :=
    mul_le_mul (residual_height_le K S D X n₁ n₂ r₁ r₂ b₁ b₂ hn₁ hn₂ hs false)
      (residual_height_le K S D X n₁ n₂ r₁ r₂ b₁ b₂ hn₁ hn₂ hs true) hv.le
      (mul_pos (by norm_num) (residualScale K S X r₁ r₂ b₁ b₂ false).property).le
  have hR : 0 < R := cubeNorm_pos K S D r₁ r₂ b₁ b₂
  have hd := (sIntegerElementNorm K Sset d).property
  have hq : 0 < r.val * (sIntegerElementNorm K Sset d).val * (u * v * R) :=
    mul_pos (mul_pos r.property hd) (mul_pos (mul_pos hu hv) hR)
  have hb : r.val * (sIntegerElementNorm K Sset d).val * (u * v * R) ≤
      4 * (r.val * (sIntegerElementNorm K Sset d).val * R * XL * XR) := by
    have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hprod hR.le)
      (mul_pos r.property hd).le
    nlinarith [hh]
  rw [CanonicalAdaptiveTail.dualRadius, primitive_dual_radius, conductorNorm,
    cubeNorm_eq K S D n₁ n₂ r₁ r₂ b₁ b₂ hs]
  change Z ^ tau ≤ (r.val * (sIntegerElementNorm K Sset d).val * (u * v * R))⁻¹ *
    fineCutoff K S D r X Z tau r₁ r₂ b₁ b₂ δ
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hq).mpr
  have hh := mul_le_mul_of_nonneg_left hb (Real.rpow_pos_of_pos hZ tau).le
  dsimp only [fineCutoff, FirstCommonEnvelope.radialScale, XL, XR, R, d] at *
  nlinarith [hh]

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable {σ : Type*}

/-- This function is chosen before all original labels and all retained
frequency ideals and sectors. -/
def sourceCutoff (T : FirstParentEnergy.Data K S (σ := σ)) (Z tau : ℝ) (hZ : 0 < Z)
    (o : OuterIndex K S D T) : {r : ℝ // 0 < r} :=
  ⟨fineCutoff K S D T.radius T.scale Z tau
    (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val o.2.2.2.val,
    fineCutoff_pos K S D T.radius T.scale Z tau hZ _ _ _ _ _⟩

theorem sourceCutoff_eq (T : FirstParentEnergy.Data K S (σ := σ))
    (Z tau : ℝ) (hZ : 0 < Z) (o : OuterIndex K S D T) :
    (sourceCutoff K S D T Z tau hZ o).val =
      4 * FirstLocalizedEnergy.radialScale K S D T o * Z ^ tau := rfl

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedCutoff
end

