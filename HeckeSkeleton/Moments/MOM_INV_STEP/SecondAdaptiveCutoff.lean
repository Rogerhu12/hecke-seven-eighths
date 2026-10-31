import HeckeSkeleton.Moments.MOM_INV_STEP.SecondPoissonSplit
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondSourceMasks
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalAdaptiveTail
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalNormPools

/-!
# The second cutoff frozen with the actual common ideal and divisor

The common ideal is computed from the original fresh pair. The retained
frequencies satisfy the source-local bound 16 r N(d₂) (X/N(g))² Z^τ.
The exact second Poisson identity, both additive zero terms and every
sector of the original unit subgroup are unchanged by this truncation.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondAdaptiveCutoff

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
  HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools ActualInverseFactors
  ActualDivisorSectors SecondSourceMasks SecondSourceGauss FirstInversePoisson
  PrimitivePoissonSource ConductorMasks ActualPoissonScale
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "e" => unitIdeal K S

/-- Sixteen accounts for the complete source pool N(x) ≤ 4X. -/
def fineScale (r : {r : ℝ // 0 < r}) (X : ℝ) (g : Ext)
    (δ : Finset (HeightOneSpectrum OS)) : ℝ :=
  16 * r.val * (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val *
    (X / height K Sset g) ^ 2

def fineCutoff (r : {r : ℝ // 0 < r}) (X Z tau : ℝ) (g : Ext)
    (δ : Finset (HeightOneSpectrum OS)) : ℝ :=
  fineScale K S r X g δ * Z ^ tau

theorem fineScale_pos (r : {r : ℝ // 0 < r}) (X : ℝ) (hX : 0 < X)
    (g : Ext) (δ : Finset (HeightOneSpectrum OS)) :
    0 < fineScale K S r X g δ := by
  unfold fineScale
  exact mul_pos (mul_pos (mul_pos (by norm_num) r.property)
    (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).property)
    (sq_pos_of_pos (div_pos hX (height_pos K Sset g)))

theorem residual_height (x₁ x₂ : Ext) (hx₁ : Squarefree x₁.val.val) :
    height K Sset (ActualInverseFactors.residual K Sset x₁ x₂) =
      height K Sset x₁ / height K Sset (common K Sset x₁ x₂) := by
  apply (eq_div_iff (height_pos K Sset _).ne').mpr
  rw [mul_comm, ← height_mul, common_mul_residual K Sset x₁ x₂ hx₁]

theorem primitive_conductor_norm (x₁ x₂ : Ext) :
    ((primitiveIdeal (pairSupport K S D x₁ x₂ e e).support
      (pairExponent K S x₁ x₂ e e)).absNorm : ℝ) =
      height K Sset (ActualInverseFactors.residual K Sset x₁ x₂) *
        height K Sset (ActualInverseFactors.residual K Sset x₂ x₁) := by
  rw [primitive_conductor, map_mul, Nat.cast_mul]
  rfl

/-- The actual denominator of the dual radius is bounded by the
frozen common/divisor scale, before any frequency is selected. -/
theorem radius_denominator_le_fineScale (x₁ x₂ : Ext)
    (hx₁ : Squarefree x₁.val.val) (hx₂ : Squarefree x₂.val.val)
    (r : {r : ℝ // 0 < r}) (X : ℝ) (hX : 0 < X)
    (hx₁N : height K Sset x₁ ≤ 4 * X) (hx₂N : height K Sset x₂ ≤ 4 * X)
    (δ : Finset (HeightOneSpectrum OS)) :
    r.val * (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val *
      ((primitiveIdeal (pairSupport K S D x₁ x₂ e e).support
        (pairExponent K S x₁ x₂ e e)).absNorm : ℝ) ≤
      fineScale K S r X (common K Sset x₁ x₂) δ := by
  have hg := height_pos K Sset (common K Sset x₁ x₂)
  have h₁ : height K Sset (ActualInverseFactors.residual K Sset x₁ x₂) ≤
      4 * X / height K Sset (common K Sset x₁ x₂) := by
    rw [residual_height K S x₁ x₂ hx₁]
    exact div_le_div_of_nonneg_right hx₁N hg.le
  have h₂ : height K Sset (ActualInverseFactors.residual K Sset x₂ x₁) ≤
      4 * X / height K Sset (common K Sset x₁ x₂) := by
    rw [residual_height K S x₂ x₁ hx₂, common_comm K Sset x₂ x₁]
    exact div_le_div_of_nonneg_right hx₂N hg.le
  rw [primitive_conductor_norm]
  calc
    _ ≤ r.val * (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val *
        ((4 * X / height K Sset (common K Sset x₁ x₂)) *
          (4 * X / height K Sset (common K Sset x₁ x₂))) := by
      apply mul_le_mul_of_nonneg_left _
        (mul_pos r.property (sIntegerElementNorm K Sset _).property).le
      exact mul_le_mul h₁ h₂ (height_pos K Sset _).le (by positivity)
    _ = _ := by unfold fineScale; ring

theorem fineCutoff_scaled_lower (x₁ x₂ : Ext)
    (hx₁ : Squarefree x₁.val.val) (hx₂ : Squarefree x₂.val.val)
    (r : {r : ℝ // 0 < r}) (X Z tau : ℝ) (hX : 0 < X) (hZ : 0 < Z)
    (hx₁N : height K Sset x₁ ≤ 4 * X) (hx₂N : height K Sset x₂ ≤ 4 * X)
    (δ : Finset (HeightOneSpectrum OS)) :
    Z ^ tau ≤
      (CanonicalAdaptiveTail.dualRadius K S D (pairSupport K S D x₁ x₂ e e)
        (pairExponent K S x₁ x₂ e e) r δ).val *
        fineCutoff K S r X Z tau (common K Sset x₁ x₂) δ := by
  let a := r.val * (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val *
    ((primitiveIdeal (pairSupport K S D x₁ x₂ e e).support
      (pairExponent K S x₁ x₂ e e)).absNorm : ℝ)
  have ha : 0 < a := by
    exact mul_pos (mul_pos r.property (sIntegerElementNorm K Sset _).property)
      (by
        exact_mod_cast (Ideal.absNorm_pos_of_nonZeroDivisors
          (primitiveExterior K S (pairSupport K S D x₁ x₂ e e)
            (pairExponent K S x₁ x₂ e e)).val))
  have hb : a ≤ fineScale K S r X (common K Sset x₁ x₂) δ :=
    radius_denominator_le_fineScale K S D x₁ x₂ hx₁ hx₂ r X hX hx₁N hx₂N δ
  have hunit : 1 ≤ a⁻¹ * fineScale K S r X (common K Sset x₁ x₂) δ := by
    rw [← div_eq_inv_mul]
    exact (one_le_div ha).mpr hb
  have hc := mul_le_mul_of_nonneg_right hunit (Real.rpow_nonneg hZ.le tau)
  simpa only [CanonicalAdaptiveTail.dualRadius, primitive_dual_radius,
    fineCutoff, one_mul, mul_assoc, a] using hc

theorem divisor_norm_le_common (g : Ext) (hg : Squarefree g.val.val)
    (δ : Finset (HeightOneSpectrum OS)) (hδ : δ ⊆ commonMask K S D g) :
    (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val ≤ height K Sset g := by
  rw [← divisorIdeal_norm]
  exact FirstMaskGeometry.absNorm_le_of_dvd K _ _ (nonZeroDivisors.coe_ne_zero g.val)
    (actual_divisor_dvd K S D g hg δ hδ)

theorem fineScale_le (r : {r : ℝ // 0 < r}) (X : ℝ)
    (g : Ext) (hg : Squarefree g.val.val) (δ : Finset (HeightOneSpectrum OS))
    (hδ : δ ⊆ commonMask K S D g) : fineScale K S r X g δ ≤ 16 * r.val * X ^ 2 := by
  have hg0 := height_pos K Sset g
  have hd : (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val ≤
      height K Sset g * height K Sset g :=
    (divisor_norm_le_common K S D g hg δ hδ).trans
      (le_mul_of_one_le_right hg0.le (height_one_le K Sset g))
  have he : (r.val * (X / height K Sset g) ^ 2) *
      (height K Sset g * height K Sset g) = r.val * X ^ 2 := by
    field_simp [hg0.ne']
    <;> ring
  calc
    _ = 16 * ((r.val * (X / height K Sset g) ^ 2) *
        (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val) := by
      unfold fineScale
      ring
    _ ≤ 16 * ((r.val * (X / height K Sset g) ^ 2) *
        (height K Sset g * height K Sset g)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hd
          (mul_nonneg r.property.le (sq_nonneg _))) (by norm_num)
    _ = _ := by rw [he]; ring

theorem actual_radius_lower (x₁ x₂ : Ext)
    (hx₁ : Squarefree x₁.val.val) (hx₂ : Squarefree x₂.val.val)
    (r : {r : ℝ // 0 < r}) (X Z Rmax : ℝ) (hX : 0 < X) (hZ : 0 < Z)
    (hx₁N : height K Sset x₁ ≤ 4 * X) (hx₂N : height K Sset x₂ ≤ 4 * X)
    (δ : Finset (HeightOneSpectrum OS))
    (hδ : δ ⊆ commonMask K S D (common K Sset x₁ x₂))
    (hbudget : 16 * r.val * X ^ 2 ≤ Z ^ Rmax) :
    Z ^ (-Rmax) ≤
      (CanonicalAdaptiveTail.dualRadius K S D (pairSupport K S D x₁ x₂ e e)
        (pairExponent K S x₁ x₂ e e) r δ).val := by
  apply primitive_dual_radius_lower K S D _ _ r _ Z Rmax hZ
  exact (radius_denominator_le_fineScale K S D x₁ x₂ hx₁ hx₂ r X hX hx₁N hx₂N δ).trans
    ((fineScale_le K S D r X _ (common_squarefree K Sset x₁ x₂) δ hδ).trans hbudget)

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

def retainedSourceAt (a : Ext → ℂ) (P : Finset (Ext × Ext)) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (r : {r : ℝ // 0 < r}) (H : Ext → Finset (HeightOneSpectrum OS) → ℝ) : ℂ :=
  ∑ p ∈ P, SecondPoissonSplit.sourceWeight K S a p *
    CanonicalAdaptiveTail.retainedDual K S D Γ μv
      (SecondPoissonSplit.pairBlock K S D Γ hΓ p φ h hlc hcs r)
      (H (common K Sset p.1 p.2))

def tailSourceAt (a : Ext → ℂ) (P : Finset (Ext × Ext)) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (r : {r : ℝ // 0 < r}) (H : Ext → Finset (HeightOneSpectrum OS) → ℝ) : ℂ :=
  ∑ p ∈ P, SecondPoissonSplit.sourceWeight K S a p *
    CanonicalAdaptiveTail.dualTail K S D Γ μv
      (SecondPoissonSplit.pairBlock K S D Γ hΓ p φ h hlc hcs r)
      (H (common K Sset p.1 p.2))

theorem nonprincipalRetainedAt_eq_sub (a : Ext → ℂ) (T : Finset Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (r : {r : ℝ // 0 < r}) (H : Ext → Finset (HeightOneSpectrum OS) → ℝ) :
    retainedSourceAt K S D Γ hΓ μv a (SecondPoissonSplit.nonprincipalPairs K S D T)
      φ h hlc hcs r H =
      retainedSourceAt K S D Γ hΓ μv a (T ×ˢ T) φ h hlc hcs r H -
        retainedSourceAt K S D Γ hΓ μv a (SecondPoissonSplit.principalPairs K S D T)
          φ h hlc hcs r H := by
  unfold retainedSourceAt SecondPoissonSplit.nonprincipalPairs
  exact Finset.sum_sdiff_eq_sub (SecondPoissonSplit.principalPairs_subset K S D T)

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

include ν in
theorem pair_transformed_head_tail_at (p : Ext × Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (r : {r : ℝ // 0 < r}) (H : Finset (HeightOneSpectrum OS) → ℝ) :
    (SecondPoissonSplit.pairBlock K S D Γ hΓ p φ h hlc hcs r).transformed
        μv D.different_outside =
      CanonicalAdaptiveTail.retainedDual K S D Γ μv
        (SecondPoissonSplit.pairBlock K S D Γ hΓ p φ h hlc hcs r) H +
      CanonicalPoissonSplit.pairPrincipal K S D Γ hΓ μv
        (e, p.1) (e, p.2) φ h hlc hcs ∅ r +
      CanonicalAdaptiveTail.dualTail K S D Γ μv
        (SecondPoissonSplit.pairBlock K S D Γ hΓ p φ h hlc hcs r) H := by
  rw [CanonicalPoissonSplit.pair_transformed_split K S D Γ hΓ μv
    (e, p.1) (e, p.2) φ h hlc hcs ∅ r,
    CanonicalAdaptiveTail.nonzeroDual_eq_retained_add_tail K S D Γ μv ν _ H]
  ring

variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
theorem physicalPrincipal_eq_retained_add_zeros_add_tail_at
    (a : Ext → ℂ) (T : Finset Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (r : {r : ℝ // 0 < r}) (H : Ext → Finset (HeightOneSpectrum OS) → ℝ) :
    SecondPoissonSplit.physicalPrincipal K S D Γ hΓ a T φ h hlc hcs r =
      retainedSourceAt K S D Γ hΓ μv a (SecondPoissonSplit.principalPairs K S D T)
        φ h hlc hcs r H +
      SecondPoissonSplit.additiveZeros K S D Γ hΓ μv a T φ h hlc hcs r +
      tailSourceAt K S D Γ hΓ μv a (SecondPoissonSplit.principalPairs K S D T)
        φ h hlc hcs r H := by
  rw [SecondPoissonSplit.additiveZeros_eq_principalPairs]
  unfold SecondPoissonSplit.physicalPrincipal retainedSourceAt tailSourceAt
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [ActualMaskedPoissonBlock.physical_eq_transformed μv D.different_outside ν μ,
    pair_transformed_head_tail_at K S D Γ hΓ μv ν p φ h hlc hcs r
      (H (common K Sset p.1 p.2))]
  ring

variable {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

include ν μ in
/-- Genuine second Poisson with an independently frozen cutoff for
each actual original common ideal and actual divisor. -/
theorem genuine_second_split_at (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (j : Ideal (𝓞 K)) (d : OS) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (r : {r : ℝ // 0 < r}) (H : Ext → Finset (HeightOneSpectrum OS) → ℝ) :
    DivisorInverseColumn.weightedEnergy K S Γ D C γ j d φ h ∅ r =
      retainedSourceAt K S D Γ hΓ μv (DivisorInverseColumn.coefficient K S D C γ j d)
        (C.columns γ ×ˢ C.columns γ) φ h hlc hcs r H +
      SecondPoissonSplit.additiveZeros K S D Γ hΓ μv
        (DivisorInverseColumn.coefficient K S D C γ j d) (C.columns γ) φ h hlc hcs r +
      tailSourceAt K S D Γ hΓ μv (DivisorInverseColumn.coefficient K S D C γ j d)
        (C.columns γ ×ˢ C.columns γ) φ h hlc hcs r H := by
  rw [DivisorInverseColumn.genuine_second_poisson K S Γ D hΓ μv ν μ
    C γ j d φ h hlc hcs ∅ r]
  unfold retainedSourceAt tailSourceAt SecondPoissonSplit.additiveZeros
    SecondPoissonSplit.sourceWeight
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  change star (DivisorInverseColumn.coefficient K S D C γ j d p.1) *
    DivisorInverseColumn.coefficient K S D C γ j d p.2 *
    (SecondPoissonSplit.pairBlock K S D Γ hΓ p φ h hlc hcs r).transformed
      μv D.different_outside = _
  rw [pair_transformed_head_tail_at K S D Γ hΓ μv ν p φ h hlc hcs r
    (H (common K Sset p.1 p.2))]
  ring

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondAdaptiveCutoff

end
