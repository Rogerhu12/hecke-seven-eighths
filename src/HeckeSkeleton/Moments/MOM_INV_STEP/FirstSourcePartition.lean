import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalFirstEnergy

/-!
# Exact finite partition of the original columns by their extraction data

Keys are computed from the original pair. An anchor is chosen from the
same finite pair range, and is used only to name data proved constant on
that slice. No extra source-identification hypothesis is introduced.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstSourcePartition

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open FirstSourceDecomposition FirstSourceFrozen PrimitivePoissonSource
  CanonicalConductor ConductorMasks FirstSourceReindexing
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
abbrev Key := Finset (HeightOneSpectrum (𝓞 K)) ×
  Finset (HeightOneSpectrum (𝓞 K)) × Finset (HeightOneSpectrum (𝓞 K))

def key (b₁ b₂ n₁ n₂ : Ext) : Key K :=
  (extractedSupport n₁.val b₁.val b₂.val,
    extractedSupport n₂.val b₁.val b₂.val, commonSupport n₁.val n₂.val b₁.val b₂.val)

def keys (N₁ N₂ : Finset Ext) (b₁ b₂ : Ext) : Finset (Key K) :=
  (N₁ ×ˢ N₂).image (fun p => key K S b₁ b₂ p.1 p.2)

theorem key_mem (N₁ N₂ : Finset Ext) (b₁ b₂ n₁ n₂ : Ext)
    (hn₁ : n₁ ∈ N₁) (hn₂ : n₂ ∈ N₂) :
    key K S b₁ b₂ n₁ n₂ ∈ keys K S N₁ N₂ b₁ b₂ :=
  Finset.mem_image.mpr ⟨(n₁, n₂), Finset.mem_product.mpr ⟨hn₁, hn₂⟩, rfl⟩

theorem sameExtraction_iff_key (b₁ b₂ n₁ n₂ r₁ r₂ : Ext) :
    SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂ ↔
      key K S b₁ b₂ n₁ n₂ = key K S b₁ b₂ r₁ r₂ := by
  simp only [SameExtraction, key, Prod.mk.injEq]

theorem exists_anchor (N₁ N₂ : Finset Ext) (b₁ b₂ : Ext)
    (κ : keys K S N₁ N₂ b₁ b₂) :
    ∃ p : Ext × Ext, p.1 ∈ N₁ ∧ p.2 ∈ N₂ ∧ key K S b₁ b₂ p.1 p.2 = κ.val := by
  obtain ⟨p, hp, hk⟩ := Finset.mem_image.mp κ.property
  exact ⟨p, (Finset.mem_product.mp hp).1, (Finset.mem_product.mp hp).2, hk⟩

def anchor (N₁ N₂ : Finset Ext) (b₁ b₂ : Ext) (κ : keys K S N₁ N₂ b₁ b₂) : Ext × Ext :=
  Classical.choose (exists_anchor K S N₁ N₂ b₁ b₂ κ)

theorem anchor_mem (N₁ N₂ : Finset Ext) (b₁ b₂ : Ext)
    (κ : keys K S N₁ N₂ b₁ b₂) :
    (anchor K S N₁ N₂ b₁ b₂ κ).1 ∈ N₁ ∧
      (anchor K S N₁ N₂ b₁ b₂ κ).2 ∈ N₂ :=
  ⟨(Classical.choose_spec (exists_anchor K S N₁ N₂ b₁ b₂ κ)).1,
    (Classical.choose_spec (exists_anchor K S N₁ N₂ b₁ b₂ κ)).2.1⟩

theorem anchor_key (N₁ N₂ : Finset Ext) (b₁ b₂ : Ext)
    (κ : keys K S N₁ N₂ b₁ b₂) :
    key K S b₁ b₂ (anchor K S N₁ N₂ b₁ b₂ κ).1
      (anchor K S N₁ N₂ b₁ b₂ κ).2 = κ.val :=
  (Classical.choose_spec (exists_anchor K S N₁ N₂ b₁ b₂ κ)).2.2

theorem sum_extraction_slices (N₁ N₂ : Finset Ext) (b₁ b₂ : Ext)
    (w : Ext → Ext → ℂ) :
    (∑ n₁ ∈ N₁, ∑ n₂ ∈ N₂, w n₁ n₂) =
      ∑ κ : keys K S N₁ N₂ b₁ b₂, ∑ n₁ ∈ N₁, ∑ n₂ ∈ N₂,
        if SameExtraction K S n₁ n₂ (anchor K S N₁ N₂ b₁ b₂ κ).1
          (anchor K S N₁ N₂ b₁ b₂ κ).2 b₁ b₂ then w n₁ n₂ else 0 := by
  have hpoint (n₁ : Ext) (hn₁ : n₁ ∈ N₁) (n₂ : Ext) (hn₂ : n₂ ∈ N₂) :
      (∑ κ : keys K S N₁ N₂ b₁ b₂,
        if SameExtraction K S n₁ n₂ (anchor K S N₁ N₂ b₁ b₂ κ).1
          (anchor K S N₁ N₂ b₁ b₂ κ).2 b₁ b₂ then w n₁ n₂ else 0) = w n₁ n₂ := by
    let κ₀ : keys K S N₁ N₂ b₁ b₂ := ⟨_, key_mem K S N₁ N₂ b₁ b₂ n₁ n₂ hn₁ hn₂⟩
    have he (κ : keys K S N₁ N₂ b₁ b₂) :
        SameExtraction K S n₁ n₂ (anchor K S N₁ N₂ b₁ b₂ κ).1
          (anchor K S N₁ N₂ b₁ b₂ κ).2 b₁ b₂ ↔ κ = κ₀ := by
      rw [sameExtraction_iff_key, anchor_key]
      constructor
      · intro hk
        exact Subtype.ext hk.symm
      · rintro rfl
        rfl
    simp_rw [he]
    simp
  calc
    _ = ∑ n₁ ∈ N₁, ∑ n₂ ∈ N₂, ∑ κ : keys K S N₁ N₂ b₁ b₂,
        if SameExtraction K S n₁ n₂ (anchor K S N₁ N₂ b₁ b₂ κ).1
          (anchor K S N₁ N₂ b₁ b₂ κ).2 b₁ b₂ then w n₁ n₂ else 0 := by
      apply Finset.sum_congr rfl
      intro n₁ hn₁
      apply Finset.sum_congr rfl
      intro n₂ hn₂
      exact (hpoint n₁ hn₁ n₂ hn₂).symm
    _ = ∑ n₁ ∈ N₁, ∑ κ : keys K S N₁ N₂ b₁ b₂, ∑ n₂ ∈ N₂,
        if SameExtraction K S n₁ n₂ (anchor K S N₁ N₂ b₁ b₂ κ).1
          (anchor K S N₁ N₂ b₁ b₂ κ).2 b₁ b₂ then w n₁ n₂ else 0 := by
      apply Finset.sum_congr rfl
      intro n₁ hn₁
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

/-- The original arbitrary exterior-prime mask joined to the computed principal mask. -/
def actualMask (M : Finset (HeightOneSpectrum OS)) (n₁ n₂ b₁ b₂ : Ext) :
    Finset (HeightOneSpectrum OS) :=
  M ∪ principalMask K S (pairSupport K S D n₁ n₂ b₁ b₂)
    (pairExponent K S n₁ n₂ b₁ b₂)

theorem cubePrincipalIdeal_eq (n₁ n₂ r₁ r₂ b₁ b₂ : Ext)
    (h : SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂) :
    CanonicalConductor.cubePrincipalIdeal K S n₁ n₂ b₁ b₂ =
      CanonicalConductor.cubePrincipalIdeal K S r₁ r₂ b₁ b₂ := by
  unfold CanonicalConductor.cubePrincipalIdeal
  congr 1
  apply Finset.filter_congr
  intro p hp
  rw [pairExponent_eq_cubeMultiplicity, pairExponent_eq_cubeMultiplicity,
    cube_bit_eq K S n₁ r₁ b₁ b₂ h.1 p hp,
    cube_bit_eq K S n₂ r₂ b₁ b₂ h.2.1 p hp]

theorem principalSupport_eq (n₁ n₂ r₁ r₂ b₁ b₂ : Ext)
    (h : SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂) :
    principalSupport (pairSupport K S D n₁ n₂ b₁ b₂).support
        (pairExponent K S n₁ n₂ b₁ b₂) =
      principalSupport (pairSupport K S D r₁ r₂ b₁ b₂).support
        (pairExponent K S r₁ r₂ b₁ b₂) := by
  have he : principalIdeal (pairSupport K S D n₁ n₂ b₁ b₂).support
      (pairExponent K S n₁ n₂ b₁ b₂) =
      principalIdeal (pairSupport K S D r₁ r₂ b₁ b₂).support
        (pairExponent K S r₁ r₂ b₁ b₂) := by
    rw [principalIdeal_eq_common_mul_cube, principalIdeal_eq_common_mul_cube,
      commonResidualIdeal_eq_C, commonResidualIdeal_eq_C,
      cubePrincipalIdeal_eq K S n₁ n₂ r₁ r₂ b₁ b₂ h]
    exact congrArg (fun I : Ideal (𝓞 K) =>
      I * CanonicalConductor.cubePrincipalIdeal K S r₁ r₂ b₁ b₂)
      (congrArg IdealMobiusMask.primeProduct h.2.2)
  have he' : nonzeroProduct (principalSupport (pairSupport K S D n₁ n₂ b₁ b₂).support
      (pairExponent K S n₁ n₂ b₁ b₂)) =
      nonzeroProduct (principalSupport (pairSupport K S D r₁ r₂ b₁ b₂).support
        (pairExponent K S r₁ r₂ b₁ b₂)) := Subtype.ext he
  simpa only [primeSupport_nonzeroProduct] using congrArg primeSupport he'

theorem principalMask_eq (n₁ n₂ r₁ r₂ b₁ b₂ : Ext)
    (h : SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂) :
    principalMask K S (pairSupport K S D n₁ n₂ b₁ b₂) (pairExponent K S n₁ n₂ b₁ b₂) =
      principalMask K S (pairSupport K S D r₁ r₂ b₁ b₂) (pairExponent K S r₁ r₂ b₁ b₂) := by
  unfold principalMask
  congr 1
  exact principalSupport_eq K S D n₁ n₂ r₁ r₂ b₁ b₂ h

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstSourcePartition

end

