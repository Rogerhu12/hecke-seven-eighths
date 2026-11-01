import HeckeSkeleton.Moments.MOM_INV_STEP.FirstMaskGeometry
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualPoissonScale

/-!
# Joint norm budget for the actual mask and conductor

An inclusion-exclusion divisor only uses the external primes and the
principal digits. Multiplying by the disjoint active conductor therefore
costs one copy of the source support. The external ideal pays for any
overlap with the active conductor.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.JointMaskGeometry

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton
open FirstMaskGeometry PrimitivePoissonSource ConductorMasks LocalizedMasks
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local instance : IsDedekindDomain OS := sIntegerOrbitMask_isDedekindDomain K Sset

theorem pair_period_dvd_source (n₁ n₂ b₁ b₂ : Ext) :
    IdealMobiusMask.primeProduct (pairSupport K S D n₁ n₂ b₁ b₂).support ∣
      b₁.val.val * b₂.val.val * n₁.val.val * n₂.val.val := by
  apply primeProduct_dvd_of_forall
  intro p hp
  rcases (mem_pairSupport K S D n₁ n₂ b₁ b₂ p).mp hp with h | h | h | h
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _) _
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _) _
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _
  · exact dvd_mul_of_dvd_right h _

variable [IsPrincipalIdealRing
  (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

/-- The mask divisor uses only external primes and principal digits. -/
theorem maskIdeal_dvd_external_mul_principal (Q n₁ n₂ b₁ b₂ : Ext)
    (δ : Finset (HeightOneSpectrum OS))
    (hδ : δ ⊆ actualMask K S D Q n₁ n₂ b₁ b₂) :
    maskIdeal K S δ ∣ Q.val.val *
      principalIdeal (pairSupport K S D n₁ n₂ b₁ b₂).support
        (pairExponent K S n₁ n₂ b₁ b₂) := by
  let J := Q.val.val *
    principalIdeal (pairSupport K S D n₁ n₂ b₁ b₂).support
      (pairExponent K S n₁ n₂ b₁ b₂)
  have hle (P : HeightOneSpectrum OS)
      (hP : P ∈ actualMask K S D Q n₁ n₂ b₁ b₂) :
      J.map (algebraMap (𝓞 K) OS) ≤ P.asIdeal := by
    rcases Finset.mem_union.mp hP with hP | hP
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hP
      change J.map (algebraMap (𝓞 K) OS) ≤ p.val.asIdeal.map (algebraMap (𝓞 K) OS)
      apply Ideal.map_mono
      apply Ideal.dvd_iff_le.mp
      exact dvd_mul_of_dvd_left ((FirstSourceDecomposition.mem_primeSupport Q.val p.val).mp
        p.property) _
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hP
      change J.map (algebraMap (𝓞 K) OS) ≤ p.val.asIdeal.map (algebraMap (𝓞 K) OS)
      apply Ideal.map_mono
      apply Ideal.dvd_iff_le.mp
      apply dvd_mul_of_dvd_right
      exact Finset.dvd_prod_of_mem (fun p : HeightOneSpectrum (𝓞 K) => p.asIdeal) p.property
  apply Ideal.dvd_iff_le.mpr
  rw [maskIdeal_eq_under]
  intro a ha
  change algebraMap (𝓞 K) OS a ∈ IdealMobiusMask.primeProduct δ
  rw [IdealMobiusMask.mem_primeProduct]
  intro P hP
  exact hle P (hδ hP) (Ideal.mem_map_of_mem _ ha)

/-- A single actual source product controls mask norm times conductor
norm. No squared source-product majorant is substituted. -/
theorem mask_mul_primitive_dvd_source (Q n₁ n₂ b₁ b₂ : Ext)
    (δ : Finset (HeightOneSpectrum OS))
    (hδ : δ ⊆ actualMask K S D Q n₁ n₂ b₁ b₂) :
    maskIdeal K S δ *
      primitiveIdeal (pairSupport K S D n₁ n₂ b₁ b₂).support
        (pairExponent K S n₁ n₂ b₁ b₂) ∣
      sourceIdeal K S Q n₁ n₂ b₁ b₂ := by
  let B := (pairSupport K S D n₁ n₂ b₁ b₂).support
  let t := pairExponent K S n₁ n₂ b₁ b₂
  have hperiod : principalIdeal B t * primitiveIdeal B t =
      IdealMobiusMask.primeProduct B := by
    rw [mul_comm, ← period_eq_primitive_mul_principal]
  have hfirst := mul_dvd_mul_right
    (maskIdeal_dvd_external_mul_principal K S D Q n₁ n₂ b₁ b₂ δ hδ)
    (primitiveIdeal B t)
  change maskIdeal K S δ * primitiveIdeal B t ∣
    (Q.val.val * principalIdeal B t) * primitiveIdeal B t at hfirst
  have hfirst' : maskIdeal K S δ * primitiveIdeal B t ∣
      Q.val.val * IdealMobiusMask.primeProduct B := by
    simpa only [mul_assoc, hperiod] using hfirst
  have hsecond := mul_dvd_mul_left Q.val.val (pair_period_dvd_source K S D n₁ n₂ b₁ b₂)
  apply hfirst'.trans
  simpa only [sourceIdeal, mul_assoc] using hsecond

theorem actual_norm_product_bound (Q n₁ n₂ b₁ b₂ : Ext)
    (δ : Finset (HeightOneSpectrum OS))
    (hδ : δ ⊆ actualMask K S D Q n₁ n₂ b₁ b₂) :
    (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val *
      ((primitiveIdeal (pairSupport K S D n₁ n₂ b₁ b₂).support
        (pairExponent K S n₁ n₂ b₁ b₂)).absNorm : ℝ) ≤
      (Q.val.val.absNorm : ℝ) * (b₁.val.val.absNorm : ℝ) * (b₂.val.val.absNorm : ℝ) *
        (n₁.val.val.absNorm : ℝ) * (n₂.val.val.absNorm : ℝ) := by
  have h := absNorm_le_of_dvd K _ _ (sourceIdeal_ne_zero K S Q n₁ n₂ b₁ b₂)
    (mask_mul_primitive_dvd_source K S D Q n₁ n₂ b₁ b₂ δ hδ)
  simpa only [map_mul, Nat.cast_mul, maskIdeal_norm,
    sourceIdeal_norm] using h

theorem actual_radius_product_bound (Q n₁ n₂ b₁ b₂ : Ext)
    (δ : Finset (HeightOneSpectrum OS))
    (hδ : δ ⊆ actualMask K S D Q n₁ n₂ b₁ b₂)
    (r : {r : ℝ // 0 < r}) (Z R E B₁ B₂ N₁ N₂ : ℝ) (hZ : 0 < Z)
    (hr : r.val ≤ Z ^ R) (hQ : (Q.val.val.absNorm : ℝ) ≤ Z ^ E)
    (hb₁ : (b₁.val.val.absNorm : ℝ) ≤ Z ^ B₁)
    (hb₂ : (b₂.val.val.absNorm : ℝ) ≤ Z ^ B₂)
    (hn₁ : (n₁.val.val.absNorm : ℝ) ≤ Z ^ N₁)
    (hn₂ : (n₂.val.val.absNorm : ℝ) ≤ Z ^ N₂) :
    r.val * (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val *
      ((primitiveIdeal (pairSupport K S D n₁ n₂ b₁ b₂).support
        (pairExponent K S n₁ n₂ b₁ b₂)).absNorm : ℝ) ≤
      Z ^ (R + E + B₁ + B₂ + N₁ + N₂) := by
  have hs : (Q.val.val.absNorm : ℝ) * (b₁.val.val.absNorm : ℝ) *
      (b₂.val.val.absNorm : ℝ) * (n₁.val.val.absNorm : ℝ) * (n₂.val.val.absNorm : ℝ) ≤
        Z ^ (E + B₁ + B₂ + N₁ + N₂) := by
    simp only [Real.rpow_add hZ]
    gcongr
  calc
    _ = r.val * ((sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val *
        ((primitiveIdeal (pairSupport K S D n₁ n₂ b₁ b₂).support
          (pairExponent K S n₁ n₂ b₁ b₂)).absNorm : ℝ)) := by ring
    _ ≤ Z ^ R * Z ^ (E + B₁ + B₂ + N₁ + N₂) :=
      mul_le_mul hr ((actual_norm_product_bound K S D Q n₁ n₂ b₁ b₂ δ hδ).trans hs)
        (mul_nonneg (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).property.le
          (Nat.cast_nonneg _)) (Real.rpow_nonneg hZ.le _)
    _ = _ := by rw [← Real.rpow_add hZ]; congr 1; ring

end HeckeSkeleton.Moments.MOM_INV_STEP.JointMaskGeometry

end

