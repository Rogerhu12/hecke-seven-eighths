import HeckeSkeleton.Moments.MOM_INV_STEP.PrimitivePacketCRT
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalConductor

/-!
# The actual first Gauss factor split over u₁, u₂, and R₁

The original pair's support determines all three blocks. Its normalized
Gauss factor is separated by the proved signed packet CRT, with all six
cross-symbol factors retained. The residual blocks have their actual
digits one and five, so their Gauss factors are the existing thetaGamma
coefficients. The cube block remains its actual normalized Gauss factor.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalGroupedGauss

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ActualFiniteSource ConductorMasks PrimitivePoissonSource PrimitiveFourier
  PrincipalGaussCRT UnitGaussTransport PrimitivePacketCRT CanonicalConductor
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

/-- Both directed cross symbols, as values of the actual primitive rows. -/
def crossFactor (B₁ B₂ : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) : ℂ :=
  primitiveCoefficient K S D B₁ t (Ideal.Quotient.mk _ (primitiveModulus K S D B₂ t)) *
    primitiveCoefficient K S D B₂ t (Ideal.Quotient.mk _ (primitiveModulus K S D B₁ t))

theorem normalizedGauss_eq_of_activeSupport_eq (B₁ B₂ : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (hactive : activeSupport B₁.support t = activeSupport B₂.support t) :
    normalizedPrimitiveGauss K S D B₁ t = normalizedPrimitiveGauss K S D B₂ t := by
  have hI : primitiveIdeal B₁.support t = primitiveIdeal B₂.support t :=
    congrArg IdealMobiusMask.primeProduct hactive
  have hE : primitiveExterior K S B₁ t = primitiveExterior K S B₂ t :=
    Subtype.ext (Subtype.ext hI)
  let c := primitiveModulus K S D B₁ t
  have hc : c ≠ 0 := primitiveModulus_ne_zero K S D B₁ t
  have hcspan₁ := primitiveModulus_span K S D B₁ t
  have hcspan₂ : Ideal.span ({c} : Set OS) =
      (primitiveIdeal B₂.support t).map (algebraMap (𝓞 K) OS) := by
    rw [← hI]
    exact hcspan₁
  have hgen : primitiveModulus K S D B₂ t = c := congrArg D.generator hE.symm
  have hchar : characterAt K S D B₁ t c hcspan₁ =
      characterAt K S D B₂ t c hcspan₂ := by
    apply MonoidHom.ext
    intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [characterAt_mk, characterAt_mk,
      primitiveCoefficient_mk_eq_product, primitiveCoefficient_mk_eq_product, hactive]
  have hG : primitiveGauss K S D B₁ t = primitiveGauss K S D B₂ t := by
    calc
      _ = gaussAt K S D B₁ t c hc hcspan₁ := (gaussAt_canonical K S D B₁ t).symm
      _ = gaussAt K S D B₂ t c hc hcspan₂ := by unfold gaussAt; rw [hchar]
      _ = _ := (primitiveGauss_eq_gaussAt_of_modulus K S D B₂ t c hc hcspan₂ hgen).symm
  simp only [normalizedPrimitiveGauss, hG, hI]

/-- Allowed generators preserve multiplication of the actual packet
row, because their only discrepancy is a proved-invisible sixth unit. -/
theorem coefficient_generator_union (hallowed : AllowedGeneratorInput K Sset D)
    (B B₁ B₂ : PrimeBlock K Sset) (hdisj : Disjoint B₁.support B₂.support)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    primitiveCoefficient K S D B t
        (Ideal.Quotient.mk _ (primitiveModulus K S D (unionBlock K S B₁ B₂) t)) =
      primitiveCoefficient K S D B t (Ideal.Quotient.mk _ (primitiveModulus K S D B₁ t)) *
        primitiveCoefficient K S D B t (Ideal.Quotient.mk _ (primitiveModulus K S D B₂ t)) := by
  obtain ⟨u, hu⟩ := hallowed.multiplicative
    (primitiveExterior K S B₁ t) (primitiveExterior K S B₂ t)
  rw [← primitiveExterior_union K S B₁ B₂ hdisj t] at hu
  change primitiveCoefficient K S D B t
    (Ideal.Quotient.mk _ (D.generator (primitiveExterior K S (unionBlock K S B₁ B₂) t))) = _
  rw [hu]
  simp only [map_mul, primitiveCoefficient_mul]
  rw [primitiveCoefficient_sixth_unit, one_mul]
  rfl

theorem crossFactor_union (hallowed : AllowedGeneratorInput K Sset D)
    (B₁ B₂ B₃ : PrimeBlock K Sset) (hdisj : Disjoint B₁.support B₂.support)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    crossFactor K S D (unionBlock K S B₁ B₂) B₃ t =
      crossFactor K S D B₁ B₃ t * crossFactor K S D B₂ B₃ t := by
  unfold crossFactor
  rw [primitiveCoefficient_union_mk K S D B₁ B₂ hdisj t,
    coefficient_generator_union K S D hallowed B₃ B₁ B₂ hdisj t]
  ring

/-- Three actual disjoint blocks, with one cross factor for each pair. -/
theorem normalizedGauss_three (hallowed : AllowedGeneratorInput K Sset D)
    (B₁ B₂ B₃ : PrimeBlock K Sset) (h₁₂ : Disjoint B₁.support B₂.support)
    (h₁₂₃ : Disjoint (B₁.support ∪ B₂.support) B₃.support)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    normalizedPrimitiveGauss K S D (unionBlock K S (unionBlock K S B₁ B₂) B₃) t =
      crossFactor K S D B₁ B₂ t * crossFactor K S D B₁ B₃ t * crossFactor K S D B₂ B₃ t *
        normalizedPrimitiveGauss K S D B₁ t * normalizedPrimitiveGauss K S D B₂ t *
          normalizedPrimitiveGauss K S D B₃ t := by
  have houter := normalizedPrimitiveGauss_union K S D hallowed (unionBlock K S B₁ B₂) B₃ h₁₂₃ t
  change normalizedPrimitiveGauss K S D (unionBlock K S (unionBlock K S B₁ B₂) B₃) t =
    crossFactor K S D (unionBlock K S B₁ B₂) B₃ t *
      normalizedPrimitiveGauss K S D (unionBlock K S B₁ B₂) t *
        normalizedPrimitiveGauss K S D B₃ t at houter
  rw [houter, crossFactor_union K S D hallowed B₁ B₂ B₃ h₁₂ t,
    normalizedPrimitiveGauss_union K S D hallowed B₁ B₂ h₁₂ t]
  unfold crossFactor
  ring

variable (n₁ n₂ b₁ b₂ : ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K))))

def leftBlock : PrimeBlock K Sset where
  support := SupportPartition.leftResidual (pairSupport K S D n₁ n₂ b₁ b₂).support
    (CubeLabels.cubeMultiplicity b₁.val b₂.val) (squarefreeBit K S n₁) (squarefreeBit K S n₂)
  outside p hp := (pairSupport K S D n₁ n₂ b₁ b₂).outside p (Finset.mem_filter.mp hp).1
  awaySix p hp := (pairSupport K S D n₁ n₂ b₁ b₂).awaySix p (Finset.mem_filter.mp hp).1

def rightBlock : PrimeBlock K Sset where
  support := SupportPartition.rightResidual (pairSupport K S D n₁ n₂ b₁ b₂).support
    (CubeLabels.cubeMultiplicity b₁.val b₂.val) (squarefreeBit K S n₁) (squarefreeBit K S n₂)
  outside p hp := (pairSupport K S D n₁ n₂ b₁ b₂).outside p (Finset.mem_filter.mp hp).1
  awaySix p hp := (pairSupport K S D n₁ n₂ b₁ b₂).awaySix p (Finset.mem_filter.mp hp).1

def cubeBlock : PrimeBlock K Sset where
  support := SupportPartition.cubeActive (pairSupport K S D n₁ n₂ b₁ b₂).support
    (CubeLabels.cubeMultiplicity b₁.val b₂.val) (squarefreeBit K S n₁) (squarefreeBit K S n₂)
  outside p hp := (pairSupport K S D n₁ n₂ b₁ b₂).outside p (Finset.mem_filter.mp hp).1
  awaySix p hp := (pairSupport K S D n₁ n₂ b₁ b₂).awaySix p (Finset.mem_filter.mp hp).1

theorem left_digit (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∈ (leftBlock K S D n₁ n₂ b₁ b₂).support) :
    pairExponent K S n₁ n₂ b₁ b₂ p = 1 := by
  obtain ⟨_hQ, hv, h₁, h₂⟩ := Finset.mem_filter.mp hp
  rw [pairExponent_eq_cubeMultiplicity, hv, h₁, h₂]
  decide

theorem right_digit (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∈ (rightBlock K S D n₁ n₂ b₁ b₂).support) :
    pairExponent K S n₁ n₂ b₁ b₂ p = 5 := by
  obtain ⟨_hQ, hv, h₁, h₂⟩ := Finset.mem_filter.mp hp
  rw [pairExponent_eq_cubeMultiplicity, hv, h₁, h₂]
  decide

theorem left_active :
    activeSupport (leftBlock K S D n₁ n₂ b₁ b₂).support (pairExponent K S n₁ n₂ b₁ b₂) =
      (leftBlock K S D n₁ n₂ b₁ b₂).support := by
  apply Finset.filter_true_of_mem
  intro p hp
  rw [left_digit K S D n₁ n₂ b₁ b₂ p hp]
  decide

theorem right_active :
    activeSupport (rightBlock K S D n₁ n₂ b₁ b₂).support (pairExponent K S n₁ n₂ b₁ b₂) =
      (rightBlock K S D n₁ n₂ b₁ b₂).support := by
  apply Finset.filter_true_of_mem
  intro p hp
  rw [right_digit K S D n₁ n₂ b₁ b₂ p hp]
  decide

theorem cube_active :
    activeSupport (cubeBlock K S D n₁ n₂ b₁ b₂).support (pairExponent K S n₁ n₂ b₁ b₂) =
      (cubeBlock K S D n₁ n₂ b₁ b₂).support := by
  apply Finset.filter_true_of_mem
  intro p hp
  rw [pairExponent_eq_cubeMultiplicity]
  exact (Finset.mem_filter.mp hp).2.2

theorem source_active_partition :
    activeSupport (pairSupport K S D n₁ n₂ b₁ b₂).support (pairExponent K S n₁ n₂ b₁ b₂) =
      ((leftBlock K S D n₁ n₂ b₁ b₂).support ∪ (rightBlock K S D n₁ n₂ b₁ b₂).support) ∪
        (cubeBlock K S D n₁ n₂ b₁ b₂).support := by
  simp only [activeSupport, pairExponent_eq_cubeMultiplicity]
  exact SupportPartition.active_partition _ _ _ _

theorem left_right_disjoint :
    Disjoint (leftBlock K S D n₁ n₂ b₁ b₂).support (rightBlock K S D n₁ n₂ b₁ b₂).support :=
  SupportPartition.residuals_disjoint _ _ _ _

theorem residuals_cube_disjoint :
    Disjoint ((leftBlock K S D n₁ n₂ b₁ b₂).support ∪ (rightBlock K S D n₁ n₂ b₁ b₂).support)
      (cubeBlock K S D n₁ n₂ b₁ b₂).support :=
  SupportPartition.residuals_disjoint_cubeActive _ _ _ _

def leftIdeal : ExteriorIdeal K Sset :=
  primitiveExterior K S (leftBlock K S D n₁ n₂ b₁ b₂) (pairExponent K S n₁ n₂ b₁ b₂)

def rightIdeal : ExteriorIdeal K Sset :=
  primitiveExterior K S (rightBlock K S D n₁ n₂ b₁ b₂) (pairExponent K S n₁ n₂ b₁ b₂)

def cubeIdeal : ExteriorIdeal K Sset :=
  primitiveExterior K S (cubeBlock K S D n₁ n₂ b₁ b₂) (pairExponent K S n₁ n₂ b₁ b₂)

theorem leftIdeal_val : (leftIdeal K S D n₁ n₂ b₁ b₂).val.val = u₁ K S D n₁ n₂ b₁ b₂ :=
  congrArg IdealMobiusMask.primeProduct (left_active K S D n₁ n₂ b₁ b₂)

theorem rightIdeal_val : (rightIdeal K S D n₁ n₂ b₁ b₂).val.val = u₂ K S D n₁ n₂ b₁ b₂ :=
  congrArg IdealMobiusMask.primeProduct (right_active K S D n₁ n₂ b₁ b₂)

theorem cubeIdeal_val : (cubeIdeal K S D n₁ n₂ b₁ b₂).val.val =
    CubeLabels.R1 b₁.val b₂.val (squarefreeBit K S n₁) (squarefreeBit K S n₂) := by
  change IdealMobiusMask.primeProduct
    (activeSupport (cubeBlock K S D n₁ n₂ b₁ b₂).support (pairExponent K S n₁ n₂ b₁ b₂)) = _
  rw [cube_active]
  change IdealMobiusMask.primeProduct (SupportPartition.cubeActive
    (pairSupport K S D n₁ n₂ b₁ b₂).support (CubeLabels.cubeMultiplicity b₁.val b₂.val)
    (squarefreeBit K S n₁) (squarefreeBit K S n₂)) = _
  rw [cubeActive_eq K S D n₁ n₂ b₁ b₂]
  simp only [CubeLabels.R1, pairExponent_eq_cubeMultiplicity]

def sourceCross : ℂ :=
  crossFactor K S D (leftBlock K S D n₁ n₂ b₁ b₂) (rightBlock K S D n₁ n₂ b₁ b₂)
      (pairExponent K S n₁ n₂ b₁ b₂) *
    crossFactor K S D (leftBlock K S D n₁ n₂ b₁ b₂) (cubeBlock K S D n₁ n₂ b₁ b₂)
      (pairExponent K S n₁ n₂ b₁ b₂) *
    crossFactor K S D (rightBlock K S D n₁ n₂ b₁ b₂) (cubeBlock K S D n₁ n₂ b₁ b₂)
      (pairExponent K S n₁ n₂ b₁ b₂)

/-- The genuine source Gauss factor has the manuscript's two residual
theta coefficients and the actual cube Gauss factor. No source-separation
or grouped-Gauss equality is an input. -/
theorem pair_normalizedGauss_grouped (hallowed : AllowedGeneratorInput K Sset D) :
    normalizedPrimitiveGauss K S D (pairSupport K S D n₁ n₂ b₁ b₂)
        (pairExponent K S n₁ n₂ b₁ b₂) =
      sourceCross K S D n₁ n₂ b₁ b₂ *
        thetaGamma K Sset D (leftIdeal K S D n₁ n₂ b₁ b₂) 1 *
        thetaGamma K Sset D (rightIdeal K S D n₁ n₂ b₁ b₂) 5 *
        normalizedPrimitiveGauss K S D (cubeBlock K S D n₁ n₂ b₁ b₂)
          (pairExponent K S n₁ n₂ b₁ b₂) := by
  let L := leftBlock K S D n₁ n₂ b₁ b₂
  let R := rightBlock K S D n₁ n₂ b₁ b₂
  let C := cubeBlock K S D n₁ n₂ b₁ b₂
  let t := pairExponent K S n₁ n₂ b₁ b₂
  have hactive : activeSupport (pairSupport K S D n₁ n₂ b₁ b₂).support t =
      activeSupport (unionBlock K S (unionBlock K S L R) C).support t := by
    rw [activeSupport_union, activeSupport_union]
    rw [left_active, right_active, cube_active]
    exact source_active_partition K S D n₁ n₂ b₁ b₂
  rw [normalizedGauss_eq_of_activeSupport_eq K S D _ _ t hactive,
    normalizedGauss_three K S D hallowed L R C
      (left_right_disjoint K S D n₁ n₂ b₁ b₂)
      (residuals_cube_disjoint K S D n₁ n₂ b₁ b₂) t]
  have hleft : normalizedPrimitiveGauss K S D L t = thetaGamma K Sset D (leftIdeal K S D n₁ n₂ b₁ b₂) 1 := by
    apply normalizedPrimitiveGauss_uniform K S D L t 1
    intro p hp
    rw [left_digit K S D n₁ n₂ b₁ b₂ p (Finset.mem_filter.mp hp).1]
    rfl
  have hright : normalizedPrimitiveGauss K S D R t = thetaGamma K Sset D (rightIdeal K S D n₁ n₂ b₁ b₂) 5 := by
    apply normalizedPrimitiveGauss_uniform K S D R t 5
    intro p hp
    rw [right_digit K S D n₁ n₂ b₁ b₂ p (Finset.mem_filter.mp hp).1]
    rfl
  rw [hleft, hright]
  rfl

/-- The fifth digit retains its actual minus-one factor when expressed
as a conjugate first digit. -/
theorem pair_normalizedGauss_grouped_conjugate (hallowed : AllowedGeneratorInput K Sset D) :
    normalizedPrimitiveGauss K S D (pairSupport K S D n₁ n₂ b₁ b₂)
        (pairExponent K S n₁ n₂ b₁ b₂) =
      sourceCross K S D n₁ n₂ b₁ b₂ *
        thetaGamma K Sset D (leftIdeal K S D n₁ n₂ b₁ b₂) 1 *
        (idealSymbol K Sset D (rightIdeal K S D n₁ n₂ b₁ b₂) (-1) *
          star (thetaGamma K Sset D (rightIdeal K S D n₁ n₂ b₁ b₂) 1)) *
        normalizedPrimitiveGauss K S D (cubeBlock K S D n₁ n₂ b₁ b₂)
          (pairExponent K S n₁ n₂ b₁ b₂) := by
  rw [pair_normalizedGauss_grouped K S D n₁ n₂ b₁ b₂ hallowed,
    GaussConjugation.thetaGamma_five]
  rfl

end HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalGroupedGauss
