import HeckeSkeleton.Moments.MOM_INV_STEP.FirstSourceColumns
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstSourceReindexing
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalSectorRows

/-!
# Fixed first-extraction data give genuine independent columns

The cube packet, extracted coefficients, retained label and dilation
are constant on an actual first-extraction slice.  Only the residual
ideal varies inside each column.  This is proved from equality of the
computed prime supports, rather than supplied as a separation identity.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstSourceFrozen

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ActualFiniteSource ConductorMasks PrimitivePoissonSource PrimitiveFourier
  PrimitivePacketCRT CanonicalGroupedGauss CanonicalConductor FirstSourceColumns
open FirstSourceDecomposition
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "E" => CanonicalIdealRow.exteriorMonoid K S

/-- Equality of the three parts actually extracted from the two sources. -/
def SameExtraction (n₁ n₂ r₁ r₂ b₁ b₂ : Ext) : Prop :=
  extractedSupport n₁.val b₁.val b₂.val = extractedSupport r₁.val b₁.val b₂.val ∧
  extractedSupport n₂.val b₁.val b₂.val = extractedSupport r₂.val b₁.val b₂.val ∧
  commonSupport n₁.val n₂.val b₁.val b₂.val = commonSupport r₁.val r₂.val b₁.val b₂.val

theorem sameExtraction_of_slice (n₁ n₂ r₁ r₂ b₁ b₂ : Ext)
    (A₁ A₂ C : Finset (HeightOneSpectrum (𝓞 K)))
    (hn : FirstSourceReindexing.Supports.Slice (primeSupport (b₁.val * b₂.val))
      A₁ A₂ C (primeSupport n₁.val) (primeSupport n₂.val))
    (hr : FirstSourceReindexing.Supports.Slice (primeSupport (b₁.val * b₂.val))
      A₁ A₂ C (primeSupport r₁.val) (primeSupport r₂.val)) :
    SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂ :=
  ⟨hn.1.trans hr.1.symm, hn.2.1.trans hr.2.1.symm, hn.2.2.trans hr.2.2.symm⟩

theorem cube_bit_eq (n r b₁ b₂ : Ext)
    (h : extractedSupport n.val b₁.val b₂.val = extractedSupport r.val b₁.val b₂.val)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ CubeLabels.cubePrimeSupport b₁.val b₂.val) :
    squarefreeBit K S n p = squarefreeBit K S r p := by
  have he := Finset.ext_iff.mp h p
  have hB : p ∈ primeSupport (b₁.val * b₂.val) := hp
  simp only [extractedSupport, Finset.mem_inter, hB, and_true, mem_primeSupport] at he
  change decide (p.asIdeal ∣ n.val.val) = decide (p.asIdeal ∣ r.val.val)
  rw [propext he]

theorem commonFactor_eq (n₁ n₂ r₁ r₂ b₁ b₂ : Ext)
    (h : SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂) :
    commonFactor K S n₁ n₂ b₁ b₂ = commonFactor K S r₁ r₂ b₁ b₂ := by
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg IdealMobiusMask.primeProduct h.2.2

theorem extractedFactor_eq (n₁ n₂ r₁ r₂ b₁ b₂ : Ext)
    (h : SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂) (side : Bool) :
    extractedFactor K S n₁ n₂ b₁ b₂ side = extractedFactor K S r₁ r₂ b₁ b₂ side := by
  unfold extractedFactor
  rw [commonFactor_eq K S n₁ n₂ r₁ r₂ b₁ b₂ h]
  congr 1
  unfold CanonicalCubeLabels.A CubeAlgebra.aLabel CubeAlgebra.primeProduct
  apply Finset.prod_congr rfl
  intro p hp
  dsimp only
  cases side with
  | false => rw [show sourceIdeal K S n₁ n₂ false = n₁ from rfl,
      show sourceIdeal K S r₁ r₂ false = r₁ from rfl, cube_bit_eq K S n₁ r₁ b₁ b₂ h.1 p hp]
  | true => rw [show sourceIdeal K S n₁ n₂ true = n₂ from rfl,
      show sourceIdeal K S r₁ r₂ true = r₂ from rfl, cube_bit_eq K S n₂ r₂ b₁ b₂ h.2.1 p hp]

theorem fixed_labels (n₁ n₂ r₁ r₂ b₁ b₂ : Ext)
    (h : SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂) :
    CanonicalCubeLabels.J K S b₁ b₂ (squarefreeBit K S n₁) (squarefreeBit K S n₂) =
      CanonicalCubeLabels.J K S b₁ b₂ (squarefreeBit K S r₁) (squarefreeBit K S r₂) ∧
    CanonicalCubeLabels.q0 K S b₁ b₂ (squarefreeBit K S n₁) (squarefreeBit K S n₂) =
      CanonicalCubeLabels.q0 K S b₁ b₂ (squarefreeBit K S r₁) (squarefreeBit K S r₂) ∧
    CanonicalCubeLabels.dilation K S b₁ b₂ (squarefreeBit K S n₁) (squarefreeBit K S n₂) =
      CanonicalCubeLabels.dilation K S b₁ b₂ (squarefreeBit K S r₁) (squarefreeBit K S r₂) := by
  have h₁ := cube_bit_eq K S n₁ r₁ b₁ b₂ h.1
  have h₂ := cube_bit_eq K S n₂ r₂ b₁ b₂ h.2.1
  refine ⟨?_, ?_, ?_⟩
  · unfold CanonicalCubeLabels.J CubeAlgebra.jLabel CubeAlgebra.primeProduct
    apply Finset.prod_congr rfl
    intro p hp
    dsimp only
    rw [h₁ p hp, h₂ p hp]
  · unfold CanonicalCubeLabels.q0 CubeAlgebra.b0Label CubeAlgebra.primeProduct
    apply Finset.prod_congr rfl
    intro p hp
    dsimp only
    rw [h₁ p hp, h₂ p hp]
  · unfold CanonicalCubeLabels.dilation CubeAlgebra.dilationLabel CubeAlgebra.primeProduct
    apply Finset.prod_congr rfl
    intro p hp
    dsimp only
    rw [h₁ p hp, h₂ p hp]

variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

theorem coefficient_congr (B₁ B₂ : PrimeBlock K Sset)
    (t₁ t₂ : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (hactive : activeSupport B₁.support t₁ = activeSupport B₂.support t₂)
    (ht : ∀ p ∈ activeSupport B₁.support t₁, t₁ p = t₂ p) (a : OS) :
    primitiveCoefficient K S D B₁ t₁ (Ideal.Quotient.mk _ a) =
      primitiveCoefficient K S D B₂ t₂ (Ideal.Quotient.mk _ a) := by
  rw [primitiveCoefficient_mk_eq_product, primitiveCoefficient_mk_eq_product]
  apply Finset.prod_congr hactive
  intro p hp
  rw [ht p (hactive.symm ▸ hp)]

/-- A finite Gauss packet depends only on its actual active ideal and
its conductor digits there. The quotient generator is transported by
the proved equality of these ideals. -/
theorem normalizedGauss_congr (B₁ B₂ : PrimeBlock K Sset)
    (t₁ t₂ : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (hactive : activeSupport B₁.support t₁ = activeSupport B₂.support t₂)
    (ht : ∀ p ∈ activeSupport B₁.support t₁, t₁ p = t₂ p) :
    normalizedPrimitiveGauss K S D B₁ t₁ = normalizedPrimitiveGauss K S D B₂ t₂ := by
  have hI : primitiveIdeal B₁.support t₁ = primitiveIdeal B₂.support t₂ :=
    congrArg IdealMobiusMask.primeProduct hactive
  have hE : primitiveExterior K S B₁ t₁ = primitiveExterior K S B₂ t₂ :=
    Subtype.ext (Subtype.ext hI)
  let c := primitiveModulus K S D B₁ t₁
  have hc : c ≠ 0 := primitiveModulus_ne_zero K S D B₁ t₁
  have hcspan₁ := primitiveModulus_span K S D B₁ t₁
  have hcspan₂ : Ideal.span ({c} : Set OS) =
      (primitiveIdeal B₂.support t₂).map (algebraMap (𝓞 K) OS) := by
    rw [← hI]
    exact hcspan₁
  have hgen : primitiveModulus K S D B₂ t₂ = c := congrArg D.generator hE.symm
  have hchar : characterAt K S D B₁ t₁ c hcspan₁ =
      characterAt K S D B₂ t₂ c hcspan₂ := by
    apply MonoidHom.ext
    intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [characterAt_mk, characterAt_mk]
    exact coefficient_congr K S D B₁ B₂ t₁ t₂ hactive ht a
  have hG : primitiveGauss K S D B₁ t₁ = primitiveGauss K S D B₂ t₂ := by
    calc
      _ = gaussAt K S D B₁ t₁ c hc hcspan₁ := (gaussAt_canonical K S D B₁ t₁).symm
      _ = gaussAt K S D B₂ t₂ c hc hcspan₂ := by unfold gaussAt; rw [hchar]
      _ = _ := (primitiveGauss_eq_gaussAt_of_modulus K S D B₂ t₂ c hc hcspan₂ hgen).symm
  simp only [normalizedPrimitiveGauss, hG, hI]

theorem cube_packet_data (n₁ n₂ r₁ r₂ b₁ b₂ : Ext)
    (h : SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂) :
    activeSupport (cubeBlock K S D n₁ n₂ b₁ b₂).support (pairExponent K S n₁ n₂ b₁ b₂) =
      activeSupport (cubeBlock K S D r₁ r₂ b₁ b₂).support (pairExponent K S r₁ r₂ b₁ b₂) ∧
    ∀ p ∈ activeSupport (cubeBlock K S D n₁ n₂ b₁ b₂).support
      (pairExponent K S n₁ n₂ b₁ b₂),
      pairExponent K S n₁ n₂ b₁ b₂ p = pairExponent K S r₁ r₂ b₁ b₂ p := by
  have ht (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ CubeLabels.cubePrimeSupport b₁.val b₂.val) :
      pairExponent K S n₁ n₂ b₁ b₂ p = pairExponent K S r₁ r₂ b₁ b₂ p := by
    rw [pairExponent_eq_cubeMultiplicity, pairExponent_eq_cubeMultiplicity,
      cube_bit_eq K S n₁ r₁ b₁ b₂ h.1 p hp,
      cube_bit_eq K S n₂ r₂ b₁ b₂ h.2.1 p hp]
  have hs (a b : Ext) : activeSupport (cubeBlock K S D a b b₁ b₂).support
      (pairExponent K S a b b₁ b₂) =
        (CubeLabels.cubePrimeSupport b₁.val b₂.val).filter
          (fun p => pairExponent K S a b b₁ b₂ p ≠ 0) := by
    rw [cube_active]
    exact cubeActive_eq K S D a b b₁ b₂
  refine ⟨?_, ?_⟩
  · rw [hs, hs]
    apply Finset.filter_congr
    intro p hp
    rw [ht p hp]
  · intro p hp
    rw [hs] at hp
    exact ht p (Finset.mem_filter.mp hp).1

theorem cubeFourierScalar_eq (n₁ n₂ r₁ r₂ b₁ b₂ : Ext)
    (h : SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂) (d a : OS) :
    cubeFourierScalar K S D n₁ n₂ b₁ b₂ d a = cubeFourierScalar K S D r₁ r₂ b₁ b₂ d a := by
  obtain ⟨hactive, ht⟩ := cube_packet_data K S D n₁ n₂ r₁ r₂ b₁ b₂ h
  unfold cubeFourierScalar
  rw [coefficient_congr K S D _ _ _ _ hactive ht d,
    coefficient_congr K S D _ _ _ _ hactive ht a,
    normalizedGauss_congr K S D _ _ _ _ hactive ht]

/-- An actual first-divisor coefficient. Its fixed parameters come
from one extraction slice; the only moving argument is the residual
ideal u. In particular d is a literal S-integer numerator in the column. -/
def fixedInverseCoefficient (ν G : HeckeCharacter K) (r₁ r₂ b₁ b₂ : Ext)
    (f z : E) (d : OS) (u : Ext) : ℂ :=
  idealSymbol K Sset D u d *
    (((UniqueFactorizationMonoid.moebius u.val.val : ℂ) *
        heckeIdealCoefficient K ν u.val * heckeIdealCoefficient K G u.val) *
      (idealSymbol K Sset D u (CanonicalIdealRow.generator K S D
        (commonFactor K S r₁ r₂ b₁ b₂ * CanonicalCubeLabels.J K S b₁ b₂
          (squarefreeBit K S r₁) (squarefreeBit K S r₂))) ^ 4 *
        (if IsCoprime u.val.val (CanonicalCubeLabels.q0 K S b₁ b₂
          (squarefreeBit K S r₁) (squarefreeBit K S r₂)).val.val then 1 else 0)) *
      conj (idealSymbol K Sset D u (CanonicalIdealRow.generator K S D
        (z * f ^ 2 * CanonicalCubeLabels.dilation K S b₁ b₂
          (squarefreeBit K S r₁) (squarefreeBit K S r₂)))))

theorem inverseCoefficient_eq_fixed (ν G : HeckeCharacter K) (n₁ n₂ r₁ r₂ b₁ b₂ : Ext)
    (h : SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂) (side : Bool) (f z : E) (d : OS) :
    divisorInverseCoefficient K S D ν G n₁ n₂ b₁ b₂ side f z d =
      fixedInverseCoefficient K S D ν G r₁ r₂ b₁ b₂ f z d
        (residualIdeal K S D n₁ n₂ b₁ b₂ side) := by
  obtain ⟨hJ, hq, hE⟩ := fixed_labels K S n₁ n₂ r₁ r₂ b₁ b₂ h
  unfold divisorInverseCoefficient inverseCoefficient fixedInverseCoefficient
  rw [commonFactor_eq K S n₁ n₂ r₁ r₂ b₁ b₂ h, hJ, hq, hE]

theorem outerCoefficient_eq (Λ ν : HeckeCharacter K) (n₁ n₂ r₁ r₂ b₁ b₂ : Ext)
    (h : SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂) (side : Bool) (f : E) :
    outerCoefficient K S D Λ ν n₁ n₂ b₁ b₂ side f =
      outerCoefficient K S D Λ ν r₁ r₂ b₁ b₂ side f := by
  unfold outerCoefficient
  rw [extractedFactor_eq K S n₁ n₂ r₁ r₂ b₁ b₂ h side]

/-- The literal first Poisson coefficient and the two original a₀
coefficients separate into fixed scalars and two independent residual
columns on the actual extraction slice. -/
theorem first_source_pair_frozen (hallowed : AllowedGeneratorInput K Sset D)
    {Λ G : HeckeCharacter K} (hcal : ThetaCalibrationInput K Sset D Λ G)
    (ν : HeckeCharacter K) (n₁ n₂ r₁ r₂ b₁ b₂ : Ext)
    (hn₁ : Squarefree n₁.val.val) (hn₂ : Squarefree n₂.val.val)
    (h : SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂)
    (f₁ f₂ z : E) (d : OS) :
    sourceCoefficient K S D Λ ν n₁ f₁ * conj (sourceCoefficient K S D Λ ν n₂ f₂) *
      pairFourier K S D n₁ n₂ b₁ b₂ d (CanonicalIdealRow.generator K S D z) =
    cubeFourierScalar K S D r₁ r₂ b₁ b₂ d (CanonicalIdealRow.generator K S D z) *
      (outerCoefficient K S D Λ ν r₁ r₂ b₁ b₂ false f₁ *
        fixedInverseCoefficient K S D ν G r₁ r₂ b₁ b₂ f₁ z d
          (residualIdeal K S D n₁ n₂ b₁ b₂ false)) *
      conj (outerCoefficient K S D Λ ν r₁ r₂ b₁ b₂ true f₂ *
        fixedInverseCoefficient K S D ν G r₁ r₂ b₁ b₂ f₂ z d
          (residualIdeal K S D n₁ n₂ b₁ b₂ true)) := by
  rw [first_source_pair K S D hallowed hcal ν n₁ n₂ b₁ b₂ hn₁ hn₂,
    cubeFourierScalar_eq K S D n₁ n₂ r₁ r₂ b₁ b₂ h,
    outerCoefficient_eq K S D Λ ν n₁ n₂ r₁ r₂ b₁ b₂ h false,
    outerCoefficient_eq K S D Λ ν n₁ n₂ r₁ r₂ b₁ b₂ h true,
    inverseCoefficient_eq_fixed K S D ν G n₁ n₂ r₁ r₂ b₁ b₂ h false,
    inverseCoefficient_eq_fixed K S D ν G n₁ n₂ r₁ r₂ b₁ b₂ h true]

theorem pairFourier_mul_left (n₁ n₂ b₁ b₂ : Ext) (d v a : OS) :
    pairFourier K S D n₁ n₂ b₁ b₂ d (v * a) =
      pairFourier K S D n₁ n₂ b₁ b₂ d a *
        conj (primitiveCoefficient K S D (pairSupport K S D n₁ n₂ b₁ b₂)
          (pairExponent K S n₁ n₂ b₁ b₂) (Ideal.Quotient.mk _ v)) := by
  rw [pairFourier_eq, pairFourier_eq, map_mul, primitiveCoefficient_mul]
  simp only [map_mul]
  ring

theorem cubeFourierScalar_mul_left (n₁ n₂ b₁ b₂ : Ext) (d v a : OS) :
    cubeFourierScalar K S D n₁ n₂ b₁ b₂ d (v * a) =
      cubeFourierScalar K S D n₁ n₂ b₁ b₂ d a *
        conj (primitiveCoefficient K S D (cubeBlock K S D n₁ n₂ b₁ b₂)
          (pairExponent K S n₁ n₂ b₁ b₂) (Ideal.Quotient.mk _ v)) := by
  unfold cubeFourierScalar
  rw [map_mul, primitiveCoefficient_mul]
  simp only [map_mul]
  ring

/-- The multiplier belongs to the row sector. Its value on the moving
residual is kept inside the column. -/
def fixedMultiplierCoefficient (ν G : HeckeCharacter K) (r₁ r₂ b₁ b₂ : Ext)
    (f z : E) (d v : OS) (u : Ext) : ℂ :=
  fixedInverseCoefficient K S D ν G r₁ r₂ b₁ b₂ f z d u *
    conj (idealSymbol K Sset D u v)

theorem first_source_pair_multiplier (hallowed : AllowedGeneratorInput K Sset D)
    {Λ G : HeckeCharacter K} (hcal : ThetaCalibrationInput K Sset D Λ G)
    (ν : HeckeCharacter K) (n₁ n₂ r₁ r₂ b₁ b₂ : Ext)
    (hn₁ : Squarefree n₁.val.val) (hn₂ : Squarefree n₂.val.val)
    (h : SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂)
    (f₁ f₂ z : E) (d v : OS) :
    sourceCoefficient K S D Λ ν n₁ f₁ * conj (sourceCoefficient K S D Λ ν n₂ f₂) *
      pairFourier K S D n₁ n₂ b₁ b₂ d (v * CanonicalIdealRow.generator K S D z) =
    cubeFourierScalar K S D r₁ r₂ b₁ b₂ d (v * CanonicalIdealRow.generator K S D z) *
      (outerCoefficient K S D Λ ν r₁ r₂ b₁ b₂ false f₁ *
        fixedMultiplierCoefficient K S D ν G r₁ r₂ b₁ b₂ f₁ z d v
          (residualIdeal K S D n₁ n₂ b₁ b₂ false)) *
      conj (outerCoefficient K S D Λ ν r₁ r₂ b₁ b₂ true f₂ *
        fixedMultiplierCoefficient K S D ν G r₁ r₂ b₁ b₂ f₂ z d v
          (residualIdeal K S D n₁ n₂ b₁ b₂ true)) := by
  have he := congrArg (fun w : ℂ => w *
    conj (primitiveCoefficient K S D (pairSupport K S D n₁ n₂ b₁ b₂)
      (pairExponent K S n₁ n₂ b₁ b₂) (Ideal.Quotient.mk _ v)))
    (first_source_pair_frozen K S D hallowed hcal ν n₁ n₂ r₁ r₂ b₁ b₂ hn₁ hn₂ h f₁ f₂ z d)
  obtain ⟨hactive, ht⟩ := cube_packet_data K S D n₁ n₂ r₁ r₂ b₁ b₂ h
  rw [primitive_pair_coefficient K S D n₁ n₂ b₁ b₂ v,
    coefficient_congr K S D _ _ _ _ hactive ht v] at he
  rw [pairFourier_mul_left, cubeFourierScalar_mul_left,
    primitive_pair_coefficient K S D n₁ n₂ b₁ b₂ v,
    coefficient_congr K S D _ _ _ _ hactive ht v]
  simp only [fixedMultiplierCoefficient, residualIdeal, Bool.false_eq_true, if_false, if_true,
    map_mul, starRingEnd_self_apply] at he ⊢
  convert he using 1 <;> ring

def fixedSectorCoefficient
    (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
    (ν G : HeckeCharacter K) (r₁ r₂ b₁ b₂ : Ext) (f z : E) (d : OS)
    (ξ : CanonicalSectors.UnitClasses K Sset Γ) (u : Ext) : ℂ :=
  fixedMultiplierCoefficient K S D ν G r₁ r₂ b₁ b₂ f z d
    ((Sset).unitEquivUnitsInteger K (CanonicalSectors.sectorUnit K Sset Γ ξ)).val u

/-- Every original unit sector is covered by its actual row element;
there is no principal-sector restriction in the first source identity. -/
theorem first_source_pair_sector
    (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
    (hallowed : AllowedGeneratorInput K Sset D)
    {Λ G : HeckeCharacter K} (hcal : ThetaCalibrationInput K Sset D Λ G)
    (ν : HeckeCharacter K) (n₁ n₂ r₁ r₂ b₁ b₂ : Ext)
    (hn₁ : Squarefree n₁.val.val) (hn₂ : Squarefree n₂.val.val)
    (h : SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂)
    (f₁ f₂ z : E) (d : OS) (ξ : CanonicalSectors.UnitClasses K Sset Γ) :
    sourceCoefficient K S D Λ ν n₁ f₁ * conj (sourceCoefficient K S D Λ ν n₂ f₂) *
      pairFourier K S D n₁ n₂ b₁ b₂ d
        (CanonicalSectors.rowElement K Sset Γ D (CanonicalIdealRow.toExterior K S z, ξ)).val =
    cubeFourierScalar K S D r₁ r₂ b₁ b₂ d
        (CanonicalSectors.rowElement K Sset Γ D (CanonicalIdealRow.toExterior K S z, ξ)).val *
      (outerCoefficient K S D Λ ν r₁ r₂ b₁ b₂ false f₁ *
        fixedSectorCoefficient K S D Γ ν G r₁ r₂ b₁ b₂ f₁ z d ξ
          (residualIdeal K S D n₁ n₂ b₁ b₂ false)) *
      conj (outerCoefficient K S D Λ ν r₁ r₂ b₁ b₂ true f₂ *
        fixedSectorCoefficient K S D Γ ν G r₁ r₂ b₁ b₂ f₂ z d ξ
          (residualIdeal K S D n₁ n₂ b₁ b₂ true)) :=
  first_source_pair_multiplier K S D hallowed hcal ν n₁ n₂ r₁ r₂ b₁ b₂ hn₁ hn₂ h
    f₁ f₂ z d ((Sset).unitEquivUnitsInteger K (CanonicalSectors.sectorUnit K Sset Γ ξ)).val

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstSourceFrozen

end
