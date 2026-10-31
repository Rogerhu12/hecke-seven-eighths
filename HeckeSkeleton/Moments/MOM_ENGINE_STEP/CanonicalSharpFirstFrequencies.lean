import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalFirstPhysicalWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDivisorPhysicalSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalActiveColumnNorm
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalFullSupportParameters

/-!
# Sharp first frequencies on the actual divisor branch

The first modulus is the product of the two residual columns and the
active common radical. Its norm therefore divides out both complete
common ideals exactly. Only nonzero original profiles enter the maximum
which defines the physical cutoff. Each complementary mask divisor
uses its own common physical cutoff, keeping its actual norm in the
first frequency length. All original columns and coefficients remain.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)

/-- The actual original ideal of the selected complementary divisor.
Its generator is the literal generator already used by Poisson. -/
def firstPhysicalDivisorIdeal (D : Finset (HeightOneSpectrum A.R)) : A.Exterior :=
  originalFrequencyIdeal
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val

theorem firstPhysicalDivisorIdeal_norm (D : Finset (HeightOneSpectrum A.R)) :
    A.exteriorNorm (firstPhysicalDivisorIdeal D) =
      (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val :=
  originalFrequencyIdeal_norm _
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).property

namespace FirstCommonCharacterBlock

variable (b : FirstCommonCharacterBlock fullI fullJ DE)

/-- The actual first modulus retains the savings from both complete
common factors; bounding it merely by the original product loses them. -/
theorem first_modulus_norm_eq_common_quotient
    (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (right : Finset κ)
    (profiles : ι → κ → 𝓢(mixedEmbedding.euclidean.mixedSpace K, ℂ))
    (i : ι) (hi : i ∈ b.leftColumns left) (j : κ) (hj : j ∈ b.rightColumns right) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨(b.pair hΓ C profiles i j).modulus, (b.pair hΓ C profiles i j).modulus_ne_zero⟩).val =
      (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) *
        (Ideal.absNorm (firstActiveRadical DE.1 DE.2) : ℝ) /
          ((Ideal.absNorm DE.1 : ℝ) * (Ideal.absNorm DE.2 : ℝ)) := by
  have hc : 0 < (Ideal.absNorm DE.1 : ℝ) := by
    rw [← b.common_left]
    exact A.exteriorNorm_pos _
  have hd : 0 < (Ideal.absNorm DE.2 : ℝ) := by
    rw [← b.common_right]
    exact A.exteriorNorm_pos _
  rw [b.first_modulus_norm hΓ C profiles i j,
    b.left_reconstruct left i hi, b.right_reconstruct right j hj]
  simp only [map_mul, Nat.cast_mul, b.common_left, b.common_right, b.activeIdeal_eq]
  field_simp [ne_of_gt hc, ne_of_gt hd]
  <;> ring

theorem first_modulus_norm_le_sharp_product
    (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (right : Finset κ)
    (profiles : ι → κ → 𝓢(mixedEmbedding.euclidean.mixedSpace K, ℂ))
    (Z productExponent : ℝ) (hZ : 1 < Z)
    (i : ι) (hi : i ∈ b.leftColumns left) (j : κ) (hj : j ∈ b.rightColumns right)
    (hproduct : (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤ Z ^ productExponent) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨(b.pair hΓ C profiles i j).modulus, (b.pair hΓ C profiles i j).modulus_ne_zero⟩).val ≤
      Z ^ (productExponent - idealLogLength Z DE.1 - idealLogLength Z DE.2 +
        idealLogLength Z (firstActiveRadical DE.1 DE.2)) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hc : DE.1 ≠ 0 := by
    rw [← b.common_left]
    exact (primePowerProduct b.primes b.leftMultiplicity).property.1
  have hd : DE.2 ≠ 0 := by
    rw [← b.common_right]
    exact (primePowerProduct b.primes b.rightMultiplicity).property.1
  rw [b.first_modulus_norm_eq_common_quotient hΓ C left right profiles i hi j hj]
  calc
    _ ≤ (Z ^ productExponent * (Ideal.absNorm (firstActiveRadical DE.1 DE.2) : ℝ)) /
          ((Ideal.absNorm DE.1 : ℝ) * (Ideal.absNorm DE.2 : ℝ)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hproduct (Nat.cast_nonneg _))
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ = _ := by
      rw [← rpow_idealLogLength Z hZ DE.1 hc,
        ← rpow_idealLogLength Z hZ DE.2 hd,
        ← rpow_idealLogLength Z hZ (firstActiveRadical DE.1 DE.2)
          (firstActiveRadical_ne_zero _ _),
        ← Real.rpow_add hz, ← Real.rpow_add hz, ← Real.rpow_sub hz]
      congr 1
      ring

/-- The selected divisor contributes its own norm, while the sharp
product window is needed only on a nonzero original Gram profile. -/
theorem divisorPhysicalCutoff_le_sharp
    (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (right : Finset κ)
    (profiles : ι → κ → 𝓢(mixedEmbedding.euclidean.mixedSpace K, ℂ))
    (M D : Finset (HeightOneSpectrum A.R)) (radius : {r : ℝ // 0 < r})
    (X : ℝ) (hX : 1 ≤ X)
    (Z productExponent rowExponent cutoffExponent : ℝ) (hZ : 1 < Z)
    (hradius : radius.val = Z ^ (-rowExponent)) (hcutoff : X ≤ Z ^ cutoffExponent)
    (hproduct : ∀ i ∈ left, ∀ j ∈ right, profiles i j ≠ 0 →
      (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤ Z ^ productExponent) :
    (b.finiteSource hΓ C left right profiles M radius X hX).divisorPhysicalCutoff D ≤
      Z ^ (productExponent - idealLogLength Z DE.1 - idealLogLength Z DE.2 +
        idealLogLength Z (firstActiveRadical DE.1 DE.2) +
        idealLogLength Z (firstPhysicalDivisorIdeal D).val - rowExponent + cutoffExponent) := by
  let exponent := productExponent - idealLogLength Z DE.1 - idealLogLength Z DE.2 +
    idealLogLength Z (firstActiveRadical DE.1 DE.2) +
    idealLogLength Z (firstPhysicalDivisorIdeal D).val - rowExponent
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hmask :
      (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val =
      Z ^ idealLogLength Z (firstPhysicalDivisorIdeal D).val := by
    rw [rpow_idealLogLength Z hZ _ (firstPhysicalDivisorIdeal D).property.1]
    exact (firstPhysicalDivisorIdeal_norm D).symm
  have hb := (b.finiteSource hΓ C left right profiles M radius X hX).divisorPhysicalCutoff_le_supported
    D (Z ^ exponent) (Real.rpow_nonneg hz.le _) (by
      intro i hi j hj hprofile
      have hp : profiles i j ≠ 0 := hprofile
      have hn := b.first_modulus_norm_le_sharp_product hΓ C left right profiles Z
        productExponent hZ i hi j hj
        (hproduct i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hp)
      change ((radius.val *
        (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
          (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val *
        (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
          ⟨(b.pair hΓ C profiles i j).modulus,
            (b.pair hΓ C profiles i j).modulus_ne_zero⟩).val)⁻¹)⁻¹ ≤ _
      rw [inv_inv, hradius, hmask]
      apply (mul_le_mul_of_nonneg_left hn
        (mul_nonneg (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hz.le _))).trans_eq
      rw [← Real.rpow_add hz, ← Real.rpow_add hz]
      congr 1
      dsimp only [exponent]
      ring)
  calc
    _ ≤ X * Z ^ exponent := hb
    _ ≤ Z ^ cutoffExponent * Z ^ exponent :=
      mul_le_mul_of_nonneg_right hcutoff (Real.rpow_nonneg hz.le _)
    _ = _ := by
      rw [← Real.rpow_add hz]
      congr 1
      dsimp only [exponent]
      ring

end FirstCommonCharacterBlock

namespace CompleteMovingRowRecipe

variable {ω ψ : HeckeCharacter K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {Index : Type*} {data : Index → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]

theorem fullSupportRadius_eq_negative_m (a : RealParameters) (Z : ℝ) (hZ : 1 < Z) :
    (Q.fullSupportRadius Z (a.m + a.q) (zero_lt_one.trans hZ)).val =
      Z ^ (-(Q.fullSupportParameters a Z).m) := by
  rw [Real.rpow_neg (zero_lt_one.trans hZ).le,
    ← Q.fullSupportRadius_inverse_eq_parameters_m a Z hZ, inv_inv]

/-- The actual original norm profiles give the sharp first frequency
length on each original divisor, before selecting a retained dyad.
The parameter repartition pays the complete effective old support. -/
theorem canonicalFirstDivisorPhysicalCutoff
    (W : NormProfileRecipe data) (ξ : Index) (a : RealParameters) (Z t Y₁ Y₂ : ℝ)
    (C : A.GeneralArithmeticContext σ η hS)
    (cap : ℕ) (annulus loss cutoffExponent : ℝ)
    (hannulus : 1 ≤ annulus) (hcap : (data ξ).geometry.slotCount ≤ cap)
    (hannulusZ : annulus ^ (cap + 2) ≤ Z ^ loss)
    {centered : Bool} {floor padding : ℝ}
    (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
    {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}
    (profiles : RawProfileWindow rowDomain heightDomain window orders (data ξ) amplitude)
    (hrows : ∀ u ∈ pairedRows (data ξ) a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
    (X : ℝ) (hX : 1 ≤ X) (hcutoff : X ≤ Z ^ cutoffExponent) :
    let atoms := (Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) a Z t;
    let raw := atoms.raw Y₁ Y₂;
    ∀ DE : FirstZeroLabel raw.exteriorColumns raw.exteriorColumns raw.columnExterior raw.columnExterior,
    ∀ D : Finset (HeightOneSpectrum A.R),
      ((raw.originalFirstBlocks C DE).finiteSource
        (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) C
        raw.exteriorColumns raw.exteriorColumns
        (fun i j => ((atoms.values Y₁ Y₂).coefficient centered i *
          star ((atoms.values Y₁ Y₂).coefficient centered j)) • CanonicalRowBall.archTest K A.Sf 1)
        ∅ (Q.fullSupportRadius Z (a.m + a.q) (zero_lt_one.trans domain.scale)) X hX).divisorPhysicalCutoff D ≤
        Z ^ (2 * (a.n₁ + a.n₂ + (data ξ).geometry.totalLength) -
          idealLogLength Z DE.val.1 - idealLogLength Z DE.val.2 +
          idealLogLength Z (firstActiveRadical DE.val.1 DE.val.2) +
          idealLogLength Z (firstPhysicalDivisorIdeal D).val -
          (Q.fullSupportParameters a Z).m + (2 * loss + cutoffExponent)) := by
  dsimp only
  intro DE D
  let atoms := (Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) a Z t
  let raw := atoms.raw Y₁ Y₂
  let gram := fun i j => ((atoms.values Y₁ Y₂).coefficient centered i *
    star ((atoms.values Y₁ Y₂).coefficient centered j)) • CanonicalRowBall.archTest K A.Sf 1
  have hb := (raw.originalFirstBlocks C DE).divisorPhysicalCutoff_le_sharp
    (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) C
    raw.exteriorColumns raw.exteriorColumns gram ∅ D
    (Q.fullSupportRadius Z (a.m + a.q) (zero_lt_one.trans domain.scale)) X hX
    Z (2 * (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss))
    (Q.fullSupportParameters a Z).m cutoffExponent domain.scale
    (Q.fullSupportRadius_eq_negative_m a Z domain.scale) hcutoff (by
      intro i hi j hj hprofile
      exact atoms.original_active_gram_pair_norm_of_domain profiles cap annulus loss
        hannulus hcap hannulusZ hrows ht hwindow domain
        (CanonicalRowBall.archTest K A.Sf 1) (i, j) (Finset.mem_product.mpr ⟨hi, hj⟩) hprofile)
  convert hb using 1 <;> congr 1 <;> ring

end CompleteMovingRowRecipe

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.first_modulus_norm_eq_common_quotient
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.divisorPhysicalCutoff_le_sharp
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalFirstDivisorPhysicalCutoff
