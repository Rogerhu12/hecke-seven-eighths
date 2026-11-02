import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalFirstPhysicalWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDivisorPhysicalSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalActiveColumnNorm
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalFullSupportParameters

set_option linter.unusedSectionVars false

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
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end CompleteMovingRowRecipe

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.first_modulus_norm_eq_common_quotient
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.divisorPhysicalCutoff_le_sharp
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalFirstDivisorPhysicalCutoff
