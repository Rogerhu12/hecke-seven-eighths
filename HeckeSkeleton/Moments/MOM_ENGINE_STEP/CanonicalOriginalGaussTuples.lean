import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalParentTuples
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonTupleFibers
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectSecondStages
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstSecondSource

/-!
# Original occurrence tuples on the six actual Gauss sources

The two plain occurrences and every original prime occurrence are retained,
with unit padding to the fixed cap. Common-support extraction has its real
divisor multiplicity. Pool extraction adds the actual valuation allocation
factor, without asserting that the quotient tuple is injective.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open DedekindZetaZeroFree.LargeSieve
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckePort.IdealMobiusDivisorSum HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}

namespace ActualGaussSource

/-- A computed tuple certificate on this exact column carrier. -/
structure OriginalTupleData {ι : Type*} (G : ActualGaussSource C ι)
    (k multiplicity : ℕ) where
  factors : ι × ι → Fin k → Ideal (𝓞 K)
  fiber_card : ∀ v,
    ((G.columns ×ˢ G.columns).filter (fun ij => factors ij = v)).card ≤ multiplicity
  product : ∀ ij ∈ G.columns ×ˢ G.columns,
    PowerfulDiagonal.tupleIdeal (factors ij) = (G.ideal ij.1).val * (G.ideal ij.2).val

end ActualGaussSource

variable {Γ : Subgroup A.U} {ω ψ : HeckeCharacter K}
variable {data : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}

namespace ParentRawAtoms

variable (raw : ParentRawAtoms
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) data a Z t Y₁ Y₂)

/-- Pull back the original tuple only through a genuine index embedding.
The six applications below use `id` or the actual valuation subtype. -/
theorem original_exterior_pair_data_reindex
    (cap : ℕ) (hcap : data.geometry.slotCount ≤ cap)
    {ι : Type*} (columns : Finset ι) (index : ι → raw.Column)
    (hinj : Function.Injective index)
    (hcolumns : ∀ i ∈ columns, index i ∈ raw.exteriorColumns) :
    Set.InjOn (fun ij r =>
      (raw.originalPairExteriorFactors cap hcap (index ij.1, index ij.2) r).val)
        (columns ×ˢ columns : Set (ι × ι)) ∧
      ∀ ij ∈ columns ×ˢ columns,
        PowerfulDiagonal.tupleIdeal (fun r =>
          (raw.originalPairExteriorFactors cap hcap (index ij.1, index ij.2) r).val) =
            (raw.columnExterior (index ij.1)).val * (raw.columnExterior (index ij.2)).val := by
  have he (ij : ι × ι) (hij : ij ∈ columns ×ˢ columns) :=
    raw.originalPairExteriorFactors_val cap hcap (index ij.1, index ij.2)
      (hcolumns ij.1 (Finset.mem_product.mp hij).1)
      (hcolumns ij.2 (Finset.mem_product.mp hij).2)
  constructor
  · intro ij hij uv huv htuple
    have hij' : ij ∈ (columns ×ˢ columns : Finset (ι × ι)) := by
      simpa only [Finset.mem_product, Set.mem_prod, Finset.mem_coe] using hij
    have huv' : uv ∈ (columns ×ˢ columns : Finset (ι × ι)) := by
      simpa only [Finset.mem_product, Set.mem_prod, Finset.mem_coe] using huv
    have hpair := raw.originalPairIdealFactors_injective cap hcap
      ((he ij hij').symm.trans (htuple.trans (he uv huv')))
    exact Prod.ext (hinj (congrArg Prod.fst hpair)) (hinj (congrArg Prod.snd hpair))
  · intro ij hij
    rw [he ij hij, raw.originalPairIdealFactors_product,
      raw.columnExterior_val_of_mem (index ij.1) (hcolumns ij.1 (Finset.mem_product.mp hij).1),
      raw.columnExterior_val_of_mem (index ij.2) (hcolumns ij.2 (Finset.mem_product.mp hij).2)]

/-- The actual common-support quotient, with no residual injectivity
premise and no supplied tuple count. -/
def originalSupportTuples (G : ActualGaussSource C raw.Column)
    (cap : ℕ) (hcap : data.geometry.slotCount ≤ cap)
    (common : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K)) (hD : D ≠ 0)
    (hcolumns : G.columns ⊆ raw.exteriorColumns)
    (hcommon : ∀ i ∈ G.columns, supportExtract (raw.columnExterior i).val common = D)
    (hresidual : ∀ i, (G.ideal i).val = supportResidual (raw.columnExterior i).val common) :
    G.OriginalTupleData (2 * (cap + 2))
      (idealDivisorCount (D ^ 2) ^ (2 * (cap + 2))) := by
  have original := raw.original_exterior_pair_data cap hcap G.columns G.columns hcolumns hcolumns
  have extracted := actual_support_residual_pair_data G.columns raw.columnExterior
    (raw.originalPairExteriorFactors cap hcap) original.1 original.2 common D hD hcommon
  exact {
    factors := fun ij r =>
      (actualSupportResidualFactors common (raw.originalPairExteriorFactors cap hcap ij) r).val
    fiber_card := extracted.2
    product := fun ij hij => (extracted.1 ij hij).trans
      (congrArg₂ (fun I J : Ideal (𝓞 K) => I * J)
        (hresidual ij.1).symm (hresidual ij.2).symm) }

/-- The actual pool quotient keeps the whole original valuation
subtype and pays both finite information losses. -/
def originalSupportPoolTuples
    {bad : Finset (HeightOneSpectrum (𝓞 K))} {base ell eps : ℝ}
    {pool : PowerScaleExteriorPool A bad base ell eps}
    (d : FirstGaussPoolData C pool raw.Column) (coefficient : raw.Column → ℂ)
    (prime : ExteriorPrime A) (n : ℕ)
    (cap : ℕ) (hcap : data.geometry.slotCount ≤ cap)
    (common : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K)) (hD : D ≠ 0)
    (hcolumns : d.columns ⊆ raw.exteriorColumns)
    (hcommon : ∀ i ∈ d.columns, supportExtract (raw.columnExterior i).val common = D)
    (hresidual : ∀ i, (d.ideal i).val = supportResidual (raw.columnExterior i).val common) :
    (d.residualSource prime n coefficient).OriginalTupleData (2 * (cap + 2))
      (idealDivisorCount (D ^ 2) ^ (2 * (cap + 2)) *
        (n + n + 1) ^ (2 * (cap + 2))) := by
  let columns : Finset (d.valuationColumns prime n) := Finset.univ
  let original := fun ij : (d.valuationColumns prime n) × (d.valuationColumns prime n) =>
    raw.originalPairExteriorFactors cap hcap (ij.1.val, ij.2.val)
  have hmem (i : d.valuationColumns prime n) : i.val ∈ d.columns :=
    (Finset.mem_filter.mp i.property).1
  have originalData := raw.original_exterior_pair_data_reindex cap hcap columns
    (fun i => i.val) Subtype.val_injective (fun i _ => hcolumns (hmem i))
  have commonData := actual_support_residual_pair_data columns
    (fun i => raw.columnExterior i.val) original originalData.1 originalData.2 common D hD
      (fun i _ => hcommon i.val (hmem i))
  have hproduct (ij : (d.valuationColumns prime n) × (d.valuationColumns prime n))
      (hij : ij ∈ columns ×ˢ columns) :
      PowerfulDiagonal.tupleIdeal (fun r => (actualSupportResidualFactors common (original ij) r).val) =
        (d.ideal ij.1.val).val * (d.ideal ij.2.val).val :=
    (commonData.1 ij hij).trans (congrArg₂ (fun I J : Ideal (𝓞 K) => I * J)
      (hresidual ij.1.val).symm (hresidual ij.2.val).symm)
  refine {
    factors := fun ij => actualResidualFactorTuple C prime
      (actualSupportResidualFactors common (original ij))
    fiber_card := ?_
    product := ?_ }
  · intro v
    apply actual_support_amplifier_tuple_fiber_card C prime (columns ×ˢ columns) original
      (by simpa only [Finset.coe_product] using originalData.1)
      common (D ^ 2) (pow_ne_zero 2 hD) _ _ v
    · intro ij hij
      rw [originalData.2 ij hij,
        supportExtract_mul _ _ (raw.columnExterior ij.1.val).property.1
          (raw.columnExterior ij.2.val).property.1 common,
        hcommon ij.1.val (hmem ij.1), hcommon ij.2.val (hmem ij.2), pow_two]
    · intro ij hij
      have hs := actual_factor_valuation_sum prime (actualSupportResidualFactors common (original ij))
        (ExteriorIdealEuler.mul (d.ideal ij.1.val) (d.ideal ij.2.val)) (hproduct ij hij)
      rw [primeExponent_exterior_mul, (d.residualPresentation prime n ij.1).original_valuation,
        (d.residualPresentation prime n ij.2).original_valuation] at hs
      exact hs
  · intro ij hij
    exact actual_residual_pair_tuple_product C prime
      (actualSupportResidualFactors common (original ij)) (d.ideal ij.1.val) (d.ideal ij.2.val)
      (hproduct ij hij) (d.residualPresentation prime n ij.1) (d.residualPresentation prime n ij.2)

end ParentRawAtoms


section Blocks

variable [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (raw : ParentRawAtoms
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) data a Z t Y₁ Y₂)
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock raw.columnExterior raw.columnExterior DE}
variable {profiles : raw.Column → raw.Column → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}} {mask : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := E) hΓ μv b C
  raw.exteriorColumns raw.exteriorColumns profiles finiteTest radius mask}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}

namespace FirstBlockDirectData

variable (p : FirstBlockDirectData chart M X hX)
variable (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)

/-- The original left direct tuple on the unchanged divisor/character source. -/
def originalLeftTuples (cap : ℕ) (hcap : data.geometry.slotCount ≤ cap) :
    (p.leftData.directSource (p.leftDivisorCoefficient S χ)).OriginalTupleData
      (2 * (cap + 2)) (idealDivisorCount (DE.1 ^ 2) ^ (2 * (cap + 2))) := by
  apply raw.originalSupportTuples _ cap hcap (primeSupport DE.1) DE.1
  · rw [← b.common_left]
    exact (primePowerProduct b.primes b.leftMultiplicity).property.1
  · intro i hi
    have hi' : i ∈ b.leftColumns raw.exteriorColumns := by
      simpa only [DirectGaussData.directSource, p.left_columns] using hi
    exact (Finset.mem_filter.mp hi').1
  · intro i hi
    have hi' : i ∈ b.leftColumns raw.exteriorColumns := by
      simpa only [DirectGaussData.directSource, p.left_columns] using hi
    exact (Finset.mem_filter.mp hi').2
  · intro i
    simpa only [DirectGaussData.directSource, p.left_ideal] using b.left_residual i

/-- The original right direct tuple on the unchanged divisor/character source. -/
def originalRightTuples (cap : ℕ) (hcap : data.geometry.slotCount ≤ cap) :
    (p.rightData.directSource (p.rightDivisorCoefficient S χ)).OriginalTupleData
      (2 * (cap + 2)) (idealDivisorCount (DE.2 ^ 2) ^ (2 * (cap + 2))) := by
  apply raw.originalSupportTuples _ cap hcap (primeSupport DE.1) DE.2
  · rw [← b.common_right]
    exact (primePowerProduct b.primes b.rightMultiplicity).property.1
  · intro i hi
    have hi' : i ∈ b.rightColumns raw.exteriorColumns := by
      simpa only [DirectGaussData.directSource, p.right_columns] using hi
    exact (Finset.mem_filter.mp hi').1
  · intro i hi
    have hi' : i ∈ b.rightColumns raw.exteriorColumns := by
      simpa only [DirectGaussData.directSource, p.right_columns] using hi
    exact (Finset.mem_filter.mp hi').2
  · intro i
    simpa only [DirectGaussData.directSource, p.right_ideal] using b.right_residual i

end FirstBlockDirectData

namespace FirstBlockPoolData

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {base ell eps : ℝ}
variable {pool : PowerScaleExteriorPool A bad base ell eps}
variable (p : FirstBlockPoolData chart pool M X hX)
variable (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)

/-- The original left main tuple keeps the same first common-divisor count. -/
def originalLeftMainTuples (cap : ℕ) (hcap : data.geometry.slotCount ≤ cap) :
    ((p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)).OriginalTupleData
      (2 * (cap + 2)) (idealDivisorCount (DE.1 ^ 2) ^ (2 * (cap + 2))) := by
  apply raw.originalSupportTuples _ cap hcap (primeSupport DE.1) DE.1
  · rw [← b.common_left]
    exact (primePowerProduct b.primes b.leftMultiplicity).property.1
  · intro i hi
    have hi' : i ∈ b.leftColumns raw.exteriorColumns := by
      simpa only [FirstGaussPoolData.mainSource, p.divisorPools.left_columns S,
        p.left_columns] using hi
    exact (Finset.mem_filter.mp hi').1
  · intro i hi
    have hi' : i ∈ b.leftColumns raw.exteriorColumns := by
      simpa only [FirstGaussPoolData.mainSource, p.divisorPools.left_columns S,
        p.left_columns] using hi
    exact (Finset.mem_filter.mp hi').2
  · intro i
    simpa only [FirstGaussPoolData.mainSource, p.divisorPools.left_ideal S,
      p.left_ideal] using b.left_residual i

/-- The left valuation tuple retains the full exponent `n`; the original
first-common and valuation allocation multiplicities are both paid. -/
def originalLeftPoolTuples (prime : ExteriorPrime A) (n : ℕ)
    (cap : ℕ) (hcap : data.geometry.slotCount ≤ cap) :
    ((p.divisorPools.leftData S).residualSource prime n
      (p.leftDivisorCoefficient S χ)).OriginalTupleData (2 * (cap + 2))
      (idealDivisorCount (DE.1 ^ 2) ^ (2 * (cap + 2)) *
        (n + n + 1) ^ (2 * (cap + 2))) := by
  apply raw.originalSupportPoolTuples (p.divisorPools.leftData S)
    (p.leftDivisorCoefficient S χ) prime n cap hcap (primeSupport DE.1) DE.1
  · rw [← b.common_left]
    exact (primePowerProduct b.primes b.leftMultiplicity).property.1
  · intro i hi
    have hi' : i ∈ b.leftColumns raw.exteriorColumns := by
      simpa only [p.divisorPools.left_columns S, p.left_columns] using hi
    exact (Finset.mem_filter.mp hi').1
  · intro i hi
    have hi' : i ∈ b.leftColumns raw.exteriorColumns := by
      simpa only [p.divisorPools.left_columns S, p.left_columns] using hi
    exact (Finset.mem_filter.mp hi').2
  · intro i
    simpa only [p.divisorPools.left_ideal S, p.left_ideal] using b.left_residual i

/-- The original right main tuple keeps the same first common-divisor count. -/
def originalRightMainTuples (cap : ℕ) (hcap : data.geometry.slotCount ≤ cap) :
    ((p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)).OriginalTupleData
      (2 * (cap + 2)) (idealDivisorCount (DE.2 ^ 2) ^ (2 * (cap + 2))) := by
  apply raw.originalSupportTuples _ cap hcap (primeSupport DE.1) DE.2
  · rw [← b.common_right]
    exact (primePowerProduct b.primes b.rightMultiplicity).property.1
  · intro i hi
    have hi' : i ∈ b.rightColumns raw.exteriorColumns := by
      simpa only [FirstGaussPoolData.mainSource, p.divisorPools.right_columns S,
        p.right_columns] using hi
    exact (Finset.mem_filter.mp hi').1
  · intro i hi
    have hi' : i ∈ b.rightColumns raw.exteriorColumns := by
      simpa only [FirstGaussPoolData.mainSource, p.divisorPools.right_columns S,
        p.right_columns] using hi
    exact (Finset.mem_filter.mp hi').2
  · intro i
    simpa only [FirstGaussPoolData.mainSource, p.divisorPools.right_ideal S,
      p.right_ideal] using b.right_residual i

/-- The right valuation tuple retains the full exponent `n`; the original
first-common and valuation allocation multiplicities are both paid. -/
def originalRightPoolTuples (prime : ExteriorPrime A) (n : ℕ)
    (cap : ℕ) (hcap : data.geometry.slotCount ≤ cap) :
    ((p.divisorPools.rightData S).residualSource prime n
      (p.rightDivisorCoefficient S χ)).OriginalTupleData (2 * (cap + 2))
      (idealDivisorCount (DE.2 ^ 2) ^ (2 * (cap + 2)) *
        (n + n + 1) ^ (2 * (cap + 2))) := by
  apply raw.originalSupportPoolTuples (p.divisorPools.rightData S)
    (p.rightDivisorCoefficient S χ) prime n cap hcap (primeSupport DE.1) DE.2
  · rw [← b.common_right]
    exact (primePowerProduct b.primes b.rightMultiplicity).property.1
  · intro i hi
    have hi' : i ∈ b.rightColumns raw.exteriorColumns := by
      simpa only [p.divisorPools.right_columns S, p.right_columns] using hi
    exact (Finset.mem_filter.mp hi').1
  · intro i hi
    have hi' : i ∈ b.rightColumns raw.exteriorColumns := by
      simpa only [p.divisorPools.right_columns S, p.right_columns] using hi
    exact (Finset.mem_filter.mp hi').2
  · intro i
    simpa only [p.divisorPools.right_ideal S, p.right_ideal] using b.right_residual i

end FirstBlockPoolData
end Blocks

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.original_exterior_pair_data_reindex
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.originalSupportTuples
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.originalSupportPoolTuples
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.originalLeftTuples
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.originalRightTuples
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.originalLeftMainTuples
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.originalRightMainTuples
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.originalLeftPoolTuples
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.originalRightPoolTuples
