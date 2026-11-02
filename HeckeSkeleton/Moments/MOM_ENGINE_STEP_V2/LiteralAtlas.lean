import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SourceCartesianCover
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralTransforms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.EffectiveChildSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridLeafOrdinaryBinding

set_option linter.unusedSectionVars false

/-!
# The actual source index after occurrence extraction

The existing source atlas transports its residual dictionary across
equal finite carriers. Those proof transports change no atom support
or original source index. The identities here expose that fact, so the
literal coefficient and location constructions can be applied to the
same already constructed covered leaf.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K] {A : SArithmeticData K}
variable {ι : Type*} {columns otherColumns : Finset ι}
variable {ideal : ι → A.Exterior} {k : ℕ}

namespace CartesianSourceReindex

/-- A finite-carrier transport affects only the proof fields of the
actual expansion dictionary. -/
private theorem carrier_cast_plain₁ (h : columns = otherColumns)
    (e : CartesianSourceReindex columns ideal k =
      CartesianSourceReindex otherColumns ideal k)
    (R : CartesianSourceReindex columns ideal k) :
    (cast e R).plain₁ = R.plain₁ := by
  sorry

private theorem carrier_cast_plain₂ (h : columns = otherColumns)
    (e : CartesianSourceReindex columns ideal k =
      CartesianSourceReindex otherColumns ideal k)
    (R : CartesianSourceReindex columns ideal k) :
    (cast e R).plain₂ = R.plain₂ := by
  sorry

private theorem carrier_cast_slots (h : columns = otherColumns)
    (e : CartesianSourceReindex columns ideal k =
      CartesianSourceReindex otherColumns ideal k)
    (R : CartesianSourceReindex columns ideal k) :
    (cast e R).slots = R.slots := by
  sorry

private theorem carrier_cast_index (h : columns = otherColumns)
    (e : CartesianSourceReindex columns ideal k =
      CartesianSourceReindex otherColumns ideal k)
    (R : CartesianSourceReindex columns ideal k) :
    (cast e R).index = R.index := by
  sorry

variable (R : CartesianSourceReindex columns ideal k)
variable (P : Finset (Ideal (𝓞 K)))
variable (b : SupportCartesianBranch R.plain₁ R.plain₂ R.slots P)
variable (J : ι → A.Exterior)
variable (hJ : ∀ i ∈ columns, (J i).val = supportResidual (ideal i).val P)

@[simp] theorem supportResidualLabelBranch_plain₁ :
    (R.supportResidualLabelBranch P b J hJ).plain₁ =
      SupportCartesian.plainResidual R.plain₁ P b.plainExtract₁ := by
  sorry

@[simp] theorem supportResidualLabelBranch_plain₂ :
    (R.supportResidualLabelBranch P b J hJ).plain₂ =
      SupportCartesian.plainResidual R.plain₂ P b.plainExtract₂ := by
  sorry

@[simp] theorem supportResidualLabelBranch_slots :
    (R.supportResidualLabelBranch P b J hJ).slots =
      fun j => SupportCartesian.primeLive (R.slots (SlotRestriction.index b.keep j)) P := by
  sorry

@[simp] theorem supportResidualLabelBranch_index :
    (R.supportResidualLabelBranch P b J hJ).index =
      fun i => R.index (b.reconstruct i) := by
  sorry

end CartesianSourceReindex

namespace SourceCartesianAtlas

variable (T : SourceCartesianAtlas columns ideal)
variable (P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
variable (J : ι → A.Exterior)
variable (hJ : ∀ i ∈ columns, (J i).val = supportResidual (ideal i).val P)
variable (a : T.labels P D)

@[simp] theorem residualReindex_plain₁ :
    (T.residualReindex P D J hJ a).plain₁ =
      SupportCartesian.plainResidual T.reindex.plain₁ P (T.branch P D a).plainExtract₁ := by
  sorry

@[simp] theorem residualReindex_plain₂ :
    (T.residualReindex P D J hJ a).plain₂ =
      SupportCartesian.plainResidual T.reindex.plain₂ P (T.branch P D a).plainExtract₂ := by
  sorry

@[simp] theorem residualReindex_slots :
    (T.residualReindex P D J hJ a).slots = fun j =>
      SupportCartesian.primeLive
        (T.reindex.slots (SlotRestriction.index (T.branch P D a).keep j)) P := by
  sorry

/-- The original column is reconstructed by the actual occurrence map,
not selected anew from an equality of complete ideals. -/
@[simp] theorem residualReindex_index :
    (T.residualReindex P D J hJ a).index =
      fun i => T.reindex.index ((T.branch P D a).reconstruct i) := by
  sorry

end SourceCartesianAtlas
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# Original occurrence indices in the actual pool cover

The main and valuation sources use the existing Cartesian covers. The
finite-carrier equality transports in those constructors alter only
their proof fields. The package below exposes their computed supports,
slot count and index together, so no arbitrary residual dictionary has
to be supplied when constructing the literal two-stage profiles.

On a valuation branch the original index is lifted to the actual
valuation subtype. Its value on every retained tuple is the original
occurrence reconstruction. The off-support fallback remains the one in
the existing source; no new column or source is selected.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K] {A : SArithmeticData K}
variable {ι : Type*} {columns otherColumns : Finset ι}
variable {ideal : ι → A.Exterior}

namespace SourceCartesianAtlas

/-- The computational part of the actual atlas, packaged independently
of its source carrier. Its slot indices are retained by the sigma. -/
def literalDictionary (T : SourceCartesianAtlas columns ideal) :
    Σ n : ℕ, (Finset (Ideal (𝓞 K)) × Finset (Ideal (𝓞 K))) ×
      (Fin n → Finset (HeightOneSpectrum (𝓞 K))) ×
        (AllocationColumn K n → ι) :=
  ⟨T.slotCount, (T.reindex.plain₁, T.reindex.plain₂), T.reindex.slots, T.reindex.index⟩

private theorem literalDictionary_cast (h : columns = otherColumns)
    (e : SourceCartesianAtlas columns ideal = SourceCartesianAtlas otherColumns ideal)
    (T : SourceCartesianAtlas columns ideal) :
    (HeckeSkeleton.Moments.EngineStepV2.SourceCartesianAtlas.literalDictionary (cast e T)) = (HeckeSkeleton.Moments.EngineStepV2.SourceCartesianAtlas.literalDictionary T) := by
  sorry

end SourceCartesianAtlas

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {htrace : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η htrace}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {originalColumns : Finset ι} {originalIdeal : ι → A.Exterior}

namespace FirstGaussPoolData

variable (d : FirstGaussPoolData C P ι)
variable (T : SourceCartesianAtlas originalColumns originalIdeal)
variable (S : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
variable (hcolumns : d.columns =
  originalColumns.filter (fun i => supportExtract (originalIdeal i).val S = D))
variable (hideal : ∀ i, (d.ideal i).val = supportResidual (originalIdeal i).val S)
variable (c : ι → ℂ)

/-- The existing main cover carries precisely the retained original
plain and prime occurrences and the actual reconstruction index. -/
theorem mainAtlasForLabel_literalDictionary (a : T.labels S D) :
    (HeckeSkeleton.Moments.EngineStepV2.SourceCartesianAtlas.literalDictionary (d.mainAtlasForLabel T S D hcolumns hideal c a)) =
      ⟨(T.branch S D a).keep.card,
        (SupportCartesian.plainResidual T.reindex.plain₁ S
            (T.branch S D a).plainExtract₁,
          SupportCartesian.plainResidual T.reindex.plain₂ S
            (T.branch S D a).plainExtract₂),
        (fun j => SupportCartesian.primeLive
          (T.reindex.slots (SlotRestriction.index (T.branch S D a).keep j)) S),
        (fun i => T.reindex.index ((T.branch S D a).reconstruct i))⟩ := by
  sorry

/-- This is the identical package at the public whole-main cover. -/
theorem mainSourceCartesianCover_literalDictionary (a : T.labels S D) :
    (HeckeSkeleton.Moments.EngineStepV2.SourceCartesianAtlas.literalDictionary ((d.mainSourceCartesianCover T S D hcolumns hideal c).branch a)) =
      ⟨(T.branch S D a).keep.card,
        (SupportCartesian.plainResidual T.reindex.plain₁ S
            (T.branch S D a).plainExtract₁,
          SupportCartesian.plainResidual T.reindex.plain₂ S
            (T.branch S D a).plainExtract₂),
        (fun j => SupportCartesian.primeLive
          (T.reindex.slots (SlotRestriction.index (T.branch S D a).keep j)) S),
        (fun i => T.reindex.index ((T.branch S D a).reconstruct i))⟩ := by
  sorry

variable (p : ExteriorPrime A) (n : ℕ)

/-- The actual valuation source lifts its retained tuple into the
original valuation subtype. On the real carrier its value is exact. -/
theorem residualSource_original_support_index_val
    (b : SupportCartesianBranch T.reindex.plain₁ T.reindex.plain₂ T.reindex.slots
      (S ∪ {p.val.asIdeal}))
    (hw : T.reindex.index b.witness ∈ d.valuationColumns p n)
    (i : AllocationColumn K b.keep.card) (hi : i ∈ b.residualColumns) :
    ((d.residualSource_cartesianBranch_of_original_support
      T S D hcolumns hideal p n c b hw).index i).val =
        T.reindex.index (b.reconstruct i) := by
  sorry

/-- The existing combined-support cover has the actual retained
occurrences. The displayed subtype index is the original constructor,
including its harmless off-carrier default. -/
theorem combinedAtlasForLabel_literalDictionary
    (a : d.combinedLabels T S p n) :
    let b := d.combinedBranchForLabel T S D hcolumns p n a
    let hb := (d.combinedBranchForLabel_spec T S D hcolumns p n a).2
    (HeckeSkeleton.Moments.EngineStepV2.SourceCartesianAtlas.literalDictionary (d.combinedAtlasForLabel T S D hcolumns hideal p n c a)) =
      ⟨b.keep.card,
        (SupportCartesian.plainResidual T.reindex.plain₁ (S ∪ {p.val.asIdeal})
            b.plainExtract₁,
          SupportCartesian.plainResidual T.reindex.plain₂ (S ∪ {p.val.asIdeal})
            b.plainExtract₂),
        (fun j => SupportCartesian.primeLive
          (T.reindex.slots (SlotRestriction.index b.keep j)) (S ∪ {p.val.asIdeal})),
        (d.residualSource_cartesianBranch_of_original_support
          T S D hcolumns hideal p n c b hb).index⟩ := by
  sorry

/-- Both the actual first common support and the pool valuation are
kept in the cover key, before any continuous Fourier parameter. -/
theorem residualSourceCartesianCover_literalDictionary
    (a : d.combinedLabels T S p n) :
    let b := d.combinedBranchForLabel T S D hcolumns p n a
    let hb := (d.combinedBranchForLabel_spec T S D hcolumns p n a).2
    (HeckeSkeleton.Moments.EngineStepV2.SourceCartesianAtlas.literalDictionary ((d.residualSourceCartesianCover T S D hcolumns hideal p n c).branch a)) =
      ⟨b.keep.card,
        (SupportCartesian.plainResidual T.reindex.plain₁ (S ∪ {p.val.asIdeal})
            b.plainExtract₁,
          SupportCartesian.plainResidual T.reindex.plain₂ (S ∪ {p.val.asIdeal})
            b.plainExtract₂),
        (fun j => SupportCartesian.primeLive
          (T.reindex.slots (SlotRestriction.index b.keep j)) (S ∪ {p.val.asIdeal})),
        (d.residualSource_cartesianBranch_of_original_support
          T S D hcolumns hideal p n c b hb).index⟩ := by
  sorry

end FirstGaussPoolData
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# Actual finite supports after occurrence extraction

The smooth profiles are not masked. At a retained ideal their actual
nonzero value gives membership in the original support once the deleted
primes are avoided. The first and second occurrence extractions preserve
this assertion, using their original witnesses and exact reconstruction.

An allocation divisor is coprime to every already deleted prime because
it divides an actual original occurrence. Consequently the child mask,
the computed Fourier profile and the literal quotient support give the
effective-support fields of the actual calibration. There is no assumed
polynomial equality or final energy bound.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open WholeAllocation

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralSupport

def Avoids (I : Ideal (𝓞 K)) (S : Finset (Ideal (𝓞 K))) : Prop :=
  ∀ p ∈ S, IsCoprime I p

theorem avoids_union (I : Ideal (𝓞 K)) (S T : Finset (Ideal (𝓞 K))) :
    Avoids I (S ∪ T) ↔ Avoids I S ∧ Avoids I T := by
  sorry

theorem residual_avoids (I : Ideal (𝓞 K)) (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ p ∈ S, Prime p) : Avoids (supportResidual I S) S := by
  sorry

theorem residual_dvd (I : Ideal (𝓞 K)) (hI : I ≠ 0) (S : Finset (Ideal (𝓞 K))) :
    supportResidual I S ∣ I := by
  sorry

theorem extract_dvd (I : Ideal (𝓞 K)) (hI : I ≠ 0) (S : Finset (Ideal (𝓞 K))) :
    supportExtract I S ∣ I := by
  sorry

theorem plain_residual_mem (T S : Finset (Ideal (𝓞 K)))
    (hS : ∀ p ∈ S, Prime p) (D I : Ideal (𝓞 K)) (hD : D ≠ 0) (hI : I ≠ 0)
    (hsmooth : primeSupport D ⊆ S) (havoid : Avoids I S) (hmem : D * I ∈ T) :
    I ∈ SupportCartesian.plainResidual T S D := by
  sorry

end CanonicalLiteralSupport

namespace CanonicalLiteralRectangles.Atoms

open CanonicalLiteralSupport

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)

/-- Exact one-occurrence support, with its finite deletion condition.
The actual constructors below derive this from the original profiles. -/
structure SupportData (excluded : Finset (Ideal (𝓞 K))) : Prop where
  left_avoids : ∀ I ∈ d.plain₁, Avoids I excluded
  right_avoids : ∀ I ∈ d.plain₂, Avoids I excluded
  slot_avoids : ∀ j p, p ∈ d.slots j → Avoids p.asIdeal excluded
  left_mem : ∀ r I, d.rectangleLeftWeight r I ≠ 0 → Avoids I.val excluded → I.val ∈ d.plain₁
  right_mem : ∀ r I, d.rightWeight r I ≠ 0 → Avoids I.val excluded → I.val ∈ d.plain₂
  slot_mem : ∀ j p, d.slotWeight j p ≠ 0 → Avoids p.asIdeal excluded → p ∈ d.slots j

namespace SupportData

variable {d} {excluded : Finset (Ideal (𝓞 K))}

def scale (W : d.SupportData excluded) (c : ℂ) : (d.scale c).SupportData excluded where
  left_avoids := W.left_avoids
  right_avoids := W.right_avoids
  slot_avoids := W.slot_avoids
  left_mem r I hI havoid := by
    rw [d.scale_rectangleLeftWeight c r I] at hI
    exact W.left_mem r I (right_ne_zero_of_mul hI) havoid
  right_mem := W.right_mem
  slot_mem := W.slot_mem

def addGauss (W : d.SupportData excluded) (G₁ G₂ : ℝ) (G : Fin k → ℝ)
    (h₁ : 0 < G₁) (h₂ : 0 < G₂) (hG : ∀ i, 0 < G i) :
    (d.addGauss G₁ G₂ G h₁ h₂ hG).SupportData excluded where
  left_avoids := W.left_avoids
  right_avoids := W.right_avoids
  slot_avoids := W.slot_avoids
  left_mem r I hI havoid := by
    rw [d.addGauss_rectangleLeftWeight G₁ G₂ G h₁ h₂ hG r I] at hI
    exact W.left_mem r I (left_ne_zero_of_mul hI) havoid
  right_mem r I hI havoid := W.right_mem r I (left_ne_zero_of_mul hI) havoid
  slot_mem j p hp havoid := W.slot_mem j p (left_ne_zero_of_mul hp) havoid

def normPower (W : d.SupportData excluded) (δ : ℝ) :
    (d.normPower δ).SupportData excluded where
  left_avoids := W.left_avoids
  right_avoids := W.right_avoids
  slot_avoids := W.slot_avoids
  left_mem r I hI havoid := by
    rw [d.normPower_rectangleLeftWeight δ r I] at hI
    exact W.left_mem r I (left_ne_zero_of_mul hI) havoid
  right_mem r I hI havoid := W.right_mem r I (left_ne_zero_of_mul hI) havoid
  slot_mem j p hp havoid := W.slot_mem j p (left_ne_zero_of_mul hp) havoid

variable {S : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots S)

private theorem extract_left_avoids (W : d.SupportData excluded) :
    Avoids b.plainExtract₁ excluded := by
  sorry

private theorem extract_right_avoids (W : d.SupportData excluded) :
    Avoids b.plainExtract₂ excluded := by
  sorry

/-- The retained profile is unchanged. Only the actual extraction's
prime exclusion is added, with both directions of support proved. -/
def extract (W : d.SupportData excluded) (hS : ∀ p ∈ S, Prime p) :
    (d.extract b).SupportData (excluded ∪ S) where
  left_avoids I hI := by
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    apply (avoids_union _ excluded S).mpr
    refine ⟨?_, residual_avoids J S hS⟩
    intro p hp
    exact (W.left_avoids J (Finset.mem_filter.mp hJ).1 p hp).of_isCoprime_of_dvd_left
      (residual_dvd J (d.plain₁_nonzero J (Finset.mem_filter.mp hJ).1) S)
  right_avoids I hI := by
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    apply (avoids_union _ excluded S).mpr
    refine ⟨?_, residual_avoids J S hS⟩
    intro p hp
    exact (W.right_avoids J (Finset.mem_filter.mp hJ).1 p hp).of_isCoprime_of_dvd_left
      (residual_dvd J (d.plain₂_nonzero J (Finset.mem_filter.mp hJ).1) S)
  slot_avoids j p hp := by
    have hm := Finset.mem_filter.mp hp
    apply (avoids_union _ excluded S).mpr
    refine ⟨W.slot_avoids _ p hm.1, ?_⟩
    have ha := residual_avoids p.asIdeal S hS
    rwa [supportResidual_prime p.asIdeal p.prime S, if_neg hm.2] at ha
  left_mem r I hI havoid := by
    rw [d.extract_rectangleLeftWeight b r I] at hI
    have ha := (avoids_union I.val excluded S).mp havoid
    have hm := W.left_mem r (b.plainDivisor₁ * I) hI (fun p hp =>
      (extract_left_avoids b W p hp).mul_left (ha.1 p hp))
    have hs := (Finset.mem_filter.mp
      (Finset.mem_product.mp (Finset.mem_product.mp b.witness_mem).1).1).2
    apply plain_residual_mem d.plain₁ S hS b.plainExtract₁ I.val
      b.plainExtract₁_ne_zero (nonZeroDivisors.coe_ne_zero I) _ ha.2 hm
    rw [← hs, supportExtract_support]
    exact Finset.inter_subset_right
  right_mem r I hI havoid := by
    have ha := (avoids_union I.val excluded S).mp havoid
    have hm := W.right_mem r (b.plainDivisor₂ * I) hI (fun p hp =>
      (extract_right_avoids b W p hp).mul_left (ha.1 p hp))
    have hs := (Finset.mem_filter.mp
      (Finset.mem_product.mp (Finset.mem_product.mp b.witness_mem).1).2).2
    apply plain_residual_mem d.plain₂ S hS b.plainExtract₂ I.val
      b.plainExtract₂_ne_zero (nonZeroDivisors.coe_ne_zero I) _ ha.2 hm
    rw [← hs, supportExtract_support]
    exact Finset.inter_subset_right
  slot_mem j p hp havoid := by
    have ha := (avoids_union p.asIdeal excluded S).mp havoid
    apply Finset.mem_filter.mpr
    refine ⟨W.slot_mem _ p hp ha.1, ?_⟩
    intro hmem
    exact p.prime.not_unit ((ha.2 p.asIdeal hmem).isUnit_of_dvd (dvd_refl _))

def firstExtracted (W : d.SupportData excluded) (hS : ∀ p ∈ S, Prime p) :
    (d.firstExtracted b).SupportData (excluded ∪ S) :=
  (W.extract b hS).scale (d.commonScalar b)

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

def movingSingleton (W : d.SupportData excluded) (I : A.Exterior) (a : A.R)
    (ha : A.Generates I a) :
    (d.movingSingleton P R I a ha).SupportData excluded where
  left_avoids := W.left_avoids
  right_avoids := W.right_avoids
  slot_avoids := W.slot_avoids
  left_mem := W.left_mem
  right_mem := W.right_mem
  slot_mem := W.slot_mem

def secondInput (W : d.SupportData excluded) (hS : ∀ p ∈ S, Prime p)
    (power firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ) :
    (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).SupportData
        (excluded ∪ S) := by
  let e := d.firstExtracted b
  let w := W.firstExtracted b hS
  let v := (((w.addGauss (e.scale₁ false) (e.scale₂ false)
    (fun j => e.base ^ e.length j) (e.scale₁_pos false) (e.scale₂_pos false)
    (fun _ => Real.rpow_pos_of_pos (zero_lt_one.trans e.base_gt_one) _)).normPower (-1)).normPower δ₁).normPower δ₂
  exact (((v.movingSingleton P R firstFixed firstElement hfirst).movingSingleton P R poolFixed poolElement hpool).movingSingleton P R unitFixed unitElement hunit).scale
      (((A.exteriorNorm power ^ δ₁ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) power.val firstElement)

end SupportData
end CanonicalLiteralRectangles.Atoms

namespace CompleteMovingRowRecipe

open CanonicalLiteralSupport

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*}
variable {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)

/-- The original atom table supplies its support data from an original
paired row. No later ordinary row or normalized child is consulted. -/
def literalOriginalSupportData (ξ : X)
    (W : NormProfileRecipe (fun _ : PUnit => data ξ))
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
    (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
    (href : reference ∈ pairedRows (data ξ) a Z) :
    ((HeckeSkeleton.Moments.EngineStepV2.CompleteMovingRowRecipe.literalOriginalAtoms Q) ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).SupportData
      (primeSupport A.cS) where
  left_avoids I hI := by
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    exact (coprime_support_iff J.val A.cS A.cS_ne_zero).mp (Finset.mem_filter.mp hJ).2
  right_avoids I hI := by
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    exact (coprime_support_iff J.val A.cS A.cS_ne_zero).mp (Finset.mem_filter.mp hJ).2
  slot_avoids j p hp :=
    (coprime_support_iff p.asIdeal A.cS A.cS_ne_zero).mp (Finset.mem_filter.mp hp).2
  left_mem r I hI havoid :=
    (HeckeSkeleton.Moments.EngineStepV2.CompleteMovingRowRecipe.literalOriginalAtoms_left_weight_mem Q) ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      reference href r I ((coprime_support_iff I.val A.cS A.cS_ne_zero).mpr havoid)
      (CanonicalLiteralRectangles.Atoms.rectangleLeftWeight_ne_zero _ r I hI)
  right_mem r I hI havoid :=
    (HeckeSkeleton.Moments.EngineStepV2.CompleteMovingRowRecipe.literalOriginalAtoms_right_weight_mem Q) ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      reference href r I ((coprime_support_iff I.val A.cS A.cS_ne_zero).mpr havoid) hI
  slot_mem j p hp havoid :=
    (HeckeSkeleton.Moments.EngineStepV2.CompleteMovingRowRecipe.literalOriginalAtoms_slot_weight_mem Q) ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ j p
      ((coprime_support_iff p.asIdeal A.cS A.cS_ne_zero).mpr havoid) hp

end CompleteMovingRowRecipe

namespace CanonicalLiteralRectangles.Atoms.SupportData

open CanonicalLiteralSupport

variable {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable {excluded : Finset (Ideal (𝓞 K))}

/-- Every allocated divisor divides the actual original witness at
that occurrence, so it introduces no already excluded prime. -/
theorem leftDivisor_avoids (W : d.SupportData excluded) (B : ActualColumnAllocation K k)
    (hplain : B.plain₁ = d.plain₁) : Avoids (B.plainDivisor 0).val excluded := by
  sorry

theorem rightDivisor_avoids (W : d.SupportData excluded) (B : ActualColumnAllocation K k)
    (hplain : B.plain₂ = d.plain₂) :
    Avoids (B.plainDivisor (Fin.succ 0)).val excluded := by
  sorry

variable {ω ψ : HeckeCharacter K}

/-- The actual Fourier profile at the quotient scale has the full
allocated atom's support. Only its genuine mask supplies avoidance. -/
theorem fourierLeft_effectiveSupport (W : d.SupportData excluded) (profiles : d.ProfileData)
    (B : ActualColumnAllocation K k) (hplain : B.plain₁ = d.plain₁)
    (child : MomentData K ω ψ) (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (r : Bool) (firstSign : ℝ) (negative : Bool) (ξ : WithLp 2 (ℝ × ℝ)) (time : ℝ)
    (hmask : ∀ I : HeckeGeneral.Analysis.NonzeroIdeal K,
      maskValue child u I.val ≠ 0 → Avoids I.val excluded) :
    EffectivePlainSupport child (profiles.fourierLeft r firstSign negative ξ) u
      (d.scale₁ r / idealNorm K (B.plainDivisor 0)) time B.childPlain₁ := by
  sorry

theorem fourierRight_effectiveSupport (W : d.SupportData excluded) (profiles : d.ProfileData)
    (B : ActualColumnAllocation K k) (hplain : B.plain₂ = d.plain₂)
    (child : MomentData K ω ψ) (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (r : Bool) (firstSign : ℝ) (negative : Bool) (ξ : WithLp 2 (ℝ × ℝ)) (time : ℝ)
    (hmask : ∀ I : HeckeGeneral.Analysis.NonzeroIdeal K,
      maskValue child u I.val ≠ 0 → Avoids I.val excluded) :
    EffectivePlainSupport child (profiles.fourierRight r firstSign negative ξ) u
      (d.scale₂ r / idealNorm K (B.plainDivisor (Fin.succ 0))) time B.childPlain₂ := by
  sorry

/-- Only the original retained slot is used. Its complete arithmetic
mask removes the excluded primes without altering its smooth window. -/
theorem fourierSlot_effectiveSupport (W : d.SupportData excluded) (profiles : d.ProfileData)
    (B : ActualColumnAllocation K k) (hslots : B.slots = d.slots)
    (child : MomentData K ω ψ) (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (count : child.geometry.slotCount = B.keep.card)
    (firstSign : ℝ) (negative : Bool) (ξ : WithLp 2 (ℝ × ℝ)) (time : ℝ)
    (hslot : ∀ i, child.geometry.slots i =
      profiles.fourierSlot (SlotRestriction.index B.keep (Fin.cast count i))
        firstSign negative ξ)
    (hmask : ∀ I : HeckeGeneral.Analysis.NonzeroIdeal K,
      maskValue child u I.val ≠ 0 → Avoids I.val excluded)
    (i : Fin child.geometry.slotCount) :
    EffectivePrimeSupport child i u d.base time (B.childSlots (Fin.cast count i)) := by
  sorry

end CanonicalLiteralRectangles.Atoms.SupportData

end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# The original atom table on the existing covered source dictionary

An existing source atlas transports its proof of finite support without
changing its original occurrence dictionary.  Here the literal atom
table is transported through that already proved dictionary equality.
Its support fields are then the actual atlas fields by definition.

No column coefficient or polynomial identity is an input.  The same
two plain tests, every original prime test, the centered difference and
all normalization factors are retained.  The index and membership
lemmas permit the actual original coefficient calculation to be applied
directly to the stored covered leaf.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralAtlasAtoms

/-- Transport only the occurrence index. The two actual plain ideals
and every prime value are unchanged. -/
def castColumn {k l : ℕ} (h : k = l) (i : AllocationColumn K k) :
    AllocationColumn K l :=
  (i.1, fun j => i.2 (Fin.cast h.symm j))

@[simp] theorem castColumn_rfl {k : ℕ} (i : AllocationColumn K k) :
    castColumn rfl i = i := rfl

@[simp] theorem castColumn_symm {k l : ℕ} (h : k = l)
    (i : AllocationColumn K k) :
    castColumn h.symm (castColumn h i) = i := by
  sorry

@[simp] theorem castColumn_ideal {k l : ℕ} (h : k = l)
    (i : AllocationColumn K k) :
    allocationColumnIdeal (castColumn h i) = allocationColumnIdeal i := by
  sorry

abbrev Dictionary (ι : Type*) :=
  Σ n : ℕ, (Finset (Ideal (𝓞 K)) × Finset (Ideal (𝓞 K))) ×
    (Fin n → Finset (HeightOneSpectrum (𝓞 K))) ×
      (AllocationColumn K n → ι)

theorem dictionary_index {ι : Type*} {L M : Dictionary (K := K) ι}
    (h : L = M) (i : AllocationColumn K L.1) :
    L.2.2.2 i = M.2.2.2 (castColumn (congrArg Sigma.fst h) i) := by
  sorry

theorem dictionary_membership {ι : Type*} {L M : Dictionary (K := K) ι}
    (h : L = M) (i : AllocationColumn K L.1) :
    i ∈ childCartesianColumns L.2.1.1 L.2.1.2 L.2.2.1 ↔
      castColumn (congrArg Sigma.fst h) i ∈
        childCartesianColumns M.2.1.1 M.2.1.2 M.2.2.1 := by
  sorry

end CanonicalLiteralAtlasAtoms

namespace CanonicalLiteralRectangles.Atoms

open CanonicalLiteralAtlasAtoms

variable {k : ℕ} (d : Atoms (K := K) k)

private def onDictionary {ι : Type*} (D : Dictionary (K := K) ι)
    (h : k = D.1)
    (h₁ : ∀ I ∈ D.2.1.1, I ≠ 0) (h₂ : ∀ I ∈ D.2.1.2, I ≠ 0) :
    Atoms (K := K) D.1 :=
  { cast (congrArg (Atoms (K := K)) h) d with
    plain₁ := D.2.1.1
    plain₂ := D.2.1.2
    slots := D.2.2.1
    plain₁_nonzero := h₁
    plain₂_nonzero := h₂ }

private theorem onDictionary_eq_cast {ι : Type*}
    (D : Dictionary (K := K) ι) (index : AllocationColumn K k → ι)
    (e : D = ⟨k, (d.plain₁, d.plain₂), d.slots, index⟩)
    (h₁ : ∀ I ∈ D.2.1.1, I ≠ 0) (h₂ : ∀ I ∈ D.2.1.2, I ≠ 0) :
    d.onDictionary D (congrArg Sigma.fst e).symm h₁ h₂ =
      cast (congrArg (Atoms (K := K)) (congrArg Sigma.fst e).symm) d := by
  sorry

variable {A : SArithmeticData K} {ι : Type*}
variable {columns : Finset ι} {ideal : ι → A.Exterior}
variable (T : SourceCartesianAtlas columns ideal)

/-- The supports are the already constructed atlas supports, while
all coefficient and profile data come from the original literal table. -/
def onAtlas (h : k = T.slotCount) : Atoms (K := K) T.slotCount :=
  d.onDictionary (HeckeSkeleton.Moments.EngineStepV2.SourceCartesianAtlas.literalDictionary T) h T.plain₁_nonzero T.plain₂_nonzero

@[simp] theorem onAtlas_plain₁ (h : k = T.slotCount) :
    (d.onAtlas T h).plain₁ = T.reindex.plain₁ := rfl

@[simp] theorem onAtlas_plain₂ (h : k = T.slotCount) :
    (d.onAtlas T h).plain₂ = T.reindex.plain₂ := rfl

@[simp] theorem onAtlas_slots (h : k = T.slotCount) :
    (d.onAtlas T h).slots = T.reindex.slots := rfl

theorem onAtlas_term (h : k = T.slotCount) (r : Bool)
    (i : AllocationColumn K T.slotCount) :
    (d.onAtlas T h).term r i = d.term r (castColumn h.symm i) := by
  sorry

theorem onAtlas_whole (h : k = T.slotCount)
    (i : AllocationColumn K T.slotCount) :
    (d.onAtlas T h).whole i = d.whole (castColumn h.symm i) := by
  sorry

/-- The original occurrence equality, rather than a completed column
identity, proves that support retargeting leaves this atom table intact. -/
theorem onAtlas_eq_cast (index : AllocationColumn K k → ι)
    (e : (HeckeSkeleton.Moments.EngineStepV2.SourceCartesianAtlas.literalDictionary T) = ⟨k, (d.plain₁, d.plain₂), d.slots, index⟩) :
    d.onAtlas T (congrArg Sigma.fst e).symm =
      cast (congrArg (Atoms (K := K)) (congrArg Sigma.fst e).symm) d := by
  sorry

theorem onAtlas_index (index : AllocationColumn K k → ι)
    (e : (HeckeSkeleton.Moments.EngineStepV2.SourceCartesianAtlas.literalDictionary T) = ⟨k, (d.plain₁, d.plain₂), d.slots, index⟩)
    (i : AllocationColumn K T.slotCount) :
    T.reindex.index i = index (castColumn (congrArg Sigma.fst e) i) := by
  sorry

theorem onAtlas_membership (index : AllocationColumn K k → ι)
    (e : (HeckeSkeleton.Moments.EngineStepV2.SourceCartesianAtlas.literalDictionary T) = ⟨k, (d.plain₁, d.plain₂), d.slots, index⟩)
    (i : AllocationColumn K T.slotCount) :
    i ∈ T.reindex.cartesian ↔
      castColumn (congrArg Sigma.fst e) i ∈
        childCartesianColumns d.plain₁ d.plain₂ d.slots := by
  sorry

namespace ProfileData

variable {d} (W : d.ProfileData)

/-- The profiles do not depend on the finite support proofs. No new
test, scale, frequency direction or Fourier parameter is selected. -/
def onAtlas (h : k = T.slotCount) : (d.onAtlas T h).ProfileData := by
  cases h
  exact
    { left := W.left
      right := W.right
      slot := W.slot
      slot_length := W.slot_length
      left_positive := W.left_positive
      right_positive := W.right_positive
      slot_positive := W.slot_positive
      left_frozen := W.left_frozen
      right_frozen := W.right_frozen
      slot_frozen := W.slot_frozen
      left_eval := W.left_eval
      right_eval := W.right_eval
      slot_eval := W.slot_eval }

end ProfileData

namespace SupportData

variable {d} {excluded : Finset (Ideal (𝓞 K))} (W : d.SupportData excluded)

private def castTable {l : ℕ} (h : k = l) :
    (cast (congrArg (Atoms (K := K)) h) d).SupportData excluded := by
  cases h
  exact W

/-- The true individual support dictionary follows through the
original finite occurrence equality. -/
def onAtlas (index : AllocationColumn K k → ι)
    (e : (HeckeSkeleton.Moments.EngineStepV2.SourceCartesianAtlas.literalDictionary T) = ⟨k, (d.plain₁, d.plain₂), d.slots, index⟩) :
    (d.onAtlas T (congrArg Sigma.fst e).symm).SupportData excluded := by
  rw [d.onAtlas_eq_cast T index e]
  exact W.castTable (congrArg Sigma.fst e).symm

end SupportData
end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# The complete common-prime deletion in the literal source

An inactive first common prime need not appear in the first active
residue character. It is nevertheless absent from every actual
residual column. This file retains that deletion as its own actual
coprimality mask. The mask equals one at each real source occurrence,
so the whole centered coefficient and both original rectangles remain
unchanged. The smooth profiles, indices and normalization scales are
not modified.

The additional remaining ideal is the product of the original deleted
primes. Its support and norm therefore stay visible to the original
support budget; no phase cancellation is used to discard it.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open CanonicalOriginalPhaseCalibration

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

/-- The whole original finite deletion, including inactive primes. -/
def literalDeletionIdeal (S : Finset (Ideal (𝓞 K))) (hS : ∀ p ∈ S, Prime p) :
    HeckeGeneral.Analysis.NonzeroIdeal K :=
  ⟨∏ p ∈ S, p, mem_nonZeroDivisors_of_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun p hp => (hS p hp).ne_zero))⟩

theorem literalDeletionIdeal_coprime (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ p ∈ S, Prime p) (I : Ideal (𝓞 K)) :
    IsCoprime I (literalDeletionIdeal S hS).val ↔ CanonicalLiteralSupport.Avoids I S := by
  sorry

/-- The deletion is charged to the genuine original common ideal. -/
theorem literalDeletionIdeal_dvd (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ p ∈ S, Prime p) (D : Ideal (𝓞 K)) (hD : D ≠ 0)
    (hsub : S ⊆ primeSupport D) : (literalDeletionIdeal S hS).val ∣ D := by
  sorry

theorem literalDeletionIdeal_norm_le (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ p ∈ S, Prime p) (D : Ideal (𝓞 K)) (hD : D ≠ 0)
    (hsub : S ⊆ primeSupport D) :
    idealNorm K (literalDeletionIdeal S hS) ≤ (Ideal.absNorm D : ℝ) := by
  sorry

namespace FixedChildCharacters

variable (T : FixedChildCharacters K k)

def deleteMask (M : HeckeGeneral.Analysis.NonzeroIdeal K) : FixedChildCharacters K k :=
  { T with mask := T.mask * originalCoprimeMask M }

@[simp] theorem deleteMask_restrictSlots (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (keep : Finset (Fin k)) :
    ((HeckeSkeleton.Moments.EngineStepV2.FixedChildCharacters.deleteMask T) M).restrictSlots keep = (HeckeSkeleton.Moments.EngineStepV2.FixedChildCharacters.deleteMask (T.restrictSlots keep)) M := rfl

theorem deleteMask_plain (M I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    sourcePlainCoefficient ((HeckeSkeleton.Moments.EngineStepV2.FixedChildCharacters.deleteMask T) M).plain ((HeckeSkeleton.Moments.EngineStepV2.FixedChildCharacters.deleteMask T) M).plainTwist
        ((HeckeSkeleton.Moments.EngineStepV2.FixedChildCharacters.deleteMask T) M).mask I =
      sourcePlainCoefficient T.plain T.plainTwist T.mask I * originalCoprimeMask M I.val := by
  sorry

theorem deleteMask_prime (M : HeckeGeneral.Analysis.NonzeroIdeal K) (i : Fin k)
    (p : HeightOneSpectrum (𝓞 K)) :
    sourcePrimeCoefficient (((HeckeSkeleton.Moments.EngineStepV2.FixedChildCharacters.deleteMask T) M).slot i) (((HeckeSkeleton.Moments.EngineStepV2.FixedChildCharacters.deleteMask T) M).slotTwist i)
        ((HeckeSkeleton.Moments.EngineStepV2.FixedChildCharacters.deleteMask T) M).mask p =
      sourcePrimeCoefficient (T.slot i) (T.slotTwist i) T.mask p *
        originalCoprimeMask M p.asIdeal := by
  sorry

/-- The new factor is the actual multiplicative mask of the complete
ideal. This is proved before any whole polynomial is formed. -/
theorem rawBare_deleteMask (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (i : AllocationColumn K k) (h₁ : i.1.1 ≠ 0) (h₂ : i.1.2 ≠ 0) :
    rawBareSourceCoefficient ((HeckeSkeleton.Moments.EngineStepV2.FixedChildCharacters.deleteMask T) M) N₁ N₂ Z length w₁ w₂ w i =
      rawBareSourceCoefficient T N₁ N₂ Z length w₁ w₂ w i *
        originalCoprimeMask M (allocationColumnIdeal i) := by
  sorry

end FixedChildCharacters

namespace CanonicalLiteralRectangles.Atoms

variable (d : CanonicalLiteralRectangles.Atoms (K := K) k)

/-- Only the actual source mask changes; every original test and every
real column carrier is retained literally. -/
def deleteMask (M : HeckeGeneral.Analysis.NonzeroIdeal K) :
    CanonicalLiteralRectangles.Atoms (K := K) k :=
  { d with characters := (HeckeSkeleton.Moments.EngineStepV2.FixedChildCharacters.deleteMask d.characters) M }

theorem deleteMask_term (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (r : Bool) (i : AllocationColumn K k)
    (hi : i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots) :
    (d.deleteMask M).term r i =
      d.term r i * originalCoprimeMask M (allocationColumnIdeal i) := by
  sorry

theorem deleteMask_whole (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (i : AllocationColumn K k)
    (hi : i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots) :
    (d.deleteMask M).whole i =
      d.whole i * originalCoprimeMask M (allocationColumnIdeal i) := by
  sorry

namespace SupportData

variable {d} {excluded : Finset (Ideal (𝓞 K))}

def deleteMask (W : d.SupportData excluded) (M : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (d.deleteMask M).SupportData excluded where
  left_avoids := W.left_avoids
  right_avoids := W.right_avoids
  slot_avoids := W.slot_avoids
  left_mem := W.left_mem
  right_mem := W.right_mem
  slot_mem := W.slot_mem

/-- The original occurrence support proves that the complete new mask
is one. No assumption on the complete coefficient is used. -/
theorem deleteMask_whole_eq (W : d.SupportData excluded)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K) (hM : primeSupport M.val ⊆ excluded)
    (i : AllocationColumn K k)
    (hi : i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots) :
    (d.deleteMask M).whole i = d.whole i := by
  sorry

end SupportData

namespace ProfileData

variable {d} (W : d.ProfileData)

def deleteMask (M : HeckeGeneral.Analysis.NonzeroIdeal K) : (d.deleteMask M).ProfileData where
  left := W.left
  right := W.right
  slot := W.slot
  slot_length := W.slot_length
  left_positive := W.left_positive
  right_positive := W.right_positive
  slot_positive := W.slot_positive
  left_frozen := W.left_frozen
  right_frozen := W.right_frozen
  slot_frozen := W.slot_frozen
  left_eval := W.left_eval
  right_eval := W.right_eval
  slot_eval := W.slot_eval

end ProfileData
end CanonicalLiteralRectangles.Atoms

end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# Reciprocal balancing of the two actual plain profiles

The two positive scale factors in a centered rectangle can be very
different, although their product is fixed by the original two plain
scales. Reciprocal multiplication of the two individual profiles keeps
each literal rectangle coefficient unchanged. No carrier, normalizer,
slot, character, location or Fourier variable is modified.

The balancing is performed before the actual normalized children are
chosen. Its factorization belongs to the original whole coefficient,
so the same stored leaf and its ordinary binding can be retained.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralRectangles.Atoms

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)

/-- The reciprocal factors act only on the two displayed plain
weights. Their actual norm scales and all prime occurrences stay fixed. -/
def balancePlain (c : Bool → ℝ) : CanonicalLiteralRectangles.Atoms (K := K) k :=
  { d with
    leftWeight := fun r I => d.leftWeight r I * (c r : ℂ)
    rightWeight := fun r I => d.rightWeight r I * (c r : ℂ)⁻¹ }

@[simp] theorem balancePlain_characters (c : Bool → ℝ) :
    (d.balancePlain c).characters = d.characters := rfl

@[simp] theorem balancePlain_normalizer (c : Bool → ℝ) :
    (d.balancePlain c).normalizer = d.normalizer := rfl

theorem balancePlain_rectangleLeftWeight (c : Bool → ℝ) (r : Bool)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (d.balancePlain c).rectangleLeftWeight r I =
      d.rectangleLeftWeight r I * (c r : ℂ) := by
  sorry

/-- The equality is proved for each original column, including every
ramified zero and the absent comparison rectangle. -/
theorem balancePlain_term (c : Bool → ℝ) (hc : ∀ r, 0 < c r)
    (r : Bool) (i : AllocationColumn K k) :
    (d.balancePlain c).term r i = d.term r i := by
  sorry

theorem balancePlain_whole (c : Bool → ℝ) (hc : ∀ r, 0 < c r)
    (i : AllocationColumn K k) :
    (d.balancePlain c).whole i = d.whole i := by
  sorry

/-- Actual support extraction and reciprocal balancing commute. The
original removed slots and the same witness are retained. -/
theorem balancePlain_extract (c : Bool → ℝ)
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support) :
    (d.balancePlain c).extract b = (d.extract b).balancePlain c := rfl

namespace ProfileData

variable {d} (W : d.ProfileData)

/-- These are the actual scaled individual tests, not assumed new
profile representatives. Their finite supports are constructed by the
existing multiplication operation. -/
def balancePlain (c : Bool → ℝ) : (d.balancePlain c).ProfileData where
  left r := CanonicalLiteralProfileData.mulIdealTest (W.left r) (fun _ => (c r : ℂ))
  right r := CanonicalLiteralProfileData.mulIdealTest (W.right r) (fun _ => (c r : ℂ)⁻¹)
  slot := W.slot
  slot_length := W.slot_length
  left_positive r := CanonicalLiteralProfileData.mulIdealTest_positive _ _ (W.left_positive r)
  right_positive r := CanonicalLiteralProfileData.mulIdealTest_positive _ _ (W.right_positive r)
  slot_positive := W.slot_positive
  left_frozen r u t y := congrArg (fun z => z * (c r : ℂ)) (W.left_frozen r u t y)
  right_frozen r u t y := congrArg (fun z => z * (c r : ℂ)⁻¹) (W.right_frozen r u t y)
  slot_frozen := W.slot_frozen
  left_eval r u t I := by
    change (W.left r).profile u t (idealNorm K I / d.scale₁ r) * (c r : ℂ) = _
    rw [W.left_eval, d.balancePlain_rectangleLeftWeight]
  right_eval r u t I := by
    change (W.right r).profile u t (idealNorm K I / d.scale₂ r) * (c r : ℂ)⁻¹ = _
    rw [W.right_eval] <;> rfl
  slot_eval := W.slot_eval

end ProfileData

namespace SupportData

variable {d} {excluded : Finset (Ideal (𝓞 K))}

def balancePlain (W : d.SupportData excluded) (c : Bool → ℝ) :
    (d.balancePlain c).SupportData excluded where
  left_avoids := W.left_avoids
  right_avoids := W.right_avoids
  slot_avoids := W.slot_avoids
  left_mem r I hI havoid := by
    rw [d.balancePlain_rectangleLeftWeight c r I] at hI
    exact W.left_mem r I (left_ne_zero_of_mul hI) havoid
  right_mem r I hI havoid := W.right_mem r I (left_ne_zero_of_mul hI) havoid
  slot_mem := W.slot_mem

end SupportData
end CanonicalLiteralRectangles.Atoms

namespace CanonicalLiteralPlainBalance

/-- A positive balancing factor determined by the actual two scalar
profiles. No upper bound or replacement scale is selected here. -/
def ratio (left right : ℝ) : ℝ := Real.sqrt (right / left)

theorem ratio_pos {left right : ℝ} (hl : 0 < left) (hr : 0 < right) :
    0 < ratio left right := by
  sorry

theorem left_mul_ratio {left right : ℝ} (hl : 0 < left) (hr : 0 < right) :
    left * ratio left right = Real.sqrt (left * right) := by
  sorry

theorem right_mul_ratio_inv {left right : ℝ} (hl : 0 < left) (hr : 0 < right) :
    right * (ratio left right)⁻¹ = Real.sqrt (left * right) := by
  sorry

end CanonicalLiteralPlainBalance

namespace CanonicalLiteralRectangles

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable {k l : ℕ}

/-- The balanced frames are a factorization of the same original
whole source. Both ordinary rectangles still have their original
allocation, locations, arithmetic rows and complete coefficients. -/
def balancedRectangles (R : ActualSecondCorrelationRows A σ H ι)
    (left : Atoms (K := K) k) (right : Atoms (K := K) l)
    (leftBalance rightBalance : Bool → ℝ)
    (hleftBalance : ∀ r, 0 < leftBalance r) (hrightBalance : ∀ r, 0 < rightBalance r)
    (IL : AllocationColumn K k → A.Exterior) (IR : AllocationColumn K l → A.Exterior)
    (hIL : ∀ i ∈ childCartesianColumns left.plain₁ left.plain₂ left.slots,
      (IL i).val = allocationColumnIdeal i)
    (hIR : ∀ j ∈ childCartesianColumns right.plain₁ right.plain₂ right.slots,
      (IR j).val = allocationColumnIdeal j)
    (b : liveSecondAllocationBranches (Ray := PUnit.{1})
      left.plain₁ left.plain₂ left.slots right.plain₁ right.plain₂ right.slots IR)
    (exceptional : H → Prop) (firstLeftSign firstRightSign : ℝ) :
    HybridOrdinaryRectangles R PUnit.{1}
      left.plain₁ left.plain₂ left.slots right.plain₁ right.plain₂ right.slots IL IR
      (fun _ => PUnit.unit) (fun _ => PUnit.unit) left.whole right.whole
      (fun _ => rawSourceLocation (CanonicalLiteralLocations.plain firstLeftSign)
        (CanonicalLiteralLocations.plain firstLeftSign)
        (CanonicalLiteralLocations.prime firstLeftSign))
      (fun _ => rawSourceLocation (CanonicalLiteralLocations.plain firstRightSign)
        (CanonicalLiteralLocations.plain firstRightSign)
        (CanonicalLiteralLocations.prime firstRightSign)) b exceptional where
  leftTerms := (left.balancePlain leftBalance).term
  rightTerms := (right.balancePlain rightBalance).term
  left_difference i _ := by
    rw [left.balancePlain_term leftBalance hleftBalance false i,
      left.balancePlain_term leftBalance hleftBalance true i]
    rfl
  right_difference i _ := by
    rw [right.balancePlain_term rightBalance hrightBalance false i,
      right.balancePlain_term rightBalance hrightBalance true i]
    rfl
  leftFactors r := (left.balancePlain leftBalance).factors
    (R.restrictRows fun h => ¬exceptional h) .left b.val.2.1 IL hIL firstLeftSign r
  rightFactors r := (right.balancePlain rightBalance).factors
    (R.restrictRows fun h => ¬exceptional h) .right b.val.2.1 IR hIR firstRightSign r

end CanonicalLiteralRectangles

namespace ActualHybridLeaf.OrdinaryBinding

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {H ι U V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup U] [InnerProductSpace ℝ U]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {leaf : ActualHybridLeaf K H U V}
variable {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin leaf.leftSlots → Finset (HeightOneSpectrum (𝓞 K))}
variable {T₁ T₂ : Finset (Ideal (𝓞 K))}
variable {T : Fin leaf.rightSlots → Finset (HeightOneSpectrum (𝓞 K))}
variable {IA : AllocationColumn K leaf.leftSlots → A.Exterior}
variable {IB : AllocationColumn K leaf.rightSlots → A.Exterior}
variable {rayLeft : AllocationColumn K leaf.leftSlots → Ray}
variable {rayRight : AllocationColumn K leaf.rightSlots → Ray}
variable {wholeLeft : AllocationColumn K leaf.leftSlots → ℂ}
variable {wholeRight : AllocationColumn K leaf.rightSlots → ℂ}
variable {x : H → AllocationColumn K leaf.leftSlots → WithLp 2 (U × V)}
variable {y : H → AllocationColumn K leaf.rightSlots → WithLp 2 (U × V)}
variable {b : liveSecondAllocationBranches (Ray := Ray) S₁ S₂ S T₁ T₂ T IB}
variable {exceptional : H → Prop}
variable {B : HybridOrdinaryRectangles R Ray S₁ S₂ S T₁ T₂ T IA IB
  rayLeft rayRight wholeLeft wholeRight x y b exceptional}

/-- A different proved factorization of the same two whole coefficients
retains every original binding field. In particular balancing does not
change the stored leaf or either Fourier kernel. -/
def refactor (binding : leaf.OrdinaryBinding B)
    (B' : HybridOrdinaryRectangles R Ray S₁ S₂ S T₁ T₂ T IA IB
      rayLeft rayRight wholeLeft wholeRight x y b exceptional) :
    leaf.OrdinaryBinding B' where
  rows := binding.rows
  rows_zero := binding.rows_zero
  left := binding.left
  right := binding.right
  exceptional := binding.exceptional
  rowWeight := binding.rowWeight
  leftCoefficient := binding.leftCoefficient
  rightCoefficient := binding.rightCoefficient
  leftPoint := binding.leftPoint
  rightPoint := binding.rightPoint

end ActualHybridLeaf.OrdinaryBinding

end HeckeSkeleton.Moments.EngineStepV2

end

