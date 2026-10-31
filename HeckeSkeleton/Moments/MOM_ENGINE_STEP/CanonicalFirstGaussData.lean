import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstLogBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectFirstBlock
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstBlocks
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualLeafNormWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalPoolMonotonicity

/-!
# Actual first Gauss data from the original orbital rows

The two row sets are the images of the same original finite orbital
source, with the required negative frequency on the right. Residual
generators are the allowed generators already chosen by the canonical
common block. The CRT support is computed from the original finite
columns, rows and one earlier prime pool.

The logarithmic chart supplies its explicit row multiplier bound. No
first-block data record, finite support cover, or whole-column estimate
is an input to the direct construction. The pooled construction adds
only original individual norm windows and the earlier pool density;
the internal divisor windows follow from the same original columns.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support HeckePort.Moments.MobiusRegroup
open MeasureTheory UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}

/-- A total row-ideal dictionary. Its zero value is never used on the
actual nonzero physical rows. -/
def originalFrequencyIdeal (h : A.R) : A.Exterior :=
  if hh : h ≠ 0 then ProbeOrbitNormSum.principalExterior A ⟨h, hh⟩
  else unitExterior A

theorem originalFrequencyIdeal_generates (h : A.R) (hh : h ≠ 0) :
    A.Generates (originalFrequencyIdeal h) h := by
  rw [originalFrequencyIdeal, dif_pos hh]
  exact ProbeOrbitNormSum.principalExterior_generates A ⟨h, hh⟩

theorem originalFrequencyIdeal_norm (h : A.R) (hh : h ≠ 0) :
    A.exteriorNorm (originalFrequencyIdeal h) =
      (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ⟨h, hh⟩).val := by
  change (Ideal.absNorm (originalFrequencyIdeal h).val : ℝ) = _
  rw [← natCard_sIntegerPrincipalResidue_eq_productNorm K
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) h hh,
    (originalFrequencyIdeal_generates h hh).2, A.exteriorResidue_card]

/-- Every actual prime factor, with its original exterior-prime type. -/
def originalExteriorPrimeSupport (I : A.Exterior) : Finset (ExteriorPrime A) :=
  (primeSupport I.val).attach.image (exteriorPrimeOfSupport I)

theorem mem_originalExteriorPrimeSupport (I : A.Exterior) (p : ExteriorPrime A)
    (hp : MaskedQuotientCRT.primeExponent p I ≠ 0) :
    p ∈ originalExteriorPrimeSupport I := by
  have hd : p.val.asIdeal ∣ I.val := by
    by_contra hn
    exact hp (primeExponent_zero_of_not_dvd I p hn)
  have hs : p.val.asIdeal ∈ primeSupport I.val :=
    (prime_mem_support_iff_dvd _ _ p.val.prime I.property.1).mpr hd
  apply Finset.mem_image.mpr
  refine ⟨⟨p.val.asIdeal, hs⟩, Finset.mem_attach _ _, ?_⟩
  apply Subtype.ext
  apply HeightOneSpectrum.asIdeal_injective
  rfl

namespace DirectGaussData

variable {ι : Type*}

/-- An earlier direct row/column dictionary determines every finite
support needed by the one fixed pool. -/
def completePoolSupport (d : DirectGaussData C ι)
    (primes : Finset (ExteriorPrime A)) : Finset (ExteriorPrime A) :=
  (d.columns.biUnion (fun i => originalExteriorPrimeSupport (d.ideal i))) ∪
    (d.rows.biUnion (fun h => originalExteriorPrimeSupport (originalFrequencyIdeal h))) ∪ primes

/-- Only the original frequency and frozen-ideal norm windows are
additional data. The CRT support and row ideals are constructed here. -/
def withOriginalPool (d : DirectGaussData C ι)
    {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
    (P : PowerScaleExteriorPool A bad Z ell eps)
    (frozen : Ideal (𝓞 K)) (hfrozen : frozen ≠ 0)
    (rowExponent frozenExponent : ℝ) (hrow : 0 ≤ rowExponent)
    (hrows : ∀ h ∈ d.rows, A.exteriorNorm (originalFrequencyIdeal h) ≤ Z ^ rowExponent)
    (hfrozenNorm : (Ideal.absNorm frozen : ℝ) ≤ Z ^ frozenExponent)
    (hdensity : 0 < P.rowDensity rowExponent frozenExponent) :
    FirstGaussPoolData C P ι where
  columns := d.columns
  ideal := d.ideal
  generator := d.generator
  generates := d.generates
  allowed := d.allowed
  rows := d.rows
  rowIdeal := originalFrequencyIdeal
  row_generates h hh := originalFrequencyIdeal_generates h (d.row_nonzero h hh)
  support := d.completePoolSupport P.primes
  column_support i hi p hp :=
    Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨i, hi, mem_originalExteriorPrimeSupport _ p hp⟩))
  row_support h hh p hp :=
    Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨h, hh, mem_originalExteriorPrimeSupport _ p hp⟩))
  pool_support := Finset.subset_union_right
  frozen := frozen
  frozen_ne_zero := hfrozen
  rowExponent := rowExponent
  frozenExponent := frozenExponent
  rowExponent_nonneg := hrow
  row_norm := hrows
  frozen_norm := hfrozenNorm
  density_pos := hdensity

end DirectGaussData

section CanonicalRows

variable {Γ : Subgroup A.U}
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

variable (C : A.GeneralArithmeticContext σ η hS)
variable {ι κ : Type*} (left : Finset ι) (right : Finset κ)
variable (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
variable (DE : Ideal (𝓞 K) × Ideal (𝓞 K))
variable (hDE : DE ∈ commonSupportPool left right
  (fun i => (fullI i).val) (fun j => (fullJ j).val))

/-- The positive original frequencies and the actual allowed residual
generators. All original orbital rows remain present. -/
def canonicalFirstLeftGaussData (rows : Finset Q) : DirectGaussData C ι := by
  let b := canonicalFirstCommonBlock C left right fullI fullJ DE hDE
  refine
    { rows := rows.image (fun q : Q => q.out.val)
      row_nonzero := ?_
      columns := b.leftColumns left
      ideal := b.leftResidual
      generator := b.leftGenerator
      generates := b.left_generates
      allowed := ?_ }
  · intro h hh
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hh
    exact q.out.property
  · intro i _
    obtain ⟨u, hu, ha⟩ :=
      (canonicalFirstCommonBlock_allowed C left right fullI fullJ DE hDE).1 i
    have he : u = Units.mk0 (b.leftGenerator i : K)
        (by exact_mod_cast (b.left_generates i).1) := Units.ext hu
    simpa only [← he] using ha

/-- The right frequencies are the literal negatives of those same
orbital rows. No second representative or independent row set is chosen. -/
def canonicalFirstRightGaussData (rows : Finset Q) : DirectGaussData C κ := by
  let b := canonicalFirstCommonBlock C left right fullI fullJ DE hDE
  refine
    { rows := rows.image (fun q : Q => -q.out.val)
      row_nonzero := ?_
      columns := b.rightColumns right
      ideal := b.rightResidual
      generator := b.rightGenerator
      generates := b.right_generates
      allowed := ?_ }
  · intro h hh
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hh
    exact neg_ne_zero.mpr q.out.property
  · intro i _
    obtain ⟨u, hu, ha⟩ :=
      (canonicalFirstCommonBlock_allowed C left right fullI fullJ DE hDE).2 i
    have he : u = Units.mk0 (b.rightGenerator i : K)
        (by exact_mod_cast (b.right_generates i).1) := Units.ext hu
    simpa only [← he] using ha

end CanonicalRows

section CanonicalChart

variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- The original logarithmic profile yields the complete first direct
block. Its row weight bound is computed from the actual active ideal,
radius and mask dilation, before either Fourier parameter. -/
def canonicalFirstDirectLogBlock
    (C : A.GeneralArithmeticContext σ η hS)
    {ι κ : Type*} (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (DE : Ideal (𝓞 K) × Ideal (𝓞 K))
    (hDE : DE ∈ commonSupportPool left right
      (fun i => (fullI i).val) (fun j => (fullJ j).val))
    (φ : 𝓢(V, ℂ)) (c : ι → ℂ) (e : κ → ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (radius : {r : ℝ // 0 < r}) (D M : Finset (HeightOneSpectrum A.R))
    (X : ℝ) (hX : 1 ≤ X) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    FirstBlockDirectData
      (FirstBlockProfileChart.canonicalLogWithCoefficients hΓ μv ν
        (canonicalFirstCommonBlock C left right fullI fullJ DE hDE)
        C left right φ c e finiteTest hlc hcs radius D δ hδ hδ1) M X hX := by
  let b := canonicalFirstCommonBlock C left right fullI fullJ DE hDE
  let profiles := fun i j => (c i * star (e j)) • φ
  let rows := (b.finiteSource hΓ C left right profiles M radius X hX).rows
  let active := actualActiveColumn hΓ C b.primes b.primes_injective
    b.leftMultiplicity b.rightMultiplicity
  exact
    { leftData := canonicalFirstLeftGaussData C left right fullI fullJ DE hDE rows
      rightData := canonicalFirstRightGaussData C left right fullI fullJ DE hDE rows
      left_columns := rfl
      right_columns := rfl
      left_ideal := rfl
      right_ideal := rfl
      left_generator := rfl
      right_generator := rfl
      left_rows := Finset.Subset.refl _
      right_rows := Finset.Subset.refl _
      weightBound := CanonicalFirstLog.rowWeightBound active radius D δ
      weight_nonneg := CanonicalFirstLog.rowWeightBound_nonneg active radius D δ
      weight_bound := fun q _ =>
        FirstBlockProfileChart.canonicalLogWithCoefficients_weight_le hΓ μv ν b C
          left right φ finiteTest hlc hcs radius D δ hδ hδ1 c e q }

end CanonicalChart

section PooledBlock

variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
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
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → 𝓢(mixedEmbedding.euclidean.mixedSpace K, ℂ)}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}} {D M : Finset (HeightOneSpectrum A.R)}
variable {X : ℝ} {hX : 1 ≤ X}
variable {chart : FirstBlockProfileChart (E := E) hΓ μv b C left right
  profiles finiteTest radius D}

namespace FirstBlockDirectData

/-- Attach one earlier pool to the actual direct block. Every internal
divisor norm is inferred from the original full right-column window.
The original rows, coefficients, chart and row multiplier remain fixed. -/
def withOriginalPool (p : FirstBlockDirectData chart M X hX)
    {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
    (P : PowerScaleExteriorPool A bad Z ell eps)
    (frozenLeft frozenRight : Ideal (𝓞 K))
    (hfrozenLeft : frozenLeft ≠ 0) (hfrozenRight : frozenRight ≠ 0)
    (rowLeft rowRight boundLeft boundRight divisorBound : ℝ)
    (hrowLeft : 0 ≤ rowLeft) (hrowRight : 0 ≤ rowRight)
    (hdivisor : 0 ≤ divisorBound)
    (hrowsLeft : ∀ h ∈ p.leftData.rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤ Z ^ rowLeft)
    (hrowsRight : ∀ h ∈ p.rightData.rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤ Z ^ rowRight)
    (hfrozenNormLeft : (Ideal.absNorm frozenLeft : ℝ) ≤ Z ^ boundLeft)
    (hfrozenNormRight : (Ideal.absNorm frozenRight : ℝ) ≤ Z ^ boundRight)
    (hcolumns : ∀ j ∈ right, (Ideal.absNorm (fullJ j).val : ℝ) ≤ Z ^ divisorBound)
    (hdensityLeft : 0 < P.rowDensity rowLeft (boundLeft + divisorBound))
    (hdensityRight : 0 < P.rowDensity rowRight (boundRight + divisorBound)) :
    FirstBlockPoolData chart P M X hX := by
  have hleft : 0 < P.rowDensity rowLeft boundLeft :=
    P.rowDensity_pos_of_uniform le_rfl (le_add_of_nonneg_right hdivisor) hdensityLeft
  have hright : 0 < P.rowDensity rowRight boundRight :=
    P.rowDensity_pos_of_uniform le_rfl (le_add_of_nonneg_right hdivisor) hdensityRight
  let L := p.leftData.withOriginalPool P frozenLeft hfrozenLeft
    rowLeft boundLeft hrowLeft hrowsLeft hfrozenNormLeft hleft
  let R := p.rightData.withOriginalPool P frozenRight hfrozenRight
    rowRight boundRight hrowRight hrowsRight hfrozenNormRight hright
  have hresidual (j : κ) (hj : j ∈ p.rightData.columns) :
      (Ideal.absNorm (p.rightData.ideal j).val : ℝ) ≤ Z ^ divisorBound := by
    rw [p.right_columns] at hj
    rw [p.right_ideal, b.right_residual]
    exact (actual_supportResidual_norm_le _ (fullJ j).property.1 _).trans
      (hcolumns j (Finset.mem_filter.mp hj).1)
  have hdiv : ∀ S ∈ divisorPool R.columns (fun j => (R.ideal j).val),
      (Ideal.absNorm S : ℝ) ≤ Z ^ divisorBound := by
    intro S hS
    exact actual_divisorPool_norm_le _ _ (Z ^ divisorBound)
      (fun j _ => (p.rightData.ideal j).property.1) hresidual ⟨S, hS⟩
  exact
    { leftData := L
      rightData := R
      divisorPools := FirstDivisorPoolData.ofNormWindows L R divisorBound hdiv
        hdensityLeft hdensityRight
      left_columns := p.left_columns
      right_columns := p.right_columns
      left_ideal := p.left_ideal
      right_ideal := p.right_ideal
      left_generator := p.left_generator
      right_generator := p.right_generator
      left_rows := p.left_rows
      right_rows := p.right_rows
      weightBound := p.weightBound
      weight_nonneg := p.weight_nonneg
      weight_bound := p.weight_bound }

end FirstBlockDirectData
end PooledBlock

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.originalFrequencyIdeal_generates
#print axioms HeckeSkeleton.Moments.EngineStep.mem_originalExteriorPrimeSupport
#print axioms HeckeSkeleton.Moments.EngineStep.DirectGaussData.withOriginalPool
#print axioms HeckeSkeleton.Moments.EngineStep.canonicalFirstDirectLogBlock
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.withOriginalPool
