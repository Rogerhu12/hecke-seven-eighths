import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalRowBallChart
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolSecondStage

/-!
# The empty row mask in the positive second Gauss majorant

Only the additional orbital row mask is empty here. The original Gauss
source, all full columns and coefficients, and the common masks carried
by those columns are unchanged. A positive whole-square source can use
this mask before Poisson summation, since its value is one on every
original orbit.

The generator selected for the empty divisor is a genuine unit, but is
not identified with the element one. Its product norm is proved to be
one, while its actual divisor character phases remain in the existing
second-transform definitions. No unit sector is discarded.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters HeckeGeneral.Bridge
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open UniqueFactorizationMonoid

/-- There is exactly one original divisor label of an empty row mask. -/
theorem emptyMask_divisor_eq {α : Type*} (D : (∅ : Finset α).powerset) :
    D.val = ∅ :=
  Finset.subset_empty.mp (Finset.mem_powerset.mp D.property)

theorem emptyMask_divisor_unique {α : Type*}
    (D E : (∅ : Finset α).powerset) : D = E :=
  Subtype.ext ((emptyMask_divisor_eq D).trans (emptyMask_divisor_eq E).symm)

section Arithmetic

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The avoidance function itself is one on every original subgroup
orbit. There is no assumption about the row's prime divisibility. -/
@[simp] theorem sIntegerOrbitAvoidanceMask_empty
    (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
    (q : SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    sIntegerOrbitAvoidanceMask K (S : Set (HeightOneSpectrum (𝓞 K))) Γ ∅ q = 1 := by
  simp [sIntegerOrbitAvoidanceMask]

variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

/-- The actual chosen generator of the empty mask is a unit. This does
not identify its element, or any of its finite character values, with one. -/
theorem sIntegerMaskGenerator_empty_isUnit :
    IsUnit (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) ∅).val := by
  apply isUnit_of_dvd_one
  change IdealMobiusMask.maskGenerator
    (∅ : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K))) ∣ 1
  apply (IdealMobiusMask.maskGenerator_dvd_iff _ _).mpr
  simp only [IdealMobiusMask.primeProduct, Finset.prod_empty,
    Ideal.one_eq_top, Submodule.mem_top]

/-- Norm one follows from the actual principal residue ring, which has
one element for a unit modulus. No representative normalization is used. -/
@[simp] theorem sIntegerMaskGenerator_empty_norm :
    (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) ∅)).val = 1 := by
  let d := sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) ∅
  have hu : IsUnit d.val := sIntegerMaskGenerator_empty_isUnit K S
  change (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) d).val = 1
  rw [← natCard_sIntegerPrincipalResidue_eq_productNorm K
    (S : Set (HeightOneSpectrum (𝓞 K))) d.val d.property,
    Ideal.span_singleton_eq_top.mpr hu]
  simp only [Nat.card_unique, Nat.cast_one]

/-- Every original column is coprime to the actual empty-divisor unit,
without deleting or changing any column. -/
theorem emptyMask_column_coprime
    (a : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) :
    IsCoprime a (sIntegerMaskGenerator K
      (S : Set (HeightOneSpectrum (𝓞 K))) ∅).val := by
  obtain ⟨u, hu⟩ := sIntegerMaskGenerator_empty_isUnit K S
  refine ⟨0, (u⁻¹).val, ?_⟩
  rw [← hu]
  simp only [zero_mul, zero_add, Units.inv_mul]

@[simp] theorem emptyMask_divisor_norm
    (D : (∅ : Finset (HeightOneSpectrum
      (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K))).powerset) :
    (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D.val)).val = 1 := by
  rw [emptyMask_divisor_eq D, sIntegerMaskGenerator_empty_norm K S]

theorem emptyMask_divisor_column_coprime
    (D : (∅ : Finset (HeightOneSpectrum
      (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K))).powerset)
    (a : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) :
    IsCoprime a (sIntegerMaskGenerator K
      (S : Set (HeightOneSpectrum (𝓞 K))) D.val).val := by
  rw [emptyMask_divisor_eq D]
  exact emptyMask_column_coprime K S a

/-- This is precisely the empty-mask input to an original physical
cutoff window; its exponent is zero for every value of the base. -/
theorem emptyMask_norm_window (Z : ℝ) :
    ∀ D ∈ (∅ : Finset (HeightOneSpectrum
      (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K))).powerset,
      (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val ≤
          Z ^ (0 : ℝ) := by
  intro D hD
  have hnorm := emptyMask_divisor_norm K S ⟨D, hD⟩
  simpa only [Real.rpow_zero, hnorm] using (le_refl (1 : ℝ))

@[simp] theorem sIntegerMaskDilationRadius_empty (r : {r : ℝ // 0 < r}) :
    sIntegerMaskDilationRadius K S r
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) ∅) = r := by
  apply Subtype.ext
  change r.val * (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
    (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) ∅)).val = r.val
  rw [sIntegerMaskGenerator_empty_norm K S, mul_one]

/-- The actual Poisson scalar still contains its inverse radius and
field factor. Only the proved empty-divisor norm and Moebius value simplify. -/
@[simp] theorem secondOrbitalScalar_empty (r : {r : ℝ // 0 < r}) :
    secondOrbitalScalar (K := K) (S := S) r ∅ =
      (r.val : ℂ)⁻¹ * (orbitalFieldFactor K : ℂ) := by
  simp only [secondOrbitalScalar, IdealMobiusMask.primeProduct, Finset.prod_empty,
    moebius_one, Int.cast_one, sIntegerMaskGenerator_empty_norm K S, mul_one, one_mul]

end Arithmetic

section Chart

variable {K : Type} [Field K] [NumberField K]
variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]

namespace GaussEnergyChart

variable {H : Type*} {rows : Finset H}
variable {rowMap : H → SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ}
variable {w : H → ℝ}
variable {φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {ψ : ((v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ}
variable {r : {r : ℝ // 0 < r}} {B : ℕ}

/-- Primitive original profile and row-fibre conditions construct the
empty-mask calibration. No energy or transformed source bound is input. -/
def ofEmptyMask
    (hweight : ∀ h ∈ rows, 0 ≤ w h)
    (hreal : ∀ q : SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ,
      (gaussSourceProfile φ ψ r q).im = 0)
    (hpositive : ∀ q : SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ,
      0 ≤ (gaussSourceProfile φ ψ r q).re)
    (hrow : ∀ h ∈ rows, w h ≤ (gaussSourceProfile φ ψ r (rowMap h)).re)
    (hfibre : ∀ q, (rows.filter (fun h => rowMap h = q)).card ≤ B) :
    GaussEnergyChart rows rowMap w φ ψ r ∅ B where
  weight_nonneg := hweight
  profile_real := hreal
  profile_nonneg := hpositive
  row_weight := hrow
  row_mask h _ := sIntegerOrbitAvoidanceMask_empty K S Γ (rowMap h)
  fiber := hfibre

/-- This transports only a positive chart's primitive fields. It is
not a comparison between separate complex transformed summands. -/
def toEmptyMask
    {M : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K))}
    (cal : GaussEnergyChart rows rowMap w φ ψ r M B) :
    GaussEnergyChart rows rowMap w φ ψ r ∅ B :=
  ofEmptyMask cal.weight_nonneg cal.profile_real cal.profile_nonneg cal.row_weight cal.fiber

end GaussEnergyChart

/-- The fixed canonical positive profile needs only the original norm
window and finite row fibres when used with the empty row mask. -/
theorem CanonicalRowBall.chart_empty {H : Type*}
    (rows : Finset H)
    (rowMap : H → SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ)
    (r : {r : ℝ // 0 < r}) (B : ℝ) (fibres : ℕ)
    (hnorm : ∀ h ∈ rows,
      r.val * (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ (rowMap h)).val ≤ B)
    (hfibres : ∀ q, (rows.filter (fun h => rowMap h = q)).card ≤ fibres) :
    GaussEnergyChart rows rowMap (fun _ => 1) (CanonicalRowBall.archTest K S B)
      (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S B)) r ∅ fibres :=
  CanonicalRowBall.chart rows rowMap r B ∅ fibres hnorm
    (fun h _ => sIntegerOrbitAvoidanceMask_empty K S Γ (rowMap h)) hfibres

end Chart

namespace ActualGaussSource

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS} {ι : Type*}
variable (G : ActualGaussSource C ι)

/-- The direct and every pooled source use these same original rows. -/
theorem emptyMask_row_avoidance :
    ∀ h ∈ G.rows, ∀ p ∈ (∅ : Finset (HeightOneSpectrum A.R)), h ∉ p.asIdeal := by
  intro h hh p hp
  exact (Finset.notMem_empty p hp).elim

variable [IsPrincipalIdealRing A.R]

/-- Evidence for the existing canonical stage's column field. All
original coefficient and column-mask data remain inside G unchanged. -/
theorem emptyMask_columns_coprime :
    ∀ i ∈ G.columns, IsCoprime (G.generator i)
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅).val :=
  fun i _ => emptyMask_column_coprime K A.Sf (G.generator i)

end ActualGaussSource
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.sIntegerOrbitAvoidanceMask_empty
#print axioms HeckeSkeleton.Moments.EngineStep.sIntegerMaskGenerator_empty_isUnit
#print axioms HeckeSkeleton.Moments.EngineStep.sIntegerMaskGenerator_empty_norm
#print axioms HeckeSkeleton.Moments.EngineStep.secondOrbitalScalar_empty
#print axioms HeckeSkeleton.Moments.EngineStep.GaussEnergyChart.ofEmptyMask
#print axioms HeckeSkeleton.Moments.EngineStep.GaussEnergyChart.toEmptyMask
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalRowBall.chart_empty
