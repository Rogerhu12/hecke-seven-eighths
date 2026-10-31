import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCanonicalLabel
import HeckeSkeleton.Moments.MOM_INV_STEP.PrimitivePoissonSource

/-!
# The first positive inverse column produces the fresh second source

The column is exactly `FirstCanonicalLabel.inverseColumn`, with its
literal μ coefficient and its fixed background, puncture, new label,
surviving original marks and norm test. Every original subgroup sector
is identified with its actual orbit, using proved sixth-unit invariance.

Its actual squared orbital series is then transformed by genuine
primitive Poisson. The resulting two indices are fresh squarefree
columns of this positive inverse norm. They are not the four historical
columns of `ActualSourceReindexing`. The coefficient conjugation has the
inverse orientation, and both additive zero terms and the full masks
remain in the primitive transformed block.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstInversePoisson

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  MeasureTheory
open HeckeSkeleton.Moments.MOMInvStep.FixedTripleFibers
open CanonicalChildren FirstCanonicalLabel
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
    ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- The inverse source has no cube variable: its cube ideal is the unit. -/
def unitIdeal : Ext := CanonicalIdealRow.toExterior K S 1

@[simp] theorem unitIdeal_nonzeroIdeal : (unitIdeal K S).val = 1 := rfl

@[simp] theorem unitIdeal_val : (unitIdeal K S).val.val = 1 := rfl

theorem idealSymbol_unit (a : OS) : idealSymbol K Sset D (unitIdeal K S) a = 1 := by
  have hStop : ∀ p : HeightOneSpectrum (𝓞 K),
      p.asIdeal ∣ (⊤ : Ideal (𝓞 K)) → p ∉ Sset := by
    intro p hp
    exact (p.isPrime.ne_top (top_le_iff.mp (Ideal.dvd_iff_le.mp hp))).elim
  simpa only [idealSymbol, unitIdeal, CanonicalIdealRow.toExterior,
    Submonoid.coe_one, Ideal.one_eq_top] using
    sIntegerSexticIdealEvaluation_top K Sset D.root6 D.primitive6 D.embedding
      hStop (fun p hp => D.away_six p (hStop p hp)) a

include hΓ in
/-- Actual orbit representatives have the same sextic value as their
canonical ideal-sector representative. -/
theorem idealSymbol_rowOrbit (n I : Ext) (ξ : Sector) :
    idealSymbol K Sset D n (CanonicalSectors.rowOrbit K Sset Γ D (I, ξ)).out.val =
      CanonicalSectorRows.sectorCharacter K S Γ D n I ξ := by
  have hrel := Quotient.exact
    (Quotient.out_eq (CanonicalSectors.rowOrbit K Sset Γ D (I, ξ)))
  obtain ⟨u, hu⟩ := (sIntegerOrbitRelation_iff K Sset Γ _ _).mp hrel
  have he : ((Sset).unitEquivUnitsInteger K u.val).val *
      (CanonicalSectors.rowElement K Sset Γ D (I, ξ)).val =
        (CanonicalSectors.rowOrbit K Sset Γ D (I, ξ)).out.val := Subtype.ext hu
  rw [← he, CanonicalPoissonSource.idealSymbol_literal_invariant K S D Γ hΓ]
  rfl

variable {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

def orbitColumn (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (j : Ideal (𝓞 K)) (q : SIntegerOrbits K Sset Γ) : ℂ :=
  ∑ n ∈ C.columns γ, inverseCoefficient K S D C γ j n *
    star (idealSymbol K Sset D n q.out.val)

include hΓ in
/-- This is the same first positive inverse column, now on genuine
subgroup orbits. No source-column identification is supplied as input. -/
theorem orbitColumn_rowOrbit (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (j : Ideal (𝓞 K)) (I : Ext) (ξ : Sector) :
    orbitColumn K S Γ D C γ j (CanonicalSectors.rowOrbit K Sset Γ D (I, ξ)) =
      inverseColumn K S Γ D C γ j (I.val.val, ξ) := by
  unfold orbitColumn inverseColumn
  apply Finset.sum_congr rfl
  intro n hn
  rw [idealSymbol_rowOrbit K S Γ D hΓ, CanonicalSectorRows.child_sectorRow]

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [Γ.FiniteIndex]

def weightedEnergy (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (j : Ideal (𝓞 K)) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) : ℂ :=
  sIntegerWeightedOrbitalSeries K S Γ φ (sIntegerFiniteTestFunction K S h) r
    (fun q => sIntegerOrbitAvoidanceMask K Sset Γ M q *
      ((‖orbitColumn K S Γ D C γ j q‖ ^ 2 : ℝ) : ℂ))

include hΓ in
/-- The complete original sector sum of the first positive inverse
column is the actual weighted orbital energy, with its original profile. -/
theorem weightedEnergy_eq_sector_sum (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (j : Ideal (𝓞 K)) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) :
    weightedEnergy K S Γ D C γ j φ h M r =
      ∑' x : Ext × Sector,
        (sIntegerOrbitAvoidanceMask K Sset Γ M (CanonicalSectors.rowOrbit K Sset Γ D x) *
          ((‖inverseColumn K S Γ D C γ j (x.1.val.val, x.2)‖ ^ 2 : ℝ) : ℂ)) *
        sUnitOrbitalProfile K Sset
          (sLocalTensorTestFunction K Sset φ (sIntegerFiniteTestFunction K S h))
          ⟨r.val * (sIntegerOrbitNorm K Sset Γ (CanonicalSectors.rowOrbit K Sset Γ D x)).val,
            mul_pos r.property
              (sIntegerOrbitNorm K Sset Γ (CanonicalSectors.rowOrbit K Sset Γ D x)).property⟩ := by
  unfold weightedEnergy sIntegerWeightedOrbitalSeries
  rw [CanonicalSectors.tsum_eq_ideal_sectors K Sset Γ D]
  apply tsum_congr
  intro x
  rw [orbitColumn_rowOrbit K S Γ D hΓ C γ j x.1 x.2]

theorem weightedEnergy_eq_inverseSquared (C : ColumnFamily K Sset σ Θ ψ)
    (γ : OuterTriple K) (j : Ideal (𝓞 K)) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) :
    weightedEnergy K S Γ D C γ j φ h M r =
      CanonicalPoissonSource.inverseSquaredRowOrbitalSeries K S D Γ
        (C.columns γ) id (fun _ => unitIdeal K S)
        (inverseCoefficient K S D C γ j) φ h M r := by
  unfold weightedEnergy CanonicalPoissonSource.inverseSquaredRowOrbitalSeries
  congr 1
  funext q
  simp only [orbitColumn, idealSymbol_unit, one_pow, one_mul, id_eq, starRingEnd_apply]

variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- Genuine second primitive Poisson on the first positive inverse
energy. Its pair consists of fresh x₁,x₂ from that column's actual
squarefree support, with opposite coefficient conjugations and every
zero-frequency and principal-mask term retained. -/
theorem genuine_second_poisson (C : ColumnFamily K Sset σ Θ ψ)
    (γ : OuterTriple K) (j : Ideal (𝓞 K)) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) :
    weightedEnergy K S Γ D C γ j φ h M r =
      ∑ p ∈ C.columns γ ×ˢ C.columns γ,
        conj (inverseCoefficient K S D C γ j p.1) * inverseCoefficient K S D C γ j p.2 *
          (PrimitivePoissonSource.block K S D Γ hΓ
            (PrimitivePoissonSource.pairSupport K S D p.1 p.2 (unitIdeal K S) (unitIdeal K S))
            (PrimitivePoissonSource.pairExponent K S p.1 p.2 (unitIdeal K S) (unitIdeal K S))
            φ h hlc hcs M r).transformed μv D.different_outside := by
  rw [weightedEnergy_eq_inverseSquared]
  exact PrimitivePoissonSource.inverseSquaredRowOrbitalSeries_primitive_poisson
    K S D Γ hΓ μv ν μ (C.columns γ) id (fun _ => unitIdeal K S)
    (inverseCoefficient K S D C γ j) (fun n hn => C.columns_squarefree γ n hn)
    φ h hlc hcs M r

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstInversePoisson

end
