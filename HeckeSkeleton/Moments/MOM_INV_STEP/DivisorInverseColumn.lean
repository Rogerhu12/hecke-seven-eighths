import HeckeSkeleton.Moments.MOM_INV_STEP.FirstInversePoisson

/-!
# The retained first divisor in the actual intermediate inverse column

The first positive inverse column keeps the literal character χ_u(d)
of its fixed Poisson divisor. The divisor is not absorbed into a fifth
power of the row and is not replaced by an arbitrary coefficient on u.
The old averaged label still moves into the row as f², and the old-label
fiber estimate removes f,h with their original common weight.

The same decorated column is then squared on the actual orbital rows
and transformed by genuine second primitive Poisson. This produces a
fresh pair of squarefree columns while retaining both copies of χ_u(d)
with their proper conjugations. The final positive row absorbs that
retained divisor after this second transform.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.DivisorInverseColumn

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  MeasureTheory DedekindZetaZeroFree.LargeSieve
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalSectorRows
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

variable {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

/-- Exactly the fixed divisor character, multiplying the literal μν
coefficient with its original puncture, label, marks and norm cutoff. -/
def coefficient (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (j : Ideal (𝓞 K)) (d : OS) (n : Ext) : ℂ :=
  FirstCanonicalLabel.inverseCoefficient K S D C γ j n * idealSymbol K Sset D n d

def column (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (j : Ideal (𝓞 K)) (d : OS) (y : Ideal (𝓞 K) × Sector) : ℂ :=
  ∑ n ∈ C.columns γ, coefficient K S D C γ j d n *
    star (sectorRow K Sset D (CanonicalSectors.sectorUnit K Sset Γ) n y)

def oldAmplitude (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (j : Ideal (𝓞 K)) (d : OS) (E : Ext) (x : FirstCanonicalLabel.SourcePair K S Γ) : ℂ :=
  ∑ n ∈ C.columns γ, coefficient K S D C γ j d n *
    idealSymbol K Sset D n (D.generator x.1) ^ 4 *
    star (sectorCharacter K S Γ D n (exteriorMul K Sset E x.2.1) x.2.2)

include hallowed in
theorem oldAmplitude_eq (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (j : Ideal (𝓞 K)) (d : OS) (E : Ext) (x : FirstCanonicalLabel.SourcePair K S Γ) :
    oldAmplitude K S Γ D C γ j d E x =
      column K S Γ D C γ j d (FirstCanonicalLabel.newRow K S Γ E x) := by
  unfold oldAmplitude column
  apply Finset.sum_congr rfl
  intro n hn
  rw [FirstCanonicalLabel.newRow_eq, child_sectorRow, mul_assoc,
    first_label_absorb K S Γ D hallowed]

include hallowed in
/-- The actual retained-divisor inverse norm after the first positive
step. Its old f,h disappear; its fixed d stays in the same column. -/
theorem first_source_energy (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (j : Ideal (𝓞 K)) (d : OS) (E : Ext)
    (T : Finset (FirstCanonicalLabel.SourcePair K S Γ))
    (w : Ideal (𝓞 K) → ℝ) (a : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hw : ∀ x ∈ T, w x.1.val.val ≤ A * ((idealDivisors x.1.val.val).card : ℝ) ^ a) :
    (∑ x ∈ T, w x.1.val.val * ‖oldAmplitude K S Γ D C γ j d E x‖ ^ 2) ≤
      ∑ y ∈ T.image (FirstCanonicalLabel.newRow K S Γ E),
        (A * ((idealDivisors y.1).card : ℝ) ^ (a + 1)) * ‖column K S Γ D C γ j d y‖ ^ 2 := by
  let T' := T.image (FirstCanonicalLabel.encode K S Γ)
  have hw' : ∀ x ∈ T', w x.label ≤ A * ((idealDivisors x.label).card : ℝ) ^ a := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact hw z hz
  have hrow' : ∀ x ∈ T',
      (FirstLabelFibers.newRow (FirstCanonicalLabel.unchangedSector K S Γ) E.val.val x).1 ≠ 0 := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact FirstCanonicalLabel.newRow_ne_zero K S Γ E z
  have hb := FirstLabelFibers.source_energy_bound
    (sectorTransport := FirstCanonicalLabel.unchangedSector K S Γ)
    T' E.val.val w a A hA hw' hrow'
    (fun y => ‖column K S Γ D C γ j d y‖ ^ 2) (fun _ _ => sq_nonneg _)
  have hsum : (∑ x ∈ T', w x.label * ‖column K S Γ D C γ j d
      (FirstLabelFibers.newRow (FirstCanonicalLabel.unchangedSector K S Γ) E.val.val x)‖ ^ 2) =
      ∑ x ∈ T, w x.1.val.val * ‖oldAmplitude K S Γ D C γ j d E x‖ ^ 2 := by
    dsimp only [T']
    rw [Finset.sum_image (fun _ _ _ _ h => FirstCanonicalLabel.encode_injective K S Γ h)]
    apply Finset.sum_congr rfl
    intro x hx
    rw [oldAmplitude_eq K S Γ D hallowed]
    rfl
  rw [hsum] at hb
  refine hb.trans_eq ?_
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨z, hz, he⟩
  · intro hy
    obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨FirstCanonicalLabel.encode K S Γ z,
      Finset.mem_image.mpr ⟨z, hz, rfl⟩, he⟩

def orbitColumn (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (j : Ideal (𝓞 K)) (d : OS) (q : SIntegerOrbits K Sset Γ) : ℂ :=
  ∑ n ∈ C.columns γ, coefficient K S D C γ j d n * star (idealSymbol K Sset D n q.out.val)

variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
    ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)

include hΓ in
theorem orbitColumn_rowOrbit (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (j : Ideal (𝓞 K)) (d : OS) (I : Ext) (ξ : Sector) :
    orbitColumn K S Γ D C γ j d (CanonicalSectors.rowOrbit K Sset Γ D (I, ξ)) =
      column K S Γ D C γ j d (I.val.val, ξ) := by
  unfold orbitColumn column
  apply Finset.sum_congr rfl
  intro n hn
  rw [FirstInversePoisson.idealSymbol_rowOrbit K S Γ D hΓ, child_sectorRow]

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [Γ.FiniteIndex]

def weightedEnergy (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (j : Ideal (𝓞 K)) (d : OS) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) : ℂ :=
  sIntegerWeightedOrbitalSeries K S Γ φ (sIntegerFiniteTestFunction K S h) r
    (fun q => sIntegerOrbitAvoidanceMask K Sset Γ M q *
      ((‖orbitColumn K S Γ D C γ j d q‖ ^ 2 : ℝ) : ℂ))

theorem weightedEnergy_eq_inverseSquared (C : ColumnFamily K Sset σ Θ ψ)
    (γ : OuterTriple K) (j : Ideal (𝓞 K)) (d : OS) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) :
    weightedEnergy K S Γ D C γ j d φ h M r =
      CanonicalPoissonSource.inverseSquaredRowOrbitalSeries K S D Γ (C.columns γ)
        id (fun _ => FirstInversePoisson.unitIdeal K S) (coefficient K S D C γ j d) φ h M r := by
  unfold weightedEnergy CanonicalPoissonSource.inverseSquaredRowOrbitalSeries
  congr 1
  funext q
  simp only [orbitColumn, FirstInversePoisson.idealSymbol_unit, one_pow, one_mul,
    id_eq, starRingEnd_apply]

variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- The fresh second pair retains both literal copies of the first
mask divisor character, along with every original column decoration. -/
theorem genuine_second_poisson (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (j : Ideal (𝓞 K)) (d : OS) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) :
    weightedEnergy K S Γ D C γ j d φ h M r =
      ∑ p ∈ C.columns γ ×ˢ C.columns γ,
        conj (coefficient K S D C γ j d p.1) * coefficient K S D C γ j d p.2 *
          (PrimitivePoissonSource.block K S D Γ hΓ
            (PrimitivePoissonSource.pairSupport K S D p.1 p.2
              (FirstInversePoisson.unitIdeal K S) (FirstInversePoisson.unitIdeal K S))
            (PrimitivePoissonSource.pairExponent K S p.1 p.2
              (FirstInversePoisson.unitIdeal K S) (FirstInversePoisson.unitIdeal K S))
            φ h hlc hcs M r).transformed μv D.different_outside := by
  rw [weightedEnergy_eq_inverseSquared]
  exact PrimitivePoissonSource.inverseSquaredRowOrbitalSeries_primitive_poisson
    K S D Γ hΓ μv ν μ (C.columns γ) id (fun _ => FirstInversePoisson.unitIdeal K S)
    (coefficient K S D C γ j d) (fun n hn => C.columns_squarefree γ n hn) φ h hlc hcs M r

end HeckeSkeleton.Moments.MOM_INV_STEP.DivisorInverseColumn

end
