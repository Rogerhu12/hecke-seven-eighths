import HeckeSkeleton.Moments.MOM_INV_STEP.InverseRowMajorant

/-!
# Forward canonical rows and the fixed orbital majorant

The provider's children use the forward sextic row. Conjugating the
whole amplitude transports the already proved positive orbital
majorant to this orientation, with the same covolume, all original
unit sectors, and no extra coefficient or mask. The coefficient below
is extracted literally from `CanonicalChildren.column`.
-/

noncomputable section

set_option maxHeartbeats 1600000

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderRows

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckeSkeleton.Moments.MOMInvStep
open HeckeSkeleton.Moments.MOM_INV_STEP
open FixedTripleFibers CanonicalChildren
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "Orbit" => SIntegerOrbits K Sset Γ
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

def amplitude (N : Finset Ext) (a : Ext → ℂ) (q : Orbit) : ℂ :=
  ∑ n ∈ N, a n * idealSymbol K Sset D n q.out.val

theorem amplitude_eq_star_inverse (N : Finset Ext) (a : Ext → ℂ) (q : Orbit) :
    amplitude K S Γ D N a q =
      star (InverseRowMajorant.amplitude K S Γ D N (fun n => star (a n)) q) := by
  simp only [amplitude, InverseRowMajorant.amplitude, star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro n hn
  exact mul_comm _ _

theorem amplitude_norm_eq_inverse (N : Finset Ext) (a : Ext → ℂ) (q : Orbit) :
    ‖amplitude K S Γ D N a q‖ =
      ‖InverseRowMajorant.amplitude K S Γ D N (fun n => star (a n)) q‖ := by
  rw [amplitude_eq_star_inverse, norm_star]

def energy (N : Finset Ext) (a : Ext → ℂ) (H : {r : ℝ // 0 < r}) : ℝ :=
  InverseRowMajorant.energy K S Γ D N (fun n => star (a n)) H

theorem energy_eq_tsum (N : Finset Ext) (a : Ext → ℂ) (H : {r : ℝ // 0 < r}) :
    energy K S Γ D N a H = ∑' q, ‖amplitude K S Γ D N a q‖ ^ 2 *
      InverseRowMajorant.fixedProfile K S Γ H q := by
  simp only [energy, InverseRowMajorant.energy, amplitude_norm_eq_inverse]

theorem energy_nonneg (N : Finset Ext) (a : Ext → ℂ) (H : {r : ℝ // 0 < r}) :
    0 ≤ energy K S Γ D N a H :=
  InverseRowMajorant.energy_nonneg K S Γ D N (fun n => star (a n)) H

/-- Forward rows use precisely the same fixed positive orbital majorant. -/
theorem finite_rows_le_energy (N : Finset Ext) (a : Ext → ℂ)
    (H : {r : ℝ // 0 < r}) (T : Finset Orbit)
    (hT : ∀ q ∈ T, (sIntegerOrbitNorm K Sset Γ q).val ≤ H.val) :
    (∑ q ∈ T, ‖amplitude K S Γ D N a q‖ ^ 2) ≤
      (InverseRowMajorant.rowCovolume K S)⁻¹ * energy K S Γ D N a H := by
  simpa only [energy, amplitude_norm_eq_inverse] using
    InverseRowMajorant.finite_rows_le_energy K S Γ D N (fun n => star (a n)) H T hT

variable {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

/-- The actual child coefficient, with the row character removed and
the full puncture, label, original marks, and norm test retained. -/
def coefficient (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (f : Ideal (𝓞 K)) (n : Ext) : ℂ :=
  CoefficientCycle.canonicalCoefficient K Sset D C.lambda n *
    heckeIdealCoefficient K (C.background γ) n.val *
    (if IsCoprime n.val.val (childPuncture C.originalPuncture γ) then 1 else 0) *
    labelRow K Sset D n f ^ 4 *
    divisorMark (C.survivors γ) C.primeLists C.primeWeights n.val.val *
    C.cutoff γ ((n.val.val.absNorm : ℝ) / C.base ^ C.columnLength γ)

theorem column_eq_sum (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (f : Ideal (𝓞 K)) (k : Ideal (𝓞 K) × Sector) :
    column K Sset D C (CanonicalSectors.sectorUnit K Sset Γ) γ f k =
      ∑ n ∈ C.columns γ, coefficient K S D C γ f n *
        sectorRow K Sset D (CanonicalSectors.sectorUnit K Sset Γ) n k := by
  unfold column
  apply Finset.sum_congr rfl
  intro n hn
  unfold coefficient
  ring

variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)

include hΓ in
theorem amplitude_rowOrbit (C : ColumnFamily K Sset σ Θ ψ)
    (γ : OuterTriple K) (f : Ideal (𝓞 K)) (I : Ext) (ξ : Sector) :
    amplitude K S Γ D (C.columns γ) (coefficient K S D C γ f)
      (CanonicalSectors.rowOrbit K Sset Γ D (I, ξ)) =
      column K Sset D C (CanonicalSectors.sectorUnit K Sset Γ) γ f (I.val.val, ξ) := by
  rw [column_eq_sum]
  unfold amplitude
  apply Finset.sum_congr rfl
  intro n hn
  rw [FirstInversePoisson.idealSymbol_rowOrbit K S Γ D hΓ,
    CanonicalSectorRows.child_sectorRow]

include hΓ in
/-- Every original unit sector is injected into its actual subgroup
orbit before the finite row set is enlarged. -/
theorem canonical_sector_rows_le_energy (C : ColumnFamily K Sset σ Θ ψ)
    (γ : OuterTriple K) (f : Ideal (𝓞 K))
    (H : {r : ℝ // 0 < r}) (T : Finset (Ext × Sector))
    (hT : ∀ x ∈ T, (x.1.val.val.absNorm : ℝ) ≤ H.val) :
    (∑ x ∈ T,
      ‖column K Sset D C (CanonicalSectors.sectorUnit K Sset Γ) γ f (x.1.val.val,x.2)‖ ^ 2) ≤
      (InverseRowMajorant.rowCovolume K S)⁻¹ *
        energy K S Γ D (C.columns γ) (coefficient K S D C γ f) H := by
  have he := finite_rows_le_energy K S Γ D (C.columns γ)
    (coefficient K S D C γ f) H
    (T.image (CanonicalSectors.rowOrbit K Sset Γ D)) (by
      intro q hq
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
      rw [CanonicalSectors.rowOrbit_norm]
      exact hT x hx)
  rw [Finset.sum_image (fun _ _ _ _ h =>
    CanonicalSectors.rowOrbit_injective K Sset Γ D h)] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro x hx
  exact congrArg (fun z : ℂ => ‖z‖ ^ 2)
    (amplitude_rowOrbit K S Γ D hΓ C γ f x.1 x.2).symm

def orbitalEnergy (N : Finset Ext) (a : Ext → ℂ)
    (H : {r : ℝ // 0 < r}) : ℂ :=
  sIntegerWeightedOrbitalSeries K S Γ (rowBallArchTest K S 1)
    (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S 1))
    (InverseRowMajorant.rowRadius H)
    (fun q => ((‖amplitude K S Γ D N a q‖ ^ 2 : ℝ) : ℂ))

/-- The positive real energy is the real part of the literal orbital
series used as a new Poisson parent. -/
theorem orbitalEnergy_re (N : Finset Ext) (a : Ext → ℂ)
    (H : {r : ℝ // 0 < r}) :
    (orbitalEnergy K S Γ D N a H).re = energy K S Γ D N a H := by
  unfold orbitalEnergy sIntegerWeightedOrbitalSeries
  simp only [amplitude_norm_eq_inverse, InverseRowMajorant.rowRadius]
  have hs := (InverseRowMajorant.summable_norm_weightedProfile
    K S Γ D N (fun n => star (a n)) H).of_norm
  rw [Complex.re_tsum hs]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rfl

include hΓ in
/-- The finite forward child row sum is controlled by the norm of an
actual positive orbital parent, with the original covolume once. -/
theorem canonical_sector_rows_le_orbital_norm (C : ColumnFamily K Sset σ Θ ψ)
    (γ : OuterTriple K) (f : Ideal (𝓞 K))
    (H : {r : ℝ // 0 < r}) (T : Finset (Ext × Sector))
    (hT : ∀ x ∈ T, (x.1.val.val.absNorm : ℝ) ≤ H.val) :
    (∑ x ∈ T,
      ‖column K Sset D C (CanonicalSectors.sectorUnit K Sset Γ) γ f (x.1.val.val,x.2)‖ ^ 2) ≤
      (InverseRowMajorant.rowCovolume K S)⁻¹ *
        ‖orbitalEnergy K S Γ D (C.columns γ) (coefficient K S D C γ f) H‖ := by
  apply (canonical_sector_rows_le_energy K S Γ D hΓ C γ f H T hT).trans
  rw [← orbitalEnergy_re]
  exact mul_le_mul_of_nonneg_left (Complex.re_le_norm _)
    (inv_nonneg.mpr (InverseRowMajorant.rowCovolume_pos K S).le)

def rowEmbedding : (Ext × Sector) ↪ (Ideal (𝓞 K) × Sector) where
  toFun x := (x.1.val.val, x.2)
  inj' := by
    intro x y h
    exact Prod.ext
      (Subtype.ext (Subtype.ext (congrArg (fun z : Ideal (𝓞 K) × Sector => z.1) h)))
      (congrArg (fun z : Ideal (𝓞 K) × Sector => z.2) h)

def exteriorRows (T : Finset (Ideal (𝓞 K) × Sector)) : Finset (Ext × Sector) :=
  T.preimage (rowEmbedding K S Γ) (rowEmbedding K S Γ).injective.injOn

theorem exteriorRows_image (T : Finset (Ideal (𝓞 K) × Sector)) :
    (exteriorRows K S Γ T).image (rowEmbedding K S Γ) =
      T.filter (fun x => IsExterior K Sset x.1) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_preimage.mp hy), exterior_isExterior K Sset y.1⟩
  · intro hx
    obtain ⟨hx, hI⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_image.mpr ⟨(exteriorOf K Sset x.1 hI, x.2), ?_, ?_⟩
    · exact Finset.mem_preimage.mpr hx
    · rfl

theorem column_zero_of_not_exterior (C : ColumnFamily K Sset σ Θ ψ)
    (γ : OuterTriple K) (f : Ideal (𝓞 K)) (k : Ideal (𝓞 K) × Sector)
    (hk : ¬ IsExterior K Sset k.1) :
    column K Sset D C (CanonicalSectors.sectorUnit K Sset Γ) γ f k = 0 := by
  simp [column, sectorRow, hk]

/-- Inadmissible ideals in an enlarged packet row set contribute zero.
Removing them and reindexing the exterior rows is an exact identity. -/
theorem rows_sum_eq_exterior (C : ColumnFamily K Sset σ Θ ψ)
    (γ : OuterTriple K) (f : Ideal (𝓞 K)) (T : Finset (Ideal (𝓞 K) × Sector)) :
    (∑ x ∈ T, ‖column K Sset D C (CanonicalSectors.sectorUnit K Sset Γ) γ f x‖ ^ 2) =
      ∑ x ∈ exteriorRows K S Γ T,
        ‖column K Sset D C (CanonicalSectors.sectorUnit K Sset Γ) γ f (x.1.val.val,x.2)‖ ^ 2 := by
  have hf : (∑ x ∈ T.filter (fun x => IsExterior K Sset x.1),
      ‖column K Sset D C (CanonicalSectors.sectorUnit K Sset Γ) γ f x‖ ^ 2) =
      ∑ x ∈ T, ‖column K Sset D C (CanonicalSectors.sectorUnit K Sset Γ) γ f x‖ ^ 2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x hx hn
    have hbad : ¬ IsExterior K Sset x.1 := by
      intro hi
      exact hn (Finset.mem_filter.mpr ⟨hx, hi⟩)
    rw [column_zero_of_not_exterior K S Γ D C γ f x hbad]
    norm_num
  rw [← hf, ← exteriorRows_image K S Γ T,
    Finset.sum_image (fun _ _ _ _ h => (rowEmbedding K S Γ).injective h)]
  rfl

set_option maxHeartbeats 6400000 in
include hΓ in
/-- The row ranges used by the actual packet need no separate
exterior-ideal assumption. All bad rows are removed by exact zeros. -/
theorem canonical_rows_le_orbital_norm (C : ColumnFamily K Sset σ Θ ψ)
    (γ : OuterTriple K) (f : Ideal (𝓞 K))
    (H : {r : ℝ // 0 < r}) (T : Finset (Ideal (𝓞 K) × Sector))
    (hT : ∀ x ∈ T, (x.1.absNorm : ℝ) ≤ H.val) :
    (∑ x ∈ T,
      ‖column K Sset D C (CanonicalSectors.sectorUnit K Sset Γ) γ f x‖ ^ 2) ≤
      (InverseRowMajorant.rowCovolume K S)⁻¹ *
        ‖orbitalEnergy K S Γ D (C.columns γ) (coefficient K S D C γ f) H‖ := by
  have hrows : ∀ x ∈ exteriorRows K S Γ T, (x.1.val.val.absNorm : ℝ) ≤ H.val := by
    intro x hx
    have hmem : rowEmbedding K S Γ x ∈ T :=
      (Finset.mem_preimage (f := rowEmbedding K S Γ)).mp hx
    exact hT (rowEmbedding K S Γ x) hmem
  calc
    _ = ∑ x ∈ exteriorRows K S Γ T,
        ‖column K Sset D C (CanonicalSectors.sectorUnit K Sset Γ) γ f (x.1.val.val, x.2)‖ ^ 2 :=
      rows_sum_eq_exterior K S Γ D C γ f T
    _ ≤ _ := canonical_sector_rows_le_orbital_norm K S Γ D hΓ C γ f H
      (exteriorRows K S Γ T) hrows

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderRows

end
