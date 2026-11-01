import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderRows
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCappedProduction

/-!
# The actual reopened cube polynomial is an orbital parent

The whole finite cube polynomial is majorized before squaring or
discarding any row character. Its row factor is exactly
`idealSymbol b k ^ 3 * idealSymbol n k`, and its mark is still evaluated
on `n * b^3` inside `canonicalColumn`. This handles the long-cube part of
the genuine cube completion, with any row-independent cube coefficient.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderCubeParent

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckeSkeleton.Moments.MOMInvStep
open HeckeSkeleton.Moments.MOM_INV_STEP
open CanonicalNormPools CanonicalChildren
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "Orbit" => SIntegerOrbits K Sset Γ
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
variable {σ : Type*}

def amplitude (C : CanonicalBlock.ColumnData K S σ) (B N : Finset Ext)
    (f : Ext) (q : Orbit) : ℂ :=
  ∑ i ∈ B ×ˢ N, CanonicalBlock.canonicalColumn K S D C f i.1 i.2 *
    (idealSymbol K Sset D i.1 q.out.val ^ 3 * idealSymbol K Sset D i.2 q.out.val)

def rowPolynomial (C : CanonicalBlock.ColumnData K S σ) (B N : Finset Ext)
    (f : Ext) (k : Ideal (𝓞 K) × Sector) : ℂ :=
  ∑ i ∈ B ×ˢ N, CanonicalBlock.canonicalColumn K S D C f i.1 i.2 *
    (sectorRow K Sset D (CanonicalSectors.sectorUnit K Sset Γ) i.1 k ^ 3 *
      sectorRow K Sset D (CanonicalSectors.sectorUnit K Sset Γ) i.2 k)

theorem amplitude_norm_le (C : CanonicalBlock.ColumnData K S σ) (B N : Finset Ext)
    (f : Ext) (q : Orbit) :
    ‖amplitude K S D Γ C B N f q‖ ≤
      ∑ i ∈ B ×ˢ N, ‖CanonicalBlock.canonicalColumn K S D C f i.1 i.2‖ := by
  have hs (n : Ext) : ‖idealSymbol K Sset D n q.out.val‖ ≤ 1 :=
    norm_sIntegerSexticIdealEvaluation_le_one K Sset D.root6 D.primitive6 D.embedding
      n.val.val (nonZeroDivisors.coe_ne_zero n.val) n.property
      (fun p hp => D.away_six p (n.property p hp)) q.out.val
  unfold amplitude
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul, norm_mul, norm_pow]
  have hp : ‖idealSymbol K Sset D i.1 q.out.val‖ ^ 3 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (hs i.1) 3
  have hh : ‖idealSymbol K Sset D i.1 q.out.val‖ ^ 3 *
      ‖idealSymbol K Sset D i.2 q.out.val‖ ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hp (hs i.2) (norm_nonneg _) zero_le_one
  exact (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq (mul_one _)

def orbitalEnergy (C : CanonicalBlock.ColumnData K S σ) (B N : Finset Ext)
    (f : Ext) (H : {r : ℝ // 0 < r}) : ℂ :=
  sIntegerWeightedOrbitalSeries K S Γ (rowBallArchTest K S 1)
    (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S 1))
    (InverseRowMajorant.rowRadius H)
    (fun q => ((‖amplitude K S D Γ C B N f q‖ ^ 2 : ℝ) : ℂ))

theorem summable_norm_weightedProfile (C : CanonicalBlock.ColumnData K S σ)
    (B N : Finset Ext) (f : Ext) (H : {r : ℝ // 0 < r}) :
    Summable (fun q => ‖((‖amplitude K S D Γ C B N f q‖ ^ 2 : ℝ) : ℂ) *
      sUnitOrbitalProfile K Sset
        (sLocalTensorTestFunction K Sset (rowBallArchTest K S 1)
          (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S 1)))
        ⟨H.val⁻¹ * (sIntegerOrbitNorm K Sset Γ q).val,
          mul_pos (inv_pos.mpr H.property) (sIntegerOrbitNorm K Sset Γ q).property⟩‖) := by
  apply summable_norm_sIntegerWeightedOrbitalProfile K S Γ (rowBallArchTest K S 1)
    (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S 1))
    (continuous_sIntegerFiniteTestFunction K S _ (rowBallFiniteFamily_locallyConstant K S 1))
    (hasCompactSupport_sIntegerFiniteTestFunction K S _ (rowBallFiniteFamily_compactSupport K S 1))
    (InverseRowMajorant.rowRadius H)
    (fun q => ((‖amplitude K S D Γ C B N f q‖ ^ 2 : ℝ) : ℂ))
    ((∑ i ∈ B ×ˢ N, ‖CanonicalBlock.canonicalColumn K S D C f i.1 i.2‖) ^ 2)
  intro q
  rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (amplitude_norm_le K S D Γ C B N f q) 2

theorem orbitalEnergy_re (C : CanonicalBlock.ColumnData K S σ)
    (B N : Finset Ext) (f : Ext) (H : {r : ℝ // 0 < r}) :
    (orbitalEnergy K S D Γ C B N f H).re =
      ∑' q, ‖amplitude K S D Γ C B N f q‖ ^ 2 *
        InverseRowMajorant.fixedProfile K S Γ H q := by
  unfold orbitalEnergy sIntegerWeightedOrbitalSeries
  dsimp only [InverseRowMajorant.rowRadius]
  rw [Complex.re_tsum (summable_norm_weightedProfile K S D Γ C B N f H).of_norm]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rfl

theorem finite_orbit_rows_le (C : CanonicalBlock.ColumnData K S σ)
    (B N : Finset Ext) (f : Ext) (H : {r : ℝ // 0 < r}) (T : Finset Orbit)
    (hT : ∀ q ∈ T, (sIntegerOrbitNorm K Sset Γ q).val ≤ H.val) :
    (∑ q ∈ T, ‖amplitude K S D Γ C B N f q‖ ^ 2) ≤
      (InverseRowMajorant.rowCovolume K S)⁻¹ * ‖orbitalEnergy K S D Γ C B N f H‖ := by
  have hs : Summable (fun q => ‖amplitude K S D Γ C B N f q‖ ^ 2 *
      InverseRowMajorant.fixedProfile K S Γ H q) := by
    have hs := (summable_norm_weightedProfile K S D Γ C B N f H).of_norm
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, InverseRowMajorant.fixedProfile] using
      (Complex.hasSum_re hs.hasSum).summable
  have hp : InverseRowMajorant.rowCovolume K S *
      (∑ q ∈ T, ‖amplitude K S D Γ C B N f q‖ ^ 2) ≤
      (orbitalEnergy K S D Γ C B N f H).re := by
    rw [orbitalEnergy_re, Finset.mul_sum]
    apply (Finset.sum_le_sum (fun q hq =>
      (mul_le_mul_of_nonneg_right
        (InverseRowMajorant.fixedProfile_lower K S Γ H q (hT q hq))
        (sq_nonneg (‖amplitude K S D Γ C B N f q‖))).trans_eq (mul_comm _ _))).trans
    exact hs.sum_le_tsum T (fun q _ => mul_nonneg (sq_nonneg _)
      (InverseRowMajorant.fixedProfile_nonneg K S Γ H q))
  calc
    _ = (InverseRowMajorant.rowCovolume K S)⁻¹ *
        (InverseRowMajorant.rowCovolume K S *
          (∑ q ∈ T, ‖amplitude K S D Γ C B N f q‖ ^ 2)) := by
      rw [← mul_assoc, inv_mul_cancel₀ (InverseRowMajorant.rowCovolume_pos K S).ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hp.trans (Complex.re_le_norm _))
      (inv_nonneg.mpr (InverseRowMajorant.rowCovolume_pos K S).le)

variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →* ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)

include hΓ in
theorem amplitude_rowOrbit (C : CanonicalBlock.ColumnData K S σ)
    (B N : Finset Ext) (f I : Ext) (ξ : Sector) :
    amplitude K S D Γ C B N f (CanonicalSectors.rowOrbit K Sset Γ D (I, ξ)) =
      rowPolynomial K S D Γ C B N f (I.val.val, ξ) := by
  unfold amplitude rowPolynomial
  apply Finset.sum_congr rfl
  intro i hi
  rw [FirstInversePoisson.idealSymbol_rowOrbit K S Γ D hΓ,
    FirstInversePoisson.idealSymbol_rowOrbit K S Γ D hΓ,
    CanonicalSectorRows.child_sectorRow, CanonicalSectorRows.child_sectorRow]

theorem rowPolynomial_zero_of_not_exterior (C : CanonicalBlock.ColumnData K S σ)
    (B N : Finset Ext) (f : Ext) (k : Ideal (𝓞 K) × Sector)
    (hk : ¬ IsExterior K Sset k.1) : rowPolynomial K S D Γ C B N f k = 0 := by
  simp [rowPolynomial, sectorRow, hk]

include hΓ in
/-- The finite original ideal-sector rows of the entire cube polynomial
are dominated by the fixed positive orbital energy. -/
theorem finite_rows_le_orbital (C : CanonicalBlock.ColumnData K S σ)
    (B N : Finset Ext) (f : Ext) (H : {r : ℝ // 0 < r})
    (T : Finset (Ideal (𝓞 K) × Sector))
    (hT : ∀ k ∈ T, (k.1.absNorm : ℝ) ≤ H.val) :
    (∑ k ∈ T, ‖rowPolynomial K S D Γ C B N f k‖ ^ 2) ≤
      (InverseRowMajorant.rowCovolume K S)⁻¹ * ‖orbitalEnergy K S D Γ C B N f H‖ := by
  have hfilter : (∑ k ∈ T.filter (fun k => IsExterior K Sset k.1),
      ‖rowPolynomial K S D Γ C B N f k‖ ^ 2) =
      ∑ k ∈ T, ‖rowPolynomial K S D Γ C B N f k‖ ^ 2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hn
    have hbad : ¬ IsExterior K Sset k.1 := by
      intro hext
      exact hn (Finset.mem_filter.mpr ⟨hk, hext⟩)
    rw [rowPolynomial_zero_of_not_exterior K S D Γ C B N f k hbad]
    norm_num
  rw [← hfilter, ← ProviderRows.exteriorRows_image K S Γ T,
    Finset.sum_image (fun _ _ _ _ h => (ProviderRows.rowEmbedding K S Γ).injective h)]
  have hrowBound : ∀ q ∈ (ProviderRows.exteriorRows K S Γ T).image
      (CanonicalSectors.rowOrbit K Sset Γ D),
      (sIntegerOrbitNorm K Sset Γ q).val ≤ H.val := by
    intro q hq
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hq
    rw [CanonicalSectors.rowOrbit_norm]
    have hmem : ProviderRows.rowEmbedding K S Γ k ∈ T :=
      (Finset.mem_preimage (f := ProviderRows.rowEmbedding K S Γ)).mp hk
    exact hT (ProviderRows.rowEmbedding K S Γ k) hmem
  have hb := finite_orbit_rows_le K S D Γ C B N f H
    ((ProviderRows.exteriorRows K S Γ T).image (CanonicalSectors.rowOrbit K Sset Γ D))
    hrowBound
  rw [Finset.sum_image (fun _ _ _ _ h =>
    CanonicalSectors.rowOrbit_injective K Sset Γ D h)] at hb
  change (∑ x ∈ ProviderRows.exteriorRows K S Γ T,
      ‖rowPolynomial K S D Γ C B N f (x.1.val.val, x.2)‖ ^ 2) ≤ _
  simpa only [amplitude_rowOrbit K S D Γ hΓ] using hb

/-- The same fixed original profile supplies a genuine provider parent
for every finite cube pool and every row-independent cube coefficient. -/
def parentData (C : CanonicalBlock.ColumnData K S σ) (B : Finset Ext)
    (hbase : 0 < C.base) (H : {r : ℝ // 0 < r}) : FirstParentEnergy.Data K S (σ := σ) where
  columns := C
  label := FirstInversePoisson.unitIdeal K S
  cubes := B
  scale := ⟨C.base ^ C.length, Real.rpow_pos_of_pos hbase _⟩
  archTest := rowBallArchTest K S 1
  localTest := rowBallFiniteFamily K S 1
  locallyConstant := rowBallFiniteFamily_locallyConstant K S 1
  compactSupport := rowBallFiniteFamily_compactSupport K S 1
  mask := ∅
  radius := InverseRowMajorant.rowRadius H
  frequencyBound := 1

variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

theorem parent_eq_orbital (C : CanonicalBlock.ColumnData K S σ) (B : Finset Ext)
    (hbase : 0 < C.base) (H : {r : ℝ // 0 < r}) (f : Ext) :
    FirstCappedProduction.parent K S D Γ (parentData K S C B hbase H) f =
      orbitalEnergy K S D Γ C B (dyadicPool K Sset (C.base ^ C.length)) f H := by
  unfold FirstCappedProduction.parent CanonicalBlock.canonicalCubeEnergy
    CanonicalPoissonSource.squaredRowOrbitalSeries orbitalEnergy
  simp only [parentData, FirstParentEnergy.columnPool, amplitude,
    sIntegerOrbitAvoidanceMask, Finset.notMem_empty, false_implies, implies_true,
    if_true, one_mul]

include hΓ in
theorem finite_rows_le_parent (C : CanonicalBlock.ColumnData K S σ) (B : Finset Ext)
    (hbase : 0 < C.base) (H : {r : ℝ // 0 < r}) (f : Ext)
    (T : Finset (Ideal (𝓞 K) × Sector))
    (hT : ∀ k ∈ T, (k.1.absNorm : ℝ) ≤ H.val) :
    (∑ k ∈ T, ‖rowPolynomial K S D Γ C B (dyadicPool K Sset (C.base ^ C.length)) f k‖ ^ 2) ≤
      (InverseRowMajorant.rowCovolume K S)⁻¹ *
        ‖FirstCappedProduction.parent K S D Γ (parentData K S C B hbase H) f‖ := by
  rw [parent_eq_orbital]
  exact finite_rows_le_orbital K S D Γ hΓ C B _ f H T hT

/-- Annular support restricts the complete norm pool to the provider's
literal dyadic pool while preserving each whole-index mark. -/
theorem complete_row_eq_dyadic (C : CanonicalBlock.ColumnData K S σ)
    (B : Finset Ext) (f : Ext) (k : Ideal (𝓞 K) × Sector)
    (hbase : 0 < C.base) (W : SchwartzMap ℝ ℂ) (hcut : C.cutoff = W)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) :
    rowPolynomial K S D Γ C B (squarefreePool K Sset (2 * C.base ^ C.length)) f k =
      rowPolynomial K S D Γ C B (dyadicPool K Sset (C.base ^ C.length)) f k := by
  have hX : 0 < C.base ^ C.length := Real.rpow_pos_of_pos hbase _
  unfold rowPolynomial
  simp only [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro b hb
  symm
  apply Finset.sum_subset
  · intro n hn
    obtain ⟨hsf, hlo, hhi⟩ := (mem_dyadicPool K Sset _ n).mp hn
    exact (mem_squarefreePool K Sset _ n).mpr ⟨hsf, by linarith⟩
  · intro n hn hnot
    have hzero : W ((n.val.val.absNorm : ℝ) / C.base ^ C.length) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hs
      have hw := hW hs
      apply hnot
      apply (mem_dyadicPool K Sset _ n).mpr
      refine ⟨((mem_squarefreePool K Sset _ n).mp hn).1, ?_, ?_⟩
      · simpa only [one_mul, height] using (le_div_iff₀ hX).mp hw.1
      · simpa only [height] using (div_le_iff₀ hX).mp hw.2
    simp only [CanonicalBlock.canonicalColumn, hcut, hzero, mul_zero, zero_mul]

include hΓ in
/-- The actual finite cube row energy, including the averaged divisor
labels, is controlled by the constructed actual provider parents. -/
theorem weighted_rows_le_parent (C : CanonicalBlock.ColumnData K S σ) (B : Finset Ext)
    (hbase : 0 < C.base) (H : {r : ℝ // 0 < r})
    (W : SchwartzMap ℝ ℂ) (hcut : C.cutoff = W) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (labels : Finset Ext) (w : Ext → ℝ) (hw : ∀ f ∈ labels, 0 ≤ w f)
    (rows : Finset (Ideal (𝓞 K) × Sector))
    (hrows : ∀ k ∈ rows, (k.1.absNorm : ℝ) ≤ H.val) :
    (∑ f ∈ labels, w f * ∑ k ∈ rows,
      ‖rowPolynomial K S D Γ C B (squarefreePool K Sset (2 * C.base ^ C.length)) f k‖ ^ 2) ≤
      (InverseRowMajorant.rowCovolume K S)⁻¹ *
        ∑ f ∈ labels, w f *
          ‖FirstCappedProduction.parent K S D Γ (parentData K S C B hbase H) f‖ := by
  simp_rw [complete_row_eq_dyadic K S D Γ C B _ _ hbase W hcut hW]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro f hf
  exact (mul_le_mul_of_nonneg_left
    (finite_rows_le_parent K S D Γ hΓ C B hbase H f rows hrows) (hw f hf)).trans_eq (by ring)

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderCubeParent

end
