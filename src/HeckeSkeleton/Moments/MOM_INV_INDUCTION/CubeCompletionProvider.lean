import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionProfile
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionPools
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderFamily
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderCubeParent
import HeckeSkeleton.Moments.MOM_BASE.CoefficientInterfaces

/-!
# Actual reopened cubes enter the canonical parent provider

The live period is `background * lambda⁻¹`. Its cube character, label
mask, and original puncture stay in one bounded cube label weight. The
squarefree coefficient is still the actual calibrated canonical
coefficient with the same background. All original marks remain at
`n * b^3`. The only frequency-dependent data are the explicit common
cube phase and the common annular Schwartz test.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionProvider

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOM_BASE
open HeckeSkeleton.Moments.MOMInvStep
open HeckeSkeleton.Moments.MOM_INV_STEP
open CanonicalNormPools CanonicalChildren CommonKernel
open CubeCompletionMellin CubeCompletionEnergy CubeCompletionProfile
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
variable {σ : Type*}

def cubeIdeals (B : Finset Ext) : Finset (Ideal (𝓞 K)) := B.image (fun b => b.val.val)

def staticTau (C : CanonicalBlock.ColumnData K S σ) (f : Ext) : Ideal (𝓞 K) →* ℂ :=
  canonicalTau K Sset D (C.background * C.lambda⁻¹) (D.generator f ^ 4) C.puncture

theorem staticTau_norm_le (C : CanonicalBlock.ColumnData K S σ) (f : Ext)
    (I : Ideal (𝓞 K)) : ‖staticTau K S D C f I‖ ≤ 1 :=
  norm_canonicalTau_le_one K Sset D _ _ _ _

theorem canonicalTau_row_factor (C : CanonicalBlock.ColumnData K S σ)
    (f n : Ext) (k : (Sset).integer K) :
    canonicalTau K Sset D (C.background * C.lambda⁻¹)
        (k * D.generator f ^ 4) C.puncture n.val.val =
      staticTau K S D C f n.val.val * idealSymbol K Sset D n k := by
  rw [canonicalTau_label, staticTau, canonicalTau_apply, idealSymbol_pow_numerator]
  ring

theorem calibrated_static_coefficient (C : CanonicalBlock.ColumnData K S σ)
    (hΛ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K C.lambda p)
    (f n : Ext) :
    exteriorGamma K Sset D n.val.val * staticTau K S D C f n.val.val =
      CoefficientCycle.canonicalCoefficient K Sset D C.lambda n *
        heckeIdealCoefficient K C.background n.val *
        (if IsCoprime n.val.val C.puncture then 1 else 0) *
        idealSymbol K Sset D n (D.generator f) ^ 4 := by
  rw [exteriorGamma_apply, staticTau, canonicalTau_apply, idealSymbol_pow_numerator]
  calc
    _ = (thetaGamma K Sset D n 2 *
        heckeIdealCoefficient K (C.background * C.lambda⁻¹) n.val) *
        (if IsCoprime n.val.val C.puncture then 1 else 0) *
        idealSymbol K Sset D n (D.generator f) ^ 4 := by ring
    _ = _ := by rw [canonical_period_coefficient K Sset D C.lambda C.background hΛ n]

def bareCoefficient (C : CanonicalBlock.ColumnData K S σ) (f b n : Ext) : ℂ :=
  CoefficientCycle.canonicalCoefficient K Sset D C.lambda n *
    heckeIdealCoefficient K C.background n.val *
    (if IsCoprime n.val.val C.puncture then 1 else 0) *
    idealSymbol K Sset D n (D.generator f) ^ 4 *
    divisorMark C.slots C.primeLists C.primeWeights (n.val.val * b.val.val ^ 3)

def arithmeticCoefficient (C : CanonicalBlock.ColumnData K S σ)
    (P : Ideal (𝓞 K) → Prop) (B : Finset Ext) (H : ℝ) (f : Ext)
    (row : Ext → ℂ) (b n : Ext) : ℂ :=
  normalizedCubeBaseCoefficient P (cubeIdeals K S B) H (staticTau K S D C f) b.val.val *
    bareCoefficient K S D C f b n * row b ^ 3 * row n

/-- Exact arithmetic source identification, including the full square
root normalization. This theorem uses the actual Hecke coefficient
identity, not an assumed inverse-polynomial representation. -/
theorem reopened_term_eq_arithmetic
    (C : CanonicalBlock.ColumnData K S σ)
    (hΛ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K C.lambda p)
    (P : Ideal (𝓞 K) → Prop) (B : Finset Ext) (H X : ℝ)
    (hH : 0 < H) (hX : 0 < X) (f b n : Ext) (hn : Squarefree n.val.val)
    (k : (Sset).integer K) (W : SchwartzMap ℝ ℂ) :
    reopenedCubeCoefficient P b.val.val *
        canonicalCompletedTerm (exteriorGamma K Sset D)
          (canonicalTau K Sset D (C.background * C.lambda⁻¹)
            (k * D.generator f ^ 4) C.puncture)
          (divisorMark C.slots C.primeLists C.primeWeights) (canonicalVstar W) X
          (n.val.val, b.val.val) =
      (sourceScale (cubeIdeals K S B) H X : ℂ) *
        arithmeticCoefficient K S D C P B H f (fun I => idealSymbol K Sset D I k) b n *
          W (height K Sset b ^ 3 * height K Sset n / X) := by
  have hs := completedVstar_cube_normalization (height K Sset n) (height K Sset b) X
    (height_pos K Sset n) (height_pos K Sset b) hX
  have hb := sourceScale_mul_coefficient P (cubeIdeals K S B) H X hH
    (staticTau K S D C f) b.val.val
  have hc := calibrated_static_coefficient K S D C hΛ f n
  simp only [canonicalCompletedTerm, hn, if_true, map_mul, map_pow,
    canonicalTau_row_factor, canonicalVstar]
  change _ = _
  have hnormN : cubeIdealNorm n.val.val = height K Sset n := rfl
  have hnormB : cubeIdealNorm b.val.val = height K Sset b := rfl
  rw [hnormN, hnormB]
  calc
    _ = ((Real.sqrt (height K Sset n * height K Sset b ^ 3 / X) : ℂ) /
          ((Real.sqrt (height K Sset n) : ℂ) * (height K Sset b : ℂ))) *
        reopenedCubeCoefficient P b.val.val * staticTau K S D C f b.val.val ^ 3 *
        (exteriorGamma K Sset D n.val.val * staticTau K S D C f n.val.val) *
        idealSymbol K Sset D b k ^ 3 * idealSymbol K Sset D n k *
        divisorMark C.slots C.primeLists C.primeWeights (n.val.val * b.val.val ^ 3) *
        W (height K Sset n * height K Sset b ^ 3 / X) := by ring
    _ = _ := by
      rw [hs, hc]
      change _ = _
      rw [hnormB] at hb
      rw [← hb]
      simp only [arithmeticCoefficient, bareCoefficient]
      rw [mul_comm (height K Sset b ^ 3) (height K Sset n)]
      ring

theorem reopened_sum_eq_source
    (C : CanonicalBlock.ColumnData K S σ)
    (hΛ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K C.lambda p)
    (P : Ideal (𝓞 K) → Prop) (B N : Finset Ext) (H X : ℝ)
    (hH : 0 < H) (hX : 0 < X) (f : Ext)
    (hN : ∀ n ∈ N, Squarefree n.val.val) (k : (Sset).integer K) (W : SchwartzMap ℝ ℂ) :
    (∑ b ∈ B, ∑ n ∈ N, reopenedCubeCoefficient P b.val.val *
      canonicalCompletedTerm (exteriorGamma K Sset D)
        (canonicalTau K Sset D (C.background * C.lambda⁻¹)
          (k * D.generator f ^ 4) C.puncture)
        (divisorMark C.slots C.primeLists C.primeWeights) (canonicalVstar W) X
        (n.val.val, b.val.val)) =
      (sourceScale (cubeIdeals K S B) H X : ℂ) *
        source B N (height K Sset) (height K Sset)
          (arithmeticCoefficient K S D C P B H f (fun I => idealSymbol K Sset D I k)) W X := by
  rw [source, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simpa only [mul_assoc] using
    reopened_term_eq_arithmetic K S D C hΛ P B H X hH hX f b n (hN n hn) k W

def columns (C : CanonicalBlock.ColumnData K S σ)
    (P : Ideal (𝓞 K) → Prop) (B : Finset Ext) (H r t : ℝ)
    (i : SchwartzTestPartition.Index) : CanonicalBlock.ColumnData K S σ :=
  { C with
    labelWeight := fun b f => normalizedCubeLabelWeight P (cubeIdeals K S B) H
      (staticTau K S D C f) t b.val.val
    cutoff := annularTest t i
    length := r }

theorem columns_labelWeight_le (C : CanonicalBlock.ColumnData K S σ)
    (P : Ideal (𝓞 K) → Prop) (B : Finset Ext) (H r t : ℝ)
    (i : SchwartzTestPartition.Index) (hH : 0 < H)
    (hb : ∀ b ∈ B, height K Sset b ≤ 2 * H) (b : Ext) (hbB : b ∈ B) (f : Ext) :
    ‖(columns K S D C P B H r t i).labelWeight b f‖ ≤ 1 := by
  apply normalizedCubeLabelWeight_norm_le P (cubeIdeals K S B) H hH
    (staticTau K S D C f) t b.val.val
  · exact Finset.mem_image_of_mem _ hbB
  · exact hb b hbB
  · exact staticTau_norm_le K S D C f b.val.val

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

/-- Every separated finite column is the literal provider polynomial,
with both original row characters and the mark at `n*b^3`. -/
theorem annularColumn_eq_rowPolynomial
    (C : CanonicalBlock.ColumnData K S σ)
    (P : Ideal (𝓞 K) → Prop) (B N : Finset Ext) (H U r t : ℝ)
    (i : SchwartzTestPartition.Index) (f : Ext) (k : Ideal (𝓞 K) × Sector)
    (hscale : C.base ^ r = SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) * U) :
    annularColumn B N (height K Sset) (height K Sset)
      (arithmeticCoefficient K S D C P B H f
        (fun I => sectorRow K Sset D (CanonicalSectors.sectorUnit K Sset Γ) I k)) U t i =
      ProviderCubeParent.rowPolynomial K S D Γ (columns K S D C P B H r t i) B N f k := by
  simp only [annularColumn, ProviderCubeParent.rowPolynomial, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [CanonicalBlock.canonicalColumn, columns, arithmeticCoefficient, bareCoefficient,
    normalizedCubeLabelWeight, hscale, height, cubeIdealNorm]
  by_cases hcop : IsCoprime n.val.val C.puncture <;>
    simp only [hcop, if_true, if_false, mul_one, mul_zero, zero_mul] <;> ring

/-- The initial enlarged squarefree pool becomes the entire provider
pool for each common annular test. -/
theorem annularColumn_eq_complete_parent_row
    (C : CanonicalBlock.ColumnData K S σ)
    (P : Ideal (𝓞 K) → Prop) (B : Finset Ext) (H X U r t : ℝ)
    (i : SchwartzTestPartition.Index) (f : Ext) (k : Ideal (𝓞 K) × Sector)
    (hX : 0 < X) (hH : 1 ≤ H) (hU : U = X / H ^ 3)
    (hscale : C.base ^ r = SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) * U) :
    annularColumn B (squarefreePool K Sset (8 * X)) (height K Sset) (height K Sset)
      (arithmeticCoefficient K S D C P B H f
        (fun I => sectorRow K Sset D (CanonicalSectors.sectorUnit K Sset Γ) I k)) U t i =
      ProviderCubeParent.rowPolynomial K S D Γ (columns K S D C P B H r t i) B
        (squarefreePool K Sset (2 * C.base ^ r)) f k := by
  have hp := CubeCompletionPools.annularColumn_eq_complete K Sset B (height K Sset)
    (arithmeticCoefficient K S D C P B H f
      (fun I => sectorRow K Sset D (CanonicalSectors.sectorUnit K Sset Γ) I k))
    X H U hX hH hU t i
  have he := annularColumn_eq_rowPolynomial K S D Γ C P B
    (squarefreePool K Sset
      (2 * (SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) * U)))
    H U r t i f k hscale
  rw [hscale]
  exact hp.trans he

variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)

include hΓ in
/-- Actual weighted annular cube energy is dominated by the constructed
canonical parent. This is the concrete input to the generic common
Mellin energy inequality. -/
theorem annularEnergy_le_parent
    (C : CanonicalBlock.ColumnData K S σ)
    (P : Ideal (𝓞 K) → Prop) (B : Finset Ext) (H X U r t : ℝ)
    (i : SchwartzTestPartition.Index)
    (hX : 0 < X) (hH : 1 ≤ H) (hU : U = X / H ^ 3)
    (hbase : 0 < C.base)
    (hscale : C.base ^ r = SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) * U)
    (R : {r : ℝ // 0 < r}) (labels : Finset Ext) (w : Ext → ℝ)
    (hw : ∀ f ∈ labels, 0 ≤ w f)
    (rows : Finset (Ideal (𝓞 K) × Sector))
    (hrows : ∀ k ∈ rows, (k.1.absNorm : ℝ) ≤ R.val) :
    annularEnergy (labels ×ˢ rows) (fun fk => w fk.1)
      B (squarefreePool K Sset (8 * X)) (height K Sset) (height K Sset)
      (fun fk => arithmeticCoefficient K S D C P B H fk.1
        (fun I => sectorRow K Sset D (CanonicalSectors.sectorUnit K Sset Γ) I fk.2)) U t i ≤
      (InverseRowMajorant.rowCovolume K S)⁻¹ *
        ∑ f ∈ labels, w f *
          ‖FirstCappedProduction.parent K S D Γ
            (ProviderCubeParent.parentData K S (columns K S D C P B H r t i) B hbase R) f‖ := by
  have heq : annularEnergy (labels ×ˢ rows) (fun fk => w fk.1)
      B (squarefreePool K Sset (8 * X)) (height K Sset) (height K Sset)
      (fun fk => arithmeticCoefficient K S D C P B H fk.1
        (fun I => sectorRow K Sset D (CanonicalSectors.sectorUnit K Sset Γ) I fk.2)) U t i =
      ∑ f ∈ labels, w f * ∑ k ∈ rows,
        ‖annularColumn B (squarefreePool K Sset (8 * X)) (height K Sset) (height K Sset)
          (arithmeticCoefficient K S D C P B H f
            (fun I => sectorRow K Sset D (CanonicalSectors.sectorUnit K Sset Γ) I k)) U t i‖ ^ 2 := by
    simp only [annularEnergy, Finset.sum_product, Finset.mul_sum]
  rw [heq]
  simp_rw [annularColumn_eq_complete_parent_row K S D Γ C P B H X U r t i
    _ _ hX hH hU hscale]
  exact ProviderCubeParent.weighted_rows_le_parent K S D Γ hΓ
    (columns K S D C P B H r t i) B hbase R
    (annularTest t i) rfl (annularTest_support t i) labels w hw rows hrows

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionProvider
