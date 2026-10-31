import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionNodeStep
import HeckeSkeleton.Moments.MOM_INV_STEP.SmallScaleEnergy
import HeckeSkeleton.Moments.MOM_INV_STEP.CoefficientBounds

/-!
# The subunit column branch of genuine cube completion

When a separated squarefree scale is below one, its actual [1,2]
profile permits only the unit ideal. The cube polynomial still keeps
every original mark at `n*b^3`; its mark is bounded using the proved
ideal-divisor small-power theorem. Actual ideal rows, labels and cube
supports are counted, and the source normalization cancels the cube
count against its genuine support condition `H^3 ≤ 2X`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionSmall

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep HeckeSkeleton.Moments.MOM_INV_STEP
open CanonicalNormPools CanonicalChildren FixedTripleEnergy
open ProviderNodes CubeCompletionMellin CubeCompletionGeometry CubeCompletionProfile
open CubeCompletionProvider CubeCompletionNodeStep
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
variable {σ : Type*}

theorem bareCoefficient_norm_le_mark (C : CanonicalBlock.ColumnData K S σ)
    (G : HeckeCharacter K) (hcal : ThetaCalibrationInput K Sset D C.lambda G)
    (f b n : Ext) (hn : Squarefree n.val.val) :
    ‖bareCoefficient K S D C f b n‖ ≤
      ‖divisorMark C.slots C.primeLists C.primeWeights (n.val.val * b.val.val ^ 3)‖ := by
  have hmask : ‖(if IsCoprime n.val.val C.puncture then 1 else 0 : ℂ)‖ ≤ 1 := by
    split_ifs <;> norm_num
  have hlabel := CoefficientBounds.idealSymbol_norm_le_one K S D n (D.generator f)
  have hbg := norm_heckeIdealCoefficient_le_one K C.background n.val
  simp only [bareCoefficient, norm_mul, norm_pow,
    CoefficientCycle.canonicalCoefficient_norm hcal n hn]
  calc
    _ ≤ 1 * 1 * 1 * 1 ^ 4 *
      ‖divisorMark C.slots C.primeLists C.primeWeights (n.val.val * b.val.val ^ 3)‖ := by
        gcongr
    _ = _ := by ring

theorem arithmeticCoefficient_norm_le_mark
    (C : CanonicalBlock.ColumnData K S σ)
    (G : HeckeCharacter K) (hcal : ThetaCalibrationInput K Sset D C.lambda G)
    (P : Ideal (𝓞 K) → Prop) (B : Finset Ext) (H : ℝ) (hH : 0 < H)
    (f b n : Ext) (hb : b ∈ B) (hbH : height K Sset b ≤ 2 * H)
    (hn : Squarefree n.val.val) (row : Ext → ℂ) (hrow : ∀ I, ‖row I‖ ≤ 1) :
    ‖arithmeticCoefficient K S D C P B H f row b n‖ ≤
      ‖divisorMark C.slots C.primeLists C.primeWeights (n.val.val * b.val.val ^ 3)‖ := by
  have hc := normalizedCubeBaseCoefficient_norm_le P (cubeIdeals K S B) H hH
    (staticTau K S D C f) b.val.val (Finset.mem_image_of_mem _ hb) hbH
    (staticTau_norm_le K S D C f b.val.val)
  have hm := bareCoefficient_norm_le_mark K S D C G hcal f b n hn
  simp only [arithmeticCoefficient, norm_mul, norm_pow]
  calc
    _ ≤ 1 * ‖divisorMark C.slots C.primeLists C.primeWeights
        (n.val.val * b.val.val ^ 3)‖ * 1 ^ 3 * 1 := by
      gcongr
      · exact hc
      · exact hm
      · exact hrow b
      · exact hrow n
    _ = _ := by ring

variable (Γ : Subgroup (Sset.unit K)) [Γ.FiniteIndex]
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

theorem sectorRow_norm_le_one (I : Ext) (k : Ideal (𝓞 K) × Sector) :
    ‖sectorRow K Sset D (CanonicalSectors.sectorUnit K Sset Γ) I k‖ ≤ 1 := by
  unfold sectorRow
  split_ifs
  · exact CoefficientBounds.idealSymbol_norm_le_one K S D I _
  · simp only [norm_zero, zero_le_one]

theorem exterior_label_mass_le (slotCap : ℕ) (labels : Finset (Ideal (𝓞 K))) :
    (∑ f ∈ ProviderChildParent.exteriorLabels K S labels,
      labelDivisorWeight slotCap f.val.val) ≤
      ∑ f ∈ labels, labelDivisorWeight slotCap f := by
  rw [← Finset.sum_image (fun _ _ _ _ h => (ProviderChildParent.labelEmbedding K S).injective h),
    ProviderChildParent.exteriorLabels_image]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun f _ _ => labelDivisorWeight_nonneg slotCap f)

/-- The small-column argument retains the actual arithmetic
coefficient and costs no squarefree-column cardinality. -/
theorem annularEnergy_le_mass {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}
    (slotCap : ℕ) (x : Node K S Γ Θ ψ σ)
    (P : Ideal (𝓞 K) → Prop) (B : Finset Ext) (H A : ℝ) (hH : 0 < H)
    (hbase : 0 < x.family.base) (hA : 0 ≤ A)
    (hcoeff : ∀ fk ∈ (ProviderChildParent.exteriorLabels K S x.labels) ×ˢ x.rows,
      ∀ b ∈ B, ∀ n ∈ squarefreePool K Sset (8 * x.family.base ^ x.columnLength),
        ‖coefficients K S D Γ x P B H fk b n‖ ≤ A)
    (s : ℝ) (i : SchwartzTestPartition.Index)
    (hsmall : annularScale i * (x.family.base ^ x.columnLength / H ^ 3) < 1) :
    annularEnergy K S D Γ slotCap x P B H s i ≤
      (x.rows.card : ℝ) * (∑ f ∈ x.labels, labelDivisorWeight slotCap f) *
        ((B.card : ℝ) * A) ^ 2 * (SchwartzMap.seminorm ℝ 0 0 (annularTest s i)) ^ 2 := by
  have hp := Real.rpow_pos_of_pos hbase x.columnLength
  have hpoint (fk) (hfk : fk ∈ (ProviderChildParent.exteriorLabels K S x.labels) ×ˢ x.rows) :
      ‖CubeCompletionEnergy.annularColumn B
        (squarefreePool K Sset (8 * x.family.base ^ x.columnLength))
        (height K Sset) (height K Sset) (coefficients K S D Γ x P B H fk)
        (x.family.base ^ x.columnLength / H ^ 3) s i‖ ^ 2 ≤
        ((B.card : ℝ) * A) ^ 2 * (SchwartzMap.seminorm ℝ 0 0 (annularTest s i)) ^ 2 := by
    have h := CubeCompletionPools.annularColumn_small_norm_le K Sset B _ (height K Sset)
      (coefficients K S D Γ x P B H fk) _ s A i (div_pos hp (pow_pos hH _))
      hsmall hA (hcoeff fk hfk)
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) h 2
  calc
    _ ≤ ∑ fk ∈ (ProviderChildParent.exteriorLabels K S x.labels) ×ˢ x.rows,
        labelDivisorWeight slotCap fk.1.val.val *
          (((B.card : ℝ) * A) ^ 2 * (SchwartzMap.seminorm ℝ 0 0 (annularTest s i)) ^ 2) :=
      Finset.sum_le_sum (fun fk hfk => mul_le_mul_of_nonneg_left (hpoint fk hfk)
        (labelDivisorWeight_nonneg slotCap _))
    _ = (x.rows.card : ℝ) *
        (∑ f ∈ ProviderChildParent.exteriorLabels K S x.labels, labelDivisorWeight slotCap f.val.val) *
        ((B.card : ℝ) * A) ^ 2 * (SchwartzMap.seminorm ℝ 0 0 (annularTest s i)) ^ 2 := by
      simp only [Finset.sum_product, Finset.sum_const, nsmul_eq_mul]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, ← Finset.sum_mul]
      ring
    _ ≤ _ := by
      gcongr
      exact exterior_label_mass_le K S slotCap x.labels

/-- A uniform bound for every actual subunit annular piece. The
constant precedes all node data. Its normalization is the same one as
the recursive branch, making the two branches usable under one common
Mellin integral. -/
theorem exists_uniform_small_annular_bound (slotCap : ℕ) (A pi : ℝ)
    (hA : 1 ≤ A) (hpi : 0 < pi) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {σ : Type*} (Θ : Subgroup (HeckeCharacter K)) (ψ Λ G : HeckeCharacter K)
        (Z Fcap c z lo hi : ℝ) (x : Node K S Γ Θ ψ σ),
      1 < Z → Fcap ≤ A → 0 ≤ c → 0 ≤ z →
      x.Admissible D Λ G slotCap Z Fcap c z lo hi →
      ∀ (P : Ideal (𝓞 K) → Prop) (B : Finset Ext) (H : ℝ),
      1 ≤ H → H ^ 3 ≤ 2 * Z ^ x.columnLength →
      (∀ b ∈ B, height K Sset b ≤ 2 * H) →
      ∀ (s : ℝ) (i : SchwartzTestPartition.Index),
      annularScale i * (Z ^ x.columnLength / H ^ 3) < 1 →
      annularEnergy K S D Γ slotCap x P B H s i ≤
        C * ((Z ^ x.columnLength) ^ 2 * (Z ^ x.labelLength) ^ 2 / H) * Z ^ pi *
          (SchwartzMap.seminorm ℝ 0 0 (annularTest s i)) ^ 2 := by
  let delta := pi / (8 * (A + 1))
  have hdelta : 0 < delta := div_pos hpi (by positivity)
  obtain ⟨Cm, hCm, hmark⟩ := CoefficientBounds.exists_divisorMark_bound K slotCap delta hdelta
  obtain ⟨Cb, hCb, _, hcount⟩ := DedekindZetaZeroFree.LargeSieve.exists_ideal_count_bound_finset K
  obtain ⟨Cr, hCr, hrows⟩ := SmallScaleEnergy.exists_row_count_bound K
  obtain ⟨Cl, hCl, hlabels⟩ := DivisorRowMass.exists_label_mass_bound
    (K := K) (9 + 4 * slotCap) (by omega) delta hdelta
  let Csmall := 8 * Cr * (Fintype.card Sector : ℝ) * Cl * Cb ^ 2 * Cm ^ 2 *
    (256 : ℝ) ^ (2 * delta)
  refine ⟨max 1 Csmall, le_max_left _ _, ?_⟩
  intro σ Θ ψ Λ G Z Fcap c z lo hi x hZ hFcap hc hz hx P B H hH hsupport hB s i hsmall
  have hz0 := zero_lt_one.trans hZ
  have hb0 : 0 < x.family.base := hx.base_eq.symm ▸ hz0
  have hH0 := zero_lt_one.trans_le hH
  let X := Z ^ x.columnLength
  let L := Z ^ x.labelLength
  let R := Z ^ x.rowLength
  have hX : 0 < X := Real.rpow_pos_of_pos hz0 _
  have hL : 0 < L := Real.rpow_pos_of_pos hz0 _
  have hR : 0 < R := Real.rpow_pos_of_pos hz0 _
  have hX1 : 1 ≤ X := Real.one_le_rpow hZ.le hx.column_nonneg
  have hL1 : 1 ≤ L := Real.one_le_rpow hZ.le hx.label_nonneg
  have hR1 : 1 ≤ R := Real.one_le_rpow hZ.le hx.row_nonneg
  have hlen := Node.Admissible.lengths_le x hx hZ hc hz
  have hMF : x.rowLength ≤ x.totalLength := by
    linarith [hx.margins.1, Node.Admissible.puncture_nonneg x hx hZ]
  have hRX : R ≤ X * L := by
    rw [← Real.rpow_add hz0]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le hMF
  have hbcard : (B.card : ℝ) ≤ 2 * Cb * H := by
    have hb := hcount (2 * H) (by linarith) (cubeIdeals K S B) (by
      intro J hJ
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hJ
      exact hB b hb)
    rw [cubeIdeals, Finset.card_image_of_injective _ (ideal_injective K Sset)] at hb
    nlinarith
  have hrmass : (x.rows.card : ℝ) ≤ Cr * (Fintype.card Sector : ℝ) * R :=
    hrows x.rows R hR1 hx.row_bound
  have hlmass : (∑ f ∈ x.labels, labelDivisorWeight slotCap f) ≤ Cl * L ^ (1 + delta) :=
    hlabels x.labels L hL1 hx.label_bound
  have hcoeff : ∀ fk ∈ (ProviderChildParent.exteriorLabels K S x.labels) ×ˢ x.rows,
      ∀ b ∈ B, ∀ n ∈ squarefreePool K Sset (8 * x.family.base ^ x.columnLength),
        ‖coefficients K S D Γ x P B H fk b n‖ ≤ Cm * (256 * X ^ 2) ^ delta := by
    intro fk hfk b hb n hn
    obtain ⟨hsf, hnX⟩ := (mem_squarefreePool K Sset _ n).mp hn
    rw [hx.base_eq] at hnX
    have hnb0 : n.val.val * b.val.val ^ 3 ≠ 0 :=
      mul_ne_zero (nonZeroDivisors.coe_ne_zero n.val)
        (pow_ne_zero 3 (nonZeroDivisors.coe_ne_zero b.val))
    have hnorm : (Ideal.absNorm (n.val.val * b.val.val ^ 3) : ℝ) ≤ 256 * X ^ 2 := by
      simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
      have hbpow : height K Sset b ^ 3 ≤ (2 * H) ^ 3 :=
        pow_le_pow_left₀ (height_pos K Sset b).le (hB b hb) 3
      have hhn : height K Sset n ≤ 16 * X := by linarith
      calc
        _ ≤ (16 * X) * (2 * H) ^ 3 := mul_le_mul hhn hbpow
          (pow_nonneg (height_pos K Sset b).le 3) (by positivity)
        _ ≤ 256 * X ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hsupport (by positivity : 0 ≤ 128 * X)]
    have hm := hmark (x.family.survivors x.triple) x.family.primeLists x.family.primeWeights
      (n.val.val * b.val.val ^ 3) hnb0 hx.marks.card_le hx.marks.weights_le
    exact (arithmeticCoefficient_norm_le_mark K S D
      (ProviderChildParent.columns K S x.family x.triple) G hx.calibration P B H hH0
      fk.1 b n hb (hB b hb) hsf _ (fun J => sectorRow_norm_le_one K S D Γ J fk.2)).trans
      (hm.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm hdelta.le) (zero_le_one.trans hCm)))
  have hraw := annularEnergy_le_mass K S D Γ slotCap x P B H
    (Cm * (256 * X ^ 2) ^ delta) hH0 hb0 (by positivity) hcoeff s i
    (by simpa only [hx.base_eq] using hsmall)
  have hmass := mul_le_mul hrmass hlmass
    (Finset.sum_nonneg fun f _ => labelDivisorWeight_nonneg slotCap f)
    (by positivity : 0 ≤ Cr * (Fintype.card Sector : ℝ) * R)
  have hcard := pow_le_pow_left₀ (by positivity : 0 ≤ (B.card : ℝ) * (Cm * (256 * X ^ 2) ^ delta))
    (mul_le_mul_of_nonneg_right hbcard (by positivity : 0 ≤ Cm * (256 * X ^ 2) ^ delta)) 2
  have hscalar : H ^ 2 * R * L ≤ 2 * (X ^ 2 * L ^ 2 / H) := by
    rw [show 2 * (X ^ 2 * L ^ 2 / H) = (2 * X ^ 2 * L ^ 2) / H by ring]
    apply (le_div_iff₀ hH0).mpr
    have hprod := mul_le_mul hsupport hRX hR.le (by positivity : 0 ≤ 2 * X)
    nlinarith [mul_le_mul_of_nonneg_right hprod hL.le]
  have hexponent : (4 * x.columnLength + x.labelLength) * delta ≤ pi := by
    have ha0 : 0 < A + 1 := by linarith
    have hnum : 4 * x.columnLength + x.labelLength ≤ 5 * A := by
      linarith [hlen.2.1, hlen.2.2]
    have he : 5 * A * delta ≤ pi := by
      dsimp only [delta]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < 8 * (A + 1))).mpr
      nlinarith
    exact (mul_le_mul_of_nonneg_right hnum hdelta.le).trans he
  have hsmallpower : L ^ delta * (X ^ 2) ^ (2 * delta) ≤ Z ^ pi := by
    have heq : L ^ delta * (X ^ 2) ^ (2 * delta) =
        Z ^ ((4 * x.columnLength + x.labelLength) * delta) := by
      dsimp only [X, L]
      rw [← Real.rpow_mul hz0.le, ← Real.rpow_natCast, ← Real.rpow_mul hz0.le,
        ← Real.rpow_mul hz0.le, ← Real.rpow_add hz0]
      congr 1
      ring
    rw [heq]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le hexponent
  have hbound : annularEnergy K S D Γ slotCap x P B H s i ≤
      Csmall * (X ^ 2 * L ^ 2 / H) * Z ^ pi *
        (SchwartzMap.seminorm ℝ 0 0 (annularTest s i)) ^ 2 := by
    calc
      _ ≤ ((Cr * (Fintype.card Sector : ℝ) * R) * (Cl * L ^ (1 + delta))) *
          ((2 * Cb * H) * (Cm * (256 * X ^ 2) ^ delta)) ^ 2 *
          (SchwartzMap.seminorm ℝ 0 0 (annularTest s i)) ^ 2 :=
        hraw.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul hmass hcard (sq_nonneg _) (by positivity)) (sq_nonneg _))
      _ = (4 * Cr * (Fintype.card Sector : ℝ) * Cl * Cb ^ 2 * Cm ^ 2 *
          (256 : ℝ) ^ (2 * delta)) * (H ^ 2 * R * L) *
          (L ^ delta * (X ^ 2) ^ (2 * delta)) *
          (SchwartzMap.seminorm ℝ 0 0 (annularTest s i)) ^ 2 := by
        rw [Real.rpow_add hL, Real.rpow_one, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 256) (sq_nonneg X)]
        simp only [mul_pow]
        rw [show ((256 : ℝ) ^ delta) ^ 2 = (256 : ℝ) ^ (2 * delta) by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 256)]
          congr 1
          ring,
          show ((X ^ 2) ^ delta) ^ 2 = (X ^ 2) ^ (2 * delta) by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (sq_nonneg X)]
            congr 1
            ring]
        ring
      _ ≤ (4 * Cr * (Fintype.card Sector : ℝ) * Cl * Cb ^ 2 * Cm ^ 2 *
          (256 : ℝ) ^ (2 * delta)) * (2 * (X ^ 2 * L ^ 2 / H)) * Z ^ pi *
          (SchwartzMap.seminorm ℝ 0 0 (annularTest s i)) ^ 2 := by
        gcongr
      _ = _ := by dsimp only [Csmall]; ring
  apply hbound.trans
  change _ ≤ max 1 Csmall * (X ^ 2 * L ^ 2 / H) * Z ^ pi * _
  gcongr
  exact le_max_right (1 : ℝ) Csmall

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionSmall
