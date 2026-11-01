import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionNodeStep
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionBlocks
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderNode

/-!
# The literal long completed node is a finite family of cube sources

The cube pool is cut out by the genuine long Möbius coefficient and
the original joint profile. Every nonzero cube satisfies `N(b)^3 ≤ 2X`.
An exact dyadic partition then exposes the actual finite source needed
by the common Mellin estimate. Nonexterior rows and labels keep their
original zeros throughout this reindexing.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionFinite

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOM_BASE HeckeSkeleton.Moments.MOMInvStep
open HeckeSkeleton.Moments.MOM_INV_STEP
open CanonicalNormPools CanonicalChildren FixedTripleEnergy
open ProviderNodes CubeCompletionProfile CubeCompletionNodeStep
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset

def longPool (X T : ℝ) : Finset Ext :=
  (boundedPool K Sset X).filter (fun b => T ≤ height K Sset b ∧ height K Sset b ^ 3 ≤ 2 * X)

theorem longPool_norm_bounds (X T : ℝ) (b : Ext) (hb : b ∈ longPool K S X T) :
    1 ≤ height K Sset b ∧ height K Sset b ≤ 2 * X ∧
      T ≤ height K Sset b ∧ height K Sset b ^ 3 ≤ 2 * X := by
  obtain ⟨hb, hlong, hcube⟩ := Finset.mem_filter.mp hb
  have hnorm : height K Sset b ≤ 2 * X := by
    simpa only [boundedPool, Finset.mem_preimage,
      DedekindZetaZeroFree.LargeSieve.mem_boundedNormIdeals, height] using hb
  exact ⟨height_one_le K Sset b, hnorm, hlong, hcube⟩

theorem block_support (X T : ℝ) (j : ℕ)
    (hne : (CubeCompletionBlocks.block (longPool K S X T) (height K Sset) j).Nonempty) :
    CubeCompletionBlocks.scale j ^ 3 ≤ 2 * X := by
  obtain ⟨b, hb⟩ := hne
  have hbP := (CubeCompletionBlocks.mem_block _ _ _ _).mp hb
  have hw := CubeCompletionBlocks.block_window (longPool K S X T) (height K Sset) j
    (fun I _ => height_one_le K Sset I) b hb
  exact (pow_le_pow_left₀ (CubeCompletionBlocks.scale_pos j).le hw.1 3).trans
    (longPool_norm_bounds K S X T b hbP.1).2.2.2

variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

/-- Both restrictions of `longPool` are consequences of the literal
summand, before the common radial profile is separated. -/
theorem reopened_eq_longPool
    (θ : HeckeCharacter K) (m : (Sset).integer K) (r : Ideal (𝓞 K))
    (mark : Ideal (𝓞 K) → ℂ) (W : SchwartzMap ℝ ℂ) (X T : ℝ)
    (hX : 0 < X) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) :
    (∑' CB : Ideal (𝓞 K) × Ideal (𝓞 K),
      reopenedCubeCoefficient (fun H => T ≤ cubeIdealNorm H) CB.2 *
        canonicalCompletedTerm (exteriorGamma K Sset D) (canonicalTau K Sset D θ m r)
          mark (canonicalVstar W) X CB) =
      ∑ b ∈ longPool K S X T, ∑ n ∈ squarefreePool K Sset (8 * X),
        reopenedCubeCoefficient (fun H => T ≤ cubeIdealNorm H) b.val.val *
          canonicalCompletedTerm (exteriorGamma K Sset D) (canonicalTau K Sset D θ m r)
            mark (canonicalVstar W) X (n.val.val, b.val.val) := by
  have hV : Function.support (canonicalVstar W) ⊆ Set.Iic 2 :=
    canonicalVstar_support_upper W 2 (fun y hy => (hW (subset_closure hy)).2)
  rw [reopenedCanonical_eq_finite_of_le K Sset D θ m r _ mark (canonicalVstar W)
    X (8 * X) hX (by linarith) hV]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro b hb hnot
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hlong : T ≤ height K Sset b
  · have hcube : ¬ height K Sset b ^ 3 ≤ 2 * X := by
      intro h
      exact hnot (Finset.mem_filter.mpr ⟨hb, hlong, h⟩)
    have hz : canonicalCompletedTerm (exteriorGamma K Sset D)
        (canonicalTau K Sset D θ m r) mark (canonicalVstar W) X (n.val.val, b.val.val) = 0 := by
      by_contra hne
      exact hcube (canonicalCompletedTerm_cube_bound K Sset _ _ mark (canonicalVstar W)
        X hX hV n b hne)
    rw [hz, mul_zero]
  · rw [longCubeCoefficient_zero_of_norm_lt T b.val.val
      (nonZeroDivisors.coe_ne_zero b.val) (lt_of_not_ge hlong), zero_mul]

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
variable {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

def finiteValue (x : Node K S Γ Θ ψ σ) (P : Ideal (𝓞 K) → Prop)
    (B : Finset Ext) (f : Ext) (k : Ideal (𝓞 K) × Sector) : ℂ :=
  if hk : IsExterior K Sset k.1 then
    ∑ b ∈ B, ∑ n ∈ squarefreePool K Sset (8 * x.family.base ^ x.columnLength),
      reopenedCubeCoefficient P b.val.val *
        canonicalCompletedTerm (exteriorGamma K Sset D)
          (TerminalNodes.rowTau K S Γ D x f (exteriorOf K Sset k.1 hk) k.2)
          (TerminalNodes.mark K S Γ x) (canonicalVstar x.test)
          (x.family.base ^ x.columnLength) (n.val.val, b.val.val)
  else 0

def finiteEnergy (slotCap : ℕ) (x : Node K S Γ Θ ψ σ)
    (P : Ideal (𝓞 K) → Prop) (B : Finset Ext) : ℝ :=
  x.family.base ^ (-x.labelLength) *
    ∑ f ∈ ProviderChildParent.exteriorLabels K S x.labels, labelDivisorWeight slotCap f.val.val *
      ∑ k ∈ x.rows, ‖finiteValue K S D Γ x P B f k‖ ^ 2

theorem longValue_eq_finiteValue (x : Node K S Γ Θ ψ σ)
    (hbase : 0 < x.family.base) (hW : tsupport x.test ⊆ Set.Icc (1 : ℝ) 2)
    (T : ℝ) (f : Ext) (k : Ideal (𝓞 K) × Sector) :
    TerminalNodes.longValue K S Γ D x T f.val.val k =
      finiteValue K S D Γ x (fun H => T ≤ cubeIdealNorm H)
        (longPool K S (x.family.base ^ x.columnLength) T) f k := by
  rw [TerminalNodes.longValue, dif_pos (exterior_isExterior K Sset f)]
  by_cases hk : IsExterior K Sset k.1
  · rw [dif_pos hk, finiteValue, dif_pos hk]
    exact reopened_eq_longPool K S D (TerminalNodes.period K S Γ x)
      ((((Sset).unitEquivUnitsInteger K (CanonicalSectors.sectorUnit K Sset Γ k.2)).val *
        D.generator (exteriorOf K Sset k.1 hk)) * D.generator f ^ 4)
      x.puncture (TerminalNodes.mark K S Γ x) x.test (x.family.base ^ x.columnLength) T
      (Real.rpow_pos_of_pos hbase _) hW
  · simp only [hk, dif_neg, finiteValue]

theorem longEnergy_eq_finiteEnergy (slotCap : ℕ) (x : Node K S Γ Θ ψ σ)
    (hbase : 0 < x.family.base) (hW : tsupport x.test ⊆ Set.Icc (1 : ℝ) 2) (T : ℝ) :
    TerminalNodes.longEnergy K S Γ D slotCap x T =
      finiteEnergy K S D Γ slotCap x (fun H => T ≤ cubeIdealNorm H)
        (longPool K S (x.family.base ^ x.columnLength) T) := by
  unfold TerminalNodes.longEnergy finiteEnergy
  congr 1
  have hfilter :
      (∑ f ∈ x.labels.filter (IsExterior K Sset), labelDivisorWeight slotCap f *
        ∑ k ∈ x.rows, ‖TerminalNodes.longValue K S Γ D x T f k‖ ^ 2) =
      ∑ f ∈ x.labels, labelDivisorWeight slotCap f *
        ∑ k ∈ x.rows, ‖TerminalNodes.longValue K S Γ D x T f k‖ ^ 2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro f hf hnot
    have hbad : ¬ IsExterior K Sset f := fun he => hnot (Finset.mem_filter.mpr ⟨hf, he⟩)
    simp only [TerminalNodes.longValue, dif_neg hbad, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
      Finset.sum_const_zero, mul_zero]
  rw [← hfilter, ← ProviderChildParent.exteriorLabels_image K S x.labels,
    Finset.sum_image (fun _ _ _ _ h => (ProviderChildParent.labelEmbedding K S).injective h)]
  apply Finset.sum_congr rfl
  intro f hf
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [longValue_eq_finiteValue K S D Γ x hbase hW T f k]

/-- Exact square-root and divisor-cap restoration on every original
ideal/sector row; the nonexterior row has the same zero on both sides. -/
theorem finiteValue_eq_source (x : Node K S Γ Θ ψ σ)
    (hbase : 0 < x.family.base)
    (hΛ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K x.family.lambda p)
    (P : Ideal (𝓞 K) → Prop) (B : Finset Ext) (H : ℝ) (hH : 0 < H)
    (f : Ext) (k : Ideal (𝓞 K) × Sector) :
    finiteValue K S D Γ x P B f k =
      (sourceScale (CubeCompletionProvider.cubeIdeals K S B) H
        (x.family.base ^ x.columnLength) : ℂ) *
      CubeCompletionEnergy.source B
        (squarefreePool K Sset (8 * x.family.base ^ x.columnLength))
        (height K Sset) (height K Sset) (coefficients K S D Γ x P B H (f, k))
        x.test (x.family.base ^ x.columnLength) := by
  by_cases hk : IsExterior K Sset k.1
  · rw [finiteValue, dif_pos hk]
    have he := CubeCompletionProvider.reopened_sum_eq_source K S D
      (ProviderChildParent.columns K S x.family x.triple) hΛ P B
      (squarefreePool K Sset (8 * x.family.base ^ x.columnLength)) H
      (x.family.base ^ x.columnLength) hH (Real.rpow_pos_of_pos hbase _) f
      (fun n hn => squarefreePool_squarefree K Sset hn)
      (((Sset).unitEquivUnitsInteger K (CanonicalSectors.sectorUnit K Sset Γ k.2)).val *
        D.generator (exteriorOf K Sset k.1 hk)) x.test
    simpa only [TerminalNodes.rowTau, TerminalNodes.period, TerminalNodes.mark,
      coefficients, sectorRow, dif_pos hk, ProviderChildParent.columns] using he
  · simp only [finiteValue, dif_neg hk, coefficients, CubeCompletionEnergy.source,
      CubeCompletionProvider.arithmeticCoefficient, sectorRow, dif_neg hk,
      zero_pow (by decide : (3 : ℕ) ≠ 0), mul_zero, Finset.sum_const_zero]

theorem finiteEnergy_eq_sourceEnergy (slotCap : ℕ) (x : Node K S Γ Θ ψ σ)
    (hbase : 0 < x.family.base)
    (hΛ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K x.family.lambda p)
    (P : Ideal (𝓞 K) → Prop) (B : Finset Ext) (H : ℝ) (hH : 0 < H) :
    finiteEnergy K S D Γ slotCap x P B =
      x.family.base ^ (-x.labelLength) *
        sourceScale (CubeCompletionProvider.cubeIdeals K S B) H (x.family.base ^ x.columnLength) ^ 2 *
        CubeCompletionEnergy.sourceEnergy
          ((ProviderChildParent.exteriorLabels K S x.labels) ×ˢ x.rows)
          (fun fk => labelDivisorWeight slotCap fk.1.val.val)
          B (squarefreePool K Sset (8 * x.family.base ^ x.columnLength))
          (height K Sset) (height K Sset) (coefficients K S D Γ x P B H)
          x.test (x.family.base ^ x.columnLength) := by
  have hS := sourceScale_pos (CubeCompletionProvider.cubeIdeals K S B) H
    (x.family.base ^ x.columnLength) hH (Real.rpow_pos_of_pos hbase _)
  unfold finiteEnergy CubeCompletionEnergy.sourceEnergy
  simp_rw [finiteValue_eq_source K S D Γ x hbase hΛ P B H hH,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg hS.le, mul_pow]
  simp only [Finset.sum_product]
  rw [mul_assoc]
  congr 1
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem finiteValue_eq_blocks (x : Node K S Γ Θ ψ σ)
    (P : Ideal (𝓞 K) → Prop) (B : Finset Ext) (R : ℝ)
    (hR : ∀ b ∈ B, height K Sset b ≤ R)
    (f : Ext) (k : Ideal (𝓞 K) × Sector) :
    finiteValue K S D Γ x P B f k =
      ∑ j ∈ Finset.range (CubeCompletionBlocks.count R),
        finiteValue K S D Γ x P (CubeCompletionBlocks.block B (height K Sset) j) f k := by
  by_cases hk : IsExterior K Sset k.1
  · simp only [finiteValue, dif_pos hk]
    exact CubeCompletionBlocks.sum_eq_blocks B (height K Sset) R
      (fun b _ => height_one_le K Sset b) hR _
  · simp only [finiteValue, dif_neg hk, Finset.sum_const_zero]

theorem finiteEnergy_le_blocks (slotCap : ℕ) (x : Node K S Γ Θ ψ σ)
    (hbase : 0 ≤ x.family.base) (P : Ideal (𝓞 K) → Prop)
    (B : Finset Ext) (R : ℝ) (hR : ∀ b ∈ B, height K Sset b ≤ R) :
    finiteEnergy K S D Γ slotCap x P B ≤ (CubeCompletionBlocks.count R : ℝ) *
      ∑ j ∈ Finset.range (CubeCompletionBlocks.count R),
        finiteEnergy K S D Γ slotCap x P (CubeCompletionBlocks.block B (height K Sset) j) := by
  have hpoint (f : Ext) (k : Ideal (𝓞 K) × Sector) :
      ‖finiteValue K S D Γ x P B f k‖ ^ 2 ≤ (CubeCompletionBlocks.count R : ℝ) *
        ∑ j ∈ Finset.range (CubeCompletionBlocks.count R),
          ‖finiteValue K S D Γ x P (CubeCompletionBlocks.block B (height K Sset) j) f k‖ ^ 2 := by
    rw [finiteValue_eq_blocks K S D Γ x P B R hR f k]
    simpa only [one_mul, Finset.card_range] using
      HeckePort.Moments.bounded_finset_coefficient_sum_sq
        (Finset.range (CubeCompletionBlocks.count R)) (fun _ => (1 : ℂ))
        (fun j => finiteValue K S D Γ x P (CubeCompletionBlocks.block B (height K Sset) j) f k)
        (by simp)
  calc
    _ ≤ x.family.base ^ (-x.labelLength) *
        ∑ f ∈ ProviderChildParent.exteriorLabels K S x.labels, labelDivisorWeight slotCap f.val.val *
          ∑ k ∈ x.rows, (CubeCompletionBlocks.count R : ℝ) *
            ∑ j ∈ Finset.range (CubeCompletionBlocks.count R),
              ‖finiteValue K S D Γ x P (CubeCompletionBlocks.block B (height K Sset) j) f k‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hbase _)
      apply Finset.sum_le_sum
      intro f hf
      apply mul_le_mul_of_nonneg_left _ (labelDivisorWeight_nonneg slotCap _)
      exact Finset.sum_le_sum (fun k hk => hpoint f k)
    _ = _ := by
      unfold finiteEnergy
      simp_rw [Finset.mul_sum]
      conv_lhs =>
        arg 2
        ext f
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro f hf
      apply Finset.sum_congr rfl
      intro k hk
      ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionFinite
