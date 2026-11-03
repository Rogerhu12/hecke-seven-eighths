import ActualChoiceMaskClearedFiber
import ActualChosenDepthPoissonBound
import ActualWholeAnnularAllScalePoisson

/-!
UNCOMPILED / native 0. The literal generator-choice masks are frozen on
actual fine cleared residue fibers, then the genuine periodic estimate is
applied to each fiber. No mask is moved into the orbital test and no
arbitrary ideal coefficient is inserted. The original divisor remains
fixed; its active and compact normalized local data are explicit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualChoiceMaskedAnnularDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Arithmetic.AllowedGeneratorConstruction
open HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft
open AlgebraicNumberTheory.PowerResidueSymbols
open ActualGeneratorChoiceDraft ActualGramJointMeanDraft ActualGramJointChartDraft
open ActualGramJointChartCoverDraft ActualGramClearedColumnDraft ActualGramFamilyDraft
open ActualClearedPairReindexDraft ActualAnnularClearedResidueDraft ActualGramFixedDenominatorDraft
open ActualClearedJointPeriodicDraft ActualBalancedClearedJointDraft
open ActualChosenDepthPoissonDraft ActualWholeAnnularAllScaleDraft ActualMeanZeroProductPoissonDraft
open ActualTraceProductFourierDilationDraft
open scoped Classical BigOperators ContDiff nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (w : GeneratorMaskWitness K)
local notation "S" => (w.S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Γ" => sixthPowerUnits K S
local instance masked_sixthUnits_finiteIndex : Subgroup.FiniteIndex Γ :=
  sUnit_power_range_finiteIndex K S 6 (by decide)
local notation "OS" => Set.integer S K
local notation "NZ" => NonzeroRingElements OS
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Z" => SFiniteLocalGroup K S
local notation "D" => finiteSIntegerDenominator K S
local notation "H" => finiteIndexSUnitBoxWidth K S Γ
local notation "J" => choiceJointPrincipalDepth K w
local notation "L" => choiceClearedExtraDepth K w H
local notation "depth" => H + L
local notation:max "active" n:max => Prod.snd (sLocalNonzeroIntegerDiagonal K S n) ∈ finiteLocalValuationBox K S H

variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ (w.S : Set (HeightOneSpectrum (𝓞 K))))

local instance maskedResidueFinite : Finite (𝓞 K ⧸ clearedSModulus K S ζ hζ depth) :=
  Ring.HasFiniteQuotients.finiteQuotient (clearedSModulus_ne_zero K S ζ hζ depth)
local instance maskedResidueFintype : Fintype (𝓞 K ⧸ clearedSModulus K S ζ hζ depth) := Fintype.ofFinite _
local notation "Residue" => 𝓞 K ⧸ clearedSModulus K S ζ hζ depth

/-- The literal same-witness mask evaluated on the actual product d*m. -/
def choiceColumnMask (d m : NZ) : ℂ :=
  choiceFiniteMask K w (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m)).2

/-- The original arithmetic annular summand, with the two genuine masks. -/
def choiceMaskedAnnularSummand (c k d : NZ) (a : ℝ → ℝ) (r : ℝ)
    (joint : NZ × NZ → ℂ) (m : NZ × NZ) : ℂ :=
  choiceColumnMask K w d m.1 * choiceColumnMask K w d m.2 *
    annularOriginalSummand K S ζ hζ Γ σ hS6 c k d a a r r joint m

/-- Exact complete fine-residue decomposition of the MASKED original sum.
Summability and coverage are derived from the genuine annular support. -/
theorem tsum_choiceMaskedAnnular_eq_fine_residues (c k d : NZ)
    (hd : (sLocalNonzeroIntegerDiagonal K S d).2 ∈ finiteLocalValuationBox K S H)
    (a : ℝ → ℝ) (a0 b0 : ℝ) (ha0 : 0 < a0)
    (haSupport : tsupport a ⊆ Set.Icc a0 b0) (r : ℝ) (hr : r ≠ 0)
    (joint : NZ × NZ → ℂ) :
    let F := choiceMaskedAnnularSummand K w ζ hζ σ hS6 c k d a r joint
    Summable F ∧
      (∀ α β : Residue, Summable
        (clearedPairSummand K S ζ hζ H depth (Quotient.out α) (Quotient.out β) F)) ∧
      (∑' m, F m) = ∑ α : Residue, ∑ β : Residue, ∑' m : NZ × NZ,
        clearedPairSummand K S ζ hζ H depth (Quotient.out α) (Quotient.out β) F m := by
  let F := choiceMaskedAnnularSummand K w ζ hζ σ hS6 c k d a r joint
  let A := fun m : NZ => sIntegerAnnularColumn K S Γ a r (divisorColumn K S d m)
  have hs := finite_support_divisor_annularColumn K S Γ d a a0 b0 ha0 haSupport r hr
  let T : Finset (NZ × NZ) := hs.toFinset ×ˢ hs.toFinset
  have hzero (m : NZ × NZ) (hm : m ∉ T) : F m = 0 := by
    by_cases h₁ : A m.1 = 0
    · change sIntegerAnnularColumn K S Γ a r (divisorColumn K S d m.1) = 0 at h₁
      simp only [F, choiceMaskedAnnularSummand, annularOriginalSummand, h₁, Complex.ofReal_zero, mul_zero, zero_mul]
    by_cases h₂ : A m.2 = 0
    · change sIntegerAnnularColumn K S Γ a r (divisorColumn K S d m.2) = 0 at h₂
      simp only [F, choiceMaskedAnnularSummand, annularOriginalSummand, h₂, Complex.ofReal_zero, mul_zero, zero_mul]
    exact False.elim (hm (Finset.mem_product.mpr
      ⟨hs.mem_toFinset.mpr h₁, hs.mem_toFinset.mpr h₂⟩))
  have hfinite : (Function.support F).Finite := by
    apply T.finite_toSet.subset
    intro m hm
    by_contra hn
    exact hm (hzero m hn)
  have hfiberzero (α β : Residue) (m : NZ × NZ) (hm : m ∉ T) :
      clearedPairSummand K S ζ hζ H depth
        (Quotient.out α) (Quotient.out β) F m = 0 := by
    simp only [clearedPairSummand, hzero m hm, ite_self]
  refine ⟨summable_of_hasFiniteSupport hfinite, ?_, ?_⟩
  · intro α β
    apply summable_of_hasFiniteSupport
    apply T.finite_toSet.subset
    intro m hm
    by_contra hn
    exact hm (hfiberzero α β m hn)
  · have hpartition (m : NZ × NZ) :
        F m = ∑ α : Residue, ∑ β : Residue,
          clearedPairSummand K S ζ hζ H depth
            (Quotient.out α) (Quotient.out β) F m := by
      by_cases hF : F m = 0
      · simp [clearedPairSummand, hF]
      have hA₁ : A m.1 ≠ 0 := by
        intro hz
        change sIntegerAnnularColumn K S Γ a r (divisorColumn K S d m.1) = 0 at hz
        exact hF (by simp only [F, choiceMaskedAnnularSummand, annularOriginalSummand, hz, Complex.ofReal_zero,
          mul_zero, zero_mul])
      have hA₂ : A m.2 ≠ 0 := by
        intro hz
        change sIntegerAnnularColumn K S Γ a r (divisorColumn K S d m.2) = 0 at hz
        exact hF (by simp only [F, choiceMaskedAnnularSummand, annularOriginalSummand, hz, Complex.ofReal_zero,
          mul_zero, zero_mul])
      have hactive {n : NZ} (hn : sIntegerAnnularColumn K S Γ a r n ≠ 0) :
          (sLocalNonzeroIntegerDiagonal K S n).2 ∈ finiteLocalValuationBox K S H := by
        by_contra hnot
        exact hn (congrFun (sUnitAnnularPartitionCutoff_eq_zero_of_not_mem_box
          K S Γ a _ hnot) _)
      obtain ⟨z₁, hz₁⟩ := exactSDenominator_pow_clears_divisor_quotient
        K S H d m.1 hd (hactive hA₁)
      obtain ⟨z₂, hz₂⟩ := exactSDenominator_pow_clears_divisor_quotient
        K S H d m.2 hd (hactive hA₂)
      have hrewrite (α β : Residue) :
          clearedPairSummand K S ζ hζ H depth
            (Quotient.out α) (Quotient.out β) F m =
          if Ideal.Quotient.mk (clearedSModulus K S ζ hζ depth) z₁ = α ∧
             Ideal.Quotient.mk (clearedSModulus K S ζ hζ depth) z₂ = β then F m else 0 := by
        unfold clearedPairSummand
        rw [clearedColumnFiber_out_iff K S ζ hζ H depth m.1 z₁ hz₁ α,
          clearedColumnFiber_out_iff K S ζ hζ H depth m.2 z₂ hz₂ β]
      simp_rw [hrewrite]
      simp [ite_and]
    rw [tsum_eq_sum hzero]
    have hfib : ∀ α β : Residue, ∑' m : NZ × NZ,
        clearedPairSummand K S ζ hζ H depth (Quotient.out α) (Quotient.out β) F m =
        ∑ m ∈ T, clearedPairSummand K S ζ hζ H depth
          (Quotient.out α) (Quotient.out β) F m :=
      fun α β => tsum_eq_sum (hfiberzero α β)
    rw [Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun β _ => hfib α β))]
    calc
      _ = ∑ m ∈ T, ∑ α : Residue, ∑ β : Residue,
          clearedPairSummand K S ζ hζ H depth
            (Quotient.out α) (Quotient.out β) F m :=
        Finset.sum_congr rfl (fun m _ => hpartition m)
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro α _
        rw [Finset.sum_comm]


variable [MeasurableSpace (sLocalNormOneGroup K (w.S : Set (HeightOneSpectrum (𝓞 K))))] [BorelSpace (sLocalNormOneGroup K (w.S : Set (HeightOneSpectrum (𝓞 K))))]
variable (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
  (a0 b0 : ℝ) (ha0 : 0 < a0) (haSupport : tsupport a ⊆ Set.Icc a0 b0)
  (ψ : ((v : (w.S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
  (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)

/-- Both actual masks multiply the literal original joint summand. -/
def choiceMaskedActualAnnularJointSummand (c k d : NZ) (ν : ℝ)
    (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) (N : ℝ) : NZ × NZ → ℂ :=
  let r := traceNormScale K N
  choiceMaskedAnnularSummand K w ζ hζ σ hS6 c k d a r
    (fun m => originalJointFactor K S ψ d ν
      (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m.1)).2
      (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m.2)).2 φ R r m)

private theorem norm_choiceColumnMask_le_one (d m : NZ) :
    ‖choiceColumnMask K w d m‖ ≤ 1 := by
  unfold choiceColumnMask choiceFiniteMask
  split_ifs <;> simp

private theorem norm_choiceColumnMask_product_le_one (d m₁ m₂ : NZ) :
    ‖choiceColumnMask K w d m₁ * choiceColumnMask K w d m₂‖ ≤ 1 := by
  rw [norm_mul]
  calc
    _ ≤ 1 * 1 := mul_le_mul (norm_choiceColumnMask_le_one K w d m₁)
      (norm_choiceColumnMask_le_one K w d m₂) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

private theorem fixedBoxJointSeminormSum_nonneg (s : Finset (ℕ × ℕ))
    (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) :
    0 ≤ fixedBoxJointSeminormSum K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport s ν φ R := by
  apply Finset.sum_nonneg
  intro e₁ _
  exact Finset.sum_nonneg (fun e₂ _ => apply_nonneg _ _)

private theorem jointSchwartz_eq_of_orders_eq (ν : ℝ) (z₁ z₂ w₁ w₂ : Z)
    (h₁ : ∀ v : S, localOrderHom K v.val (z₁ v) = localOrderHom K v.val (w₁ v))
    (h₂ : ∀ v : S, localOrderHom K v.val (z₂ v) = localOrderHom K v.val (w₂ v))
    (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) :
    sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
        ψ hψ hψsupport ν z₁ z₂ φ R =
      sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
        ψ hψ hψsupport ν w₁ w₂ φ R := by
  ext p
  rw [sUnitMellinAnnularPartitionJointSchwartz_apply,
    sUnitMellinAnnularPartitionJointSchwartz_apply]
  unfold sUnitMellinPhase sUnitAnnularPartitionJointCutoff
  rw [sFiniteProductNorm_eq_of_orders_eq K S z₁ w₁ h₁,
    sFiniteProductNorm_eq_of_orders_eq K S z₂ w₂ h₂,
    sUnitAnnularPartitionCutoff_eq_of_orders_eq K S Γ a z₁ w₁ h₁,
    sUnitAnnularPartitionCutoff_eq_of_orders_eq K S Γ a z₂ w₂ h₂]

private theorem jointSeminorm_le_fixedBoxSum (s : Finset (ℕ × ℕ))
    (ν : ℝ) (z₁ z₂ : Z)
    (h₁ : z₁ ∈ finiteLocalValuationBox K S H)
    (h₂ : z₂ ∈ finiteLocalValuationBox K S H)
    (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) :
    s.sup (schwartzSeminormFamily ℝ (V × V) ℂ)
        (sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
          ψ hψ hψsupport ν z₁ z₂ φ R) ≤
      fixedBoxJointSeminormSum K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport s ν φ R := by
  obtain ⟨e₁, he₁⟩ := exists_sUnitPartitionFiniteFibreRepresentative K S H z₁ h₁
  obtain ⟨e₂, he₂⟩ := exists_sUnitPartitionFiniteFibreRepresentative K S H z₂ h₂
  rw [jointSchwartz_eq_of_orders_eq K w a ha a0 b0 ha0 haSupport ψ hψ hψsupport
    ν z₁ z₂ _ _ he₁ he₂ φ R]
  let g : (S → Fin H) → (S → Fin H) → ℝ := fun f₁ f₂ =>
    s.sup (schwartzSeminormFamily ℝ (V × V) ℂ)
      (sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
        ψ hψ hψsupport ν (sUnitPartitionFiniteFibreRepresentative K S H f₁)
        (sUnitPartitionFiniteFibreRepresentative K S H f₂) φ R)
  have hg : ∀ f₁ f₂, 0 ≤ g f₁ f₂ := fun f₁ f₂ => apply_nonneg _ _
  have step1 : g e₁ e₂ ≤ ∑ f₂, g e₁ f₂ :=
    Finset.single_le_sum (f := g e₁) (fun f₂ _ => hg e₁ f₂) (Finset.mem_univ e₂)
  have step2 : ∑ f₂, g e₁ f₂ ≤ ∑ f₁, ∑ f₂, g f₁ f₂ :=
    Finset.single_le_sum (f := fun f₁ => ∑ f₂, g f₁ f₂)
      (fun f₁ _ => Finset.sum_nonneg (fun f₂ _ => hg f₁ f₂)) (Finset.mem_univ e₁)
  exact step1.trans step2

private theorem finiteNorm_eq_of_fixedSChart (n base : NZ)
    (hn : n ∈ fixedSChart K S ζ hζ base) (hb : active base) :
    sFiniteProductNorm K S (sLocalNonzeroIntegerDiagonal K S n).2 =
      sFiniteProductNorm K S (sLocalNonzeroIntegerDiagonal K S base).2 := by
  obtain ⟨t, ht, he⟩ := hn
  have hreverse : base.val - n.val = algebraMap (𝓞 K) OS (-t) := by
    rw [map_neg, ← he, neg_sub]
  have ho := sIntegerAnnular_active_orders_eq K S Γ base n (-t) hreverse
    (fun v => (v.val.asIdeal).neg_mem (correctionModulus_le_prime K S ζ hζ v ht)) hb
  exact (sFiniteProductNorm_eq_of_orders_eq K S _ _ ho).symm


private theorem fineFiber_congr (x y : 𝓞 K)
    (he : Ideal.Quotient.mk (clearedSModulus K S ζ hζ depth) x =
      Ideal.Quotient.mk (clearedSModulus K S ζ hζ depth) y) (m : NZ) :
    clearedColumnFiber K S ζ hζ H depth x m ↔ clearedColumnFiber K S ζ hζ H depth y m := by
  constructor
  · rintro ⟨z, hz, hmem⟩
    exact ⟨z, hz, Ideal.Quotient.eq.mp ((Ideal.Quotient.eq.mpr hmem).trans he)⟩
  · rintro ⟨z, hz, hmem⟩
    exact ⟨z, hz, Ideal.Quotient.eq.mp ((Ideal.Quotient.eq.mpr hmem).trans he.symm)⟩

/-- L is fixed and at least H. The SAME divisor is cleared at L by
multiplying its genuine H-clearing coordinate by D^J. -/
private theorem lift_divisor_clearing (d : NZ) (b : 𝓞 K)
    (hd : algebraMap (𝓞 K) OS (D ^ H) * d.val = algebraMap (𝓞 K) OS b) :
    algebraMap (𝓞 K) OS (D ^ L) * d.val = algebraMap (𝓞 K) OS (D ^ J * b) := by
  change algebraMap (𝓞 K) OS (D ^ (H + J)) * d.val = _
  calc
    _ = algebraMap (𝓞 K) OS (D ^ J) *
        (algebraMap (𝓞 K) OS (D ^ H) * d.val) := by
      rw [pow_add, map_mul]
      ring
    _ = _ := by rw [hd, map_mul]

/-- On each complete fine fiber, the two masks are actual constants of
norm at most one and the finite Mellin coordinates are the actual center's. -/
theorem choiceMaskedFiber_eq_constant_centerFiber
    (c k d m₀₁ m₀₂ : NZ) (b z₀₁ z₀₂ : 𝓞 K)
    (hd : algebraMap (𝓞 K) OS (D ^ H) * d.val = algebraMap (𝓞 K) OS b)
    (h₀₁ : algebraMap (𝓞 K) OS (D ^ H) * m₀₁.val = algebraMap (𝓞 K) OS z₀₁)
    (h₀₂ : algebraMap (𝓞 K) OS (D ^ H) * m₀₂.val = algebraMap (𝓞 K) OS z₀₂)
    (hb₁ : active (divisorColumn K S d m₀₁)) (hb₂ : active (divisorColumn K S d m₀₂))
    (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) (N : ℝ) :
    clearedPairSummand K S ζ hζ H depth z₀₁ z₀₂
      (choiceMaskedActualAnnularJointSummand K w ζ hζ σ hS6 a ψ c k d ν φ R N) =
    fun m => (choiceColumnMask K w d m₀₁ * choiceColumnMask K w d m₀₂) *
      clearedPairSummand K S ζ hζ H depth z₀₁ z₀₂
        (annularOriginalSummand K S ζ hζ Γ σ hS6 c k d a a
          (traceNormScale K N) (traceNormScale K N)
          (originalJointFactor K S ψ d ν
            (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₀₁)).2
            (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₀₂)).2
            φ R (traceNormScale K N))) m := by
  have hdL := lift_divisor_clearing K w d b hd
  funext m
  by_cases hm : clearedColumnFiber K S ζ hζ H depth z₀₁ m.1 ∧
      clearedColumnFiber K S ζ hζ H depth z₀₂ m.2
  · have hmask₁ : choiceColumnMask K w d m.1 = choiceColumnMask K w d m₀₁ :=
      choiceFiniteMask_divisorColumn_eq_on_clearedFiber K w ζ hζ H d m₀₁ m.1 b z₀₁
        hd h₀₁ hb₁ hm.1
    have hmask₂ : choiceColumnMask K w d m.2 = choiceColumnMask K w d m₀₂ :=
      choiceFiniteMask_divisorColumn_eq_on_clearedFiber K w ζ hζ H d m₀₂ m.2 b z₀₂
        hd h₀₂ hb₂ hm.2
    obtain ⟨z₁, h₁, hz₁⟩ := hm.1
    obtain ⟨z₂, h₂, hz₂⟩ := hm.2
    have hn₁ := finiteNorm_eq_of_fixedSChart (K := K) (w := w) (ζ := ζ) (hζ := hζ) _ _
      (divisorColumn_chart_of_cleared_congruence K S ζ hζ H L d m.1 m₀₁
        (D ^ J * b) z₁ z₀₁ hdL h₁ h₀₁ hz₁) hb₁
    have hn₂ := finiteNorm_eq_of_fixedSChart (K := K) (w := w) (ζ := ζ) (hζ := hζ) _ _
      (divisorColumn_chart_of_cleared_congruence K S ζ hζ H L d m.2 m₀₂
        (D ^ J * b) z₂ z₀₂ hdL h₂ h₀₂ hz₂) hb₂
    simp only [clearedPairSummand, if_pos hm, choiceMaskedActualAnnularJointSummand,
      choiceMaskedAnnularSummand, annularOriginalSummand, originalJointFactor,
      sUnitMellinPhase, hn₁, hn₂, hmask₁, hmask₂]
  · simp only [clearedPairSummand, if_neg hm, mul_zero]

/-- Complete masked min-saving for the SAME active compact divisor.
Constants and the finite set of original profile seminorms precede d,c,k
and all moving analytic data. The two genuine nonexceptional conditions
are retained. Compact normalized divisor data are not inferred from its
finite-place active condition. -/
theorem exists_choiceMasked_whole_annular_allScale_min_bound (A : ℕ) (hA : 2 < A) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ d : NZ,
      normalizedDivisorLocalPoint K S d ∈ sUnitCompactRepresentativeSet K S Γ →
      active d → ∀ (c k : NZ)
      (p : jointPlaces K (actualFrequencyIdeal K S c) (actualFrequencyIdeal K S k)
        (actualFrequencyIdeal_ne_zero K S c) (actualFrequencyIdeal_ne_zero K S k)),
      (¬ p.val.asIdeal ∣ actualFrequencyIdeal K S c) →
      (¬ 6 ∣ idealPrimeMultiplicity K p.val (actualFrequencyIdeal K S k)) →
      ∀ (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) (N : ℝ), 0 < N →
      ‖∑' m, choiceMaskedActualAnnularJointSummand K w ζ hζ σ hS6 a ψ c k d ν φ R N m‖ ≤
        C * (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
          fixedBoxJointSeminormSum K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport s ν φ R *
          (N / (sIntegerElementNorm K S d).val) ^ 2 *
          min 1 ((((Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
            (Ideal.absNorm (actualFrequencyIdeal K S k) : ℝ)) /
              (N / (sIntegerElementNorm K S d).val)) ^ A) := by
  obtain ⟨s, C₀, hC₀, hbound⟩ := exists_balancedJoint_chosenDepth_allScale_min_bound
    K S Γ ζ hζ σ hS6 a ha a0 b0 ha0 haSupport ψ hψ hψsupport depth H A hA
  let n : ℝ := Fintype.card Residue
  have hn : 0 < n := by
    have h : (0 : ℝ) < ((Fintype.card Residue : ℕ) : ℝ) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Residue)
    exact h
  refine ⟨s, C₀ * n ^ 2, mul_pos hC₀ (sq_pos_of_pos hn), ?_⟩
  intro d hcompact hd c k p hpC hpJ ν φ R N hN
  let F := choiceMaskedActualAnnularJointSummand K w ζ hζ σ hS6 a ψ c k d ν φ R N
  let r := traceNormScale K N
  let q := N / (sIntegerElementNorm K S d).val
  let B := C₀ * (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
    fixedBoxJointSeminormSum K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport s ν φ R *
    q ^ 2 * min 1 ((((Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
      (Ideal.absNorm (actualFrequencyIdeal K S k) : ℝ)) / q) ^ A)
  have hq : 0 < q := div_pos hN (sIntegerElementNorm K S d).property
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (mul_nonneg hC₀.le (Nat.cast_nonneg _))
        (fixedBoxJointSeminormSum_nonneg (K := K) (w := w)
          (a := a) (ha := ha) (a0 := a0) (b0 := b0) (ha0 := ha0)
          (haSupport := haSupport) (ψ := ψ) (hψ := hψ) (hψsupport := hψsupport) s ν φ R))
      (sq_nonneg q)) (by positivity)
  have hfiber (α β : Residue) :
      ‖∑' m, clearedPairSummand K S ζ hζ H depth
        (Quotient.out α) (Quotient.out β) F m‖ ≤ B := by
    by_cases hz : ∀ m : NZ × NZ, clearedPairSummand K S ζ hζ H depth
        (Quotient.out α) (Quotient.out β) F m = 0
    · simpa only [hz, tsum_zero, norm_zero] using hB
    push_neg at hz
    obtain ⟨m₀, hm₀⟩ := hz
    have hmem : clearedColumnFiber K S ζ hζ H depth (Quotient.out α) m₀.1 ∧
        clearedColumnFiber K S ζ hζ H depth (Quotient.out β) m₀.2 := by
      by_contra h
      exact hm₀ (by simp only [clearedPairSummand, if_neg h])
    have hF : F m₀ ≠ 0 := by
      simpa only [clearedPairSummand, if_pos hmem] using hm₀
    have hactive {m : NZ} (hm : sIntegerAnnularColumn K S Γ a r
        (divisorColumn K S d m) ≠ 0) : active (divisorColumn K S d m) := by
      by_contra h
      exact hm (congrFun (sUnitAnnularPartitionCutoff_eq_zero_of_not_mem_box K S Γ a _ h) _)
    have hb₁ : active (divisorColumn K S d m₀.1) := by
      apply hactive
      intro hz₁
      exact hF (by simp only [F, choiceMaskedActualAnnularJointSummand,
        choiceMaskedAnnularSummand, annularOriginalSummand,
        r, hz₁, Complex.ofReal_zero, mul_zero, zero_mul])
    have hb₂ : active (divisorColumn K S d m₀.2) := by
      apply hactive
      intro hz₂
      exact hF (by simp only [F, choiceMaskedActualAnnularJointSummand,
        choiceMaskedAnnularSummand, annularOriginalSummand,
        r, hz₂, Complex.ofReal_zero, mul_zero, zero_mul])
    obtain ⟨b, z₀₁, z₀₂, hdb, h₀₁, h₀₂⟩ := fixed_clearing_triple K S H d m₀.1 m₀.2 hd hb₁ hb₂
    have hα : Ideal.Quotient.mk (clearedSModulus K S ζ hζ depth) z₀₁ = α :=
      (clearedColumnFiber_out_iff K S ζ hζ H depth m₀.1 z₀₁ h₀₁ α).mp hmem.1
    have hβ : Ideal.Quotient.mk (clearedSModulus K S ζ hζ depth) z₀₂ = β :=
      (clearedColumnFiber_out_iff K S ζ hζ H depth m₀.2 z₀₂ h₀₂ β).mp hmem.2
    have hreplace : clearedPairSummand K S ζ hζ H depth
        (Quotient.out α) (Quotient.out β) F =
        clearedPairSummand K S ζ hζ H depth z₀₁ z₀₂ F := by
      funext m
      unfold clearedPairSummand
      rw [fineFiber_congr (K := K) (w := w) (ζ := ζ) (hζ := hζ) (Quotient.out α) z₀₁
          ((Ideal.Quotient.mk_out α).trans hα.symm) m.1,
        fineFiber_congr (K := K) (w := w) (ζ := ζ) (hζ := hζ) (Quotient.out β) z₀₂
          ((Ideal.Quotient.mk_out β).trans hβ.symm) m.2]
    rw [hreplace]
    change ‖∑' m, clearedPairSummand K S ζ hζ H depth z₀₁ z₀₂
      (choiceMaskedActualAnnularJointSummand K w ζ hζ σ hS6 a ψ c k d ν φ R N) m‖ ≤ B
    rw [choiceMaskedFiber_eq_constant_centerFiber
      (K := K) (w := w) (ζ := ζ) (hζ := hζ) (σ := σ) (hS6 := hS6) (a := a) (ψ := ψ)
      c k d m₀.1 m₀.2 b z₀₁ z₀₂ hdb h₀₁ h₀₂ hb₁ hb₂ ν φ R N, tsum_mul_left, norm_mul]
    calc
      _ ≤ ‖∑' m, clearedPairSummand K S ζ hζ H depth z₀₁ z₀₂
          (annularOriginalSummand K S ζ hζ Γ σ hS6 c k d a a r r
            (originalJointFactor K S ψ d ν
              (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₀.1)).2
              (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₀.2)).2 φ R r)) m‖ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (norm_choiceColumnMask_product_le_one K w d m₀.1 m₀.2) (norm_nonneg _)
      _ ≤ B := by
        have hdL := lift_divisor_clearing K w d b hdb
        rw [tsum_cleared_original_joint_eq_productPeriodicSum K S Γ
          a ha a0 b0 ha0 haSupport ψ hψ hψsupport ζ hζ σ hS6
          c k d m₀.1 m₀.2 H L (D ^ J * b) z₀₁ z₀₂ hdL h₀₁ h₀₂ hb₁ hb₂ ν φ R N]
        rw [productPeriodicSum_cleared_eq_balanced K S Γ a ha a0 b0 ha0 haSupport
          ψ hψ hψsupport _ _ H d ν _ _ φ R N hN]
        have hb := hbound c k (Ideal.Quotient.mk _ z₀₁) (Ideal.Quotient.mk _ z₀₂)
          d (divisorColumn K S d m₀.1) (divisorColumn K S d m₀.2) p hpC hpJ
          (normalizedDivisorLocalPoint K S d) hcompact ν
          (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₀.1)).2
          (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₀.2)).2 φ R q hq
        have hs := jointSeminorm_le_fixedBoxSum
          (K := K) (w := w) (a := a) (ha := ha) (a0 := a0) (b0 := b0)
          (ha0 := ha0) (haSupport := haSupport) (ψ := ψ) (hψ := hψ) (hψsupport := hψsupport)
          s ν (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₀.1)).2
          (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₀.2)).2 hb₁ hb₂ φ R
        exact hb.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hs (mul_nonneg hC₀.le (Nat.cast_nonneg _)))
              (sq_nonneg q)) (by positivity))
  have hdecomp := tsum_choiceMaskedAnnular_eq_fine_residues K w ζ hζ σ hS6
    c k d hd a a0 b0 ha0 haSupport r (traceNormScale_pos K N hN).ne'
      (fun m => originalJointFactor K S ψ d ν
        (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m.1)).2
        (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m.2)).2 φ R r m)
  have hwhole : (∑' m, F m) = ∑ α : Residue, ∑ β : Residue, ∑' m,
      clearedPairSummand K S ζ hζ H depth
        (Quotient.out α) (Quotient.out β) F m := hdecomp.2.2
  change ‖∑' m, F m‖ ≤ _
  rw [hwhole]
  calc
    _ ≤ ∑ α : Residue, ∑ β : Residue,
        ‖∑' m, clearedPairSummand K S ζ hζ H depth
          (Quotient.out α) (Quotient.out β) F m‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun α _ => norm_sum_le _ _))
    _ ≤ ∑ _α : Residue, ∑ _β : Residue, B :=
      Finset.sum_le_sum (fun α _ => Finset.sum_le_sum (fun β _ => hfiber α β))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp only [B, q, n]
      ring

end HeckeGeneral.ThetaSkeleton.Physical.ActualChoiceMaskedAnnularDraft

