import ActualAnnularClearedResidueDecomposition
import ActualBalancedJointAllScalePoisson

/-!
UNCOMPILED / native 0. A whole-annular consumer of the actual complete
cleared-residue decomposition and balanced periodic Poisson estimate.
The original coefficient, subgroup, two annular masks and unsplit orbital
kernel are literal. The finite Mellin coordinates are those of each actual
column, and are frozen on a fiber by proved equality of local orders.

The fixed finite box contributes a finite sum of original joint-profile
seminorms. The fixed number of ordinary residue pairs is absorbed in the
constant. No fiber estimate, Gram estimate, convergence, finite-ray
cancellation or arbitrary ideal-coefficient hypothesis is supplied.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeGeneral.Analysis.ActualWholeAnnularAllScaleDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open AlgebraicNumberTheory.PowerResidueSymbols
open ActualGramJointMeanDraft ActualGramJointChartDraft ActualGramJointChartCoverDraft
open ActualGramClearedColumnDraft ActualGramFamilyDraft ActualClearedPairReindexDraft
open ActualAnnularClearedResidueDraft ActualGramFixedDenominatorDraft
open ActualClearedJointPeriodicDraft ActualBalancedClearedJointDraft
open ActualBalancedJointAllScaleDraft ActualMeanZeroProductPoissonDraft ActualTraceProductFourierDilationDraft
open scoped Classical BigOperators ContDiff nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
local notation "OS" => S.integer K
local notation "NZ" => NonzeroRingElements OS
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Z" => SFiniteLocalGroup K S
local notation "D" => finiteSIntegerDenominator K S
local notation "H" => finiteIndexSUnitBoxWidth K S Γ
local notation:max "active" n:max =>
  Prod.snd (sLocalNonzeroIntegerDiagonal K S n) ∈ finiteLocalValuationBox K S H

variable (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
  (a0 b0 : ℝ) (ha0 : 0 < a0) (haSupport : tsupport a ⊆ Set.Icc a0 b0)
  (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
  (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)

/-- The actual whole summand: its Mellin phase uses each column's own
finite coordinate; the two-column orbital kernel is not split. -/
def actualAnnularJointSummand (c k d : NZ) (ν : ℝ) (φ : SchwartzMap V ℂ)
    (R : {r : ℝ // 0 < r}) (N : ℝ) : NZ × NZ → ℂ :=
  let r := traceNormScale K N
  annularOriginalSummand K S ζ hζ Γ σ hS6 c k d a a r r
    (fun m => originalJointFactor K S ψ d ν
      (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m.1)).2
      (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m.2)).2 φ R r m)

/-- A fixed finite collection of the ORIGINAL joint-profile seminorms.
It retains nu, the orbital pair radius and all original finite fibers. -/
def fixedBoxJointSeminormSum (s : Finset (ℕ × ℕ))
    (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) : ℝ :=
  ∑ e₁ : S → Fin H, ∑ e₂ : S → Fin H,
    s.sup (schwartzSeminormFamily ℝ (V × V) ℂ)
      (sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
        ψ hψ hψsupport ν (sUnitPartitionFiniteFibreRepresentative K S H e₁)
        (sUnitPartitionFiniteFibreRepresentative K S H e₂) φ R)

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
  rw [jointSchwartz_eq_of_orders_eq K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport
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

private theorem clearedColumnFiber_congr (M L : ℕ) (x y : 𝓞 K)
    (he : Ideal.Quotient.mk (clearedSModulus K S ζ hζ L) x =
      Ideal.Quotient.mk (clearedSModulus K S ζ hζ L) y) (m : NZ) :
    clearedColumnFiber K S ζ hζ M L x m ↔ clearedColumnFiber K S ζ hζ M L y m := by
  constructor
  · rintro ⟨z, hz, hmem⟩
    exact ⟨z, hz, Ideal.Quotient.eq.mp ((Ideal.Quotient.eq.mpr hmem).trans he)⟩
  · rintro ⟨z, hz, hmem⟩
    exact ⟨z, hz, Ideal.Quotient.eq.mp ((Ideal.Quotient.eq.mpr hmem).trans he.symm)⟩

/-- Within a real complete fiber, the whole actual summand equals the
same literal summand with its finite Mellin coordinates frozen at an
active actual center. This uses norms of the proved local orders. -/
private theorem actualFiber_eq_centerFiber
    (c k d m₀₁ m₀₂ : NZ) (b z₀₁ z₀₂ : 𝓞 K)
    (hd : algebraMap (𝓞 K) OS (D ^ H) * d.val = algebraMap (𝓞 K) OS b)
    (h₀₁ : algebraMap (𝓞 K) OS (D ^ H) * m₀₁.val = algebraMap (𝓞 K) OS z₀₁)
    (h₀₂ : algebraMap (𝓞 K) OS (D ^ H) * m₀₂.val = algebraMap (𝓞 K) OS z₀₂)
    (hb₁ : active (divisorColumn K S d m₀₁)) (hb₂ : active (divisorColumn K S d m₀₂))
    (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) (N : ℝ) :
    clearedPairSummand K S ζ hζ H (H + H) z₀₁ z₀₂
      (actualAnnularJointSummand K S Γ a ψ ζ hζ σ hS6 c k d ν φ R N) =
    clearedPairSummand K S ζ hζ H (H + H) z₀₁ z₀₂
      (annularOriginalSummand K S ζ hζ Γ σ hS6 c k d a a
        (traceNormScale K N) (traceNormScale K N)
        (originalJointFactor K S ψ d ν
          (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₀₁)).2
          (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₀₂)).2
          φ R (traceNormScale K N))) := by
  funext m
  unfold clearedPairSummand
  split_ifs with hm
  · obtain ⟨z₁, h₁, hz₁⟩ := hm.1
    obtain ⟨z₂, h₂, hz₂⟩ := hm.2
    have hn₁ := finiteNorm_eq_of_fixedSChart K S Γ ζ hζ _ _
      (divisorColumn_chart_of_cleared_congruence K S ζ hζ H H d m.1 m₀₁
        b z₁ z₀₁ hd h₁ h₀₁ hz₁) hb₁
    have hn₂ := finiteNorm_eq_of_fixedSChart K S Γ ζ hζ _ _
      (divisorColumn_chart_of_cleared_congruence K S ζ hζ H H d m.2 m₀₂
        b z₂ z₀₂ hd h₂ h₀₂ hz₂) hb₂
    simp only [actualAnnularJointSummand, annularOriginalSummand, originalJointFactor,
      sUnitMellinPhase, hn₁, hn₂]
  · rfl

local instance clearedResidueFinite :
    Finite (𝓞 K ⧸ clearedSModulus K S ζ hζ (H + H)) :=
  Ring.HasFiniteQuotients.finiteQuotient (clearedSModulus_ne_zero K S ζ hζ (H + H))
local instance clearedResidueFintype :
    Fintype (𝓞 K ⧸ clearedSModulus K S ζ hζ (H + H)) := Fintype.ofFinite _
local notation "Residue" => 𝓞 K ⧸ clearedSModulus K S ζ hζ (H + H)

/-- Whole actual annular min-saving, after choosing the same original
Gamma representative for the divisor. Constants precede every moving
ideal/frequency/chart/scale; the original profile seminorms remain visible.
The two nonexceptional-prime conditions are not dropped. -/
theorem exists_whole_annular_fixedDepth_allScale_min_bound (A : ℕ) (hA : 2 < A) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ d : NZ,
      ∃ u : Γ, let d' := sIntegerOrbitTranslate K S Γ u d
      normalizedDivisorLocalPoint K S d' ∈ sUnitCompactRepresentativeSet K S Γ ∧
      active d' ∧ ∀ (c k : NZ)
      (p : jointPlaces K (actualFrequencyIdeal K S c) (actualFrequencyIdeal K S k)
        (actualFrequencyIdeal_ne_zero K S c) (actualFrequencyIdeal_ne_zero K S k)),
      (¬ p.val.asIdeal ∣ actualFrequencyIdeal K S c) →
      (¬ 6 ∣ idealPrimeMultiplicity K p.val (actualFrequencyIdeal K S k)) →
      ∀ (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) (N : ℝ), 0 < N →
      ‖∑' m, actualAnnularJointSummand K S Γ a ψ ζ hζ σ hS6 c k d' ν φ R N m‖ ≤
        C * (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
          fixedBoxJointSeminormSum K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport s ν φ R *
          (N / (sIntegerElementNorm K S d').val) ^ 2 *
          min 1 ((((Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
            (Ideal.absNorm (actualFrequencyIdeal K S k) : ℝ)) /
              (N / (sIntegerElementNorm K S d').val)) ^ A) := by
  obtain ⟨s, C₀, hC₀, hbound⟩ := exists_balancedJoint_fixedDepth_allScale_min_bound
    K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport ζ hζ σ hS6 A hA
  let n : ℝ := Fintype.card Residue
  have hn : 0 < n := by
    have h : (0 : ℝ) < ((Fintype.card Residue : ℕ) : ℝ) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Residue)
    exact h
  refine ⟨s, C₀ * n ^ 2, mul_pos hC₀ (sq_pos_of_pos hn), ?_⟩
  intro d
  obtain ⟨u, hu, hd, _, _⟩ := exists_compact_divisor_with_fixed_denominator K S Γ d
  let d' := sIntegerOrbitTranslate K S Γ u d
  refine ⟨u, hu, hd, ?_⟩
  intro c k p hpC hpJ ν φ R N hN
  let F := actualAnnularJointSummand K S Γ a ψ ζ hζ σ hS6 c k d' ν φ R N
  let r := traceNormScale K N
  let q := N / (sIntegerElementNorm K S d').val
  let B := C₀ * (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
    fixedBoxJointSeminormSum K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport s ν φ R *
    q ^ 2 * min 1 ((((Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
      (Ideal.absNorm (actualFrequencyIdeal K S k) : ℝ)) / q) ^ A)
  have hq : 0 < q := div_pos hN (sIntegerElementNorm K S d').property
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (mul_nonneg hC₀.le (Nat.cast_nonneg _))
        (fixedBoxJointSeminormSum_nonneg K S Γ a ha a0 b0 ha0 haSupport
          ψ hψ hψsupport s ν φ R)) (sq_nonneg q)) (by positivity)
  have hfiber (α β : Residue) :
      ‖∑' m, clearedPairSummand K S ζ hζ H (H + H)
        (Quotient.out α) (Quotient.out β) F m‖ ≤ B := by
    by_cases hz : ∀ m : NZ × NZ, clearedPairSummand K S ζ hζ H (H + H)
        (Quotient.out α) (Quotient.out β) F m = 0
    · simpa only [hz, tsum_zero, norm_zero] using hB
    push_neg at hz
    obtain ⟨m₀, hm₀⟩ := hz
    have hmem : clearedColumnFiber K S ζ hζ H (H + H) (Quotient.out α) m₀.1 ∧
        clearedColumnFiber K S ζ hζ H (H + H) (Quotient.out β) m₀.2 := by
      by_contra h
      exact hm₀ (by simp only [clearedPairSummand, if_neg h])
    have hF : F m₀ ≠ 0 := by
      simpa only [clearedPairSummand, if_pos hmem] using hm₀
    have hactive {m : NZ} (hm : sIntegerAnnularColumn K S Γ a r
        (divisorColumn K S d' m) ≠ 0) : active (divisorColumn K S d' m) := by
      by_contra h
      exact hm (congrFun (sUnitAnnularPartitionCutoff_eq_zero_of_not_mem_box K S Γ a _ h) _)
    have hb₁ : active (divisorColumn K S d' m₀.1) := by
      apply hactive
      intro hz₁
      exact hF (by simp only [F, actualAnnularJointSummand, annularOriginalSummand,
        r, hz₁, Complex.ofReal_zero, mul_zero, zero_mul])
    have hb₂ : active (divisorColumn K S d' m₀.2) := by
      apply hactive
      intro hz₂
      exact hF (by simp only [F, actualAnnularJointSummand, annularOriginalSummand,
        r, hz₂, Complex.ofReal_zero, mul_zero, zero_mul])
    obtain ⟨b, z₀₁, z₀₂, hdb, h₀₁, h₀₂⟩ := fixed_clearing_triple K S H d' m₀.1 m₀.2 hd hb₁ hb₂
    have hα : Ideal.Quotient.mk (clearedSModulus K S ζ hζ (H + H)) z₀₁ = α :=
      (clearedColumnFiber_out_iff K S ζ hζ H (H + H) m₀.1 z₀₁ h₀₁ α).mp hmem.1
    have hβ : Ideal.Quotient.mk (clearedSModulus K S ζ hζ (H + H)) z₀₂ = β :=
      (clearedColumnFiber_out_iff K S ζ hζ H (H + H) m₀.2 z₀₂ h₀₂ β).mp hmem.2
    have hreplace : clearedPairSummand K S ζ hζ H (H + H)
        (Quotient.out α) (Quotient.out β) F =
        clearedPairSummand K S ζ hζ H (H + H) z₀₁ z₀₂ F := by
      funext m
      unfold clearedPairSummand
      rw [clearedColumnFiber_congr K S ζ hζ H (H + H) (Quotient.out α) z₀₁
          ((Ideal.Quotient.mk_out α).trans hα.symm) m.1,
        clearedColumnFiber_congr K S ζ hζ H (H + H) (Quotient.out β) z₀₂
          ((Ideal.Quotient.mk_out β).trans hβ.symm) m.2]
    rw [hreplace, actualFiber_eq_centerFiber K S Γ a ψ ζ hζ σ hS6
      c k d' m₀.1 m₀.2 b z₀₁ z₀₂ hdb h₀₁ h₀₂ hb₁ hb₂ ν φ R N]
    rw [tsum_cleared_original_joint_eq_productPeriodicSum K S Γ
      a ha a0 b0 ha0 haSupport ψ hψ hψsupport ζ hζ σ hS6
      c k d' m₀.1 m₀.2 H H b z₀₁ z₀₂ hdb h₀₁ h₀₂ hb₁ hb₂ ν φ R N]
    rw [productPeriodicSum_cleared_eq_balanced K S Γ a ha a0 b0 ha0 haSupport
      ψ hψ hψsupport _ _ H d' ν _ _ φ R N hN]
    have hb := hbound c k (Ideal.Quotient.mk _ z₀₁) (Ideal.Quotient.mk _ z₀₂)
      d' (divisorColumn K S d' m₀.1) (divisorColumn K S d' m₀.2) p hpC hpJ
      (normalizedDivisorLocalPoint K S d') hu ν
      (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d' m₀.1)).2
      (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d' m₀.2)).2 φ R q hq
    have hs := jointSeminorm_le_fixedBoxSum K S Γ a ha a0 b0 ha0 haSupport
      ψ hψ hψsupport s ν (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d' m₀.1)).2
      (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d' m₀.2)).2 hb₁ hb₂ φ R
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs (mul_nonneg hC₀.le (Nat.cast_nonneg _)))
          (sq_nonneg q)) (by positivity))
  have hdecomp := tsum_annularOriginal_eq_cleared_residues K S ζ hζ Γ σ hS6
    c k d' hd a a0 b0 ha0 haSupport r (traceNormScale_pos K N hN).ne'
      (fun m => originalJointFactor K S ψ d' ν
        (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d' m.1)).2
        (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d' m.2)).2 φ R r m)
  have hwhole : (∑' m, F m) = ∑ α : Residue, ∑ β : Residue, ∑' m,
      clearedPairSummand K S ζ hζ H (H + H)
        (Quotient.out α) (Quotient.out β) F m := hdecomp.2.2
  change ‖∑' m, F m‖ ≤ _
  rw [hwhole]
  calc
    _ ≤ ∑ α : Residue, ∑ β : Residue,
        ‖∑' m, clearedPairSummand K S ζ hζ H (H + H)
          (Quotient.out α) (Quotient.out β) F m‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun α _ => norm_sum_le _ _))
    _ ≤ ∑ _α : Residue, ∑ _β : Residue, B :=
      Finset.sum_le_sum (fun α _ => Finset.sum_le_sum (fun β _ => hfiber α β))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp only [B, q, n]
      ring

end HeckeGeneral.Analysis.ActualWholeAnnularAllScaleDraft
