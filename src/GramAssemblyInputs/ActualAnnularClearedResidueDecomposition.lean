import ActualClearedJointPeriodicTransport
import ActualFixedSBoxDenominator

/-!
UNCOMPILED / native 0. The whole actual annular pair sum is the finite
sum of its complete ordinary cleared-residue fibers. The clearing power
is H and the residue depth is H+H, for the original finite-index subgroup.
All arithmetic zero masks and the unsplit joint factor are retained.

The active-divisor condition is supplied by an actual translate in the
same subgroup in the final endpoint. Neither summability nor a partition,
coefficient identity, cancellation estimate, or coprimality is an input.
This exact identity alone does not assert cancellation for arbitrary ideal
coefficients; its coefficient is the literal originalChartCoefficient.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeGeneral.Characters.ActualAnnularClearedResidueDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open ActualGramJointChartDraft ActualGramJointChartCoverDraft ActualGramFamilyDraft
open ActualClearedPairReindexDraft ActualGramFixedDenominatorDraft
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "OS" => S.integer K
local notation "NZ" => NonzeroRingElements OS
local notation "D" => finiteSIntegerDenominator K S

private theorem integerMap_injective : Function.Injective (algebraMap (𝓞 K) OS) := by
  intro x y h
  apply IsFractionRing.injective (𝓞 K) K
  simpa using congrArg (fun x : OS => (x : K)) h

variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6)

local instance clearedResidueFinite (N : ℕ) :
    Finite (𝓞 K ⧸ clearedSModulus K S ζ hζ N) :=
  Ring.HasFiniteQuotients.finiteQuotient (clearedSModulus_ne_zero K S ζ hζ N)

local instance clearedResidueFintype (N : ℕ) :
    Fintype (𝓞 K ⧸ clearedSModulus K S ζ hζ N) := Fintype.ofFinite _

/-- On a genuinely cleared column, the literal fiber is exactly its
ordinary quotient residue. This proves uniqueness as well as coverage. -/
theorem clearedColumnFiber_out_iff (M N : ℕ) (m : NZ) (z : 𝓞 K)
    (hz : algebraMap (𝓞 K) OS (D ^ M) * m.val = algebraMap (𝓞 K) OS z)
    (α : 𝓞 K ⧸ clearedSModulus K S ζ hζ N) :
    clearedColumnFiber K S ζ hζ M N (Quotient.out α) m ↔
      Ideal.Quotient.mk (clearedSModulus K S ζ hζ N) z = α := by
  constructor
  · rintro ⟨t, ht, hmem⟩
    have ht' : t = z := integerMap_injective K S (ht.symm.trans hz)
    have he : Ideal.Quotient.mk (clearedSModulus K S ζ hζ N) z =
        Ideal.Quotient.mk (clearedSModulus K S ζ hζ N) (Quotient.out α) :=
      Ideal.Quotient.eq.mpr (by simpa only [ht'] using hmem)
    exact he.trans (Ideal.Quotient.mk_out α)
  · intro he
    refine ⟨z, hz, ?_⟩
    exact Ideal.Quotient.eq.mp (he.trans (Ideal.Quotient.mk_out α).symm)

variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
variable (σ : K →+* ℂ) (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
local notation "H" => finiteIndexSUnitBoxWidth K S Γ
local notation "Residue" => 𝓞 K ⧸ clearedSModulus K S ζ hζ (H + H)

/-- Complete fixed-depth decomposition of the genuine whole annular sum.
No coarser chart is repeated and no residue, unit sector or zero mask is
deleted. The joint factor is retained without a tensor factorization. -/
theorem tsum_annularOriginal_eq_cleared_residues (c k d : NZ)
    (hd : (sLocalNonzeroIntegerDiagonal K S d).2 ∈ finiteLocalValuationBox K S H)
    (a : ℝ → ℝ) (a0 b0 : ℝ) (ha0 : 0 < a0)
    (haSupport : tsupport a ⊆ Set.Icc a0 b0) (r : ℝ) (hr : r ≠ 0)
    (joint : NZ × NZ → ℂ) :
    let F := annularOriginalSummand K S ζ hζ Γ σ hS6 c k d a a r r joint
    Summable F ∧
      (∀ α β : Residue, Summable
        (clearedPairSummand K S ζ hζ H (H + H) (Quotient.out α) (Quotient.out β) F)) ∧
      (∑' m, F m) = ∑ α : Residue, ∑ β : Residue, ∑' m : NZ × NZ,
        clearedPairSummand K S ζ hζ H (H + H) (Quotient.out α) (Quotient.out β) F m := by
  let F := annularOriginalSummand K S ζ hζ Γ σ hS6 c k d a a r r joint
  let A := fun m : NZ => sIntegerAnnularColumn K S Γ a r (divisorColumn K S d m)
  have hs := finite_support_divisor_annularColumn K S Γ d a a0 b0 ha0 haSupport r hr
  let T : Finset (NZ × NZ) := hs.toFinset ×ˢ hs.toFinset
  have hzero (m : NZ × NZ) (hm : m ∉ T) : F m = 0 := by
    by_cases h₁ : A m.1 = 0
    · change sIntegerAnnularColumn K S Γ a r (divisorColumn K S d m.1) = 0 at h₁
      simp only [F, annularOriginalSummand, h₁, Complex.ofReal_zero, mul_zero, zero_mul]
    by_cases h₂ : A m.2 = 0
    · change sIntegerAnnularColumn K S Γ a r (divisorColumn K S d m.2) = 0 at h₂
      simp only [F, annularOriginalSummand, h₂, Complex.ofReal_zero, mul_zero, zero_mul]
    exact False.elim (hm (Finset.mem_product.mpr
      ⟨hs.mem_toFinset.mpr h₁, hs.mem_toFinset.mpr h₂⟩))
  have hfinite : (Function.support F).Finite := by
    apply T.finite_toSet.subset
    intro m hm
    by_contra hn
    exact hm (hzero m hn)
  have hfiberzero (α β : Residue) (m : NZ × NZ) (hm : m ∉ T) :
      clearedPairSummand K S ζ hζ H (H + H)
        (Quotient.out α) (Quotient.out β) F m = 0 := by
    simp only [clearedPairSummand, hzero m hm, ite_self]
  refine ⟨summable_of_hasFiniteSupport hfinite, ?_, ?_⟩
  · intro α β
    exact summable_cleared_original_annularPair K S ζ hζ Γ σ hS6
      H (H + H) (Quotient.out α) (Quotient.out β) c k d a a0 b0 ha0 haSupport r hr joint
  · have hpartition (m : NZ × NZ) :
        F m = ∑ α : Residue, ∑ β : Residue,
          clearedPairSummand K S ζ hζ H (H + H)
            (Quotient.out α) (Quotient.out β) F m := by
      by_cases hF : F m = 0
      · simp [clearedPairSummand, hF]
      have hA₁ : A m.1 ≠ 0 := by
        intro hz
        change sIntegerAnnularColumn K S Γ a r (divisorColumn K S d m.1) = 0 at hz
        exact hF (by simp only [F, annularOriginalSummand, hz, Complex.ofReal_zero,
          mul_zero, zero_mul])
      have hA₂ : A m.2 ≠ 0 := by
        intro hz
        change sIntegerAnnularColumn K S Γ a r (divisorColumn K S d m.2) = 0 at hz
        exact hF (by simp only [F, annularOriginalSummand, hz, Complex.ofReal_zero,
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
          clearedPairSummand K S ζ hζ H (H + H)
            (Quotient.out α) (Quotient.out β) F m =
          if Ideal.Quotient.mk (clearedSModulus K S ζ hζ (H + H)) z₁ = α ∧
             Ideal.Quotient.mk (clearedSModulus K S ζ hζ (H + H)) z₂ = β then F m else 0 := by
        unfold clearedPairSummand
        rw [clearedColumnFiber_out_iff K S ζ hζ H (H + H) m.1 z₁ hz₁ α,
          clearedColumnFiber_out_iff K S ζ hζ H (H + H) m.2 z₂ hz₂ β]
      simp_rw [hrewrite]
      simp [ite_and]
    rw [tsum_eq_sum hzero]
    have hfib : ∀ α β : Residue, ∑' m : NZ × NZ,
        clearedPairSummand K S ζ hζ H (H + H) (Quotient.out α) (Quotient.out β) F m =
        ∑ m ∈ T, clearedPairSummand K S ζ hζ H (H + H)
          (Quotient.out α) (Quotient.out β) F m :=
      fun α β => tsum_eq_sum (hfiberzero α β)
    rw [Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun β _ => hfib α β))]
    calc
      _ = ∑ m ∈ T, ∑ α : Residue, ∑ β : Residue,
          clearedPairSummand K S ζ hζ H (H + H)
            (Quotient.out α) (Quotient.out β) F m :=
        Finset.sum_congr rfl (fun m _ => hpartition m)
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro α _
        rw [Finset.sum_comm]

/-- The required active divisor is selected inside the original Γ, before
the frequency, cutoff, scale and joint factor. No additional reduction or
clearing hypothesis remains in this existence endpoint. -/
theorem exists_translate_tsum_annularOriginal_eq_cleared_residues (d : NZ) :
    ∃ u : Γ, let d' := sIntegerOrbitTranslate K S Γ u d
      (sLocalNonzeroIntegerDiagonal K S d').2 ∈ finiteLocalValuationBox K S H ∧
      ∀ (c k : NZ) (a : ℝ → ℝ) (a0 b0 : ℝ),
        0 < a0 → tsupport a ⊆ Set.Icc a0 b0 →
        ∀ (r : ℝ), r ≠ 0 → ∀ joint : NZ × NZ → ℂ,
        let F := annularOriginalSummand K S ζ hζ Γ σ hS6 c k d' a a r r joint
        Summable F ∧
          (∀ α β : Residue, Summable
            (clearedPairSummand K S ζ hζ H (H + H)
              (Quotient.out α) (Quotient.out β) F)) ∧
          (∑' m, F m) = ∑ α : Residue, ∑ β : Residue, ∑' m : NZ × NZ,
            clearedPairSummand K S ζ hζ H (H + H)
              (Quotient.out α) (Quotient.out β) F m := by
  obtain ⟨u, hd, _, _⟩ := exists_subgroup_translate_with_fixed_denominator K S Γ d
  refine ⟨u, hd, ?_⟩
  intro c k a a0 b0 ha0 haSupport r hr joint
  exact tsum_annularOriginal_eq_cleared_residues K S ζ hζ Γ σ hS6
    c k (sIntegerOrbitTranslate K S Γ u d) hd a a0 b0 ha0 haSupport r hr joint

end HeckeGeneral.Characters.ActualAnnularClearedResidueDraft
