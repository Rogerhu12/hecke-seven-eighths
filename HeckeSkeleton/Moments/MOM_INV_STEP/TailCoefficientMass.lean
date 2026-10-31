import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalTailBound
import HeckeSkeleton.Moments.MOM_INV_STEP.JointMaskGeometry
import HeckeSkeleton.Moments.MOM_INV_STEP.MaskCounting
import HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalBudget

/-!
# Absolute mass of every actual first-source subfamily

The original marked canonical columns, the actual localized Poisson masks,
the source ideals and the original divisor-weighted labels are all counted
here. A fixed polynomial bound suffices for the arbitrarily rapid tail.
No free coefficient mass or energy bound is an input.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.TailCoefficientMass

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton
open HeckeSkeleton.Moments.MOMInvStep DedekindZetaZeroFree.LargeSieve
open CanonicalBlock CanonicalPoissonSplit CanonicalTailBound CoefficientBounds
  PrincipalBudget FirstMaskGeometry PrimitivePoissonSource ConductorMasks
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "Pair" => (Ext × Ext) × (Ext × Ext)

/-- The constant precedes the coefficient data, source windows, subfamily
and old label measure. The exponent one in each divisor estimate is a
fixed choice; rapid Schwartz decay later absorbs this explicit cost. -/
theorem exists_weighted_source_mass_bound (slotCap p : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {σ : Type*} (C : ColumnData K S σ)
      (G : HeckeCharacter K) (hcal : ThetaCalibrationInput K Sset D C.lambda G)
      (B N L : Finset Ext) (P : Ext → Finset Pair) (Q : Ext) (w : Ext → ℝ)
      (X H Y β W Aweight : ℝ),
      1 ≤ X → 1 ≤ H → 1 ≤ Y → 0 ≤ β → 0 ≤ W → 0 ≤ Aweight →
      C.slots.card ≤ slotCap →
      (∀ i ∈ C.slots, ∀ J ∈ C.primeLists i, ‖C.primeWeights i J‖ ≤ 1) →
      (∀ n ∈ N, Squarefree n.val.val) →
      (∀ n ∈ N, (n.val.val.absNorm : ℝ) ≤ X) →
      (∀ b ∈ B, (b.val.val.absNorm : ℝ) ≤ H) →
      (∀ f ∈ L, (f.val.val.absNorm : ℝ) ≤ Y) →
      (∀ f ∈ L, P f ⊆ (B ×ˢ N) ×ˢ (B ×ˢ N)) →
      (∀ b ∈ B, ∀ f ∈ L, ‖C.labelWeight b f‖ ≤ β) →
      (∀ n ∈ N, ‖C.cutoff ((n.val.val.absNorm : ℝ) / C.base ^ C.length)‖ ≤ W) →
      (∀ f ∈ L, 0 ≤ w f) →
      (∀ f ∈ L, w f ≤ Aweight * ((idealDivisors f.val.val).card : ℝ) ^ p) →
      (∑ f ∈ L, w f * coefficientMaskMass K S D C f (P f) (externalMask K S Q)) ≤
        A * Aweight * (β * W) ^ 2 * (Q.val.val.absNorm : ℝ) * H ^ 10 * X ^ 6 * Y ^ 2 := by
  obtain ⟨Ac, hAc, hcolumn⟩ := exists_uniform_column_bound K S D slotCap 1 (by norm_num)
  obtain ⟨Am, hAm, hmask⟩ := MaskCounting.exists_actual_pair_mask_bound K S D 1 (by norm_num)
  obtain ⟨Ai, hAi, hcount⟩ := exists_ideal_count_bound K
  obtain ⟨Al, hAl, hlabel⟩ := exists_label_mass_bound K S p 1 (by norm_num)
  let A := Al * Ai ^ 4 * Ac ^ 2 * Am
  have hA : 1 ≤ A := by
    dsimp only [A]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le hAl (one_le_pow₀ hAi))
        (one_le_pow₀ hAc)) hAm
  refine ⟨A, hA, ?_⟩
  intro σ C G hcal B N L P Q w X H Y β W Aweight hX hH hY hβ hW hAweight
    hcap ha hsf hn hb hf hP hlabelWeight hcut hw0 hw
  have hX0 := zero_le_one.trans hX
  have hH0 := zero_le_one.trans hH
  have hY0 := zero_le_one.trans hY
  have hAc0 := zero_le_one.trans hAc
  have hAm0 := zero_le_one.trans hAm
  have hAi0 := zero_le_one.trans hAi
  have hAl0 := zero_le_one.trans hAl
  have hcB : (B.card : ℝ) ≤ Ai * H := by
    have hc : (B.card : ℝ) ≤ ((boundedNormIdeals K H).card : ℝ) := by
      exact_mod_cast exterior_card_le_norm_count K S B H hb
    exact hc.trans (hcount H hH)
  have hcN : (N.card : ℝ) ≤ Ai * X := by
    have hc : (N.card : ℝ) ≤ ((boundedNormIdeals K X).card : ℝ) := by
      exact_mod_cast exterior_card_le_norm_count K S N X hn
    exact hc.trans (hcount X hX)
  have hcPairs : (((B ×ˢ N) ×ˢ (B ×ˢ N)).card : ℝ) ≤
      Ai ^ 4 * H ^ 2 * X ^ 2 := by
    simp only [Finset.card_product, Nat.cast_mul]
    calc
      _ ≤ (Ai * H * (Ai * X)) * (Ai * H * (Ai * X)) := by gcongr
      _ = _ := by ring
  let U : ℝ := (Ac * β * W * (X * H ^ 3)) ^ 2 *
    (Am * ((Q.val.val.absNorm : ℝ) * (H * H * X * X)))
  have hU : 0 ≤ U := by
    dsimp only [U]
    positivity
  have hmass (f : Ext) (hfl : f ∈ L) :
      coefficientMaskMass K S D C f (P f) (externalMask K S Q) ≤
        Ai ^ 4 * H ^ 2 * X ^ 2 * U := by
    have hpoint (x : Pair) (hx : x ∈ P f) :
        ‖pairWeight K S D C f x‖ *
          (2 : ℝ) ^ (externalMask K S Q ∪
            principalMask K S (pairSupport K S D x.1.2 x.2.2 x.1.1 x.2.1)
              (pairExponent K S x.1.2 x.2.2 x.1.1 x.2.1)).card ≤ U := by
      obtain ⟨hleft, hright⟩ := Finset.mem_product.mp (hP f hfl hx)
      obtain ⟨hb₁, hn₁⟩ := Finset.mem_product.mp hleft
      obtain ⟨hb₂, hn₂⟩ := Finset.mem_product.mp hright
      have hcol₁ := hcolumn C G hcal f x.1.1 x.1.2 X H β W (hsf _ hn₁) hcap
        hX0 hH0 hβ hW (hn _ hn₁) (hb _ hb₁) (hlabelWeight _ hb₁ f hfl) (hcut _ hn₁) ha
      have hcol₂ := hcolumn C G hcal f x.2.1 x.2.2 X H β W (hsf _ hn₂) hcap
        hX0 hH0 hβ hW (hn _ hn₂) (hb _ hb₂) (hlabelWeight _ hb₂ f hfl) (hcut _ hn₂) ha
      simp only [Real.rpow_one] at hcol₁ hcol₂
      have hpair : ‖pairWeight K S D C f x‖ ≤ (Ac * β * W * (X * H ^ 3)) ^ 2 := by
        rw [pairWeight, norm_mul, norm_conj, pow_two]
        exact mul_le_mul hcol₁ hcol₂ (norm_nonneg _) (by positivity)
      have hm := hmask (FirstSourceDecomposition.primeSupport Q.val)
        (fun p hp => Q.property p ((FirstSourceDecomposition.mem_primeSupport Q.val p).mp hp))
        Q.val.val (nonZeroDivisors.coe_ne_zero Q.val)
        (fun p hp => (FirstSourceDecomposition.mem_primeSupport Q.val p).mp hp)
        x.1.2 x.2.2 x.1.1 x.2.1
      simp only [Real.rpow_one, Ideal.absNorm_mul, Nat.cast_mul] at hm
      have hm' :
          (2 : ℝ) ^ (externalMask K S Q ∪
            principalMask K S (pairSupport K S D x.1.2 x.2.2 x.1.1 x.2.1)
              (pairExponent K S x.1.2 x.2.2 x.1.1 x.2.1)).card ≤
            Am * ((Q.val.val.absNorm : ℝ) * (H * H * X * X)) := by
        apply hm.trans
        gcongr
        · exact hb _ hb₁
        · exact hb _ hb₂
        · exact hn _ hn₁
        · exact hn _ hn₂
      exact mul_le_mul hpair hm' (by positivity) (sq_nonneg _)
    unfold coefficientMaskMass
    calc
      _ ≤ ∑ _x ∈ P f, U := Finset.sum_le_sum hpoint
      _ = ((P f).card : ℝ) * U := by simp
      _ ≤ Ai ^ 4 * H ^ 2 * X ^ 2 * U := by
        apply mul_le_mul_of_nonneg_right _ hU
        have hc : ((P f).card : ℝ) ≤ (((B ×ˢ N) ×ˢ (B ×ˢ N)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card (hP f hfl)
        exact hc.trans hcPairs
  have hlabelMass : (∑ f ∈ L, w f) ≤ Al * Aweight * Y ^ 2 := by
    simpa using hlabel L w Aweight Y hAweight hY hf hw
  calc
    _ ≤ ∑ f ∈ L, w f * (Ai ^ 4 * H ^ 2 * X ^ 2 * U) :=
      Finset.sum_le_sum (fun f hfl => mul_le_mul_of_nonneg_left (hmass f hfl) (hw0 f hfl))
    _ = (∑ f ∈ L, w f) * (Ai ^ 4 * H ^ 2 * X ^ 2 * U) := Finset.sum_mul.symm
    _ ≤ (Al * Aweight * Y ^ 2) * (Ai ^ 4 * H ^ 2 * X ^ 2 * U) :=
      mul_le_mul_of_nonneg_right hlabelMass (by positivity)
    _ = A * Aweight * (β * W) ^ 2 * (Q.val.val.absNorm : ℝ) * H ^ 10 * X ^ 6 * Y ^ 2 := by
      dsimp only [A, U]
      ring

end HeckeSkeleton.Moments.MOM_INV_STEP.TailCoefficientMass

end

