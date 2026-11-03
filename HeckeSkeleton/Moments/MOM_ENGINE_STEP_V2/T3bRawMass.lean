import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalRawNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalProfileAtomBounds

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Actual exceptional mass keeps the full inner frozen ideal

The original central denominators, finite prime counts and the actual
frozen prime norm window give a full inverse frozen norm. The prime
occurrence set is partitioned only into its original frozen and live
positions. The resulting scale product is the unallocated original
product, so both independent divisor allocations stay visible.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Ψ : Ideal (𝓞 K) →* ℂ} {W₁ W₂ : ℝ → ℂ} {g h : A.R} {k : ℕ}

private theorem product_split (keep : Finset (Fin k)) (f : Fin k → ℝ) :
    (∏ i, f i) = (∏ i ∈ Finset.univ \ keep, f i) *
      ∏ j, f (SlotRestriction.index keep j) := by
  simpa only [Finset.sdiff_eq_filter, Finset.mem_univ, true_and] using
    (SlotRestriction.product_extend keep (fun _ => (PUnit.unit : PUnit.{1}))
      (fun _ => (PUnit.unit : PUnit.{1})) (fun i _ => f i))

private theorem prime_card_bound (S : Finset (HeightOneSpectrum (𝓞 K)))
    (X : ℝ) (hX : 1 ≤ X)
    (h : ∀ q ∈ S, (Ideal.absNorm q.asIdeal : ℝ) ≤ X) :
    (S.card : ℝ) ≤ idealCountConstant K * X := by
  have hi : Function.Injective (HeightOneSpectrum.asIdeal : HeightOneSpectrum (𝓞 K) → _) :=
    fun _ _ h => HeightOneSpectrum.ext h
  have hb := card_le_idealCountConstant K (S.image HeightOneSpectrum.asIdeal) X hX (by
    intro I hI
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hI
    exact h q hq)
  simpa only [Finset.card_image_of_injective _ hi] using hb

private theorem square_mass_composition
    (scalar slots product live frozen total B : ℝ) (cap : ℕ)
    (hs : 0 ≤ scalar) (ht : 0 ≤ slots) (hq : 0 ≤ product)
    (hl : 0 ≤ live) (hf : 0 < frozen) (hX : 0 ≤ total) (hB : 0 ≤ B)
    (hscalar : scalar ^ 2 ≤ B ^ (2 * cap) / frozen)
    (hslots : slots ^ 2 ≤ B ^ (2 * cap) * live)
    (hscale : product * live * frozen ≤ B ^ (2 * cap) * total) :
    scalar * slots * Real.sqrt product ≤ B ^ (3 * cap) * Real.sqrt total / frozen := by
  apply (le_div_iff₀ hf).mpr
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  have hprod : scalar ^ 2 * slots ^ 2 ≤ B ^ (4 * cap) * live / frozen := by
    have hm := mul_le_mul hscalar hslots (sq_nonneg slots)
      (div_nonneg (pow_nonneg hB _) hf.le)
    convert hm using 1 <;> rw [show 4 * cap = 2 * cap + 2 * cap by omega, pow_add] <;> ring
  calc
    _ = (scalar ^ 2 * slots ^ 2) * (product * frozen ^ 2) := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hq]
      ring
    _ ≤ (B ^ (4 * cap) * live / frozen) * (product * frozen ^ 2) :=
      mul_le_mul_of_nonneg_right hprod (mul_nonneg hq (sq_nonneg _))
    _ = B ^ (4 * cap) * (product * live * frozen) := by
      field_simp [hf.ne']
      <;> ring
    _ ≤ B ^ (4 * cap) * (B ^ (2 * cap) * total) :=
      mul_le_mul_of_nonneg_left hscale (pow_nonneg hB _)
    _ = (B ^ (3 * cap) * Real.sqrt total) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hX, ← pow_mul, ← mul_assoc, ← pow_add,
        show 4 * cap + 2 * cap = (3 * cap) * 2 by omega]

/-- The only analytic inputs are the actual individual prime profile
and annulus bounds. In particular no source mass or scalar inequality
is assumed. The scalar denominator is proved from the same allocation. -/
theorem rawMass_le_scale_quotient
    (s : AllocatedExceptionalSource (V := V) (σ := σ) Ψ W₁ W₂ g h k)
    (C : A.GeneralArithmeticContext σ η hS)
    (cap : ℕ) (hcap : k ≤ cap) (annulus profile B : ℝ)
    (hZ : 1 < s.Zslot) (hlength : ∀ i, 0 ≤ s.length i)
    (hannulus : 1 ≤ annulus) (hprofile : 0 ≤ profile) (hB : 1 ≤ B)
    (hAB : annulus ≤ B) (hAPB : annulus * profile ^ 2 ≤ B)
    (hCPB : idealCountConstant K * annulus * profile ≤ B)
    (hmask : ∀ I, s.characters.mask I = 0 ∨ s.characters.mask I = 1)
    (hwindow : ∀ i, ∀ q ∈ s.allocation.slots i,
      (Ideal.absNorm q.asIdeal : ℝ) ≤ annulus * s.Zslot ^ s.length i)
    (hweight : ∀ i, ∀ q ∈ s.allocation.slots i, ‖s.w i q‖ ≤ profile) :
    s.rawMass ≤ B ^ (3 * cap) *
      Real.sqrt (s.X₁ * s.X₂ * ∏ i, s.Zslot ^ s.length i) /
        (Ideal.absNorm s.allocation.frozenIdeal : ℝ) := by
  let frozen := Finset.univ \ s.allocation.keep
  let L : Fin k → ℝ := fun i => s.Zslot ^ s.length i
  let live : ℝ := ∏ j, L (SlotRestriction.index s.allocation.keep j)
  let D : ℝ := idealNorm K (s.allocation.plainDivisor 0) *
    idealNorm K (s.allocation.plainDivisor (Fin.succ 0))
  let N : ℝ := (Ideal.absNorm s.allocation.frozenIdeal : ℝ)
  have hz := zero_lt_one.trans hZ
  have hb := zero_le_one.trans hB
  have ha := zero_le_one.trans hannulus
  have hL (i) : 0 < L i := Real.rpow_pos_of_pos hz _
  have hD : 0 < D := mul_pos (idealNorm_pos K _) (idealNorm_pos K _)
  have hN : 0 < N := by
    change (0 : ℝ) < (Ideal.absNorm s.allocation.frozenIdeal : ℝ)
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr s.allocation.frozenIdeal_ne_zero)
  have hfrozenCard : frozen.card ≤ cap := by
    have hcard : frozen.card ≤ k := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ frozen
    exact hcard.trans hcap
  have hkeepCard : s.allocation.keep.card ≤ cap := by
    have hcard : s.allocation.keep.card ≤ k := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ s.allocation.keep
    exact hcard.trans hcap
  have hwitness (i) : s.allocation.witness.2 i ∈ s.allocation.slots i := by
    have hm := s.allocation.witness_mem
    rw [WholeAllocation.paired_allocated_columns_eq_filter] at hm
    exact Fintype.mem_piFinset.mp (Finset.mem_product.mp (Finset.mem_filter.mp hm).1).2 i
  have hplain (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
      ‖sourcePlainCoefficient s.characters.plain s.characters.plainTwist s.characters.mask I‖ ≤ 1 :=
    OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one _ _ _ _ (hmask _)
  have hprime (i) (q : HeightOneSpectrum (𝓞 K)) :
      ‖sourcePrimeCoefficient (s.characters.slot i) (s.characters.slotTwist i) s.characters.mask q‖ ≤ 1 :=
    OriginalProfileAtomBounds.sourcePrimeCoefficient_norm_le_one _ _ _ _ (hmask _)
  have hscalar : ‖s.allocation.scalar (σ := σ) s.characters g h s.Zslot s.length s.w‖ ^ 2 ≤
      B ^ (2 * cap) / N := by
    apply (s.allocation.scalar_norm_sq_le_frozen_norm C s.characters g h s.Zslot hz
      s.length s.w (fun _ => annulus) (fun _ => profile ^ 2)
      (hplain _) (hplain _) (fun i _ => hprime i _)
      (fun i _ => hwindow i _ (hwitness i))
      (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hweight i _ (hwitness i)) 2)
      (fun _ => ha) (fun _ => sq_nonneg _)).trans
    apply div_le_div_of_nonneg_right ?_ hN.le
    calc
      _ ≤ ∏ _i ∈ frozen, B :=
        Finset.prod_le_prod₀ (fun _ _ => mul_nonneg ha (sq_nonneg _)) (fun _ _ => hAPB)
      _ = B ^ frozen.card := by rw [Finset.prod_const]
      _ ≤ B ^ (2 * cap) := pow_le_pow_right₀ hB (by omega)
  have hslot : s.slotMass ≤ B ^ cap * Real.sqrt live := by
    have hsingle (j : Fin s.allocation.keep.card) :
        (∑ q ∈ s.allocation.childSlots j,
          ‖sourcePrimeTerm (σ := σ) ((s.characters.restrictSlots s.allocation.keep).slot j)
            ((s.characters.restrictSlots s.allocation.keep).slotTwist j)
            (s.characters.restrictSlots s.allocation.keep).mask g h
            (s.w (SlotRestriction.index s.allocation.keep j))
            (s.Zslot ^ s.length (SlotRestriction.index s.allocation.keep j)) q‖) ≤
        B * Real.sqrt (L (SlotRestriction.index s.allocation.keep j)) := by
      let i := SlotRestriction.index s.allocation.keep j
      have hterm (q) (hq : q ∈ s.allocation.childSlots j) :=
        sourcePrimeTerm_norm_le_profile C (s.characters.slot i) (s.characters.slotTwist i)
          s.characters.mask g h (s.w i) (L i) profile q (hprime i q) (hweight i q hq)
      have hcount := prime_card_bound (s.allocation.childSlots j) (annulus * L i)
        (one_le_mul_of_one_le_of_one_le hannulus (Real.one_le_rpow hZ.le (hlength i)))
        (hwindow i)
      calc
        _ ≤ ∑ _q ∈ s.allocation.childSlots j, profile / Real.sqrt (L i) :=
          Finset.sum_le_sum hterm
        _ = ((s.allocation.childSlots j).card : ℝ) * (profile / Real.sqrt (L i)) := by simp
        _ ≤ (idealCountConstant K * (annulus * L i)) * (profile / Real.sqrt (L i)) :=
          mul_le_mul_of_nonneg_right hcount (div_nonneg hprofile (Real.sqrt_nonneg _))
        _ = (idealCountConstant K * annulus * profile) * Real.sqrt (L i) := by
          have hsqrt := Real.sq_sqrt (hL i).le
          field_simp [(Real.sqrt_pos.mpr (hL i)).ne']
          nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_right hCPB (Real.sqrt_nonneg _)
    calc
      _ ≤ ∏ j, B * Real.sqrt (L (SlotRestriction.index s.allocation.keep j)) :=
        Finset.prod_le_prod₀ (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
          (fun j _ => hsingle j)
      _ = B ^ s.allocation.keep.card * Real.sqrt live := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ← Real.sqrt_prod Finset.univ (fun j _ => (hL _).le)]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hB hkeepCard) (Real.sqrt_nonneg _)
  have hslotSquare : s.slotMass ^ 2 ≤ B ^ (2 * cap) * live := by
    have hs := pow_le_pow_left₀ s.slotMass_nonneg hslot 2
    rw [mul_pow, Real.sq_sqrt (Finset.prod_nonneg (fun _ _ => (hL _).le)), ← pow_mul] at hs
    simpa only [Nat.mul_comm cap 2] using hs
  have hNupper : N ≤ D * (B ^ (2 * cap) * ∏ i ∈ frozen, L i) := by
    dsimp only [N]
    rw [s.allocation.frozenIdeal_norm]
    apply mul_le_mul_of_nonneg_left ?_ hD.le
    calc
      _ ≤ ∏ i ∈ frozen, B * L i := Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        (fun i _ => (hwindow i _ (hwitness i)).trans
          (mul_le_mul_of_nonneg_right hAB (hL i).le))
      _ = B ^ frozen.card * ∏ i ∈ frozen, L i := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB (by omega))
        (Finset.prod_nonneg (fun _ _ => (hL _).le))
  have hX₁ : 0 < s.X₁ := by
    have ht := mul_pos (s.lower_pos.trans_le s.X₁_lower)
      (idealNorm_pos K (s.allocation.plainDivisor 0))
    simpa only [div_mul_cancel₀ _ (idealNorm_pos K _).ne'] using ht
  have hX₂ : 0 < s.X₂ := by
    have ht := mul_pos (s.lower_pos.trans_le s.X₂_lower)
      (idealNorm_pos K (s.allocation.plainDivisor (Fin.succ 0)))
    simpa only [div_mul_cancel₀ _ (idealNorm_pos K _).ne'] using ht
  have hq : 0 < s.product := by
    rw [← s.productX]
    exact mul_pos (s.lower_pos.trans_le s.X₁_lower) (s.lower_pos.trans_le s.X₂_lower)
  have hprod : s.product = s.X₁ * s.X₂ / D := by
    rw [← s.productX, div_mul_div_comm]
  have hcomp : s.product * live * N ≤
      B ^ (2 * cap) * (s.X₁ * s.X₂ * ∏ i, L i) := by
    have hlive : 0 ≤ live := by
      dsimp only [live]
      exact Finset.prod_nonneg
        (fun j _ => (hL (SlotRestriction.index s.allocation.keep j)).le)
    have hm : s.product * live * N ≤
        (s.product * live) * (D * (B ^ (2 * cap) * ∏ i ∈ frozen, L i)) :=
      mul_le_mul_of_nonneg_left hNupper (mul_nonneg hq.le hlive)
    apply hm.trans_eq
    rw [hprod, product_split s.allocation.keep L]
    change (_ / D) * live * (D * _) = _
    field_simp [hD.ne']
    <;> ring
  exact square_mass_composition
    ‖s.allocation.scalar (σ := σ) s.characters g h s.Zslot s.length s.w‖ s.slotMass
    s.product live N (s.X₁ * s.X₂ * ∏ i, L i) B cap
    (norm_nonneg _) s.slotMass_nonneg hq.le (Finset.prod_nonneg (fun _ _ => (hL _).le))
    hN (mul_nonneg (mul_nonneg hX₁.le hX₂.le) (Finset.prod_nonneg (fun _ _ => (hL _).le)))
    hb hscalar hslotSquare hcomp

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.rawMass_le_scale_quotient
