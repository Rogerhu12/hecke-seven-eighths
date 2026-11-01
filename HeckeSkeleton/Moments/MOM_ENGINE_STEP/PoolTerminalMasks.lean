import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCoveredLabels
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalMaskCardinality

/-!
# The actual masks of all four terminal pool branches

The main mask is certified prime by prime against the original mask
ideal and first common ideal.  Each residual mask may additionally
contain its genuine amplifier prime, with the actual exponent 1, 6 or 7.
No inclusion in the first mask and no bound on a whole mask cardinality
is assumed.  Taking the maximum of these actual mask sizes costs no
additional pool cardinality.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}

def poolTagMaskFactor (P : PowerScaleExteriorPool A bad Z ell eps) :
    PoolSourceTag P → Ideal (𝓞 K)
  | .inl _ => 1
  | .inr (.inl p) => p.val.val.asIdeal ^ 1
  | .inr (.inr (.inl p)) => p.val.val.asIdeal ^ 6
  | .inr (.inr (.inr p)) => p.val.val.asIdeal ^ 7

theorem poolTagMaskFactor_ne_zero (P : PowerScaleExteriorPool A bad Z ell eps)
    (tag : PoolSourceTag P) : poolTagMaskFactor P tag ≠ 0 := by
  rcases tag with ⟨⟩ | p | p | p
  · exact one_ne_zero
  all_goals exact pow_ne_zero _ p.val.val.ne_bot

theorem poolTagMaskFactor_norm (P : PowerScaleExteriorPool A bad Z ell eps)
    (L : ℝ) (hL : 0 ≤ L) (hell : ell ≤ L) (tag : PoolSourceTag P) :
    (Ideal.absNorm (poolTagMaskFactor P tag) : ℝ) ≤ Z ^ (7 * L) := by
  have hz : 0 < Z := zero_lt_one.trans P.base_gt_one
  have hp (p : P.primes) (n : ℕ) (hn : n ≤ 7) :
      (Ideal.absNorm (p.val.val.asIdeal ^ n) : ℝ) ≤ Z ^ (7 * L) := by
    calc
      _ = (Ideal.absNorm p.val.val.asIdeal : ℝ) ^ n := by
        simp only [map_pow, Nat.cast_pow]
      _ ≤ (Z ^ ell) ^ n :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (P.norm_upper p.val p.property) n
      _ = Z ^ (ell * (n : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le P.base_gt_one.le (by
        have hn' : (n : ℝ) ≤ 7 := by exact_mod_cast hn
        exact (mul_le_mul_of_nonneg_left hn' P.exponent_pos.le).trans
          ((mul_le_mul_of_nonneg_right hell (by norm_num : (0 : ℝ) ≤ 7)).trans_eq (by ring)))
  rcases tag with ⟨⟩ | p | p | p
  · simpa only [poolTagMaskFactor, map_one, Nat.cast_one] using
      Real.one_le_rpow P.base_gt_one.le (mul_nonneg (by norm_num) hL)
  · exact hp p 1 (by decide)
  · exact hp p 6 (by decide)
  · exact hp p 7 le_rfl

/-- The literal old mask, first common ideal and actual residual prime. -/
def poolTerminalMaskIdeal (P : PowerScaleExteriorPool A bad Z ell eps)
    (oldMask common : Ideal (𝓞 K)) (tag : PoolSourceTag P) : Ideal (𝓞 K) :=
  oldMask * common * poolTagMaskFactor P tag

theorem poolTerminalMaskIdeal_ne_zero (P : PowerScaleExteriorPool A bad Z ell eps)
    (oldMask common : Ideal (𝓞 K)) (hmask : oldMask ≠ 0) (hcommon : common ≠ 0)
    (tag : PoolSourceTag P) : poolTerminalMaskIdeal P oldMask common tag ≠ 0 :=
  mul_ne_zero (mul_ne_zero hmask hcommon) (poolTagMaskFactor_ne_zero P tag)

theorem poolTerminalMaskIdeal_norm (P : PowerScaleExteriorPool A bad Z ell eps)
    (B L : ℝ) (hL : 0 ≤ L) (hell : ell ≤ L)
    (oldMask common : Ideal (𝓞 K))
    (hmask : (Ideal.absNorm oldMask : ℝ) ≤ Z ^ B)
    (hcommon : (Ideal.absNorm common : ℝ) ≤ Z ^ B) (tag : PoolSourceTag P) :
    (Ideal.absNorm (poolTerminalMaskIdeal P oldMask common tag) : ℝ) ≤ Z ^ (2 * B + 7 * L) := by
  have hz : 0 < Z := zero_lt_one.trans P.base_gt_one
  unfold poolTerminalMaskIdeal
  simp only [map_mul, Nat.cast_mul]
  calc
    _ ≤ (Z ^ B * Z ^ B) * Z ^ (7 * L) :=
      mul_le_mul
        (mul_le_mul hmask hcommon (Nat.cast_nonneg _) (Real.rpow_nonneg hz.le _))
        (poolTagMaskFactor_norm P L hL hell tag) (Nat.cast_nonneg _)
        (mul_nonneg (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hz.le _))
    _ = _ := by
      rw [← Real.rpow_add hz, ← Real.rpow_add hz]
      congr 1
      ring

variable {α : Type*}

/-- The actual maximum over the two original sides and four branch
sorts; it introduces no sum over the pool. -/
def poolTerminalMaskCap (P : PowerScaleExteriorPool A bad Z ell eps)
    (left right : PoolSourceTag P → Finset α) : ℕ :=
  Finset.univ.sup (fun j : Bool × PoolSourceTag P =>
    if j.1 then (left j.2).card else (right j.2).card)

theorem poolTerminalMaskCap_left (P : PowerScaleExteriorPool A bad Z ell eps)
    (left right : PoolSourceTag P → Finset α) (tag : PoolSourceTag P) :
    (left tag).card ≤ poolTerminalMaskCap P left right := by
  exact Finset.le_sup (b := (true, tag)) (Finset.mem_univ _)

theorem poolTerminalMaskCap_right (P : PowerScaleExteriorPool A bad Z ell eps)
    (left right : PoolSourceTag P → Finset α) (tag : PoolSourceTag P) :
    (right tag).card ≤ poolTerminalMaskCap P left right := by
  exact Finset.le_sup (b := (false, tag)) (Finset.mem_univ _)

theorem poolTerminalMaskCap_power_le (P : PowerScaleExteriorPool A bad Z ell eps)
    (left right : PoolSourceTag P → Finset α) (bound : ℝ)
    (hleft : ∀ tag, (2 : ℝ) ^ (left tag).card ≤ bound)
    (hright : ∀ tag, (2 : ℝ) ^ (right tag).card ≤ bound) :
    (2 : ℝ) ^ poolTerminalMaskCap P left right ≤ bound := by
  obtain ⟨⟨side, tag⟩, _, heq⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (Bool × PoolSourceTag P))
    ⟨(true, .inl ()), Finset.mem_univ _⟩
    (fun j : Bool × PoolSourceTag P => if j.1 then (left j.2).card else (right j.2).card)
  unfold poolTerminalMaskCap
  rw [heq]
  cases side
  · exact hright tag
  · exact hleft tag

/-- The fixed small-power constant controls every actual pool mask
from its original per-prime certificate.  In particular the residual
prime is retained, and the maximum does not pay another pool density. -/
theorem pool_terminal_masks_subpower (B L ε : ℝ) (hB : 0 ≤ B)
    (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ Cmask : ℝ, 0 < Cmask ∧
    ∀ (Z ell eps : ℝ) (bad : Finset (HeightOneSpectrum (𝓞 K)))
      (P : PowerScaleExteriorPool A bad Z ell eps), ell ≤ L →
    ∀ (oldMask commonLeft commonRight : Ideal (𝓞 K)), oldMask ≠ 0 →
      commonLeft ≠ 0 → commonRight ≠ 0 →
      (Ideal.absNorm oldMask : ℝ) ≤ Z ^ B →
      (Ideal.absNorm commonLeft : ℝ) ≤ Z ^ B →
      (Ideal.absNorm commonRight : ℝ) ≤ Z ^ B →
    ∀ (left right : PoolSourceTag P → Finset α),
      (∀ tag, OriginalMaskPrimeData (left tag) (poolTerminalMaskIdeal P oldMask commonLeft tag)) →
      (∀ tag, OriginalMaskPrimeData (right tag) (poolTerminalMaskIdeal P oldMask commonRight tag)) →
      (2 : ℝ) ^ poolTerminalMaskCap P left right ≤ Cmask * Z ^ ε := by
  obtain ⟨Cmask, hC, hmask⟩ := original_mask_labels_subpower (K := K)
    (2 * B + 7 * L) ε (by positivity) hε
  refine ⟨Cmask, hC, ?_⟩
  intro Z ell eps bad P hell oldMask commonLeft commonRight hM0 hL0 hR0 hMN hLN hRN
    left right ML MR
  apply poolTerminalMaskCap_power_le P left right
  · intro tag
    simpa only [Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat] using
      hmask Z P.base_gt_one.le (left tag) (poolTerminalMaskIdeal P oldMask commonLeft tag)
        (poolTerminalMaskIdeal_ne_zero P oldMask commonLeft hM0 hL0 tag)
        (poolTerminalMaskIdeal_norm P B L hL hell oldMask commonLeft hMN hLN tag) (ML tag)
  · intro tag
    simpa only [Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat] using
      hmask Z P.base_gt_one.le (right tag) (poolTerminalMaskIdeal P oldMask commonRight tag)
        (poolTerminalMaskIdeal_ne_zero P oldMask commonRight hM0 hR0 tag)
        (poolTerminalMaskIdeal_norm P B L hL hell oldMask commonRight hMN hRN tag) (MR tag)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.poolTerminalMaskIdeal_norm
#print axioms HeckeSkeleton.Moments.EngineStep.poolTerminalMaskCap_power_le
#print axioms HeckeSkeleton.Moments.EngineStep.pool_terminal_masks_subpower
