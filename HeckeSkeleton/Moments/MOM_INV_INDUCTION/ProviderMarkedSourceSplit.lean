import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceMarkedBlockEnergy

/-!
# The full original marked sum is a finite sum of genuine Mellin blocks

The actual common-slot subset and common prime tuple are extracted from
the original prime tuple and squarefree inverse ideal.  The new column
annuli are a fixed finite partition of their proved norm window.  Every
row mask and original coefficient remains in the displayed identities.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedSourceSplit

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeSkeleton.Moments.MOMInvStep HeckeSkeleton.Moments.MOM_INV_STEP AssignedMarkSource
open ProviderMarkedOverlap ProviderMarkedSlots ProviderMarkedReindex ProviderMarkedTupleSplit
  ProviderMarkedMellin ProviderMarkedAnnuli ProviderMarkedWindows
open scoped Classical BigOperators nonZeroDivisors Function

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K} {d : ℕ}

def rawSource (χ : HeckeCharacter K)
    (lists : Fin d → Finset (HeightOneSpectrum (𝓞 K)))
    (a : Fin d → Ideal (𝓞 K) → ℂ) (good : HeightOneSpectrum (𝓞 K) → Prop)
    (u : Ideal (𝓞 K)) (X : ℝ) (W : ℝ → ℂ) : ℂ :=
  ∑ p ∈ tuples lists, ∑ n ∈ (ProviderMarkedPools.pool X).filter Squarefree,
    (moebius n : ℂ) * idealCoefficient (primeCoefficient K χ) n *
      idealCoefficient (primeCoefficient K χ) (primeProduct Finset.univ p) * choiceWeight a p *
      ProviderMarkedMask.value good u n *
      ProviderMarkedMask.value good u (primeProduct Finset.univ p) * W (ProviderMarkedPools.norm n / X)

def selectedSource {J : ℕ} (χ : HeckeCharacter K)
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (a : Fin J → Ideal (𝓞 K) → ℂ) (good : HeightOneSpectrum (𝓞 K) → Prop)
    (u j : Ideal (𝓞 K)) (X : ℝ) (W : ℝ → ℂ) : ℂ :=
  ∑ p ∈ tuples lists, ∑ n ∈ ProviderMarkedPools.sourcePool X j (primeProduct Finset.univ p),
    originalCoefficient χ a j p n * ProviderMarkedMask.value good u n *
      ProviderMarkedMask.value good u (j * primeProduct Finset.univ p) * W (ProviderMarkedPools.norm n / X)

theorem source_eq_selected (χ : HeckeCharacter K)
    (lists : Fin d → Finset (HeightOneSpectrum (𝓞 K)))
    (hdis : Pairwise (Disjoint on lists)) (a : Fin d → Ideal (𝓞 K) → ℂ)
    (good : HeightOneSpectrum (𝓞 K) → Prop) (u : Ideal (𝓞 K)) (X : ℝ) (W : ℝ → ℂ) :
    rawSource χ lists a good u X W =
      ∑ J ∈ (Finset.univ : Finset (Fin d)).powerset,
        ∑ q ∈ tuples (restrictedLists J lists),
          choiceWeight (fun i => a (slot J i)) q *
            selectedSource χ (restrictedLists (remaining J) lists)
              (fun i => a (slot (remaining J) i)) good u
              (primeProduct Finset.univ q) X W := by
  unfold rawSource
  rw [full_source_decomposition lists hdis X]
  apply Finset.sum_congr rfl
  intro J hJ
  apply Finset.sum_congr rfl
  intro q hq
  unfold selectedSource
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [primeProduct_glue J q p]
  have hw := weight_glue J (fun i p => a i p.asIdeal) q p
  change choiceWeight a (glue J q p) =
    choiceWeight (fun i => a (slot J i)) q *
      choiceWeight (fun i => a (slot (remaining J) i)) p at hw
  rw [hw]
  unfold originalCoefficient
  ring

/-- The change-of-variable norm identity is normalized at its original
source scale, without rounding either extracted prime product. -/
theorem normalized_forward (Z r z G : ℝ) (hZ : 0 < Z)
    (j P : Ideal (𝓞 K)) (hP : P ≠ 0) (n : Source j P) :
    (ProviderMarkedPools.norm j / Z ^ G) *
        (ProviderMarkedPools.norm (forward j P n.val) /
          Z ^ ProviderMarkedScale.columnLength r z G) =
      (ProviderMarkedPools.norm n.val / Z ^ r) *
        (ProviderMarkedPools.norm P / Z ^ (z - G)) := by
  have h := ProviderMarkedScale.profile_argument Z r z G
    (ProviderMarkedPools.norm n.val) (ProviderMarkedPools.norm j)
    (ProviderMarkedPools.norm P) (ProviderMarkedPools.norm (forward j P n.val)) hZ
    (ProviderMarkedPools.norm_pos hP).ne' (forward_norm j P n)
  exact (eq_div_iff (div_pos (ProviderMarkedPools.norm_pos hP)
    (Real.rpow_pos_of_pos hZ _)).ne').mp h |>.symm

theorem forward_window (slotCap : ℕ) (Z r z G : ℝ) (hZ : 0 < Z)
    (j P : Ideal (𝓞 K)) (hP : P ≠ 0) (n : Source j P)
    (hj : ((2 : ℝ) ^ slotCap)⁻¹ ≤ ProviderMarkedPools.norm j / Z ^ G ∧
      ProviderMarkedPools.norm j / Z ^ G ≤ (2 : ℝ) ^ slotCap)
    (hp : ((2 : ℝ) ^ slotCap)⁻¹ ≤ ProviderMarkedPools.norm P / Z ^ (z - G) ∧
      ProviderMarkedPools.norm P / Z ^ (z - G) ≤ (2 : ℝ) ^ slotCap)
    (hn : 1 / 2 ≤ ProviderMarkedPools.norm n.val / Z ^ r ∧
      ProviderMarkedPools.norm n.val / Z ^ r ≤ 2) :
    Z ^ ProviderMarkedScale.columnLength r z G / (2 : ℝ) ^ width slotCap ≤
        ProviderMarkedPools.norm (forward j P n.val) ∧
      ProviderMarkedPools.norm (forward j P n.val) ≤
        (2 : ℝ) ^ width slotCap * Z ^ ProviderMarkedScale.columnLength r z G := by
  have hx : 0 ≤ ProviderMarkedPools.norm (forward j P n.val) /
      Z ^ ProviderMarkedScale.columnLength r z G :=
    div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)
  have h := quotient_window ((2 : ℝ) ^ slotCap)
    (ProviderMarkedPools.norm j / Z ^ G) (ProviderMarkedPools.norm P / Z ^ (z - G))
    (ProviderMarkedPools.norm (forward j P n.val) / Z ^ ProviderMarkedScale.columnLength r z G)
    (ProviderMarkedPools.norm n.val / Z ^ r) (one_le_pow₀ (by norm_num)) hx hj hp hn
    (normalized_forward Z r z G hZ j P hP n)
  rw [dyadic_width] at h
  have hR : 0 < Z ^ ProviderMarkedScale.columnLength r z G := Real.rpow_pos_of_pos hZ _
  constructor
  · have hb := (le_div_iff₀ hR).mp h.1
    simpa only [div_eq_mul_inv, mul_comm] using hb
  · exact (div_le_iff₀ hR).mp h.2

/-- A fixed selected source is the finite sum of the actual annular
blocks.  The sole support premise is the original radial profile on
positive arguments. -/
theorem selected_eq_blocks {J : ℕ} (slotCap : ℕ)
    (d₀ : MomentData K ω ψ) (u : NonzeroIdeal K)
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (a : Fin J → Ideal (𝓞 K) → ℂ) (good : HeightOneSpectrum (𝓞 K) → Prop)
    (j : Ideal (𝓞 K)) (F : NonzeroIdeal K → SchwartzMap ℝ ℂ)
    (Z r z G : ℝ) (hZ : 0 < Z)
    (hj : ((2 : ℝ) ^ slotCap)⁻¹ ≤ ProviderMarkedPools.norm j / Z ^ G ∧
      ProviderMarkedPools.norm j / Z ^ G ≤ (2 : ℝ) ^ slotCap)
    (hp : ∀ p ∈ tuples lists,
      ((2 : ℝ) ^ slotCap)⁻¹ ≤ ProviderMarkedPools.norm (primeProduct Finset.univ p) / Z ^ (z - G) ∧
      ProviderMarkedPools.norm (primeProduct Finset.univ p) / Z ^ (z - G) ≤ (2 : ℝ) ^ slotCap)
    (hP0 : ∀ p ∈ tuples lists, primeProduct Finset.univ p ≠ 0)
    (hprofile : ∀ y : ℝ, 0 < y → ProviderMarkedLogMellin.profile (F u) y ≠ 0 →
      1 / 2 ≤ y ∧ y ≤ 2) :
    selectedSource (d₀.inverseBackground * d₀.rowCharacter u) lists a good u.val j
      (Z ^ r) (ProviderMarkedLogMellin.profile (F u)) =
      ∑ k ∈ blocks slotCap, SourceMarkedBlockEnergy.block d₀ lists a good j (Z ^ r)
        (scale slotCap k * Z ^ ProviderMarkedScale.columnLength r z G) F u := by
  unfold selectedSource SourceMarkedBlockEnergy.block
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hpP
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  let a₀ : ℂ := originalCoefficient (d₀.inverseBackground * d₀.rowCharacter u) a j p n *
    ProviderMarkedMask.value good u.val n *
    ProviderMarkedMask.value good u.val (j * primeProduct Finset.univ p)
  have hsum := partition slotCap (ProviderMarkedPools.norm
      (forward j (primeProduct Finset.univ p) n))
    (Z ^ ProviderMarkedScale.columnLength r z G) (Real.rpow_pos_of_pos hZ _)
  by_cases hzero : ProviderMarkedLogMellin.profile (F u) (ProviderMarkedPools.norm n / Z ^ r) = 0
  · simp only [hzero, mul_zero, Finset.sum_const_zero]
  · let n' : Source j (primeProduct Finset.univ p) := ⟨n, ProviderMarkedPools.source_of_mem hn⟩
    have hwin := forward_window slotCap Z r z G hZ j (primeProduct Finset.univ p)
      (hP0 p hpP) n' hj (hp p hpP)
      (hprofile _ (div_pos (ProviderMarkedPools.norm_pos n'.property.1.ne_zero)
        (Real.rpow_pos_of_pos hZ _)) hzero)
    have hpart := hsum hwin.1 hwin.2
    calc
      _ = a₀ * ProviderMarkedLogMellin.profile (F u) (ProviderMarkedPools.norm n / Z ^ r) *
          ∑ k ∈ blocks slotCap, Expansion.Dyadic.annularProfile
            (ProviderMarkedPools.norm (forward j (primeProduct Finset.univ p) n) /
              (scale slotCap k * Z ^ ProviderMarkedScale.columnLength r z G)) := by rw [hpart, mul_one]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        dsimp only [a₀]
        ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedSourceSplit

end
