import HeckeGeneral.Analysis.PrimePolynomialAbsoluteBound

/-!
# Absolute prime products at the endpoint

The constants are chosen before the moment data, the row characters, all
masks, and the scales.  The hypotheses concern the actual prime windows:
their number, annular supports, and supremum norms.  The three ideal tests
are irrelevant to this estimate.  Both branches of `pairedRows` are retained.

The only counting input is the proved linear count of integral ideals.
Thus no prime number theorem or zero-free hypothesis is used at κ = 1.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME

open NumberField IsDedekindDomain Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

/-- Every permitted row family is contained in the actual ideal ball.
The constant is uniform in all fields of `MomentData`. -/
theorem exists_rows_card_absolute_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {ω ψ : HeckeCharacter K} (d : MomentData K ω ψ)
      (U : ℝ), 1 ≤ U → ((d.rows U).card : ℝ) ≤ C * U := by
  obtain ⟨C, hC, hcount⟩ := dyadicIdealSupport_linear_count K
  refine ⟨C, hC, ?_⟩
  intro ω ψ d U hU
  have hsub : d.rows U ⊆ dyadicIdealSupport K (U / 2) := by
    intro u hu
    apply (mem_dyadicIdealSupport_iff K
      (div_nonneg (zero_le_one.trans hU) (by norm_num)) u).mpr
    nlinarith [((d.rows_spec U u).mp hu).2]
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcount U hU)

/-- The positive-slot exceptional-character filter and the unrestricted
zero-slot filter only decrease the same ideal-ball count. -/
theorem exists_pairedRows_card_absolute_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {ω ψ : HeckeCharacter K} (d : MomentData K ω ψ)
      (a : RealParameters) (Z : ℝ), 1 ≤ Z → 0 ≤ a.m + a.q →
        ((pairedRows d a Z).card : ℝ) ≤ C * Z ^ (a.m + a.q) := by
  obtain ⟨C, hC, hrows⟩ := exists_rows_card_absolute_bound K
  refine ⟨C, hC, ?_⟩
  intro ω ψ d a Z hZ hM
  exact (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans
    (hrows d (Z ^ (a.m + a.q)) (Real.one_le_rpow hZ hM))

/-- The endpoint prime estimate for an entire family of actual slot products.
The independent height bound is shared by at most `N` prime windows.  The
constant is uniform in rows, masks, characters, lengths, and all scales. -/
theorem exists_slotProductAbsoluteBound (N : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ω ψ : HeckeCharacter K} (d : MomentData K ω ψ)
      (u : NonzeroIdeal K) (Z t V H : ℝ),
      1 ≤ Z → 1 ≤ V → 0 ≤ H → d.geometry.slotCount ≤ N →
      (∀ i, Function.support ((d.geometry.slots i).profile t) ⊆ Ioo (1 : ℝ) 2) →
      (∀ i y, ‖(d.geometry.slots i).profile t y‖ ≤ B * V ^ H) →
      ‖slotProduct d u Z t‖ ^ 2 ≤
        C * Z ^ d.geometry.totalLength * V ^ (2 * (N : ℝ) * H) := by
  obtain ⟨C₀, hC₀, hprime⟩ := exists_norm_primePolynomial_absolute_bound K
  let D : ℝ := max 1 (C₀ * B)
  have hD : 1 ≤ D := le_max_left _ _
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  refine ⟨D ^ (2 * N), pow_pos hD0 _, ?_⟩
  intro ω ψ d u Z t V H hZ hV hH hN hann hprof
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hV0 : 0 < V := zero_lt_one.trans_le hV
  have hVH : 1 ≤ V ^ H := Real.one_le_rpow hV hH
  have hVH0 : 0 ≤ V ^ H := zero_le_one.trans hVH
  have hpow : (V ^ H) ^ (2 * N) = V ^ (2 * (N : ℝ) * H) := by
    rw [← Real.rpow_natCast (V ^ H) (2 * N), ← Real.rpow_mul hV0.le]
    congr 1
    push_cast
    ring
  have hi (i : Fin d.geometry.slotCount) :
      ‖primePolynomial d i u Z t‖ ^ 2 ≤
        (D * V ^ H) ^ 2 * Z ^ (d.geometry.slots i).length := by
    have hp : ‖primePolynomial d i u Z t‖ ≤
        D * V ^ H * Real.sqrt (Z ^ (d.geometry.slots i).length) := by
      calc
        _ ≤ C₀ * (B * V ^ H) * Real.sqrt (Z ^ (d.geometry.slots i).length) :=
          hprime d i u Z t (B * V ^ H) hZ (mul_nonneg hB hVH0)
            (hann i) (hprof i)
        _ = (C₀ * B) * V ^ H * Real.sqrt (Z ^ (d.geometry.slots i).length) :=
          by ring
        _ ≤ D * V ^ H * Real.sqrt (Z ^ (d.geometry.slots i).length) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right 1 (C₀ * B)) hVH0)
            (Real.sqrt_nonneg _)
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity :
      0 ≤ D * V ^ H * Real.sqrt (Z ^ (d.geometry.slots i).length))).mpr hp
    simpa only [mul_pow, Real.sq_sqrt (Real.rpow_nonneg hZ0.le _)] using hs
  have hbase : 1 ≤ (D * V ^ H) ^ 2 :=
    one_le_pow₀ (one_le_mul_of_one_le_of_one_le hD hVH)
  calc
    _ = ∏ i, ‖primePolynomial d i u Z t‖ ^ 2 := by
      rw [slotProduct, norm_prod, Finset.prod_pow]
    _ ≤ ∏ i, (D * V ^ H) ^ 2 * Z ^ (d.geometry.slots i).length :=
      Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _) (fun i _ => hi i)
    _ = ((D * V ^ H) ^ 2) ^ d.geometry.slotCount * Z ^ d.geometry.totalLength := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← Real.rpow_sum_of_pos hZ0]
    _ ≤ ((D * V ^ H) ^ 2) ^ N * Z ^ d.geometry.totalLength :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hbase hN)
        (Real.rpow_nonneg hZ0.le _)
    _ = D ^ (2 * N) * Z ^ d.geometry.totalLength * V ^ (2 * (N : ℝ) * H) := by
      rw [← pow_mul, mul_pow, hpow]
      ring

/-- A single constant controls a whole family of actual prime products.

`N` bounds the number of prime windows.  `B * V ^ H` is a bound on their
actual profiles, with the independent height base `V ≥ 1`.  The conclusion
keeps the exact total slot length.  In particular, the constant cannot be
chosen separately at each external scale or after the row data.
-/
theorem exists_pairedPrimeAbsoluteBound (N : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ω ψ : HeckeCharacter K} (d : MomentData K ω ψ)
      (a : RealParameters) (Z t V H : ℝ),
      1 ≤ Z → 1 ≤ V → 0 ≤ H → 0 ≤ a.m + a.q →
      d.geometry.slotCount ≤ N →
      (∀ i, Function.support ((d.geometry.slots i).profile t) ⊆ Ioo (1 : ℝ) 2) →
      (∀ i y, ‖(d.geometry.slots i).profile t y‖ ≤ B * V ^ H) →
      (∑ u ∈ pairedRows d a Z, ‖slotProduct d u Z t‖ ^ 2) ≤
        C * Z ^ (a.m + a.q + d.geometry.totalLength) * V ^ (2 * (N : ℝ) * H) := by
  obtain ⟨Cₛ, hCₛ, hslots⟩ := exists_slotProductAbsoluteBound K N B hB
  obtain ⟨Cᵣ, hCᵣ, hrows⟩ := exists_pairedRows_card_absolute_bound K
  refine ⟨Cᵣ * Cₛ, mul_pos hCᵣ hCₛ, ?_⟩
  intro ω ψ d a Z t V H hZ hV hH hM hN hann hprof
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hV0 : 0 ≤ V := zero_le_one.trans hV
  have hslot (u : NonzeroIdeal K) :
      ‖slotProduct d u Z t‖ ^ 2 ≤
        Cₛ * Z ^ d.geometry.totalLength * V ^ (2 * (N : ℝ) * H) :=
    hslots d u Z t V H hZ hV hH hN hann hprof
  calc
    _ ≤ ∑ _u ∈ pairedRows d a Z,
        Cₛ * Z ^ d.geometry.totalLength * V ^ (2 * (N : ℝ) * H) :=
      Finset.sum_le_sum (fun u _ => hslot u)
    _ = ((pairedRows d a Z).card : ℝ) *
        (Cₛ * Z ^ d.geometry.totalLength * V ^ (2 * (N : ℝ) * H)) := by
      simp
    _ ≤ (Cᵣ * Z ^ (a.m + a.q)) *
        (Cₛ * Z ^ d.geometry.totalLength * V ^ (2 * (N : ℝ) * H)) :=
      mul_le_mul_of_nonneg_right (hrows d a Z hZ hM) (by positivity)
    _ = (Cᵣ * Cₛ) * Z ^ (a.m + a.q + d.geometry.totalLength) *
        V ^ (2 * (N : ℝ) * H) := by
      rw [Real.rpow_add hZ0 (a.m + a.q) d.geometry.totalLength]
      ring

/-- Height-independent profiles give the exact κ = 1 exponent, including
the empty slot set.  No capacity condition is needed for this estimate. -/
theorem exists_pairedPrimeAbsoluteBound_fixed (N : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ω ψ : HeckeCharacter K} (d : MomentData K ω ψ)
      (a : RealParameters) (Z t : ℝ),
      1 ≤ Z → 0 ≤ a.m + a.q → d.geometry.slotCount ≤ N →
      (∀ i, Function.support ((d.geometry.slots i).profile t) ⊆ Ioo (1 : ℝ) 2) →
      (∀ i y, ‖(d.geometry.slots i).profile t y‖ ≤ B) →
      (∑ u ∈ pairedRows d a Z, ‖slotProduct d u Z t‖ ^ 2) ≤
        C * Z ^ (a.m + a.q + d.geometry.totalLength) := by
  obtain ⟨C, hC, hbound⟩ := exists_pairedPrimeAbsoluteBound K N B hB
  refine ⟨C, hC, ?_⟩
  intro ω ψ d a Z t hZ hM hN hann hprof
  simpa only [Real.one_rpow, mul_one, mul_zero, Real.rpow_zero] using
    hbound d a Z t 1 0 hZ le_rfl le_rfl hM hN hann (by simpa using hprof)

end HeckeSkeleton.Moments.MOM_PRIME
