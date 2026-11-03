import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Square--cube Rankin counting and the powerful-row half-norm budget

The square--cube encoding is injective, while the two ambient Dirichlet
majorants are summable.  These arithmetic inputs imply both the counting
bound and the half-norm mass bound directly.  No counting bound for powerful
objects is assumed, and no dyadic logarithm needs to be absorbed.

The companion `IdealRankin.lean` instantiates this with actual number-field
ideals and Mathlib's proved Dedekind-zeta convergence.
-/

set_option autoImplicit false

namespace HeckeSkeleton.LowEnergy.Rankin

open scoped BigOperators

/-- The factorization of the norm gives exactly the two convergent weights. -/
theorem square_cube_rpow (a b s : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a ^ 2 * b ^ 3) ^ (-s) = a ^ (-(2 * s)) * b ^ (-(3 * s)) := by
  rw [Real.mul_rpow (sq_nonneg _) (pow_nonneg hb _),
    ← Real.rpow_natCast_mul ha 2 (-s), ← Real.rpow_natCast_mul hb 3 (-s)]
  norm_num

/-- Summability of powerful-object weights from an injective square--cube
encoding.  The hypothesis is only the ordinary ambient zeta majorant. -/
theorem summable_square_cube
    {I P : Type*} (q : I → ℝ) (w : P → ℝ) (f : P → I × I)
    (hq : ∀ I, 0 ≤ q I) (hf : Function.Injective f)
    (hw : ∀ p, w p = q (f p).1 ^ 2 * q (f p).2 ^ 3)
    (s : ℝ)
    (h2 : Summable (fun I => q I ^ (-(2 * s))))
    (h3 : Summable (fun I => q I ^ (-(3 * s)))) :
    Summable (fun p => w p ^ (-s)) := by
  have hprod := h2.mul_of_nonneg h3
    (fun I => Real.rpow_nonneg (hq I) _) (fun I => Real.rpow_nonneg (hq I) _)
  have hcomp := hprod.comp_injective hf
  refine hcomp.congr (fun p => ?_)
  rw [hw p, square_cube_rpow _ _ _ (hq _) (hq _)]
  rfl

/-- The same zeta majorant simultaneously controls the number of powerful
rows and the half-norm weight used when frozen row fibres are reassembled. -/
theorem cardinality_and_half_mass
    {I : Type*} (q : I → ℝ) (hq : ∀ i, 0 < q i)
    (eps : ℝ) (heps : 0 < eps)
    (hsum : Summable (fun i => q i ^ (-((1 / 2 : ℝ) + eps)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset I) (X : ℝ), 1 ≤ X →
      (∀ i ∈ s, q i ≤ X) →
      (s.card : ℝ) ≤ C * X ^ ((1 / 2 : ℝ) + eps) ∧
      (∑ i ∈ s, q i ^ (-(1 / 2 : ℝ))) ≤ C * X ^ eps := by
  classical
  let C : ℝ := 1 + ∑' i, q i ^ (-((1 / 2 : ℝ) + eps))
  have htotal : 0 ≤ ∑' i, q i ^ (-((1 / 2 : ℝ) + eps)) :=
    tsum_nonneg (fun i => Real.rpow_nonneg (hq i).le _)
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro s X hX hs
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hweight : (∑ i ∈ s, q i ^ (-((1 / 2 : ℝ) + eps))) ≤ C := by
    have h := hsum.sum_le_tsum s (fun i _ => Real.rpow_nonneg (hq i).le _)
    dsimp [C]
    linarith
  constructor
  · have hpoint (i : I) (hi : i ∈ s) :
        1 ≤ X ^ ((1 / 2 : ℝ) + eps) * q i ^ (-((1 / 2 : ℝ) + eps)) := by
      have hmono := Real.rpow_le_rpow (hq i).le (hs i hi)
        (show 0 ≤ (1 / 2 : ℝ) + eps by linarith)
      have hm := mul_le_mul_of_nonneg_right hmono
        (Real.rpow_nonneg (hq i).le (-((1 / 2 : ℝ) + eps)))
      rw [← Real.rpow_add (hq i), add_neg_cancel, Real.rpow_zero] at hm
      exact hm
    calc
      (s.card : ℝ) = ∑ _i ∈ s, (1 : ℝ) := by simp
      _ ≤ ∑ i ∈ s, X ^ ((1 / 2 : ℝ) + eps) * q i ^ (-((1 / 2 : ℝ) + eps)) :=
        Finset.sum_le_sum hpoint
      _ = X ^ ((1 / 2 : ℝ) + eps) * ∑ i ∈ s, q i ^ (-((1 / 2 : ℝ) + eps)) := by
        rw [Finset.mul_sum]
      _ ≤ X ^ ((1 / 2 : ℝ) + eps) * C :=
        mul_le_mul_of_nonneg_left hweight (Real.rpow_nonneg hXpos.le _)
      _ = C * X ^ ((1 / 2 : ℝ) + eps) := mul_comm _ _
  · have hpoint (i : I) (hi : i ∈ s) :
        q i ^ (-(1 / 2 : ℝ)) ≤ X ^ eps * q i ^ (-((1 / 2 : ℝ) + eps)) := by
      have hmono := Real.rpow_le_rpow (hq i).le (hs i hi) heps.le
      have hm := mul_le_mul_of_nonneg_right hmono
        (Real.rpow_nonneg (hq i).le (-((1 / 2 : ℝ) + eps)))
      rw [← Real.rpow_add (hq i)] at hm
      have hexp : eps + -((1 / 2 : ℝ) + eps) = -(1 / 2 : ℝ) := by ring
      simpa only [hexp] using hm
    calc
      _ ≤ ∑ i ∈ s, X ^ eps * q i ^ (-((1 / 2 : ℝ) + eps)) := Finset.sum_le_sum hpoint
      _ = X ^ eps * ∑ i ∈ s, q i ^ (-((1 / 2 : ℝ) + eps)) := by rw [Finset.mul_sum]
      _ ≤ X ^ eps * C := mul_le_mul_of_nonneg_left hweight (Real.rpow_nonneg hXpos.le _)
      _ = C * X ^ eps := mul_comm _ _

/-- The complete Rankin theorem: the finite counting statement follows from
the injection and the two ordinary (not powerful-restricted) zeta series. -/
theorem powerful_count_and_half_mass_from_encoding
    {I P : Type*} (q : I → ℝ) (w : P → ℝ) (f : P → I × I)
    (hq : ∀ I, 0 < q I) (hf : Function.Injective f)
    (hw : ∀ p, w p = q (f p).1 ^ 2 * q (f p).2 ^ 3)
    (eps : ℝ) (heps : 0 < eps)
    (h2 : Summable (fun I => q I ^ (-(1 + 2 * eps))))
    (h3 : Summable (fun I => q I ^ (-((3 / 2 : ℝ) + 3 * eps)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset P) (X : ℝ), 1 ≤ X →
      (∀ p ∈ s, w p ≤ X) →
      (s.card : ℝ) ≤ C * X ^ ((1 / 2 : ℝ) + eps) ∧
      (∑ p ∈ s, w p ^ (-(1 / 2 : ℝ))) ≤ C * X ^ eps := by
  have hwpos : ∀ p, 0 < w p := by
    intro p
    rw [hw p]
    exact mul_pos (pow_pos (hq _) 2) (pow_pos (hq _) 3)
  have h2' : Summable (fun I => q I ^ (-(2 * ((1 / 2 : ℝ) + eps)))) := by
    convert h2 using 1
    congr 1
    funext i
    congr 1
    ring
  have h3' : Summable (fun I => q I ^ (-(3 * ((1 / 2 : ℝ) + eps)))) := by
    convert h3 using 1
    congr 1
    funext i
    congr 1
    ring
  exact cardinality_and_half_mass w hwpos eps heps
    (summable_square_cube q w f (fun I => (hq I).le) hf hw _ h2' h3')

#print axioms square_cube_rpow
#print axioms summable_square_cube
#print axioms cardinality_and_half_mass
#print axioms powerful_count_and_half_mass_from_encoding

end HeckeSkeleton.LowEnergy.Rankin
