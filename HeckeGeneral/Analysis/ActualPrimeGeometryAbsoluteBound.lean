import HeckeGeneral.Analysis.PrimePolynomialAbsoluteBound
import Mathlib.Analysis.Normed.Group.Bounded

/-!
Fixed smooth prime geometry supplies its own uniform profile constant.
All constants below precede arbitrary MomentData, slot characters, rows,
scales and heights. The one data wrapper installs precisely the fixed
actual geometry and the supplied characters, retaining every other field,
including the common mask. These are absolute prime/slot estimates only;
there is no paired plain moment, canonical admissibility or P estimate.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain Set
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

/-- Compact support and continuity give a positive norm bound without
introducing a new profile-bound assumption. -/
theorem smoothAnnularTest_exists_pos_norm_bound (W : SmoothAnnularTest) :
    ∃ B : ℝ, 0 < B ∧ ∀ y, ‖W.toFun y‖ ≤ B := by
  have hs : HasCompactSupport W.toFun :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc W.support
  obtain ⟨B, hB⟩ := hs.exists_bound_of_continuous W.smooth.continuous
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro y
  exact (hB y).trans (le_max_right _ _)

/-- The fixed actual profiles ignore height. A single positive bound is
chosen from g before any characters or rows are selected. -/
theorem exists_actualMomentPrimeGeometry_profile_bound (g : PrimeWindowGeometry) :
    ∃ B : ℝ, 0 < B ∧ ∀ (i : Fin g.slots) (t y : ℝ),
      ‖((momentPrimeGeometry K g).slots i).profile t y‖ ≤ B := by
  have hb : ∀ i : Fin g.slots, ∃ B : ℝ, 0 < B ∧
      ∀ y, ‖(g.weight i).toFun y‖ ≤ B :=
    fun i => smoothAnnularTest_exists_pos_norm_bound (g.weight i)
  choose B hB hbound using hb
  have hsum : 0 ≤ ∑ i : Fin g.slots, B i :=
    Finset.sum_nonneg (fun i _ => (hB i).le)
  refine ⟨1 + ∑ i : Fin g.slots, B i, by linarith, ?_⟩
  intro i t y
  change ‖(g.weight i).toFun y‖ ≤ 1 + ∑ j : Fin g.slots, B j
  have hi : B i ≤ ∑ j : Fin g.slots, B j :=
    Finset.single_le_sum (fun j _ => (hB j).le) (Finset.mem_univ i)
  exact (hbound i y).trans (by linarith)

/-- Install the fixed real prime geometry with arbitrary genuine Hecke
slot characters. Common masks, row characters, row enumeration, witness
tests, backgrounds and orientations are the original data fields. -/
abbrev actualPrimeGeometryMomentData {ω ψ : HeckeCharacter K}
    (g : PrimeWindowGeometry) (d : MomentData K ω ψ)
    (χ : Fin g.slots → HeckeCharacter K) : MomentData K ω ψ :=
  { d with geometry := momentPrimeGeometry K g, slotCoefficient := χ }

/-- For fixed g, C and A are chosen before all later data/characters/rows
and all real heights. The actual full slot-square exponent is 1/6.
No nonramification, mask deletion or prime-density premise is used. -/
theorem exists_actualPrimeGeometry_absolute_bounds (g : PrimeWindowGeometry) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      (∀ {ω ψ : HeckeCharacter K} (d : MomentData K ω ψ)
        (χ : Fin g.slots → HeckeCharacter K) (i : Fin g.slots)
        (u : NonzeroIdeal K) (Z t : ℝ), 1 ≤ Z →
        ‖primePolynomial (actualPrimeGeometryMomentData K g d χ) i u Z t‖ ≤
          C * Real.sqrt (primeScale g Z)) ∧
      (∀ {ω ψ : HeckeCharacter K} (d : MomentData K ω ψ)
        (χ : Fin g.slots → HeckeCharacter K)
        (u : NonzeroIdeal K) (Z t : ℝ), 1 ≤ Z →
        ‖slotProduct (actualPrimeGeometryMomentData K g d χ) u Z t‖ ^ 2 ≤
          A * Z ^ (1 / 6 : ℝ)) := by
  obtain ⟨C₀, hC₀, hp⟩ := exists_norm_primePolynomial_absolute_bound K
  obtain ⟨B, hB, hprof⟩ := exists_actualMomentPrimeGeometry_profile_bound K g
  let C : ℝ := C₀ * B
  have hC : 0 < C := mul_pos hC₀ hB
  let A : ℝ := ∏ _i : Fin g.slots, C ^ 2
  have hA : 0 < A := Finset.prod_pos (fun _ _ => sq_pos_of_pos hC)
  have hprime : ∀ {ω ψ : HeckeCharacter K} (d : MomentData K ω ψ)
      (χ : Fin g.slots → HeckeCharacter K) (i : Fin g.slots)
      (u : NonzeroIdeal K) (Z t : ℝ), 1 ≤ Z →
      ‖primePolynomial (actualPrimeGeometryMomentData K g d χ) i u Z t‖ ≤
        C * Real.sqrt (primeScale g Z) := by
    intro ω ψ d χ i u Z t hZ
    exact hp (actualPrimeGeometryMomentData K g d χ) i u Z t B hZ hB.le
      (g.support_annular i) (hprof i t)
  refine ⟨C, A, hC, hA, hprime, ?_⟩
  intro ω ψ d χ u Z t hZ
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  let M := actualPrimeGeometryMomentData K g d χ
  change ‖slotProduct M u Z t‖ ^ 2 ≤ A * Z ^ (1 / 6 : ℝ)
  have hi (i : Fin g.slots) :
      ‖primePolynomial M i u Z t‖ ^ 2 ≤
        C ^ 2 * Z ^ ((momentPrimeGeometry K g).slots i).length := by
    have h := (sq_le_sq₀ (norm_nonneg _) (by positivity :
        0 ≤ C * Real.sqrt (primeScale g Z))).mpr
      (hprime d χ i u Z t hZ)
    simpa only [M, momentPrimeGeometry, analyticMomentPrimeWindow, primeScale, mul_pow,
      Real.sq_sqrt (Real.rpow_nonneg hZ0.le _)] using h
  calc
    _ = ∏ i : Fin g.slots, ‖primePolynomial M i u Z t‖ ^ 2 := by
      rw [slotProduct, norm_prod, Finset.prod_pow]
      rfl
    _ ≤ ∏ i : Fin g.slots,
        C ^ 2 * Z ^ ((momentPrimeGeometry K g).slots i).length :=
      Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _) (fun i _ => hi i)
    _ = A * Z ^ (momentPrimeGeometry K g).totalLength := by
      change (∏ i : Fin g.slots,
          C ^ 2 * Z ^ ((momentPrimeGeometry K g).slots i).length) =
        (∏ _i : Fin g.slots, C ^ 2) *
          Z ^ (∑ i : Fin g.slots, ((momentPrimeGeometry K g).slots i).length)
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hZ0]
    _ = A * Z ^ (1 / 6 : ℝ) := by
      rw [momentPrimeGeometry_totalLength]

end HeckeGeneral.ThetaSkeleton.Physical
