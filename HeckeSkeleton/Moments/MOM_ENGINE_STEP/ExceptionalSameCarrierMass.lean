import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FiniteBranchIndex
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FinitePhase

/-!
# The exceptional divisor saving pays its actual finite carrier

The exceptional bound retains the second divisor dyad as `Z ^ -r`.
The original upper norm window turns this into the harmonic weight of
that same second divisor with one mesh-width cost.  Both common-support
labels, the first divisor, and both complete second-divisor allocations
are exactly the canonical index used for ordinary children.  Additional
finite source labels are paid by the fibres of their actual index map.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters UniqueFactorizationMonoid

namespace CommonSupportMass.TwoDivisorCommonBranch

variable {K : Type} [Field K] [NumberField K]

def exceptionalDyadWeight (b : TwoDivisorCommonBranch (K := K))
    (Z r : ℝ) (i : b.Index) : ℝ :=
  (1 / (Ideal.absNorm (commonRadical i.1.val.1.1 i.1.val.1.2) : ℝ)) *
    ‖(moebius i.2.1.val : ℂ)‖ *
    (1 / (Ideal.absNorm (commonRadical i.2.2.1.val.1.1 i.2.2.1.val.1.2) : ℝ)) *
    ‖(moebius i.2.2.2.1.val : ℂ)‖ * Z ^ (-r)

theorem exceptionalDyadWeight_nonneg (b : TwoDivisorCommonBranch (K := K))
    (Z r : ℝ) (hZ : 0 ≤ Z) (i : b.Index) : 0 ≤ b.exceptionalDyadWeight Z r i := by
  unfold exceptionalDyadWeight
  positivity

private theorem dyad_weight_le_harmonic (Z r mesh N factor : ℝ)
    (hZ : 0 < Z) (hN : 0 < N) (hfactor : 0 ≤ factor)
    (hwindow : N ≤ Z ^ (r + mesh)) :
    factor * Z ^ (-r) ≤ Z ^ mesh * (factor / N) := by
  have hi : Z ^ (-r) ≤ Z ^ mesh / N := by
    apply (le_div_iff₀ hN).mpr
    calc
      _ ≤ Z ^ (-r) * Z ^ (r + mesh) :=
        mul_le_mul_of_nonneg_left hwindow (Real.rpow_nonneg hZ.le _)
      _ = Z ^ mesh := by
        rw [← Real.rpow_add hZ]
        congr 1
        ring
  calc
    _ ≤ factor * (Z ^ mesh / N) := mul_le_mul_of_nonneg_left hi hfactor
    _ = _ := by ring

/-- No count of the second-divisor carrier is assumed: its original
upper norm window produces the precise harmonic denominator already
present in the proved two-divisor mass theorem. -/
theorem exceptionalDyadWeight_le_indexWeight (b : TwoDivisorCommonBranch (K := K))
    (Z r mesh : ℝ) (hZ : 0 < Z) (i : b.Index)
    (hL : i.2.2.2.1.val ≠ 0)
    (hwindow : (Ideal.absNorm i.2.2.2.1.val : ℝ) ≤ Z ^ (r + mesh)) :
    b.exceptionalDyadWeight Z r i ≤ Z ^ mesh * b.indexWeight i := by
  have hnorm : (0 : ℝ) < Ideal.absNorm i.2.2.2.1.val :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hL))
  unfold exceptionalDyadWeight indexWeight
  exact dyad_weight_le_harmonic Z r mesh _ _ hZ hnorm (by positivity) hwindow

/-- Select the arithmetic constant before introducing the dependent
allocation carrier.  The choice theorem itself mentions only `b.mass`. -/
private def exceptionalArithmeticConstant (N : ℕ) (B ε : ℝ)
    (hB : 0 ≤ B) (hε : 0 < ε) : ℝ :=
  Classical.choose (uniform_mass (K := K) N B ε hB hε)

private theorem exceptionalArithmeticConstant_pos (N : ℕ) (B ε : ℝ)
    (hB : 0 ≤ B) (hε : 0 < ε) :
    0 < exceptionalArithmeticConstant (K := K) N B ε hB hε :=
  (Classical.choose_spec (uniform_mass (K := K) N B ε hB hε)).1

private theorem exceptionalArithmeticConstant_mass (N : ℕ) (B ε : ℝ)
    (hB : 0 ≤ B) (hε : 0 < ε)
    (Z : ℝ) (hZ : 1 ≤ Z) (s : Ideal (𝓞 K)) (hs : Squarefree s) (hs0 : s ≠ 0)
    (b : TwoDivisorCommonBranch (K := K)) (hb : b.Admissible N B Z s) :
    b.mass ≤ exceptionalArithmeticConstant (K := K) N B ε hB hε *
      Z ^ ε / (Ideal.absNorm s : ℝ) :=
  (Classical.choose_spec (uniform_mass (K := K) N B ε hB hε)).2 Z hZ s hs hs0 b hb

/-- Finite-sum transport on abstract types.  In particular, deciding
equality in a fibre never unfolds the actual nested allocation carrier. -/
private theorem weighted_sum_bound_of_fibres
    {I J : Type*} [Fintype I] [Fintype J]
    (index : I → J) (weight : J → ℝ) (hweight : ∀ j, 0 ≤ weight j)
    (summand : I → ℝ) (scale massBound multiplicity : ℝ)
    (hscale : 0 ≤ scale) (hmultiplicity : 0 ≤ multiplicity)
    (cardDecision : ∀ j : J, DecidablePred (fun i : I => index i = j))
    (hcard : ∀ j, ((@Finset.filter I (fun i => index i = j)
      (cardDecision j) Finset.univ).card : ℝ) ≤ multiplicity)
    (hpoint : ∀ i, summand i ≤ scale * weight (index i))
    (hmass : (∑ j : J, weight j) ≤ massBound) :
    (∑ i : I, summand i) ≤ scale * (multiplicity * massBound) := by
  have hfibre : (∑ i : I, weight (index i)) ≤ multiplicity * ∑ j : J, weight j :=
    sum_weighted_fibres_le (I := I) (J := J) index weight hweight multiplicity
      (fun j => calc
        _ = ((@Finset.filter I (fun i => index i = j)
          (cardDecision j) Finset.univ).card : ℝ) := by congr
        _ ≤ multiplicity := hcard j)
  calc
    _ ≤ ∑ i : I, scale * weight (index i) := Finset.sum_le_sum (fun i _ => hpoint i)
    _ = scale * ∑ i : I, weight (index i) := (Finset.mul_sum _ _ _).symm
    _ ≤ scale * (multiplicity * ∑ j : J, weight j) :=
      mul_le_mul_of_nonneg_left hfibre hscale
    _ ≤ scale * (multiplicity * massBound) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hmass hmultiplicity) hscale

private theorem dyad_mass_scale_identity (Z ε mesh multiplicity C norm : ℝ)
    (hZ : 0 < Z) :
    Z ^ mesh * (multiplicity * (C * Z ^ ε / norm)) =
      multiplicity * C * Z ^ (ε + mesh) / norm := by
  rw [Real.rpow_add hZ]
  ring

private theorem admissible_index_second_divisor_ne_zero
    (N : ℕ) (B Z : ℝ) (s : Ideal (𝓞 K))
    (b : TwoDivisorCommonBranch (K := K)) (hb : b.Admissible N B Z s)
    (j : b.Index) : j.2.2.2.1.val ≠ 0 :=
  hb.second_divisor_ne_zero j.1.val j.1.property
    j.2.1.val j.2.1.property j.2.2.1.val j.2.2.1.property
    j.2.2.2.1.val j.2.2.2.1.property

/-- The same fixed arithmetic constant controls the actual decorated
exceptional carrier.  Only its original ideal windows and actual fibre
cardinalities enter; no exceptional sum or terminal budget is an input. -/
theorem uniform_exceptional_dyad_mass (N : ℕ) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ s : Ideal (𝓞 K), Squarefree s → s ≠ 0 →
      ∀ b : TwoDivisorCommonBranch (K := K), b.Admissible N B Z s →
      ∀ {I : Type*} [Fintype I] (index : I → b.Index) (multiplicity mesh : ℝ),
      0 ≤ multiplicity →
      (∀ j, ((Finset.univ.filter (fun i => index i = j)).card : ℝ) ≤ multiplicity) →
      ∀ lower : I → ℝ,
      (∀ i, (Ideal.absNorm (index i).2.2.2.1.val : ℝ) ≤ Z ^ (lower i + mesh)) →
      (∑ i : I, b.exceptionalDyadWeight Z (lower i) (index i)) ≤
        multiplicity * C * Z ^ (ε + mesh) / (Ideal.absNorm s : ℝ) := by
  let C : ℝ := exceptionalArithmeticConstant (K := K) N B ε hB hε
  refine ⟨C, exceptionalArithmeticConstant_pos (K := K) N B ε hB hε, ?_⟩
  intro Z hZ s hs hs0 b hbranch I inst index multiplicity mesh hmult hcard lower hwindow
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hmass : b.mass ≤ C * Z ^ ε / (Ideal.absNorm s : ℝ) :=
    exceptionalArithmeticConstant_mass N B ε hB hε Z hZ s hs hs0 b hbranch
  have hindex : (∑ j : b.Index, b.indexWeight j) ≤
      C * Z ^ ε / (Ideal.absNorm s : ℝ) :=
    b.sum_indexWeight.le.trans hmass
  have hi (i : I) : b.exceptionalDyadWeight Z (lower i) (index i) ≤
      Z ^ mesh * b.indexWeight (index i) :=
    b.exceptionalDyadWeight_le_indexWeight Z (lower i) mesh hz (index i)
      (admissible_index_second_divisor_ne_zero N B Z s b hbranch (index i)) (hwindow i)
  have hsum : (∑ i : I, b.exceptionalDyadWeight Z (lower i) (index i)) ≤
      Z ^ mesh * (multiplicity * (C * Z ^ ε / (Ideal.absNorm s : ℝ))) :=
    weighted_sum_bound_of_fibres (I := I) (J := b.Index)
      index (fun j : b.Index => b.indexWeight j) (fun j => b.indexWeight_nonneg j)
      (fun i : I => b.exceptionalDyadWeight Z (lower i) (index i))
      (Z ^ mesh) (C * Z ^ ε / (Ideal.absNorm s : ℝ)) multiplicity
      (Real.rpow_nonneg hz.le mesh) hmult (fun _ _ => inferInstance) hcard hi hindex
  exact hsum.trans_eq (dyad_mass_scale_identity Z ε mesh multiplicity C
    (Ideal.absNorm s : ℝ) hz)

end CommonSupportMass.TwoDivisorCommonBranch

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CommonSupportMass.TwoDivisorCommonBranch.uniform_exceptional_dyad_mass
