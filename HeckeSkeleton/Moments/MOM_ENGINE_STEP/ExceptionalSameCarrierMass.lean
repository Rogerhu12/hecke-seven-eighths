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
  have hi : Z ^ (-r) ≤ Z ^ mesh / (Ideal.absNorm i.2.2.2.1.val : ℝ) := by
    apply (le_div_iff₀ hnorm).mpr
    calc
      _ ≤ Z ^ (-r) * Z ^ (r + mesh) :=
        mul_le_mul_of_nonneg_left hwindow (Real.rpow_nonneg hZ.le _)
      _ = Z ^ mesh := by
        rw [← Real.rpow_add hZ]
        congr 1
        ring
  have hp := mul_le_mul_of_nonneg_left hi
    (show 0 ≤ (1 / (Ideal.absNorm (commonRadical i.1.val.1.1 i.1.val.1.2) : ℝ)) *
      ‖(moebius i.2.1.val : ℂ)‖ *
      (1 / (Ideal.absNorm (commonRadical i.2.2.1.val.1.1 i.2.2.1.val.1.2) : ℝ)) *
      ‖(moebius i.2.2.2.1.val : ℂ)‖ by positivity)
  convert hp using 1 <;> unfold exceptionalDyadWeight indexWeight <;> ring

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
  obtain ⟨C, hC, hb⟩ := uniform_index_mass (K := K) N B ε hB hε
  refine ⟨C, hC, ?_⟩
  intro Z hZ s hs hs0 b hbranch I inst index multiplicity mesh hmult hcard lower hwindow
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hi (i : I) : b.exceptionalDyadWeight Z (lower i) (index i) ≤
      Z ^ mesh * b.indexWeight (index i) := by
    apply b.exceptionalDyadWeight_le_indexWeight Z (lower i) mesh hz (index i)
    · exact hbranch.second_divisor_ne_zero (index i).1.val (index i).1.property
        (index i).2.1.val (index i).2.1.property
        (index i).2.2.1.val (index i).2.2.1.property
        (index i).2.2.2.1.val (index i).2.2.2.1.property
    · exact hwindow i
  calc
    _ ≤ ∑ i : I, Z ^ mesh * b.indexWeight (index i) := Finset.sum_le_sum (fun i _ => hi i)
    _ = Z ^ mesh * ∑ i : I, b.indexWeight (index i) := by rw [Finset.mul_sum]
    _ ≤ Z ^ mesh * (multiplicity * C * Z ^ ε / (Ideal.absNorm s : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (hb Z hZ s hs hs0 b hbranch index multiplicity hmult hcard)
        (Real.rpow_nonneg hz.le _)
    _ = _ := by rw [Real.rpow_add hz]; ring

end CommonSupportMass.TwoDivisorCommonBranch

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CommonSupportMass.TwoDivisorCommonBranch.uniform_exceptional_dyad_mass
