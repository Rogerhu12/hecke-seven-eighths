import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondDivisorMass

/-!
# The actual finite index of both divisor expansions

The two common-support labels, the first shared divisor and independent
second residual divisor are kept as different coordinates. Both complete
occurrence-allocation families belong to the second divisor. This exact
finite carrier is the arithmetic target of the final source-label map.
Additional genuine support, sector and rectangle labels are charged by
their actual fibres, rather than discarded from the sum.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField UniqueFactorizationMonoid

/-- A weighted finite fibre estimate. The supplied fibre cardinalities
are used only for a concrete finite index map; the total weighted mass
is proved by the exact finite partition. -/
theorem sum_weighted_fibres_le {I J : Type*} [Fintype I] [Fintype J]
    (index : I → J) (weight : J → ℝ) (hweight : ∀ j, 0 ≤ weight j)
    (multiplicity : ℝ)
    (hcard : ∀ j, ((Finset.univ.filter (fun i => index i = j)).card : ℝ) ≤ multiplicity) :
    (∑ i : I, weight (index i)) ≤ multiplicity * ∑ j : J, weight j := by
  calc
    _ = ∑ j : J, ∑ i ∈ Finset.univ.filter (fun i => index i = j), weight (index i) :=
      (Finset.sum_fiberwise_of_maps_to
        (fun i (_ : i ∈ (Finset.univ : Finset I)) => Finset.mem_univ (index i))
        (fun i => weight (index i))).symm
    _ = ∑ j : J, ((Finset.univ.filter (fun i => index i = j)).card : ℝ) * weight j := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = ∑ i ∈ Finset.univ.filter (fun i => index i = j), weight j :=
          Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2])
        _ = _ := by simp
    _ ≤ ∑ j : J, multiplicity * weight j :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hcard j) (hweight j))
    _ = _ := by rw [Finset.mul_sum]

namespace CommonSupportMass.TwoDivisorCommonBranch

variable {K : Type} [Field K] [NumberField K]

abbrev Index (b : TwoDivisorCommonBranch (K := K)) :=
  Σ v : b.first, Σ S : b.firstDivisors v.val,
    Σ w : b.second v.val S.val, Σ L : b.secondDivisors v.val S.val w.val,
      (AllocationMass.idealAllocations L.val (b.leftOccurrences v.val S.val w.val L.val)) ×
        (AllocationMass.idealAllocations L.val (b.rightOccurrences v.val S.val w.val L.val))

def indexWeight (b : TwoDivisorCommonBranch (K := K)) (i : b.Index) : ℝ :=
  (1 / (Ideal.absNorm (commonRadical i.1.val.1.1 i.1.val.1.2) : ℝ)) *
    ‖(moebius i.2.1.val : ℂ)‖ *
      (1 / (Ideal.absNorm (commonRadical i.2.2.1.val.1.1 i.2.2.1.val.1.2) : ℝ)) *
        ‖(moebius i.2.2.2.1.val : ℂ)‖ / (Ideal.absNorm i.2.2.2.1.val : ℝ)

theorem indexWeight_nonneg (b : TwoDivisorCommonBranch (K := K)) (i : b.Index) :
    0 ≤ b.indexWeight i := by
  unfold indexWeight
  positivity

/-- Exact enumeration of both complete occurrence allocations. -/
theorem sum_indexWeight (b : TwoDivisorCommonBranch (K := K)) :
    (∑ i : b.Index, b.indexWeight i) = b.mass := by
  unfold mass secondDivisorAllocationMass
  simp only [Index, Fintype.sum_sigma, Fintype.sum_prod_type, indexWeight,
    Finset.sum_coe_sort, Finset.sum_const, nsmul_eq_mul, Nat.cast_mul,
    ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_div]
  ring

/-- Raw support/fibre conditions suffice to bound the mass of a true
decorated source carrier. All arithmetic constants precede its data. -/
theorem uniform_index_mass (N : ℕ) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ s : Ideal (𝓞 K), Squarefree s → s ≠ 0 →
      ∀ b : TwoDivisorCommonBranch (K := K), b.Admissible N B Z s →
      ∀ {I : Type*} [Fintype I] (index : I → b.Index) (multiplicity : ℝ),
      0 ≤ multiplicity →
      (∀ j, ((Finset.univ.filter (fun i => index i = j)).card : ℝ) ≤ multiplicity) →
      (∑ i : I, b.indexWeight (index i)) ≤
        multiplicity * C * Z ^ ε / (Ideal.absNorm s : ℝ) := by
  obtain ⟨C, hC, hmass⟩ := uniform_mass (K := K) N B ε hB hε
  refine ⟨C, hC, ?_⟩
  intro Z hZ s hs hs0 b hb I inst index multiplicity hmultiplicity hcard
  have hf := sum_weighted_fibres_le index b.indexWeight b.indexWeight_nonneg
    multiplicity hcard
  rw [b.sum_indexWeight] at hf
  exact hf.trans ((mul_le_mul_of_nonneg_left
    (hmass Z hZ s hs hs0 b hb) hmultiplicity).trans_eq (by ring))

end CommonSupportMass.TwoDivisorCommonBranch
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CommonSupportMass.TwoDivisorCommonBranch.sum_indexWeight
#print axioms HeckeSkeleton.Moments.EngineStep.CommonSupportMass.TwoDivisorCommonBranch.uniform_index_mass
