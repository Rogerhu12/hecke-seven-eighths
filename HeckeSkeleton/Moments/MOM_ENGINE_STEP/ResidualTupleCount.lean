import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstZeroDiagonal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AmplifierGaussExtraction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ValuationAllocation
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.Pool

/-!
# The actual factor tuples after removing an amplifier prime

Removing the prime from every factor need not preserve injectivity of the
original whole index.  The lost information is its finite valuation
allocation.  Here the residual ideals are constructed by the actual
amplifier quotient provider; their product and the bound for their fibres
are proved from reconstruction.  No residual injection or diagonal count
is assumed.  All statements include the empty tuple.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open UniqueFactorizationMonoid MaskedQuotientCRT

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}

def actualFactorValuation {k : ℕ} (p : ExteriorPrime A)
    (f : Fin k → A.Exterior) : Fin k → ℕ := fun i => primeExponent p (f i)

def actualResidualFactorTuple {k : ℕ} (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (f : Fin k → A.Exterior) : Fin k → Ideal (𝓞 K) :=
  fun i => (amplifierResidualPresentation C p (primeExponent p (f i)) (f i) rfl).residual.val

theorem actual_factor_reconstructed {k : ℕ} (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (f : Fin k → A.Exterior) (i : Fin k) :
    (f i).val = p.val.asIdeal ^ actualFactorValuation p f i *
      actualResidualFactorTuple C p f i :=
  (amplifierResidualPresentation C p (primeExponent p (f i)) (f i) rfl).reconstructed

theorem actual_factor_valuation_sum {k : ℕ} (p : ExteriorPrime A)
    (f : Fin k → A.Exterior) (I : A.Exterior)
    (hproduct : PowerfulDiagonal.tupleIdeal (fun i => (f i).val) = I.val) :
    (∑ i, actualFactorValuation p f i) = primeExponent p I := by
  have hc := ValuationAllocation.count_product Finset.univ (fun i => (f i).val)
    p.val.asIdeal (fun i _ => (f i).property.1)
  change (normalizedFactors (PowerfulDiagonal.tupleIdeal (fun i => (f i).val))).count
      p.val.asIdeal = ∑ i, actualFactorValuation p f i at hc
  rw [hproduct] at hc
  exact hc.symm

theorem actual_residual_tuple_reconstructed {k : ℕ}
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (f : Fin k → A.Exterior) :
    PowerfulDiagonal.tupleIdeal (fun i => (f i).val) =
      p.val.asIdeal ^ (∑ i, actualFactorValuation p f i) *
        PowerfulDiagonal.tupleIdeal (actualResidualFactorTuple C p f) := by
  unfold PowerfulDiagonal.tupleIdeal
  calc
    _ = ∏ i, p.val.asIdeal ^ actualFactorValuation p f i *
        actualResidualFactorTuple C p f i :=
      Finset.prod_congr rfl (fun i _ => actual_factor_reconstructed C p f i)
    _ = _ := by rw [Finset.prod_mul_distrib, ← Finset.prod_pow_eq_pow_sum]

/-- The factorwise actual quotients multiply to the actual whole-column
quotient, even though their allowed generators were chosen independently. -/
theorem actual_residual_tuple_product {k n : ℕ}
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (f : Fin k → A.Exterior) (I : A.Exterior)
    (hproduct : PowerfulDiagonal.tupleIdeal (fun i => (f i).val) = I.val)
    (hvaluation : primeExponent p I = n)
    (R : AmplifierResidualPresentation C p n I) :
    PowerfulDiagonal.tupleIdeal (actualResidualFactorTuple C p f) = R.residual.val := by
  apply mul_left_cancel₀ (pow_ne_zero n p.val.ne_bot)
  have he := actual_residual_tuple_reconstructed C p f
  rw [actual_factor_valuation_sum p f I hproduct, hvaluation, hproduct] at he
  exact he.symm.trans R.reconstructed

theorem AmplifierResidualPresentation.original_valuation {n : ℕ}
    {C : A.GeneralArithmeticContext σ η hS} {p : ExteriorPrime A} {I : A.Exterior}
    (R : AmplifierResidualPresentation C p n I) : primeExponent p I = n := by
  change (normalizedFactors I.val).count p.val.asIdeal = n
  rw [R.reconstructed, PrimePowerQuotientSupport.count_prime_power_mul
    p.val n R.residual.val R.residual.property.1]
  change n + primeExponent p R.residual = n
  rw [R.primitive, add_zero]

theorem actual_residual_pair_tuple_product {k nLeft nRight : ℕ}
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (f : Fin k → A.Exterior) (I J : A.Exterior)
    (hproduct : PowerfulDiagonal.tupleIdeal (fun i => (f i).val) = I.val * J.val)
    (left : AmplifierResidualPresentation C p nLeft I)
    (right : AmplifierResidualPresentation C p nRight J) :
    PowerfulDiagonal.tupleIdeal (actualResidualFactorTuple C p f) =
      left.residual.val * right.residual.val := by
  have hs := actual_factor_valuation_sum p f (ExteriorIdealEuler.mul I J) hproduct
  rw [primeExponent_exterior_mul, left.original_valuation, right.original_valuation] at hs
  have he := actual_residual_tuple_reconstructed C p f
  rw [hs, hproduct, left.reconstructed, right.reconstructed] at he
  apply mul_left_cancel₀ (pow_ne_zero (nLeft + nRight) p.val.ne_bot)
  calc
    _ = (p.val.asIdeal ^ nLeft * left.residual.val) *
        (p.val.asIdeal ^ nRight * right.residual.val) := he.symm
    _ = _ := by rw [pow_add]; ring

/-- For a fixed allocation the original tuple is recovered literally. -/
theorem actual_residual_tuple_injective_on_allocation {α : Type*} {k : ℕ}
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (S : Finset α) (f : α → Fin k → A.Exterior)
    (hinj : Set.InjOn (fun x i => (f x i).val) (S : Set α))
    (allocation : Fin k → ℕ)
    (hallocation : ∀ x ∈ S, actualFactorValuation p (f x) = allocation) :
    Set.InjOn (fun x => actualResidualFactorTuple C p (f x)) (S : Set α) := by
  intro x hx y hy he
  apply hinj hx hy
  funext i
  rw [actual_factor_reconstructed C p (f x) i,
    actual_factor_reconstructed C p (f y) i,
    hallocation x hx, hallocation y hy, congrFun he i]

/-- Without fixing the allocation, every fibre still has a fixed finite
size.  The bound is independent of the prime, the ideals and the scale. -/
theorem actual_residual_tuple_fiber_card {α : Type*} {k n : ℕ}
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (S : Finset α) (f : α → Fin k → A.Exterior)
    (hinj : Set.InjOn (fun x i => (f x i).val) (S : Set α))
    (hvaluation : ∀ x ∈ S, ∑ i, actualFactorValuation p (f x) i = n)
    (v : Fin k → Ideal (𝓞 K)) :
    (S.filter (fun x => actualResidualFactorTuple C p (f x) = v)).card ≤ (n + 1) ^ k := by
  let T := S.filter (fun x => actualResidualFactorTuple C p (f x) = v)
  have hi : Set.InjOn (fun x => actualFactorValuation p (f x)) (T : Set α) := by
    intro x hx y hy he
    apply hinj (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1
    funext i
    rw [actual_factor_reconstructed C p (f x) i,
      actual_factor_reconstructed C p (f y) i,
      congrFun he i, (Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2]
  have hs : T.image (fun x => actualFactorValuation p (f x)) ⊆
      ValuationAllocation.choices k n := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
    exact ValuationAllocation.mem_choices_of_sum _
      (hvaluation x (Finset.mem_filter.mp hx).1)
  have hc := (Finset.card_le_card hs).trans (ValuationAllocation.card_choices_le k n)
  rw [Finset.card_image_of_injOn hi] at hc
  exact hc

namespace PowerfulDiagonal

/-- The same powerful-ideal estimate with a proved finite fibre bound.
The coefficient remains whole and the multiplicity is paid exactly once. -/
theorem powerful_whole_index_normalized_sum_of_fibers (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : Type*} (S : Finset α)
      (factors : α → Fin k → Ideal (𝓞 K)) (multiplicity : ℕ),
      (∀ v, (S.filter (fun x => factors x = v)).card ≤ multiplicity) →
      ∀ (X Amp : ℝ) (c : α → ℂ), 1 ≤ X → 0 ≤ Amp →
      (∀ v ∈ S, tupleIdeal (factors v) ≠ 0) →
      (∀ v ∈ S, (Ideal.absNorm (tupleIdeal (factors v)) : ℝ) ≤ X) →
      (∀ v ∈ S, ¬Powerful (tupleIdeal (factors v)) → c v = 0) →
      (∀ v ∈ S, ‖c v‖ ≤ Amp / Real.sqrt X) →
      ‖∑ v ∈ S, c v‖ ≤ C * multiplicity * Amp * X ^ ε := by
  obtain ⟨C, hC, hcount⟩ := powerful_tuple_count (K := K) k ε hε
  refine ⟨C, hC, ?_⟩
  intro α S factors multiplicity hfiber X Amp c hX hAmp hzero hnorm hvanish hcoeff
  let T := S.filter (fun v => Powerful (tupleIdeal (factors v)))
  have hc := hcount (T.image factors) X hX
    (by intro v hv; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
        exact hzero w (Finset.mem_filter.mp hw).1)
    (by intro v hv; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
        exact (Finset.mem_filter.mp hw).2)
    (by intro v hv; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
        exact hnorm w (Finset.mem_filter.mp hw).1)
  have hf (v) : ((T.filter (fun x => factors x = v)).card : ℝ) ≤ multiplicity := by
    exact_mod_cast (Finset.card_le_card (show T.filter (fun x => factors x = v) ⊆
      S.filter (fun x => factors x = v) from fun x hx =>
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1,
          (Finset.mem_filter.mp hx).2⟩)).trans (hfiber v)
  have hTc : (T.card : ℝ) ≤ (multiplicity : ℝ) * (T.image factors).card := by
    simpa using positive_pushforward_bound T factors (fun _ => (1 : ℝ))
      (multiplicity : ℝ) (fun _ _ => zero_le_one) (fun v _ => hf v)
  have hsum : (∑ v ∈ S, c v) = ∑ v ∈ T, c v := by
    dsimp only [T]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hp : Powerful (tupleIdeal (factors v))
    · simp only [hp, ite_true]
    · simp only [hp, ite_false, hvanish v hv hp]
  have hsqrt : 0 < Real.sqrt X := Real.sqrt_pos.mpr (zero_lt_one.trans_le hX)
  rw [hsum]
  calc
    _ ≤ ∑ v ∈ T, ‖c v‖ := norm_sum_le _ _
    _ ≤ ∑ _v ∈ T, Amp / Real.sqrt X :=
      Finset.sum_le_sum (fun v hv => hcoeff v (Finset.mem_filter.mp hv).1)
    _ = (T.card : ℝ) * (Amp / Real.sqrt X) := by simp
    _ ≤ ((multiplicity : ℝ) * (C * Real.sqrt X * X ^ ε)) * (Amp / Real.sqrt X) :=
      mul_le_mul_of_nonneg_right
        (hTc.trans (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)))
        (div_nonneg hAmp hsqrt.le)
    _ = C * multiplicity * Amp * X ^ ε := by field_simp [hsqrt.ne'] <;> ring

end PowerfulDiagonal

/-- The genuine common-support label is unique, so it introduces no
additional fibre multiplicity in either source transform. -/
theorem common_label_powerful_normalized_sum_of_fibers
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ Cbound : ℝ, 0 < Cbound ∧
    ∀ {ι κ : Type*} (left : Finset ι) (right : Finset κ)
      (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
      (factors : ι × κ → Fin k → Ideal (𝓞 K)) (multiplicity : ℕ),
    (∀ v, ((left ×ˢ right).filter (fun ij => factors ij = v)).card ≤ multiplicity) →
    (∀ ij ∈ left ×ˢ right, PowerfulDiagonal.tupleIdeal (factors ij) =
      (fullI ij.1).val * (fullJ ij.2).val) →
    ∀ N Amp : ℝ, 1 ≤ N → 0 ≤ Amp →
    (∀ ij ∈ left ×ˢ right,
      (Ideal.absNorm ((fullI ij.1).val * (fullJ ij.2).val) : ℝ) ≤ N) →
    ∀ coeff : FirstZeroLabel left right fullI fullJ × (ι × κ) → ℂ,
    (∀ v ∈ firstZeroPairs left right fullI fullJ,
      ¬ Powerful ((fullI v.2.1).val * (fullJ v.2.2).val) → coeff v = 0) →
    (∀ v ∈ firstZeroPairs left right fullI fullJ, ‖coeff v‖ ≤ Amp / Real.sqrt N) →
    ‖∑ v ∈ firstZeroPairs left right fullI fullJ, coeff v‖ ≤
      Cbound * multiplicity * Amp * N ^ ε := by
  obtain ⟨Cbound, hCbound, hcount⟩ :=
    PowerfulDiagonal.powerful_whole_index_normalized_sum_of_fibers (K := K) k ε hε
  refine ⟨Cbound, hCbound, ?_⟩
  intro ι κ left right fullI fullJ factors multiplicity hfiber hfactor
    N Amp hN hAmp hnorm coeff hzero hcoef
  have hij (v) (hv : v ∈ firstZeroPairs left right fullI fullJ) : v.2 ∈ left ×ˢ right := by
    have hv' := (mem_firstZeroPairs left right fullI fullJ v).mp hv
    exact Finset.mem_product.mpr ⟨hv'.1, hv'.2.1⟩
  apply hcount (firstZeroPairs left right fullI fullJ) (fun v => factors v.2)
    multiplicity ?_ N Amp coeff hN hAmp
  · intro w
    let T := (firstZeroPairs left right fullI fullJ).filter (fun v => factors v.2 = w)
    have hi : Set.InjOn Prod.snd (T : Set _) := by
      intro v hv u hu he
      exact firstZeroPairs_projection_injective left right fullI fullJ
        (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hu).1 he
    have hs : T.image Prod.snd ⊆ (left ×ˢ right).filter (fun ij => factors ij = w) := by
      intro ij hij'
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hij'
      exact Finset.mem_filter.mpr ⟨hij v (Finset.mem_filter.mp hv).1,
        (Finset.mem_filter.mp hv).2⟩
    have hc := (Finset.card_le_card hs).trans (hfiber w)
    rw [Finset.card_image_of_injOn hi] at hc
    exact hc
  · intro v hv
    rw [hfactor v.2 (hij v hv)]
    exact mul_ne_zero (fullI v.2.1).property.1 (fullJ v.2.2).property.1
  · intro v hv
    rw [hfactor v.2 (hij v hv)]
    exact hnorm v.2 (hij v hv)
  · intro v hv hbad
    apply hzero v hv
    simpa only [hfactor v.2 (hij v hv)] using hbad
  · exact hcoef

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_residual_tuple_product
#print axioms HeckeSkeleton.Moments.EngineStep.actual_residual_tuple_fiber_card
#print axioms HeckeSkeleton.Moments.EngineStep.common_label_powerful_normalized_sum_of_fibers
