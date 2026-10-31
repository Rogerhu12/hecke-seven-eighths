import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalBinding

/-!
# Exceptional rows retain their actual finite inducing-character pair

Membership in theta synchronizes the two sides, but does not say that
every exceptional row has the same inducing character.  The original
row set is partitioned here by the actual pair of character values.
Each class keeps its literal rows, coefficients, Fourier locations,
kernel and scalar.  Its exceptional cost is an exact part of the
canonical source cost, before any volume estimate is applied.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField HeckeGeneral.Characters MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {H : Type*} {theta : Finset (HeckeCharacter K)}

namespace PairedFiniteCharacters

variable (Q : PairedFiniteCharacters theta H)

def thetaClass (χ : theta × theta) (h : H) : Prop :=
  Q.left h = χ.1.val ∧ Q.right h = χ.2.val

theorem thetaClass_exceptional (χ : theta × theta) (h : H) (hh : Q.thetaClass χ h) :
    Q.exceptional h := by
  change Q.left h ∈ theta
  rw [hh.1]
  exact χ.1.property

/-- Both class coordinates are the actual original character values.
There is one and only one pair for each exceptional row. -/
theorem sum_exceptional_eq_theta_classes (rows : Finset H) (term : H → ℝ) :
    (∑ h ∈ rows.filter Q.exceptional, term h) =
      ∑ χ : theta × theta, ∑ h ∈ rows.filter (Q.thetaClass χ), term h := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  by_cases he : Q.exceptional h
  · let χ : theta × theta :=
      (⟨Q.left h, he⟩, ⟨Q.right h, (Q.right_exceptional h).mpr he⟩)
    rw [if_pos he]
    symm
    calc
      _ = if Q.thetaClass χ h then term h else 0 := by
        apply Finset.sum_eq_single χ
        · intro j hj hne
          apply if_neg
          intro hclass
          apply hne
          apply Prod.ext
          · apply Subtype.ext
            exact hclass.1.symm
          · apply Subtype.ext
            exact hclass.2.symm
        · intro hnot
          exact False.elim (hnot (Finset.mem_univ χ))
      _ = term h := by simp only [thetaClass, χ, and_self, if_true]
  · rw [if_neg he]
    symm
    apply Finset.sum_eq_zero
    intro χ hχ
    exact if_neg (fun hclass => he (Q.thetaClass_exceptional χ h hclass))

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem pair_magnitude_eq_theta_classes {ι κ : Type*}
    (rows : Finset H) (left : Finset ι) (right : Finset κ)
    (weight : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
    (x : H → ι → V) (y : H → κ → V) (ξ : V) :
    jointColumnPairMagnitude (rows.filter Q.exceptional) left right weight c d x y ξ =
      ∑ χ : theta × theta,
        jointColumnPairMagnitude (rows.filter (Q.thetaClass χ))
          left right weight c d x y ξ :=
  Q.sum_exceptional_eq_theta_classes rows
    (fun h => ‖weight h‖ * ‖jointFourierColumn left (c h) (x h) ξ‖ *
      ‖jointFourierColumn right (d h) (y h) ξ‖)

end PairedFiniteCharacters

section Leaves

variable {U W : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

namespace ActualHybridLeaf

variable (B : ActualHybridLeaf K H U W) (Q : PairedFiniteCharacters theta H)

/-- A literal restriction of the original rows.  No coefficient,
location, normalizer or original Fourier measure is replaced. -/
def thetaClassLeaf (χ : theta × theta) : ActualHybridLeaf K H U W :=
  { B with rows := B.rows.filter (Q.thetaClass χ) }

@[simp] theorem thetaClassLeaf_weight (χ : theta × theta) :
    (B.thetaClassLeaf Q χ).weight = B.weight := rfl

@[simp] theorem thetaClassLeaf_measure (χ : theta × theta) :
    (B.thetaClassLeaf Q χ).measure = B.measure := rfl

theorem thetaClassLeaf_integrand (hpredicate : B.exceptional = Q.exceptional)
    (χ : theta × theta) (z : U × W) :
    (B.thetaClassLeaf Q χ).exceptionalIntegrand z =
      jointColumnPairMagnitude (B.rows.filter (Q.thetaClass χ)) B.left B.right
        B.rowWeight B.leftCoefficient (fun h j => star (B.rightCoefficient h j))
        (fun h i => WithLp.toLp 2 (B.leftFirst h i, B.leftSecond h i))
        (fun h j => WithLp.toLp 2 (-B.rightFirst h j, B.rightSecond h j))
        (WithLp.toLp 2 z) := by
  have hrows : (B.rows.filter (Q.thetaClass χ)).filter B.exceptional =
      B.rows.filter (Q.thetaClass χ) := by
    apply Finset.filter_eq_self.mpr
    intro h hh
    rw [hpredicate]
    exact Q.thetaClass_exceptional χ h (Finset.mem_filter.mp hh).2
  simp only [thetaClassLeaf, exceptionalIntegrand, hrows]

/-- Pointwise exact partition of the canonical exceptional integrand. -/
theorem exceptionalIntegrand_eq_theta_sum (hpredicate : B.exceptional = Q.exceptional)
    (z : U × W) :
    B.exceptionalIntegrand z =
      ∑ χ : theta × theta, (B.thetaClassLeaf Q χ).exceptionalIntegrand z := by
  simp_rw [B.thetaClassLeaf_integrand Q hpredicate]
  unfold exceptionalIntegrand
  rw [hpredicate]
  exact Q.pair_magnitude_eq_theta_classes B.rows B.left B.right B.rowWeight
    B.leftCoefficient (fun h j => star (B.rightCoefficient h j))
    (fun h i => WithLp.toLp 2 (B.leftFirst h i, B.leftSecond h i))
    (fun h j => WithLp.toLp 2 (-B.rightFirst h j, B.rightSecond h j))
    (WithLp.toLp 2 z)

/-- Actual finite-polynomial integrability proves the interchange.
The original nested Fourier measure is still used exactly once. -/
theorem exceptionalCost_eq_theta_sum (hpredicate : B.exceptional = Q.exceptional) :
    B.exceptionalCost = ∑ χ : theta × theta, (B.thetaClassLeaf Q χ).exceptionalCost := by
  unfold exceptionalCost
  simp_rw [B.exceptionalIntegrand_eq_theta_sum Q hpredicate]
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    rfl
  · intro χ hχ
    exact (B.thetaClassLeaf Q χ).exceptionalIntegrand_integrable

end ActualHybridLeaf
end Leaves

/-- One order can be chosen from the original finite family before
any scale, row or Fourier variable. -/
def finiteExceptionalOrder {I : Type*} [Fintype I] (order : I → ℕ) : ℕ :=
  Finset.univ.sup order

def finiteExceptionalConstant {I : Type*} [Fintype I] (constant : I → ℝ) : ℝ :=
  1 + ∑ i, constant i

theorem finiteExceptionalConstant_pos {I : Type*} [Fintype I]
    (constant : I → ℝ) (hconstant : ∀ i, 0 ≤ constant i) :
    0 < finiteExceptionalConstant constant := by
  unfold finiteExceptionalConstant
  have hs : 0 ≤ ∑ i, constant i := Finset.sum_nonneg fun i _ => hconstant i
  linarith

theorem finite_exceptional_envelope_le {I : Type*} [Fintype I]
    (order : I → ℕ) (constant : I → ℝ) (hconstant : ∀ i, 0 ≤ constant i)
    (i : I) (height : ℝ) (hheight : 0 ≤ height) :
    constant i * (1 + height) ^ order i ≤
      finiteExceptionalConstant constant * (1 + height) ^ finiteExceptionalOrder order := by
  have hc : constant i ≤ finiteExceptionalConstant constant := by
    have hs := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset I)) => hconstant j)
      (Finset.mem_univ i)
    unfold finiteExceptionalConstant
    linarith
  have ho : order i ≤ finiteExceptionalOrder order := Finset.le_sup (Finset.mem_univ i)
  exact mul_le_mul hc
    (pow_le_pow_right₀ (by linarith : 1 ≤ 1 + height) ho)
    (pow_nonneg (by linarith) _)
    (finiteExceptionalConstant_pos constant hconstant).le

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.PairedFiniteCharacters.sum_exceptional_eq_theta_classes
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.exceptionalCost_eq_theta_sum
#print axioms HeckeSkeleton.Moments.EngineStep.finite_exceptional_envelope_le
