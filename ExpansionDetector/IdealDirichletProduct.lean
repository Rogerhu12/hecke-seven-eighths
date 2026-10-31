import ExpansionDetector.IdealConvolution
import ExpansionDetector.ZeroDetectorBound

/-! An explicit finite ideal inverse and its exact initial-line Cauchy
product. Coefficients are the same literal mu(I), character weight, and
cutoff used by the later terminal source. -/
noncomputable section
namespace ExpansionDetector.IdealCutoff
open UniqueFactorizationMonoid
open scoped NumberField Classical BigOperators nonZeroDivisors
variable {K : Type*} [Field K] [NumberField K]

def idealDirichletWeight (w : Ideal (𝓞 K) →*₀ ℂ) (s : ℂ) : Ideal (𝓞 K) →*₀ ℂ where
  toFun := fun I => w I * (Ideal.absNorm I : ℂ) ^ (-s)
  map_zero' := by rw [map_zero, zero_mul]
  map_one' := by rw [map_one, map_one]; simp
  map_mul' := by
    intro I J
    simp only [map_mul, Nat.cast_mul]
    rw [Complex.natCast_mul_natCast_cpow]
    ring

@[simp] lemma idealDirichletWeight_apply (w : Ideal (𝓞 K) →*₀ ℂ) (s : ℂ) (I : Ideal (𝓞 K)) :
    idealDirichletWeight w s I = w I * (Ideal.absNorm I : ℂ) ^ (-s) := rfl

def inverseIdealSet (D : ℝ) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOfPred_absNorm_le ⌈2 * D⌉₊).toFinset.filter
    (fun I => I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ 2 * D)

lemma mem_inverseIdealSet (D : ℝ) (I : Ideal (𝓞 K)) :
    I ∈ inverseIdealSet D ↔ I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ 2 * D := by
  simp only [inverseIdealSet, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    exact_mod_cast h.2.trans (Nat.le_ceil (2 * D))

def inverseIdealCoefficient (w : Ideal (𝓞 K) →*₀ ℂ) (V : ℝ → ℂ)
    (D : ℝ) (I : Ideal (𝓞 K)) : ℂ :=
  (moebius I : ℂ) * w I * V ((Ideal.absNorm I : ℝ) / D)

def actualInverse (w : Ideal (𝓞 K) →*₀ ℂ) (V : ℝ → ℂ) (D : ℝ) : ℂ → ℂ :=
  ExpansionDetector.Analytic.dirichletPolynomial (inverseIdealSet D)
    (inverseIdealCoefficient w V D) (fun I => (Ideal.absNorm I : ℝ))

lemma actualInverse_entire (w : Ideal (𝓞 K) →*₀ ℂ) (V : ℝ → ℂ) (D : ℝ) :
    Differentiable ℂ (actualInverse w V D) := by
  apply ExpansionDetector.Analytic.dirichletPolynomial_entire
  intro I hI
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    ((mem_inverseIdealSet D I).mp hI).1)

lemma inverseIdealCoefficient_zero_outside
    (w : Ideal (𝓞 K) →*₀ ℂ) (V : ℝ → ℂ) (D : ℝ) (hD : 0 < D)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (I : Ideal (𝓞 K)) (hI : I ∉ inverseIdealSet D) :
    inverseIdealCoefficient w V D I = 0 := by
  by_cases hI0 : I = 0
  · subst I
    simp only [inverseIdealCoefficient, map_zero, mul_zero, zero_mul]
  have hlarge : 2 * D < (Ideal.absNorm I : ℝ) := by
    have h := hI
    rw [mem_inverseIdealSet] at h
    exact lt_of_not_ge (fun hle => h ⟨hI0, hle⟩)
  have hz := hVzero ((Ideal.absNorm I : ℝ) / D)
    ((le_div_iff₀ hD).mpr hlarge.le)
  simp only [inverseIdealCoefficient, hz, mul_zero]

/-- This is a finite polynomial for every complex s, not a formal infinite
inverse outside its convergence domain. -/
theorem inverse_tsum_eq_actualInverse
    (w : Ideal (𝓞 K) →*₀ ℂ) (V : ℝ → ℂ) (D : ℝ) (hD : 0 < D)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) :
    (∑' I : Ideal (𝓞 K), (moebius I : ℂ) * V ((Ideal.absNorm I : ℝ) / D) *
        idealDirichletWeight w s I) = actualInverse w V D s := by
  have hterm (I : Ideal (𝓞 K)) :
      (moebius I : ℂ) * V ((Ideal.absNorm I : ℝ) / D) * idealDirichletWeight w s I =
        inverseIdealCoefficient w V D I * (Ideal.absNorm I : ℂ) ^ (-s) := by
    simp only [idealDirichletWeight_apply, inverseIdealCoefficient]
    ring
  simp_rw [hterm]
  rw [tsum_eq_sum (s := inverseIdealSet D) (fun I hI => by
    rw [inverseIdealCoefficient_zero_outside w V D hD hVzero I hI, zero_mul])]
  rfl

lemma norm_ideal_moebius_le_one (I : Ideal (𝓞 K)) : ‖(moebius I : ℂ)‖ ≤ 1 := by
  unfold moebius
  split_ifs <;> simp

lemma summable_moebius_weight (w : Ideal (𝓞 K) →*₀ ℂ) (V : ℝ → ℂ) (D : ℝ)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ 1)
    (hw : Summable (fun I : Ideal (𝓞 K) => ‖w I‖)) :
    Summable (fun I : Ideal (𝓞 K) =>
      ‖(moebius I : ℂ) * V ((Ideal.absNorm I : ℝ) / D) * w I‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hw
  intro I
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (1 * 1) * ‖w I‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul (norm_ideal_moebius_le_one I) (hV _) (norm_nonneg _) (by norm_num)
    _ = _ := by ring

/-- Exact initial Dirichlet-line identity for the actual finite inverse.
The only L-function premise is its ordinary absolutely convergent series.
There is no assumption about a detector, zero, or witness. -/
theorem initial_product_identity
    (w : Ideal (𝓞 K) →*₀ ℂ) (V : ℝ → ℂ) (D : ℝ) (hD : 0 < D)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (L : ℂ → ℂ) (s : ℂ)
    (hL : L s = ∑' I : Ideal (𝓞 K), idealDirichletWeight w s I)
    (hw : Summable (fun I : Ideal (𝓞 K) => ‖idealDirichletWeight w s I‖)) :
    L s * actualInverse w V D s =
      ∑' I : Ideal (𝓞 K), coefficient V D I * w I * (Ideal.absNorm I : ℂ) ^ (-s) := by
  have hc := weighted_convolution_identity (idealDirichletWeight w s) V D
    (summable_moebius_weight (idealDirichletWeight w s) V D hV hw) hw
  rw [inverse_tsum_eq_actualInverse w V D hD hVzero s, ← hL] at hc
  rw [mul_comm] at hc
  apply hc.trans
  apply tsum_congr
  intro I
  simp only [idealDirichletWeight_apply]
  ring

/-- The exact Cauchy product also proves summability of the resulting
truncated-convolution Dirichlet coefficients on that initial line. -/
theorem initial_product_summable
    (w : Ideal (𝓞 K) →*₀ ℂ) (V : ℝ → ℂ) (D : ℝ)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) (s : ℂ)
    (hw : Summable (fun I : Ideal (𝓞 K) => ‖idealDirichletWeight w s I‖)) :
    Summable (fun I : Ideal (𝓞 K) => coefficient V D I * w I * (Ideal.absNorm I : ℂ) ^ (-s)) := by
  have h := (weighted_convolution_hasSum (idealDirichletWeight w s) V D
    (summable_moebius_weight (idealDirichletWeight w s) V D hV hw) hw).summable
  apply h.congr
  intro I
  simp only [idealDirichletWeight_apply]
  ring

end ExpansionDetector.IdealCutoff
