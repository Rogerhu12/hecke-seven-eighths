import HeckeGeneral.Analysis.LatticeFiniteMask
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Actual nonzero lattice tails under scalar dilation. The constants are explicit
Schwartz seminorms and a convergent inverse-power sum on the fixed lattice.
This does not supply uniform constants for a moving ideal lattice; balanced
generators and compact shape control are separate arithmetic obligations.
-/

noncomputable section

open Classical Module
open scoped FourierTransform

namespace HeckeGeneral.Analysis

open HeckeGeneral.Arithmetic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

abbrev NonzeroLattice (L : Submodule ℤ E) := {l : L // l ≠ 0}

def latticeInversePowerMass (L : Submodule ℤ E) (M : ℕ) : ℝ :=
  ∑' l : NonzeroLattice L, ‖((l : L) : E)‖⁻¹ ^ M

omit [FiniteDimensional ℝ E] in
/-- All weighted derivative norms have a homogeneous decay bound controlled
by one actual Schwartz seminorm. -/
theorem schwartz_scaled_derivative_bound (f : SchwartzMap E ℂ)
    (M h : ℕ) {α : ℝ} (hα : 0 < α) {x : E} (hx : x ≠ 0) :
    ‖α • x‖ ^ h * ‖iteratedFDeriv ℝ h f (α • x)‖ ≤
      SchwartzMap.seminorm ℂ (M + h) h f * α⁻¹ ^ M * ‖x‖⁻¹ ^ M := by
  have hn : 0 < ‖α • x‖ := norm_pos_iff.mpr (smul_ne_zero hα.ne' hx)
  calc
    _ ≤ SchwartzMap.seminorm ℂ (M + h) h f / ‖α • x‖ ^ M := by
      apply (le_div_iff₀ (pow_pos hn M)).mpr
      calc
        (‖α • x‖ ^ h * ‖iteratedFDeriv ℝ h f (α • x)‖) * ‖α • x‖ ^ M =
          ‖α • x‖ ^ (M + h) * ‖iteratedFDeriv ℝ h f (α • x)‖ := by
            rw [pow_add]; ring
        _ ≤ _ := SchwartzMap.le_seminorm ℂ (M + h) h f (α • x)
    _ = _ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hα, mul_pow, div_eq_mul_inv,
        mul_inv_rev, inv_pow, inv_pow]
      ring

theorem summable_lattice_inverse_power (L : Submodule ℤ E) [DiscreteTopology L]
    (M : ℕ) (hM : Module.finrank ℤ L < M) :
    Summable fun l : NonzeroLattice L => ‖((l : L) : E)‖⁻¹ ^ M := by
  exact (ZLattice.summable_norm_pow_inv (L := L) M hM).subtype _

theorem summable_scaled_schwartz_derivative (L : Submodule ℤ E) [DiscreteTopology L]
    (f : SchwartzMap E ℂ) (M h : ℕ) (hM : Module.finrank ℤ L < M)
    {α : ℝ} (hα : 0 < α) :
    Summable fun l : NonzeroLattice L =>
      ‖α • ((l : L) : E)‖ ^ h * ‖iteratedFDeriv ℝ h f (α • ((l : L) : E))‖ := by
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun l => ?_)
    ((summable_lattice_inverse_power L M hM).mul_left
      (SchwartzMap.seminorm ℂ (M + h) h f * α⁻¹ ^ M))
  exact schwartz_scaled_derivative_bound f M h hα (by
    intro hl
    exact l.property (Subtype.ext hl))

/-- The actual all-order lattice tail, including its finite seminorm constant. -/
theorem tsum_scaled_schwartz_derivative_le (L : Submodule ℤ E) [DiscreteTopology L]
    (f : SchwartzMap E ℂ) (M h : ℕ) (hM : Module.finrank ℤ L < M)
    {α : ℝ} (hα : 0 < α) :
    (∑' l : NonzeroLattice L,
      ‖α • ((l : L) : E)‖ ^ h * ‖iteratedFDeriv ℝ h f (α • ((l : L) : E))‖) ≤
      SchwartzMap.seminorm ℂ (M + h) h f * α⁻¹ ^ M * latticeInversePowerMass L M := by
  calc
    _ ≤ ∑' l : NonzeroLattice L,
        (SchwartzMap.seminorm ℂ (M + h) h f * α⁻¹ ^ M) * ‖((l : L) : E)‖⁻¹ ^ M := by
      apply Summable.tsum_le_tsum
        (fun l => schwartz_scaled_derivative_bound f M h hα (by
          intro hl; exact l.property (Subtype.ext hl)))
        (summable_scaled_schwartz_derivative L f M h hM hα)
        ((summable_lattice_inverse_power L M hM).mul_left _)
    _ = _ := tsum_mul_left

theorem norm_tsum_scaled_schwartz_le (L : Submodule ℤ E) [DiscreteTopology L]
    (f : SchwartzMap E ℂ) (M : ℕ) (hM : Module.finrank ℤ L < M)
    {α : ℝ} (hα : 0 < α) :
    ‖∑' l : NonzeroLattice L, f (α • ((l : L) : E))‖ ≤
      SchwartzMap.seminorm ℂ M 0 f * α⁻¹ ^ M * latticeInversePowerMass L M := by
  have hs : Summable fun l : NonzeroLattice L => ‖f (α • ((l : L) : E))‖ := by
    simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero] using
      summable_scaled_schwartz_derivative L f M 0 hM hα
  calc
    _ ≤ ∑' l : NonzeroLattice L, ‖f (α • ((l : L) : E))‖ := norm_tsum_le_tsum_norm hs
    _ ≤ _ := by
      simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero, Nat.add_zero] using
        tsum_scaled_schwartz_derivative_le L f M 0 hM hα

/-- Passing from coordinate length `ρ^(1/d)` to norm length `ρ` changes the
required Schwartz order, without adding a new norm-length exponent. -/
theorem norm_tsum_normSection_schwartz_le (L : Submodule ℤ E) [DiscreteTopology L]
    (f : SchwartzMap E ℂ) (M d : ℕ) (hM : Module.finrank ℤ L < M) (hd : 0 < d)
    (A ρ : ℝ) (hρ : 1 ≤ ρ) (hOrder : (d : ℝ) * A ≤ M) :
    ‖∑' l : NonzeroLattice L, f ((ρ ^ (d : ℝ)⁻¹) • ((l : L) : E))‖ ≤
      SchwartzMap.seminorm ℂ M 0 f * latticeInversePowerMass L M * ρ ^ (-A) := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hα := Real.rpow_pos_of_pos hρpos (d : ℝ)⁻¹
  have hdpos : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hexp : -(d : ℝ)⁻¹ * M ≤ -A := by
    have h := mul_le_mul_of_nonneg_left hOrder (inv_nonneg.mpr hdpos.le)
    rw [← mul_assoc, inv_mul_cancel₀ hdpos.ne', one_mul] at h
    linarith
  have hpow : ((ρ ^ (d : ℝ)⁻¹)⁻¹) ^ M ≤ ρ ^ (-A) := by
    rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul hρpos.le,
      ← Real.rpow_neg hρpos.le]
    apply Real.rpow_le_rpow_of_exponent_le hρ
    simpa only [neg_mul] using hexp
  calc
    _ ≤ SchwartzMap.seminorm ℂ M 0 f * ((ρ ^ (d : ℝ)⁻¹)⁻¹) ^ M *
        latticeInversePowerMass L M := norm_tsum_scaled_schwartz_le L f M hM hα
    _ = SchwartzMap.seminorm ℂ M 0 f * latticeInversePowerMass L M *
        ((ρ ^ (d : ℝ)⁻¹)⁻¹) ^ M := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow
      (mul_nonneg (apply_nonneg (SchwartzMap.seminorm ℂ M 0) f)
        (tsum_nonneg fun _ => by positivity))

/-- Bounded coefficients preserve absolute convergence of the actual scaled
nonzero lattice series. The majorant is the convergent lattice inverse-power
sum, rather than a supplied summability field. -/
theorem summable_norm_scaled_weighted_schwartz (L : Submodule ℤ E)
    [DiscreteTopology L] (f : SchwartzMap E ℂ) (M : ℕ)
    (hM : Module.finrank ℤ L < M) {α C : ℝ} (hα : 0 < α)
    (b : NonzeroLattice L → ℂ) (hb : ∀ l, ‖b l‖ ≤ C) :
    Summable fun l : NonzeroLattice L => ‖b l * f (α • ((l : L) : E))‖ := by
  have hs : Summable fun l : NonzeroLattice L => ‖f (α • ((l : L) : E))‖ := by
    simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero] using
      summable_scaled_schwartz_derivative L f M 0 hM hα
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => ?_) (hs.mul_left C)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hb l) (norm_nonneg _)

/-- The coefficient norm multiplies the fixed-lattice Schwartz tail constant. -/
theorem norm_tsum_scaled_weighted_schwartz_le (L : Submodule ℤ E)
    [DiscreteTopology L] (f : SchwartzMap E ℂ) (M : ℕ)
    (hM : Module.finrank ℤ L < M) {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    (b : NonzeroLattice L → ℂ) (hb : ∀ l, ‖b l‖ ≤ C) :
    ‖∑' l : NonzeroLattice L, b l * f (α • ((l : L) : E))‖ ≤
      C * (SchwartzMap.seminorm ℂ M 0 f * α⁻¹ ^ M * latticeInversePowerMass L M) := by
  have hs : Summable fun l : NonzeroLattice L => ‖f (α • ((l : L) : E))‖ := by
    simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero] using
      summable_scaled_schwartz_derivative L f M 0 hM hα
  calc
    _ ≤ ∑' l : NonzeroLattice L, ‖b l * f (α • ((l : L) : E))‖ :=
      norm_tsum_le_tsum_norm
        (summable_norm_scaled_weighted_schwartz L f M hM hα b hb)
    _ ≤ ∑' l : NonzeroLattice L, C * ‖f (α • ((l : L) : E))‖ := by
      apply Summable.tsum_le_tsum (fun l => ?_)
        (summable_norm_scaled_weighted_schwartz L f M hM hα b hb) (hs.mul_left C)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hb l) (norm_nonneg _)
    _ = C * ∑' l : NonzeroLattice L, ‖f (α • ((l : L) : E))‖ := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (by
      simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero, Nat.add_zero] using
        tsum_scaled_schwartz_derivative_le L f M 0 hM hα) hC

section FourierMask

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The actual finite character coefficient gives a uniform coefficient bound
in the nonzero polar sum; no primitive-frequency assumption is needed. -/
theorem norm_tsum_scaled_fourier_mask_le (L J : Submodule ℤ V)
    [DiscreteTopology J] [IsZLattice ℝ J] [Fintype (LatticeQuotient L J)]
    (w : LatticeQuotient L J → ℂ) (f : SchwartzMap V ℂ) (v : V)
    (M : ℕ) (hM : Module.finrank ℤ (dualLattice J) < M)
    {α : ℝ} (hα : 0 < α) :
    ‖∑' m : NonzeroLattice (dualLattice J),
      latticePhase v ((m : dualLattice J) : V) * latticeMaskCoefficient L J w m *
        (𝓕 ⇑f) (α • ((m : dualLattice J) : V))‖ ≤
      (∑ q, ‖w q‖) * (SchwartzMap.seminorm ℂ M 0 (𝓕 f) * α⁻¹ ^ M *
        latticeInversePowerMass (dualLattice J) M) := by
  let b : NonzeroLattice (dualLattice J) → ℂ := fun m =>
    latticePhase v ((m : dualLattice J) : V) * latticeMaskCoefficient L J w m
  have hb : ∀ m, ‖b m‖ ≤ ∑ q, ‖w q‖ := by
    intro m
    simpa only [b, norm_mul, norm_latticePhase, one_mul] using
      norm_latticeMaskCoefficient_le L J w (m : dualLattice J)
  simpa only [b, SchwartzMap.fourier_coe] using
    norm_tsum_scaled_weighted_schwartz_le (dualLattice J) (𝓕 f) M hM hα
      (Finset.sum_nonneg fun _ _ => norm_nonneg _) b hb

end FourierMask

end HeckeGeneral.Analysis
