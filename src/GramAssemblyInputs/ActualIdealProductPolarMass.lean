import ActualIdealTraceUniformShape
import HeckeGeneral.Analysis.TraceProductCovolume
import Mathlib.Tactic

/-!
UNCOMPILED candidate. Uniform polar mass for the actual two-column ideal
lattice, with the constant chosen before the arbitrary integral ideal.
Only the joint origin is removed: both nonzero coordinate axes are retained.
The homogeneous order is degree times A; the ideal-norm exponent is A.
This supplies the moving-lattice part of revised (3.37), not its arithmetic
coefficient, Fourier dilation/Jacobian or original Gram-sum identification.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Analysis.ActualIdealProductPolarMassDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.Arithmetic.ActualIdealTraceUniformShapeDraft
open scoped Classical BigOperators nonZeroDivisors

section Product

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Apply the same actual linear equivalence to both Hilbert columns. -/
def diagonalLpEquiv (e : E ≃L[ℝ] E) :
    WithLp 2 (E × E) ≃L[ℝ] WithLp 2 (E × E) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ E E).trans (e.prodCongr e)).trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm

@[simp] theorem diagonalLpEquiv_apply (e : E ≃L[ℝ] E) (v : WithLp 2 (E × E)) :
    diagonalLpEquiv e v = WithLp.toLp 2 (e (WithLp.ofLp v).1, e (WithLp.ofLp v).2) := rfl

@[simp] theorem diagonalLpEquiv_symm_apply (e : E ≃L[ℝ] E)
    (v : WithLp 2 (E × E)) :
    (diagonalLpEquiv e).symm v =
      WithLp.toLp 2 (e.symm (WithLp.ofLp v).1, e.symm (WithLp.ofLp v).2) := rfl

/-- The product operator has the same bound, with no dimension or ideal loss. -/
theorem diagonalLpEquiv_norm_le (e : E ≃L[ℝ] E) {C : ℝ}
    (hC : 0 ≤ C) (he : ‖e.toContinuousLinearMap‖ ≤ C) :
    ‖(diagonalLpEquiv e).toContinuousLinearMap‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  have hx : ‖e (WithLp.ofLp v).1‖ ≤ C * ‖(WithLp.ofLp v).1‖ :=
    e.toContinuousLinearMap.le_of_opNorm_le he (WithLp.ofLp v).1
  have hy : ‖e (WithLp.ofLp v).2‖ ≤ C * ‖(WithLp.ofLp v).2‖ :=
    e.toContinuousLinearMap.le_of_opNorm_le he (WithLp.ofLp v).2
  have hx2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hy2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
  have hsource := WithLp.prod_norm_sq_eq_of_L2 v
  have htarget := WithLp.prod_norm_sq_eq_of_L2 (diagonalLpEquiv e v)
  change ‖diagonalLpEquiv e v‖ ≤ C * ‖v‖
  change ‖v‖ ^ 2 = ‖(WithLp.ofLp v).1‖ ^ 2 + ‖(WithLp.ofLp v).2‖ ^ 2 at hsource
  change ‖diagonalLpEquiv e v‖ ^ 2 =
    ‖e (WithLp.ofLp v).1‖ ^ 2 + ‖e (WithLp.ofLp v).2‖ ^ 2 at htarget
  have hsq : ‖diagonalLpEquiv e v‖ ^ 2 ≤ (C * ‖v‖) ^ 2 := by
    rw [htarget, mul_pow, hsource]
    nlinarith only [hx2, hy2]
  nlinarith only [hsq, norm_nonneg (diagonalLpEquiv e v),
    mul_nonneg hC (norm_nonneg v)]

/-- Actual image equality, before passing to the dual lattice. -/
theorem lpProductLattice_image_diagonal (L : Submodule ℤ E) (e : E ≃L[ℝ] E) :
    lpProductLattice (imageLattice L e) (imageLattice L e) =
      imageLattice (lpProductLattice L L) (diagonalLpEquiv e) := by
  ext v
  rfl

end Product

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "W" => traceProductSpace K

/-- Both columns use the literal same ordinary period ideal. -/
abbrev idealProductLattice (I : (Ideal (𝓞 K))⁰) : Submodule ℤ W :=
  traceProductIdealLattice K (integralIdealUnit K I) (integralIdealUnit K I)

include S Γ in
/-- A class-dependent lattice sum is absorbed by a finite constant. Nothing
about the varying ideal, its generator or its prime factors enters C. -/
theorem exists_uniform_idealProduct_polar_mass (A : ℕ) (hA : 2 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : (Ideal (𝓞 K))⁰,
      latticeInversePowerMass (dualLattice (idealProductLattice K I))
          (Module.finrank ℚ K * A) ≤ C * (Ideal.absNorm I.val : ℝ) ^ A := by
  letI : Fintype (ClassGroup (𝓞 K)) := Fintype.ofFinite _
  let d := Module.finrank ℚ K
  let p := d * A
  have hd : 0 < d := Module.finrank_pos
  have hp : 2 * d < p := by
    dsimp only [p]
    nlinarith only [hA, hd]
  let mass : ClassGroup (𝓞 K) → ℝ := fun q =>
    latticeInversePowerMass (dualLattice (idealProductLattice K (periodClassRepresentative K q))) p
  have hmass (q : ClassGroup (𝓞 K)) : 0 ≤ mass q :=
    tsum_nonneg fun _ => by positivity
  let T : ℝ := 1 + ∑ q, mass q
  have hT : 0 < T := by
    have hsum := Finset.sum_nonneg (fun q (_ : q ∈ Finset.univ) => hmass q)
    dsimp only [T]
    linarith
  have hmassT (q : ClassGroup (𝓞 K)) : mass q ≤ T := by
    have hle := Finset.single_le_sum (fun q' (_ : q' ∈ Finset.univ) => hmass q')
      (Finset.mem_univ q)
    dsimp only [T]
    linarith
  obtain ⟨B, hB, hshape⟩ := exists_uniform_ideal_trace_shape K S Γ
  refine ⟨B ^ p * T, mul_pos (pow_pos hB _) hT, fun I => ?_⟩
  obtain ⟨q, ρ, hρ, e, hlat, hnorm, he⟩ := hshape I
  let L := idealProductLattice K (periodClassRepresentative K q)
  have hproduct : idealProductLattice K I = imageLattice L (diagonalLpEquiv e) := by
    change lpProductLattice (traceIdealLattice K (integralIdealUnit K I))
      (traceIdealLattice K (integralIdealUnit K I)) = _
    rw [hlat, lpProductLattice_image_diagonal]
    rfl
  have hrank : Module.finrank ℤ (dualLattice L) < p := by
    rw [ZLattice.rank ℝ (dualLattice L), finrank_traceProductSpace K]
    exact hp
  have hpolar := movingPeriod_polar_mass_le L (diagonalLpEquiv e) p hrank
    (diagonalLpEquiv_norm_le e (mul_nonneg hρ.le hB.le) he)
  have hnormOne : (1 : ℝ) ≤ (Ideal.absNorm (periodClassRepresentative K q).val : ℝ) := by
    have hn : 1 ≤ Ideal.absNorm (periodClassRepresentative K q).val :=
      Ideal.absNorm_pos_of_nonZeroDivisors (periodClassRepresentative K q)
    exact_mod_cast hn
  have hnormI : 0 ≤ (Ideal.absNorm I.val : ℝ) := Nat.cast_nonneg _
  have hrhopow : ρ ^ p ≤ (Ideal.absNorm I.val : ℝ) ^ A := by
    change ρ ^ (d * A) ≤ _
    rw [pow_mul, hnorm]
    exact pow_le_pow_left₀ (div_nonneg hnormI (zero_le_one.trans hnormOne))
      (div_le_self hnormI hnormOne) A
  change latticeInversePowerMass (dualLattice (idealProductLattice K I)) p ≤ _
  calc
    _ ≤ (ρ * B) ^ p * mass q := by
      rw [hproduct]
      exact hpolar
    _ = B ^ p * mass q * ρ ^ p := by rw [mul_pow]; ring
    _ ≤ B ^ p * T * (Ideal.absNorm I.val : ℝ) ^ A := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hmassT q) (pow_nonneg hB.le p))
        hrhopow (pow_nonneg hρ.le p) (mul_nonneg (pow_nonneg hB.le p) hT.le)

/-- The degree affects the derivative order, not the scale-saving exponent. -/
theorem normSection_inverse_power (N : ℝ) (hN : 0 < N) (A : ℕ) :
    ((N ^ (Module.finrank ℚ K : ℝ)⁻¹)⁻¹) ^ (Module.finrank ℚ K * A) =
      (N ^ A)⁻¹ := by
  rw [inv_pow, pow_mul, Real.rpow_inv_natCast_pow hN.le
    (Module.finrank_pos (R := ℚ) (M := K)).ne']

include S Γ in
/-- Actual bounded-coefficient dual sum, uniformly in the moving ideal.
The coefficient premise is only its elementary magnitude bound; neither
Poisson decay nor lattice mass is supplied as an analytic premise. -/
theorem exists_uniform_idealProduct_weighted_tail (A : ℕ) (hA : 2 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : (Ideal (𝓞 K))⁰) (F : SchwartzMap W ℂ)
      (N Q : ℝ), 0 < N → 0 ≤ Q →
      ∀ b : NonzeroLattice (dualLattice (idealProductLattice K I)) → ℂ,
        (∀ m, ‖b m‖ ≤ Q) →
        ‖∑' m : NonzeroLattice (dualLattice (idealProductLattice K I)),
          b m * F ((N ^ (Module.finrank ℚ K : ℝ)⁻¹) •
            ((m : dualLattice (idealProductLattice K I)) : W))‖ ≤
          C * Q * SchwartzMap.seminorm ℂ (Module.finrank ℚ K * A) 0 F *
            ((Ideal.absNorm I.val : ℝ) / N) ^ A := by
  obtain ⟨C, hC, hmass⟩ := exists_uniform_idealProduct_polar_mass K S Γ A hA
  refine ⟨C, hC, fun I F N Q hN hQ b hb => ?_⟩
  let p := Module.finrank ℚ K * A
  let D := dualLattice (idealProductLattice K I)
  have hrank : Module.finrank ℤ D < p := by
    rw [ZLattice.rank ℝ D, finrank_traceProductSpace K]
    dsimp only [p]
    have hd := Module.finrank_pos (R := ℚ) (M := K)
    nlinarith only [hA, hd]
  have hα := Real.rpow_pos_of_pos hN (Module.finrank ℚ K : ℝ)⁻¹
  calc
    _ ≤ Q * (SchwartzMap.seminorm ℂ p 0 F *
        ((N ^ (Module.finrank ℚ K : ℝ)⁻¹)⁻¹) ^ p * latticeInversePowerMass D p) :=
      norm_tsum_scaled_weighted_schwartz_le D F p hrank hα hQ b hb
    _ ≤ Q * (SchwartzMap.seminorm ℂ p 0 F *
        ((N ^ (Module.finrank ℚ K : ℝ)⁻¹)⁻¹) ^ p *
          (C * (Ideal.absNorm I.val : ℝ) ^ A)) := by
      apply mul_le_mul_of_nonneg_left _ hQ
      exact mul_le_mul_of_nonneg_left (hmass I) (by positivity)
    _ = _ := by
      dsimp only [p]
      rw [normSection_inverse_power K N hN A, div_pow, div_eq_mul_inv]
      ring

end HeckeGeneral.Analysis.ActualIdealProductPolarMassDraft
