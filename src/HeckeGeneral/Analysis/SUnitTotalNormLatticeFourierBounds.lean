import HeckeGeneral.Analysis.SUnitTotalNormFourierBounds
import HeckeGeneral.Analysis.TraceProductPoisson
import HeckeGeneral.Analysis.LatticeSchwartzTail

/-!
Fourier summation for a fixed pair of actual fractional ideal lattices.
The nonzero dual index removes only the single origin, retaining both axes.
Translation is the genuine positive Poisson phase and has absolute value one.
The constants depend on the two fixed ideals.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Bridge
open scoped Classical ContDiff BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
variable (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
  (a0 b0 : ℝ) (ha0 : 0 < a0) (haSupport : tsupport a ⊆ Set.Icc a0 b0)
  (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
  (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
variable (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "W" => traceProductSpace K
local notation "Z" => SFiniteLocalGroup K S
local notation "D" => dualLattice (traceProductIdealLattice K I J)
local notation "L0" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- Fixed-ideal absolute dual-lattice summation for the actual total-norm
Fourier kernel. The constants precede every moving analytic parameter and
the arbitrary translation. They may depend on the fixed ideals I and J.

The profile order M is separate from the frequency order q = 2[K:Q] + 1.
The latter is obtained from the actual rank of the product polar lattice.
The real and complex Schwartz seminorm values below are definitionally
equal: both use real iterated differentials and the same norm.
-/
theorem exists_sUnitTotalNormAnnularPartitionJointFourier_lattice_bound
    (B : ℝ) (M : ℕ) (hM : Module.finrank ℤ L0 < M)
    (hOrder : (Module.finrank ℚ K : ℝ) * B ≤ M) :
    ∃ s : Finset (ℕ × ℕ), ∃ C R0 : ℝ, ∃ Jheight : ℕ,
      0 ≤ C ∧ 1 ≤ R0 ∧
      ∀ ν : ℝ, ∀ ζ ξ : Z, ∀ φ : SchwartzMap V ℂ,
      ∀ R : {r : ℝ // 0 < r}, R0 ≤ R.val → ∀ v : W,
        let F := sUnitTotalNormAnnularPartitionJointFourier K S Γ
          a ha a0 b0 ha0 haSupport ψ hψ hψsupport ν ζ ξ φ R
        let t : NonzeroLattice D → ℂ := fun m =>
          latticePhase v ((m : D) : W) *
            F ((traceJointConjugation K).symm ((m : D) : W))
        Summable (fun m => ‖t m‖) ∧
          (∑' m, ‖t m‖) ≤
            C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
              (1 + |ν|) ^ Jheight * R.val ^ (-B) ∧
          ‖∑' m, t m‖ ≤
            C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
              (1 + |ν|) ^ Jheight * R.val ^ (-B) := by
  let q : ℕ := 2 * Module.finrank ℚ K + 1
  have hq : Module.finrank ℤ D < q := by
    dsimp only [q]
    rw [ZLattice.rank ℝ D, finrank_traceProductSpace K]
    omega
  let mass : ℝ := latticeInversePowerMass D q
  have hmass : 0 ≤ mass := tsum_nonneg fun _ => by positivity
  obtain ⟨s, C, R0, Jheight, hC, hR0, hb⟩ :=
    exists_sUnitTotalNormAnnularPartitionJointFourier_seminorm_power_bound
      K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport B M hM hOrder q 0
  refine ⟨s, C * mass, R0, Jheight, mul_nonneg hC hmass, hR0, ?_⟩
  intro ν ζ ξ φ R hR v
  let F : SchwartzMap W ℂ := sUnitTotalNormAnnularPartitionJointFourier K S Γ
    a ha a0 b0 ha0 haSupport ψ hψ hψsupport ν ζ ξ φ R
  let c : W ≃ₗᵢ[ℝ] W := (traceJointConjugation K).symm
  let t : NonzeroLattice D → ℂ := fun m =>
    latticePhase v ((m : D) : W) * F (c ((m : D) : W))
  change Summable (fun m => ‖t m‖) ∧
    (∑' m, ‖t m‖) ≤ (C * mass) *
      s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ Jheight * R.val ^ (-B) ∧
    ‖∑' m, t m‖ ≤ (C * mass) *
      s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ Jheight * R.val ^ (-B)
  have hF : SchwartzMap.seminorm ℂ q 0 F ≤
      C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
        (1 + |ν|) ^ Jheight * R.val ^ (-B) := by
    -- Only the seminorm's scalar field changes, not its value.
    change SchwartzMap.seminorm ℝ q 0 F ≤ _
    exact hb ν ζ ξ φ R hR
  have hpoint (m : NonzeroLattice D) :
      ‖t m‖ ≤ SchwartzMap.seminorm ℂ q 0 F * ‖((m : D) : W)‖⁻¹ ^ q := by
    have hm : ((m : D) : W) ≠ 0 := by
      intro hz
      exact m.property (Subtype.ext hz)
    have hcm : c ((m : D) : W) ≠ 0 := by
      intro hz
      exact hm (c.injective (by simpa only [map_zero] using hz))
    have hd := schwartz_scaled_derivative_bound F q 0 (α := 1)
      zero_lt_one hcm
    simpa only [t, norm_mul, norm_latticePhase, one_mul, one_smul,
      pow_zero, norm_iteratedFDeriv_zero, Nat.add_zero, inv_one,
      one_pow, mul_one, c.norm_map] using hd
  have hmajorant : Summable fun m : NonzeroLattice D =>
      SchwartzMap.seminorm ℂ q 0 F * ‖((m : D) : W)‖⁻¹ ^ q :=
    (summable_lattice_inverse_power D q hq).mul_left _
  have hs : Summable (fun m => ‖t m‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint hmajorant
  have habs : (∑' m, ‖t m‖) ≤ (C * mass) *
      s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
        (1 + |ν|) ^ Jheight * R.val ^ (-B) := by
    calc
      _ ≤ ∑' m : NonzeroLattice D,
          SchwartzMap.seminorm ℂ q 0 F * ‖((m : D) : W)‖⁻¹ ^ q :=
        Summable.tsum_le_tsum hpoint hs hmajorant
      _ = SchwartzMap.seminorm ℂ q 0 F * mass := tsum_mul_left
      _ ≤ (C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
          (1 + |ν|) ^ Jheight * R.val ^ (-B)) * mass :=
        mul_le_mul_of_nonneg_right hF hmass
      _ = _ := by ring
  exact ⟨hs, habs, (norm_tsum_le_tsum_norm hs).trans habs⟩

/-!
Translated Poisson alignment:

For H = sUnitTotalNormAnnularPartitionJointSchwartz(...), take
F = SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (traceJointToProduct K) H
in traceProductPoisson K I J F v. Then the actual G in this theorem is
traceJointFourierCLM K F by the definition of traceJointProductFourierCLM.
Each standard Fourier term is (2^r₂)^2 * G(conj⁻¹ m), while the positive
exponential phase is latticePhase v m. Consequently the mixed Poisson
coefficient stays traceProductMixedPoissonCoefficient K I J. The present
bound omits only m = 0; the PSF origin and both axes must remain explicit.
No statement here supplies a uniform constant over moving ideals.
-/

open NumberField.InfinitePlace
open scoped FourierTransform

/-- Translated Poisson for the actual total-norm annular partition kernel.
Both sums include the origin and both coordinate axes. The mixed coefficient
contains the original squared Jacobian divided by the actual covolume. -/
theorem sUnitTotalNormAnnularPartitionJointPoisson_translated
    (ν : ℝ) (ζ ξ : Z) (φ : SchwartzMap V ℂ)
    (R : {r : ℝ // 0 < r}) (v : W) :
    (∑' l : traceProductIdealLattice K I J,
      sUnitTotalNormAnnularPartitionJointSchwartz K S Γ
        a ha a0 b0 ha0 haSupport ψ hψ hψsupport ν ζ ξ φ R
          (traceJointToProduct K (v + (l : W)))) =
      traceProductMixedPoissonCoefficient K I J *
        ∑' m : D, latticePhase v (m : W) *
          sUnitTotalNormAnnularPartitionJointFourier K S Γ
            a ha a0 b0 ha0 haSupport ψ hψ hψsupport ν ζ ξ φ R
              ((traceJointConjugation K).symm (m : W)) := by
  let H := sUnitTotalNormAnnularPartitionJointSchwartz K S Γ
    a ha a0 b0 ha0 haSupport ψ hψ hψsupport ν ζ ξ φ R
  let F : SchwartzMap W ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (traceJointToProduct K) H
  let G := sUnitTotalNormAnnularPartitionJointFourier K S Γ
    a ha a0 b0 ha0 haSupport ψ hψ hψsupport ν ζ ξ φ R
  have hG : G = traceJointFourierCLM K F := rfl
  let jac : ℂ := (((2 : ℝ) ^ nrComplexPlaces K) ^ 2 : ℝ)
  have hFT (m : W) :
      (𝓕 (F : W → ℂ)) m =
        jac * G ((traceJointConjugation K).symm m) := by
    rw [hG, traceJointFourierCLM_apply, LinearIsometryEquiv.apply_symm_apply]
    have hj : (((((2 : ℝ) ^ nrComplexPlaces K) ^ 2) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast pow_ne_zero 2
        (pow_ne_zero (nrComplexPlaces K) (by norm_num : (2 : ℝ) ≠ 0))
    dsimp only [jac]
    push_cast at hj ⊢
    rw [← mul_assoc, mul_inv_cancel₀ hj, one_mul]
  change (∑' l : traceProductIdealLattice K I J, F (v + (l : W))) =
    traceProductMixedPoissonCoefficient K I J *
      ∑' m : D, latticePhase v (m : W) *
        G ((traceJointConjugation K).symm (m : W))
  have h := traceProductPoisson K I J F v
  simp_rw [hFT, ← latticePhase_eq_exp] at h
  have hsum :
      (∑' m : D, (jac * G ((traceJointConjugation K).symm (m : W))) *
        latticePhase v (m : W)) =
      jac * ∑' m : D, latticePhase v (m : W) *
        G ((traceJointConjugation K).symm (m : W)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    ring
  rw [hsum] at h
  rw [h]
  unfold traceProductMixedPoissonCoefficient
  dsimp only [jac]
  ring

end HeckeGeneral.Analysis
