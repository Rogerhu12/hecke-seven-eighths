import HeckeSkeleton.Moments.MOM_INV_STEP.CommonKernel
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Data.Nat.Choose.Sum

/-!
# Uniform bounds for the actual common Fourier density

All finite original-test seminorms, constants, and radius thresholds are
selected before the original Schwartz test and the outer radius.  The
estimates follow from the proved joint orbital Euler bounds and the fixed
compact cutoff.  In particular an individual outer radius does not come
with an independently assumed Fourier mass.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CommonKernel

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
  HeckeGeneral.Bridge MeasureTheory
open scoped Classical ContDiff BigOperators nonZeroDivisors FourierTransform

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Lattice" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
variable (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
  (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)

private def rawProfile (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) : LogPlane → ℂ :=
  fun p => sUnitJointRadialProfile K S φ ψ R 0 (logCoordinates p)

include Γ hψ hψsupport in
private theorem rawProfile_contDiff (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) :
    ContDiff ℝ ∞ (rawProfile K S ψ φ R) :=
  (contDiff_sUnitJointRadialProfile K S Γ φ ψ hψ hψsupport R 0).comp
    logCoordinates.contDiff

include Γ hψ hψsupport in
private theorem exists_rawProfile_compact_bound
    (A : Set LogPlane) (hA : IsCompact A)
    (B : ℝ) (M : ℕ) (hM : Module.finrank ℤ Lattice < M)
    (hOrder : (Module.finrank ℚ K : ℝ) * B ≤ M) (J : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C R0 : ℝ, 0 ≤ C ∧ 1 ≤ R0 ∧
      ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r}, R0 ≤ R.val →
      ∀ p ∈ A, ∀ n : ℕ, n ≤ J →
        ‖iteratedFDeriv ℝ n (rawProfile K S ψ φ R) p‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B) := by
  let q : LogPlane → ℝ := fun p => Real.exp p.fst * Real.exp p.snd
  have hq : Continuous q :=
    (Real.continuous_exp.comp logCoordinates.continuous.fst).mul
      (Real.continuous_exp.comp logCoordinates.continuous.snd)
  have hqpos (p : LogPlane) : 0 < q p := mul_pos (Real.exp_pos _) (Real.exp_pos _)
  obtain ⟨H, hH⟩ := hA.bddAbove_image hq.continuousOn
  have hqB : ContinuousOn (fun p => q p ^ B) A :=
    hq.continuousOn.rpow_const (fun p _ => Or.inl (hqpos p).ne')
  obtain ⟨Z, hZ⟩ := hA.bddAbove_image hqB
  let T : ℝ := max Z 0
  have hT : 0 ≤ T := le_max_right _ _
  have hqT (p : LogPlane) (hp : p ∈ A) : q p ^ B ≤ T :=
    (hZ (Set.mem_image_of_mem _ hp)).trans (le_max_left _ _)
  let E := logCoordinates.toContinuousLinearMap
  let D0 : ℝ := max 1 ‖E‖
  have hD0 : 1 ≤ D0 := le_max_left _ _
  obtain ⟨s, C, hC, hb⟩ := exists_sUnitJointRadialProfile_iteratedFDeriv_power_bound
    K S Γ ψ hψ hψsupport B M hM hOrder J
  refine ⟨s, C * T * D0 ^ J, max 1 H,
    mul_nonneg (mul_nonneg hC hT) (pow_nonneg (zero_le_one.trans hD0) _),
    le_max_left _ _, fun φ R hR p hp n hn => ?_⟩
  have hqR : q p ≤ R.val :=
    (hH (Set.mem_image_of_mem _ hp)).trans ((le_max_right _ _).trans hR)
  have hρeq : Real.exp (Real.log R.val - p.fst - p.snd) = R.val / q p :=
    sUnitJoint_exp_radius R p.fst p.snd
  have hρ : 1 ≤ Real.exp (Real.log R.val - p.fst - p.snd) := by
    rw [hρeq]
    exact (le_div_iff₀ (hqpos p)).mpr (by simpa using hqR)
  have houter := hb φ R (logCoordinates p) hρ n hn
  change ‖iteratedFDeriv ℝ n (sUnitJointRadialProfile K S φ ψ R 0)
    (logCoordinates p)‖ ≤ _ at houter
  rw [hρeq, Real.div_rpow R.property.le (hqpos p).le,
    Real.rpow_neg (hqpos p).le, div_inv_eq_mul] at houter
  have hbase : 0 ≤ C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B) :=
    mul_nonneg (mul_nonneg hC (apply_nonneg _ _)) (Real.rpow_nonneg R.property.le _)
  have hout : ‖iteratedFDeriv ℝ n (sUnitJointRadialProfile K S φ ψ R 0)
      (logCoordinates p)‖ ≤
      (C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B)) * T := by
    calc
      _ ≤ C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
          (R.val ^ (-B) * q p ^ B) := houter
      _ = (C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B)) * q p ^ B := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hqT p hp) hbase
  have hscale : ‖E‖ ^ n ≤ D0 ^ J :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ hD0 hn)
  have hG := contDiff_sUnitJointRadialProfile K S Γ φ ψ hψ hψsupport R 0
  change ‖iteratedFDeriv ℝ n ((sUnitJointRadialProfile K S φ ψ R 0) ∘ E) p‖ ≤ _
  rw [E.iteratedFDeriv_comp_right hG p (by simp)]
  have hcomp := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ n (sUnitJointRadialProfile K S φ ψ R 0) (E p))
    (fun _ : Fin n => E)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcomp
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (sUnitJointRadialProfile K S φ ψ R 0) (E p)‖ * ‖E‖ ^ n := hcomp
    _ ≤ ((C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B)) * T) * D0 ^ J :=
      mul_le_mul hout hscale (pow_nonneg (norm_nonneg _) _) (mul_nonneg hbase hT)
    _ = _ := by ring

variable (χ : LogPlane → ℂ) (hχ : ContDiff ℝ ∞ χ)
  (hχsupport : HasCompactSupport χ)

/-- One uniform seminorm bound for the genuine cutoff orbital kernel.
The support-dependent threshold is fixed before φ and the outer radius. -/
theorem exists_orbitalKernel_seminorm_power_bound
    (B : ℝ) (M : ℕ) (hM : Module.finrank ℤ Lattice < M)
    (hOrder : (Module.finrank ℚ K : ℝ) * B ≤ M) (k J : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C R0 : ℝ, 0 ≤ C ∧ 1 ≤ R0 ∧
      ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r}, R0 ≤ R.val →
      ∀ n : ℕ, n ≤ J →
        SchwartzMap.seminorm ℝ k n
          (orbitalKernel K S Γ ψ hψ hψsupport χ hχ hχsupport φ R) ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B) := by
  obtain ⟨s, C, R0, hC, hR0, hb⟩ := exists_rawProfile_compact_bound
    K S Γ ψ hψ hψsupport (tsupport χ) hχsupport B M hM hOrder J
  have hbi (i : ℕ) : ∃ b : ℝ, ∀ p, ‖iteratedFDeriv ℝ i χ p‖ ≤ b :=
    (hχsupport.iteratedFDeriv i).exists_bound_of_continuous
      (hχ.continuous_iteratedFDeriv (m := i) (by simp))
  choose b hbound using hbi
  let L : ℝ := ∑ i ∈ Finset.range (J + 1), max (b i) 0
  have hL : 0 ≤ L := Finset.sum_nonneg (fun i _ => le_max_right _ _)
  have hcut (i : ℕ) (hi : i ≤ J) (p : LogPlane) : ‖iteratedFDeriv ℝ i χ p‖ ≤ L :=
    (hbound i p).trans ((le_max_left _ _).trans
      (Finset.single_le_sum (fun j _ => le_max_right _ _)
        (Finset.mem_range.mpr (by omega))))
  obtain ⟨H, hH⟩ := hχsupport.bddAbove_image (continuous_norm.continuousOn)
  let W : ℝ := max H 0
  have hW : 0 ≤ W := le_max_right _ _
  have hweight (p : LogPlane) (hp : p ∈ tsupport χ) : ‖p‖ ^ k ≤ W ^ k :=
    pow_le_pow_left₀ (norm_nonneg _)
      ((hH (Set.mem_image_of_mem _ hp)).trans (le_max_left _ _)) k
  have hfactor : 0 ≤ W ^ k * (2 : ℝ) ^ J * L * C := by positivity
  refine ⟨s, W ^ k * (2 : ℝ) ^ J * L * C, R0, hfactor, hR0,
    fun φ R hR n hn => ?_⟩
  let Q : ℝ := C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B)
  have hQ : 0 ≤ Q :=
    mul_nonneg (mul_nonneg hC (apply_nonneg _ _)) (Real.rpow_nonneg R.property.le _)
  have hnorm (p : LogPlane) (hp : p ∈ tsupport χ) :
      ‖iteratedFDeriv ℝ n (fun p => χ p * rawProfile K S ψ φ R p) p‖ ≤
        (2 : ℝ) ^ J * L * Q := by
    have hleib := norm_iteratedFDeriv_mul_le hχ
      (rawProfile_contDiff K S Γ ψ hψ hψsupport φ R) p
      (show (n : ℕ∞ω) ≤ ∞ by simp)
    have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
      exact_mod_cast Nat.sum_range_choose n
    calc
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i χ p‖ * ‖iteratedFDeriv ℝ (n - i) (rawProfile K S ψ φ R) p‖ := hleib
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * L * Q := by
        apply Finset.sum_le_sum
        intro i hi
        have hin : i ≤ n := Finset.mem_range_succ_iff.mp hi
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hcut i (hin.trans hn) p)
          (Nat.cast_nonneg _))
          (hb φ R hR p hp (n - i) ((Nat.sub_le n i).trans hn))
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hL)
      _ = (2 : ℝ) ^ n * L * Q := by rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hL) hQ
  have hfinal : 0 ≤ (W ^ k * (2 : ℝ) ^ J * L * C) *
      s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B) :=
    mul_nonneg (mul_nonneg hfactor (apply_nonneg _ _)) (Real.rpow_nonneg R.property.le _)
  apply SchwartzMap.seminorm_le_bound ℝ k n _ hfinal
  intro p
  change ‖p‖ ^ k * ‖iteratedFDeriv ℝ n (fun p => χ p * rawProfile K S ψ φ R p) p‖ ≤ _
  by_cases hp : p ∈ tsupport χ
  · calc
      _ ≤ W ^ k * ((2 : ℝ) ^ J * L * Q) :=
        mul_le_mul (hweight p hp) (hnorm p hp) (norm_nonneg _) (pow_nonneg hW _)
      _ = _ := by dsimp only [Q]; ring
  · have hz : iteratedFDeriv ℝ n (fun p => χ p * rawProfile K S ψ φ R p) p = 0 := by
      apply notMem_support.mp
      intro h
      exact hp (tsupport_mul_subset_left (support_iteratedFDeriv_subset n h))
    rw [hz, norm_zero, mul_zero]
    exact hfinal

/-- Finite aggregation retains one family of original-test seminorms and
one constant for all requested target seminorms. -/
theorem exists_orbitalKernel_finite_seminorm_power_bound
    (B : ℝ) (M : ℕ) (hM : Module.finrank ℤ Lattice < M)
    (hOrder : (Module.finrank ℚ K : ℝ) * B ≤ M) (t : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C R0 : ℝ, 0 ≤ C ∧ 1 ≤ R0 ∧
      ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r}, R0 ≤ R.val →
        t.sup (schwartzSeminormFamily ℝ LogPlane ℂ)
          (orbitalKernel K S Γ ψ hψ hψsupport χ hχ hχsupport φ R) ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B) := by
  have hex (j : ℕ × ℕ) := exists_orbitalKernel_seminorm_power_bound
    K S Γ ψ hψ hψsupport χ hχ hχsupport B M hM hOrder j.1 j.2
  choose s C R0 hC _hR0 hb using hex
  let sall := t.biUnion s
  let Call : ℝ := ∑ j ∈ t, C j
  let Rall : ℝ := 1 + ∑ j ∈ t, max (R0 j) 0
  have hCall : 0 ≤ Call := Finset.sum_nonneg (fun j _ => hC j)
  have hRall : 1 ≤ Rall :=
    le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => le_max_right _ _))
  refine ⟨sall, Call, Rall, hCall, hRall, fun φ R hR => ?_⟩
  have hfinal : 0 ≤ Call * sall.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B) :=
    mul_nonneg (mul_nonneg hCall (apply_nonneg _ _)) (Real.rpow_nonneg R.property.le _)
  apply Seminorm.finset_sup_apply_le hfinal
  intro j hj
  have hCj : C j ≤ Call := Finset.single_le_sum (fun i _ => hC i) hj
  have hRj : R0 j ≤ Rall := by
    calc
      R0 j ≤ max (R0 j) 0 := le_max_left _ _
      _ ≤ ∑ i ∈ t, max (R0 i) 0 := Finset.single_le_sum (fun i _ => le_max_right _ _) hj
      _ ≤ Rall := le_add_of_nonneg_left (by norm_num)
  have hsj : (s j).sup (schwartzSeminormFamily ℝ V ℂ) φ ≤
      sall.sup (schwartzSeminormFamily ℝ V ℂ) φ :=
    Seminorm.finset_sup_apply_le (apply_nonneg _ _)
      (fun i hi => Seminorm.le_finset_sup_apply (Finset.mem_biUnion.mpr ⟨j, hj, hi⟩))
  exact (hb j φ R (hRj.trans hR) j.2 le_rfl).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul hCj hsj (apply_nonneg _ _) hCall) (Real.rpow_nonneg R.property.le _))

/-- A common L¹ density bound, uniform in the actual outer radius and
the original test function. -/
theorem exists_orbitalDensity_mass_power_bound
    (B : ℝ) (M : ℕ) (hM : Module.finrank ℤ Lattice < M)
    (hOrder : (Module.finrank ℚ K : ℝ) * B ≤ M) :
    ∃ s : Finset (ℕ × ℕ), ∃ C R0 : ℝ, 0 ≤ C ∧ 1 ≤ R0 ∧
      ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r}, R0 ≤ R.val →
        (∫ ξ : LogPlane, ‖orbitalDensity K S Γ ψ hψ hψsupport χ hχ hχsupport φ R ξ‖) ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B) := by
  obtain ⟨t, D0, _hD0, hfourier⟩ := exists_spectralMass_seminorm_bound
  obtain ⟨s, C, R0, hC, hR0, hb⟩ := exists_orbitalKernel_finite_seminorm_power_bound
    K S Γ ψ hψ hψsupport χ hχ hχsupport B M hM hOrder t
  refine ⟨s, (D0 : ℝ) * C, R0, mul_nonneg D0.coe_nonneg hC, hR0,
    fun φ R hR => ?_⟩
  exact (hfourier (orbitalKernel K S Γ ψ hψ hψsupport χ hχ hχsupport φ R)).trans
    ((mul_le_mul_of_nonneg_left (hb φ R hR) D0.coe_nonneg).trans_eq (by ring))

/-- One Fourier-frequency envelope for every outer radius.  In
particular the residual radius cannot select its own frequency cutoff. -/
theorem exists_orbitalDensity_weighted_power_bound
    (B : ℝ) (M : ℕ) (hM : Module.finrank ℤ Lattice < M)
    (hOrder : (Module.finrank ℚ K : ℝ) * B ≤ M) (q : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C R0 : ℝ, 0 ≤ C ∧ 1 ≤ R0 ∧
      ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r}, R0 ≤ R.val →
      ∀ ξ : LogPlane,
        (1 + ‖ξ‖) ^ q *
          ‖orbitalDensity K S Γ ψ hψ hψsupport χ hχ hχsupport φ R ξ‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B) := by
  obtain ⟨t, D0, hD0, hfourier⟩ := exists_weighted_fourier_bound q
  obtain ⟨s, C, R0, hC, hR0, hb⟩ := exists_orbitalKernel_finite_seminorm_power_bound
    K S Γ ψ hψ hψsupport χ hχ hχsupport B M hM hOrder t
  refine ⟨s, D0 * C, R0, mul_nonneg hD0 hC, hR0, fun φ R hR ξ => ?_⟩
  exact (hfourier (orbitalKernel K S Γ ψ hψ hψsupport χ hχ hχsupport φ R) ξ).trans
    ((mul_le_mul_of_nonneg_left (hb φ R hR) hD0).trans_eq (by ring))

/-- The actual densities share the same fixed integrable Fourier
envelope.  Only the scalar original-test seminorm and radius decay vary. -/
theorem exists_orbitalDensity_common_envelope
    (B : ℝ) (M : ℕ) (hM : Module.finrank ℤ Lattice < M)
    (hOrder : (Module.finrank ℚ K : ℝ) * B ≤ M) :
    ∃ s : Finset (ℕ × ℕ), ∃ C R0 : ℝ, 0 ≤ C ∧ 1 ≤ R0 ∧
      ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r}, R0 ≤ R.val →
      ∀ ξ : LogPlane,
        ‖orbitalDensity K S Γ ψ hψ hψsupport χ hχ hχsupport φ R ξ‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B)) *
            fourierEnvelope ξ := by
  let q := (volume : Measure LogPlane).integrablePower
  obtain ⟨s, C, R0, hC, hR0, hb⟩ := exists_orbitalDensity_weighted_power_bound
    K S Γ ψ hψ hψsupport χ hχ hχsupport B M hM hOrder q
  refine ⟨s, C, R0, hC, hR0, fun φ R hR ξ => ?_⟩
  have hpow : 0 < (1 + ‖ξ‖) ^ q := pow_pos (by positivity) _
  have hd := (le_div_iff₀ hpow).mpr (by simpa only [mul_comm] using hb φ R hR ξ)
  simpa only [fourierEnvelope, Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖),
    Real.rpow_natCast, div_eq_mul_inv, q] using hd

end HeckeSkeleton.Moments.MOM_INV_STEP.CommonKernel
