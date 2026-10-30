import HeckeGeneral.Analysis.TraceJointProfileBounds
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Data.Nat.Choose.Sum

/-! A fixed smooth compact cutoff turns the actual joint orbital kernel into
a Schwartz function on the full two-column trace vector space. Smooth extension
across the coordinate hyperplanes follows from local vanishing of the cutoff.
The quantitative bound uses the genuine Leibniz derivative estimate and the
proved compact-region orbital derivative bounds. No final Schwartz bound is
assumed, and no moving phase is included in this fixed-cutoff construction. -/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic Function
open scoped Classical ContDiff BigOperators nonZeroDivisors Topology

variable (K : Type) [Field K] [NumberField K]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Ω" => (Set.prod (traceArchRegular K) (traceArchRegular K))
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

def traceCutoffOrbitalKernel (χ : V × V → ℂ) (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (R : {r : ℝ // 0 < r}) (p : V × V) : ℂ :=
  χ p * traceJointOrbitalKernel K S φ ψ R p

theorem tsupport_traceCutoffOrbitalKernel_subset (χ : V × V → ℂ)
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (R : {r : ℝ // 0 < r}) :
    tsupport (traceCutoffOrbitalKernel K S χ φ ψ R) ⊆ tsupport χ :=
  tsupport_mul_subset_left

theorem hasCompactSupport_traceCutoffOrbitalKernel (χ : V × V → ℂ)
    (hχsupport : HasCompactSupport χ) (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ) (R : {r : ℝ // 0 < r}) :
    HasCompactSupport (traceCutoffOrbitalKernel K S χ φ ψ R) :=
  hχsupport.mul_right

/-- Every derivative of the actual cutoff product vanishes outside its cutoff
support, including points on the excluded mixed-coordinate hyperplanes. -/
theorem iteratedFDeriv_traceCutoffOrbitalKernel_zero (χ : V × V → ℂ)
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (R : {r : ℝ // 0 < r}) (n : ℕ) {p : V × V} (hp : p ∉ tsupport χ) :
    iteratedFDeriv ℝ n (traceCutoffOrbitalKernel K S χ φ ψ R) p = 0 := by
  apply notMem_support.mp
  intro h
  exact hp ((tsupport_traceCutoffOrbitalKernel_subset K S χ φ ψ R)
    (support_iteratedFDeriv_subset n h))

include Γ in
theorem contDiffAt_traceJointOrbitalKernel (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (R : {r : ℝ // 0 < r}) {p : V × V} (hp : p ∈ Ω) :
    ContDiffAt ℝ ∞ (traceJointOrbitalKernel K S φ ψ R) p := by
  have hΩ : IsOpen Ω := (isOpen_traceArchRegular K).prod (isOpen_traceArchRegular K)
  exact (contDiffOn_sUnitJointRadialProfile_traceLogNorm K S Γ φ ψ hψ hψsupport R 0).contDiffAt
    (hΩ.mem_nhds hp)

include Γ in
theorem contDiff_traceCutoffOrbitalKernel (χ : V × V → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hχΩ : tsupport χ ⊆ Ω) (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (R : {r : ℝ // 0 < r}) :
    ContDiff ℝ ∞ (traceCutoffOrbitalKernel K S χ φ ψ R) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p ∈ tsupport χ
  · exact hχ.contDiffAt.mul
      (contDiffAt_traceJointOrbitalKernel K S Γ φ ψ hψ hψsupport R (hχΩ hp))
  · have hz : χ =ᶠ[𝓝 p] 0 := notMem_tsupport_iff_eventuallyEq.mp hp
    have hz' : traceCutoffOrbitalKernel K S χ φ ψ R =ᶠ[𝓝 p] (fun _ => 0) := by
      filter_upwards [hz] with q hq
      change χ q * traceJointOrbitalKernel K S φ ψ R q = 0
      simpa only [Pi.zero_apply, zero_mul] using congrArg
        (fun c : ℂ => c * traceJointOrbitalKernel K S φ ψ R q) hq
    exact contDiffAt_const.congr_of_eventuallyEq hz'

/-- An actual Schwartz function, not a package assuming Schwartz estimates. -/
def traceCutoffOrbitalSchwartz
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (χ : V × V → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hχsupport : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) : SchwartzMap (V × V) ℂ :=
  (hasCompactSupport_traceCutoffOrbitalKernel K S χ hχsupport φ ψ R).toSchwartzMap
    (contDiff_traceCutoffOrbitalKernel K S Γ χ hχ hχΩ φ ψ hψ hψsupport R)

@[simp] theorem traceCutoffOrbitalSchwartz_apply
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (χ : V × V → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hχsupport : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) (p : V × V) :
    traceCutoffOrbitalSchwartz K S Γ ψ hψ hψsupport χ hχ hχsupport hχΩ φ R p =
      χ p * traceJointOrbitalKernel K S φ ψ R p := rfl

include Γ in
/-- The actual multivariable Leibniz estimate on the regular locus. -/
theorem norm_iteratedFDeriv_traceCutoffOrbitalKernel_le
    (χ : V × V → ℂ) (hχ : ContDiff ℝ ∞ χ) (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (R : {r : ℝ // 0 < r}) (n : ℕ) {p : V × V} (hp : p ∈ Ω) :
    ‖iteratedFDeriv ℝ n (traceCutoffOrbitalKernel K S χ φ ψ R) p‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ p‖ *
        ‖iteratedFDeriv ℝ (n - i) (traceJointOrbitalKernel K S φ ψ R) p‖ := by
  have hΩ : IsOpen Ω := (isOpen_traceArchRegular K).prod (isOpen_traceArchRegular K)
  have hg : ContDiffOn ℝ ∞ (traceJointOrbitalKernel K S φ ψ R) Ω :=
    contDiffOn_sUnitJointRadialProfile_traceLogNorm K S Γ φ ψ hψ hψsupport R 0
  have hgp := contDiffAt_traceJointOrbitalKernel K S Γ φ ψ hψ hψsupport R hp
  have hb := norm_iteratedFDerivWithin_mul_le hχ.contDiffOn hg hΩ.uniqueDiffOn hp
    (show (n : ℕ∞ω) ≤ ∞ by simp)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hΩ.uniqueDiffOn
    ((hχ.contDiffAt.mul hgp).of_le (by simp)) hp] at hb
  simp_rw [iteratedFDerivWithin_eq_iteratedFDeriv hΩ.uniqueDiffOn
      (hχ.contDiffAt.of_le (by simp)) hp,
    iteratedFDerivWithin_eq_iteratedFDeriv hΩ.uniqueDiffOn (hgp.of_le (by simp)) hp] at hb
  exact hb

/-- Smooth compact support supplies the common derivative constant through any
fixed order. This is proved for the cutoff itself, independently of the kernel. -/
theorem exists_traceCutoff_derivative_bound (χ : V × V → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hχsupport : HasCompactSupport χ) (J : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ i : ℕ, i ≤ J → ∀ p, ‖iteratedFDeriv ℝ i χ p‖ ≤ L := by
  have hbi (i : ℕ) : ∃ b : ℝ, ∀ p, ‖iteratedFDeriv ℝ i χ p‖ ≤ b :=
    (hχsupport.iteratedFDeriv i).exists_bound_of_continuous
      (hχ.continuous_iteratedFDeriv (m := i) (by simp))
  choose b hb using hbi
  let L : ℝ := ∑ i ∈ Finset.range (J + 1), max (b i) 0
  refine ⟨L, Finset.sum_nonneg (fun i _ => le_max_right _ _), fun i hi p => ?_⟩
  have himem : i ∈ Finset.range (J + 1) := Finset.mem_range.mpr (by omega)
  exact (hb i p).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun k _ => le_max_right _ _) himem))

local notation "Lattice" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

include Γ in
/-- Genuine Schwartz seminorm bounds for the compactly supported joint orbital
kernel. Weight k and derivative orders through J share finite original φ
seminorms, a constant, and a support-dependent threshold, all chosen before φ/R.
No assertion for all R ≥ 1 or for an unconstructed unit partition is made. -/
theorem exists_traceCutoffOrbitalSchwartz_seminorm_power_bound
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (χ : V × V → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hχsupport : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (B : ℝ) (M : ℕ) (hM : Module.finrank ℤ Lattice < M)
    (hOrder : (Module.finrank ℚ K : ℝ) * B ≤ M) (k J : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C R0 : ℝ, 0 ≤ C ∧ 1 ≤ R0 ∧
      ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r}, R0 ≤ R.val →
      ∀ n : ℕ, n ≤ J →
        SchwartzMap.seminorm ℝ k n
          (traceCutoffOrbitalSchwartz K S Γ ψ hψ hψsupport χ hχ hχsupport hχΩ φ R) ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B) := by
  obtain ⟨s, C, R0, hC, hR0, hkernel⟩ := exists_traceJointOrbitalKernel_compact_power_bound
    K S Γ ψ hψ hψsupport (tsupport χ) hχsupport hχΩ B M hM hOrder J
  obtain ⟨L, hL, hcutoff⟩ := exists_traceCutoff_derivative_bound K χ hχ hχsupport J
  obtain ⟨H, hH⟩ := hχsupport.bddAbove_image (continuous_norm.continuousOn)
  let W : ℝ := max H 0
  have hW : 0 ≤ W := le_max_right _ _
  have hweight (p : V × V) (hp : p ∈ tsupport χ) : ‖p‖ ^ k ≤ W ^ k :=
    pow_le_pow_left₀ (norm_nonneg _)
      ((hH (Set.mem_image_of_mem _ hp)).trans (le_max_left _ _)) k
  have hfactor : 0 ≤ W ^ k * (2 : ℝ) ^ J * L * C :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hW _) (by positivity)) hL) hC
  refine ⟨s, W ^ k * (2 : ℝ) ^ J * L * C, R0,
    hfactor, hR0, fun φ R hR n hn => ?_⟩
  let Q : ℝ := C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B)
  have hQ : 0 ≤ Q :=
    mul_nonneg (mul_nonneg hC (apply_nonneg _ _)) (Real.rpow_nonneg R.property.le _)
  have hnorm (p : V × V) (hp : p ∈ tsupport χ) :
      ‖iteratedFDeriv ℝ n (traceCutoffOrbitalKernel K S χ φ ψ R) p‖ ≤
        (2 : ℝ) ^ J * L * Q := by
    have hleib := norm_iteratedFDeriv_traceCutoffOrbitalKernel_le
      K S Γ χ hχ φ ψ hψ hψsupport R n (hχΩ hp)
    have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
      exact_mod_cast Nat.sum_range_choose n
    calc
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ p‖ *
          ‖iteratedFDeriv ℝ (n - i) (traceJointOrbitalKernel K S φ ψ R) p‖ := hleib
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * L * Q := by
        apply Finset.sum_le_sum
        intro i hi
        have hin : i ≤ n := Finset.mem_range_succ_iff.mp hi
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hcutoff i (hin.trans hn) p)
          (Nat.cast_nonneg _))
          (hkernel φ R hR p hp (n - i) ((Nat.sub_le n i).trans hn))
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hL)
      _ = (2 : ℝ) ^ n * L * Q := by rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
      _ ≤ (2 : ℝ) ^ J * L * Q :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hL) hQ
  have hfinal : 0 ≤ (W ^ k * (2 : ℝ) ^ J * L * C) *
      s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B) :=
    mul_nonneg (mul_nonneg hfactor (apply_nonneg _ _)) (Real.rpow_nonneg R.property.le _)
  apply SchwartzMap.seminorm_le_bound ℝ k n _ hfinal
  intro p
  change ‖p‖ ^ k * ‖iteratedFDeriv ℝ n (traceCutoffOrbitalKernel K S χ φ ψ R) p‖ ≤ _
  by_cases hp : p ∈ tsupport χ
  · calc
      _ ≤ W ^ k * ((2 : ℝ) ^ J * L * Q) :=
        mul_le_mul (hweight p hp) (hnorm p hp) (norm_nonneg _) (pow_nonneg hW _)
      _ = (W ^ k * (2 : ℝ) ^ J * L * C) *
          s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B) := by dsimp [Q]; ring
  · rw [iteratedFDeriv_traceCutoffOrbitalKernel_zero K S χ φ ψ R n hp, norm_zero, mul_zero]
    exact hfinal

end HeckeGeneral.Analysis
