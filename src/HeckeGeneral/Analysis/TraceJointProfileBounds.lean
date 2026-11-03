import HeckeGeneral.Analysis.TraceLogNormSmooth
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Quantitative composition of the genuine Fourier orbital kernel with the
two actual archimedean log norms. A fixed compact subset of the regular locus
supplies its own derivative constants and radius threshold. The resulting
bound concerns full multilinear derivatives on weighted trace vector space;
no partition of unity or final Schwartz seminorm reconstruction is assumed. -/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped Classical ContDiff BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Ω" => (Set.prod (traceArchRegular K) (traceArchRegular K))

def traceJointLogNormMap (p : V × V) : ℝ × ℝ :=
  (traceArchLogNorm K p.1, traceArchLogNorm K p.2)

theorem contDiffAt_traceJointLogNormMap {p : V × V} (hp : p ∈ Ω) :
    ContDiffAt ℝ ∞ (traceJointLogNormMap K) p :=
  ((contDiffAt_traceArchLogNorm K hp.1).comp p contDiff_fst.contDiffAt).prodMk
    ((contDiffAt_traceArchLogNorm K hp.2).comp p contDiff_snd.contDiffAt)

theorem contDiffOn_traceJointLogNormMap :
    ContDiffOn ℝ ∞ (traceJointLogNormMap K) Ω :=
  fun _ hp => (contDiffAt_traceJointLogNormMap K hp).contDiffWithinAt

/-- All finitely many actual derivatives of the inner log-norm map are bounded
on a fixed compact set. The constant is obtained from continuity and compactness,
not supplied as a derivative-bound hypothesis. -/
theorem exists_traceJointLogNormMap_compact_derivative_bound
    (A : Set (V × V)) (hA : IsCompact A) (hAΩ : A ⊆ Ω) (J : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ p ∈ A, ∀ i : ℕ, 1 ≤ i → i ≤ J →
      ‖iteratedFDerivWithin ℝ i (traceJointLogNormMap K) Ω p‖ ≤ D ^ i := by
  have hΩ : IsOpen Ω := (isOpen_traceArchRegular K).prod (isOpen_traceArchRegular K)
  have hf := contDiffOn_traceJointLogNormMap K
  have hbi (i : ℕ) : ∃ b : ℝ, ∀ p ∈ A,
      ‖iteratedFDerivWithin ℝ i (traceJointLogNormMap K) Ω p‖ ≤ b := by
    obtain ⟨b, hb⟩ := hA.bddAbove_image
      (((hf.continuousOn_iteratedFDerivWithin (m := i) (by simp) hΩ.uniqueDiffOn).norm).mono hAΩ)
    exact ⟨b, fun p hp => hb (Set.mem_image_of_mem _ hp)⟩
  choose b hb using hbi
  let D : ℝ := 1 + ∑ i ∈ Finset.range (J + 1), max (b i) 0
  have hsum : 0 ≤ ∑ i ∈ Finset.range (J + 1), max (b i) 0 :=
    Finset.sum_nonneg (fun i _ => le_max_right _ _)
  have hD : 1 ≤ D := by dsimp [D]; linarith
  refine ⟨D, hD, fun p hp i hi hiJ => ?_⟩
  have hi' : i ∈ Finset.range (J + 1) := Finset.mem_range.mpr (by omega)
  have hsingle : max (b i) 0 ≤ ∑ k ∈ Finset.range (J + 1), max (b k) 0 :=
    Finset.single_le_sum (fun k _ => le_max_right _ _) hi'
  have hiD : b i ≤ D := by
    dsimp [D]
    linarith [le_max_left (b i) 0]
  exact ((hb i p hp).trans hiD).trans (le_self_pow₀ hD (by omega))

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

/-- Actual two-column orbital kernel on trace vector space. -/
def traceJointOrbitalKernel (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (R : {r : ℝ // 0 < r}) : V × V → ℂ :=
  sUnitJointRadialProfile K S φ ψ R 0 ∘ traceJointLogNormMap K

local notation "L" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

include Γ in
/-- On any fixed compact regular two-column region, all derivatives through J
have a common bound by finite original Schwartz seminorms times R^(-B).
The genuine profile radius is at least one because R exceeds an explicitly
selected compact upper bound for the product of the two arithmetic norms.
B may be any real number; positivity of those norms controls their B-th power. -/
theorem exists_traceJointOrbitalKernel_compact_power_bound
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (A : Set (V × V)) (hA : IsCompact A) (hAΩ : A ⊆ Ω)
    (B : ℝ) (M : ℕ) (hM : Module.finrank ℤ L < M)
    (hOrder : (Module.finrank ℚ K : ℝ) * B ≤ M) (J : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C R0 : ℝ, 0 ≤ C ∧ 1 ≤ R0 ∧
      ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r}, R0 ≤ R.val →
      ∀ p ∈ A, ∀ n : ℕ, n ≤ J →
        ‖iteratedFDeriv ℝ n (traceJointOrbitalKernel K S φ ψ R) p‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B) := by
  let F := traceJointLogNormMap K
  let q : V × V → ℝ := fun p => traceArchProductNorm K p.1 * traceArchProductNorm K p.2
  have hq : Continuous q := ((continuous_traceArchProductNorm K).comp continuous_fst).mul
    ((continuous_traceArchProductNorm K).comp continuous_snd)
  have hqpos (p : V × V) (hp : p ∈ A) : 0 < q p :=
    mul_pos (traceArchProductNorm_pos K (hAΩ hp).1)
      (traceArchProductNorm_pos K (hAΩ hp).2)
  obtain ⟨H, hH⟩ := hA.bddAbove_image hq.continuousOn
  have hqB : ContinuousOn (fun p => q p ^ B) A :=
    hq.continuousOn.rpow_const (fun p hp => Or.inl (hqpos p hp).ne')
  obtain ⟨Z, hZ⟩ := hA.bddAbove_image hqB
  let T : ℝ := max Z 0
  have hT : 0 ≤ T := le_max_right _ _
  have hqT (p : V × V) (hp : p ∈ A) : q p ^ B ≤ T :=
    (hZ (Set.mem_image_of_mem _ hp)).trans (le_max_left _ _)
  obtain ⟨D, hD, hinner⟩ :=
    exists_traceJointLogNormMap_compact_derivative_bound K A hA hAΩ J
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  obtain ⟨s, C, hC, houter⟩ := exists_sUnitJointRadialProfile_iteratedFDeriv_power_bound
    K S Γ ψ hψ hψsupport B M hM hOrder J
  refine ⟨s, (J.factorial : ℝ) * C * T * D ^ J, max 1 H,
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hC) hT) (pow_nonneg hD0 _),
    le_max_left _ _, fun φ R hR p hp n hn => ?_⟩
  have hpΩ := hAΩ hp
  have hΩ : IsOpen Ω := (isOpen_traceArchRegular K).prod (isOpen_traceArchRegular K)
  have hqp : 0 < q p := hqpos p hp
  have hqR : q p ≤ R.val :=
    (hH (Set.mem_image_of_mem _ hp)).trans ((le_max_right _ _).trans hR)
  have hρeq : Real.exp (Real.log R.val - (F p).1 - (F p).2) = R.val / q p := by
    change Real.exp (Real.log R.val - Real.log (traceArchProductNorm K p.1) -
      Real.log (traceArchProductNorm K p.2)) = _
    simpa only [q, Real.exp_log (traceArchProductNorm_pos K hpΩ.1),
      Real.exp_log (traceArchProductNorm_pos K hpΩ.2)] using
      sUnitJoint_exp_radius R (Real.log (traceArchProductNorm K p.1))
        (Real.log (traceArchProductNorm K p.2))
  have hρ : 1 ≤ Real.exp (Real.log R.val - (F p).1 - (F p).2) := by
    rw [hρeq]
    exact (le_div_iff₀ hqp).mpr (by simpa using hqR)
  let Q : ℝ := C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B) * T
  have hbase : 0 ≤ C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B) :=
    mul_nonneg (mul_nonneg hC (apply_nonneg _ _)) (Real.rpow_nonneg R.property.le _)
  have hQ : 0 ≤ Q := mul_nonneg hbase hT
  let G : ℝ × ℝ → ℂ := sUnitJointRadialProfile K S φ ψ R 0
  have hG : ContDiff ℝ ∞ G :=
    contDiff_sUnitJointRadialProfile K S Γ φ ψ hψ hψsupport R 0
  have hCG : ∀ i, i ≤ n → ‖iteratedFDerivWithin ℝ i G Set.univ (F p)‖ ≤ Q := by
    intro i hi
    rw [iteratedFDerivWithin_univ]
    have hiBound := houter φ R (F p) hρ i (hi.trans hn)
    rw [hρeq, Real.div_rpow R.property.le hqp.le, Real.rpow_neg hqp.le,
      div_inv_eq_mul] at hiBound
    calc
      _ ≤ C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (R.val ^ (-B) * q p ^ B) := hiBound
      _ = (C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B)) * q p ^ B := by ring
      _ ≤ Q := mul_le_mul_of_nonneg_left (hqT p hp) hbase
  have hc := norm_iteratedFDerivWithin_comp_le hG.contDiffOn
    (contDiffOn_traceJointLogNormMap K) (show (n : ℕ∞ω) ≤ ∞ by simp)
    uniqueDiffOn_univ hΩ.uniqueDiffOn (Set.mapsTo_univ F Ω) hpΩ hCG
    (fun i hi hin => hinner p hp i hi (hin.trans hn))
  have hcompAt : ContDiffAt ℝ ∞ (G ∘ F) p :=
    hG.contDiffAt.comp p (contDiffAt_traceJointLogNormMap K hpΩ)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hΩ.uniqueDiffOn
    (hcompAt.of_le (by simp)) hpΩ] at hc
  change ‖iteratedFDeriv ℝ n (traceJointOrbitalKernel K S φ ψ R) p‖ ≤
    (n.factorial : ℝ) * Q * D ^ n at hc
  have hfac : (n.factorial : ℝ) ≤ J.factorial := by exact_mod_cast Nat.factorial_le hn
  have hDn : D ^ n ≤ D ^ J := pow_le_pow_right₀ hD hn
  calc
    _ ≤ (n.factorial : ℝ) * Q * D ^ n := hc
    _ ≤ (J.factorial : ℝ) * Q * D ^ J :=
      mul_le_mul (mul_le_mul_of_nonneg_right hfac hQ) hDn
        (pow_nonneg (zero_le_one.trans hD) _) (mul_nonneg (by positivity) hQ)
    _ = ((J.factorial : ℝ) * C * T * D ^ J) *
        s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B) := by dsimp [Q]; ring

end HeckeGeneral.Analysis
