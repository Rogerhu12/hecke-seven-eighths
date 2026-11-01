import Expansion.ActualPrincipalZShift

/-!
# Genuine truncation errors for the two principal residue moves

The difference between a complete vertical integral and its original
finite-height truncation is estimated on the actual complement of the
height interval.  Combining this with the proved full-line residue
identities gives arbitrary inverse-height bounds for the two finite
residue moves.  The errors here are actual differences of contour
integrals, not arbitrary functions assumed to be small.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory Set Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.Expansion.PrincipalRows
open DedekindZetaZeroFree DedekindZetaZeroFree.Quantitative.SimplePoleVerticalShift
open scoped Classical Topology

def principalTailEnvelopeMass : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-2 : ℝ)

theorem principalTailEnvelopeMass_nonneg : 0 ≤ principalTailEnvelopeMass :=
  integral_nonneg fun t => Real.rpow_nonneg (by positivity) _

private theorem integrable_principalTailEnvelope :
    Integrable (fun t : ℝ => (1 + |t|) ^ (-2 : ℝ)) := by
  simpa only [Real.norm_eq_abs] using
    (integrable_one_add_norm (E := ℝ) (r := 2) (μ := volume) (by norm_num))

/-- The actual complement of [-H,H] gains the requested inverse power.
The remaining integrable envelope is fixed before the requested order. -/
theorem principal_rapid_integral_tail_bound
    (f : ℝ → ℂ) (hf : Continuous f) (M : ℝ) (hM : 0 ≤ M) (N : ℕ)
    (hbound : ∀ t : ℝ, 1 ≤ |t| → ‖f t‖ ≤ M * (1 + |t|) ^ (-((N : ℝ) + 2)))
    (H : ℝ) (hH : 1 ≤ H) :
    ‖(∫ t : ℝ, f t) - ∫ t in Icc (-H) H, f t‖ ≤
      (M * principalTailEnvelopeMass) * H ^ (-(N : ℝ)) := by
  have hi : Integrable f := integrable_of_decay f M 1 le_rfl hf (fun t ht =>
    (hbound t ht).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by have := abs_nonneg t; linarith : 1 ≤ 1 + |t|)
        (by linarith [show (0 : ℝ) ≤ (N : ℝ) by positivity])) hM))
  have htail : ∀ t ∈ (Icc (-H) H)ᶜ,
      ‖f t‖ ≤ (M * H ^ (-(N : ℝ))) * (1 + |t|) ^ (-2 : ℝ) := by
    intro t ht
    have habs : H ≤ |t| := by
      by_contra! hh
      exact ht ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    have hpow : (1 + |t|) ^ (-(N : ℝ)) ≤ H ^ (-(N : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith)
        (by linarith [show (0 : ℝ) ≤ (N : ℝ) by positivity])
    apply (hbound t (hH.trans habs)).trans
    rw [show -((N : ℝ) + 2) = -(N : ℝ) + (-2 : ℝ) by ring,
      Real.rpow_add (by positivity : 0 < 1 + |t|)]
    exact (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (by positivity) _)) hM).trans_eq (by ring)
  rw [← setIntegral_compl measurableSet_Icc hi]
  apply (norm_integral_le_integral_norm _).trans
  calc
    (∫ t in (Icc (-H) H)ᶜ, ‖f t‖) ≤
        ∫ t in (Icc (-H) H)ᶜ, (M * H ^ (-(N : ℝ))) * (1 + |t|) ^ (-2 : ℝ) :=
      integral_mono_ae hi.norm.integrableOn
        ((integrable_principalTailEnvelope.const_mul _).integrableOn)
        (ae_restrict_of_forall_mem measurableSet_Icc.compl htail)
    _ = (M * H ^ (-(N : ℝ))) *
        ∫ t in (Icc (-H) H)ᶜ, (1 + |t|) ^ (-2 : ℝ) := integral_const_mul _ _
    _ ≤ (M * H ^ (-(N : ℝ))) * principalTailEnvelopeMass :=
      mul_le_mul_of_nonneg_left
        (setIntegral_le_integral integrable_principalTailEnvelope
          (ae_of_all _ fun t => Real.rpow_nonneg (by positivity) _)) (by positivity)
    _ = _ := by ring

def principalFiniteVerticalIntegral (sigma H : ℝ) (f : ℂ → ℂ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ t in Icc (-H) H, f ((sigma : ℂ) + (t : ℂ) * Complex.I)

theorem principal_vertical_tail_bound
    (f : ℂ → ℂ) (sigma M : ℝ) (hM : 0 ≤ M) (N : ℕ)
    (hf : Continuous (fun t : ℝ => f ((sigma : ℂ) + (t : ℂ) * Complex.I)))
    (hbound : ∀ t : ℝ, 1 ≤ |t| →
      ‖f ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M * (1 + |t|) ^ (-((N : ℝ) + 2)))
    (H : ℝ) (hH : 1 ≤ H) :
    ‖comparisonVerticalIntegral sigma f - principalFiniteVerticalIntegral sigma H f‖ ≤
      (‖(2 * (Real.pi : ℂ))⁻¹‖ * M * principalTailEnvelopeMass) * H ^ (-(N : ℝ)) := by
  rw [comparisonVerticalIntegral, principalFiniteVerticalIntegral, ← mul_sub, norm_mul]
  exact (mul_le_mul_of_nonneg_left
    (principal_rapid_integral_tail_bound _ hf M hM N hbound H hH) (norm_nonneg _)).trans_eq
      (by ring)

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
local notation "muS" => (fun p : Sset => mu (Subtype.val p))

theorem actualPrincipal_w_truncated_shift
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {e : ℝ} (he : 0 < e) (he1 : e < 1 / 1000) (N : ℕ) :
    ∃ Z0 : ℝ, 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z → ∀ s z : ℂ,
      7 / 8 ≤ s.re → 33 / 200 ≤ z.re → z.re ≤ 1 →
      ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 1 ≤ H →
        ‖principalFiniteVerticalIntegral (1 + e) H
          (fun w => actualPrincipalKernelCore K S mu P psi g Z s w z
            (heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) w)) -
          principalFiniteVerticalIntegral (19 / 20) H
            (fun w => actualPrincipalKernelCore K S mu P psi g Z s w z
              (heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) w)) -
          actualPrincipalWResidueKernel K S mu P psi g Z s z‖ ≤ C * H ^ (-(N : ℝ)) := by
  obtain ⟨Za, hZa, ha⟩ := actualPrincipal_w_fullLine_shift K S mu hcomplex P psi hunram g he he1
  obtain ⟨Zb, hZb, hb⟩ := exists_actualPrincipal_w_strip_decay K S mu hcomplex P psi hunram
    g he he1 ((N : ℝ) + 2)
  refine ⟨max Za Zb, hZa.trans (le_max_left _ _), ?_⟩
  intro Z hZ s z hs hz hz1
  have hZA : Za ≤ Z := (le_max_left _ _).trans hZ
  have hZB : Zb ≤ Z := (le_max_right _ _).trans hZ
  have hZpos : 0 < Z := zero_lt_one.trans_le (hZa.trans hZA)
  obtain ⟨M, hM, hbound⟩ := hb Z hZB s z hs hz hz1
  let f : ℂ → ℂ := fun w => actualPrincipalKernelCore K S mu P psi g Z s w z
    (heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) w)
  let D : ℝ := ‖(2 * (Real.pi : ℂ))⁻¹‖ * M * principalTailEnvelopeMass
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (norm_nonneg _) hM.le) principalTailEnvelopeMass_nonneg
  have hcont (a : ℝ) (hlo : 19 / 20 ≤ a) (ha1 : a ≠ 1) :
      Continuous (fun t : ℝ => f ((a : ℂ) + (t : ℂ) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hne : (a : ℂ) + (t : ℂ) * Complex.I ≠ 1 := by
      intro h
      exact ha1 (by simpa using congrArg Complex.re h)
    have hline : ContinuousAt (fun r : ℝ => (a : ℂ) + (r : ℂ) * Complex.I) t := by
      fun_prop
    exact (differentiableAt_actualPrincipal_w_kernel K S mu P psi g Z hZpos s z _ hne
      (principal_rectangle_mem_rowEulerRegion s _ z hs (by simpa using hlo) hz)).continuousAt.comp_of_eq
        hline rfl
  refine ⟨2 * D + 1, by linarith, ?_⟩
  intro H hH
  have hleft := principal_vertical_tail_bound f (19 / 20) M hM.le N
    (hcont _ le_rfl (by norm_num))
    (fun t ht => by
      simpa [f] using hbound ((19 / 20 : ℂ) + (t : ℂ) * Complex.I)
        (by norm_num) (by simp; linarith) (by simpa using ht)) H hH
  have hright := principal_vertical_tail_bound f (1 + e) M hM.le N
    (hcont _ (by linarith) (by linarith))
    (fun t ht => by
      simpa [f] using hbound ((1 + e : ℝ) + (t : ℂ) * Complex.I)
        (by simp; linarith) (by simp) (by simpa using ht)) H hH
  have hshift := ha Z hZA s z hs hz hz1
  have heq : principalFiniteVerticalIntegral (1 + e) H f -
      principalFiniteVerticalIntegral (19 / 20) H f -
      actualPrincipalWResidueKernel K S mu P psi g Z s z =
      (comparisonVerticalIntegral (19 / 20) f - principalFiniteVerticalIntegral (19 / 20) H f) -
        (comparisonVerticalIntegral (1 + e) f - principalFiniteVerticalIntegral (1 + e) H f) := by
    rw [← hshift]
    ring
  rw [heq]
  exact (norm_sub_le _ _).trans ((add_le_add hleft hright).trans (by
    dsimp only [D]
    nlinarith [Real.rpow_nonneg (by linarith : 0 ≤ H) (-(N : ℝ))]))

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
variable [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (nu : Measure (FiniteAdeleRing (𝓞 K) K)) [nu.IsAddHaarMeasure]

include nu in
theorem actualPrincipal_z_truncated_shift
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {e : ℝ} (he : 0 < e) (he1 : e < 1 / 1000) (N : ℕ) :
    ∃ Z0 : ℝ, 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z → ∀ s : ℂ, 7 / 8 ≤ s.re →
      ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 1 ≤ H →
        ‖principalFiniteVerticalIntegral (1 / 6 + e) H (actualPrincipalWResidueKernel K S mu P psi g Z s) -
          principalFiniteVerticalIntegral (33 / 200) H (actualPrincipalWResidueKernel K S mu P psi g Z s) -
          actualPrincipalZRegularPart K S mu P psi g Z s (1 / 6) *
            (deletedZetaResidue K Sset / 6)‖ ≤ C * H ^ (-(N : ℝ)) := by
  letI : IsTotallyComplex K := ⟨hcomplex⟩
  obtain ⟨Za, hZa, ha⟩ := actualPrincipal_z_fullLine_shift K S mu nu hcomplex P psi hunram g he he1
  obtain ⟨Zb, hZb, hb⟩ := exists_actualPrincipal_z_strip_decay K S mu nu hcomplex P psi hunram
    g he he1 ((N : ℝ) + 2)
  refine ⟨max Za Zb, hZa.trans (le_max_left _ _), ?_⟩
  intro Z hZ s hs
  have hZA : Za ≤ Z := (le_max_left _ _).trans hZ
  have hZB : Zb ≤ Z := (le_max_right _ _).trans hZ
  have hZpos : 0 < Z := zero_lt_one.trans_le (hZa.trans hZA)
  obtain ⟨M, hM, hbound⟩ := hb Z hZB s hs
  let f : ℂ → ℂ := actualPrincipalWResidueKernel K S mu P psi g Z s
  let D : ℝ := ‖(2 * (Real.pi : ℂ))⁻¹‖ * M * principalTailEnvelopeMass
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (norm_nonneg _) hM.le) principalTailEnvelopeMass_nonneg
  have hcont (a : ℝ) (hlo : 33 / 200 ≤ a) (ha1 : a ≠ 1 / 6) :
      Continuous (fun t : ℝ => f ((a : ℂ) + (t : ℂ) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hne : (a : ℂ) + (t : ℂ) * Complex.I ≠ 1 / 6 := by
      intro h
      exact ha1 (by simpa using congrArg Complex.re h)
    have hline : ContinuousAt (fun r : ℝ => (a : ℂ) + (r : ℂ) * Complex.I) t := by
      fun_prop
    exact (differentiableAt_actualPrincipal_z_kernel K S mu nu P psi g Z hZpos s _
      (by simp; linarith) hne
      (principal_rectangle_mem_rowEulerRegion s 1 _ hs (by norm_num) (by simpa using hlo))).continuousAt.comp_of_eq
        hline rfl
  refine ⟨2 * D + 1, by linarith, ?_⟩
  intro H hH
  have hleft := principal_vertical_tail_bound f (33 / 200) M hM.le N
    (hcont _ le_rfl (by norm_num))
    (fun t ht => by
      simpa [f] using hbound ((33 / 200 : ℂ) + (t : ℂ) * Complex.I)
        (by norm_num) (by simp; linarith) (by simpa using ht)) H hH
  have hright := principal_vertical_tail_bound f (1 / 6 + e) M hM.le N
    (hcont _ (by linarith) (by linarith))
    (fun t ht => by
      simpa [f] using hbound ((1 / 6 + e : ℝ) + (t : ℂ) * Complex.I)
        (by simp; linarith) (by simp) (by simpa using ht)) H hH
  have hshift := ha Z hZA s hs
  have heq : principalFiniteVerticalIntegral (1 / 6 + e) H f -
      principalFiniteVerticalIntegral (33 / 200) H f -
      actualPrincipalZRegularPart K S mu P psi g Z s (1 / 6) *
        (deletedZetaResidue K Sset / 6) =
      (comparisonVerticalIntegral (33 / 200) f - principalFiniteVerticalIntegral (33 / 200) H f) -
        (comparisonVerticalIntegral (1 / 6 + e) f - principalFiniteVerticalIntegral (1 / 6 + e) H f) := by
    rw [← hshift]
    ring
  rw [heq]
  exact (norm_sub_le _ _).trans ((add_le_add hleft hright).trans (by
    dsimp only [D]
    nlinarith [Real.rpow_nonneg (by linarith : 0 ≤ H) (-(N : ℝ))]))

end Expansion.Project

#print axioms Expansion.Project.principal_rapid_integral_tail_bound
#print axioms Expansion.Project.actualPrincipal_w_truncated_shift
#print axioms Expansion.Project.actualPrincipal_z_truncated_shift
