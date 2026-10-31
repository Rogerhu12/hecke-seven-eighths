import Expansion.ActualPrincipalResidueAssembly
import Expansion.ActualPrincipalSweepDecay
import Expansion.PhysicalInitialRowTruncation
import Expansion.PowerHeightTailAlgebra
import Expansion.ActualRetainedComponents

/-!
# The actual principal initial integral and its retained components

The original full initial row on (5,5,3) is split by its true height-cube
complement, moved through six actual horizontal faces, and then passed
through the two proved principal residues.  The retained part consists of
the original w remainder, original z remainder and original slot error.
Every remaining term has a proved external power-height tail bound.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.Expansion.KernelRegularity
open Expansion.PhysicalInitialMellin Expansion.PhysicalInitialHeight
open Expansion.PhysicalRapidTruncation
open scoped Classical Topology

private theorem actual_quarterGaussian_rapid (N : ℕ) (H : ℝ) (hH : 1 ≤ H) :
    Real.exp (-(1 / 4 : ℝ) * H ^ 2) ≤
      ((2 : ℝ) ^ N * HighBinBoundary.gaussianMoment N) * H ^ (-(N : ℝ)) := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hg := HighBinBoundary.gaussian_weighted_bound N (H / 2)
  rw [show -(H / 2) ^ 2 = -(1 / 4 : ℝ) * H ^ 2 by ring] at hg
  have hp : H ^ N ≤ (2 : ℝ) ^ N * (1 + |H / 2|) ^ N := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ hH0
    rw [abs_of_nonneg (by positivity : 0 ≤ H / 2)]
    linarith
  have hm : H ^ N * Real.exp (-(1 / 4 : ℝ) * H ^ 2) ≤
      (2 : ℝ) ^ N * HighBinBoundary.gaussianMoment N := by
    apply (mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)).trans
    exact (mul_le_mul_of_nonneg_left hg (by positivity)).trans_eq (by ring)
  rw [Real.rpow_neg hH0, Real.rpow_natCast, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hHpos N)).mpr (by simpa only [mul_comm] using hm)

variable (K : Type) [Field K] [NumberField K]

theorem actualPrincipal_main_tail
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K S) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    {B e : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    PowerHeightTailBound (fun Z H => actualPrincipalMainTail K S P psi Z H (B + e)) := by
  obtain ⟨C, hC, hb⟩ := exists_actualPrincipal_main_tail_bound K S hcomplex
    P omega psi hpsi hB hB1 he he1 hboundary
  apply PowerHeightTailBound.of_uniform_decay (A := 0) (R := B + e - 11 / 16) le_rfl
  intro N
  refine ⟨C * (2 : ℝ) ^ N * HighBinBoundary.gaussianMoment N, 1,
    mul_pos (mul_pos hC (by positivity)) (HighBinBoundary.gaussianMoment_pos _), le_rfl, ?_⟩
  intro Z H hZ hH
  apply (hb Z H hZ (by linarith)).trans
  have hh := mul_le_mul_of_nonneg_left (actual_quarterGaussian_rapid N H hH)
    (show 0 ≤ C * Z ^ (B + e - 11 / 16) by positivity)
  simpa only [Real.rpow_zero, mul_one, mul_assoc, mul_left_comm, mul_comm] using hh

variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
local notation "muS" => (fun p : Sset => mu (Subtype.val p))

/-- Every term is a genuine complement, horizontal face, or finite
residue/main-line truncation error of the original principal contour. -/
def actualPrincipalTail (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z H B e : ℝ) : ℂ :=
  actualInitialRowTailIntegral K S mu P psi g ∅ Z H (physicalPrincipalRow K Sset) +
    actualPrincipalInitialHorizontal K S mu P psi g Z H B e +
    actualPrincipalWShiftError K S mu P psi g Z H B e +
    actualPrincipalZShiftError K S mu P psi g Z H B e +
    actualPrincipalMainTail K Sset P psi Z H (B + e)

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
variable [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (nu : Measure (FiniteAdeleRing (𝓞 K) K)) [nu.IsAddHaarMeasure]

include nu in
theorem actualPrincipal_initial_truncation_tail
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {B e : ℝ}
    (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    PowerHeightTailBound (fun Z H =>
      actualInitialRowTailIntegral K S mu P psi g ∅ Z H (physicalPrincipalRow K Sset)) := by
  letI : IsTotallyComplex K := ⟨hcomplex⟩
  obtain ⟨Z0, hZ0, hrapid⟩ := exists_actual_principal_sweep_kernel_rapid K S mu nu
    hcomplex P omega psi hpsi hAllowed hunram g hB hB1 he he1 hboundary
  apply PowerHeightTailBound.of_uniform_decay (A := 0) (R := 14) le_rfl
  intro N
  obtain ⟨C, hC, hc⟩ := hrapid (N + 2)
  let kappa : ℝ := ‖tripleMellinConstant‖
  have hkappa : 0 ≤ kappa := norm_nonneg _
  have hmass := heightMass_nonneg
  refine ⟨(kappa + 1) * C * (heightMass + 1), Z0, by positivity, hZ0, ?_⟩
  intro Z H hZ hH
  have hZ1 : 1 ≤ Z := hZ0.trans hZ
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ1
  have hf : Continuous (actualInitialProductKernel K S mu P psi g ∅ Z (physicalPrincipalRow K Sset)) :=
    continuous_actual_rowVerticalKernel_absolute K S mu nu P psi g ∅
      (physicalPrincipalRow K Sset) Z hZpos 5 5 3 (by norm_num) (by norm_num) (by norm_num)
  have hb (t : Heights) : heightWeight (N + 2) t *
      ‖actualInitialProductKernel K S mu P psi g ∅ Z (physicalPrincipalRow K Sset) t‖ ≤
        C * Z ^ (14 : ℝ) := by
    simpa [heightWeight, tripleHeightWeight, actualInitialProductKernel, rowVerticalKernel] using
      hc Z hZ ((5 : ℂ) + (t.1 : ℂ) * Complex.I)
        ((5 : ℂ) + (t.2.1 : ℂ) * Complex.I) ((3 : ℂ) + (t.2.2 : ℂ) * Complex.I)
        (by simp; linarith) (by simp) (by simp; linarith) (by simp)
        (by simp; linarith) (by simp)
  have ht := norm_tail_integral_le hf.aestronglyMeasurable N (C * Z ^ (14 : ℝ)) hb (by linarith : 0 ≤ H)
  have hheight : ((1 + H) ^ N)⁻¹ ≤ H ^ (-(N : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by linarith : 0 ≤ 1 + H)]
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith)
      (by linarith [show (0 : ℝ) ≤ (N : ℝ) by positivity])
  unfold actualInitialRowTailIntegral
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_left ht hkappa).trans
  have hcoef : kappa * heightMass ≤ (kappa + 1) * (heightMass + 1) := by nlinarith
  simp only [Real.rpow_zero, mul_one, div_eq_mul_inv]
  have hh := mul_le_mul_of_nonneg_left hheight
    (show 0 ≤ kappa * C * Z ^ (14 : ℝ) * heightMass by positivity)
  have hh' := mul_le_mul_of_nonneg_right hcoef
    (show 0 ≤ C * Z ^ (14 : ℝ) * H ^ (-(N : ℝ)) by positivity)
  dsimp only [kappa] at hh hh' ⊢
  nlinarith [hh, hh']

include nu in
/-- The actual principal tail has one external budget.  All polynomial
degrees and the height ceiling are fixed before tau and the tail order. -/
theorem actualPrincipal_tail_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {B e : ℝ}
    (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    PowerHeightTailBound (fun Z H => actualPrincipalTail K S mu P psi g Z H B e) := by
  have hi := actualPrincipal_initial_truncation_tail K S mu nu hcomplex P omega psi hpsi
    hAllowed hunram g hB hB1 he he1 hboundary
  have hh := actualPrincipal_initial_horizontal_tail K S mu nu hcomplex P omega psi hpsi
    hAllowed hunram g hB hB1 he he1 hboundary
  have hw := actualPrincipal_w_shift_error_tail K S mu nu hcomplex P omega psi hpsi
    hunram g hB hB1 he he1 hboundary
  have hz := actualPrincipal_z_shift_error_tail K S mu nu hcomplex P omega psi hpsi
    hunram g hB hB1 he he1 hboundary
  have hm := actualPrincipal_main_tail K Sset hcomplex P omega psi hpsi hB hB1 he he1 hboundary
  exact (((hi.add hh).add hw).add hz).add hm

include nu in
/-- The original full principal initial integral, with the three retained
remainders and the actual external tail separated by a proved identity. -/
theorem actualPrincipal_initial_integral_expansion [IsTotallyComplex K]
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (hN : physicalResidueNormalizer K Sset muS P ≠ 0)
    (g : PrimeWindowGeometry) {B e Z H : ℝ}
    (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (hZ : 0 < Z) (hH : 0 ≤ H)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    actualInitialRowIntegral K S mu P psi g ∅ Z (physicalPrincipalRow K Sset) -
      principalLineProbe K Sset P psi Z =
      actualPrincipalRetained K S mu P psi g Z H B e +
      actualPrincipalTail K S mu P psi g Z H B e := by
  have hi := actualInitialRowIntegral_eq_box_add_tail K S mu nu P hAllowed psi hcal hunram g ∅
    hZ H (physicalPrincipalRow K Sset)
  have ht := actualPrincipal_initial_box_transport K S mu nu P omega psi hpsi hAllowed g
    hB hB1 he he1 hZ hH hboundary
  have hr := actualPrincipal_two_finite_residues K S mu nu P omega psi hpsi hAllowed hN g
    hB he hZ H hboundary
  unfold actualPrincipalRetained actualPrincipalTail
  linear_combination hi + ht + hr

end Expansion.Project

#print axioms Expansion.Project.actualPrincipal_main_tail
#print axioms Expansion.Project.actualPrincipal_initial_truncation_tail
#print axioms Expansion.Project.actualPrincipal_tail_bound
#print axioms Expansion.Project.actualPrincipal_initial_integral_expansion
