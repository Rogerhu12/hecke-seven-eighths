import Expansion.ActualDeletedZetaResidue
import Expansion.ActualPrincipalResidueKernels
import Expansion.ActualRowKernelHolomorphy

/-!
# Actual simple poles of the principal row

The principal w-pole and the subsequent z-pole are exposed in the exact
original kernel.  Their regular factors are differentiable by actual
Mellin holomorphy and the original Euler correction theorem.  The pole
limits use the specific deleted zeta residue and its factor-six Jacobian.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory Set Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler
open HeckeSkeleton.Expansion.MellinRegularity
open scoped Classical Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
local notation "muS" => (fun p : Sset => mu p.val)

/-- The exposed w-zeta factor is the only possible w-pole on the original
Euler region; this proves regularity of its actual remaining factor. -/
theorem differentiableAt_actualPrincipal_w_regular
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z : ℝ) (hZ : 0 < Z) (s z w0 : ℂ)
    (hregion : (s, w0, z) ∈ rowEulerRegion) :
    DifferentiableAt ℂ (fun w => actualPrincipalKernelCore K S mu P psi g Z s w z 1) w0 := by
  have hden := HighBinBoundary.ActualDenominator.differentiable_mellin
    P.denominator.toSmoothAnnularTest w0
  have hY : ((Z ^ (23 / 48 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hZ _).ne'
  have hpow : DifferentiableAt ℂ
      (fun w : ℂ => ((Z ^ (23 / 48 : ℝ) : ℝ) : ℂ) ^ (w - 1)) w0 :=
    (differentiableAt_id.sub_const 1).const_cpow (Or.inl hY)
  have hcorr := differentiableAt_actual_fullCorrection_comp K S P psi g ∅
    (physicalPrincipalRow K Sset) Z (fun _ : ℂ => s) id (fun _ : ℂ => z) w0
    (differentiableAt_const _) differentiableAt_id (differentiableAt_const _) hregion
  unfold actualPrincipalKernelCore
  exact ((((((hden.const_mul _).mul_const _).mul_const _).fun_mul hpow).mul_const _).fun_mul
    hcorr).div_const _

theorem differentiableAt_actualPrincipal_w_kernel
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z : ℝ) (hZ : 0 < Z) (s z w0 : ℂ)
    (hw0 : w0 ≠ 1) (hregion : (s, w0, z) ∈ rowEulerRegion) :
    DifferentiableAt ℂ (fun w => actualPrincipalKernelCore K S mu P psi g Z s w z
      (heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) w)) w0 := by
  have heq : (fun w => actualPrincipalKernelCore K S mu P psi g Z s w z
      (heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) w)) =
      fun w => actualPrincipalKernelCore K S mu P psi g Z s w z 1 *
        heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) w := by
    funext w
    exact actualPrincipalKernelCore_linear K S mu P psi g Z s w z _
  rw [heq]
  exact (differentiableAt_actualPrincipal_w_regular K S mu P psi g Z hZ s z w0 hregion).fun_mul
    (actual_deletedZeta_analyticAt K Sset w0 hw0).differentiableAt

/-- The residue at w=1 is exactly the original w-residue kernel. -/
theorem actualPrincipal_w_residue
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z : ℝ) (hZ : 0 < Z) (s z : ℂ)
    (hregion : (s, (1 : ℂ), z) ∈ rowEulerRegion) :
    Tendsto (fun w : ℂ => (w - 1) * actualPrincipalKernelCore K S mu P psi g Z s w z
      (heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) w))
      (𝓝[≠] (1 : ℂ)) (𝓝 (actualPrincipalWResidueKernel K S mu P psi g Z s z)) := by
  have hreg := differentiableAt_actualPrincipal_w_regular K S mu P psi g Z hZ s z 1 hregion
  have hlim := (hreg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
    (actual_deletedZeta_residue_one K Sset)
  have hvalue : actualPrincipalKernelCore K S mu P psi g Z s 1 z 1 *
      deletedZetaResidue K Sset = actualPrincipalWResidueKernel K S mu P psi g Z s z :=
    (actualPrincipalKernelCore_linear K S mu P psi g Z s 1 z _).symm
  rw [hvalue] at hlim
  apply hlim.congr'
  filter_upwards [] with w
  rw [actualPrincipalKernelCore_linear K S mu P psi g Z s w z
    (heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) w)]
  ring

/-- The same pole limit holds for the literal compensated principal row. -/
theorem actualPrincipal_literal_w_residue
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (g : PrimeWindowGeometry) (Z : ℝ) (hZ : 0 < Z) (s z : ℂ)
    (hregion : (s, (1 : ℂ), z) ∈ rowEulerRegion) :
    Tendsto (fun w : ℂ => (w - 1) * compensatedRowMellinKernel K Sset muS P psi
      (arithmeticHighEulerData K Sset P psi) g ∅ (physicalPrincipalRow K Sset) Z s w z)
      (𝓝[≠] (1 : ℂ)) (𝓝 (actualPrincipalWResidueKernel K S mu P psi g Z s z)) := by
  simp_rw [actualPrincipalKernel_eq_core K S mu P psi hAllowed g Z hZ]
  exact actualPrincipal_w_residue K S mu P psi g Z hZ s z hregion

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
variable [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (nu : Measure (FiniteAdeleRing (𝓞 K) K)) [nu.IsAddHaarMeasure]

include nu

theorem differentiableAt_actualPrincipal_z_regular [IsTotallyComplex K]
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z : ℝ) (hZ : 0 < Z) (s z0 : ℂ)
    (hz0 : 0 < z0.re) (hregion : (s, (1 : ℂ), z0) ∈ rowEulerRegion) :
    DifferentiableAt ℂ (actualPrincipalZRegularPart K S mu P psi g Z s) z0 := by
  have hM := (analyticOnNhd_actual_additiveMellin K S mu nu P.additive z0 hz0).differentiableAt
  have hX : ((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hZ _).ne'
  have hZc : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hxPower : DifferentiableAt ℂ
      (fun z : ℂ => ((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ^ (1 / 2 - z)) z0 :=
    ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl hX)
  have hzPower : DifferentiableAt ℂ (fun z : ℂ => (Z : ℂ) ^ (s + z - 1)) z0 :=
    (((differentiableAt_const _).add differentiableAt_id).sub_const 1).const_cpow (Or.inl hZc)
  have hexp : DifferentiableAt ℂ (fun z : ℂ => Complex.exp ((s + z - 1) ^ 2)) z0 := by
    fun_prop
  have hcorr := differentiableAt_actual_fullCorrection_comp K S P psi g ∅
    (physicalPrincipalRow K Sset) Z (fun _ : ℂ => s) (fun _ : ℂ => 1) id z0
    (differentiableAt_const _) (differentiableAt_const _) differentiableAt_id hregion
  unfold actualPrincipalZRegularPart
  exact ((((((((differentiableAt_const _).fun_mul hexp).fun_mul hM).mul_const _).fun_mul hxPower).fun_mul
    hzPower).mul_const _).fun_mul hcorr).div_const _

theorem differentiableAt_actualPrincipal_z_kernel [IsTotallyComplex K]
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z : ℝ) (hZ : 0 < Z) (s z0 : ℂ)
    (hz0 : 0 < z0.re) (hpole : z0 ≠ 1 / 6)
    (hregion : (s, (1 : ℂ), z0) ∈ rowEulerRegion) :
    DifferentiableAt ℂ (actualPrincipalWResidueKernel K S mu P psi g Z s) z0 := by
  have heq : actualPrincipalWResidueKernel K S mu P psi g Z s =
      fun z => actualPrincipalZRegularPart K S mu P psi g Z s z *
        heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) (6 * z) :=
    funext (actualPrincipalWResidueKernel_factorization K S mu P psi g Z s)
  rw [heq]
  apply (differentiableAt_actualPrincipal_z_regular K S mu nu P psi g Z hZ s z0 hz0 hregion).fun_mul
  apply (actual_deletedZeta_analyticAt K Sset (6 * z0) _).differentiableAt.comp z0
    ((differentiableAt_const _).fun_mul differentiableAt_id)
  intro h
  apply hpole
  linear_combination h / 6

/-- The second residue is the actual factor-six deleted zeta residue
times the literal regular part, ready for exact physical normalization. -/
theorem actualPrincipal_z_residue [IsTotallyComplex K]
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z : ℝ) (hZ : 0 < Z) (s : ℂ)
    (hregion : (s, (1 : ℂ), (1 / 6 : ℂ)) ∈ rowEulerRegion) :
    Tendsto (fun z : ℂ => (z - 1 / 6) * actualPrincipalWResidueKernel K S mu P psi g Z s z)
      (𝓝[≠] (1 / 6 : ℂ))
      (𝓝 (actualPrincipalZRegularPart K S mu P psi g Z s (1 / 6) *
        (deletedZetaResidue K Sset / 6))) := by
  have hreg := differentiableAt_actualPrincipal_z_regular K S mu nu P psi g Z hZ s
    (1 / 6) (by norm_num) hregion
  have hlim := (hreg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
    (actual_deletedZeta_residue_one_sixth K Sset)
  apply hlim.congr'
  filter_upwards [] with z
  rw [actualPrincipalWResidueKernel_factorization K S mu P psi g Z s z]
  ring

end Expansion.Project

#print axioms Expansion.Project.actualPrincipal_literal_w_residue
#print axioms Expansion.Project.differentiableAt_actualPrincipal_z_regular
#print axioms Expansion.Project.actualPrincipal_z_residue
