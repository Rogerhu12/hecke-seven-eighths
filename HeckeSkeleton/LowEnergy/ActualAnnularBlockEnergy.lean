import HeckeSkeleton.LowEnergy.ActualBlockEnergy
import HeckeSkeleton.LowEnergy.ActualDyadicReflection
import HeckeSkeleton.LowEnergy.GaussianTheta
import HeckeSkeleton.LowEnergy.PhysicalBlockPolynomial
import HeckeSkeleton.LowEnergy.PhysicalDyadicBudget
import HeckeSkeleton.LowEnergy.PhysicalGaussianEnergy

/-!
# Physical Gaussian annular blocks with their actual frozen norm charges

This module specializes the two-sieve block estimate to the literal
Gaussian annulus and its physical scale.  All ideal norms, frozen local
charges and dyadic endpoints are retained in the resulting polynomial.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.ActualAnnularBlockEnergy

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckePort.CenteredMomentGenerator
open HeckeSkeleton.LowEnergy.ActualReflection
open HeckeSkeleton.LowEnergy.ActualSymbols HeckeSkeleton.LowEnergy.ActualSieveDictionary
open HeckeSkeleton.LowEnergy.ActualReflectionReindex
open HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open HeckeSkeleton.LowEnergy.ActualFrozenCharges
open HeckeSkeleton.LowEnergy.ActualBlockEnergy
open HeckeSkeleton.LowEnergy.ActualBlockReindex
open HeckeSkeleton.LowEnergy.ActualDyadicReflection
open HeckeSkeleton.LowEnergy.ClassSlices
open HeckeSkeleton.LowEnergy.LogGeometry HeckeSkeleton.LowEnergy.PhysicalBlockPolynomial
open scoped Classical BigOperators NumberField

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

theorem exteriorNorm_one_le (I : ExteriorIdeal K S) : 1 ≤ exteriorNorm K S I := by
  change (1 : ℝ) ≤ (I.val.val.absNorm : ℝ)
  have h : 1 ≤ I.val.val.absNorm := Ideal.absNorm_pos_of_nonZeroDivisors I.val
  exact_mod_cast h

def physicalThreshold (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
    (Z shift Klo Plo : ℝ) : ℝ :=
  threshold Z shift (exteriorNorm K S (primeSetIdeal K S f.inactive))
    (exteriorNorm K S (primeSetIdeal K S s.active))
    (exteriorNorm K S (minimumLinearIdeal K S s))
    (exteriorNorm K S (minimumCubeIdeal K S s)) Klo Plo

theorem normalizedScale_eq_physicalScale
    (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
    (Z shift Klo Plo Clo Blo : ℝ) :
    normalizedScale K S f s (Z * Real.exp shift) Klo Plo Clo Blo =
      physicalScale Z shift (exteriorNorm K S (primeSetIdeal K S f.inactive))
        (exteriorNorm K S (primeSetIdeal K S s.active))
        (exteriorNorm K S (minimumLinearIdeal K S s))
        (exteriorNorm K S (minimumCubeIdeal K S s)) Klo Plo Clo Blo := by
  unfold normalizedScale physicalBase physicalScale
  rw [minimum_norm_decomposition K S s]

/-- The literal local charge and one common Mellin profile give the
physical paper polynomial, with a constant before every block datum. -/
theorem actual_annular_physical_polynomial [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (delta : ℝ) (hdelta : 0 < delta) (hdelta' : delta ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
        (q : FourClasses (SixthLocalClasses K S)) (shift : ℤ)
        (Z Klo Plo Clo Blo : ℝ),
      1 < Z → 1 ≤ Klo → 1 ≤ Plo → 1 ≤ Clo → 1 ≤ Blo →
      ∀ rows ps cs bs : Finset (Ideal (𝓞 K)),
      (∀ k ∈ rows, IsExterior K S k ∧ Squarefree k ∧ (k.absNorm : ℝ) ≤ 2 * Klo) →
      (∀ P ∈ ps, IsExterior K S P ∧ Squarefree P ∧ (P.absNorm : ℝ) ≤ 2 * Plo) →
      (∀ c ∈ cs, IsExterior K S c ∧ Squarefree c ∧ (c.absNorm : ℝ) ≤ 2 * Clo) →
      (∀ b ∈ bs, IsExterior K S b ∧ (b.absNorm : ℝ) ≤ 2 * Blo) →
      (∀ k ∈ rows, 1 ≤ safeNorm k / Klo ∧ safeNorm k / Klo ≤ 2) →
      (∀ P ∈ ps, 1 ≤ safeNorm P / Plo ∧ safeNorm P / Plo ≤ 2) →
      (∀ c ∈ cs, 1 ≤ safeNorm c / Clo ∧ safeNorm c / Clo ≤ 2) →
      (∀ b ∈ bs, 1 ≤ safeNorm b / Blo ∧ safeNorm b / Blo ≤ 2) →
      ∀ (markWeight : Ideal (𝓞 K) → ℂ) (A : ℝ), 0 < A →
      (∀ P ∈ ps, ‖markWeight P‖ ≤ A) →
      (∑ k ∈ rows, ‖slicedPhysicalBlock K S D f s F θ q markWeight
        (GaussianTheta.annulusTest shift).toFun (Z * Real.exp (shift : ℝ)) ps cs bs k‖ ^ 2) ≤
        C * A ^ 2 * GaussianSeminorm.seminorm shift (ActualCommonMellinTail.order K 0) 2 ^ 2 *
        ‖inactiveWeight K S f‖ ^ 2 *
        (Z ^ scale Z Klo * Z ^ scale Z Clo * Z ^ scale Z Blo * Z ^ scale Z Plo) ^ delta *
        BlockPolynomial.weightedReflectedPolynomial Z 0 (scale Z Klo)
          (scale Z (exteriorNorm K S (minimumSmallIdeal K S s)))
          (scale Z (exteriorNorm K S (minimumCubeIdeal K S s)))
          (scale Z Plo) (scale Z Clo) (scale Z Blo)
          (physicalThreshold K S f s Z (shift : ℝ) Klo Plo) := by
  obtain ⟨Ce, hCe, he⟩ := actual_block_energy K S D F hF θ hKernel hθ hD
    hquadratic hcubic delta hdelta
  refine ⟨512 * Ce, by positivity, ?_⟩
  intro f s q shift Z Klo Plo Clo Blo hZ hK hP hC hB rows ps cs bs
    hrows hps hcs hbs hd hp hc hb markWeight A hA hw
  have hK0 : 0 < Klo := zero_lt_one.trans_le hK
  have hP0 : 0 < Plo := zero_lt_one.trans_le hP
  have hC0 : 0 < Clo := zero_lt_one.trans_le hC
  have hB0 : 0 < Blo := zero_lt_one.trans_le hB
  have hb0 := he f s q (GaussianTheta.annulusTest shift)
    (Z * Real.exp (shift : ℝ)) Klo Plo Clo Blo (2 * Klo) (2 * Plo) (2 * Clo) (2 * Blo)
    (mul_pos (zero_lt_one.trans hZ) (Real.exp_pos _)) hK0 hP0 hC0 hB0
    (by linarith) (by linarith) (by linarith) (by linarith)
    rows ps cs bs hrows hps hcs hbs hd hp hc hb markWeight A hA hw
  rw [GaussianTheta.testSeminorm_annulus,
    normalizedScale_eq_physicalScale K S f s] at hb0
  have hpoly := physical_polynomial_le (shift := (shift : ℝ)) hZ
    (exteriorNorm_pos K S (primeSetIdeal K S f.inactive))
    (exteriorNorm_pos K S (primeSetIdeal K S s.active))
    (exteriorNorm_pos K S (minimumLinearIdeal K S s))
    (exteriorNorm_pos K S (minimumCubeIdeal K S s))
    (exteriorNorm_pos K S (minimumSmallIdeal K S s))
    hK0 hP0 hC0 hB0 hdelta' (stateMajorant_sq_le_inverse_charge K S s)
  have hmul := mul_le_mul_of_nonneg_left hpoly
    (mul_nonneg (mul_nonneg (mul_nonneg hCe.le (sq_nonneg A))
      (sq_nonneg (GaussianSeminorm.seminorm shift (ActualCommonMellinTail.order K 0) 2)))
      (sq_nonneg ‖inactiveWeight K S f‖))
  apply hb0.trans
  convert hmul using 1 <;> simp only [sievePolynomial, physicalThreshold] <;> ring

#print axioms normalizedScale_eq_physicalScale
#print axioms actual_annular_physical_polynomial

/-- The true annular block already has the low exponent and the inverse
half-norm of the actual powerful part.  The displayed geometric premises
are only the original row cutoff and product-window inequalities. -/
theorem actual_annular_dyadic_block_energy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (delta : ℝ) (hdelta : 0 < delta) (hdelta' : delta ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
        (classes : FourClasses (SixthLocalClasses K S)) (shift : ℤ)
        (Z Klo Plo Clo Blo q d eta Ccut Cwin : ℝ),
      1 < Z → 1 ≤ Klo → 1 ≤ Plo → 1 ≤ Clo → 1 ≤ Blo →
      0 < q → 0 < Ccut → 0 < Cwin → 0 ≤ d → d ≤ (1 / 6 : ℝ) → 0 ≤ eta →
      IdealRows.Powerful f.frozen.val → f.puncture = primeSetIdeal K S ∅ →
      Z ^ d ≤ q →
      exteriorNorm K S f.frozen * Klo ≤ Ccut * Z ^ (5 / 6 : ℝ) / q ^ 2 →
      exteriorNorm K S (primeSetIdeal K S f.inactive) * Plo ≤
        Cwin * Z ^ ((1 / 6 : ℝ) - d) →
      scale Z Ccut ≤ eta → scale Z Cwin ≤ eta → |(shift : ℝ) / Real.log Z| ≤ eta →
      ∀ rows ps cs bs : Finset (Ideal (𝓞 K)),
      (∀ k ∈ rows, IsExterior K S k ∧ Squarefree k ∧ (k.absNorm : ℝ) ≤ 2 * Klo) →
      (∀ P ∈ ps, IsExterior K S P ∧ Squarefree P ∧ (P.absNorm : ℝ) ≤ 2 * Plo) →
      (∀ c ∈ cs, IsExterior K S c ∧ Squarefree c ∧ (c.absNorm : ℝ) ≤ 2 * Clo) →
      (∀ b ∈ bs, IsExterior K S b ∧ (b.absNorm : ℝ) ≤ 2 * Blo) →
      (∀ k ∈ rows, 1 ≤ safeNorm k / Klo ∧ safeNorm k / Klo ≤ 2) →
      (∀ P ∈ ps, 1 ≤ safeNorm P / Plo ∧ safeNorm P / Plo ≤ 2) →
      (∀ c ∈ cs, 1 ≤ safeNorm c / Clo ∧ safeNorm c / Clo ≤ 2) →
      (∀ b ∈ bs, 1 ≤ safeNorm b / Blo ∧ safeNorm b / Blo ≤ 2) →
      ∀ (markWeight : Ideal (𝓞 K) → ℂ) (A : ℝ), 0 < A →
      (∀ P ∈ ps, ‖markWeight P‖ ≤ A) →
      (∑ k ∈ rows, ‖slicedPhysicalBlock K S D f s F θ classes markWeight
        (GaussianTheta.annulusTest shift).toFun (Z * Real.exp (shift : ℝ)) ps cs bs k‖ ^ 2) ≤
        C * A ^ 2 * GaussianSeminorm.seminorm shift (ActualCommonMellinTail.order K 0) 2 ^ 2 *
        ‖inactiveWeight K S f‖ ^ 2 * exteriorNorm K S f.frozen ^ (-1 / 2 : ℝ) *
        Z ^ ((5 / 6 : ℝ) - 2 * d + 2 * delta + 21 * eta -
          2 * max (scale Z Clo + 3 * scale Z Blo -
            physicalThreshold K S f s Z (shift : ℝ) Klo Plo) 0) := by
  obtain ⟨Ce, hCe, he⟩ := actual_block_energy K S D F hF θ hKernel hθ hD
    hquadratic hcubic delta hdelta
  refine ⟨3072 * Ce, by positivity, ?_⟩
  intro f s classes shift Z Klo Plo Clo Blo q d eta Ccut Cwin hZ hK hP hC hB
    hq hCut hWin hd hd' heta hf hpunc hselected hrow hwindow hcuterr hwinerr hshift
    rows ps cs bs hrows hps hcs hbs hkr hpr hcr hbr markWeight A hA hw
  have hK0 : 0 < Klo := zero_lt_one.trans_le hK
  have hP0 : 0 < Plo := zero_lt_one.trans_le hP
  have hC0 : 0 < Clo := zero_lt_one.trans_le hC
  have hB0 : 0 < Blo := zero_lt_one.trans_le hB
  have hb0 := he f s classes (GaussianTheta.annulusTest shift)
    (Z * Real.exp (shift : ℝ)) Klo Plo Clo Blo (2 * Klo) (2 * Plo) (2 * Clo) (2 * Blo)
    (mul_pos (zero_lt_one.trans hZ) (Real.exp_pos _)) hK0 hP0 hC0 hB0
    (by linarith) (by linarith) (by linarith) (by linarith)
    rows ps cs bs hrows hps hcs hbs hkr hpr hcr hbr markWeight A hA hw
  rw [GaussianTheta.testSeminorm_annulus,
    normalizedScale_eq_physicalScale K S f s] at hb0
  have hpoly := physical_low_polynomial hZ
    (exteriorNorm_one_le K S (primeSetIdeal K S f.inactive))
    (exteriorNorm_one_le K S (primeSetIdeal K S s.active))
    (exteriorNorm_one_le K S (minimumLinearIdeal K S s))
    (exteriorNorm_one_le K S (minimumCubeIdeal K S s))
    (exteriorNorm_one_le K S (minimumSmallIdeal K S s)) hK hP hC hB
    (exteriorNorm_one_le K S f.frozen) hq hCut hWin hd hd' hdelta.le hdelta' heta
    (stateMajorant_sq_le_inverse_charge K S s)
    (state_active_norm_sq_le_of_powerful K S hf hpunc s)
    (minimum_linear_norm_le_active K S s) hselected hrow hwindow hcuterr hwinerr hshift
  have hmul := mul_le_mul_of_nonneg_left hpoly
    (mul_nonneg (mul_nonneg (mul_nonneg hCe.le (sq_nonneg A))
      (sq_nonneg (GaussianSeminorm.seminorm shift (ActualCommonMellinTail.order K 0) 2)))
      (sq_nonneg ‖inactiveWeight K S f‖))
  apply hb0.trans
  convert hmul using 1 <;> simp only [sievePolynomial, physicalThreshold] <;> ring

#print axioms actual_annular_dyadic_block_energy

theorem physicalThreshold_le
    (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
    {Z Klo Plo q d eta Ccut Cwin : ℝ} (shift : ℝ)
    (hZ : 1 < Z) (hK : 1 ≤ Klo) (hP : 1 ≤ Plo)
    (hq : 0 < q) (hCut : 0 < Ccut) (hWin : 0 < Cwin)
    (hd : 0 ≤ d) (heta : 0 ≤ eta)
    (hf : IdealRows.Powerful f.frozen.val) (hpunc : f.puncture = primeSetIdeal K S ∅)
    (hselected : Z ^ d ≤ q)
    (hrow : exteriorNorm K S f.frozen * Klo ≤ Ccut * Z ^ (5 / 6 : ℝ) / q ^ 2)
    (hwindow : exteriorNorm K S (primeSetIdeal K S f.inactive) * Plo ≤
      Cwin * Z ^ ((1 / 6 : ℝ) - d))
    (hcuterr : scale Z Ccut ≤ eta) (hwinerr : scale Z Cwin ≤ eta)
    (hshift : |shift / Real.log Z| ≤ eta) :
    physicalThreshold K S f s Z shift Klo Plo ≤ (5 / 6 : ℝ) + 8 * eta := by
  have hK0 := zero_lt_one.trans_le hK
  have hP0 := zero_lt_one.trans_le hP
  have hi := exteriorNorm_one_le K S (primeSetIdeal K S f.inactive)
  have hi0 := exteriorNorm_pos K S (primeSetIdeal K S f.inactive)
  have ha0 := exteriorNorm_pos K S (primeSetIdeal K S s.active)
  have hwidth : scale Z (exteriorNorm K S f.frozen) + scale Z Klo ≤
      (5 / 6 : ℝ) - 2 * d + eta := by
    have h := selected_row_width hZ (exteriorNorm_pos K S f.frozen) hK0 hq hCut hselected hrow
    linarith
  have hconductor : 2 * scale Z (exteriorNorm K S (primeSetIdeal K S s.active)) ≤
      scale Z (exteriorNorm K S f.frozen) + eta := by
    have h := scale_mono hZ (sq_pos_of_pos ha0)
      (state_active_norm_sq_le_of_powerful K S hf hpunc s)
    rw [scale_pow] at h
    norm_num at h
    linarith
  have hslot : scale Z Plo ≤
      scale Z (exteriorNorm K S (primeSetIdeal K S f.inactive) * Plo) + eta := by
    have hnorm : Plo ≤ exteriorNorm K S (primeSetIdeal K S f.inactive) * Plo := by nlinarith
    have h := scale_mono hZ hP0 hnorm
    linarith
  have hell : scale Z (exteriorNorm K S (primeSetIdeal K S f.inactive) * Plo) ≤
      (1 / 6 : ℝ) - d + eta := by
    have h := window_width hZ (mul_pos hi0 hP0) hWin hwindow
    linarith
  have h := PhysicalDyadicBudget.dual_threshold_upper
    (d := d) (O := scale Z (exteriorNorm K S f.frozen)) (H := scale Z Klo)
    (A := scale Z (exteriorNorm K S (primeSetIdeal K S s.active)))
    (N := scale Z (exteriorNorm K S (minimumLinearIdeal K S s)))
    (B := scale Z (exteriorNorm K S (minimumCubeIdeal K S s)))
    (z := scale Z Plo) (e := 0)
    (ell := scale Z (exteriorNorm K S (primeSetIdeal K S f.inactive) * Plo))
    (theta := shift / Real.log Z) (T := physicalThreshold K S f s Z shift Klo Plo)
    hd (scale_nonneg hZ (exteriorNorm_one_le K S f.frozen))
    (scale_nonneg hZ (exteriorNorm_one_le K S (minimumLinearIdeal K S s)))
    (scale_nonneg hZ (exteriorNorm_one_le K S (minimumCubeIdeal K S s)))
    (by linarith) hwidth hconductor hslot hell hshift rfl
  simpa only [sub_zero] using h

def squarefreeShellIdeals (j : ℕ) : Finset (Ideal (𝓞 K)) :=
  (squarefreeShell K S j).image (fun I => I.val.val)

def fullCubeShellIdeals (j : ℕ) : Finset (Ideal (𝓞 K)) :=
  (idealShell K S j).image (fun I => I.val.val)

theorem squarefreeShellIdeals_bounds (j : ℕ) :
    ∀ c ∈ squarefreeShellIdeals K S j,
      IsExterior K S c ∧ Squarefree c ∧ (c.absNorm : ℝ) ≤ 2 * (2 : ℝ) ^ j := by
  intro c hc
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hc
  have h := squarefreeShell_bounds K S hI
  exact ⟨exterior_isExterior K S I, h.1, h.2.2.le⟩

theorem fullCubeShellIdeals_bounds (j : ℕ) :
    ∀ b ∈ fullCubeShellIdeals K S j,
      IsExterior K S b ∧ (b.absNorm : ℝ) ≤ 2 * (2 : ℝ) ^ j := by
  intro b hb
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hb
  exact ⟨exterior_isExterior K S I, (idealShell_bounds K S hI).2.le⟩

theorem fullCubeShellIdeals_ratio (j : ℕ) :
    ∀ b ∈ fullCubeShellIdeals K S j,
      1 ≤ safeNorm b / (2 : ℝ) ^ j ∧ safeNorm b / (2 : ℝ) ^ j ≤ 2 := by
  intro b hb
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hb
  rw [safeNorm_exterior K S I]
  have h := idealShell_bounds K S hI
  constructor
  · exact (le_div_iff₀ (by positivity)).mpr (by simpa only [one_mul] using h.1)
  · exact (div_le_iff₀ (by positivity)).mpr h.2.le

theorem squarefreeShellIdeals_ratio (j : ℕ) :
    ∀ c ∈ squarefreeShellIdeals K S j,
      1 ≤ safeNorm c / (2 : ℝ) ^ j ∧ safeNorm c / (2 : ℝ) ^ j ≤ 2 := by
  intro c hc
  apply fullCubeShellIdeals_ratio K S j c
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hc
  exact Finset.mem_image.mpr ⟨I, (Finset.mem_filter.mp hI).1, rfl⟩

theorem scale_dyadic_combination (Z : ℝ) (j l : ℕ) :
    scale Z ((2 : ℝ) ^ j) + 3 * scale Z ((2 : ℝ) ^ l) =
      ((j : ℝ) + 3 * l) * Real.log 2 / Real.log Z := by
  rw [scale_pow, scale_pow]
  unfold scale
  ring

def annularDualRow (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (classes : FourClasses (SixthLocalClasses K S))
    (a : Ideal (𝓞 K) → ℂ) (Z : ℝ) (ps : Finset (Ideal (𝓞 K)))
    (i : GaussianEnergyAssembly.Index) (k : Ideal (𝓞 K)) : ℂ :=
  slicedPhysicalBlock K S D f s F θ classes a (GaussianTheta.annulusTest i.1).toFun
    (Z * Real.exp (i.1 : ℝ)) ps (squarefreeShellIdeals K S i.2.1)
      (fullCubeShellIdeals K S i.2.2) k

/-- Actual simultaneous summation of all Gaussian annuli and both dual
dyads.  Only the two original sieves are energy inputs. -/
theorem actual_all_annuli_dual_energy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (delta eps C0 : ℝ) (hdelta : 0 < delta) (hdelta' : delta ≤ 1)
    (heps : 0 < eps) (hC0 : 0 ≤ C0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
        (classes : FourClasses (SixthLocalClasses K S)) (Z Klo Plo q d Ccut Cwin : ℝ),
      1 < Z → 1 ≤ Klo → 1 ≤ Plo → 0 < q → 0 < Ccut → 0 < Cwin →
      0 ≤ d → d ≤ (1 / 6 : ℝ) →
      IdealRows.Powerful f.frozen.val → f.puncture = primeSetIdeal K S ∅ →
      Z ^ d ≤ q →
      exteriorNorm K S f.frozen * Klo ≤ Ccut * Z ^ (5 / 6 : ℝ) / q ^ 2 →
      exteriorNorm K S (primeSetIdeal K S f.inactive) * Plo ≤ Cwin * Z ^ ((1 / 6 : ℝ) - d) →
      Real.log Ccut ≤ C0 → Real.log Cwin ≤ C0 →
      ∀ rows ps : Finset (Ideal (𝓞 K)),
      (∀ k ∈ rows, IsExterior K S k ∧ Squarefree k ∧ (k.absNorm : ℝ) ≤ 2 * Klo) →
      (∀ P ∈ ps, IsExterior K S P ∧ Squarefree P ∧ (P.absNorm : ℝ) ≤ 2 * Plo) →
      (∀ k ∈ rows, 1 ≤ safeNorm k / Klo ∧ safeNorm k / Klo ≤ 2) →
      (∀ P ∈ ps, 1 ≤ safeNorm P / Plo ∧ safeNorm P / Plo ≤ 2) →
      ∀ (a : Ideal (𝓞 K) → ℂ) (A : ℝ), 0 < A → (∀ P ∈ ps, ‖a P‖ ≤ A) →
      (∀ k ∈ rows, Summable (fun i => annularDualRow K S D f s F θ classes a Z ps i k)) ∧
      (∑ k ∈ rows, ‖∑' i, annularDualRow K S D f s F θ classes a Z ps i k‖ ^ 2) ≤
        C * A ^ 2 * ‖inactiveWeight K S f‖ ^ 2 *
          exteriorNorm K S f.frozen ^ (-1 / 2 : ℝ) *
          Z ^ ((5 / 6 : ℝ) - 2 * d + 23 * delta + 2 * eps) := by
  obtain ⟨Cb, hCb, hblock⟩ := actual_annular_dyadic_block_energy K S D F hF θ hKernel hθ hD
    hquadratic hcubic delta hdelta hdelta'
  obtain ⟨Cg, hCg, hgauss⟩ := PhysicalGaussianEnergy.all_physical_blocks_energy
    (ActualCommonMellinTail.order K 0) 2 delta C0 eps hdelta.le hC0 heps
  refine ⟨Cg * Real.exp (21 * C0) * Cb, by positivity, ?_⟩
  intro f s classes Z Klo Plo q d Ccut Cwin hZ hK hP hq hCut hWin hd hd' hf hpunc
    hselected hrow hwindow hlogCut hlogWin rows ps hrows hps hkr hpr a A hA ha
  let T : ℤ → ℝ := fun k => physicalThreshold K S f s Z (k : ℝ) Klo Plo
  let eta : ℤ → ℝ := fun k => PhysicalDyadicBudget.annularError Z delta C0 (k : ℝ)
  have herr (k : ℤ) : 0 ≤ eta k ∧ |(k : ℝ) / Real.log Z| ≤ eta k ∧
      scale Z Ccut ≤ eta k ∧ scale Z Cwin ≤ eta k := by
    have ht := annular_tolerance hZ hdelta.le hC0 k
    refine ⟨ht.1, ht.2.1, ?_, ?_⟩
    · exact (div_le_div_of_nonneg_right hlogCut (Real.log_pos hZ).le).trans ht.2.2
    · exact (div_le_div_of_nonneg_right hlogWin (Real.log_pos hZ).le).trans ht.2.2
  have hT (k : ℤ) : T k ≤ (5 / 6 : ℝ) + 8 * PhysicalDyadicBudget.annularError Z delta C0 (k : ℝ) :=
    physicalThreshold_le K S f s (k : ℝ) hZ hK hP hq hCut hWin hd (herr k).1
      hf hpunc hselected hrow hwindow (herr k).2.2.1 (herr k).2.2.2 (herr k).2.1
  let Row := {k : Ideal (𝓞 K) // k ∈ rows}
  let G : GaussianEnergyAssembly.Index → Row → ℂ :=
    fun i k => annularDualRow K S D f s F θ classes a Z ps i k.val
  let R : ℝ := Cb * A ^ 2 * ‖inactiveWeight K S f‖ ^ 2 *
    exteriorNorm K S f.frozen ^ (-1 / 2 : ℝ)
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hCb.le (sq_nonneg A)) (sq_nonneg ‖inactiveWeight K S f‖))
      (Real.rpow_nonneg (exteriorNorm_pos K S f.frozen).le _)
  have hlocal (i : GaussianEnergyAssembly.Index) (rset : Finset Row) :
      (∑ r ∈ rset, ‖G i r‖ ^ 2) ≤
        GaussianSeminorm.seminorm i.1 (ActualCommonMellinTail.order K 0) 2 ^ 2 *
        Z ^ ((5 / 6 : ℝ) - 2 * d + 2 * delta +
          21 * PhysicalDyadicBudget.annularError Z delta C0 (i.1 : ℝ) -
          2 * PhysicalGaussianEnergy.excess Z (T i.1) i.2) * R := by
    let rs := rset.image (fun r => r.val)
    have hrs : ∀ r ∈ rs, r ∈ rows := by
      intro r hr
      obtain ⟨r', hr', rfl⟩ := Finset.mem_image.mp hr
      exact r'.property
    have hb := hblock f s classes i.1 Z Klo Plo ((2 : ℝ) ^ i.2.1) ((2 : ℝ) ^ i.2.2)
      q d (eta i.1) Ccut Cwin hZ hK hP (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
      hq hCut hWin hd hd' (herr i.1).1 hf hpunc hselected hrow hwindow
      (herr i.1).2.2.1 (herr i.1).2.2.2 (herr i.1).2.1 rs ps
      (squarefreeShellIdeals K S i.2.1) (fullCubeShellIdeals K S i.2.2)
      (fun r hr => hrows r (hrs r hr)) hps
      (squarefreeShellIdeals_bounds K S i.2.1) (fullCubeShellIdeals_bounds K S i.2.2)
      (fun r hr => hkr r (hrs r hr)) hpr
      (squarefreeShellIdeals_ratio K S i.2.1) (fullCubeShellIdeals_ratio K S i.2.2) a A hA ha
    rw [Finset.sum_image (fun a _ b _ h => Subtype.ext h)] at hb
    rw [scale_dyadic_combination] at hb
    convert hb using 1 <;>
      (try dsimp [G, annularDualRow, eta, R, T, PhysicalGaussianEnergy.excess]) <;> ring
  obtain ⟨hpoint, hsum, he⟩ := hgauss Z hZ T hT Row G ((5 / 6 : ℝ) - 2 * d) R hR hlocal
  refine ⟨fun k hk => hpoint ⟨k, hk⟩, ?_⟩
  have heq : (∑' r : Row, ‖∑' i, G i r‖ ^ 2) =
      ∑ k ∈ rows, ‖∑' i, annularDualRow K S D f s F θ classes a Z ps i k‖ ^ 2 := by
    simpa only [Row, G] using
      (Finset.tsum_subtype rows
        (fun k : Ideal (𝓞 K) => ‖∑' i, annularDualRow K S D f s F θ classes a Z ps i k‖ ^ 2))
  rw [heq] at he
  convert he using 1 <;> (try dsimp [R]) <;> ring

#print axioms physicalThreshold_le
#print axioms actual_all_annuli_dual_energy

end HeckeSkeleton.LowEnergy.ActualAnnularBlockEnergy
