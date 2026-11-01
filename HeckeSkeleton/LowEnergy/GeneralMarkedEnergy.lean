import HeckeSkeleton.LowEnergy.GeneralReflectedBlock
import HeckeSkeleton.LowEnergy.GeneralBlockPolynomial
import HeckeSkeleton.LowEnergy.IdealRankin

/-!
# General marked reflected energy on the genuine dual blocks

The completed scale is independent of the mark.  The original row,
active-mark and full-cube masks remain in `slicedBlock`.  The annular
profile is arbitrary and its finite seminorm is displayed.  A common
sieve exponent is chosen before every frozen datum and every ideal range.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.GeneralMarkedEnergy

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckePort.CenteredMomentGenerator
open HeckeSkeleton.LowEnergy.ActualReflection
open HeckeSkeleton.LowEnergy.ActualReflectionReindex
open HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open HeckeSkeleton.LowEnergy.ActualFrozenCharges
open HeckeSkeleton.LowEnergy.ActualSieveDictionary
open HeckeSkeleton.LowEnergy.ClassSlices
open HeckeSkeleton.LowEnergy.LogGeometry
open HeckeSkeleton.LowEnergy.Numerics
open HeckeSkeleton.LowEnergy.GeneralReflectedBlock
open HeckeSkeleton.LowEnergy.GeneralBlockPolynomial
open scoped Classical BigOperators NumberField nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

def dualThreshold (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
    (Z X Klo Plo : ℝ) : ℝ :=
  GeneralBlockPolynomial.threshold Z X
    (exteriorNorm K S (primeSetIdeal K S s.active))
    (exteriorNorm K S (minimumLinearIdeal K S s))
    (exteriorNorm K S (minimumCubeIdeal K S s)) Klo Plo

def fixedExponent (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
    (Z X Klo Plo Clo Blo : ℝ) : ℝ :=
  paperExponent 0 (scale Z Klo)
    (scale Z (exteriorNorm K S (minimumSmallIdeal K S s)))
    (scale Z (exteriorNorm K S (minimumCubeIdeal K S s)))
    (scale Z Plo) (scale Z Clo) (scale Z Blo)
    (dualThreshold K S f s Z X Klo Plo)

theorem normalizedScale_eq_kernelScale
    (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
    (X Klo Plo Clo Blo : ℝ) :
    GeneralReflectedBlock.normalizedScale K S f s X Klo Plo Clo Blo =
      kernelScale X (exteriorNorm K S (primeSetIdeal K S s.active))
        (exteriorNorm K S (minimumLinearIdeal K S s))
        (exteriorNorm K S (minimumCubeIdeal K S s)) Klo Plo Clo Blo := by
  unfold GeneralReflectedBlock.normalizedScale GeneralReflectedBlock.baseScale kernelScale
  rw [minimum_norm_decomposition K S s]

/-- General reflected block estimate with its exact four-scale loss.
Neither the puncture nor the row/label/background data is specialized. -/
theorem general_marked_block_energy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (delta : ℝ) (hdelta : 0 < delta) (hdelta' : delta ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
        (q : FourClasses (SixthLocalClasses K S)) (V : SmoothAnnularTest)
        (Z X Klo Plo Clo Blo : ℝ),
      1 < Z → 0 < X → 1 ≤ Klo → 1 ≤ Plo → 1 ≤ Clo → 1 ≤ Blo →
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
      (∑ k ∈ rows, ‖slicedBlock K S D f s F θ q markWeight V.toFun X ps cs bs k‖ ^ 2) ≤
        C * A ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
        ‖inactiveWeight K S f‖ ^ 2 *
        Z ^ (fixedExponent K S f s Z X Klo Plo Clo Blo -
          4 * max (scale Z Clo + 3 * scale Z Blo - dualThreshold K S f s Z X Klo Plo) 0 +
          delta * (scale Z Klo + scale Z Clo + scale Z Blo + scale Z Plo)) := by
  obtain ⟨Ce, hCe, he⟩ := general_block_energy K S D F hF θ hKernel hθ hD
    hquadratic hcubic delta hdelta
  refine ⟨3072 * Ce, by positivity, ?_⟩
  intro f s q V Z X Klo Plo Clo Blo hZ hX hK hP hC hB rows ps cs bs
    hrows hps hcs hbs hd hp hc hb markWeight A hA hw
  have hK0 := zero_lt_one.trans_le hK
  have hP0 := zero_lt_one.trans_le hP
  have hC0 := zero_lt_one.trans_le hC
  have hB0 := zero_lt_one.trans_le hB
  have hb0 := he f s q V X Klo Plo Clo Blo (2 * Klo) (2 * Plo) (2 * Clo) (2 * Blo)
    hX hK0 hP0 hC0 hB0 (by linarith) (by linarith) (by linarith) (by linarith)
    rows ps cs bs hrows hps hcs hbs hd hp hc hb markWeight A hA hw
  rw [normalizedScale_eq_kernelScale K S f s] at hb0
  have hpoly := general_exponent_le hZ hX
    (exteriorNorm_pos K S (primeSetIdeal K S s.active))
    (exteriorNorm_pos K S (minimumLinearIdeal K S s))
    (exteriorNorm_pos K S (minimumCubeIdeal K S s))
    (exteriorNorm_pos K S (minimumSmallIdeal K S s))
    hK0 hP0 hC0 hB0 hdelta' (stateMajorant_sq_le_inverse_charge K S s)
  have hmul := mul_le_mul_of_nonneg_left hpoly
    (mul_nonneg (mul_nonneg (mul_nonneg hCe.le (sq_nonneg A))
      (sq_nonneg (testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2)))
      (sq_nonneg ‖inactiveWeight K S f‖))
  apply hb0.trans
  convert hmul using 1 <;>
    simp only [PhysicalBlockPolynomial.sievePolynomial, fixedExponent,
      dualThreshold, fullPaperExponent] <;> ring

/-- Uniformity in every block of a bounded length family: one delta and
one constant work before the frozen data, profile and finite supports. -/
theorem general_marked_block_energy_eps [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (W eps : ℝ) (hW : 0 ≤ W) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
        (q : FourClasses (SixthLocalClasses K S)) (V : SmoothAnnularTest)
        (Z X Klo Plo Clo Blo : ℝ),
      1 < Z → 0 < X → 1 ≤ Klo → 1 ≤ Plo → 1 ≤ Clo → 1 ≤ Blo →
      scale Z Klo + scale Z Clo + scale Z Blo + scale Z Plo ≤ W →
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
      (∑ k ∈ rows, ‖slicedBlock K S D f s F θ q markWeight V.toFun X ps cs bs k‖ ^ 2) ≤
        C * A ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
        ‖inactiveWeight K S f‖ ^ 2 *
        Z ^ (fixedExponent K S f s Z X Klo Plo Clo Blo + eps) := by
  obtain ⟨delta, hd, hd', hbudget⟩ := exists_sieve_loss W eps hW heps
  obtain ⟨C, hC, hbound⟩ := general_marked_block_energy K S D F hF θ hKernel hθ hD
    hquadratic hcubic delta hd hd'
  refine ⟨C, hC, ?_⟩
  intro f s q V Z X Klo Plo Clo Blo hZ hX hK hP hClo hB hWsum
    rows ps cs bs hrows hps hcs hbs hd hp hc hb markWeight A hA hw
  have hlocal := hbound f s q V Z X Klo Plo Clo Blo hZ hX hK hP hClo hB
    rows ps cs bs hrows hps hcs hbs hd hp hc hb markWeight A hA hw
  apply hlocal.trans
  apply mul_le_mul_of_nonneg_left
  · apply Real.rpow_le_rpow_of_exponent_le hZ.le
    have hsmall := hbudget (scale Z Klo) (scale Z Clo) (scale Z Blo) (scale Z Plo) hWsum
    have htail := le_max_right
      (scale Z Clo + 3 * scale Z Blo - dualThreshold K S f s Z X Klo Plo) 0
    linarith
  · positivity

/-- A literal finite reflected block.  Its energy is computed from the
actual coefficient; no energy estimate is a field of this structure. -/
structure ReflectedBlock where
  fixed : FixedData K S
  state : FrozenState K S fixed.frozen fixed.puncture
  classes : FourClasses (SixthLocalClasses K S)
  X : ℝ
  rowScale : ℝ
  markScale : ℝ
  squarefreeScale : ℝ
  cubeScale : ℝ
  rows : Finset (Ideal (𝓞 K))
  marks : Finset (Ideal (𝓞 K))
  squarefreeColumns : Finset (Ideal (𝓞 K))
  cubeColumns : Finset (Ideal (𝓞 K))
  markWeight : Ideal (𝓞 K) → ℂ

namespace ReflectedBlock

variable {K S}

/-- All restrictions are explicit arithmetic supports or scalar bounds. -/
structure Admissible (b : ReflectedBlock K S) (Z W A : ℝ) : Prop where
  scale_pos : 0 < b.X
  rowScale_ge : 1 ≤ b.rowScale
  markScale_ge : 1 ≤ b.markScale
  squarefreeScale_ge : 1 ≤ b.squarefreeScale
  cubeScale_ge : 1 ≤ b.cubeScale
  width_bound : scale Z b.rowScale + scale Z b.squarefreeScale +
    scale Z b.cubeScale + scale Z b.markScale ≤ W
  rows_bound : ∀ k ∈ b.rows,
    IsExterior K S k ∧ Squarefree k ∧ (k.absNorm : ℝ) ≤ 2 * b.rowScale
  marks_bound : ∀ P ∈ b.marks,
    IsExterior K S P ∧ Squarefree P ∧ (P.absNorm : ℝ) ≤ 2 * b.markScale
  squarefree_bound : ∀ c ∈ b.squarefreeColumns,
    IsExterior K S c ∧ Squarefree c ∧ (c.absNorm : ℝ) ≤ 2 * b.squarefreeScale
  cube_bound : ∀ u ∈ b.cubeColumns,
    IsExterior K S u ∧ (u.absNorm : ℝ) ≤ 2 * b.cubeScale
  rows_ratio : ∀ k ∈ b.rows,
    1 ≤ safeNorm k / b.rowScale ∧ safeNorm k / b.rowScale ≤ 2
  marks_ratio : ∀ P ∈ b.marks,
    1 ≤ safeNorm P / b.markScale ∧ safeNorm P / b.markScale ≤ 2
  squarefree_ratio : ∀ c ∈ b.squarefreeColumns,
    1 ≤ safeNorm c / b.squarefreeScale ∧ safeNorm c / b.squarefreeScale ≤ 2
  cube_ratio : ∀ u ∈ b.cubeColumns,
    1 ≤ safeNorm u / b.cubeScale ∧ safeNorm u / b.cubeScale ≤ 2
  markWeight_bound : ∀ P ∈ b.marks, ‖b.markWeight P‖ ≤ A

def energy (b : ReflectedBlock K S) (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (V : SmoothAnnularTest) : ℝ :=
  ∑ k ∈ b.rows, ‖slicedBlock K S D b.fixed b.state F θ b.classes b.markWeight V.toFun b.X
    b.marks b.squarefreeColumns b.cubeColumns k‖ ^ 2

def exponent (b : ReflectedBlock K S) (Z : ℝ) : ℝ :=
  fixedExponent K S b.fixed b.state Z b.X b.rowScale b.markScale b.squarefreeScale b.cubeScale

end ReflectedBlock

/-- Bundle form for consumers of the general terminal, with the same
quantifier order as the unbundled actual-sum theorem. -/
theorem general_marked_block_family [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (W eps : ℝ) (hW : 0 ≤ W) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z A : ℝ), 1 < Z → 0 < A →
      ∀ (V : SmoothAnnularTest) (b : ReflectedBlock K S), b.Admissible Z W A →
      b.energy D F θ V ≤
        C * A ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
          ‖inactiveWeight K S b.fixed‖ ^ 2 * Z ^ (b.exponent Z + eps) := by
  obtain ⟨C, hC, hb⟩ := general_marked_block_energy_eps K S D F hF θ hKernel hθ hD
    hquadratic hcubic W eps hW heps
  refine ⟨C, hC, ?_⟩
  intro Z A hZ hA V b h
  exact hb b.fixed b.state b.classes V Z b.X b.rowScale b.markScale b.squarefreeScale
    b.cubeScale hZ h.scale_pos h.rowScale_ge h.markScale_ge h.squarefreeScale_ge h.cubeScale_ge
    h.width_bound b.rows b.marks b.squarefreeColumns b.cubeColumns h.rows_bound h.marks_bound
    h.squarefree_bound h.cube_bound h.rows_ratio h.marks_ratio h.squarefree_ratio h.cube_ratio
    b.markWeight A hA h.markWeight_bound

/-- The actual powerful count at a common bounded scale, with one epsilon
selected before the powerful dyad. -/
theorem powerful_count_at_scale (Omax eps : ℝ) (hOmax : 0 ≤ Omax) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z O : ℝ), 1 < Z → 0 ≤ O → O ≤ Omax →
      ∀ R : Finset (IdealRankin.PowerfulIdeal K),
      (∀ I ∈ R, IdealRankin.powerfulNorm K I ≤ Z ^ O) →
      (R.card : ℝ) ≤ C * Z ^ (O / 2 + eps) := by
  let delta := eps / (Omax + 1)
  have hd : 0 < delta := div_pos heps (by linarith)
  obtain ⟨C, hC, hb⟩ := IdealRankin.powerful_count_and_half_mass K delta hd
  refine ⟨C, hC, ?_⟩
  intro Z O hZ hO hO' R hR
  have hcount := (hb R (Z ^ O) (Real.one_le_rpow hZ.le hO) hR).1
  rw [← Real.rpow_mul (zero_lt_one.trans hZ).le] at hcount
  apply hcount.trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  have hdelta : delta * (Omax + 1) = eps := by
    dsimp [delta]
    exact div_mul_cancel₀ eps (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hO' hd.le
  nlinarith

/-- The powerful part adds O/2 once.  Each summand is the literal block
energy, and its bound is proved above.  Only scalar and exponent comparisons
for the actual blocks occur among the premises. -/
theorem general_marked_powerful_energy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (W Omax eps : ℝ) (hW : 0 ≤ W) (hOmax : 0 ≤ Omax) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z O A R0 E0 : ℝ),
      1 < Z → 0 ≤ O → O ≤ Omax → 0 < A → 0 ≤ R0 →
      ∀ (V : SmoothAnnularTest) (R : Finset (IdealRankin.PowerfulIdeal K))
        (blocks : IdealRankin.PowerfulIdeal K → ReflectedBlock K S),
      (∀ I ∈ R, IdealRankin.powerfulNorm K I ≤ Z ^ O) →
      (∀ I ∈ R, (blocks I).Admissible Z W A) →
      (∀ I ∈ R, ‖inactiveWeight K S (blocks I).fixed‖ ^ 2 ≤ R0) →
      (∀ I ∈ R, (blocks I).exponent Z ≤ E0) →
      (∑ I ∈ R, (blocks I).energy D F θ V) ≤
        C * A ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
          R0 * Z ^ (O / 2 + E0 + eps) := by
  obtain ⟨Cb, hCb, hb⟩ := general_marked_block_family K S D F hF θ hKernel hθ hD
    hquadratic hcubic W (eps / 2) hW (by linarith)
  obtain ⟨Cp, hCp, hp⟩ := powerful_count_at_scale K Omax (eps / 2) hOmax (by linarith)
  refine ⟨Cb * Cp, mul_pos hCb hCp, ?_⟩
  intro Z O A R0 E0 hZ hO hO' hA hR0 V R blocks hnorm hadm hweight hexp
  let L := Cb * A ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hlocal (I : IdealRankin.PowerfulIdeal K) (hI : I ∈ R) :
      (blocks I).energy D F θ V ≤ L * R0 * Z ^ (E0 + eps / 2) := by
    have h := hb Z A hZ hA V (blocks I) (hadm I hI)
    apply h.trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (hweight I hI) hL
    · exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [hexp I hI])
    · positivity
    · exact mul_nonneg hL hR0
  calc
    _ ≤ ∑ _I ∈ R, L * R0 * Z ^ (E0 + eps / 2) := Finset.sum_le_sum hlocal
    _ = (R.card : ℝ) * (L * R0 * Z ^ (E0 + eps / 2)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Cp * Z ^ (O / 2 + eps / 2)) * (L * R0 * Z ^ (E0 + eps / 2)) :=
      mul_le_mul_of_nonneg_right (hp Z O hZ hO hO' R hnorm) (by positivity)
    _ = _ := by
      have hpow : Z ^ (O / 2 + eps / 2) * Z ^ (E0 + eps / 2) =
          Z ^ (O / 2 + E0 + eps) := by
        rw [← Real.rpow_add (zero_lt_one.trans hZ)]
        congr 1
        ring
      dsimp [L]
      calc
        _ = (Cb * Cp) * A ^ 2 *
            testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 * R0 *
            (Z ^ (O / 2 + eps / 2) * Z ^ (E0 + eps / 2)) := by ring
        _ = _ := by rw [hpow]

/-- Explicit fixed polynomial height for the same genuine block. -/
theorem general_marked_block_energy_height [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ₀ : HeckeCharacter K)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (delta : ℝ) (hdelta : 0 < delta) (hdelta' : delta ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ν : HeckeCharacter K), FiniteOrder ν → ∀ (t : ℝ),
      MellinKernelInput K S F (ν * θ₀ * heckeNormTwist K t) →
      (∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K (ν * θ₀ * heckeNormTwist K t) p) →
      ∀ (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
        (q : FourClasses (SixthLocalClasses K S)) (V : SmoothAnnularTest)
        (Z X Klo Plo Clo Blo : ℝ),
      1 < Z → 0 < X → 1 ≤ Klo → 1 ≤ Plo → 1 ≤ Clo → 1 ≤ Blo →
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
      (∑ k ∈ rows, ‖slicedBlock K S D f s F (ν * θ₀ * heckeNormTwist K t) q markWeight V.toFun X ps cs bs k‖ ^ 2) ≤
        C * (1 + |t|) ^ (18 * HeckeSkeleton.ThetaKernel.ncx K) * A ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
        ‖inactiveWeight K S f‖ ^ 2 *
        Z ^ (fixedExponent K S f s Z X Klo Plo Clo Blo -
          4 * max (scale Z Clo + 3 * scale Z Blo - dualThreshold K S f s Z X Klo Plo) 0 +
          delta * (scale Z Klo + scale Z Clo + scale Z Blo + scale Z Plo)) := by
  obtain ⟨Ce, hCe, he⟩ := general_block_energy_height K S D F hF θ₀ hD
    hquadratic hcubic delta hdelta
  refine ⟨3072 * Ce, by positivity, ?_⟩
  intro ν hν t hKernel hθ f s q V Z X Klo Plo Clo Blo hZ hX hK hP hC hB rows ps cs bs
    hrows hps hcs hbs hd hp hc hb markWeight A hA hw
  have hK0 := zero_lt_one.trans_le hK
  have hP0 := zero_lt_one.trans_le hP
  have hC0 := zero_lt_one.trans_le hC
  have hB0 := zero_lt_one.trans_le hB
  have hb0 := he ν hν t hKernel hθ f s q V X Klo Plo Clo Blo (2 * Klo) (2 * Plo) (2 * Clo) (2 * Blo)
    hX hK0 hP0 hC0 hB0 (by linarith) (by linarith) (by linarith) (by linarith)
    rows ps cs bs hrows hps hcs hbs hd hp hc hb markWeight A hA hw
  rw [normalizedScale_eq_kernelScale K S f s] at hb0
  have hpoly := general_exponent_le hZ hX
    (exteriorNorm_pos K S (primeSetIdeal K S s.active))
    (exteriorNorm_pos K S (minimumLinearIdeal K S s))
    (exteriorNorm_pos K S (minimumCubeIdeal K S s))
    (exteriorNorm_pos K S (minimumSmallIdeal K S s))
    hK0 hP0 hC0 hB0 hdelta' (stateMajorant_sq_le_inverse_charge K S s)
  have hmul := mul_le_mul_of_nonneg_left hpoly
    (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg hCe.le (by positivity : 0 ≤ (1 + |t|) ^ (18 * HeckeSkeleton.ThetaKernel.ncx K))) (sq_nonneg A))
      (sq_nonneg (testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2)))
      (sq_nonneg ‖inactiveWeight K S f‖))
  apply hb0.trans
  convert hmul using 1 <;>
    simp only [PhysicalBlockPolynomial.sievePolynomial, fixedExponent,
      dualThreshold, fullPaperExponent] <;> ring

/-- Explicit fixed polynomial height for the same genuine block. -/
theorem general_marked_block_energy_eps_height [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ₀ : HeckeCharacter K)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (W eps : ℝ) (hW : 0 ≤ W) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ν : HeckeCharacter K), FiniteOrder ν → ∀ (t : ℝ),
      MellinKernelInput K S F (ν * θ₀ * heckeNormTwist K t) →
      (∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K (ν * θ₀ * heckeNormTwist K t) p) →
      ∀ (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
        (q : FourClasses (SixthLocalClasses K S)) (V : SmoothAnnularTest)
        (Z X Klo Plo Clo Blo : ℝ),
      1 < Z → 0 < X → 1 ≤ Klo → 1 ≤ Plo → 1 ≤ Clo → 1 ≤ Blo →
      scale Z Klo + scale Z Clo + scale Z Blo + scale Z Plo ≤ W →
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
      (∑ k ∈ rows, ‖slicedBlock K S D f s F (ν * θ₀ * heckeNormTwist K t) q markWeight V.toFun X ps cs bs k‖ ^ 2) ≤
        C * (1 + |t|) ^ (18 * HeckeSkeleton.ThetaKernel.ncx K) * A ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
        ‖inactiveWeight K S f‖ ^ 2 *
        Z ^ (fixedExponent K S f s Z X Klo Plo Clo Blo + eps) := by
  obtain ⟨delta, hd, hd', hbudget⟩ := exists_sieve_loss W eps hW heps
  obtain ⟨C, hC, hbound⟩ := general_marked_block_energy_height K S D F hF θ₀ hD
    hquadratic hcubic delta hd hd'
  refine ⟨C, hC, ?_⟩
  intro ν hν t hKernel hθ f s q V Z X Klo Plo Clo Blo hZ hX hK hP hClo hB hWsum
    rows ps cs bs hrows hps hcs hbs hd hp hc hb markWeight A hA hw
  have hlocal := hbound ν hν t hKernel hθ f s q V Z X Klo Plo Clo Blo hZ hX hK hP hClo hB
    rows ps cs bs hrows hps hcs hbs hd hp hc hb markWeight A hA hw
  apply hlocal.trans
  apply mul_le_mul_of_nonneg_left
  · apply Real.rpow_le_rpow_of_exponent_le hZ.le
    have hsmall := hbudget (scale Z Klo) (scale Z Clo) (scale Z Blo) (scale Z Plo) hWsum
    have htail := le_max_right
      (scale Z Clo + 3 * scale Z Blo - dualThreshold K S f s Z X Klo Plo) 0
    linarith
  · positivity

/-- Uniform finite-order/norm-twist version of the actual data-bundle endpoint. -/
theorem general_marked_block_family_height [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ₀ : HeckeCharacter K)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (W eps : ℝ) (hW : 0 ≤ W) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ν : HeckeCharacter K), FiniteOrder ν → ∀ (t : ℝ),
      MellinKernelInput K S F (ν * θ₀ * heckeNormTwist K t) →
      (∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K (ν * θ₀ * heckeNormTwist K t) p) →
      ∀ (Z A : ℝ), 1 < Z → 0 < A →
      ∀ (V : SmoothAnnularTest) (b : ReflectedBlock K S), b.Admissible Z W A →
      b.energy D F (ν * θ₀ * heckeNormTwist K t) V ≤
        C * (1 + |t|) ^ (18 * HeckeSkeleton.ThetaKernel.ncx K) * A ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
          ‖inactiveWeight K S b.fixed‖ ^ 2 * Z ^ (b.exponent Z + eps) := by
  obtain ⟨C, hC, hb⟩ := general_marked_block_energy_eps_height K S D F hF θ₀ hD
    hquadratic hcubic W eps hW heps
  refine ⟨C, hC, ?_⟩
  intro ν hν t hKernel hθ Z A hZ hA V b h
  exact hb ν hν t hKernel hθ b.fixed b.state b.classes V Z b.X b.rowScale b.markScale b.squarefreeScale
    b.cubeScale hZ h.scale_pos h.rowScale_ge h.markScale_ge h.squarefreeScale_ge h.cubeScale_ge
    h.width_bound b.rows b.marks b.squarefreeColumns b.cubeColumns h.rows_bound h.marks_bound
    h.squarefree_bound h.cube_bound h.rows_ratio h.marks_ratio h.squarefree_ratio h.cube_ratio
    b.markWeight A hA h.markWeight_bound


#print axioms general_marked_block_family
#print axioms general_marked_block_family_height
#print axioms powerful_count_at_scale
#print axioms general_marked_powerful_energy

#print axioms normalizedScale_eq_kernelScale
#print axioms general_marked_block_energy
#print axioms general_marked_block_energy_eps

end HeckeSkeleton.LowEnergy.GeneralMarkedEnergy
