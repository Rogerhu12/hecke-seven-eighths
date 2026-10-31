import HeckeSkeleton.LowEnergy.GeneralReflectedBlock
import HeckeSkeleton.LowEnergy.GeneralMarkedEnergy
import HeckeSkeleton.LowEnergy.GeneralTailNumerics
import HeckeSkeleton.LowEnergy.IdealMajorant
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Arbitrary tails of the actual general reflected coefficients

The large-argument order comes from the original `MellinKernelInput`.
One fixed Dirichlet majorant, with exponents 3/2 and 4, controls the
unrestricted squarefree/cube columns.  Its polynomial prefactor is
independent of the requested tail order.  Every coefficient, common-prime
mask and finite class restriction remains in the summand until its norm
is estimated.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.GeneralKernelTail

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckePort.CenteredMomentGenerator
open HeckeSkeleton.LowEnergy.ActualReflection
open HeckeSkeleton.LowEnergy.ActualSymbols
open HeckeSkeleton.LowEnergy.ActualFrozenMajorant
open HeckeSkeleton.LowEnergy.ActualReflectionReindex
open HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open HeckeSkeleton.LowEnergy.ActualGeneratorClasses
open HeckeSkeleton.LowEnergy.ClassSlices
open HeckeSkeleton.LowEnergy.GeneralReflectedBlock
open HeckeSkeleton.LowEnergy.ActualFrozenCharges
open HeckeSkeleton.LowEnergy.GeneralMarkedEnergy
open HeckeSkeleton.LowEnergy.GeneralTailNumerics
open HeckeSkeleton.LowEnergy.LogGeometry
open scoped Classical BigOperators NumberField nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

theorem seminorm_nonneg (V : ℝ → ℂ) (J : ℕ) (A : ℝ) :
    0 ≤ testSeminorm V J A := by
  unfold testSeminorm
  exact (le_max_left 0 (testIntegral V 0 A)).trans
    (Finset.le_sup' (fun j => max 0 (testIntegral V j A))
      (by simp : 0 ∈ Finset.range (J + 1)))

/-- Fixed majorant for the two actual exterior ideal variables. -/
def columnWeight (cb : ExteriorIdeal K S × ExteriorIdeal K S) : ℝ :=
  exteriorNorm K S cb.1 ^ (-(3 / 2 : ℝ)) * exteriorNorm K S cb.2 ^ (-4 : ℝ)

theorem columnWeight_nonneg (cb : ExteriorIdeal K S × ExteriorIdeal K S) :
    0 ≤ columnWeight K S cb := by
  unfold columnWeight
  positivity

theorem columnWeight_summable : Summable (columnWeight K S) := by
  have hc : Summable (fun c : ExteriorIdeal K S =>
      exteriorNorm K S c ^ (-(3 / 2 : ℝ))) :=
    (summable_nonzeroIdeal_norm_rpow K (by norm_num : (1 : ℝ) < 3 / 2)).subtype _
  have hb : Summable (fun b : ExteriorIdeal K S =>
      exteriorNorm K S b ^ (-4 : ℝ)) :=
    (summable_nonzeroIdeal_norm_rpow K (by norm_num : (1 : ℝ) < 4)).subtype _
  exact hc.mul_of_nonneg hb
    (fun c => Real.rpow_nonneg (exteriorNorm_pos K S c).le _)
    (fun b => Real.rpow_nonneg (exteriorNorm_pos K S b).le _)

def columnMass : ℝ := ∑' cb, columnWeight K S cb

theorem columnMass_nonneg : 0 ≤ columnMass K S :=
  tsum_nonneg (columnWeight_nonneg K S)

/-- One extra power, independent of the tail order, pays for both columns. -/
theorem column_kernel_identity {Y d P c b : ℝ}
    (hY : 0 < Y) (hd : 0 < d) (hP : 0 < P) (hc : 0 < c) (hb : 0 < b) :
    (Real.sqrt c * b)⁻¹ * (CommonMellin.argument Y d P c b) ^ (-1 : ℝ) =
      d ^ 2 * P ^ 2 / Y * (c ^ (-(3 / 2 : ℝ)) * b ^ (-4 : ℝ)) := by
  have hce : c ^ (-(3 / 2 : ℝ)) = (Real.sqrt c * c)⁻¹ := by
    rw [show -(3 / 2 : ℝ) = -((1 / 2 : ℝ) + 1) by ring,
      Real.rpow_neg hc.le, Real.rpow_add hc, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hbe : b ^ (-4 : ℝ) = (b ^ 4)⁻¹ := by
    rw [Real.rpow_neg hb.le]
    norm_num
  rw [hce, hbe, Real.rpow_neg_one]
  unfold CommonMellin.argument
  have hs := (Real.sqrt_pos.2 hc).ne'
  field_simp [hY.ne', hd.ne', hP.ne', hc.ne', hb.ne', hs]
  <;> ring

theorem power_tail {y T A : ℝ} (hy : 0 < y) (hT : 0 < T)
    (hTy : T ≤ y) (hA : 1 ≤ A) :
    y ^ (-A) ≤ y ^ (-1 : ℝ) * T ^ (-(A - 1)) := by
  have h := Real.rpow_le_rpow_of_nonpos hT hTy (by linarith : -(A - 1) ≤ 0)
  calc
    y ^ (-A) = y ^ (-1 : ℝ) * y ^ (-(A - 1)) := by
      rw [← Real.rpow_add hy]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hy.le _)

/-- The whole common ratio box loses at most sixteen, from its two
denominator coordinates.  The column coordinates only increase it. -/
theorem argument_lower_on_ratio_box {Y d P c b : ℝ} (hY : 0 < Y)
    (hd0 : 1 ≤ d) (hd1 : d ≤ 2) (hP0 : 1 ≤ P) (hP1 : P ≤ 2)
    (hc : 1 ≤ c) (hb : 1 ≤ b) :
    Y / 16 ≤ CommonMellin.argument Y d P c b := by
  have hd : 0 < d := zero_lt_one.trans_le hd0
  have hP : 0 < P := zero_lt_one.trans_le hP0
  have hden : 0 < d ^ 2 * P ^ 2 := mul_pos (sq_pos_of_pos hd) (sq_pos_of_pos hP)
  have hd2 : d ^ 2 ≤ 4 := by nlinarith
  have hp2 : P ^ 2 ≤ 4 := by nlinarith
  have hden16 : d ^ 2 * P ^ 2 ≤ 16 := by
    have h := mul_le_mul hd2 hp2 (sq_nonneg P) (by norm_num : (0 : ℝ) ≤ 4)
    norm_num at h
    exact h
  have hb3 : 1 ≤ b ^ 3 := one_le_pow₀ hb
  have hnum : Y ≤ Y * c * b ^ 3 := by
    calc
      Y ≤ Y * c := by nlinarith
      _ ≤ Y * c * b ^ 3 := by
        exact le_mul_of_one_le_right (by positivity) hb3
  unfold CommonMellin.argument
  apply (le_div_iff₀ hden).mpr
  calc
    Y / 16 * (d ^ 2 * P ^ 2) ≤ Y / 16 * 16 :=
      mul_le_mul_of_nonneg_left hden16 (by positivity)
    _ = Y := by ring
    _ ≤ _ := hnum

/-- An actual dual block beyond Td+tau lies in the genuine kernel tail.
The norm ratios and the original P² denominator are retained exactly. -/
theorem argument_ge_tau_threshold (f : FixedData K S)
    (s : FrozenState K S f.frozen f.puncture)
    (Z X Klo Plo Clo Blo tau : ℝ) (hZ : 1 < Z) (hX : 0 < X)
    (hK : 0 < Klo) (hP : 0 < Plo) (hC : 0 < Clo) (hB : 0 < Blo)
    (hlarge : 16 ≤ Z ^ (tau / 2))
    (htail : dualThreshold K S f s Z X Klo Plo + tau ≤
      scale Z Clo + 3 * scale Z Blo)
    (k P c b : ExteriorIdeal K S)
    (hk0 : 1 ≤ exteriorNorm K S k / Klo) (hk1 : exteriorNorm K S k / Klo ≤ 2)
    (hp0 : 1 ≤ exteriorNorm K S P / Plo) (hp1 : exteriorNorm K S P / Plo ≤ 2)
    (hc : 1 ≤ exteriorNorm K S c / Clo) (hb : 1 ≤ exteriorNorm K S b / Blo) :
    Z ^ (tau / 2) ≤ CommonMellin.argument (baseScale K S f s X)
      (exteriorNorm K S k) (exteriorNorm K S P) (exteriorNorm K S c) (exteriorNorm K S b) := by
  let Y := GeneralReflectedBlock.normalizedScale K S f s X Klo Plo Clo Blo
  have hY : 0 < Y := GeneralReflectedBlock.normalizedScale_pos K S f s hX hK hP hC hB
  have hYe : Y = Z ^ (scale Z Clo + 3 * scale Z Blo - dualThreshold K S f s Z X Klo Plo) := by
    dsimp [Y]
    rw [normalizedScale_eq_kernelScale K S f s]
    exact GeneralBlockPolynomial.kernelScale_eq_rpow hZ hX
      (exteriorNorm_pos K S (primeSetIdeal K S s.active))
      (exteriorNorm_pos K S (minimumLinearIdeal K S s))
      (exteriorNorm_pos K S (minimumCubeIdeal K S s)) hK hP hC hB
  have hYtau : Z ^ tau ≤ Y := by
    rw [hYe]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hpow : Z ^ tau = Z ^ (tau / 2) * Z ^ (tau / 2) := by
    rw [← Real.rpow_add (zero_lt_one.trans hZ)]
    congr 1
    ring
  have hT : Z ^ (tau / 2) ≤ Y / 16 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
    calc
      Z ^ (tau / 2) * 16 ≤ Z ^ (tau / 2) * Z ^ (tau / 2) :=
        mul_le_mul_of_nonneg_left hlarge (by positivity)
      _ = Z ^ tau := hpow.symm
      _ ≤ Y := hYtau
  have harg := argument_lower_on_ratio_box hY hk0 hk1 hp0 hp1 hc hb
  have hnorm := GeneralReflectedBlock.argument_normalized K S f s X Klo Plo Clo Blo
    k.val.val P.val.val c.val.val b.val.val hK hP hC hB
  simp only [safeNorm_exterior] at hnorm
  rw [hnorm]
  exact hT.trans harg

/-- A single constant is selected before the profile, sector, class,
argument and tail threshold.  The seminorm order alone grows with A. -/
theorem kernel_tail_bound (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hKernel : MellinKernelInput K S F θ) (A : ℝ) (hA : 1 ≤ A) :
    ∃ (J : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (V : SmoothAnnularTest) u κ (y T : ℝ),
      0 < y → 0 < T → T ≤ y →
      ‖mellinReflectionKernel K S F θ u κ V.toFun 0 y‖ ≤
        C * testSeminorm V.toFun J A * y ^ (-1 : ℝ) * T ^ (-(A - 1)) := by
  let J := Nat.ceil (4 * (Fintype.card {v : InfinitePlace K // v.IsComplex} : ℝ) * A + 1) + 1
  have hJ : 4 * (Fintype.card {v : InfinitePlace K // v.IsComplex} : ℝ) * A +
      (0 : ℕ) + 1 < (J : ℝ) := by
    have h := Nat.le_ceil
      (4 * (Fintype.card {v : InfinitePlace K // v.IsComplex} : ℝ) * A + 1)
    dsimp [J]
    push_cast
    linarith
  obtain ⟨C, hC, hbound⟩ := hKernel.derivative_bound A 0 J (by linarith) hJ
  refine ⟨J, C, hC, ?_⟩
  intro V u κ y T hy hT hTy
  have hk := hbound V u κ y hy
  simp only [eulerDerivativeOrder, Function.iterate_zero, id_eq] at hk
  have hCS := mul_nonneg hC (seminorm_nonneg V.toFun J A)
  calc
    _ ≤ C * testSeminorm V.toFun J A * y ^ (-A) :=
      hk.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hCS)
    _ ≤ C * testSeminorm V.toFun J A *
        (y ^ (-1 : ℝ) * T ^ (-(A - 1))) :=
      mul_le_mul_of_nonneg_left (power_tail hy hT hTy hA) hCS
    _ = _ := by ring

theorem hybridKernel_norm_le_one (hD : AllowedGeneratorInput K S D)
    (k : Ideal (𝓞 K)) (P : ExteriorIdeal K S) (c b : Ideal (𝓞 K)) :
    ‖FiniteHybridIntegral.hybridKernel (cubicKernel K S D) (quadraticKernel K S D)
      k P.val.val c b‖ ≤ 1 := by
  have hP : (1 : ℝ) ≤ P.val.val.absNorm := by
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors P.val
  have hinv : ‖(Real.sqrt (P.val.val.absNorm : ℝ) : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr hP)
  unfold FiniteHybridIntegral.hybridKernel
  apply mul_norm_le_one
  · apply mul_norm_le_one
    · apply mul_norm_le_one
      · exact mul_norm_le_one _ _ hinv (KeepOriginalRow.mask_norm_le _ _)
      · exact (quadraticKernel_axioms K S D hD (fun _ => True)).norm_le_one _ _
    · exact (cubicKernel_axioms K S D hD).norm_le_one _ _
  · exact KeepOriginalRow.mask_norm_le _ _

variable (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)

/-- The literal unrestricted squarefree/cube contribution of one row and
one mark in the general reflected block. -/
def columnAtom (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (q : FourClasses (SixthLocalClasses K S)) (V : ℝ → ℂ) (X : ℝ)
    (k P : ExteriorIdeal K S) (cb : ExteriorIdeal K S × ExteriorIdeal K S) : ℂ :=
  ordinaryColumn K S D f s θ q cb.1.val.val cb.2.val.val *
    FiniteHybridIntegral.hybridKernel (cubicKernel K S D) (quadraticKernel K S D)
      k.val.val P.val.val cb.1.val.val cb.2.val.val *
    mellinReflectionKernel K S F θ (QuotientGroup.mk f.rowUnit)
      (blockFrequency (frozenClass K S D f s) q.1.1 q.1.2 q.2.1 q.2.2) V 0
      (CommonMellin.argument (baseScale K S f s X)
        (exteriorNorm K S k) (exteriorNorm K S P)
        (exteriorNorm K S cb.1) (exteriorNorm K S cb.2))

def tailColumnAtom (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (q : FourClasses (SixthLocalClasses K S)) (V : ℝ → ℂ) (X T : ℝ)
    (k P : ExteriorIdeal K S) (cb : ExteriorIdeal K S × ExteriorIdeal K S) : ℂ :=
  if T ≤ CommonMellin.argument (baseScale K S f s X)
      (exteriorNorm K S k) (exteriorNorm K S P)
      (exteriorNorm K S cb.1) (exteriorNorm K S cb.2)
  then columnAtom K S D f s F θ q V X k P cb else 0

/-- Uniform tail of the actual coefficient series, before Fourier
absolutization.  The prefactor d² P² / baseScale is independent of A. -/
theorem actual_column_tail (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D) (A : ℝ) (hA : 1 ≤ A) :
    ∃ (J : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (V : SmoothAnnularTest) (q : FourClasses (SixthLocalClasses K S))
        (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
        (X T : ℝ) (k P : ExteriorIdeal K S),
      0 < X → 0 < T →
      Summable (fun cb => ‖tailColumnAtom K S D f s F θ q V.toFun X T k P cb‖) ∧
      (∑' cb, ‖tailColumnAtom K S D f s F θ q V.toFun X T k P cb‖) ≤
        C * testSeminorm V.toFun J A * stateMajorant K S s *
          (exteriorNorm K S k ^ 2 * exteriorNorm K S P ^ 2 / baseScale K S f s X) *
          T ^ (-(A - 1)) := by
  obtain ⟨J, C, hC, hb⟩ := kernel_tail_bound K S F θ hKernel A hA
  refine ⟨J, C * columnMass K S, mul_nonneg hC (columnMass_nonneg K S), ?_⟩
  intro V q f s X T k P hX hT
  have hbase : 0 < baseScale K S f s X := by
    unfold baseScale
    exact div_pos (mul_pos hX (exteriorNorm_pos K S s.minimum))
      (sq_pos_of_pos (exteriorNorm_pos K S (primeSetIdeal K S s.active)))
  let L := C * testSeminorm V.toFun J A * stateMajorant K S s *
    (exteriorNorm K S k ^ 2 * exteriorNorm K S P ^ 2 / baseScale K S f s X) *
    T ^ (-(A - 1))
  have hL : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hC (seminorm_nonneg V.toFun J A))
        (stateMajorant_nonneg K S s)) (by positivity)) (by positivity)
  have hpoint (cb : ExteriorIdeal K S × ExteriorIdeal K S) :
      ‖tailColumnAtom K S D f s F θ q V.toFun X T k P cb‖ ≤ L * columnWeight K S cb := by
    unfold tailColumnAtom
    split_ifs with htail
    · have hc := exteriorNorm_pos K S cb.1
      have hbb := exteriorNorm_pos K S cb.2
      have hk := exteriorNorm_pos K S k
      have hp := exteriorNorm_pos K S P
      have harg := CommonMellin.argument_pos hbase hk hp hc hbb
      have hker := hb V (QuotientGroup.mk f.rowUnit)
        (blockFrequency (frozenClass K S D f s) q.1.1 q.1.2 q.2.1 q.2.2)
        _ T harg hT htail
      have hcol := ordinaryColumn_norm_le K S D f s θ hθ q cb.1.val.val cb.2.val.val
        ⟨nonZeroDivisors.coe_ne_zero cb.1.val, cb.1.property⟩
        ⟨nonZeroDivisors.coe_ne_zero cb.2.val, cb.2.property⟩
      have hhyb := hybridKernel_norm_le_one K S D hD k.val.val P cb.1.val.val cb.2.val.val
      have hcoef : ‖ordinaryColumn K S D f s θ q cb.1.val.val cb.2.val.val *
          FiniteHybridIntegral.hybridKernel (cubicKernel K S D) (quadraticKernel K S D)
            k.val.val P.val.val cb.1.val.val cb.2.val.val‖ ≤
          stateMajorant K S s / (Real.sqrt (exteriorNorm K S cb.1) * exteriorNorm K S cb.2) := by
        rw [norm_mul]
        simpa only [mul_one] using mul_le_mul hcol hhyb (norm_nonneg _)
          (div_nonneg (stateMajorant_nonneg K S s) (by positivity))
      have h := mul_le_mul hcoef hker (norm_nonneg _)
        (div_nonneg (stateMajorant_nonneg K S s) (by positivity))
      rw [columnAtom, norm_mul]
      apply h.trans_eq
      have hid := column_kernel_identity hbase hk hp hc hbb
      dsimp [L, columnWeight]
      calc
        _ = (C * testSeminorm V.toFun J A * stateMajorant K S s * T ^ (-(A - 1))) *
            ((Real.sqrt (exteriorNorm K S cb.1) * exteriorNorm K S cb.2)⁻¹ *
              (CommonMellin.argument (baseScale K S f s X)
                (exteriorNorm K S k) (exteriorNorm K S P)
                (exteriorNorm K S cb.1) (exteriorNorm K S cb.2)) ^ (-1 : ℝ)) := by ring
        _ = _ := by rw [hid]; ring
    · rw [norm_zero]
      exact mul_nonneg hL (columnWeight_nonneg K S cb)
  have hm : Summable (fun cb => L * columnWeight K S cb) :=
    (columnWeight_summable K S).mul_left L
  have ht := hm.of_nonneg_of_le (fun cb => norm_nonneg _) hpoint
  refine ⟨ht, (ht.tsum_le_tsum hpoint hm).trans_eq ?_⟩
  rw [tsum_mul_left]
  dsimp [L, columnMass]
  ring

/-- The kernel order and scale threshold are chosen here.  Consumers
specify a fixed polynomial budget B and the requested decay L, and do
not supply a kernel order or a tail estimate. -/
theorem actual_power_tail (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D) (B tau L : ℝ)
    (hB : 0 ≤ B) (htau : 0 < tau) (hL : 0 < L) :
    ∃ (J : ℕ) (C Z0 : ℝ), 0 ≤ C ∧ 1 < Z0 ∧
      ∀ Z : ℝ, Z0 ≤ Z → 16 ≤ Z ^ (tau / 2) ∧
      ∀ (V : SmoothAnnularTest) (q : FourClasses (SixthLocalClasses K S))
        (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
        (X : ℝ) (k P : ExteriorIdeal K S), 0 < X →
      stateMajorant K S s *
        (exteriorNorm K S k ^ 2 * exteriorNorm K S P ^ 2 / baseScale K S f s X) ≤ Z ^ B →
      Summable (fun cb => ‖tailColumnAtom K S D f s F θ q V.toFun X
        (Z ^ (tau / 2)) k P cb‖) ∧
      (∑' cb, ‖tailColumnAtom K S D f s F θ q V.toFun X (Z ^ (tau / 2)) k P cb‖) ≤
        C * testSeminorm V.toFun J (tailOrder B tau L) * Z ^ (-L) := by
  obtain ⟨J, C, hC, hb⟩ := actual_column_tail K S D F θ hKernel hθ hD
    (tailOrder B tau L) (tailOrder_ge_one hB htau hL.le)
  obtain ⟨Z1, hZ1, hz1⟩ := exists_ratio_threshold tau htau
  refine ⟨J, C, max 2 Z1, hC, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro Z hZ0
  have hZ : 1 < Z := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hZ0)
  refine ⟨hz1 Z ((le_max_right _ _).trans hZ0), ?_⟩
  intro V q f s X k P hX hpref
  obtain ⟨hsum, htail⟩ := hb V q f s X (Z ^ (tau / 2)) k P hX (by positivity)
  refine ⟨hsum, htail.trans ?_⟩
  have hCS := mul_nonneg hC (seminorm_nonneg V.toFun J (tailOrder B tau L))
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpref hCS)
    (Real.rpow_nonneg (by positivity : 0 ≤ Z ^ (tau / 2)) (-(tailOrder B tau L - 1)))
  calc
    _ = (C * testSeminorm V.toFun J (tailOrder B tau L) *
        (stateMajorant K S s *
          (exteriorNorm K S k ^ 2 * exteriorNorm K S P ^ 2 / baseScale K S f s X))) *
        (Z ^ (tau / 2)) ^ (-(tailOrder B tau L - 1)) := by ring
    _ ≤ (C * testSeminorm V.toFun J (tailOrder B tau L) * Z ^ B) *
        (Z ^ (tau / 2)) ^ (-(tailOrder B tau L - 1)) := h
    _ = _ := by
      rw [mul_assoc, polynomial_tail_eq htau (zero_lt_one.trans hZ)]

theorem columnAtom_eq_tail_beyond_threshold
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (q : FourClasses (SixthLocalClasses K S)) (V : ℝ → ℂ)
    (Z X Klo Plo Clo Blo tau : ℝ) (hZ : 1 < Z) (hX : 0 < X)
    (hK : 0 < Klo) (hP : 0 < Plo) (hC : 0 < Clo) (hB : 0 < Blo)
    (hlarge : 16 ≤ Z ^ (tau / 2))
    (htail : dualThreshold K S f s Z X Klo Plo + tau ≤
      scale Z Clo + 3 * scale Z Blo)
    (k P c b : ExteriorIdeal K S)
    (hk0 : 1 ≤ exteriorNorm K S k / Klo) (hk1 : exteriorNorm K S k / Klo ≤ 2)
    (hp0 : 1 ≤ exteriorNorm K S P / Plo) (hp1 : exteriorNorm K S P / Plo ≤ 2)
    (hc : 1 ≤ exteriorNorm K S c / Clo) (hb : 1 ≤ exteriorNorm K S b / Blo) :
    columnAtom K S D f s F θ q V X k P (c, b) =
      tailColumnAtom K S D f s F θ q V X (Z ^ (tau / 2)) k P (c, b) := by
  symm
  exact if_pos (argument_ge_tau_threshold K S f s Z X Klo Plo Clo Blo tau
    hZ hX hK hP hC hB hlarge htail k P c b hk0 hk1 hp0 hp1 hc hb)

theorem exteriorNorm_one_le (I : ExteriorIdeal K S) : 1 ≤ exteriorNorm K S I := by
  exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I.val

theorem stateMajorant_le_one {frozen puncture : ExteriorIdeal K S}
    (s : FrozenState K S frozen puncture) : stateMajorant K S s ≤ 1 := by
  have hS := exteriorNorm_one_le K S (minimumSmallIdeal K S s)
  have hB := exteriorNorm_one_le K S (minimumCubeIdeal K S s)
  have hSB : 1 ≤ exteriorNorm K S (minimumSmallIdeal K S s) *
      exteriorNorm K S (minimumCubeIdeal K S s) := by
    simpa only [one_mul] using mul_le_mul hS hB (by norm_num : (0 : ℝ) ≤ 1)
      (zero_le_one.trans hS)
  have h := (stateMajorant_sq_le_inverse_charge K S s).trans
    (inv_le_one_of_one_le₀ hSB)
  nlinarith [stateMajorant_nonneg K S s]

/-- The polynomial cost is derived from ordinary norm-length bounds.
Its exponent contains no kernel order. -/
theorem prefactor_le_from_lengths (f : FixedData K S)
    (s : FrozenState K S f.frozen f.puncture)
    (k P : ExteriorIdeal K S) {Z X Hmax Pmax Amax Nmax : ℝ}
    (hZ : 0 < Z) (hX : 0 < X)
    (hk : exteriorNorm K S k ≤ Z ^ Hmax)
    (hP : exteriorNorm K S P ≤ Z ^ Pmax)
    (hactive : exteriorNorm K S (primeSetIdeal K S s.active) ≤ Z ^ Amax)
    (hscale : Z ^ (-Nmax) ≤ X) :
    stateMajorant K S s *
      (exteriorNorm K S k ^ 2 * exteriorNorm K S P ^ 2 / baseScale K S f s X) ≤
      Z ^ (2 * Hmax + 2 * Pmax + 2 * Amax + Nmax) := by
  have hk0 := exteriorNorm_pos K S k
  have hp0 := exteriorNorm_pos K S P
  have ha0 := exteriorNorm_pos K S (primeSetIdeal K S s.active)
  have hm0 := exteriorNorm_pos K S s.minimum
  have hm1 := exteriorNorm_one_le K S s.minimum
  have hbase : 0 < baseScale K S f s X := by unfold baseScale; positivity
  have hnum : exteriorNorm K S k ^ 2 * exteriorNorm K S P ^ 2 *
      exteriorNorm K S (primeSetIdeal K S s.active) ^ 2 ≤
      (Z ^ Hmax) ^ 2 * (Z ^ Pmax) ^ 2 * (Z ^ Amax) ^ 2 := by
    exact mul_le_mul
      (mul_le_mul (pow_le_pow_left₀ hk0.le hk 2) (pow_le_pow_left₀ hp0.le hP 2)
        (sq_nonneg _) (sq_nonneg _))
      (pow_le_pow_left₀ ha0.le hactive 2) (sq_nonneg _) (by positivity)
  have hpow : ((Z ^ Hmax) ^ 2 * (Z ^ Pmax) ^ 2 * (Z ^ Amax) ^ 2) / Z ^ (-Nmax) =
      Z ^ (2 * Hmax + 2 * Pmax + 2 * Amax + Nmax) := by
    rw [← Real.rpow_mul_natCast hZ.le, ← Real.rpow_mul_natCast hZ.le,
      ← Real.rpow_mul_natCast hZ.le, ← Real.rpow_add hZ, ← Real.rpow_add hZ,
      ← Real.rpow_sub hZ]
    congr 1
    ring
  calc
    _ ≤ exteriorNorm K S k ^ 2 * exteriorNorm K S P ^ 2 / baseScale K S f s X :=
      mul_le_of_le_one_left (by positivity) (stateMajorant_le_one K S s)
    _ = (exteriorNorm K S k ^ 2 * exteriorNorm K S P ^ 2 *
        exteriorNorm K S (primeSetIdeal K S s.active) ^ 2) /
        (X * exteriorNorm K S s.minimum) := by
      unfold baseScale
      field_simp [hX.ne', hm0.ne', ha0.ne']
    _ ≤ (exteriorNorm K S k ^ 2 * exteriorNorm K S P ^ 2 *
        exteriorNorm K S (primeSetIdeal K S s.active) ^ 2) / X :=
      div_le_div_of_nonneg_left (by positivity) hX (le_mul_of_one_le_right hX.le hm1)
    _ ≤ ((Z ^ Hmax) ^ 2 * (Z ^ Pmax) ^ 2 * (Z ^ Amax) ^ 2) / Z ^ (-Nmax) :=
      div_le_div₀ (by positivity) hnum (Real.rpow_pos_of_pos hZ _) hscale
    _ = _ := hpow

/-- One finite outer piece of the genuine coefficient series.  The
weight contains only its static row, mark and inactive coefficients. -/
structure TailPiece where
  fixed : FixedData K S
  state : FrozenState K S fixed.frozen fixed.puncture
  classes : FourClasses (SixthLocalClasses K S)
  X : ℝ
  row : ExteriorIdeal K S
  mark : ExteriorIdeal K S
  weight : ℂ

namespace TailPiece

variable {K S}

def prefactor (p : TailPiece K S) : ℝ :=
  ‖p.weight‖ * stateMajorant K S p.state *
    (exteriorNorm K S p.row ^ 2 * exteriorNorm K S p.mark ^ 2 /
      baseScale K S p.fixed p.state p.X)

def tailMass (p : TailPiece K S) (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (V : SmoothAnnularTest) (T : ℝ) : ℝ :=
  ∑' cb, ‖p.weight * tailColumnAtom K S D p.fixed p.state F θ p.classes V.toFun p.X
    T p.row p.mark cb‖

end TailPiece

/-- A bounded number of outer rows and tuples costs a fixed polynomial.
Every premise concerns actual finite cardinalities, coefficient norms or
ideal norms; none concerns a reflected series or an energy. -/
theorem total_prefactor_le_from_lengths {ι : Type*} (I : Finset ι)
    (p : ι → TailPiece K S) {Z Cmax Wmax Hmax Pmax Amax Nmax : ℝ}
    (hZ : 0 < Z) (hcard : (I.card : ℝ) ≤ Z ^ Cmax)
    (hX : ∀ i ∈ I, 0 < (p i).X)
    (hw : ∀ i ∈ I, ‖(p i).weight‖ ≤ Z ^ Wmax)
    (hk : ∀ i ∈ I, exteriorNorm K S (p i).row ≤ Z ^ Hmax)
    (hP : ∀ i ∈ I, exteriorNorm K S (p i).mark ≤ Z ^ Pmax)
    (ha : ∀ i ∈ I,
      exteriorNorm K S (primeSetIdeal K S (p i).state.active) ≤ Z ^ Amax)
    (hs : ∀ i ∈ I, Z ^ (-Nmax) ≤ (p i).X) :
    (∑ i ∈ I, (p i).prefactor) ≤
      Z ^ (Cmax + Wmax + 2 * Hmax + 2 * Pmax + 2 * Amax + Nmax) := by
  have hlocal (i : ι) (hi : i ∈ I) : (p i).prefactor ≤
      Z ^ (Wmax + 2 * Hmax + 2 * Pmax + 2 * Amax + Nmax) := by
    have he := prefactor_le_from_lengths K S (p i).fixed (p i).state (p i).row (p i).mark
      hZ (hX i hi) (hk i hi) (hP i hi) (ha i hi) (hs i hi)
    have hbase : 0 < baseScale K S (p i).fixed (p i).state (p i).X := by
      have hm := exteriorNorm_pos K S (p i).state.minimum
      have hf := exteriorNorm_pos K S (primeSetIdeal K S (p i).state.active)
      have hx := hX i hi
      unfold baseScale
      positivity
    have h := mul_le_mul (hw i hi) he
      (mul_nonneg (stateMajorant_nonneg K S (p i).state) (by positivity)) (by positivity)
    unfold TailPiece.prefactor
    calc
      _ = ‖(p i).weight‖ * (stateMajorant K S (p i).state *
          (exteriorNorm K S (p i).row ^ 2 * exteriorNorm K S (p i).mark ^ 2 /
            baseScale K S (p i).fixed (p i).state (p i).X)) := by ring
      _ ≤ Z ^ Wmax * Z ^ (2 * Hmax + 2 * Pmax + 2 * Amax + Nmax) := h
      _ = _ := by rw [← Real.rpow_add hZ]; congr 1 <;> ring
  calc
    _ ≤ ∑ _i ∈ I, Z ^ (Wmax + 2 * Hmax + 2 * Pmax + 2 * Amax + Nmax) :=
      Finset.sum_le_sum hlocal
    _ = (I.card : ℝ) * Z ^ (Wmax + 2 * Hmax + 2 * Pmax + 2 * Amax + Nmax) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Z ^ Cmax * Z ^ (Wmax + 2 * Hmax + 2 * Pmax + 2 * Amax + Nmax) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by rw [← Real.rpow_add hZ]; congr 1 <;> ring

/-- Arbitrary power saving for the total finite outer family of genuine
reflected tails.  A is chosen from its already fixed polynomial budget. -/
theorem actual_total_power_tail (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D) (B tau L : ℝ)
    (hB : 0 ≤ B) (htau : 0 < tau) (hL : 0 < L) :
    ∃ (J : ℕ) (C Z0 : ℝ), 0 ≤ C ∧ 1 < Z0 ∧
      ∀ Z : ℝ, Z0 ≤ Z → 16 ≤ Z ^ (tau / 2) ∧
      ∀ (V : SmoothAnnularTest) {ι : Type*} (I : Finset ι) (p : ι → TailPiece K S),
      (∀ i ∈ I, 0 < (p i).X) → (∑ i ∈ I, (p i).prefactor) ≤ Z ^ B →
      (∀ i ∈ I, Summable (fun cb => ‖(p i).weight *
        tailColumnAtom K S D (p i).fixed (p i).state F θ (p i).classes V.toFun (p i).X
          (Z ^ (tau / 2)) (p i).row (p i).mark cb‖)) ∧
      (∑ i ∈ I, (p i).tailMass D F θ V (Z ^ (tau / 2))) ≤
        C * testSeminorm V.toFun J (tailOrder B tau L) * Z ^ (-L) := by
  obtain ⟨J, C, hC, hb⟩ := actual_column_tail K S D F θ hKernel hθ hD
    (tailOrder B tau L) (tailOrder_ge_one hB htau hL.le)
  obtain ⟨Z1, hZ1, hz1⟩ := exists_ratio_threshold tau htau
  refine ⟨J, C, max 2 Z1, hC, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro Z hZ0
  have hZ : 1 < Z := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hZ0)
  refine ⟨hz1 Z ((le_max_right _ _).trans hZ0), ?_⟩
  intro V ι I p hX hpref
  have hCS := mul_nonneg hC (seminorm_nonneg V.toFun J (tailOrder B tau L))
  have hpiece (i : ι) (hi : i ∈ I) := hb V (p i).classes (p i).fixed (p i).state
    (p i).X (Z ^ (tau / 2)) (p i).row (p i).mark (hX i hi) (by positivity)
  have hsum (i : ι) (hi : i ∈ I) : Summable (fun cb => ‖(p i).weight *
      tailColumnAtom K S D (p i).fixed (p i).state F θ (p i).classes V.toFun (p i).X
        (Z ^ (tau / 2)) (p i).row (p i).mark cb‖) := by
    simpa only [norm_mul] using (hpiece i hi).1.mul_left ‖(p i).weight‖
  refine ⟨hsum, ?_⟩
  have hlocal (i : ι) (hi : i ∈ I) :
      (p i).tailMass D F θ V (Z ^ (tau / 2)) ≤
      C * testSeminorm V.toFun J (tailOrder B tau L) * (p i).prefactor *
        (Z ^ (tau / 2)) ^ (-(tailOrder B tau L - 1)) := by
    unfold TailPiece.tailMass
    simp_rw [norm_mul]
    rw [tsum_mul_left]
    have h := mul_le_mul_of_nonneg_left (hpiece i hi).2 (norm_nonneg (p i).weight)
    apply h.trans_eq
    unfold TailPiece.prefactor
    ring
  calc
    _ ≤ ∑ i ∈ I, C * testSeminorm V.toFun J (tailOrder B tau L) * (p i).prefactor *
        (Z ^ (tau / 2)) ^ (-(tailOrder B tau L - 1)) := Finset.sum_le_sum hlocal
    _ = C * testSeminorm V.toFun J (tailOrder B tau L) *
        (∑ i ∈ I, (p i).prefactor) * (Z ^ (tau / 2)) ^ (-(tailOrder B tau L - 1)) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ C * testSeminorm V.toFun J (tailOrder B tau L) * Z ^ B *
        (Z ^ (tau / 2)) ^ (-(tailOrder B tau L - 1)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpref hCS) (by positivity)
    _ = _ := by
      rw [mul_assoc, polynomial_tail_eq htau (zero_lt_one.trans hZ)]

#print axioms columnWeight_summable
#print axioms kernel_tail_bound
#print axioms actual_column_tail
#print axioms argument_ge_tau_threshold
#print axioms actual_power_tail
#print axioms columnAtom_eq_tail_beyond_threshold
#print axioms prefactor_le_from_lengths
#print axioms total_prefactor_le_from_lengths
#print axioms actual_total_power_tail

end HeckeSkeleton.LowEnergy.GeneralKernelTail
