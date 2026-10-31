import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderInput
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderStates
import ThetaGlobal.ReflectedAbsoluteProject

/-!
# Arbitrary saving for the actual full-cube reflected tail

A further positive kernel line is supplied by the already proved
`MellinKernelInput.derivative_bound`. The off-threshold series is
majorized on its original two ideal coordinates by the actual
Dedekind inverse-square series. Constants are chosen before every
row, active coefficient, frozen state, and completed scale.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalTail

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.ActualReflection
  HeckeSkeleton.LowEnergy.ActualReflectionReindex
  HeckeSkeleton.LowEnergy.ActualFrozenCharges
  HeckeSkeleton.LowEnergy.ActualFrozenIndependence
  HeckeSkeleton.LowEnergy.ActualHybridEntry
  HeckeSkeleton.LowEnergy.ActualSeparatedBlock
  HeckeSkeleton.LowEnergy.ActualSymbols
  HeckeSkeleton.LowEnergy.ActualClassSlices
open HeckeSkeleton.LowEnergy
open ThetaGlobal.ReflectedAbsolute
open TerminalMellin TerminalSlices TerminalExponent
open scoped Classical BigOperators nonZeroDivisors NumberField

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local notation "Ext" => ExteriorIdeal K S

def idealMass : ℝ := ∑' I : Ext, inverseSquare (exteriorNorm K S I)

theorem idealMass_nonneg : 0 ≤ idealMass K S :=
  tsum_nonneg (fun I => inverseSquare_nonneg _)

theorem column_mass_summable : Summable (fun cb : Ext × Ext =>
    inverseSquare (exteriorNorm K S cb.1) * inverseSquare (exteriorNorm K S cb.2)) :=
  (ThetaGlobal.ReflectedAbsoluteProject.summable_exterior_inverseSquare K S).mul_of_nonneg
    (ThetaGlobal.ReflectedAbsoluteProject.summable_exterior_inverseSquare K S)
    (fun _ => inverseSquare_nonneg _) (fun _ => inverseSquare_nonneg _)

theorem column_mass :
    (∑' cb : Ext × Ext,
      inverseSquare (exteriorNorm K S cb.1) * inverseSquare (exteriorNorm K S cb.2)) =
      idealMass K S ^ 2 := by
  rw [pow_two]
  exact ((ThetaGlobal.ReflectedAbsoluteProject.summable_exterior_inverseSquare K S).tsum_mul_tsum
    (ThetaGlobal.ReflectedAbsoluteProject.summable_exterior_inverseSquare K S)
    (column_mass_summable K S)).symm

/-- A coarse count follows from the same convergent ideal majorant.
It is only used for an arbitrarily shifted tail. -/
theorem card_le_mass (R : Finset Ext) (X : ℝ) (hX : 0 < X)
    (hR : ∀ I ∈ R, exteriorNorm K S I ≤ X) :
    (R.card : ℝ) ≤ X ^ 2 * idealMass K S := by
  calc
    _ = ∑ _I ∈ R, (1 : ℝ) := by simp
    _ ≤ ∑ I ∈ R, X ^ 2 * inverseSquare (exteriorNorm K S I) := by
      apply Finset.sum_le_sum
      intro I hI
      have hs := pow_le_pow_left₀ (exteriorNorm_pos K S I).le (hR I hI) 2
      have hi := (div_le_div_iff_of_pos_right
        (sq_pos_of_pos (exteriorNorm_pos K S I))).mpr hs
      simpa only [div_self (sq_pos_of_pos (exteriorNorm_pos K S I)).ne',
        div_eq_mul_inv, inverseSquare] using hi
    _ = X ^ 2 * ∑ I ∈ R, inverseSquare (exteriorNorm K S I) :=
      (Finset.mul_sum ..).symm
    _ ≤ X ^ 2 * idealMass K S := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact (ThetaGlobal.ReflectedAbsoluteProject.summable_exterior_inverseSquare K S).sum_le_tsum
        R (fun _ _ => inverseSquare_nonneg _)

def kernelOrder (A : ℝ) : ℕ :=
  Nat.ceil (4 * (Fintype.card {v : InfinitePlace K // v.IsComplex} : ℝ) * A + 2)

/-- A fixed arbitrary positive kernel line, with one finite seminorm. -/
theorem kernel_bound (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hkernel : MellinKernelInput K S F θ) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (V : SmoothAnnularTest) (u : SixthUnitClasses K S)
        (κ : SixthLocalClasses K S) (y : ℝ), 0 < y →
      ‖mellinReflectionKernel K S F θ u κ V.toFun 0 y‖ ≤
        C * testSeminorm V.toFun (kernelOrder K A) A * y ^ (-A) := by
  let J := kernelOrder K A
  have hJ : 4 * (Fintype.card {v : InfinitePlace K // v.IsComplex} : ℝ) * A +
      (0 : ℕ) + 1 < (J : ℝ) := by
    have hc := Nat.le_ceil (4 * (Fintype.card {v : InfinitePlace K // v.IsComplex} : ℝ) * A + 2)
    dsimp [J, kernelOrder]
    push_cast
    linarith
  obtain ⟨C, hC, hb⟩ := hkernel.derivative_bound A 0 J hA hJ
  refine ⟨C, hC, ?_⟩
  intro V u κ y hy
  have hh := hb V u κ y hy
  simp only [eulerDerivativeOrder, Function.iterate_zero, id_eq] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (min_le_right _ _)
    (mul_nonneg hC (ThetaGlobal.ReflectedAbsoluteProject.testSeminorm_nonneg _ _ _)))

variable (D : ThetaArithmeticData K S)
variable (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)

theorem norm_ge_one (I : Ext) : 1 ≤ exteriorNorm K S I := by
  exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I.val

theorem stateMajorant_le_one : stateMajorant K S s ≤ 1 := by
  have hc := stateMajorant_sq_le_inverse_charge K S s
  have hn : 1 ≤ exteriorNorm K S (minimumSmallIdeal K S s) *
      exteriorNorm K S (minimumCubeIdeal K S s) :=
    one_le_mul_of_one_le_of_one_le (norm_ge_one K S _) (norm_ge_one K S _)
  have hi : (exteriorNorm K S (minimumSmallIdeal K S s) *
      exteriorNorm K S (minimumCubeIdeal K S s))⁻¹ ≤ 1 := by
    simpa only [inv_one] using inv_anti₀ (by norm_num : (0 : ℝ) < 1) hn
  nlinarith [stateMajorant_nonneg K S s]

theorem columnCoefficient_norm_le_one (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (c b : Ext) : ‖columnCoefficient K S D θ f s c b‖ ≤ 1 := by
  have hc : 1 ≤ Real.sqrt (exteriorNorm K S c) := by
    simpa using Real.sqrt_le_sqrt (norm_ge_one K S c)
  have hden : 1 ≤ Real.sqrt (exteriorNorm K S c) * exteriorNorm K S b :=
    one_le_mul_of_one_le_of_one_le hc (norm_ge_one K S b)
  apply (columnCoefficient_norm_le K S D f s θ hθ c b).trans
  exact (div_le_one (zero_lt_one.trans_le hden)).mpr
    ((stateMajorant_le_one K S f s).trans hden)

theorem hybridKernel_norm_le_one (hD : AllowedGeneratorInput K S D)
    (k P c b : Ext) :
    ‖FiniteHybridIntegral.hybridKernel (cubicKernel K S D) (quadraticKernel K S D)
      k.val.val P.val.val c.val.val b.val.val‖ ≤ 1 := by
  have hp : 1 ≤ Real.sqrt (P.val.val.absNorm : ℝ) := by
    simpa only [exteriorNorm] using Real.sqrt_le_sqrt (norm_ge_one K S P)
  have hinv : ‖(Real.sqrt (P.val.val.absNorm : ℝ) : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    simpa only [inv_one] using inv_anti₀ (by norm_num : (0 : ℝ) < 1) hp
  have hmask (I J : Ideal (𝓞 K)) : ‖KeepOriginalRow.mask I J‖ ≤ 1 := by
    unfold KeepOriginalRow.mask
    split_ifs <;> norm_num
  unfold FiniteHybridIntegral.hybridKernel
  apply mul_norm_le_one _ _ _ (hmask _ _)
  apply mul_norm_le_one _ _ _ ((cubicKernel_axioms K S D hD).norm_le_one _ _)
  apply mul_norm_le_one _ _ _ ((quadraticKernel_axioms K S D hD (fun _ => True)).norm_le_one _ _)
  exact mul_norm_le_one _ _ hinv (hmask _ _)

def argument (X : ℝ) (k P c b : Ext) : ℝ :=
  CommonMellin.argument (canonicalBase K S f s X)
    (exteriorNorm K S k) (exteriorNorm K S P)
    (exteriorNorm K S c) (exteriorNorm K S b)

theorem argument_pos {X : ℝ} (hX : 0 < X) (k P c b : Ext) :
    0 < argument K S f s X k P c b := by
  have hbase : 0 < canonicalBase K S f s X := by
    unfold canonicalBase
    have := exteriorNorm_pos K S s.minimum
    have := exteriorNorm_pos K S (primeSetIdeal K S s.active)
    positivity
  exact CommonMellin.argument_pos hbase (exteriorNorm_pos K S k)
    (exteriorNorm_pos K S P) (exteriorNorm_pos K S c) (exteriorNorm_pos K S b)

/-- Every arithmetic coefficient is contracted before the tail sum;
the inactive scalar is preserved exactly. -/
theorem atom_norm_le_kernel (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (V : ℝ → ℂ) (X : ℝ) (k P c b : Ext) :
    ‖GeneralReflectedEnergy.atom K S D f s F θ V X k P c b‖ ≤
      ‖inactiveWeight K S f‖ *
        ‖mellinReflectionKernel K S F θ (QuotientGroup.mk f.rowUnit)
          (blockFrequency (frozenClass K S D f s) (generatorLocalClass K S D k)
            (generatorLocalClass K S D P) (generatorLocalClass K S D c)
            (generatorLocalClass K S D b)) V 0 (argument K S f s X k P c b)‖ := by
  by_cases hk : RowAdmissible K S f k
  · by_cases hP : MarkAdmissible K S f P
    · rw [atom_eq_entry K S D f s hD F θ V X k P c b hk hP]
      unfold entry argument
      have hcoeff := mul_norm_le_one _ _
        (mul_norm_le_one _ _
          (mul_norm_le_one _ _ (rowCoefficient_norm_le_one K S D f s θ hθ k)
            (markCoefficient_norm_le_one K S D f s θ hθ P))
          (columnCoefficient_norm_le_one K S D f s θ hθ c b))
        (hybridKernel_norm_le_one K S D hD k P c b)
      have hi := mul_le_mul_of_nonneg_left hcoeff (norm_nonneg (inactiveWeight K S f))
      have ho := mul_le_mul_of_nonneg_right hi
        (norm_nonneg (mellinReflectionKernel K S F θ (QuotientGroup.mk f.rowUnit)
          (blockFrequency (frozenClass K S D f s) (generatorLocalClass K S D k)
            (generatorLocalClass K S D P) (generatorLocalClass K S D c)
            (generatorLocalClass K S D b)) V 0
          (CommonMellin.argument (canonicalBase K S f s X)
            (exteriorNorm K S k) (exteriorNorm K S P)
            (exteriorNorm K S c) (exteriorNorm K S b))))
      simpa only [norm_mul, mul_one, mul_assoc] using ho
    · simp only [GeneralReflectedEnergy.atom, dif_pos hk, dif_neg hP, norm_zero]
      positivity
  · simp only [GeneralReflectedEnergy.atom, dif_neg hk, norm_zero]
    positivity

/-- Only the literal active radical is counted in this coarse tail
bound. It divides the frozen row times the puncture. -/
theorem active_norm_le (f : FixedData K S)
    (s : FrozenState K S f.frozen f.puncture) :
    exteriorNorm K S (primeSetIdeal K S s.active) ≤
      exteriorNorm K S f.frozen * exteriorNorm K S f.puncture := by
  have hn : 0 < (f.frozen.val.val * f.puncture.val.val).absNorm := by
    exact Ideal.absNorm_pos_of_nonZeroDivisors (f.frozen.val * f.puncture.val)
  have hd := Ideal.absNorm_dvd_absNorm_of_le
    (Ideal.dvd_iff_le.mp (TerminalStates.active_divides K S f.frozen f.puncture s))
  have hh := Nat.le_of_dvd hn hd
  simpa only [map_mul, Nat.cast_mul, exteriorNorm] using
    (show ((primeSetIdeal K S s.active).val.val.absNorm : ℝ) ≤
      ((f.frozen.val.val * f.puncture.val.val).absNorm : ℝ) by exact_mod_cast hh)

theorem threshold_le {Z L Nstar H za : ℝ} (hZ : 1 < Z)
    (hsource : GeneralReflectedEnergy.BoundedSource K S f Z L Nstar H za) :
    GeneralReflectedEnergy.threshold K S f s Z Nstar H za ≤ 9 * L := by
  rcases hsource with ⟨hN, hH0, hH, hza0, hza, hf, hr, hi⟩
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hn : exteriorNorm K S (primeSetIdeal K S s.active) ≤ Z ^ (2 * L) := by
    apply (active_norm_le K S f s).trans
    calc
      _ ≤ Z ^ L * Z ^ L := mul_le_mul hf hr (exteriorNorm_pos K S f.puncture).le (by positivity)
      _ = _ := by rw [← Real.rpow_add hz]; congr 1 <;> ring
  have ha : GeneralReflectedEnergy.logNorm K S Z (primeSetIdeal K S s.active) ≤ 2 * L := by
    have hh := (Real.logb_le_iff_le_rpow hZ
      (exteriorNorm_pos K S (primeSetIdeal K S s.active))).mpr hn
    simpa only [GeneralReflectedEnergy.logNorm, Real.logb] using hh
  unfold GeneralReflectedEnergy.threshold
  have hlin := logNorm_nonneg K S hZ (minimumLinearIdeal K S s)
  have hcub := logNorm_nonneg K S hZ (minimumCubeIdeal K S s)
  have hNlow := (abs_le.mp hN).1
  linarith

/-- The factor sixteen is the complete row/active-mark dyadic loss.
The squarefree and full-cube coordinates are still literal norms. -/
theorem argument_lower {Z Nstar H za : ℝ} (hZ : 1 < Z) (k P c b : Ext)
    (hk : GeneralReflectedEnergy.InAnnulus K S Z H k)
    (hP : GeneralReflectedEnergy.InAnnulus K S Z za P) :
    Z ^ (-GeneralReflectedEnergy.threshold K S f s Z Nstar H za) *
      exteriorNorm K S c * exteriorNorm K S b ^ 3 / 16 ≤
      argument K S f s (Z ^ Nstar) k P c b := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hkpos := exteriorNorm_pos K S k
  have hPpos := exteriorNorm_pos K S P
  have hcpos := exteriorNorm_pos K S c
  have hbpos := exteriorNorm_pos K S b
  have hmpos := exteriorNorm_pos K S s.minimum
  have hapos := exteriorNorm_pos K S (primeSetIdeal K S s.active)
  have hscale := canonicalScale_eq K S f s hZ Nstar H za 0 0
  simp only [Real.rpow_zero, one_pow, mul_one, zero_add, zero_mul, sub_zero,
    zero_sub] at hscale
  have hden : exteriorNorm K S k ^ 2 * exteriorNorm K S P ^ 2 ≤
      16 * ((Z ^ H) ^ 2 * (Z ^ za) ^ 2) := by
    have hh := mul_le_mul (pow_le_pow_left₀ (exteriorNorm_pos K S k).le hk.2 2)
      (pow_le_pow_left₀ (exteriorNorm_pos K S P).le hP.2 2) (sq_nonneg _) (sq_nonneg _)
    convert hh using 1 <;> ring
  calc
    _ = (canonicalBase K S f s (Z ^ Nstar) * exteriorNorm K S c *
        exteriorNorm K S b ^ 3) / (16 * ((Z ^ H) ^ 2 * (Z ^ za) ^ 2)) := by
      rw [← hscale]
      unfold canonicalScale
      simp only [Real.rpow_zero, one_pow, mul_one]
      field_simp
      <;> ring
    _ ≤ (canonicalBase K S f s (Z ^ Nstar) * exteriorNorm K S c *
        exteriorNorm K S b ^ 3) / (exteriorNorm K S k ^ 2 * exteriorNorm K S P ^ 2) := by
      apply div_le_div_of_nonneg_left _ (by positivity) hden
      unfold canonicalBase
      positivity
    _ = _ := rfl

theorem argument_tail_lower {Z Nstar H za tau : ℝ} (hZ : 1 < Z) (k P c b : Ext)
    (hk : GeneralReflectedEnergy.InAnnulus K S Z H k)
    (hP : GeneralReflectedEnergy.InAnnulus K S Z za P)
    (htail : Z ^ (GeneralReflectedEnergy.threshold K S f s Z Nstar H za + tau) <
      exteriorNorm K S c * exteriorNorm K S b ^ 3) :
    Z ^ tau / 16 ≤ argument K S f s (Z ^ Nstar) k P c b := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  calc
    _ = Z ^ (-GeneralReflectedEnergy.threshold K S f s Z Nstar H za) *
        Z ^ (GeneralReflectedEnergy.threshold K S f s Z Nstar H za + tau) / 16 := by
      rw [← Real.rpow_add hz]
      congr 2
      ring
    _ ≤ Z ^ (-GeneralReflectedEnergy.threshold K S f s Z Nstar H za) *
        (exteriorNorm K S c * exteriorNorm K S b ^ 3) / 16 := by
      gcongr
      exact htail.le
    _ ≤ _ := by
      simpa only [mul_assoc] using argument_lower K S f s hZ k P c b hk hP

theorem argument_inverseSquare_le {Z L Nstar H za : ℝ} (hZ : 1 < Z)
    (hsource : GeneralReflectedEnergy.BoundedSource K S f Z L Nstar H za)
    (k P c b : Ext)
    (hk : GeneralReflectedEnergy.InAnnulus K S Z H k)
    (hP : GeneralReflectedEnergy.InAnnulus K S Z za P) :
    inverseSquare (argument K S f s (Z ^ Nstar) k P c b) ≤
      256 * Z ^ (18 * L) * inverseSquare (exteriorNorm K S c) *
        inverseSquare (exteriorNorm K S b) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hcpos := exteriorNorm_pos K S c
  have hbpos := exteriorNorm_pos K S b
  have ht : 0 < Z ^ (-9 * L) / 16 := by positivity
  have hl : (Z ^ (-9 * L) / 16) * 1 * exteriorNorm K S c * exteriorNorm K S b ^ 3 ≤
      argument K S f s (Z ^ Nstar) k P c b := by
    have hh := Real.rpow_le_rpow_of_exponent_le hZ.le
      (neg_le_neg (threshold_le K S f s hZ hsource))
    have hh' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hh (exteriorNorm_pos K S c).le)
      (pow_nonneg (exteriorNorm_pos K S b).le 3)
    have hdiv := div_le_div_of_nonneg_right hh' (by norm_num : (0 : ℝ) ≤ 16)
    apply (by convert hdiv using 1 <;> ring).trans
    exact argument_lower K S f s hZ k P c b hk hP
  have hinv : inverseSquare (argument K S f s (Z ^ Nstar) k P c b) ≤
      inverseSquare ((Z ^ (-9 * L) / 16) * 1 * exteriorNorm K S c * exteriorNorm K S b ^ 3) := by
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hl 2)
  have hh := cubic_scale_inverse_square_le 1 (exteriorNorm K S c) (exteriorNorm K S b)
    (Z ^ (-9 * L) / 16) (by norm_num) (exteriorNorm_pos K S c) (norm_ge_one K S b) ht
  have hscale : (Z ^ (-9 * L) / 16)⁻¹ ^ 2 = 256 * Z ^ (18 * L) := by
    rw [inv_div, div_pow, ← Real.rpow_mul_natCast hz.le, div_eq_mul_inv,
      ← Real.rpow_neg hz.le]
    norm_num
    congr 1
    ring
  exact hinv.trans (by simpa only [hscale, inverseSquare, one_pow, inv_one, mul_one] using hh)

/-- The extra positive kernel line is used only on the literal removed
range. The remaining two-coordinate majorant is summable. -/
theorem tail_power_bound {Z L Nstar H za tau A : ℝ} (hZ : 1 < Z) (hA : 2 ≤ A)
    (hsource : GeneralReflectedEnergy.BoundedSource K S f Z L Nstar H za)
    (k P c b : Ext)
    (hk : GeneralReflectedEnergy.InAnnulus K S Z H k)
    (hP : GeneralReflectedEnergy.InAnnulus K S Z za P)
    (htail : Z ^ (GeneralReflectedEnergy.threshold K S f s Z Nstar H za + tau) <
      exteriorNorm K S c * exteriorNorm K S b ^ 3) :
    argument K S f s (Z ^ Nstar) k P c b ^ (-A) ≤
      (256 * 16 ^ (A - 2)) * Z ^ (18 * L - tau * (A - 2)) *
        (inverseSquare (exteriorNorm K S c) * inverseSquare (exteriorNorm K S b)) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  let y := argument K S f s (Z ^ Nstar) k P c b
  have hy : 0 < y := argument_pos K S f s (Real.rpow_pos_of_pos hz _) k P c b
  have hsplit : y ^ (-A) = inverseSquare y * y ^ (-(A - 2)) := by
    rw [inverseSquare, ← Real.rpow_two, ← Real.rpow_neg hy.le, ← Real.rpow_add hy]
    congr 1
    ring
  have htailpow : y ^ (-(A - 2)) ≤ 16 ^ (A - 2) * Z ^ (-tau * (A - 2)) := by
    have hh := Real.rpow_le_rpow_of_nonpos (show 0 < Z ^ tau / 16 by positivity)
      (argument_tail_lower K S f s hZ k P c b hk hP htail) (by linarith : -(A - 2) ≤ 0)
    apply hh.trans_eq
    rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hz.le,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 16), div_inv_eq_mul, mul_comm]
    congr 1
    congr 1
    ring
  rw [hsplit]
  have hh := mul_le_mul (argument_inverseSquare_le K S f s hZ hsource k P c b hk hP)
    htailpow (Real.rpow_nonneg hy.le _) (by positivity)
  apply hh.trans_eq
  calc
    _ = (256 * 16 ^ (A - 2)) *
        (Z ^ (18 * L) * Z ^ (-tau * (A - 2))) *
        (inverseSquare (exteriorNorm K S c) * inverseSquare (exteriorNorm K S b)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hz]
      congr 2
      ring

/-- The original tail is absolutely summable with its original two
ideal coordinates. The majorant is selected independently of P and k. -/
theorem tail_norm_bound
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (A C : ℝ) (J : ℕ) (hA : 2 ≤ A) (hC : 0 ≤ C)
    (hkernel : ∀ (V : SmoothAnnularTest) (u : SixthUnitClasses K S)
      (κ : SixthLocalClasses K S) (y : ℝ), 0 < y →
      ‖mellinReflectionKernel K S F θ u κ V.toFun 0 y‖ ≤ C * testSeminorm V.toFun J A * y ^ (-A))
    (V : SmoothAnnularTest) (Z L Nstar H za tau amp : ℝ) (hZ : 1 < Z)
    (hsource : GeneralReflectedEnergy.BoundedSource K S f Z L Nstar H za)
    (hamp : 0 ≤ amp) (ps : Finset Ext) (a : Ext → ℂ) (k : Ext)
    (hk : GeneralReflectedEnergy.InAnnulus K S Z H k)
    (hps : ∀ P ∈ ps, GeneralReflectedEnergy.InAnnulus K S Z za P)
    (ha : ∀ P ∈ ps, ‖a P‖ ≤ amp) :
    ‖GeneralReflectedEnergy.tail K S D f s F θ a V.toFun Z Nstar H za tau ps k‖ ≤
      (ps.card : ℝ) * amp * ‖inactiveWeight K S f‖ * C * testSeminorm V.toFun J A *
        ((256 * 16 ^ (A - 2)) * Z ^ (18 * L - tau * (A - 2))) * idealMass K S ^ 2 := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hq : 0 ≤ testSeminorm V.toFun J A :=
    ThetaGlobal.ReflectedAbsoluteProject.testSeminorm_nonneg _ _ _
  let B := ‖inactiveWeight K S f‖ * C * testSeminorm V.toFun J A *
    ((256 * 16 ^ (A - 2)) * Z ^ (18 * L - tau * (A - 2)))
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let term (P : Ext) (cb : Ext × Ext) : ℂ :=
    if Z ^ (GeneralReflectedEnergy.threshold K S f s Z Nstar H za + tau) <
        exteriorNorm K S cb.1 * exteriorNorm K S cb.2 ^ 3 then
      GeneralReflectedEnergy.atom K S D f s F θ V.toFun (Z ^ Nstar) k P cb.1 cb.2
    else 0
  have hterm (P : Ext) (hP : P ∈ ps) (cb : Ext × Ext) :
      ‖term P cb‖ ≤ B *
        (inverseSquare (exteriorNorm K S cb.1) * inverseSquare (exteriorNorm K S cb.2)) := by
    dsimp only [term]
    split_ifs with ht
    · have hy := argument_pos K S f s (Real.rpow_pos_of_pos hz _) k P cb.1 cb.2
      have hkern := hkernel V (QuotientGroup.mk f.rowUnit)
        (blockFrequency (frozenClass K S D f s) (generatorLocalClass K S D k)
          (generatorLocalClass K S D P) (generatorLocalClass K S D cb.1)
          (generatorLocalClass K S D cb.2)) _ hy
      have hn := atom_norm_le_kernel K S D f s hreflection.allowed_generators F θ
        hreflection.exterior_unramified V.toFun (Z ^ Nstar) k P cb.1 cb.2
      have ht := tail_power_bound K S f s hZ hA hsource k P cb.1 cb.2 hk (hps P hP) ht
      apply (hn.trans (mul_le_mul_of_nonneg_left hkern (norm_nonneg _))).trans
      have hh := mul_le_mul_of_nonneg_left ht
        (show 0 ≤ ‖inactiveWeight K S f‖ * (C * testSeminorm V.toFun J A) by positivity)
      simpa only [B, mul_assoc] using hh
    · simp only [norm_zero]
      exact mul_nonneg hB (mul_nonneg (inverseSquare_nonneg _) (inverseSquare_nonneg _))
  have hsum (P : Ext) (hP : P ∈ ps) :
      ‖∑' cb : Ext × Ext, term P cb‖ ≤ B * idealMass K S ^ 2 := by
    have hmajor := (column_mass_summable K S).mul_left B
    have hnorm : Summable (fun cb : Ext × Ext => ‖term P cb‖) :=
      hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) (hterm P hP)
    calc
      _ ≤ ∑' cb : Ext × Ext, ‖term P cb‖ := norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' cb : Ext × Ext, B *
          (inverseSquare (exteriorNorm K S cb.1) * inverseSquare (exteriorNorm K S cb.2)) :=
        hnorm.tsum_le_tsum (hterm P hP) hmajor
      _ = B * idealMass K S ^ 2 := by rw [tsum_mul_left, column_mass]
  unfold GeneralReflectedEnergy.tail
  calc
    _ ≤ ∑ P ∈ ps, ‖a P * ∑' cb : Ext × Ext, term P cb‖ := norm_sum_le _ _
    _ ≤ ∑ _P ∈ ps, amp * (B * idealMass K S ^ 2) := by
      apply Finset.sum_le_sum
      intro P hP
      rw [norm_mul]
      exact mul_le_mul (ha P hP) (hsum P hP) (norm_nonneg _) hamp
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      dsimp only [B]
      ring

def tailShift (L tau saving : ℝ) : ℝ := 2 + (saving + 42 * L) / (2 * tau)

theorem tailShift_ge_two {L tau saving : ℝ} (hL : 0 ≤ L)
    (htau : 0 < tau) (hsaving : 0 ≤ saving) : 2 ≤ tailShift L tau saving := by
  unfold tailShift
  have hq : 0 ≤ (saving + 42 * L) / (2 * tau) := by positivity
  linarith

/-- Actual arbitrary saving for one fixed period. The only analytic
input is its genuine Mellin kernel, already contained in reflection. -/
theorem fixed_period_tail_energy
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (L tau saving : ℝ) (hL : 0 < L) (htau : 0 < tau) (hsaving : 0 < saving) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
        (V : SmoothAnnularTest) (Z Nstar H za amp : ℝ),
      1 < Z → GeneralReflectedEnergy.BoundedSource K S f Z L Nstar H za → 0 ≤ amp →
      ∀ (rows ps : Finset Ext) (a : Ext → ℂ),
      (∀ k ∈ rows, GeneralReflectedEnergy.InAnnulus K S Z H k) →
      (∀ P ∈ ps, GeneralReflectedEnergy.InAnnulus K S Z za P) →
      (∀ P ∈ ps, ‖a P‖ ≤ amp) →
      (∑ k ∈ rows, ‖GeneralReflectedEnergy.tail K S D f s F θ a V.toFun
        Z Nstar H za tau ps k‖ ^ 2) ≤
        C * amp ^ 2 *
          testSeminorm V.toFun (kernelOrder K (tailShift L tau saving)) (tailShift L tau saving) ^ 2 *
          ‖inactiveWeight K S f‖ ^ 2 * Z ^ (-saving) := by
  let A := tailShift L tau saving
  have hA : 2 ≤ A := tailShift_ge_two hL.le htau hsaving.le
  obtain ⟨C, hC, hk⟩ := kernel_bound K S F θ hreflection.kernel A (by linarith)
  let B := 4 * idealMass K S * C * (256 * 16 ^ (A - 2)) * idealMass K S ^ 2
  have hm := idealMass_nonneg K S
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let Cout := 4 * idealMass K S * B ^ 2
  have hCout : 0 ≤ Cout := by dsimp only [Cout]; positivity
  refine ⟨1 + Cout, by positivity, ?_⟩
  intro f s V Z Nstar H za amp hZ hsource hamp rows ps a hrows hps ha
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hq : 0 ≤ testSeminorm V.toFun (kernelOrder K A) A :=
    ThetaGlobal.ReflectedAbsoluteProject.testSeminorm_nonneg _ _ _
  have hm := idealMass_nonneg K S
  have hcard (R : Finset Ext) (hR : ∀ I ∈ R, exteriorNorm K S I ≤ 2 * Z ^ L) :
      (R.card : ℝ) ≤ 4 * idealMass K S * Z ^ (2 * L) := by
    have hh := card_le_mass K S R (2 * Z ^ L) (by positivity) hR
    apply hh.trans_eq
    rw [mul_pow, ← Real.rpow_mul_natCast hz.le]
    norm_num
    have he : L * (2 : ℝ) = 2 * L := by ring
    rw [he]
    ring
  have hrowsCard : (rows.card : ℝ) ≤ 4 * idealMass K S * Z ^ (2 * L) := by
    apply hcard
    intro k hk
    exact (hrows k hk).2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.le hsource.2.2.1) (by norm_num))
  have hpsCard : (ps.card : ℝ) ≤ 4 * idealMass K S * Z ^ (2 * L) := by
    apply hcard
    intro P hP
    exact (hps P hP).2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.le hsource.2.2.2.2.1) (by norm_num))
  have hrow (k : Ext) (hkr : k ∈ rows) :
      ‖GeneralReflectedEnergy.tail K S D f s F θ a V.toFun Z Nstar H za tau ps k‖ ≤
        B * amp * testSeminorm V.toFun (kernelOrder K A) A * ‖inactiveWeight K S f‖ *
          Z ^ (20 * L - tau * (A - 2)) := by
    have hh := tail_norm_bound K S D f s F θ hreflection A C (kernelOrder K A) hA hC hk
      V Z L Nstar H za tau amp hZ hsource hamp ps a k (hrows k hkr) hps ha
    have hc := mul_le_mul_of_nonneg_right hpsCard
      (show 0 ≤ amp * ‖inactiveWeight K S f‖ * C *
        testSeminorm V.toFun (kernelOrder K A) A *
        ((256 * 16 ^ (A - 2)) * Z ^ (18 * L - tau * (A - 2))) * idealMass K S ^ 2 by positivity)
    apply hh.trans
    apply (by simpa only [mul_assoc] using hc : _ ≤ _).trans_eq
    calc
      _ = B * amp * testSeminorm V.toFun (kernelOrder K A) A * ‖inactiveWeight K S f‖ *
          (Z ^ (2 * L) * Z ^ (18 * L - tau * (A - 2))) := by dsimp only [B]; ring
      _ = _ := by rw [← Real.rpow_add hz]; congr 1 <;> congr 1 <;> ring
  let R := B * amp * testSeminorm V.toFun (kernelOrder K A) A * ‖inactiveWeight K S f‖ *
    Z ^ (20 * L - tau * (A - 2))
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  calc
    _ ≤ ∑ _k ∈ rows, R ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk'
      exact pow_le_pow_left₀ (norm_nonneg _) (hrow k hk') 2
    _ = (rows.card : ℝ) * R ^ 2 := by simp
    _ ≤ (4 * idealMass K S * Z ^ (2 * L)) * R ^ 2 :=
      mul_le_mul_of_nonneg_right hrowsCard (sq_nonneg _)
    _ = Cout * amp ^ 2 * testSeminorm V.toFun (kernelOrder K A) A ^ 2 *
        ‖inactiveWeight K S f‖ ^ 2 * Z ^ (-saving) := by
      have hexp : 2 * L + (20 * L - tau * (A - 2)) * 2 = -saving := by
        dsimp only [A, tailShift]
        field_simp [htau.ne']
        <;> ring
      dsimp only [R, Cout]
      simp only [mul_pow]
      rw [← Real.rpow_mul_natCast hz.le]
      have hpow : Z ^ (2 * L) * Z ^ ((20 * L - tau * (A - 2)) * 2) = Z ^ (-saving) := by
        rw [← Real.rpow_add hz, hexp]
      calc
        _ = (4 * idealMass K S * B ^ 2) * amp ^ 2 *
            testSeminorm V.toFun (kernelOrder K A) A ^ 2 * ‖inactiveWeight K S f‖ ^ 2 *
            (Z ^ (2 * L) * Z ^ ((20 * L - tau * (A - 2)) * 2)) := by ring
        _ = _ := by rw [hpow]
    _ ≤ _ := by
      dsimp only [A]
      gcongr
      linarith

/-- Uniform tail input on the one fixed finite period inventory. The
positive line and finite derivative order are common to all periods. -/
theorem uniform_tail_energy
    (backgrounds : Finset (HeckeCharacter K))
    (R : GeneralReflectedEnergy.ReflectionFamily K S D backgrounds)
    (L lo hi tau saving : ℝ) (hL : 0 < L) (_hlo : 0 < lo) (_hhi : lo ≤ hi)
    (htau : 0 < tau) (hsaving : 0 < saving) :
    ∃ C Z₀ A : ℝ, ∃ J : ℕ,
      0 < C ∧ 1 < Z₀ ∧ 0 ≤ A ∧
      ∀ (θ : HeckeCharacter K), θ ∈ backgrounds →
      MarkedCoefficientReflectionInput K S D (R.data θ) θ →
      ∀ (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
        (V : SmoothAnnularTest) (Z Nstar H za amp : ℝ),
      Z₀ ≤ Z → GeneralReflectedEnergy.BoundedSource K S f Z L Nstar H za → 0 ≤ amp →
      Function.support V.toFun ⊆ Set.Icc lo hi →
      ∀ (rows ps : Finset Ext) (a : Ext → ℂ),
      (∀ k ∈ rows, GeneralReflectedEnergy.InAnnulus K S Z H k) →
      (∀ P ∈ ps, GeneralReflectedEnergy.InAnnulus K S Z za P) →
      (∀ P ∈ ps, ‖a P‖ ≤ amp) →
      (∑ k ∈ rows, ‖GeneralReflectedEnergy.tail K S D f s (R.data θ) θ a V.toFun
        Z Nstar H za tau ps k‖ ^ 2) ≤
        C * amp ^ 2 * testSeminorm V.toFun J A ^ 2 * ‖inactiveWeight K S f‖ ^ 2 *
          Z ^ (-saving) := by
  classical
  choose C hC hb using fun θ : backgrounds => fixed_period_tail_energy K S D
    (R.data θ.val) θ.val (R.reflection θ.val θ.property) L tau saving hL htau hsaving
  refine ⟨1 + ∑ θ : backgrounds, C θ, 2, tailShift L tau saving,
    kernelOrder K (tailShift L tau saving), by positivity, by norm_num,
    le_trans (by norm_num) (tailShift_ge_two hL.le htau hsaving.le), ?_⟩
  intro θ hθ _hreflection f s V Z Nstar H za amp hZ hsource hamp _hV rows ps a hr hp ha
  have hz : 1 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hh := hb ⟨θ, hθ⟩ f s V Z Nstar H za amp hz hsource hamp rows ps a hr hp ha
  have hconst : C ⟨θ, hθ⟩ ≤ 1 + ∑ θ : backgrounds, C θ := by
    have hs : C ⟨θ, hθ⟩ ≤ ∑ θ : backgrounds, C θ :=
      Finset.single_le_sum (fun θ _ => (hC θ).le) (Finset.mem_univ _)
    linarith
  exact hh.trans (by gcongr)

/-- The general Lemma 4.8 interface is a consequence of the original
two sieves and the genuine coefficient-reflection family. It is not
an additional premise of the canonical inverse theorem. -/
theorem reflected_energy_input [Finite (SixthLocalClasses K S)]
    (backgrounds : Finset (HeckeCharacter K))
    (R : GeneralReflectedEnergy.ReflectionFamily K S D backgrounds)
    (hquadratic : HeckeSkeleton.LowEnergy.ActualSieveDictionary.ExteriorQuadraticBound K S D)
    (hcubic : HeckeSkeleton.LowEnergy.ActualSieveDictionary.ExteriorCubicBound K S D) :
    GeneralReflectedEnergy.Input K S D R.data backgrounds where
  block_energy := TerminalInput.uniform_block_energy K S D backgrounds R hquadratic hcubic
  tail_energy := uniform_tail_energy K S D backgrounds R

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalTail

end
