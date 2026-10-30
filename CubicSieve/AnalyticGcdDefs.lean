import CubicSieve.AnalyticRowDecomposition
import CubicSieve.AnalyticDyadic

/-!
Actual ordinary-ideal quotients and column gcd factors for the cubic Gram
expansion. Quotients stay outside the original S, and division rescales the
actual ideal norm. No principal-ideal-domain assumption on algebraic integers
is used. Kernel multiplicativity comes from the actual allowed section.
-/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.AnalyticGcd

open NumberField IsDedekindDomain
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open CubicSieve.ExteriorKernel CubicSieve.AnalyticRowDecomposition
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

def quotient (d I : ExteriorIdeal K S) (h : d.val.val ∣ I.val.val) : ExteriorIdeal K S := by
  let q : Ideal (𝓞 K) := Classical.choose h
  have he : I.val.val = d.val.val * q := Classical.choose_spec h
  have hq : q ≠ 0 := by
    intro hz
    exact nonZeroDivisors.coe_ne_zero I.val (by rw [he, hz, mul_zero])
  refine ⟨⟨q, mem_nonZeroDivisors_of_ne_zero hq⟩, ?_⟩
  intro p hp
  exact I.property p (dvd_trans hp ⟨d.val.val, he.trans (mul_comm _ _)⟩)

theorem quotient_product (d I : ExteriorIdeal K S) (h : d.val.val ∣ I.val.val) :
    exteriorMul K S d (quotient K S d I h) = I := by
  apply Subtype.ext
  apply Subtype.ext
  exact (Classical.choose_spec h).symm

theorem quotient_dvd (d I : ExteriorIdeal K S) (h : d.val.val ∣ I.val.val) :
    (quotient K S d I h).val.val ∣ I.val.val := by
  refine ⟨d.val.val, ?_⟩
  have he := congrArg (fun J : ExteriorIdeal K S => J.val.val) (quotient_product K S d I h)
  exact he.symm.trans (mul_comm _ _)

theorem quotient_squarefree (d I : ExteriorIdeal K S) (h : d.val.val ∣ I.val.val)
    (hI : Squarefree I.val.val) : Squarefree (quotient K S d I h).val.val :=
  hI.squarefree_of_dvd (quotient_dvd K S d I h)

theorem quotient_norm_mul (d I : ExteriorIdeal K S) (h : d.val.val ∣ I.val.val) :
    exteriorNorm K S d * exteriorNorm K S (quotient K S d I h) = exteriorNorm K S I := by
  have he := congrArg (fun J : ExteriorIdeal K S => J.val.val.absNorm)
    (quotient_product K S d I h)
  simp only [exteriorMul, Submonoid.coe_mul, map_mul] at he
  change (d.val.val.absNorm : ℝ) * ((quotient K S d I h).val.val.absNorm : ℝ) =
    (I.val.val.absNorm : ℝ)
  exact_mod_cast he

theorem quotient_norm (d I : ExteriorIdeal K S) (h : d.val.val ∣ I.val.val) :
    exteriorNorm K S (quotient K S d I h) = exteriorNorm K S I / exteriorNorm K S d := by
  have hd := AnalyticDyadic.one_le_norm K S d
  apply (eq_div_iff (by linarith : exteriorNorm K S d ≠ 0)).mpr
  simpa only [mul_comm] using quotient_norm_mul K S d I h

theorem quotient_injective (d : ExteriorIdeal K S) : Function.Injective
    (fun I : {I : ExteriorIdeal K S // d.val.val ∣ I.val.val} => quotient K S d I.val I.property) := by
  intro I J h
  have he := congrArg (exteriorMul K S d) h
  rw [quotient_product, quotient_product] at he
  exact Subtype.ext he

def exteriorGcd (I J : ExteriorIdeal K S) : ExteriorIdeal K S := by
  have h0 : gcd I.val.val J.val.val ≠ 0 := by
    intro hz
    have hd : gcd I.val.val J.val.val ∣ I.val.val := gcd_dvd_left _ _
    rw [hz, zero_dvd_iff] at hd
    exact nonZeroDivisors.coe_ne_zero I.val hd
  exact ⟨⟨gcd I.val.val J.val.val, mem_nonZeroDivisors_of_ne_zero h0⟩,
    fun p hp => I.property p (dvd_trans hp (gcd_dvd_left _ _))⟩

@[simp] theorem exteriorGcd_val (I J : ExteriorIdeal K S) :
    (exteriorGcd K S I J).val.val = gcd I.val.val J.val.val := rfl

theorem exteriorGcd_dvd_left (I J : ExteriorIdeal K S) :
    (exteriorGcd K S I J).val.val ∣ I.val.val := gcd_dvd_left _ _

theorem exteriorGcd_dvd_right (I J : ExteriorIdeal K S) :
    (exteriorGcd K S I J).val.val ∣ J.val.val := gcd_dvd_right _ _

theorem gcd_eq_iff_quotient_coprime (d I J : ExteriorIdeal K S)
    (hI : d.val.val ∣ I.val.val) (hJ : d.val.val ∣ J.val.val) :
    exteriorGcd K S I J = d ↔
      IsCoprime (quotient K S d I hI).val.val (quotient K S d J hJ).val.val := by
  let a := (quotient K S d I hI).val.val
  let b := (quotient K S d J hJ).val.val
  have heI : I.val.val = d.val.val * a :=
    (congrArg (fun X : ExteriorIdeal K S => X.val.val) (quotient_product K S d I hI)).symm
  have heJ : J.val.val = d.val.val * b :=
    (congrArg (fun X : ExteriorIdeal K S => X.val.val) (quotient_product K S d J hJ)).symm
  have he : gcd I.val.val J.val.val = d.val.val * gcd a b := by
    rw [heI, heJ, gcd_mul_left, normalize_eq]
  constructor
  · intro hg
    apply Ideal.isCoprime_iff_gcd.mpr
    apply mul_left_cancel₀ (nonZeroDivisors.coe_ne_zero d.val)
    have hh := congrArg (fun X : ExteriorIdeal K S => X.val.val) hg
    change gcd I.val.val J.val.val = d.val.val at hh
    rw [he] at hh
    simpa only [mul_one] using hh
  · intro hcop
    apply Subtype.ext
    apply Subtype.ext
    change gcd I.val.val J.val.val = d.val.val
    rw [he, Ideal.isCoprime_iff_gcd.mp hcop, mul_one]

theorem positiveKernel_column_mul (hD : AllowedGeneratorInput K S D)
    (I A B : ExteriorIdeal K S) :
    positiveKernel K S D I (exteriorMul K S A B) =
      positiveKernel K S D I A * positiveKernel K S D I B := by
  calc
    _ = positiveKernel K S D (exteriorMul K S A B) I :=
      kernel_reciprocity K S D hD 2 I (exteriorMul K S A B)
    _ = positiveKernel K S D A I * positiveKernel K S D B I :=
      positiveKernel_row_mul K S D hD A B I
    _ = _ := by
      rw [show positiveKernel K S D A I = positiveKernel K S D I A from
        kernel_reciprocity K S D hD 2 A I,
        show positiveKernel K S D B I = positiveKernel K S D I B from
          kernel_reciprocity K S D hD 2 B I]

theorem kernel_divisor_factor (hD : AllowedGeneratorInput K S D)
    (R d I : ExteriorIdeal K S) (h : d.val.val ∣ I.val.val) :
    positiveKernel K S D R I =
      positiveKernel K S D R d * positiveKernel K S D R (quotient K S d I h) := by
  calc
    _ = positiveKernel K S D R (exteriorMul K S d (quotient K S d I h)) :=
      congrArg (positiveKernel K S D R) (quotient_product K S d I h).symm
    _ = _ := positiveKernel_column_mul K S D hD R d (quotient K S d I h)

theorem common_kernel_mask (R d : ExteriorIdeal K S) :
    conj (positiveKernel K S D R d) * positiveKernel K S D R d =
      if IsCoprime R.val.val d.val.val then 1 else 0 := by
  rw [← positiveKernel_square_eq_conj]
  calc
    _ = positiveKernel K S D R d ^ 3 := by ring
    _ = _ := positiveKernel_cube_coprime_mask K S D R d

/-- A true column gcd removes exactly the common-prime mask and leaves a coprime pair. -/
theorem gcd_pair_factor (hD : AllowedGeneratorInput K S D)
    (R d I J : ExteriorIdeal K S) (hI : d.val.val ∣ I.val.val) (hJ : d.val.val ∣ J.val.val)
    (a b : ℂ) :
    (if exteriorGcd K S I J = d then
      conj (positiveKernel K S D R I * a) * (positiveKernel K S D R J * b) else 0) =
      (if IsCoprime R.val.val d.val.val then (1 : ℂ) else 0) *
        (if IsCoprime (quotient K S d I hI).val.val (quotient K S d J hJ).val.val then
          conj (positiveKernel K S D R (quotient K S d I hI) * a) *
            (positiveKernel K S D R (quotient K S d J hJ) * b) else 0) := by
  have hg := gcd_eq_iff_quotient_coprime K S d I J hI hJ
  by_cases hcop : IsCoprime (quotient K S d I hI).val.val (quotient K S d J hJ).val.val
  · rw [ite_eq_left (hg.mpr hcop), ite_eq_left hcop,
      kernel_divisor_factor K S D hD R d I hI, kernel_divisor_factor K S D hD R d J hJ]
    rw [← common_kernel_mask K S D R d]
    simp only [map_mul]
    ring
  · rw [ite_eq_right (fun h => hcop (hg.mp h)), ite_eq_right hcop, mul_zero]

end CubicSieve.AnalyticGcd
