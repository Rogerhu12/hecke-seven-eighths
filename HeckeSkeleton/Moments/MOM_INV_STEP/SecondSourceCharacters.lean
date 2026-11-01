import HeckeSkeleton.Moments.MOM_INV_STEP.SecondSourceGauss
import HeckeSkeleton.Moments.MOM_INV_STEP.MaskDivisorTransport

/-!
# The actual second Fourier row and its retained common zeros

The fresh inverse pair's primitive character is computed on every
numerator as χ_z₁ times conjugate χ_z₂. Its arbitrary divisor Fourier
coefficient therefore retains exactly the two divisor characters and
the two opposite frequency characters.

The original fourth-power label and retained first divisor are split on
the actual common/residual factorization. Their common factor is exactly
two coprimality zeros, including the original label zero. This is used
before positive enlargement and already forces the second divisor to
remain coprime to the old label.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondSourceCharacters

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep.FixedTripleFibers
open FirstInversePoisson ConductorMasks PrimitivePoissonSource PrimitiveFourier
  PrimitivePacketCRT CanonicalGroupedGauss SecondSourceGauss
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "e" => unitIdeal K S

theorem idealSymbol_fifth (n : Ext) (a : OS) :
    idealSymbol K Sset D n a ^ 5 = star (idealSymbol K Sset D n a) := by
  have h := LocalSource.actualRow_zero_or_one K Sset D.root6 D.primitive6 D.embedding
    n.val.val (nonZeroDivisors.coe_ne_zero n.val) n.property
    (fun p hp => D.away_six p (n.property p hp)) a
  change idealSymbol K Sset D n a ^ 6 = 0 ∨ idealSymbol K Sset D n a ^ 6 = 1 at h
  rcases h with hzero | hone
  · have hz := (pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp hzero
    simp only [hz, zero_pow (by decide : (5 : ℕ) ≠ 0), star_zero]
  · have hn : ‖idealSymbol K Sset D n a‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one hone (by decide)
    have hm : idealSymbol K Sset D n a ^ 5 * idealSymbol K Sset D n a = 1 := by
      simpa only [← pow_succ] using hone
    rw [Complex.star_def]
    exact (eq_inv_of_mul_eq_one_left hm).trans (Complex.inv_eq_conj hn)

theorem left_character (x₁ x₂ : Ext) (a : OS) :
    primitiveCoefficient K S D (leftBlock K S D x₁ x₂ e e)
        (pairExponent K S x₁ x₂ e e) (Ideal.Quotient.mk _ a) =
      idealSymbol K Sset D (ActualInverseFactors.residual K Sset x₁ x₂) a := by
  rw [← leftIdeal_eq_residual K S D x₁ x₂]
  have ht : ∀ p ∈ activeSupport (leftBlock K S D x₁ x₂ e e).support
      (pairExponent K S x₁ x₂ e e), (pairExponent K S x₁ x₂ e e p).val = 1 := by
    intro p hp
    rw [left_digit K S D x₁ x₂ e e p (Finset.mem_filter.mp hp).1]
    rfl
  simpa only [pow_one, leftIdeal] using primitiveCoefficient_uniform K S D
    (leftBlock K S D x₁ x₂ e e) (pairExponent K S x₁ x₂ e e) 1 ht a

theorem right_character (x₁ x₂ : Ext) (a : OS) :
    primitiveCoefficient K S D (rightBlock K S D x₁ x₂ e e)
        (pairExponent K S x₁ x₂ e e) (Ideal.Quotient.mk _ a) =
      star (idealSymbol K Sset D (ActualInverseFactors.residual K Sset x₂ x₁) a) := by
  rw [← idealSymbol_fifth, ← rightIdeal_eq_residual K S D x₁ x₂]
  apply primitiveCoefficient_uniform K S D _ _ 5 _ a
  intro p hp
  rw [right_digit K S D x₁ x₂ e e p (Finset.mem_filter.mp hp).1]
  rfl

/-- The true second primitive character, at every numerator including
bad residues and zero. -/
theorem primitive_character (x₁ x₂ : Ext) (a : OS) :
    primitiveCoefficient K S D (pairSupport K S D x₁ x₂ e e)
        (pairExponent K S x₁ x₂ e e) (Ideal.Quotient.mk _ a) =
      idealSymbol K Sset D (ActualInverseFactors.residual K Sset x₁ x₂) a *
        star (idealSymbol K Sset D (ActualInverseFactors.residual K Sset x₂ x₁) a) := by
  have ha : activeSupport (pairSupport K S D x₁ x₂ e e).support
      (pairExponent K S x₁ x₂ e e) =
      (leftBlock K S D x₁ x₂ e e).support ∪ (rightBlock K S D x₁ x₂ e e).support := by
    rw [source_active_partition, cube_support_empty, Finset.union_empty]
  calc
    _ = primitiveCoefficient K S D (leftBlock K S D x₁ x₂ e e)
          (pairExponent K S x₁ x₂ e e) (Ideal.Quotient.mk _ a) *
        primitiveCoefficient K S D (rightBlock K S D x₁ x₂ e e)
          (pairExponent K S x₁ x₂ e e) (Ideal.Quotient.mk _ a) := by
      rw [primitiveCoefficient_mk_eq_product, primitiveCoefficient_mk_eq_product,
        primitiveCoefficient_mk_eq_product, ha, left_active, right_active,
        Finset.prod_union (left_right_disjoint K S D x₁ x₂ e e)]
    _ = _ := by rw [left_character, right_character]

/-- The actual second divisor Fourier coefficient, with all divisor
and frequency phases and the genuine Gauss factor retained. -/
theorem divisor_fourier_split (x₁ x₂ : Ext) (d k : OS) :
    sIntegerPeriodicDivisorFourier K Sset D.different_outside
      (primitiveModulus K S D (pairSupport K S D x₁ x₂ e e) (pairExponent K S x₁ x₂ e e))
      (primitiveModulus_ne_zero K S D (pairSupport K S D x₁ x₂ e e) (pairExponent K S x₁ x₂ e e))
      (primitiveCoefficient K S D (pairSupport K S D x₁ x₂ e e) (pairExponent K S x₁ x₂ e e))
      d (Ideal.Quotient.mk _ k) =
      (idealSymbol K Sset D (ActualInverseFactors.residual K Sset x₁ x₂) d *
        star (idealSymbol K Sset D (ActualInverseFactors.residual K Sset x₂ x₁) d)) *
      (star (idealSymbol K Sset D (ActualInverseFactors.residual K Sset x₁ x₂) k) *
        idealSymbol K Sset D (ActualInverseFactors.residual K Sset x₂ x₁) k) *
      primitiveGauss K S D (pairSupport K S D x₁ x₂ e e) (pairExponent K S x₁ x₂ e e) := by
  rw [PrimitiveFourier.divisor_fourier, primitive_character, primitive_character,
    star_mul, star_star]
  ring

def decoration (n j : Ext) (d : OS) : ℂ :=
  idealSymbol K Sset D n d * idealSymbol K Sset D n (D.generator j) ^ 4

def commonZero (g j : Ext) (d : OS) : ℂ :=
  idealCoprimeMask (sIntegerModulusContraction K Sset d) g.val.val *
    idealCoprimeMask j.val.val g.val.val

theorem symbol_self_pair (n : Ext) (a : OS) :
    star (idealSymbol K Sset D n a) * idealSymbol K Sset D n a =
      idealCoprimeMask (sIntegerModulusContraction K Sset a) n.val.val := by
  let χ := LocalSource.actualRow K Sset D.root6 D.primitive6 D.embedding
    n.val.val (nonZeroDivisors.coe_ne_zero n.val) n.property
    (fun p hp => D.away_six p (n.property p hp))
  have hχ : ∀ a, χ a ^ 6 = 0 ∨ χ a ^ 6 = 1 :=
    LocalSource.actualRow_zero_or_one K Sset D.root6 D.primitive6 D.embedding
      n.val.val (nonZeroDivisors.coe_ne_zero n.val) n.property
      (fun p hp => D.away_six p (n.property p hp))
  exact (mul_comm _ _).trans ((CubeAlgebra.row_self_pair χ hχ a).trans
    (LocalSource.actualRow_mask K Sset D.root6 D.primitive6 D.embedding
      n.val.val (nonZeroDivisors.coe_ne_zero n.val) n.property
      (fun p hp => D.away_six p (n.property p hp)) a))

theorem decoration_self_pair (g j : Ext) (d : OS) :
    star (decoration K S D g j d) * decoration K S D g j d = commonZero K S g j d := by
  have hj : sIntegerModulusContraction K Sset (D.generator j) = j.val.val := by
    simpa only [CanonicalIdealRow.generator_ofExterior, CanonicalIdealRow.ofExterior_val] using
      CanonicalIdealRow.generator_contraction K S D (CanonicalIdealRow.ofExterior K S j)
  unfold decoration
  calc
    _ = (star (idealSymbol K Sset D g d) * idealSymbol K Sset D g d) *
        (star (idealSymbol K Sset D g (D.generator j)) *
          idealSymbol K Sset D g (D.generator j)) ^ 4 := by
      rw [star_mul, star_pow]
      ring
    _ = _ := by
      rw [symbol_self_pair, symbol_self_pair, hj]
      unfold commonZero idealCoprimeMask
      split_ifs <;> norm_num

theorem decoration_mul (g u j : Ext) (d : OS) :
    decoration K S D (exteriorMul K Sset g u) j d =
      decoration K S D g j d * decoration K S D u j d := by
  simp only [decoration, ThetaGaussCRT.idealSymbol_mul_denominator, mul_pow]
  ring

/-- The original decorated source retains its computed common zero
before the residual label and divisor characters are reorganized. -/
theorem actual_pair_decorations (x₁ x₂ j : Ext) (d : OS)
    (hx₁ : Squarefree x₁.val.val) (hx₂ : Squarefree x₂.val.val) :
    star (decoration K S D x₁ j d) * decoration K S D x₂ j d =
      commonZero K S (ActualInverseFactors.common K Sset x₁ x₂) j d *
      star (decoration K S D (ActualInverseFactors.residual K Sset x₁ x₂) j d) *
        decoration K S D (ActualInverseFactors.residual K Sset x₂ x₁) j d := by
  have h₁ : decoration K S D x₁ j d =
      decoration K S D (ActualInverseFactors.common K Sset x₁ x₂) j d *
        decoration K S D (ActualInverseFactors.residual K Sset x₁ x₂) j d := by
    exact (congrArg (fun n => decoration K S D n j d)
      (ActualInverseFactors.common_mul_residual K Sset x₁ x₂ hx₁)).symm.trans
        (decoration_mul K S D _ _ j d)
  have h₂ : decoration K S D x₂ j d =
      decoration K S D (ActualInverseFactors.common K Sset x₁ x₂) j d *
        decoration K S D (ActualInverseFactors.residual K Sset x₂ x₁) j d := by
    have h := (congrArg (fun n => decoration K S D n j d)
      (ActualInverseFactors.common_mul_residual K Sset x₂ x₁ hx₂)).symm.trans
        (decoration_mul K S D _ _ j d)
    simpa only [ActualInverseFactors.common_comm K Sset x₂ x₁] using h
  rw [h₁, h₂, star_mul]
  calc
    _ = (star (decoration K S D (ActualInverseFactors.common K Sset x₁ x₂) j d) *
          decoration K S D (ActualInverseFactors.common K Sset x₁ x₂) j d) *
        star (decoration K S D (ActualInverseFactors.residual K Sset x₁ x₂) j d) *
          decoration K S D (ActualInverseFactors.residual K Sset x₂ x₁) j d := by ring
    _ = _ := by rw [decoration_self_pair]

theorem commonZero_coprime (g j : Ext) (d : OS) (hlive : commonZero K S g j d ≠ 0) :
    IsCoprime g.val.val j.val.val := by
  exact (idealCoprimeMask_ne_zero _ _).mp ((mul_ne_zero_iff.mp hlive).2)

/-- A genuine second common-factor divisor preserves squarefreeness of
the next label, as a consequence of the retained original source zero. -/
theorem second_label_squarefree (x₁ x₂ j : Ext) (d : OS) (hj : Squarefree j.val.val)
    (d₂ : Ideal (𝓞 K)) (hd₂ : d₂ ∣ (ActualInverseFactors.common K Sset x₁ x₂).val.val)
    (hlive : commonZero K S (ActualInverseFactors.common K Sset x₁ x₂) j d ≠ 0) :
    Squarefree (j.val.val * d₂) := by
  have hc := (commonZero_coprime K S
    (ActualInverseFactors.common K Sset x₁ x₂) j d hlive).of_isCoprime_of_dvd_left hd₂
  exact squarefree_mul_iff.mpr ⟨hc.symm.isRelPrime, hj,
    (ActualInverseFactors.common_squarefree K Sset x₁ x₂).squarefree_of_dvd hd₂⟩

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondSourceCharacters

end
