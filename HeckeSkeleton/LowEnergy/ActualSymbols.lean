import HeckeGeneral.Analysis.MarkedThetaReflection
import HeckeGeneral.Characters.SIntegerSexticPowerMask
import HeckePort.CenteredMoment.Generator
import HeckePort.Moments.Descent.Hybrid

/-!
# Actual sextic kernels for the hybrid terminal

The symbols in this file are the project's actual `idealSymbol`, evaluated
at its actual allowed generators.  The ordinary-ideal kernels are extended
by zero at nonexterior ideals.  Multiplicativity retains the sixth S-unit
error; common-prime zeros are proved before taking negative powers.

This is an adapter requiring the full project's transitive dependencies.
It supplies the algebraic kernel inputs, not either large-sieve estimate.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowEnergy.ActualSymbols

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckePort.CenteredMomentGenerator HeckePort.Moments
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- The supplied generator contracts to the literal exterior ideal, using
its actual span and the proved saturation of ideals away from S. -/
theorem generator_contraction (A : ExteriorIdeal K S) :
    sIntegerModulusContraction K S (D.generator A) = A.val.val := by
  unfold sIntegerModulusContraction
  rw [D.generator_span]
  exact under_map_coprime_sIntegerIdeal K S A.val.val
    (sexticIdeal_coprime_S K S A.val.val A.property)

/-- Evaluation in the numerator variable really is a monoid hom. -/
def elementSymbolHom (I : ExteriorIdeal K S) : S.integer K →* ℂ where
  toFun := idealSymbol K S D I
  map_one' := sIntegerSexticIdealEvaluation_one K S D.root6 D.primitive6 D.embedding _ _ _ _
  map_mul' := sIntegerSexticIdealEvaluation_mul K S D.root6 D.primitive6 D.embedding _ _ _ _

/-- Allowed generator multiplication is used exactly, including its sixth-unit factor. -/
theorem actualSymbol_mul_right (hD : AllowedGeneratorInput K S D)
    (I J L : ExteriorIdeal K S) :
    idealSymbol K S D I (D.generator (exteriorMul K S J L)) =
      idealSymbol K S D I (D.generator J) * idealSymbol K S D I (D.generator L) := by
  obtain ⟨u, hu⟩ := hD.multiplicative J L
  rw [hu, mul_assoc]
  change sIntegerSexticIdealEvaluation K S D.root6 D.primitive6 D.embedding _ _ _ _
    ((S.unitEquivUnitsInteger K u).val ^ 6 * (D.generator J * D.generator L)) = _
  rw [sIntegerSexticIdealEvaluation_mul_sixth_power_unit,
    sIntegerSexticIdealEvaluation_mul]
  rfl

/-- Sixth powers retain exactly the actual ordinary-ideal coprimality mask. -/
theorem actualSymbol_sixth (I J : ExteriorIdeal K S) :
    idealSymbol K S D I (D.generator J) ^ 6 =
      if IsCoprime I.val.val J.val.val then 1 else 0 := by
  have hp := (map_pow (elementSymbolHom K S D I) (D.generator J) 6).symm
  change idealSymbol K S D I (D.generator J) ^ 6 =
    idealSymbol K S D I (D.generator J ^ 6) at hp
  rw [hp]
  change sIntegerSexticIdealEvaluation K S D.root6 D.primitive6 D.embedding _ _ _ _
    (D.generator J ^ 6) = _
  rw [sIntegerSexticIdealEvaluation_sixth_power_coprime_mask,
    generator_contraction K S D J]

/-- Shared prime factors force the actual symbol to zero before any inverse is used. -/
theorem actualSymbol_eq_zero_of_not_coprime (I J : ExteriorIdeal K S)
    (hIJ : ¬IsCoprime I.val.val J.val.val) :
    idealSymbol K S D I (D.generator J) = 0 := by
  have h := actualSymbol_sixth K S D I J
  rw [if_neg hIJ] at h
  by_contra hn
  exact pow_ne_zero 6 hn h

theorem actualSymbol_norm_eq_one (I J : ExteriorIdeal K S)
    (hIJ : IsCoprime I.val.val J.val.val) :
    ‖idealSymbol K S D I (D.generator J)‖ = 1 := by
  apply norm_sIntegerSexticIdealEvaluation_eq_one K S D.root6 D.primitive6 D.embedding
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp))
  apply (sIntegerSextic_no_badPrime_iff_coprime_contraction K S I.val.val
    (nonZeroDivisors.coe_ne_zero I.val) I.property (D.generator J)).mpr
  rw [generator_contraction K S D J]
  exact hIJ

/-- The ordinary ideal kernel has both nonexterior extensions explicit. -/
def sexticSymbol (I J : Ideal (𝓞 K)) : ℂ :=
  if hI : IsExterior K S I then
    if hJ : IsExterior K S J then
      idealSymbol K S D (toExterior K S I hI) (D.generator (toExterior K S J hJ))
    else 0
  else 0

theorem sexticSymbol_of_exterior (I J : Ideal (𝓞 K))
    (hI : IsExterior K S I) (hJ : IsExterior K S J) :
    sexticSymbol K S D I J =
      idealSymbol K S D (toExterior K S I hI) (D.generator (toExterior K S J hJ)) := by
  simp only [sexticSymbol, dif_pos hI, dif_pos hJ]

theorem sexticSymbol_eq_zero_of_not_left (I J : Ideal (𝓞 K))
    (hI : ¬IsExterior K S I) : sexticSymbol K S D I J = 0 := by
  simp only [sexticSymbol, dif_neg hI]

theorem sexticSymbol_eq_zero_of_not_right (I J : Ideal (𝓞 K))
    (hJ : ¬IsExterior K S J) : sexticSymbol K S D I J = 0 := by
  unfold sexticSymbol
  split_ifs <;> simp_all

/-- Reciprocity is extended by zero on precisely the same ideal domains. -/
theorem sexticSymbol_reciprocity (hD : AllowedGeneratorInput K S D)
    (I J : Ideal (𝓞 K)) : sexticSymbol K S D I J = sexticSymbol K S D J I := by
  by_cases hI : IsExterior K S I
  · by_cases hJ : IsExterior K S J
    · rw [sexticSymbol_of_exterior K S D I J hI hJ,
        sexticSymbol_of_exterior K S D J I hJ hI]
      exact hD.reciprocity _ _
    · rw [sexticSymbol_eq_zero_of_not_right K S D I J hJ,
        sexticSymbol_eq_zero_of_not_left K S D J I hJ]
  · rw [sexticSymbol_eq_zero_of_not_left K S D I J hI,
      sexticSymbol_eq_zero_of_not_right K S D J I hI]

/-- The right multiplication law holds globally, with nonexterior zeros. -/
theorem sexticSymbol_mul_right (hD : AllowedGeneratorInput K S D)
    (I J L : Ideal (𝓞 K)) :
    sexticSymbol K S D I (J * L) = sexticSymbol K S D I J * sexticSymbol K S D I L := by
  by_cases hI : IsExterior K S I
  · by_cases hJ : IsExterior K S J
    · by_cases hL : IsExterior K S L
      · have hJL := (isExterior_mul_iff K S).mpr ⟨hJ, hL⟩
        rw [sexticSymbol_of_exterior K S D I (J * L) hI hJL,
          sexticSymbol_of_exterior K S D I J hI hJ,
          sexticSymbol_of_exterior K S D I L hI hL,
          toExterior_mul K S hJ hL hJL]
        exact actualSymbol_mul_right K S D hD _ _ _
      · rw [sexticSymbol_eq_zero_of_not_right K S D I (J * L)
          (fun h => hL ((isExterior_mul_iff K S).mp h).2),
          sexticSymbol_eq_zero_of_not_right K S D I L hL, mul_zero]
    · rw [sexticSymbol_eq_zero_of_not_right K S D I (J * L)
        (fun h => hJ ((isExterior_mul_iff K S).mp h).1),
        sexticSymbol_eq_zero_of_not_right K S D I J hJ, zero_mul]
  · rw [sexticSymbol_eq_zero_of_not_left K S D I (J * L) hI,
      sexticSymbol_eq_zero_of_not_left K S D I J hI, zero_mul]

theorem sexticSymbol_mul_left (hD : AllowedGeneratorInput K S D)
    (I J L : Ideal (𝓞 K)) :
    sexticSymbol K S D (I * J) L = sexticSymbol K S D I L * sexticSymbol K S D J L := by
  rw [sexticSymbol_reciprocity K S D hD (I * J) L,
    sexticSymbol_mul_right K S D hD L I J,
    sexticSymbol_reciprocity K S D hD L I,
    sexticSymbol_reciprocity K S D hD L J]

theorem sexticSymbol_sixth (I J : Ideal (𝓞 K))
    (hI : IsExterior K S I) (hJ : IsExterior K S J) :
    sexticSymbol K S D I J ^ 6 = if IsCoprime I J then 1 else 0 := by
  rw [sexticSymbol_of_exterior K S D I J hI hJ]
  exact actualSymbol_sixth K S D _ _

theorem sexticSymbol_eq_zero_of_not_coprime (I J : Ideal (𝓞 K))
    (hI : IsExterior K S I) (hJ : IsExterior K S J) (hIJ : ¬IsCoprime I J) :
    sexticSymbol K S D I J = 0 := by
  rw [sexticSymbol_of_exterior K S D I J hI hJ]
  exact actualSymbol_eq_zero_of_not_coprime K S D _ _ hIJ

/-- This stronger norm dichotomy justifies negative powers of the symbol. -/
theorem sexticSymbol_norm_zero_or_one (I J : Ideal (𝓞 K)) :
    ‖sexticSymbol K S D I J‖ = 0 ∨ ‖sexticSymbol K S D I J‖ = 1 := by
  by_cases hI : IsExterior K S I
  · by_cases hJ : IsExterior K S J
    · by_cases hIJ : IsCoprime I J
      · right
        rw [sexticSymbol_of_exterior K S D I J hI hJ]
        exact actualSymbol_norm_eq_one K S D _ _ hIJ
      · left
        rw [sexticSymbol_eq_zero_of_not_coprime K S D I J hI hJ hIJ, norm_zero]
    · left
      rw [sexticSymbol_eq_zero_of_not_right K S D I J hJ, norm_zero]
  · left
    rw [sexticSymbol_eq_zero_of_not_left K S D I J hI, norm_zero]

def quadraticKernel (I J : Ideal (𝓞 K)) : ℂ := sexticSymbol K S D I J ^ 3

def cubicKernel (I J : Ideal (𝓞 K)) : ℂ := sexticSymbol K S D I J ^ (-2 : ℤ)

theorem quadraticKernel_mul_right (hD : AllowedGeneratorInput K S D)
    (I J L : Ideal (𝓞 K)) :
    quadraticKernel K S D I (J * L) =
      quadraticKernel K S D I J * quadraticKernel K S D I L := by
  simp only [quadraticKernel, sexticSymbol_mul_right K S D hD, mul_pow]

/-- The exact square mask needed by the completed quadratic reduction. -/
theorem quadraticKernel_square (hD : AllowedGeneratorInput K S D)
    (I J : Ideal (𝓞 K)) (hI : IsExterior K S I) (hJ : IsExterior K S J) :
    quadraticKernel K S D I (J ^ 2) = if IsCoprime I J then 1 else 0 := by
  calc
    _ = sexticSymbol K S D I J ^ 6 := by
      rw [quadraticKernel, pow_two J, sexticSymbol_mul_right K S D hD]
      ring
    _ = _ := sexticSymbol_sixth K S D I J hI hJ

/-- Exact input for `HeckePort.Moments.CubicKernelAxioms`. -/
theorem cubicKernel_axioms (hD : AllowedGeneratorInput K S D) :
    CubicKernelAxioms (IsExterior K S) (cubicKernel K S D) where
  mul_left := by
    intro I J L
    simp only [cubicKernel, sexticSymbol_mul_left K S D hD, mul_zpow]
  mul_right := by
    intro I J L _hI
    simp only [cubicKernel, sexticSymbol_mul_right K S D hD, mul_zpow]
  norm_le_one := by
    intro I J
    rw [cubicKernel, norm_zpow]
    rcases sexticSymbol_norm_zero_or_one K S D I J with h | h <;> simp [h]
  eq_zero_of_not_coprime := by
    intro I J hI hJ hIJ
    rw [cubicKernel, sexticSymbol_eq_zero_of_not_coprime K S D I J hI hJ hIJ]
    norm_num

/-- Exact input for the quadratic-row algebra, for any row-admissibility predicate. -/
theorem quadraticKernel_axioms (hD : AllowedGeneratorInput K S D)
    (Adm : Ideal (𝓞 K) → Prop) : QuadraticRowAxioms Adm (quadraticKernel K S D) where
  mul := by
    intro I J L _hIJ
    simp only [quadraticKernel, sexticSymbol_mul_left K S D hD, mul_pow]
  norm_le_one := by
    intro I J
    rw [quadraticKernel, norm_pow]
    rcases sexticSymbol_norm_zero_or_one K S D I J with h | h <;> simp [h]

/-- The actual square-mask identity for `n=c m`, `b=c h t²`, with all zeros. -/
theorem original_quadratic_square_mask (hD : AllowedGeneratorInput K S D)
    (k c m h t : Ideal (𝓞 K))
    (hk : IsExterior K S k) (hc : IsExterior K S c) (ht : IsExterior K S t) :
    quadraticKernel K S D k ((c * m) * ((c * h) * t ^ 2)) =
      (if IsCoprime k (c * t) then 1 else 0) * quadraticKernel K S D k (m * h) := by
  have he : (c * m) * ((c * h) * t ^ 2) = (c * t) ^ 2 * (m * h) := by ring
  rw [he, quadraticKernel_mul_right K S D hD,
    quadraticKernel_square K S D hD k (c * t) hk ((isExterior_mul_iff K S).mpr ⟨hc, ht⟩)]

#print axioms HeckeSkeleton.LowEnergy.ActualSymbols.cubicKernel_axioms
#print axioms HeckeSkeleton.LowEnergy.ActualSymbols.quadraticKernel_axioms
#print axioms HeckeSkeleton.LowEnergy.ActualSymbols.original_quadratic_square_mask

end HeckeSkeleton.LowEnergy.ActualSymbols
