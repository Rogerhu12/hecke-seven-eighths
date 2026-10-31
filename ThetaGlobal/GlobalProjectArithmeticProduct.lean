import ThetaGlobal.GlobalProjectPhases
import ThetaGlobal.GlobalIndexSupport
import HeckeGeneral.Analysis.PrimeCalibrationIdealAssembly

/-!
# Finite ideal products in the literal marked coefficient

The norm and symbol products use the actual ideal prime exponents.
The symmetric local interactions are reduced by the proved sextic
reciprocity identity, with all zero extensions retained. In particular
the mark--column factor has exponent -2 and the moving row factor has
exponent 3 exactly as in `reflectedCoefficient`.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GlobalProjectArithmeticProduct

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
  (D : ThetaArithmeticData K S)

theorem prod_exteriorSupport_val (I : ExteriorIdeal K S)
    {M : Type*} [CommMonoid M] (f : HeightOneSpectrum (𝓞 K) → M) :
    (∏ p ∈ exteriorSupport K S I, f p.val) = ∏ p ∈ (primeExponents I.val).support, f p := by
  unfold exteriorSupport
  rw [Finset.prod_image]
  · exact Finset.prod_attach _ _
  · intro p _ q _ h
    apply Subtype.ext
    exact congrArg (fun r : ExteriorPrime K S => r.val) h

theorem squarefree_exponent (I : ExteriorIdeal K S) (hI : Squarefree I.val.val)
    (p : ExteriorPrime K S) :
    primeExponents I.val p.val = if p ∈ exteriorSupport K S I then 1 else 0 := by
  have hle : primeExponents I.val p.val ≤ 1 :=
    Multiset.nodup_iff_count_le_one.mp
      ((squarefree_iff_nodup_normalizedFactors (nonZeroDivisors.coe_ne_zero I.val)).mp hI)
      p.val.asIdeal
  by_cases hp : p ∈ exteriorSupport K S I
  · rw [if_pos hp]
    have hn := (GlobalIndexSupport.mem_exteriorSupport K S I p).mp hp
    omega
  · rw [if_neg hp]
    exact not_ne_iff.mp (fun h => hp ((GlobalIndexSupport.mem_exteriorSupport K S I p).mpr h))

theorem exteriorNorm_product (I : ExteriorIdeal K S) :
    exteriorNorm K S I =
      ∏ p ∈ exteriorSupport K S I, (p.val.asIdeal.absNorm : ℝ) ^ primeExponents I.val p.val := by
  rw [prod_exteriorSupport_val K S I
    (fun p : HeightOneSpectrum (𝓞 K) => (p.asIdeal.absNorm : ℝ) ^ primeExponents I.val p)]
  have hI := congrArg (fun J : NonzeroIdeal K => (J.val.absNorm : ℝ))
    (idealOfPrimeExponents_primeExponents I.val)
  simpa only [exteriorNorm, idealOfPrimeExponents_val, Finsupp.prod, map_prod,
    map_pow, Nat.cast_prod, Nat.cast_pow] using hI.symm

theorem exteriorNorm_squarefree (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) :
    exteriorNorm K S I = ∏ p ∈ exteriorSupport K S I, (p.val.asIdeal.absNorm : ℝ) := by
  rw [exteriorNorm_product]
  apply Finset.prod_congr rfl
  intro p hp
  rw [squarefree_exponent K S I hI p, if_pos hp, pow_one]

theorem sqrt_exteriorNorm_squarefree (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) :
    (Real.sqrt (exteriorNorm K S I) : ℂ) =
      ∏ p ∈ exteriorSupport K S I, (Real.sqrt (p.val.asIdeal.absNorm : ℝ) : ℂ) := by
  rw [exteriorNorm_squarefree K S I hI,
    Real.sqrt_prod _ (fun p _ => Nat.cast_nonneg _), Complex.ofReal_prod]

def divisorEquiv (I : ExteriorIdeal K S) :
    {p : ExteriorPrime K S // p ∈ exteriorSupport K S I} ≃ idealPrimeDivisors K I.val.val where
  toFun p := ⟨p.val.val, (mem_idealPrimeSupport_iff K I.val p.val.val).mp
    (Finsupp.mem_support_iff.mpr
      ((GlobalIndexSupport.mem_exteriorSupport K S I p.val).mp p.property))⟩
  invFun p := ⟨⟨p.val, I.property p.val p.property⟩,
    (GlobalIndexSupport.mem_exteriorSupport K S I _).mpr
      (Finsupp.mem_support_iff.mp ((mem_idealPrimeSupport_iff K I.val p.val).mpr p.property))⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem idealSymbol_product (I : ExteriorIdeal K S) (a : S.integer K) :
    idealSymbol K S D I a =
      ∏ p ∈ exteriorSupport K S I, primeEvaluation K S D p a ^ primeExponents I.val p.val := by
  letI : Fintype (idealPrimeDivisors K I.val.val) :=
    (idealPrimeDivisors_finite K I.val.val (nonZeroDivisors.coe_ne_zero I.val)).fintype
  calc
    _ = ∏ p : {p : ExteriorPrime K S // p ∈ exteriorSupport K S I},
        primeEvaluation K S D p.val a ^ primeExponents I.val p.val.val := by
      unfold idealSymbol sIntegerSexticIdealEvaluation
      symm
      apply Fintype.prod_equiv (divisorEquiv K S I)
      intro p
      rw [PrimeCalibrationDraft.idealPrimeMultiplicity_eq_primeExponents]
      rfl
    _ = _ := Finset.prod_coe_sort (exteriorSupport K S I)
      (fun p => primeEvaluation K S D p a ^ primeExponents I.val p.val)

theorem idealSymbol_squarefree_product (I : ExteriorIdeal K S)
    (hI : Squarefree I.val.val) (a : S.integer K) :
    idealSymbol K S D I a = ∏ p ∈ exteriorSupport K S I, primeEvaluation K S D p a := by
  rw [idealSymbol_product]
  apply Finset.prod_congr rfl
  intro p hp
  rw [squarefree_exponent K S I hI p, if_pos hp, pow_one]

theorem primeSetIdeal_support (T : Finset (ExteriorPrime K S)) :
    exteriorSupport K S (primeSetIdeal K S T) = T := by
  ext p
  rw [GlobalIndexSupport.mem_exteriorSupport, GlobalIndexSupport.exponent_primeSetIdeal]
  by_cases hp : p ∈ T <;> simp [hp]

theorem primeSetIdeal_squarefree (T : Finset (ExteriorPrime K S)) :
    Squarefree (primeSetIdeal K S T).val.val :=
  IdealMobiusMask.squarefree_primeProduct (T.image Subtype.val)

theorem idealSymbol_primeSet_product (T : Finset (ExteriorPrime K S)) (a : S.integer K) :
    idealSymbol K S D (primeSetIdeal K S T) a = ∏ p ∈ T, primeEvaluation K S D p a := by
  rw [idealSymbol_squarefree_product K S D _ (primeSetIdeal_squarefree K S T),
    primeSetIdeal_support]

variable (d : MarkedDatum K S) (i : ReflectionIndex K S d) (θ : HeckeCharacter K)

theorem moving_coprime_activeMarks :
    IsCoprime d.moving.val.val (activeMarkedIdeal K S d i).val.val := by
  apply GlobalIndexSupport.coprime_of_exponent_zeros K S
  intro p hp
  have hm : p ∈ i.activeMarks := by
    by_contra hm
    exact hp (by rw [activeMarkedIdeal, GlobalIndexSupport.exponent_primeSetIdeal, if_neg hm])
  by_contra he
  exact (d.marks_coprime p (i.marks_subset hm)).1
    ((mem_idealPrimeSupport_iff K d.moving.val p.val).mp (Finsupp.mem_support_iff.mpr he))

theorem n_coprime_activeMarks :
    IsCoprime i.n.val.val (activeMarkedIdeal K S d i).val.val := by
  apply GlobalIndexSupport.coprime_of_exponent_zeros K S
  intro p hp
  have hd : p.val.asIdeal ∣ (activeMarkedIdeal K S d i).val.val :=
    (mem_idealPrimeSupport_iff K _ p.val).mp (Finsupp.mem_support_iff.mpr hp)
  apply GlobalIndexSupport.exponent_zero_of_coprime K S i.n
    (exteriorMul K S (activeFrozenIdeal K S d i) (activeMarkedIdeal K S d i))
    i.n_coprime p
  exact dvd_mul_of_dvd_right hd _

/-- The coefficient before reciprocity. Its five cross interactions are
the ones produced by multiplication of the actual local unit phases. -/
def symmetricCoefficient : ℂ :=
  (∏ p ∈ d.marks \ i.activeMarks, (p.val.asIdeal.absNorm : ℂ)⁻¹) *
  (Real.sqrt (exteriorNorm K S (activeMarkedIdeal K S d i)) : ℂ)⁻¹ *
  frozenOmega K S D d i θ / (exteriorNorm K S i.n : ℂ) *
  reflectedMarkFactor K S D d i θ * reflectedRowFactor K S D d i θ *
  reflectedColumnFactor K S D d i θ / (Real.sqrt (exteriorNorm K S i.c) : ℂ) *
  ((idealSymbol K S D d.moving (D.generator i.c) *
      idealSymbol K S D i.c (D.generator d.moving) ^ (-4 : ℤ)) *
    (idealSymbol K S D d.moving (D.generator (activeMarkedIdeal K S d i)) ^ (-2 : ℤ) *
      idealSymbol K S D (activeMarkedIdeal K S d i) (D.generator d.moving) ^ (-4 : ℤ)) *
    (idealSymbol K S D (activeMarkedIdeal K S d i) (D.generator i.c) ^ 2 *
      idealSymbol K S D i.c (D.generator (activeMarkedIdeal K S d i)) ^ (-4 : ℤ)) *
    idealSymbol K S D d.moving (D.generator i.n) ^ 3 *
    idealSymbol K S D (activeMarkedIdeal K S d i) (D.generator i.n) ^ 6)

/-- This identity holds on the full enlarged index, including all zero
coefficients. No cancellation of a residue symbol is performed. -/
theorem symmetricCoefficient_eq (hA : AllowedGeneratorInput K S D) :
    symmetricCoefficient K S D d i θ = ReflectedArithmetic.reflectedCoefficient K S D d i θ := by
  rw [symmetricCoefficient,
    GlobalProjectPhases.actual_moving_couplings K S D hA,
    if_pos (moving_coprime_activeMarks K S d i),
    if_pos (n_coprime_activeMarks K S d i).symm]
  simp only [mul_one, ReflectedArithmetic.reflectedCoefficient, mul_assoc]

end ThetaGlobal.GlobalProjectArithmeticProduct
