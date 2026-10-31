import ThetaGlobal.ReflectedLocalBounds
import HeckeGeneral.Analysis.MarkedThetaReflection
import HeckeGeneral.Analysis.ThetaPrimeGaussNorm

/-!
# Elementary bounds for the actual reflected arithmetic coefficients

This file imports the project's literal residue characters and finite sums.
It does not import HeckeSkeleton.Theta, nor any KP realization hypothesis.
The local bound is deliberately coarse and uniform in the numerator valuation.
The sharp local Weyl table is not needed for fixed-row absolute convergence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace ThetaGlobal.ReflectedArithmetic

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.ReflectedAbsolute
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

theorem exteriorNorm_ge_one (I : ExteriorIdeal K S) : 1 ≤ exteriorNorm K S I :=
  one_le_idealNorm K I.val

theorem exteriorNorm_pos (I : ExteriorIdeal K S) : 0 < exteriorNorm K S I :=
  idealNorm_pos K I.val

theorem primeNorm_ge_one (p : ExteriorPrime K S) :
    (1 : ℝ) ≤ (p.val.asIdeal.absNorm : ℝ) := by
  exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm p.val).le

theorem norm_real_inv_le_one {r : ℝ} (hr : 1 ≤ r) : ‖(r : ℂ)⁻¹‖ ≤ 1 :=
  ReflectedLocalBounds.norm_real_inv_le_one hr

theorem norm_real_sqrt_inv_le_one {r : ℝ} (hr : 1 ≤ r) :
    ‖(Real.sqrt r : ℂ)⁻¹‖ ≤ 1 :=
  ReflectedLocalBounds.norm_real_sqrt_inv_le_one hr

theorem primeEvaluation_zeroOrUnit (p : ExteriorPrime K S) (a : S.integer K) :
    ZeroOrUnitNorm (primeEvaluation K S D p a) := by
  unfold primeEvaluation sIntegerSexticEvaluation
  by_cases ha : sIntegerSexticResidueMap K S p.val p.property a = 0
  · exact Or.inl (by rw [ha, sexticResidueCharacter_zero])
  · exact Or.inr (sexticResidueCharacter_norm K D.root6 D.primitive6 D.embedding
      p.val (D.away_six p.val p.property) _ ha)

theorem thetaPrimeCharacter_zeroOrUnit (p : ExteriorPrime K S)
    (a : 𝓞 K ⧸ p.val.asIdeal) : ZeroOrUnitNorm (thetaPrimeCharacter K S D p a) := by
  unfold thetaPrimeCharacter
  by_cases ha : a = 0
  · exact Or.inl (by rw [ha, sexticResidueCharacter_zero])
  · exact Or.inr (sexticResidueCharacter_norm K D.root6 D.primitive6 D.embedding
      p.val (D.away_six p.val p.property) a ha)

theorem idealSymbol_zeroOrUnit (I : ExteriorIdeal K S) (a : S.integer K) :
    ZeroOrUnitNorm (idealSymbol K S D I a) := by
  letI : Fintype (AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeDivisors K I.val.val) :=
    (AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeDivisors_finite
      K I.val.val (nonZeroDivisors.coe_ne_zero I.val)).fintype
  unfold idealSymbol sIntegerSexticIdealEvaluation
  apply ZeroOrUnitNorm.finset_prod
  intro p _
  exact (primeEvaluation_zeroOrUnit K S D
    ⟨p.val, I.property p.val p.property⟩ a).pow _

theorem primeCoefficient_zeroOrUnit (θ : HeckeCharacter K)
    (p : HeightOneSpectrum (𝓞 K)) : ZeroOrUnitNorm (primeCoefficient K θ p) := by
  unfold primeCoefficient
  split_ifs
  · exact Or.inr (by simp)
  · exact ZeroOrUnitNorm.zero

theorem heckeIdealCoefficient_zeroOrUnit (θ : HeckeCharacter K) (I : NonzeroIdeal K) :
    ZeroOrUnitNorm (heckeIdealCoefficient K θ I) := by
  unfold heckeIdealCoefficient nonzeroIdealCoefficient idealCoefficient
  split_ifs
  · exact ZeroOrUnitNorm.zero
  apply ZeroOrUnitNorm.multiset_prod
  intro z hz
  obtain ⟨P, _, rfl⟩ := Multiset.mem_map.mp hz
  unfold primeIdealValue
  split_ifs
  · exact primeCoefficient_zeroOrUnit K θ _
  · exact ZeroOrUnitNorm.one

theorem periodValue_zeroOrUnit (d : MarkedDatum K S) (θ : HeckeCharacter K)
    (I : ExteriorIdeal K S) : ZeroOrUnitNorm (periodValue K S D d θ I) :=
  (heckeIdealCoefficient_zeroOrUnit K θ I.val).mul
    (idealSymbol_zeroOrUnit K S D I _)

theorem norm_sphericalDigit_le_one (p : ExteriorPrime K S) (e : ℕ) :
    ‖sphericalDigit K S D p e‖ ≤ 1 := by
  simpa only [sphericalDigit, ReflectedLocalBounds.sphericalCoefficient,
    Complex.ofReal_natCast] using ReflectedLocalBounds.norm_sphericalCoefficient_le_one
      (primeNorm_ge_one K S p) (thetaGamma_exteriorPrime_two_norm K S D p) e

/-- A literal finite upper bound for the digit sum; it involves no division
by a conjectural nonzero local scalar.  In particular it also works when a
digit coefficient happens to vanish. -/
def localWeylBound (p : ExteriorPrime K S) (j : Fin 6) : ℝ := by
  letI : Fintype (𝓞 K ⧸ p.val.asIdeal) := Fintype.ofFinite _
  exact ∑ x : (𝓞 K ⧸ p.val.asIdeal)ˣ,
    ‖digitMask K S D p j x‖ *
      (1 + ‖primePhase K S D p ((x⁻¹ : (𝓞 K ⧸ p.val.asIdeal)ˣ) :
        𝓞 K ⧸ p.val.asIdeal)‖)

theorem localWeylBound_nonneg (p : ExteriorPrime K S) (j : Fin 6) :
    0 ≤ localWeylBound K S D p j := by
  unfold localWeylBound
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (norm_nonneg _) (by positivity))

theorem norm_localWeylScalar_le (p : ExteriorPrime K S) (j : Fin 6) (e : ℕ) :
    ‖localWeylScalar K S D p j e‖ ≤ localWeylBound K S D p j := by
  letI : Fintype (𝓞 K ⧸ p.val.asIdeal) := Fintype.ofFinite _
  simpa only [localWeylScalar, localWeylBound, sphericalDigit,
    ReflectedLocalBounds.finiteWeylCoefficient, ReflectedLocalBounds.finiteWeylBound,
    ReflectedLocalBounds.sphericalCoefficient, Complex.ofReal_natCast] using
    ReflectedLocalBounds.norm_finiteWeylCoefficient_le (primeNorm_ge_one K S p)
      (thetaGamma_exteriorPrime_two_norm K S D p)
      (fun x : (𝓞 K ⧸ p.val.asIdeal)ˣ => digitMask K S D p j x)
      (fun x : (𝓞 K ⧸ p.val.asIdeal)ˣ => thetaPrimeCharacter K S D p x)
      (fun x : (𝓞 K ⧸ p.val.asIdeal)ˣ =>
        primePhase K S D p ((x⁻¹ : (𝓞 K ⧸ p.val.asIdeal)ˣ) : 𝓞 K ⧸ p.val.asIdeal))
      (fun x => thetaPrimeCharacter_zeroOrUnit K S D p x) e

theorem norm_one_sub_prime_inverse_le_one (p : ExteriorPrime K S) :
    ‖1 - (p.val.asIdeal.absNorm : ℂ)⁻¹‖ ≤ 1 := by
  simpa only [Complex.ofReal_natCast] using
    ReflectedLocalBounds.norm_one_sub_real_inverse_le_one (primeNorm_ge_one K S p)

private theorem norm_mul_bound {z w : ℂ} {a b : ℝ}
    (hz : ‖z‖ ≤ a) (hw : ‖w‖ ≤ b) : ‖z * w‖ ≤ a * b := by
  rw [norm_mul]
  exact mul_le_mul hz hw (norm_nonneg _) ((norm_nonneg _).trans hz)

private theorem norm_prod_bound {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (b : ι → ℝ) (h : ∀ i ∈ s, ‖f i‖ ≤ b i) :
    ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, b i := by
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) h

private theorem norm_prod_le_one {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ s, ‖f i‖ ≤ 1) : ‖∏ i ∈ s, f i‖ ≤ 1 := by
  simpa using norm_prod_bound s f (fun _ => 1) h

variable (d : MarkedDatum K S) (i : ReflectionIndex K S d) (θ : HeckeCharacter K)

def frozenArithmeticBound (f : Finset (ExteriorPrime K S)) : ℝ :=
  ∏ p ∈ f, localWeylBound K S D p (rowDigit K S d p)

def rowArithmeticBound : ℝ :=
  ∏ p ∈ exteriorSupport K S d.moving, localWeylBound K S D p ⟨1, by decide⟩

theorem frozenArithmeticBound_nonneg (f : Finset (ExteriorPrime K S)) :
    0 ≤ frozenArithmeticBound K S D d f :=
  Finset.prod_nonneg (fun p _ => localWeylBound_nonneg K S D p _)

theorem rowArithmeticBound_nonneg : 0 ≤ rowArithmeticBound K S D d :=
  Finset.prod_nonneg (fun p _ => localWeylBound_nonneg K S D p _)

theorem frozenUnitFactor_zeroOrUnit (p : ExteriorPrime K S) :
    ZeroOrUnitNorm
      ((primeEvaluation K S D p (S.unitEquivUnitsInteger K (frequencyUnit K S d i)).val *
        primeEvaluation K S D p (D.generator (removePrime K S i.numeratorFrozen p)) *
        primeEvaluation K S D p (D.generator i.n) ^ 3 *
        primeEvaluation K S D p (D.generator (removePrime K S (activeFrozenIdeal K S d i) p)) ^
          (-2 : ℤ)) ^ localWeylExponent (rowDigit K S d p)
            (primeExponents i.numeratorFrozen.val p.val)) :=
  ((((primeEvaluation_zeroOrUnit K S D p _).mul (primeEvaluation_zeroOrUnit K S D p _)).mul
    ((primeEvaluation_zeroOrUnit K S D p _).pow 3)).mul
    ((primeEvaluation_zeroOrUnit K S D p _).zpow (-2))).pow _

theorem norm_frozenOmega_le :
    ‖frozenOmega K S D d i θ‖ ≤ frozenArithmeticBound K S D d i.activeFrozen := by
  have hI := norm_prod_le_one (frozenPrimes K S d \ i.activeFrozen)
    (fun p => (1 : ℂ) - (p.val.asIdeal.absNorm : ℂ)⁻¹)
    (fun p _ => norm_one_sub_prime_inverse_le_one K S p)
  have hunit := norm_mul_bound (norm_mul_bound (norm_mul_bound hI
    ((periodValue_zeroOrUnit K S D d θ i.numeratorFrozen).inv.norm_le))
    ((periodValue_zeroOrUnit K S D d θ i.n).zpow (-3)).norm_le)
    ((periodValue_zeroOrUnit K S D d θ (activeFrozenIdeal K S d i)).pow 2).norm_le
  have hprod : ‖∏ p ∈ i.activeFrozen,
      let e := primeExponents i.numeratorFrozen.val p.val
      localWeylScalar K S D p (rowDigit K S d p) e *
        (primeEvaluation K S D p (S.unitEquivUnitsInteger K (frequencyUnit K S d i)).val *
         primeEvaluation K S D p (D.generator (removePrime K S i.numeratorFrozen p)) *
         primeEvaluation K S D p (D.generator i.n) ^ 3 *
         primeEvaluation K S D p (D.generator (removePrime K S (activeFrozenIdeal K S d i) p)) ^
           (-2 : ℤ)) ^ localWeylExponent (rowDigit K S d p) e‖ ≤
      frozenArithmeticBound K S D d i.activeFrozen := by
    apply norm_prod_bound
    intro p _
    dsimp only
    simpa only [mul_one] using norm_mul_bound
      (norm_localWeylScalar_le K S D p (rowDigit K S d p) _)
      (frozenUnitFactor_zeroOrUnit K S D d i p).norm_le
  simpa only [frozenOmega, one_mul, mul_one] using norm_mul_bound hunit hprod

theorem rowUnitFactor_zeroOrUnit (p : ExteriorPrime K S) :
    ZeroOrUnitNorm
      (primeEvaluation K S D p (S.unitEquivUnitsInteger K (frequencyUnit K S d i)).val *
       primeEvaluation K S D p (D.generator i.numeratorFrozen) *
       primeEvaluation K S D p (D.generator (removePrime K S d.moving p)) ^ (-2 : ℤ) *
       primeEvaluation K S D p (D.generator (activeFrozenIdeal K S d i)) ^ (-2 : ℤ)) :=
  (((primeEvaluation_zeroOrUnit K S D p _).mul (primeEvaluation_zeroOrUnit K S D p _)).mul
    ((primeEvaluation_zeroOrUnit K S D p _).zpow (-2))).mul
    ((primeEvaluation_zeroOrUnit K S D p _).zpow (-2))

theorem norm_reflectedRowFactor_le :
    ‖reflectedRowFactor K S D d i θ‖ ≤ rowArithmeticBound K S D d := by
  have hfirst := ((periodValue_zeroOrUnit K S D d θ d.moving).pow 2).norm_le
  have hprod : ‖∏ p ∈ exteriorSupport K S d.moving,
      localWeylScalar K S D p ⟨1, by decide⟩ 0 *
      (primeEvaluation K S D p (S.unitEquivUnitsInteger K (frequencyUnit K S d i)).val *
       primeEvaluation K S D p (D.generator i.numeratorFrozen) *
       primeEvaluation K S D p (D.generator (removePrime K S d.moving p)) ^ (-2 : ℤ) *
       primeEvaluation K S D p (D.generator (activeFrozenIdeal K S d i)) ^ (-2 : ℤ))‖ ≤
      rowArithmeticBound K S D d := by
    apply norm_prod_bound
    intro p _
    simpa only [mul_one] using norm_mul_bound
      (norm_localWeylScalar_le K S D p ⟨1, by decide⟩ 0)
      (rowUnitFactor_zeroOrUnit K S D d i p).norm_le
  have hlast : ‖∏ p ∈ i.activeFrozen,
      primeEvaluation K S D p (D.generator d.moving) ^
        (-(2 * localWeylExponent (rowDigit K S d p)
          (primeExponents i.numeratorFrozen.val p.val) : ℤ))‖ ≤ 1 := by
    apply norm_prod_le_one
    intro p _
    exact ((primeEvaluation_zeroOrUnit K S D p _).zpow _).norm_le
  simpa only [reflectedRowFactor, one_mul, mul_one] using
    norm_mul_bound (norm_mul_bound hfirst hprod) hlast

theorem reflectedMarkFactor_zeroOrUnit :
    ZeroOrUnitNorm (reflectedMarkFactor K S D d i θ) := by
  unfold reflectedMarkFactor
  apply ZeroOrUnitNorm.mul
  · apply ZeroOrUnitNorm.mul
    · exact (periodValue_zeroOrUnit K S D d θ _).pow 2
    · apply ZeroOrUnitNorm.finset_prod
      intro p _
      apply ZeroOrUnitNorm.mul
      · exact Or.inr (thetaGamma_exteriorPrime_two_norm K S D p)
      · apply ZeroOrUnitNorm.pow
        exact (((primeEvaluation_zeroOrUnit K S D p _).mul
          (primeEvaluation_zeroOrUnit K S D p _)).mul
          ((primeEvaluation_zeroOrUnit K S D p _).zpow (-2))).mul
          ((primeEvaluation_zeroOrUnit K S D p _).zpow (-2))
  · apply ZeroOrUnitNorm.finset_prod
    intro p _
    exact (primeEvaluation_zeroOrUnit K S D p _).zpow _

theorem reflectedColumnFactor_zeroOrUnit :
    ZeroOrUnitNorm (reflectedColumnFactor K S D d i θ) := by
  unfold reflectedColumnFactor
  apply ZeroOrUnitNorm.mul
  · apply ZeroOrUnitNorm.mul
    · exact (periodValue_zeroOrUnit K S D d θ i.c).inv
    · apply ZeroOrUnitNorm.finset_prod
      intro p _
      exact (primeEvaluation_zeroOrUnit K S D p _).pow _
  · apply ZeroOrUnitNorm.finset_prod
    intro p _
    apply ZeroOrUnitNorm.mul
    · exact Or.inr (thetaGamma_exteriorPrime_two_norm K S D p)
    · apply ZeroOrUnitNorm.pow
      exact (((primeEvaluation_zeroOrUnit K S D p _).mul
        (primeEvaluation_zeroOrUnit K S D p _)).mul
        (primeEvaluation_zeroOrUnit K S D p _)).mul
        ((primeEvaluation_zeroOrUnit K S D p _).zpow (-2))

/-- Precisely the arithmetic prefactor in `reflectedTerm`, with its actual
zero extensions and inverse powers. -/
def reflectedCoefficient : ℂ :=
  (∏ p ∈ d.marks \ i.activeMarks, (p.val.asIdeal.absNorm : ℂ)⁻¹) *
  (Real.sqrt (exteriorNorm K S (activeMarkedIdeal K S d i)) : ℂ)⁻¹ *
  frozenOmega K S D d i θ / (exteriorNorm K S i.n : ℂ) *
  reflectedMarkFactor K S D d i θ * reflectedRowFactor K S D d i θ *
  reflectedColumnFactor K S D d i θ / (Real.sqrt (exteriorNorm K S i.c) : ℂ) *
  idealSymbol K S D d.moving (D.generator i.c * D.generator i.n) ^ 3 *
  idealSymbol K S D (activeMarkedIdeal K S d i) (D.generator i.c) ^ (-2 : ℤ)

theorem norm_reflectedCoefficient_le :
    ‖reflectedCoefficient K S D d i θ‖ ≤
      frozenArithmeticBound K S D d i.activeFrozen * rowArithmeticBound K S D d := by
  have hmark := norm_prod_le_one (d.marks \ i.activeMarks)
    (fun p => (p.val.asIdeal.absNorm : ℂ)⁻¹) (by
      intro p _
      simpa only [Complex.ofReal_natCast] using norm_real_inv_le_one (primeNorm_ge_one K S p))
  have hsP := norm_real_sqrt_inv_le_one
    (exteriorNorm_ge_one K S (activeMarkedIdeal K S d i))
  have hn := norm_real_inv_le_one (exteriorNorm_ge_one K S i.n)
  have hc := norm_real_sqrt_inv_le_one (exteriorNorm_ge_one K S i.c)
  have hrowSymbol := ((idealSymbol_zeroOrUnit K S D d.moving
    (D.generator i.c * D.generator i.n)).pow 3).norm_le
  have hmarkSymbol := ((idealSymbol_zeroOrUnit K S D
    (activeMarkedIdeal K S d i) (D.generator i.c)).zpow (-2)).norm_le
  have h := norm_mul_bound (norm_mul_bound
    (norm_mul_bound (norm_mul_bound (norm_mul_bound
      (norm_mul_bound (norm_mul_bound (norm_mul_bound
        (norm_mul_bound hmark hsP) (norm_frozenOmega_le K S D d i θ)) hn)
        (reflectedMarkFactor_zeroOrUnit K S D d i θ).norm_le)
        (norm_reflectedRowFactor_le K S D d i θ))
        (reflectedColumnFactor_zeroOrUnit K S D d i θ).norm_le) hc)
        hrowSymbol) hmarkSymbol
  simpa only [reflectedCoefficient, div_eq_mul_inv, one_mul, mul_one] using h

end ThetaGlobal.ReflectedArithmetic
