import HeckeSkeleton.Moments.MOM_INV_STEP.GaussConjugation

/-!
# Evenness supplied by the specified twelfth root

The arithmetic datum already contains a primitive twelfth root. Its
sixth power is -1, and the root is an algebraic integer unit. Thus -1
is an actual sixth power of an S-unit. The literal sextic character
therefore takes value one at -1, including at the unit conductor.
This removes the finite sign in the fifth-digit Gauss conjugation
without adding a calibration or nonvanishing assumption.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SexticEvenness

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.Analysis
open scoped Classical ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

def dodecicIntegerRoot : 𝓞 K :=
  ⟨D.root12, D.primitive12.isIntegral (by decide)⟩

theorem dodecicIntegerRoot_primitive :
    IsPrimitiveRoot (dodecicIntegerRoot K S D) 12 :=
  D.primitive12.of_map_of_injective
    (f := algebraMap (𝓞 K) K) RingOfIntegers.coe_injective

theorem dodecicIntegerRoot_pow_six :
    dodecicIntegerRoot K S D ^ 6 = -1 :=
  (IsPrimitiveRoot.pow (by decide : 0 < (12 : ℕ))
    (dodecicIntegerRoot_primitive K S D) (by decide : 12 = 6 * 2)).eq_neg_one_of_two_right

def dodecicIntegerUnit : (𝓞 K)ˣ :=
  ((dodecicIntegerRoot_primitive K S D).isUnit (by decide)).unit

@[simp] theorem dodecicIntegerUnit_val :
    (dodecicIntegerUnit K S D : 𝓞 K) = dodecicIntegerRoot K S D :=
  IsUnit.unit_spec _

include D in
/-- A witness in the actual S-unit group, obtained by mapping the
specified integral twelfth root. -/
theorem exists_sixth_unit_neg_one :
    ∃ u : S.unit K, (S.unitEquivUnitsInteger K u).val ^ 6 = -1 := by
  let v : (S.integer K)ˣ :=
    Units.map (algebraMap (𝓞 K) (S.integer K)).toMonoidHom (dodecicIntegerUnit K S D)
  refine ⟨(S.unitEquivUnitsInteger K).symm v, ?_⟩
  rw [MulEquiv.apply_symm_apply]
  change (algebraMap (𝓞 K) (S.integer K) (dodecicIntegerUnit K S D : 𝓞 K)) ^ 6 = -1
  rw [dodecicIntegerUnit_val, ← map_pow, dodecicIntegerRoot_pow_six, map_neg, map_one]

/-- No conductor or numerator coprimality hypothesis is required. -/
theorem idealSymbol_neg_one (I : ExteriorIdeal K S) :
    idealSymbol K S D I (-1) = 1 := by
  obtain ⟨u, hu⟩ := exists_sixth_unit_neg_one K S D
  rw [← hu]
  exact sIntegerSexticIdealEvaluation_sixth_power_unit K S D.root6 D.primitive6 D.embedding
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp)) u

theorem idealSymbol_neg (I : ExteriorIdeal K S) (a : S.integer K) :
    idealSymbol K S D I (-a) = idealSymbol K S D I a := by
  change LocalSource.actualRow K S D.root6 D.primitive6 D.embedding I.val.val
    (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp)) (-a) = _
  rw [← neg_one_mul, map_mul]
  change idealSymbol K S D I (-1) * idealSymbol K S D I a = _
  rw [idealSymbol_neg_one, one_mul]

/-- The actual fifth-digit normalized Gauss coefficient equals the
conjugate of the first digit with its original phase and generator. -/
theorem thetaGamma_five_eq_conj (I : ExteriorIdeal K S) :
    thetaGamma K S D I 5 = conj (thetaGamma K S D I 1) := by
  rw [GaussConjugation.thetaGamma_five, idealSymbol_neg_one, one_mul]

/-- The second coefficient cycle now has exactly the original a₀ row;
the sign is discharged from arithmetic data rather than suppressed. -/
theorem second_cycle_five {Λ G : HeckeCharacter K}
    (hcal : ThetaCalibrationInput K S D Λ G)
    (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) :
    (UniqueFactorizationMonoid.moebius I.val.val : ℂ) * thetaGamma K S D I 5 =
      CoefficientCycle.canonicalCoefficient K S D Λ I *
        conj (heckeIdealCoefficient K G I.val) := by
  rw [GaussConjugation.second_cycle_five K S D hcal I hI, idealSymbol_neg_one, one_mul]

end HeckeSkeleton.Moments.MOM_INV_STEP.SexticEvenness

end
