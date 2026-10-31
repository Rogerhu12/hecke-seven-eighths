import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PhaseDictionary
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstKernel
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ArithmeticPrimePool

/-!
# The first residual Gauss columns are the actual amplifier columns

The common active character stays in the row weight.  Each residual
column uses the unit first modulus, so the arithmetic finite coefficient
is its ordinary complete S-local Gauss sum.  The exact ideal norm is
moved into the original whole coefficient before the one-pool operation.
This is an equality at every frequency, including nonunits and zero.

Allowed generator replacement is also transported through the same
dictionary.  It changes neither the whole coefficient nor the frequency;
its input is the existing primitive arithmetic recipe from MOM_BASE.
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}

set_option maxHeartbeats 1600000 in
/-- The actual arithmetic coefficient with unit first modulus is exactly
the complete Gauss column of the genuine orbital phase. -/
theorem actual_unit_coefficient_eq_gauss
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (C : A.GeneralArithmeticContext σ η htrace)
    (I : A.Exterior) (a h : A.R) (ha : A.Generates I a) :
    MaskedQuotientCRT.coefficient C (unitExterior A) I 1 a h
        (unitExterior_generates A) ha =
      actualSIntegerGauss K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hS a ha.1
        (generatedIdealCharacter (σ := σ) I a ha) h := by
  letI : Finite (FiniteTransform.Residue A.R.toSubring (1 : A.R)) := by
    change Finite (A.R ⧸ Ideal.span {(1 : A.R)})
    rw [Ideal.span_singleton_one]
    infer_instance
  letI : Finite (FiniteTransform.Residue A.R.toSubring a) := by
    change Finite (A.R ⧸ Ideal.span {a})
    rw [ha.2]
    exact A.exteriorResidue_finite I
  letI := Fintype.ofFinite (FiniteTransform.Residue A.R.toSubring (1 : A.R))
  letI := Fintype.ofFinite (FiniteTransform.Residue A.R.toSubring a)
  unfold MaskedQuotientCRT.coefficient
  rw [finiteCoefficient_unit_modulus A.R.toSubring a h ha.1]
  · exact (completeResidueGauss_eq_finiteGauss K A hS a ha.1
      (generatedIdealCharacter (σ := σ) I a ha) h).symm
  · intro r
    change (A.fieldTraceCharacter (r : K) : ℂ) = 1
    rw [A.eS_integer htrace r, Circle.coe_one]

/-- The central norm has not disappeared: it is exactly the denominator
of the actual amplifier column. -/
theorem actual_unit_column_eq_gauss_div_norm
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (C : A.GeneralArithmeticContext σ η htrace)
    (I : A.Exterior) (a h : A.R) (ha : A.Generates I a) :
    actualFiniteColumn C (unitExterior A) I 1 a (unitExterior_generates A) ha h =
      actualSIntegerGauss K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hS a ha.1
        (generatedIdealCharacter (σ := σ) I a ha) h / (A.exteriorNorm I : ℂ) := by
  unfold actualFiniteColumn
  rw [actual_unit_coefficient_eq_gauss hS C I a h ha]

/-- The entire original polynomial is transferred to the pool, without
splitting any centered difference or live-slot coefficient. -/
theorem whole_gauss_eq_actual_unit_columns {ι : Type*}
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (C : A.GeneralArithmeticContext σ η htrace)
    (columns : Finset ι) (c : ι → ℂ)
    (I : ι → A.Exterior) (a : ι → A.R) (ha : ∀ i, A.Generates (I i) (a i)) (h : A.R) :
    wholePolynomial columns c
        (fun i h => actualSIntegerGauss K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hS (a i) (ha i).1
          (generatedIdealCharacter (σ := σ) (I i) (a i) (ha i)) h) h =
      wholePolynomial columns (fun i => c i * (A.exteriorNorm (I i) : ℂ))
        (fun i h => actualFiniteColumn C (unitExterior A) (I i) 1 (a i)
          (unitExterior_generates A) (ha i) h) h := by
  unfold wholePolynomial
  apply Finset.sum_congr rfl
  intro i hi
  change c i * actualSIntegerGauss K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hS
      (a i) (ha i).1 (generatedIdealCharacter (σ := σ) (I i) (a i) (ha i)) h =
    (c i * (A.exteriorNorm (I i) : ℂ)) *
      actualFiniteColumn C (unitExterior A) (I i) 1 (a i)
        (unitExterior_generates A) (ha i) h
  rw [actual_unit_column_eq_gauss_div_norm hS C (I i) (a i) h (ha i)]
  have hn : (A.exteriorNorm (I i) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (A.exteriorNorm_pos (I i)))
  field_simp

/-- Allowed presentations of one residual ideal give exactly the same
actual Gauss column.  This uses the existing arithmetic recipe, rather
than identifying two independently selected generators. -/
theorem actual_gauss_generator_replacement
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (C : A.GeneralArithmeticContext σ η htrace)
    (D : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ htrace C.correction.B D)
    (I : A.Exterior) (a b h : A.R)
    (ha : A.Generates I a) (hb : A.Generates I b)
    (haa : A.IsAllowed C.correction.B (Units.mk0 (a : K) (by exact_mod_cast ha.1)))
    (hbb : A.IsAllowed C.correction.B (Units.mk0 (b : K) (by exact_mod_cast hb.1))) :
    actualSIntegerGauss K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hS b hb.1
        (generatedIdealCharacter (σ := σ) I b hb) h =
      actualSIntegerGauss K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hS a ha.1
        (generatedIdealCharacter (σ := σ) I a ha) h := by
  have he := actual_gauss_column_generator_replacement C D hD I a b h ha hb haa hbb
  simpa only [actual_unit_coefficient_eq_gauss hS C] using he

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_unit_coefficient_eq_gauss
#print axioms HeckeSkeleton.Moments.EngineStep.whole_gauss_eq_actual_unit_columns
#print axioms HeckeSkeleton.Moments.EngineStep.actual_gauss_generator_replacement
