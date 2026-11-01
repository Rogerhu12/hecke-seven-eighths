import HeckeGeneral.Analysis.MarkedThetaReflection
import HeckeGeneral.Arithmetic.SUnitNormOneQuotient

/-!
# The literal reflected index's field frequency, local class and norm

The three independent ideal coordinates and both active finite sets are
retained.  These are identities on the full index, including its zero
coefficients; injectivity is required only after restricting to support.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GlobalActualFrequency

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
  (D : ThetaArithmeticData K S)

def generatorUnit (I : ExteriorIdeal K S) : Kˣ :=
  nonzeroSIntegerFieldUnit K S ⟨D.generator I, D.generator_ne_zero I⟩

def representative (d : MarkedDatum K S) (i : ReflectionIndex K S d) : Kˣ :=
  (frequencyUnit K S d i).val * generatorUnit K S D i.numeratorFrozen *
    generatorUnit K S D i.c * generatorUnit K S D i.n ^ 3 *
    generatorUnit K S D d.moving ^ (-2 : ℤ) *
    generatorUnit K S D (activeFrozenIdeal K S d i) ^ (-2 : ℤ) *
    generatorUnit K S D (activeMarkedIdeal K S d i) ^ (-2 : ℤ)

theorem localClass_representative (d : MarkedDatum K S) (i : ReflectionIndex K S d) :
    (QuotientGroup.mk (sLocalFieldUnitDiagonal K S (representative K S D d i)) :
      SixthLocalClasses K S) = frequencyClass K S D d i := by
  change (QuotientGroup.mk' (powMonoidHom 6 : sLocalMultiplicativeGroup K S →*
    sLocalMultiplicativeGroup K S).range)
    (sLocalFieldUnitDiagonal K S (representative K S D d i)) = _
  simp only [representative, map_mul, map_pow, map_zpow]
  rfl

def normHom : Kˣ →* ℝˣ :=
  (sLocalProductNormHom K S).comp (sLocalFieldUnitDiagonal K S)

theorem normHom_sUnit (u : S.unit K) : (normHom K S u.val : ℝ) = 1 :=
  sLocalProductNorm_diagonal K S u

theorem normHom_generator (hG : AllowedGeneratorInput K S D) (I : ExteriorIdeal K S) :
    (normHom K S (generatorUnit K S D I) : ℝ) = exteriorNorm K S I :=
  hG.generator_norm I

/-- Exactly the positive argument used by `reflectedTerm`, before the
external scale X is inserted. -/
theorem norm_representative (hG : AllowedGeneratorInput K S D)
    (d : MarkedDatum K S) (i : ReflectionIndex K S d) :
    sLocalProductNorm K S (sLocalFieldUnitDiagonal K S (representative K S D d i)) =
      exteriorNorm K S i.numeratorFrozen * exteriorNorm K S i.c *
        exteriorNorm K S i.n ^ 3 /
        (exteriorNorm K S d.moving * exteriorNorm K S (activeFrozenIdeal K S d i) *
          exteriorNorm K S (activeMarkedIdeal K S d i)) ^ 2 := by
  change (normHom K S (representative K S D d i) : ℝ) = _
  simp only [representative, map_mul, map_pow, map_zpow, Units.val_mul,
    Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val,
    normHom_sUnit, normHom_generator K S D hG, one_mul]
  simp only [zpow_neg, zpow_ofNat, div_eq_mul_inv, mul_pow, mul_inv_rev]
  ring

theorem scaled_norm_representative (hG : AllowedGeneratorInput K S D)
    (d : MarkedDatum K S) (i : ReflectionIndex K S d) (X : ℝ) :
    X * sLocalProductNorm K S
      (sLocalFieldUnitDiagonal K S (representative K S D d i)) =
      X * exteriorNorm K S i.numeratorFrozen * exteriorNorm K S i.c *
        exteriorNorm K S i.n ^ 3 /
        (exteriorNorm K S d.moving * exteriorNorm K S (activeFrozenIdeal K S d i) *
          exteriorNorm K S (activeMarkedIdeal K S d i)) ^ 2 := by
  rw [norm_representative K S D hG]
  ring

end ThetaGlobal.GlobalActualFrequency
