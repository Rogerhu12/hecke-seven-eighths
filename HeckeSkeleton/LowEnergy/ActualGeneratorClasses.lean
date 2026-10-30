import HeckeSkeleton.LowEnergy.ActualClassSlices

/-!
# Generator classes and the full cube column

The accepted generator-section compatibility is used exactly once: a
multiplicative defect is a sixth power of an S-unit, hence has trivial class
in `SixthLocalClasses`.  The local-frequency class therefore depends on the
full cube column `x*n` after `numeratorFrozen = minimum*x^3`.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.ActualGeneratorClasses
open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.ActualClassSlices
open HeckeSkeleton.LowEnergy.ClassSlices
open scoped BigOperators NumberField

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- The multiplicative section defect dies in the actual local class group. -/
theorem generatorLocalClass_mul (hD : AllowedGeneratorInput K S D)
    (I J : ExteriorIdeal K S) :
    generatorLocalClass K S D (exteriorMul K S I J) =
      generatorLocalClass K S D I * generatorLocalClass K S D J := by
  obtain ⟨u, hu⟩ := hD.multiplicative I J
  have hfield :
      nonzeroSIntegerFieldUnit K S ⟨D.generator (exteriorMul K S I J), D.generator_ne_zero _⟩ =
        (u : Kˣ) ^ 6 *
          nonzeroSIntegerFieldUnit K S ⟨D.generator I, D.generator_ne_zero I⟩ *
          nonzeroSIntegerFieldUnit K S ⟨D.generator J, D.generator_ne_zero J⟩ := by
    apply Units.ext
    have h := congrArg (fun a : S.integer K => (a : K)) hu
    exact h
  have hdiag :
      sLocalNonzeroIntegerDiagonal K S
          ⟨D.generator (exteriorMul K S I J), D.generator_ne_zero _⟩ =
        sLocalDiagonal K S u ^ 6 *
          sLocalNonzeroIntegerDiagonal K S ⟨D.generator I, D.generator_ne_zero I⟩ *
          sLocalNonzeroIntegerDiagonal K S ⟨D.generator J, D.generator_ne_zero J⟩ := by
    unfold sLocalNonzeroIntegerDiagonal
    rw [hfield, map_mul, map_mul, map_pow, sLocalFieldUnitDiagonal_sUnit]
  have h6 : (QuotientGroup.mk (sLocalDiagonal K S u ^ 6) : SixthLocalClasses K S) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨sLocalDiagonal K S u, rfl⟩
  have hclass := congrArg
    (fun x : sLocalMultiplicativeGroup K S => (QuotientGroup.mk x : SixthLocalClasses K S)) hdiag
  simpa only [generatorLocalClass, QuotientGroup.mk_mul, h6, one_mul] using hclass

/-- The actual exterior power; its underlying ideal is the usual ideal power. -/
def exteriorPow (I : ExteriorIdeal K S) (n : ℕ) : ExteriorIdeal K S :=
  ⟨I.val ^ n, fun p hp => I.property p (p.prime.dvd_of_dvd_pow hp)⟩

theorem exteriorPow_succ (I : ExteriorIdeal K S) (n : ℕ) :
    exteriorPow K S I (n + 1) = exteriorMul K S (exteriorPow K S I n) I := by
  apply Subtype.ext
  exact pow_succ I.val n

theorem generatorLocalClass_pow (hD : AllowedGeneratorInput K S D)
    (I : ExteriorIdeal K S) (n : ℕ) :
    generatorLocalClass K S D (exteriorPow K S I n) = generatorLocalClass K S D I ^ n := by
  induction n with
  | zero =>
    have he : exteriorMul K S (exteriorPow K S I 0) (exteriorPow K S I 0) =
        exteriorPow K S I 0 := by
      apply Subtype.ext
      simp [exteriorMul, exteriorPow]
    have hm := generatorLocalClass_mul K S D hD (exteriorPow K S I 0) (exteriorPow K S I 0)
    rw [he] at hm
    have hx : generatorLocalClass K S D (exteriorPow K S I 0) * 1 =
        generatorLocalClass K S D (exteriorPow K S I 0) *
          generatorLocalClass K S D (exteriorPow K S I 0) := by simpa using hm
    simpa only [pow_zero] using (mul_left_cancel hx).symm
  | succ n ih =>
    rw [exteriorPow_succ, generatorLocalClass_mul K S D hD, ih, pow_succ]

/-- General form for any exterior ideal presented by the given underlying power. -/
theorem generatorLocalClass_of_power (hD : AllowedGeneratorInput K S D)
    (I J : ExteriorIdeal K S) (n : ℕ) (hJ : J.val = I.val ^ n) :
    generatorLocalClass K S D J = generatorLocalClass K S D I ^ n := by
  have he : J = exteriorPow K S I n := Subtype.ext hJ
  rw [he]
  exact generatorLocalClass_pow K S D hD I n

/-- Regrouping is exact: the local-frequency class sees the full cube `x*n`,
not an independently frozen cube variable. -/
theorem frequencyClass_full_cube (hD : AllowedGeneratorInput K S D)
    (d : MarkedDatum K S) (i : ReflectionIndex K S d)
    (minimum cube : ExteriorIdeal K S)
    (hnum : exteriorMul K S minimum (exteriorPow K S cube 3) = i.numeratorFrozen) :
    frequencyClass K S D d i =
      blockFrequency
        (unitLocalClass K S (frequencyUnit K S d i) * generatorLocalClass K S D minimum *
          generatorLocalClass K S D (activeFrozenIdeal K S d i) ^ (-2 : ℤ))
        (generatorLocalClass K S D d.moving)
        (generatorLocalClass K S D (activeMarkedIdeal K S d i))
        (generatorLocalClass K S D i.c)
        (generatorLocalClass K S D (exteriorMul K S cube i.n)) := by
  unfold frequencyClass blockFrequency
  rw [← hnum, generatorLocalClass_mul K S D hD,
    generatorLocalClass_pow K S D hD,
    generatorLocalClass_mul K S D hD, mul_pow]
  ac_rfl

/-- The actual kernel's class can now be sliced with a fixed minimum and a
joint column mask on `(c, x*n)`. -/
theorem kernel_frequency_full_cube_expansion [Fintype (SixthLocalClasses K S)]
    (hD : AllowedGeneratorInput K S D) (F : FiniteMellinData K S)
    (θ : HeckeGeneral.Characters.HeckeCharacter K)
    (d : MarkedDatum K S) (i : ReflectionIndex K S d)
    (minimum cube : ExteriorIdeal K S)
    (hnum : exteriorMul K S minimum (exteriorPow K S cube 3) = i.numeratorFrozen)
    (V : ℝ → ℂ) (y : ℝ) :
    mellinReflectionKernel K S F θ (QuotientGroup.mk d.rowUnit)
      (frequencyClass K S D d i) V 0 y =
      ∑ q : FourClasses (SixthLocalClasses K S),
        mellinReflectionKernel K S F θ (QuotientGroup.mk d.rowUnit)
          (blockFrequency
            (unitLocalClass K S (frequencyUnit K S d i) * generatorLocalClass K S D minimum *
              generatorLocalClass K S D (activeFrozenIdeal K S d i) ^ (-2 : ℤ))
            q.1.1 q.1.2 q.2.1 q.2.2) V 0 y *
        rowMask q (generatorLocalClass K S D d.moving) *
        markMask q (generatorLocalClass K S D (activeMarkedIdeal K S d i)) *
        columnMask q (generatorLocalClass K S D i.c)
          (generatorLocalClass K S D (exteriorMul K S cube i.n)) := by
  rw [frequencyClass_full_cube K S D hD d i minimum cube hnum]
  exact class_expansion (fun r m c n =>
    mellinReflectionKernel K S F θ (QuotientGroup.mk d.rowUnit)
      (blockFrequency
        (unitLocalClass K S (frequencyUnit K S d i) * generatorLocalClass K S D minimum *
          generatorLocalClass K S D (activeFrozenIdeal K S d i) ^ (-2 : ℤ)) r m c n) V 0 y)
    _ _ _ _

#print axioms generatorLocalClass_mul
#print axioms generatorLocalClass_pow
#print axioms frequencyClass_full_cube
#print axioms kernel_frequency_full_cube_expansion

end HeckeSkeleton.LowEnergy.ActualGeneratorClasses
