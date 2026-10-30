import CubicSieve.OrbitRows

/-! The cubic orbital kernel separates into the same ideal kernel and one
unitary column phase for each of the finitely many sixth-unit sectors. -/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.OrbitKernel

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global
open CubicSieve.OrbitRows CubicSieve.ExteriorKernel
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

def coefficient (J : ExteriorIdeal K S) (q : Orbits K S) : ℂ :=
  Quotient.liftOn q (fun a => idealSymbol K S D J a.val ^ (2 : ℕ)) (by
    intro a b hab
    obtain ⟨u, hu⟩ := (sIntegerOrbitRelation_iff K S (Γ K S) a b).mp hab
    have he : (S.unitEquivUnitsInteger K u.val).val * b.val = a.val := Subtype.ext hu
    rw [← he]
    unfold idealSymbol
    rw [sIntegerSexticIdealEvaluation_literal_invariant K S D.root6 D.primitive6 D.embedding
      J.val.val (nonZeroDivisors.coe_ne_zero J.val) J.property
      (fun p hp => D.away_six p (J.property p hp)) (Γ K S) le_rfl u b.val])

@[simp] theorem coefficient_mk (J : ExteriorIdeal K S) (a : NonzeroRingElements (S.integer K)) :
    coefficient K S D J (Quotient.mk _ a) = idealSymbol K S D J a.val ^ (2 : ℕ) := rfl

def unitPhase (l : SixthUnitClasses K S) (J : ExteriorIdeal K S) : ℂ :=
  idealSymbol K S D J (S.unitEquivUnitsInteger K l.out).val ^ (2 : ℕ)

theorem unitPhase_norm (l : SixthUnitClasses K S) (J : ExteriorIdeal K S) :
    ‖unitPhase K S D l J‖ = 1 := by
  have hu : ‖idealSymbol K S D J (S.unitEquivUnitsInteger K l.out).val‖ = 1 := by
    apply norm_sIntegerSexticIdealEvaluation_eq_one K S D.root6 D.primitive6 D.embedding
      J.val.val (nonZeroDivisors.coe_ne_zero J.val) J.property
      (fun p hp => D.away_six p (J.property p hp))
    intro p hp
    letI : Field (𝓞 K ⧸ p.asIdeal) := Ideal.Quotient.field _
    exact ((S.unitEquivUnitsInteger K l.out).isUnit.map
      (sIntegerSexticResidueMap K S p (J.property p hp))).ne_zero
  rw [unitPhase, norm_pow, hu, one_pow]

theorem coefficient_classOrbit (I J : ExteriorIdeal K S) (l : SixthUnitClasses K S) :
    coefficient K S D J (classOrbit K S D (I, l)) =
      positiveKernel K S D I J * unitPhase K S D l J := by
  change idealSymbol K S D J
    ((S.unitEquivUnitsInteger K l.out).val * D.generator I) ^ (2 : ℕ) = _
  simp only [idealSymbol, sIntegerSexticIdealEvaluation_mul, mul_pow,
    positiveKernel, kernel, symbol, unitPhase, zpow_ofNat]
  all_goals ring

end CubicSieve.OrbitKernel
