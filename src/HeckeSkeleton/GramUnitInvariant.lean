import HeckeGeneral.Analysis.PhysicalProbeData
import Mathlib.Algebra.Group.Units.Equiv

/-!
Sixth-unit invariance for the literal finite Gauss sum in the Gram amplitude.
The proof reindexes the full residue quotient by a unit; zero and nonunit
frequencies remain present, and the original sixth-power subgroup is retained.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.Gram

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem gramIdealSymbol_mul_sixth_unit (D : ThetaArithmeticData K S)
    (I : ExteriorIdeal K S) (u : S.unit K) (a : S.integer K) :
    idealSymbol K S D I ((S.unitEquivUnitsInteger K u).val ^ 6 * a) =
      idealSymbol K S D I a :=
  sIntegerSexticIdealEvaluation_mul_sixth_power_unit K S D.root6 D.primitive6
    D.embedding I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp)) u a

theorem gramProbeGauss_mul_sixth_unit (P : ProbeData K S) (I : ExteriorIdeal K S)
    (u : S.unit K) (k : S.integer K) :
    probeGauss K S P I ((S.unitEquivUnitsInteger K u).val ^ 6 * k) =
      probeGauss K S P I k := by
  letI : Finite (ThetaQuotient K S I) :=
    finite_sIntegerSexticIdealQuotient K S I.val.val
      (nonZeroDivisors.coe_ne_zero I.val) I.property
  letI : Fintype (ThetaQuotient K S I) := Fintype.ofFinite _
  let χ := sIntegerSexticIdealQuotientFunction K S P.arithmetic.root6
    P.arithmetic.primitive6 P.arithmetic.embedding I.val.val
    (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => P.arithmetic.away_six p (I.property p hp))
  let v : (ThetaQuotient K S I)ˣ :=
    Units.map (Ideal.Quotient.mk
      (I.val.val.map (algebraMap (𝓞 K) (S.integer K)))).toMonoidHom
      ((S.unitEquivUnitsInteger K u) ^ 6)
  have hv : (v : ThetaQuotient K S I) =
      Ideal.Quotient.mk _ ((S.unitEquivUnitsInteger K u).val ^ 6) := by
    simp only [v, Units.coe_map, Units.val_pow_eq_pow_val]
    rfl
  have hχ : ∀ d : ThetaQuotient K S I, χ ((v : ThetaQuotient K S I) * d) = χ d := by
    intro d
    refine Quotient.inductionOn' d ?_
    intro a
    change χ ((v : ThetaQuotient K S I) * Ideal.Quotient.mk _ a) =
      χ (Ideal.Quotient.mk _ a)
    rw [hv, ← map_mul]
    exact (sIntegerSexticIdealQuotientFunction_mk K S P.arithmetic.root6
      P.arithmetic.primitive6 P.arithmetic.embedding I.val.val
      (nonZeroDivisors.coe_ne_zero I.val) I.property
      (fun p hp => P.arithmetic.away_six p (I.property p hp)) _).trans
        ((gramIdealSymbol_mul_sixth_unit K S P.arithmetic I u a).trans
          (sIntegerSexticIdealQuotientFunction_mk K S P.arithmetic.root6
            P.arithmetic.primitive6 P.arithmetic.embedding I.val.val
            (nonZeroDivisors.coe_ne_zero I.val) I.property
            (fun p hp => P.arithmetic.away_six p (I.property p hp)) a).symm)
  change (∑ d : ThetaQuotient K S I, χ d * thetaPrincipalAddCharacter K S P.arithmetic I
      (Ideal.Quotient.mk _ ((S.unitEquivUnitsInteger K u).val ^ 6 * k) * d)) =
    ∑ d : ThetaQuotient K S I, χ d * thetaPrincipalAddCharacter K S P.arithmetic I
      (Ideal.Quotient.mk _ k * d)
  apply Fintype.sum_equiv v.mulLeft
  intro d
  change χ d * thetaPrincipalAddCharacter K S P.arithmetic I
      (Ideal.Quotient.mk _ ((S.unitEquivUnitsInteger K u).val ^ 6 * k) * d) =
    χ ((v : ThetaQuotient K S I) * d) * thetaPrincipalAddCharacter K S P.arithmetic I
      (Ideal.Quotient.mk _ k * ((v : ThetaQuotient K S I) * d))
  rw [hχ]
  apply congrArg (fun x => χ d * thetaPrincipalAddCharacter K S P.arithmetic I x)
  rw [hv, map_mul]
  ring

theorem gramProbeGauss_neg_mul_sixthPowerUnits (P : ProbeData K S)
    (I : ExteriorIdeal K S) (γ : sixthPowerUnits K S) (m : S.integer K) :
    probeGauss K S P I (-((S.unitEquivUnitsInteger K γ.val).val * m)) =
      probeGauss K S P I (-m) := by
  have hγ : γ.val ∈ (powMonoidHom 6 : S.unit K →* S.unit K).range := γ.property
  obtain ⟨u, hu⟩ := hγ
  change u ^ 6 = γ.val at hu
  rw [← hu, map_pow, Units.val_pow_eq_pow_val]
  rw [show -((S.unitEquivUnitsInteger K u).val ^ 6 * m) =
    (S.unitEquivUnitsInteger K u).val ^ 6 * (-m) by ring]
  exact gramProbeGauss_mul_sixth_unit K S P I u (-m)

end HeckeSkeleton.Gram
