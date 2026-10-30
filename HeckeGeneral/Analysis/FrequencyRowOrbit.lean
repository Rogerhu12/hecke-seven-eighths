import HeckeGeneral.Analysis.PhysicalProbeRows
import HeckeGeneral.Analysis.ActualSIntegerSimultaneousAmplifier

/-!
Physical frequency rows embed into actual sixth-power S-unit orbits.
The contraction recovers the exterior ideal. Cancellation of its actual
nonzero generator then recovers the original unit sector. No row-injection
or sector-identification assumption is introduced.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S)

theorem frequencyRowElement_ne_zero (u : FrequencyRow K S) :
    frequencyRowElement K S P u ≠ 0 := by
  exact mul_ne_zero (Units.ne_zero _) (P.arithmetic.generator_ne_zero u.ideal)

theorem frequencyRowElement_contraction (u : FrequencyRow K S) :
    sIntegerModulusContraction K S (frequencyRowElement K S P u) = u.ideal.val.val := by
  unfold frequencyRowElement sIntegerModulusContraction
  rw [Ideal.span_singleton_mul_left_unit
    (S.unitEquivUnitsInteger K (Quotient.out u.sector)).isUnit]
  exact contraction_thetaGenerator K S P.arithmetic u.ideal

def frequencyRowOrbit (u : FrequencyRow K S) : ActualSIntegerOrbit K S :=
  Quotient.mk _ ⟨frequencyRowElement K S P u, frequencyRowElement_ne_zero K S P u⟩

theorem frequencyRowOrbit_contraction (u : FrequencyRow K S) :
    actualSIntegerOrbitContraction K S (frequencyRowOrbit K S P u) = u.ideal.val.val :=
  frequencyRowElement_contraction K S P u

theorem frequencyRowOrbit_ideal (u : FrequencyRow K S) :
    actualSIntegerOrbitIdeal K S (frequencyRowOrbit K S P u) = u.ideal.val :=
  Subtype.ext (frequencyRowOrbit_contraction K S P u)

theorem frequencyRowOrbit_norm (u : FrequencyRow K S) :
    actualSIntegerOrbitNorm K S (frequencyRowOrbit K S P u) = frequencyRowNorm K S u := by
  rw [actualSIntegerOrbitNorm_eq_absNorm_contraction, frequencyRowOrbit_contraction]
  rfl

def frequencyRowSixthPowerFreeOrbit (u : FrequencyRow K S) : ActualSixthPowerFreeOrbit K S :=
  ⟨frequencyRowOrbit K S P u, by
    rw [frequencyRowOrbit_ideal, sixthPowerFreeIdeal_iff_primeExponents_lt]
    exact u.sixthPowerFree⟩

theorem frequencyRowOrbit_injective : Function.Injective (frequencyRowOrbit K S P) := by
  intro u v huv
  have hi : u.ideal = v.ideal := by
    apply Subtype.ext
    have h := congrArg (actualSIntegerOrbitIdeal K S) huv
    simpa only [frequencyRowOrbit_ideal] using h
  obtain ⟨γ, hγ⟩ := (sIntegerOrbitRelation_iff K S (sixthPowerSUnitSubgroup K S)
    ⟨frequencyRowElement K S P u, frequencyRowElement_ne_zero K S P u⟩
    ⟨frequencyRowElement K S P v, frequencyRowElement_ne_zero K S P v⟩).mp
      (Quotient.exact huv)
  have hg : (P.arithmetic.generator v.ideal : K) ≠ 0 := by
    intro h
    exact P.arithmetic.generator_ne_zero v.ideal (Subtype.ext h)
  have he : γ.val * Quotient.out v.sector = Quotient.out u.sector := by
    apply Subtype.ext
    apply Units.ext
    apply mul_right_cancel₀ hg
    change (((γ.val : Kˣ) : K) * (((Quotient.out v.sector : S.unit K) : Kˣ) : K)) *
        (P.arithmetic.generator v.ideal : K) =
      (((Quotient.out u.sector : S.unit K) : Kˣ) : K) * (P.arithmetic.generator v.ideal : K)
    change ((γ.val : Kˣ) : K) *
        ((((Quotient.out v.sector : S.unit K) : Kˣ) : K) * (P.arithmetic.generator v.ideal : K)) =
      (((Quotient.out u.sector : S.unit K) : Kˣ) : K) * (P.arithmetic.generator u.ideal : K) at hγ
    rw [hi] at hγ
    exact (mul_assoc _ _ _).trans hγ
  have hq : QuotientGroup.mk' (sixthPowerSUnitSubgroup K S) (Quotient.out v.sector) =
      QuotientGroup.mk' (sixthPowerSUnitSubgroup K S) (Quotient.out u.sector) := by
    apply (QuotientGroup.mk'_eq_mk' (sixthPowerSUnitSubgroup K S)).mpr
    exact ⟨γ.val, γ.property, (mul_comm _ _).trans he⟩
  have hqu : QuotientGroup.mk' (sixthPowerSUnitSubgroup K S) (Quotient.out u.sector) =
      u.sector := Quotient.out_eq u.sector
  have hqv : QuotientGroup.mk' (sixthPowerSUnitSubgroup K S) (Quotient.out v.sector) =
      v.sector := Quotient.out_eq v.sector
  have hs : u.sector = v.sector := hqu.symm.trans (hq.symm.trans hqv)
  cases u
  cases v
  cases hi
  cases hs
  rfl

theorem frequencyRowSixthPowerFreeOrbit_injective :
    Function.Injective (frequencyRowSixthPowerFreeOrbit K S P) := by
  intro u v h
  exact frequencyRowOrbit_injective K S P (congrArg Subtype.val h)

def frequencyRowOrbitEmbedding : FrequencyRow K S ↪ ActualSixthPowerFreeOrbit K S :=
  ⟨frequencyRowSixthPowerFreeOrbit K S P, frequencyRowSixthPowerFreeOrbit_injective K S P⟩

/-- Both the physical base row and its exterior amplifier ideal are
recovered from the actual amplified orbit. -/
def frequencyRowAmplifierEmbedding :
    (FrequencyRow K S × ExteriorIdeal K S) ↪ ActualSIntegerOrbit K S where
  toFun x := actualSimultaneousAmplifier K S P.arithmetic
    (frequencyRowSixthPowerFreeOrbit K S P x.1).val x.2
  inj' x y h := by
    have he := actualSimultaneousAmplifier_injective K S P.arithmetic
      (a₁ := (frequencyRowSixthPowerFreeOrbit K S P x.1, x.2))
      (a₂ := (frequencyRowSixthPowerFreeOrbit K S P y.1, y.2)) h
    have hbase : frequencyRowSixthPowerFreeOrbit K S P x.1 =
        frequencyRowSixthPowerFreeOrbit K S P y.1 :=
      congrArg (fun z : ActualSixthPowerFreeOrbit K S × ExteriorIdeal K S => z.1) he
    have hA : x.2 = y.2 :=
      congrArg (fun z : ActualSixthPowerFreeOrbit K S × ExteriorIdeal K S => z.2) he
    exact Prod.ext (frequencyRowSixthPowerFreeOrbit_injective K S P hbase) hA

end HeckeGeneral.ThetaSkeleton.Physical
