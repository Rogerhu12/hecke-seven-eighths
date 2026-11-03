import HeckeSkeleton.ActualProbeSixthUnitInvariant

/-!
UNCOMPILED / native 0. Specialization of the existing actual finite quotient
unit-substitution proof to the ORIGINAL sixthPowerUnits subgroup. No new
subgroup, unit-symbol hypothesis, or frequency-invariance premise is introduced.
The imported substitution theorem already has a matching successful cache
native receipt; the new orbit specializations below have not been compiled.
-/

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualProbeGaussFourierDraft

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Literal invariance for every element of the original physical unit group,
including all zero and nonunit frequencies. Membership itself supplies the
sixth root needed by the proved finite Gauss unit substitution. -/
theorem probeGauss_mul_sixthPowerUnits (P : ProbeData K S)
    (I : ExteriorIdeal K S) (γ : sixthPowerUnits K S) (m : S.integer K) :
    probeGauss K S P I ((S.unitEquivUnitsInteger K γ.val).val * m) =
      probeGauss K S P I m := by
  have hγ : γ.val ∈ (powMonoidHom 6 : S.unit K →* S.unit K).range := γ.property
  obtain ⟨u, hu⟩ := hγ
  change u ^ 6 = γ.val at hu
  rw [← hu, map_pow, Units.val_pow_eq_pow_val]
  exact probeGauss_mul_sixth_unit K S P I u m

/-- The actual row uses negative frequency; the same group action preserves
that literal negative argument without changing the additive-character sign. -/
theorem probeGauss_neg_mul_sixthPowerUnits (P : ProbeData K S)
    (I : ExteriorIdeal K S) (γ : sixthPowerUnits K S) (m : S.integer K) :
    probeGauss K S P I (-((S.unitEquivUnitsInteger K γ.val).val * m)) =
      probeGauss K S P I (-m) := by
  rw [show -((S.unitEquivUnitsInteger K γ.val).val * m) =
    (S.unitEquivUnitsInteger K γ.val).val * (-m) by ring]
  exact probeGauss_mul_sixthPowerUnits K S P I γ (-m)

/-- Both actual Gauss columns descend under the SAME original unit action. -/
theorem probeGauss_mul_conj_sixthPowerUnits (P : ProbeData K S)
    (I J : ExteriorIdeal K S) (γ : sixthPowerUnits K S) (m : S.integer K) :
    probeGauss K S P I ((S.unitEquivUnitsInteger K γ.val).val * m) *
        conj (probeGauss K S P J ((S.unitEquivUnitsInteger K γ.val).val * m)) =
      probeGauss K S P I m * conj (probeGauss K S P J m) := by
  rw [probeGauss_mul_sixthPowerUnits, probeGauss_mul_sixthPowerUnits]

end HeckeGeneral.ThetaSkeleton.Physical.ActualProbeGaussFourierDraft
