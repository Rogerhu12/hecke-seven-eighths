import ActualAdditiveGramAmplitude
import ActualProbePairPeriodicFourier
import ActualProbeGaussSixthUnitOrbit

/-!
SOURCE CANDIDATE / not compiled. The literal (3.33) amplitude and the actual
two-column periodic coefficient descend under the ORIGINAL sixthPowerUnits.
The coefficient c is fixed before the row. Every sector of that subgroup
is retained. No invariance assumption or new subgroup is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualAdditiveGramDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open ActualProbeGaussFourierDraft ActualProbePairFourierDraft
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.SquarefreeAmplification
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem actualAdditiveGramTerm_unit_invariant (P : ProbeData K S)
    (c : ExteriorIdeal K S → ℂ) (W : SmoothAnnularTest)
    (Y ν : ℝ) (γ : sixthPowerUnits K S) (m : S.integer K) (I : ExteriorIdeal K S) :
    actualAdditiveGramTerm K S P c W Y ν ((S.unitEquivUnitsInteger K γ.val).val * m) I =
      actualAdditiveGramTerm K S P c W Y ν m I := by
  unfold actualAdditiveGramTerm
  rw [probeGauss_neg_mul_sixthPowerUnits]

/-- Literal invariance is proved for the defined amplitude, even before
restricting to positive scales. Positive-scale finite support is separate. -/
theorem actualAdditiveGramAmplitude_unit_invariant (P : ProbeData K S)
    (c : ExteriorIdeal K S → ℂ) (W : SmoothAnnularTest)
    (Y ν : ℝ) (γ : sixthPowerUnits K S) (m : S.integer K) :
    actualAdditiveGramAmplitude K S P c W Y ν ((S.unitEquivUnitsInteger K γ.val).val * m) =
      actualAdditiveGramAmplitude K S P c W Y ν m := by
  unfold actualAdditiveGramAmplitude
  congr 1
  apply tsum_congr
  intro I
  exact actualAdditiveGramTerm_unit_invariant K S P c W Y ν γ m I

/-- The actual nonzero-row amplitude on all original sixth-unit sectors. -/
def actualAdditiveGramOrbitAmplitude (P : ProbeData K S)
    (c : ExteriorIdeal K S → ℂ) (W : SmoothAnnularTest) (Y ν : ℝ) :
    SIntegerOrbits K S (sixthPowerUnits K S) → ℂ :=
  Quotient.lift (fun m => actualAdditiveGramAmplitude K S P c W Y ν m.val) (by
    intro a b hab
    obtain ⟨γ, hγ⟩ := (sIntegerOrbitRelation_iff K S (sixthPowerUnits K S) a b).mp hab
    have he : (S.unitEquivUnitsInteger K γ.val).val * b.val = a.val := Subtype.ext hγ
    have h := actualAdditiveGramAmplitude_unit_invariant K S P c W Y ν γ b.val
    rw [he] at h
    exact h)

@[simp] theorem actualAdditiveGramOrbitAmplitude_mk (P : ProbeData K S)
    (c : ExteriorIdeal K S → ℂ) (W : SmoothAnnularTest) (Y ν : ℝ)
    (m : NonzeroRingElements (S.integer K)) :
    actualAdditiveGramOrbitAmplitude K S P c W Y ν (Quotient.mk _ m) =
      actualAdditiveGramAmplitude K S P c W Y ν m.val := rfl

/-- This is exactly the hypothesis consumed by periodic orbital Poisson,
now a theorem for the actual negative-frequency probe pair. -/
theorem probeNegativeGaussPairResidue_literal_invariant (P : ProbeData K S)
    (I J : ExteriorIdeal K S) (γ : sixthPowerUnits K S) (m : S.integer K) :
    probeNegativeGaussPairResidue K S P I J
        (Ideal.Quotient.mk _ ((S.unitEquivUnitsInteger K γ.val).val * m)) =
      probeNegativeGaussPairResidue K S P I J (Ideal.Quotient.mk _ m) := by
  rw [probeNegativeGaussPairResidue_mk, probeNegativeGaussPairResidue_mk,
    probeGauss_neg_mul_sixthPowerUnits, probeGauss_neg_mul_sixthPowerUnits]

end HeckeGeneral.ThetaSkeleton.Physical.ActualAdditiveGramDraft
