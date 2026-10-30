import HeckeGeneral.Analysis.MarkedThetaReflection
import HeckeGeneral.Analysis.ActualSIntegerAmplifierRows

/-! UNCOMPILED CACHE CANDIDATE.

The norm field of AllowedGeneratorInput follows from generator_span and the
proved identification of actual principal residue cardinality with the local
product norm. It holds for every ThetaArithmeticData, including sections which
are not allowed or multiplicative. Multiplicativity and reciprocity remain
explicit hypotheses of the builder below; neither is inferred from the span.
No Lean/Lake invocation has checked this candidate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Global

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis.ActualSIntegerMoments

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- The actual S-local norm is determined by the generated exterior ideal,
without any allowed-section, reciprocity, or norm hypothesis. -/
theorem thetaGenerator_productNorm (I : ExteriorIdeal K S) :
    sLocalProductNorm K S (sLocalNonzeroIntegerDiagonal K S
      ⟨D.generator I, D.generator_ne_zero I⟩) = exteriorNorm K S I := by
  change (sIntegerElementNorm K S ⟨D.generator I, D.generator_ne_zero I⟩).val =
    (I.val.val.absNorm : ℝ)
  have h := natCard_sIntegerPrincipalResidue_eq_productNorm K S
    (D.generator I) (D.generator_ne_zero I)
  rw [natCard_sIntegerPrincipalResidue K S (D.generator I) (D.generator_ne_zero I),
    contraction_thetaGenerator K S D I] at h
  exact h.symm

/-- Only the two genuine allowed-section compatibilities need to be supplied.
In particular this does not assert their existence for an arbitrary section. -/
theorem AllowedGeneratorInput.of_multiplicative_reciprocity
    (hmul : ∀ I J : ExteriorIdeal K S, ∃ u : S.unit K,
      D.generator (exteriorMul K S I J) =
        (S.unitEquivUnitsInteger K u).val ^ 6 * D.generator I * D.generator J)
    (hrecip : ∀ I J : ExteriorIdeal K S,
      idealSymbol K S D I (D.generator J) = idealSymbol K S D J (D.generator I)) :
    AllowedGeneratorInput K S D :=
  { multiplicative := hmul
    reciprocity := hrecip
    generator_norm := thetaGenerator_productNorm K S D }

end HeckeGeneral.ThetaSkeleton.Global
