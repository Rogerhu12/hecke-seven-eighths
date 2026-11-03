module

public import DedekindZetaZeroFree.Theta.Profiles.ReflectedSheetClasses
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.SexticRowReciprocity

@[expose] public section

/-!
# Hilbert-symbol orientation in the reflected Mellin table

The paper uses `chi_I(epsilon) = H_paper(epsilon,a)⁻¹`.
The actual Axiom normalization has `chi_I(epsilon) = H_Axiom(epsilon,a)`;
its local Hilbert pairing is explicitly inverse-normalized relative to
the raw class-field-theory pairing.  Therefore

`H_paper = embedding(H_Axiom)⁻¹`.

This file records the exact dictionary against the actual residue symbol,
the actual period branch, and the actual reflected sheet integrand.
Consequently the squared paper pairing in the finite Mellin table must be
the inverse square of the embedded `A.H_S6` pairing.

Project-facing source; see the separate compilation-status report.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GlobalProjectConvention

open NumberField DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)

def paperHilbert (κ τ : R.A.V) : ℂ :=
  (R.σ ((R.A.H_S6 κ τ : Fˣ) : F))⁻¹

theorem paperHilbert_on_representatives (x y : R.A.G) :
    paperHilbert R (QuotientGroup.mk' R.A.sixthPowers x)
      (QuotientGroup.mk' R.A.sixthPowers y) =
      (R.σ ((R.A.H_S x y : Fˣ) : F))⁻¹ := by
  rw [paperHilbert, R.A.H_S6_on_representatives]

/-- The actual residue symbol fixes the orientation; it is not an
independent convention that may be changed after the choice of data. -/
theorem unit_residue_eq_paperHilbert_inv
    (I : R.A.Exterior) (r : R.A.R) (a : Fˣ) (ε : R.A.U)
    (hr : R.A.Generates I r) (har : (a : F) = (r : F))
    (ha : ThetaReflectionData.rationalClass R.A a ∈ R.probe.correction.B) :
    R.σ (R.A.sexticResidue I (R.A.unitEquiv ε : R.A.R)) =
      (paperHilbert R
        (QuotientGroup.mk' R.A.sixthPowers (R.A.diagonal ε.val))
        (QuotientGroup.mk' R.A.sixthPowers (R.A.diagonal a)))⁻¹ := by
  have hrec := ArithmeticContext.actual_hilbert_sextic_reciprocity R.A
    R.probe.correction.H R.probe.correction.B R.probe.correction.H_actual
    R.probe.correction.B_complement
  have hu := hrec.2.1 I r a ε hr har ha
  have hu' : R.A.sexticResidue I (R.A.unitEquiv ε : R.A.R) =
      ((R.A.H_S (R.A.diagonal ε.val) (R.A.diagonal a) : Fˣ) : F) := by
    rw [hu]
    exact congrArg (fun z : Fˣ => (z : F)) (R.probe.correction.H_actual _ _)
  rw [hu', paperHilbert_on_representatives, inv_inv]

theorem correction_inverse_square (κ τ : R.A.V) :
    (R.σ ((R.probe.correction.H κ τ : Fˣ) : F) ^ 2)⁻¹ =
      paperHilbert R κ τ ^ 2 := by
  rw [OrbitExpansion.correction_pairing_eq]
  simp only [paperHilbert, inv_pow]

/-- The paper's row-unit twist is the positive Axiom pairing in the
actual period branch. -/
theorem packet_branch_dictionary {Q : AdmissibleFlatSources R}
    (P : Packet R Q) (u : R.A.UnitQuotient) (y : R.A.G) :
    P.branch u y =
      (R.A.correctionLS R.probe.correction.Λ R.probe.correction.G
        R.probe.correction.η_id y : ℂ) *
      (paperHilbert R
        (QuotientGroup.mk' R.A.sixthPowers
          (R.A.diagonal (R.probe.unitReps.representative u).val))
        (QuotientGroup.mk' R.A.sixthPowers y))⁻¹ := by
  rw [P.branch_global, paperHilbert_on_representatives, inv_inv]

/-- Exact reflected sheet integrand in the paper convention. -/
theorem sheetIntegrand_dictionary {Q : AdmissibleFlatSources R}
    (T : Realization R Q) (P : Packet R Q)
    (u : R.A.UnitQuotient) (κ : R.A.V) (y : R.A.G) :
    T.sheetIntegrand P u κ y =
      (if κ * (QuotientGroup.mk' R.A.sixthPowers y)⁻¹ ∈ R.probe.correction.B
        then 1 else 0) *
      paperHilbert R κ (QuotientGroup.mk' R.A.sixthPowers y) ^ 2 *
      P.branch u y * fourier R Q.dq (T.theta u)
        (diagonal R y * KPRationalAdelicSplitting.pglW
          F R.A.zeta12 R.A.primitive_zeta12) := by
  unfold Realization.sheetIntegrand
  rw [correction_inverse_square]

end ThetaGlobal.GlobalProjectConvention
