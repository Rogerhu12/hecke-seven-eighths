import ThetaGlobal.PrimalLimitProject
import ThetaGlobal.ReflectedLimitProject

/-!
# The final extensional limit step for the actual marked theorem

This module is deliberately conditional: an independently established family
of positive-parameter regularized identities implies the literal annular
reflection by uniqueness of limits. The regularized identities themselves
must come from the ACTUAL fixed-profile theta source and the proved scalar
deconvolution/Fubini machinery. They are not asserted here.

`ActualAnnularTransfer` constructs these identities from the literal seed;
`GlobalProjectLiteralSeed` supplies that seed from the actual source. This
module keeps the limit argument separate from those arithmetic steps.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace ThetaGlobal.ActualRegularizerRemoval

open NumberField IsDedekindDomain Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators Topology nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [Finite (SixthLocalClasses K S)]
variable (D : ThetaArithmeticData K S) (d : MarkedDatum K S)
variable (F : FiniteMellinData K S) (θ : HeckeCharacter K)

/-- Exact regularized marked equality, supplied by fixed-profile automorphy
and scalar Fubini in `ActualAnnularTransfer.regularized_identity`.
It is a proposition about positive regularization parameters, not a theorem. -/
def RegularizedMarkedIdentity (V : SmoothAnnularTest) (ε X : ℝ) : Prop :=
  completedThetaSum K S D θ (rowElement K S D d) d.puncture d.marks
    (RegularizedTestProject.regularizedTest V ε 0) X =
  ∑' i : ReflectionIndex K S d, ReflectedLimitProject.term K S D d θ
    (fun κ y => RegularizedKernelProject.regularizedKernel F θ
      (QuotientGroup.mk d.rowUnit) κ V ε 0 y) X i

/-- The actual marked annular identity follows once the independently derived
positive-regularizer identities are supplied. Both series convergence and both
passages to the limit are proved, using the literal actual arithmetic indices.

This theorem is an extensional final step. Its regularized-identity premise
is discharged by `ActualAnnularTransfer`, using the separately derived seed. -/
theorem marked_reflection_of_regularized_identities
    (hF : FiniteMellinAdmissible K S F) (V : SmoothAnnularTest)
    (ε : ℕ → ℝ) (hεpos : ∀ n, 0 < ε n) (hε₁ : ∀ n, ε n ≤ 1)
    (hε : Tendsto ε atTop (𝓝 0)) {X : ℝ} (hX : 0 < X)
    (hregularized : ∀ n, RegularizedMarkedIdentity K S D d F θ V (ε n) X) :
    Summable (completedTerm K S D θ (rowElement K S D d)
      d.puncture d.marks V.toFun X) ∧
      Summable (fun i : ReflectionIndex K S d =>
        reflectedTerm K S D d i F θ V.toFun X) ∧
      completedThetaSum K S D θ (rowElement K S D d)
        d.puncture d.marks V.toFun X =
        ∑' i : ReflectionIndex K S d, reflectedTerm K S D d i F θ V.toFun X := by
  have hε₀ : ∀ n, 0 ≤ ε n := fun n => (hεpos n).le
  have hp := PrimalLimitProject.regularized_completed_sum_tendsto
    K S D θ (rowElement K S D d) d.puncture d.marks V ε hε₀ hε₁ hε hX
  have hr := ReflectedLimitProject.regularized_reflected_sum_tendsto
    K S D d θ F hF V ε hε₀ hε₁ hε hX
  refine ⟨hp.1, hr.1, ?_⟩
  exact tendsto_nhds_unique (hp.2.congr (fun n => hregularized n)) hr.2

end ThetaGlobal.ActualRegularizerRemoval

