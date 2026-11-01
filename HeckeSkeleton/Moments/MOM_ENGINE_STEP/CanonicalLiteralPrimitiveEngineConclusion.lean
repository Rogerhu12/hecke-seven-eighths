import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FiniteEngineOutput
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.MovingEngineOutput

/-!
# The conclusion of the complete literal source family

The direct and amplified producers have already fixed the same active
children, their original kernel measures, their geometry and their
individual analytic certificates. This final internal packaging step
uses those proved output facts. It derives the Cauchy integrability
from the two child energies and reindexes precisely the actual active
carrier to `Fin n`.

The parent, terminal and mass inequalities here are the outputs of the
source and arithmetic estimates. They are not primitive hypotheses of
the engine theorem.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Analysis.ActualSIntegerMoments (ActualSIntegerOrbit)
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {ω ψ : HeckeCharacter K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {V Λ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Fintype Λ]
variable {centered : Bool} {d : MomentData K ω ψ} {a : RealParameters}
variable {Z t Y₁ Y₂ step ε terminalExponent C control : ℝ}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {window : Set ℝ} {orders : Finset (ℕ × ℕ)}

/-- Package the proved complete-family estimates without changing its
labels, child choices, original measures or active admissibility. -/
def PairedEngineConclusion.ofLiteralPrimitiveFamily
    (family : ActualNormalizedPairFamily A σ V Λ ω ψ Z)
    (μ : Λ → Measure V)
    (geometry : family.OutputGeometry Finset.univ d a step rowDomain window orders)
    (moving : ∀ (b : family.active Finset.univ) (ξ : V),
      MovingEngineChildAdmissible A P R
          (ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) d
          rowDomain window orders Z
          (family.leftData Finset.univ b ξ) (family.leftParameters Finset.univ b) ∧
        MovingEngineChildAdmissible A P R
          (ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) d
          rowDomain window orders Z
          (family.rightData Finset.univ b ξ) (family.rightParameters Finset.univ b))
    (children : ∀ b : family.active Finset.univ,
      Integrable (fun ξ => normalizedPairedEnergy
          (family.leftData Finset.univ b ξ) (family.leftParameters Finset.univ b) Z 0)
          (family.kernel Finset.univ μ (a.m + a.q) b) ∧
        Integrable (fun ξ => normalizedPairedEnergy
          (family.rightData Finset.univ b ξ) (family.rightParameters Finset.univ b) Z 0)
          (family.kernel Finset.univ μ (a.m + a.q) b))
    (hZ : 0 < Z)
    (firstZero secondZero exceptional tail : ℝ)
    (hfirstZero : 0 ≤ firstZero) (hsecondZero : 0 ≤ secondZero)
    (hexceptional : 0 ≤ exceptional) (htail : 0 ≤ tail)
    (hterminals : firstZero + secondZero + exceptional + tail ≤
      C * control * Z ^ terminalExponent)
    (hparent : pairedStageEnergy centered d a Z t Y₁ Y₂ / Z ^ (a.m + a.q) ≤
      firstZero + secondZero + exceptional + tail +
        ∑ b : family.active Finset.univ, ∫ ξ,
          Real.sqrt (normalizedPairedEnergy (family.leftData Finset.univ b ξ)
            (family.leftParameters Finset.univ b) Z 0) *
          Real.sqrt (normalizedPairedEnergy (family.rightData Finset.univ b ξ)
            (family.rightParameters Finset.univ b) Z 0)
              ∂family.kernel Finset.univ μ (a.m + a.q) b)
    (hmass : (∀ b : family.active Finset.univ,
        IsFiniteMeasure (family.kernel Finset.univ μ (a.m + a.q) b)) ∧
      (∑ b : family.active Finset.univ,
        (family.kernel Finset.univ μ (a.m + a.q) b).real Set.univ) ≤
          C * control * Z ^ ε) :
    PairedEngineConclusion (Ω := V) centered d a
      Z t Y₁ Y₂ step ε terminalExponent C control
        (MovingEngineChildAdmissible A P R
          (ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) d
          rowDomain window orders Z) := by
  exact PairedEngineConclusion.ofFintype
    (family.leftData Finset.univ) (family.rightData Finset.univ)
    (family.leftParameters Finset.univ) (family.rightParameters Finset.univ)
    (fun _ _ => 0) (fun _ _ => 0)
    (family.kernel Finset.univ μ (a.m + a.q))
    (fun _ _ => rfl) (fun _ _ => rfl) hmass.1
    geometry.left_width geometry.right_width
    geometry.left_width_nonneg geometry.right_width_nonneg
    geometry.left_plain_left_nonneg geometry.left_plain_right_nonneg
    geometry.right_plain_left_nonneg geometry.right_plain_right_nonneg
    geometry.left_length geometry.right_length
    geometry.left_kappa geometry.right_kappa
    geometry.left_slots geometry.right_slots
    geometry.left_theta geometry.right_theta
    geometry.left_slot_characters geometry.right_slot_characters
    (fun b ξ => (moving b ξ).1) (fun b ξ => (moving b ξ).2)
    geometry.left_capacity geometry.right_capacity
    firstZero secondZero exceptional tail
    hfirstZero hsecondZero hexceptional htail hterminals
    (fun b => (children b).1) (fun b => (children b).2)
    (fun b => actual_normalized_pair_integrable
      (family.kernel Finset.univ μ (a.m + a.q) b)
      (family.leftData Finset.univ b) (family.rightData Finset.univ b)
      (family.leftParameters Finset.univ b) (family.rightParameters Finset.univ b)
      (fun _ => 0) (fun _ => 0) Z hZ (children b).1 (children b).2)
    hparent hmass.2

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.PairedEngineConclusion.ofLiteralPrimitiveFamily
