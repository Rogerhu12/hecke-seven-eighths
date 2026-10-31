import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedOutputConditions
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FiniteEngineOutput

/-!
# Packaging the same normalized family after its source estimates

This is the last finite reindexing used by the source-producing theorem.
The geometry and individual atom controls refer to the same constructed
family as the source, terminal and mass estimates. Both actual evaluation
heights have already been frozen into the normalized data. Integrability
is proved from the original finite atoms under the original two Fourier
measures, and both public twists are identically zero.

The three numerical estimates accepted here must be proved by the actual
source construction before this wrapper is called. This definition is not
an alternative source calibration or the public engine producing theorem.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}
variable {U E Λ : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (WithLp 2 (U × E))] [BorelSpace (WithLp 2 (U × E))]
variable {centered : Bool} {d : MomentData K ω ψ} {a : RealParameters}
variable {Z t Y₁ Y₂ step ε terminalExponent C control : ℝ}
variable {rowDomain : Set (NonzeroIdeal K)} {window : Set ℝ}
variable {seminorms : Finset (ℕ × ℕ)}
variable {J₁₁ J₁₂ J₂₁ J₂₂ : ℕ}

/-- Reindex exactly the proved active family, with no new child choice.
The source-producing theorem supplies the three estimates only after
deriving them from its original individual arithmetic/profile inputs. -/
def PairedEngineConclusion.ofActualNormalizedFamily
    (family : ActualNormalizedPairFamily A σ (WithLp 2 (U × E)) Λ ω ψ Z)
    (labels : Finset Λ)
    (geometry : family.OutputGeometry labels d a step rowDomain window seminorms)
    (atoms : family.FourierAtomControl labels J₁₁ J₁₂ J₂₁ J₂₂)
    (F₁ : Λ → 𝓢(U, ℂ)) (F₂ : Λ → 𝓢(E, ℂ)) (outer : Λ → ℝ)
    (hZ : 0 < Z)
    (firstZero secondZero exceptional tail : ℝ)
    (hfirstZero : 0 ≤ firstZero) (hsecondZero : 0 ≤ secondZero)
    (hexceptional : 0 ≤ exceptional) (htail : 0 ≤ tail)
    (hterminals : firstZero + secondZero + exceptional + tail ≤
      C * control * Z ^ terminalExponent)
    (hparent : pairedStageEnergy centered d a Z t Y₁ Y₂ / Z ^ (a.m + a.q) ≤
      firstZero + secondZero + exceptional + tail +
        ∑ b : family.active labels, ∫ ξ,
          Real.sqrt (normalizedPairedEnergy (family.leftData labels b ξ)
            (family.leftParameters labels b) Z 0) *
          Real.sqrt (normalizedPairedEnergy (family.rightData labels b ξ)
            (family.rightParameters labels b) Z 0)
              ∂family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) (a.m + a.q) b)
    (hmass : (∑ b : family.active labels,
      (family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) (a.m + a.q) b).real
        Set.univ) ≤ C * control * Z ^ ε) :
    PairedEngineConclusion (Ω := WithLp 2 (U × E)) centered d a
      Z t Y₁ Y₂ step ε terminalExponent C control
        (EngineChildAdmissible A rowDomain window seminorms Z) := by
  let convergence := atoms.outputIntegrability F₁ F₂ outer (a.m + a.q) hZ
  exact PairedEngineConclusion.ofFintype
    (family.leftData labels) (family.rightData labels)
    (family.leftParameters labels) (family.rightParameters labels)
    (fun _ _ => 0) (fun _ _ => 0)
    (family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) (a.m + a.q))
    (fun _ _ => rfl) (fun _ _ => rfl)
    convergence.finite_kernel
    geometry.left_width geometry.right_width
    geometry.left_width_nonneg geometry.right_width_nonneg
    geometry.left_plain_left_nonneg geometry.left_plain_right_nonneg
    geometry.right_plain_left_nonneg geometry.right_plain_right_nonneg
    geometry.left_length geometry.right_length
    geometry.left_kappa geometry.right_kappa
    geometry.left_slots geometry.right_slots
    geometry.left_theta geometry.right_theta
    geometry.left_slot_characters geometry.right_slot_characters
    geometry.left_admissible geometry.right_admissible
    geometry.left_capacity geometry.right_capacity
    firstZero secondZero exceptional tail
    hfirstZero hsecondZero hexceptional htail hterminals
    convergence.left_integrable convergence.right_integrable convergence.cauchy_integrable
    hparent hmass

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.PairedEngineConclusion.ofActualNormalizedFamily
