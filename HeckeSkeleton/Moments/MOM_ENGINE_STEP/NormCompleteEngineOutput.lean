import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CompleteEngineOutput
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentArithmeticAtoms

/-!
# Norm and arithmetic recipes in the same public child family

This strengthens the public output with original per-profile and
per-ideal dictionaries transported through the actual child operations.
It does not replace the source provider: positivity of the fixed
orbital majorant and identification of the phase arrays with the actual
periodic columns remain the original MOM_UNIFORM and MOM_BASE inputs.

An ordinary power-window replacement can reuse these arithmetic atoms
and substitute its two literal norm tests.  No mixed source Gram
identity or final parent estimate is assumed by the new recipes.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open DedekindZetaZeroFree

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

/-- The original orbit type is a fixed parameter.  The two extra fields
are identities on profiles and individual arithmetic atoms, not source
inequalities or an assertion of recursive eligibility. -/
structure NormCompleteEngineChildAdmissible (A : SArithmeticData K)
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
    (Q : Type*) (parent : MomentData K ω ψ)
    (rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)) (window : Set ℝ)
    (seminorms : Finset (ℕ × ℕ)) (Z : ℝ)
    (d : MomentData K ω ψ) (a : RealParameters) : Prop where
  complete : CompleteEngineChildAdmissible A P R parent rowDomain window seminorms Z d a
  profiles : Nonempty (NormProfileRecipe (fun _ : PUnit => d))
  arithmetic : Nonempty (ParentArithmeticAtoms Q d)

namespace NormCompleteEngineChildAdmissible

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {Q : Type*} {parent d : MomentData K ω ψ} {a : RealParameters} {Z : ℝ}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {window : Set ℝ}
variable {seminorms : Finset (ℕ × ℕ)}
variable (h : NormCompleteEngineChildAdmissible A P R Q parent
  rowDomain window seminorms Z d a)

/-- The next original constant-profile source is computed at arbitrary
new scales and times.  Its periodic-column identification is supplied
separately by the original single-column arithmetic provider. -/
def constantAtoms (next : RealParameters) (base time : ℝ) :
    ParentConstantAtoms Q d next base time :=
  (Classical.choice h.arithmetic).constantAtoms (Classical.choice h.profiles) next base time

def withPlainTests (next : RealParameters) (base time : ℝ)
    (W₁ W₂ : IdealTest K) (f₁ f₂ : ℝ → ℂ)
    (hW₁ : ∀ u ∈ pairedRows d next base, ∀ y, W₁.profile u time y = f₁ y)
    (hW₂ : ∀ u ∈ pairedRows d next base, ∀ y, W₂.profile u time y = f₂ y) :
    ParentConstantAtoms (ω := ω) (ψ := ψ) Q { d with plainTest₁ := W₁, plainTest₂ := W₂ } next base time :=
  (h.constantAtoms next base time).withPlainTests W₁ W₂ f₁ f₂ hW₁ hW₂

end NormCompleteEngineChildAdmissible

namespace ActualNormalizedPairFamily

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {V Λ Q : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : ℝ}
variable {family : ActualNormalizedPairFamily A σ V Λ ω ψ Z} {labels : Finset Λ}
variable {parent : MomentData K ω ψ} {a : RealParameters} {step : ℝ}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {window : Set ℝ}
variable {seminorms : Finset (ℕ × ℕ)}

theorem norm_complete_left_admissible
    (geometry : family.OutputGeometry labels parent a step rowDomain window seminorms)
    (rows : family.CompleteRowInputs (P := P) (R := R) labels)
    (characters : family.ParentCharacterInputs labels parent)
    (profiles : family.NormProfileInputs labels)
    (arithmetic : family.ArithmeticAtomInputs labels Q)
    (b : family.active labels) (ξ : V) :
    NormCompleteEngineChildAdmissible A P R Q parent rowDomain window seminorms Z
      (family.leftData labels b ξ) (family.leftParameters labels b) where
  complete := complete_left_admissible geometry rows characters b ξ
  profiles := ⟨(profiles.leftRecipe b).at ξ⟩
  arithmetic := ⟨arithmetic.leftAtoms b ξ⟩

theorem norm_complete_right_admissible
    (geometry : family.OutputGeometry labels parent a step rowDomain window seminorms)
    (rows : family.CompleteRowInputs (P := P) (R := R) labels)
    (characters : family.ParentCharacterInputs labels parent)
    (profiles : family.NormProfileInputs labels)
    (arithmetic : family.ArithmeticAtomInputs labels Q)
    (b : family.active labels) (ξ : V) :
    NormCompleteEngineChildAdmissible A P R Q parent rowDomain window seminorms Z
      (family.rightData labels b ξ) (family.rightParameters labels b) where
  complete := complete_right_admissible geometry rows characters b ξ
  profiles := ⟨(profiles.rightRecipe b).at ξ⟩
  arithmetic := ⟨arithmetic.rightAtoms b ξ⟩

end ActualNormalizedPairFamily

section Output

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {U E Λ Q : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (WithLp 2 (U × E))] [BorelSpace (WithLp 2 (U × E))]
variable {centered : Bool} {d : MomentData K ω ψ} {a : RealParameters}
variable {Z t Y₁ Y₂ step ε terminalExponent C control : ℝ}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {window : Set ℝ}
variable {seminorms : Finset (ℕ × ℕ)}
variable {J₁₁ J₁₂ J₂₁ J₂₂ : ℕ}

/-- This is the same constructed family and the same kernel.  The new
raw inputs are transported through its already selected children. -/
def PairedEngineConclusion.ofNormCompleteActualNormalizedFamily
    (family : ActualNormalizedPairFamily A σ (WithLp 2 (U × E)) Λ ω ψ Z)
    (labels : Finset Λ)
    (geometry : family.OutputGeometry labels d a step rowDomain window seminorms)
    (rows : family.CompleteRowInputs (P := P) (R := R) labels)
    (characters : family.ParentCharacterInputs labels d)
    (profiles : family.NormProfileInputs labels)
    (arithmetic : family.ArithmeticAtomInputs labels Q)
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
        (NormCompleteEngineChildAdmissible A P R Q d rowDomain window seminorms Z) := by
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
    (ActualNormalizedPairFamily.norm_complete_left_admissible geometry rows characters profiles arithmetic)
    (ActualNormalizedPairFamily.norm_complete_right_admissible geometry rows characters profiles arithmetic)
    geometry.left_capacity geometry.right_capacity
    firstZero secondZero exceptional tail
    hfirstZero hsecondZero hexceptional htail hterminals
    convergence.left_integrable convergence.right_integrable convergence.cauchy_integrable
    hparent hmass

end Output
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.NormCompleteEngineChildAdmissible.constantAtoms
#print axioms HeckeSkeleton.Moments.EngineStep.PairedEngineConclusion.ofNormCompleteActualNormalizedFamily
