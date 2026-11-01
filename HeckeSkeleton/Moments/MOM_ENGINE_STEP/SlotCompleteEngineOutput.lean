import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormCompleteEngineOutput
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SlotMeshPreservation

/-!
# Original slot lengths in the complete public engine output

The already selected normalized children retain an injection into the
original parent slots and the exact length of every surviving slot.
Consequently every mesh valid for the parent remains valid for these
same children.  The raw input is the original per-source slot dictionary,
before either capacity deletion; no bound on a produced child is assumed.

The constructor below is the final packaging of the same actual family.
Its parent, terminal and mass inequalities are arguments only to this
packaging helper and must be proved by the full engine provider.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open DedekindZetaZeroFree

open NumberField MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

/-- All original norm and arithmetic recipes, together with the actual
retained-slot injection.  The mesh itself is not an extra field. -/
structure SlotCompleteEngineChildAdmissible (A : SArithmeticData K)
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
    (Q : Type*) (parent : MomentData K ω ψ)
    (rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)) (window : Set ℝ)
    (seminorms : Finset (ℕ × ℕ)) (Z : ℝ)
    (d : MomentData K ω ψ) (a : RealParameters) : Prop where
  normComplete : NormCompleteEngineChildAdmissible A P R Q parent
    rowDomain window seminorms Z d a
  slots : Nonempty (SlotLengthEmbedding parent d)

namespace SlotCompleteEngineChildAdmissible

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {Q : Type*} {parent d : MomentData K ω ψ} {a : RealParameters} {Z : ℝ}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {window : Set ℝ}
variable {seminorms : Finset (ℕ × ℕ)}
variable (h : SlotCompleteEngineChildAdmissible A P R Q parent
  rowDomain window seminorms Z d a)

include h

def slotEmbedding : SlotLengthEmbedding parent d := Classical.choice h.slots

theorem slot_length (i : Fin d.geometry.slotCount) :
    (d.geometry.slots i).length =
      (parent.geometry.slots (h.slotEmbedding.index i)).length :=
  h.slotEmbedding.length_eq i

/-- Any original mesh is preserved, independently of the auxiliary
mesh used by the capacity argument. -/
theorem fitsMesh {mesh : ℝ} (hparent : parent.geometry.fitsMesh mesh) :
    d.geometry.fitsMesh mesh := h.slotEmbedding.fitsMesh hparent

theorem slot_count : d.geometry.slotCount ≤ parent.geometry.slotCount :=
  h.slotEmbedding.slotCount_le

end SlotCompleteEngineChildAdmissible

namespace ActualNormalizedPairFamily

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {V Λ Q : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : ℝ}
variable {family : ActualNormalizedPairFamily A σ V Λ ω ψ Z} {labels : Finset Λ}
variable {parent : MomentData K ω ψ} {a : RealParameters} {step : ℝ}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {window : Set ℝ}
variable {seminorms : Finset (ℕ × ℕ)}

theorem slot_complete_left_admissible
    (geometry : family.OutputGeometry labels parent a step rowDomain window seminorms)
    (rows : family.CompleteRowInputs (P := P) (R := R) labels)
    (characters : family.ParentCharacterInputs labels parent)
    (profiles : family.NormProfileInputs labels)
    (arithmetic : family.ArithmeticAtomInputs labels Q)
    (slots : family.ParentSlotDictionaries labels parent)
    (b : family.active labels) (ξ : V) :
    SlotCompleteEngineChildAdmissible A P R Q parent rowDomain window seminorms Z
      (family.leftData labels b ξ) (family.leftParameters labels b) where
  normComplete := norm_complete_left_admissible geometry rows characters profiles arithmetic b ξ
  slots := ⟨slots.leftEmbedding b ξ⟩

theorem slot_complete_right_admissible
    (geometry : family.OutputGeometry labels parent a step rowDomain window seminorms)
    (rows : family.CompleteRowInputs (P := P) (R := R) labels)
    (characters : family.ParentCharacterInputs labels parent)
    (profiles : family.NormProfileInputs labels)
    (arithmetic : family.ArithmeticAtomInputs labels Q)
    (slots : family.ParentSlotDictionaries labels parent)
    (b : family.active labels) (ξ : V) :
    SlotCompleteEngineChildAdmissible A P R Q parent rowDomain window seminorms Z
      (family.rightData labels b ξ) (family.rightParameters labels b) where
  normComplete := norm_complete_right_admissible geometry rows characters profiles arithmetic b ξ
  slots := ⟨slots.rightEmbedding b ξ⟩

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

/-- Package the same family with its original slot injection exposed.
The active carrier, capacity choices, actual Fourier measures and
evaluation point zero are unchanged. -/
def PairedEngineConclusion.ofSlotCompleteActualNormalizedFamily
    (family : ActualNormalizedPairFamily A σ (WithLp 2 (U × E)) Λ ω ψ Z)
    (labels : Finset Λ)
    (geometry : family.OutputGeometry labels d a step rowDomain window seminorms)
    (rows : family.CompleteRowInputs (P := P) (R := R) labels)
    (characters : family.ParentCharacterInputs labels d)
    (profiles : family.NormProfileInputs labels)
    (arithmetic : family.ArithmeticAtomInputs labels Q)
    (slots : family.ParentSlotDictionaries labels d)
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
        (SlotCompleteEngineChildAdmissible A P R Q d rowDomain window seminorms Z) := by
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
    (ActualNormalizedPairFamily.slot_complete_left_admissible
      geometry rows characters profiles arithmetic slots)
    (ActualNormalizedPairFamily.slot_complete_right_admissible
      geometry rows characters profiles arithmetic slots)
    geometry.left_capacity geometry.right_capacity
    firstZero secondZero exceptional tail
    hfirstZero hsecondZero hexceptional htail hterminals
    convergence.left_integrable convergence.right_integrable convergence.cauchy_integrable
    hparent hmass

end Output
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SlotCompleteEngineChildAdmissible.fitsMesh
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.slot_complete_left_admissible
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.slot_complete_right_admissible
#print axioms HeckeSkeleton.Moments.EngineStep.PairedEngineConclusion.ofSlotCompleteActualNormalizedFamily
