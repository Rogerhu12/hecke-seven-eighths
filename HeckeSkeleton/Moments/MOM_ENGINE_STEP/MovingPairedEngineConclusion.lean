import HeckeSkeleton.Moments.MOM_ENGINE_STEP.MovingEngineOutput

/-!
# Package the actual finite family with its complete moving admissibility

The selected normalized children already carry their original moving
factors, remaining mask, complete row budget, norm profiles, arithmetic
atoms and retained-slot injection. This constructor exposes that full
admissibility in the public conclusion while preserving the same active
family, chosen children, actual Fourier kernels and zero evaluation
heights.

This is a packaging helper. The parent, terminal and mass inequalities
are supplied only after the actual source producer proves them. It does
not replace the primitive engine theorem or add an estimate to the
original moving-row inputs.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}
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

/-- Reindex the same actual family to `Fin n`, retaining complete
moving-row admissibility for both existing children. All numerical
estimates are already proved inputs to this final packaging step. -/
def PairedEngineConclusion.ofMovingActualNormalizedFamily
    (family : ActualNormalizedPairFamily A σ (WithLp 2 (U × E)) Λ ω ψ Z)
    (labels : Finset Λ)
    (geometry : family.OutputGeometry labels d a step rowDomain window seminorms)
    (rows : family.MovingRowInputs (P := P) (R := R) labels)
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
        (MovingEngineChildAdmissible A P R Q d rowDomain window seminorms Z) := by
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
    (ActualNormalizedPairFamily.moving_left_admissible
      geometry rows characters profiles arithmetic slots)
    (ActualNormalizedPairFamily.moving_right_admissible
      geometry rows characters profiles arithmetic slots)
    geometry.left_capacity geometry.right_capacity
    firstZero secondZero exceptional tail
    hfirstZero hsecondZero hexceptional htail hterminals
    convergence.left_integrable convergence.right_integrable convergence.cauchy_integrable
    hparent hmass

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.PairedEngineConclusion.ofMovingActualNormalizedFamily
