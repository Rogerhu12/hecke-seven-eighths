import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CompleteRowRecipe
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CharacterRecipePreservation
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedEngineOutput

/-!
# Complete arithmetic admissibility of the same actual output family

The original probe and row-character input are fixed parameters of the
public admissibility predicate.  Every allowed complete ideal retains
its literal arithmetic character, and the plain background is the
original parent's background or its whole conjugate.

These facts are derived from the raw CompleteRowInputs and original
ParentCharacterRecipe, through the already selected normalized capacity
children.  No new child, kernel, twist or finite carrier is chosen.  The
final constructor only packages estimates already proved by the source
producer; complete admissibility is not among its input estimates.
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

/-- The arithmetic rows use the fixed original probe and row recipe.
The complete-mask product budget and fixed normalized profile window
are the existing engine admissibility fields. -/
structure CompleteEngineChildAdmissible (A : SArithmeticData K)
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
    (parent : MomentData K ω ψ)
    (rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)) (window : Set ℝ)
    (seminorms : Finset (ℕ × ℕ)) (Z : ℝ)
    (d : MomentData K ω ψ) (a : RealParameters) : Prop where
  engine : EngineChildAdmissible A rowDomain window seminorms Z d a
  exterior : ∀ u, d.allowedRow u →
    completeIdealIsExterior K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u
  character : ∀ u, d.allowedRow u →
    ∃ sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
      d.rowCharacter u =
        completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R sector u
  plain_background : d.plainBackground = parent.plainBackground ∨
    d.plainBackground = parent.plainBackground⁻¹

namespace CompleteEngineChildAdmissible

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {parent d : MomentData K ω ψ} {a : RealParameters} {Z : ℝ}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {window : Set ℝ}
variable {seminorms : Finset (ℕ × ℕ)}
variable (h : CompleteEngineChildAdmissible A P R parent rowDomain window seminorms Z d a)

/-- This is the original full-row identification used by reflection,
obtained directly from public output admissibility. -/
theorem identify (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hu : u ∈ pairedRows d a Z) :
    ∃ v : ExteriorIdeal K (A.Sf : Set (HeightOneSpectrum (𝓞 K))), v.val = u ∧
      ∃ sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
        d.rowCharacter u =
          completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R sector u := by
  have hallowed := ((d.rows_spec _ u).1 (Finset.mem_filter.mp hu).1).1
  exact ⟨⟨u, h.exterior u hallowed⟩, rfl, h.character u hallowed⟩

end CompleteEngineChildAdmissible

namespace ActualNormalizedPairFamily

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {V Λ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : ℝ}
variable (family : ActualNormalizedPairFamily A σ V Λ ω ψ Z) (labels : Finset Λ)

/-- Each whole-conjugation choice is made on the original calibration,
before the Fourier variable.  The separate CompleteRowInputs identify
the row function on every allowed row with the fixed arithmetic recipe. -/
structure ParentCharacterInputs (parent : MomentData K ω ψ) : Prop where
  left : ∀ b ∈ labels, ∃ conjugated row,
    ParentCharacterRecipe parent (family.leftCalibration b).data conjugated row
  right : ∀ b ∈ labels, ∃ conjugated row,
    ParentCharacterRecipe parent (family.rightCalibration b).data conjugated row

namespace ParentCharacterInputs

variable {family labels} {parent : MomentData K ω ψ}
variable (raw : family.ParentCharacterInputs labels parent)

theorem left_background (b : family.active labels) (ξ : V) :
    (family.leftData labels b ξ).plainBackground = parent.plainBackground ∨
      (family.leftData labels b ξ).plainBackground = parent.plainBackground⁻¹ := by
  obtain ⟨conjugated, row, recipe⟩ :=
    raw.left b.val (Finset.mem_filter.mp b.property).1
  have h := ((family.leftChild labels b).frozen_parentCharacterRecipe recipe).background ξ
  cases hc : conjugated with
  | false => exact Or.inl (by simpa [parentPlainCharacter, hc] using h)
  | true => exact Or.inr (by simpa [parentPlainCharacter, hc] using h)

theorem right_background (b : family.active labels) (ξ : V) :
    (family.rightData labels b ξ).plainBackground = parent.plainBackground ∨
      (family.rightData labels b ξ).plainBackground = parent.plainBackground⁻¹ := by
  obtain ⟨conjugated, row, recipe⟩ :=
    raw.right b.val (Finset.mem_filter.mp b.property).1
  have h := ((family.rightChild labels b).frozen_parentCharacterRecipe recipe).background ξ
  cases hc : conjugated with
  | false => exact Or.inl (by simpa [parentPlainCharacter, hc] using h)
  | true => exact Or.inr (by simpa [parentPlainCharacter, hc] using h)

end ParentCharacterInputs

variable {family labels} {parent : MomentData K ω ψ} {a : RealParameters} {step : ℝ}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {window : Set ℝ}
variable {seminorms : Finset (ℕ × ℕ)}

/-- The left output is the same frozen child selected by this family.
Its sector is exactly the original raw recipe's sector, fixed before ξ. -/
theorem complete_left_admissible
    (geometry : family.OutputGeometry labels parent a step rowDomain window seminorms)
    (rows : family.CompleteRowInputs (P := P) (R := R) labels)
    (characters : family.ParentCharacterInputs labels parent)
    (b : family.active labels) (ξ : V) :
    CompleteEngineChildAdmissible A P R parent rowDomain window seminorms Z
      (family.leftData labels b ξ) (family.leftParameters labels b) where
  engine := geometry.left_admissible b ξ
  exterior u hu := (rows.leftRecipe b).exterior ξ u hu
  character u hu :=
    ⟨(rows.leftRecipe b).sector u, (rows.leftRecipe b).character ξ u hu⟩
  plain_background := characters.left_background b ξ

theorem complete_right_admissible
    (geometry : family.OutputGeometry labels parent a step rowDomain window seminorms)
    (rows : family.CompleteRowInputs (P := P) (R := R) labels)
    (characters : family.ParentCharacterInputs labels parent)
    (b : family.active labels) (ξ : V) :
    CompleteEngineChildAdmissible A P R parent rowDomain window seminorms Z
      (family.rightData labels b ξ) (family.rightParameters labels b) where
  engine := geometry.right_admissible b ξ
  exterior u hu := (rows.rightRecipe b).exterior ξ u hu
  character u hu :=
    ⟨(rows.rightRecipe b).sector u, (rows.rightRecipe b).character ξ u hu⟩
  plain_background := characters.right_background b ξ

end ActualNormalizedPairFamily

section Output

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {U E Λ : Type*}
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

/-- The same finite family, actual kernels and zero twists have complete
arithmetic admissibility.  The producer supplies its already proved
source, terminal and mass estimates; the stronger character fields are
derived here from original one-row recipes, not assumed for the output. -/
def PairedEngineConclusion.ofCompleteActualNormalizedFamily
    (family : ActualNormalizedPairFamily A σ (WithLp 2 (U × E)) Λ ω ψ Z)
    (labels : Finset Λ)
    (geometry : family.OutputGeometry labels d a step rowDomain window seminorms)
    (rows : family.CompleteRowInputs (P := P) (R := R) labels)
    (characters : family.ParentCharacterInputs labels d)
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
        (CompleteEngineChildAdmissible A P R d rowDomain window seminorms Z) := by
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
    (ActualNormalizedPairFamily.complete_left_admissible geometry rows characters)
    (ActualNormalizedPairFamily.complete_right_admissible geometry rows characters)
    geometry.left_capacity geometry.right_capacity
    firstZero secondZero exceptional tail
    hfirstZero hsecondZero hexceptional htail hterminals
    convergence.left_integrable convergence.right_integrable convergence.cauchy_integrable
    hparent hmass

end Output
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteEngineChildAdmissible.identify
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.complete_left_admissible
#print axioms HeckeSkeleton.Moments.EngineStep.PairedEngineConclusion.ofCompleteActualNormalizedFamily
