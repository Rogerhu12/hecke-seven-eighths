import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CurriedNormalizedSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedOutputConditions
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.MovingEngineOutput

/-!
# Complete output facts for the same curried family

A source factory fixes its children before the individual analytic
certificates are supplied. This record retains the actual output geometry,
the complete moving-child admissibility on its active labels, and
integrability under the specified original kernel measure. It introduces
neither another child choice nor a new source estimate.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ω ψ : HeckeCharacter K} {Z : ℝ}

namespace CurriedNormalizedFamily

structure Output (f : CurriedNormalizedFamily A σ V ω ψ Z)
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
    (parent : MomentData K ω ψ) (a : RealParameters) (step : ℝ)
    (rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)) (window : Set ℝ)
    (orders : Finset (ℕ × ℕ)) (μ : f.Label → Measure V) : Prop where
  geometry : ∀ input : f.Input,
    (f.family input).OutputGeometry Finset.univ parent a step rowDomain window orders
  moving : ∀ (input : f.Input) (b : (f.family input).active Finset.univ) (ξ : V),
    MovingEngineChildAdmissible A P R
        (ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) parent
        rowDomain window orders Z
        ((f.family input).leftData Finset.univ b ξ)
        ((f.family input).leftParameters Finset.univ b) ∧
      MovingEngineChildAdmissible A P R
        (ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) parent
        rowDomain window orders Z
        ((f.family input).rightData Finset.univ b ξ)
        ((f.family input).rightParameters Finset.univ b)
  integrable : ∀ (input : f.Input) (parentWidth : ℝ)
      (b : (f.family input).active Finset.univ),
    Integrable (fun ξ => normalizedPairedEnergy
      ((f.family input).leftData Finset.univ b ξ)
      ((f.family input).leftParameters Finset.univ b) Z 0)
      ((f.family input).kernel Finset.univ μ parentWidth b) ∧
    Integrable (fun ξ => normalizedPairedEnergy
      ((f.family input).rightData Finset.univ b ξ)
      ((f.family input).rightParameters Finset.univ b) Z 0)
      ((f.family input).kernel Finset.univ μ parentWidth b)

namespace Output

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {parent : MomentData K ω ψ} {a a' : RealParameters} {step : ℝ}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {window : Set ℝ}
variable {orders : Finset (ℕ × ℕ)}

/-- Read the literal producer's three curried proofs at the same
individual analytic certificates. -/
def ofCurried {Λ L R' : Type} [Fintype Λ]
    {hl : L → Prop} {hr : R' → Prop}
    {make : ∀ l r, hl l → hr r → ActualNormalizedPairFamily A σ V Λ ω ψ Z}
    {μ : Λ → Measure V}
    (geometry : ∀ l r hleft hright,
      (make l r hleft hright).OutputGeometry Finset.univ
        parent a step rowDomain window orders)
    (moving : ∀ l r hleft hright
      (b : (make l r hleft hright).active Finset.univ) (ξ : V),
      MovingEngineChildAdmissible A P R
          (ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) parent
          rowDomain window orders Z
          ((make l r hleft hright).leftData Finset.univ b ξ)
          ((make l r hleft hright).leftParameters Finset.univ b) ∧
        MovingEngineChildAdmissible A P R
          (ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) parent
          rowDomain window orders Z
          ((make l r hleft hright).rightData Finset.univ b ξ)
          ((make l r hleft hright).rightParameters Finset.univ b))
    (integrable : ∀ l r hleft hright (parentWidth : ℝ)
      (b : (make l r hleft hright).active Finset.univ),
      Integrable (fun ξ => normalizedPairedEnergy
        ((make l r hleft hright).leftData Finset.univ b ξ)
        ((make l r hleft hright).leftParameters Finset.univ b) Z 0)
        ((make l r hleft hright).kernel Finset.univ μ parentWidth b) ∧
      Integrable (fun ξ => normalizedPairedEnergy
        ((make l r hleft hright).rightData Finset.univ b ξ)
        ((make l r hleft hright).rightParameters Finset.univ b) Z 0)
        ((make l r hleft hright).kernel Finset.univ μ parentWidth b)) :
    (CurriedNormalizedFamily.ofCurried make).Output P R
      parent a step rowDomain window orders μ where
  geometry input := geometry input.1.val input.2.val input.1.property input.2.property
  moving input := moving input.1.val input.2.val input.1.property input.2.property
  integrable input := integrable input.1.val input.2.val input.1.property input.2.property

/-- Splitting the original row/support width differently changes no
chosen child, mask, profile or kernel. Only the four parent comparisons
mention those parameters. -/
def withParentParameters {f : CurriedNormalizedFamily A σ V ω ψ Z}
    {μ : f.Label → Measure V}
    (O : f.Output P R parent a step rowDomain window orders μ)
    (hwidth : a.m + a.q = a'.m + a'.q) (hkappa : a.κ = a'.κ) :
    f.Output P R parent a' step rowDomain window orders μ where
  geometry input := {
    O.geometry input with
    left_width := fun b => by rw [← hwidth]; exact (O.geometry input).left_width b
    right_width := fun b => by rw [← hwidth]; exact (O.geometry input).right_width b
    left_kappa := fun b => ((O.geometry input).left_kappa b).trans hkappa
    right_kappa := fun b => ((O.geometry input).right_kappa b).trans hkappa }
  moving := O.moving
  integrable := O.integrable

end Output
end CurriedNormalizedFamily
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CurriedNormalizedFamily.Output.ofCurried
#print axioms HeckeSkeleton.Moments.EngineStep.CurriedNormalizedFamily.Output.withParentParameters
