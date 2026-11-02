import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SignedDirectFirstSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalFirstDualCalibration

set_option linter.unusedSectionVars false

/-!
# Direct first terminals from original windows

This entrance has no prime-pool parameter and no slot-count case split.
The same original whole-factor tuple and profile/mask windows compute
both terminal amplitudes. The pure dual zero uses the actual powerful
product diagonal; the original zero is handled by its whole Gram sign.

The final theorem supplies both the raw finite-row exit and its direct
normalized exit, on the same source and the same chosen cutoff. Neither
an aggregate terminal bound nor a vanishing-profile condition is given.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local notation "Lattice" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
local instance directFirstDualTerminalCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

/-- The direct source's two actual terminals are bounded from original
individual windows. The zero amplitude is calculated internally from
the original profile, norm and complete principal-mask data. -/
theorem actual_direct_first_dual_terminal_cost_bound
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ sZero : Finset (ℕ × ℕ), ∃ Czero : ℝ, 0 < Czero ∧
    ∀ (sTail : Finset (ℕ × ℕ)) (Ctail : ℝ), 0 ≤ Ctail →
    ∀ (Z : ℝ),
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ (s : ActualDirectFirstSource (E := E) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX)
      (normBound Lmax Nsave decay : ℝ), 1 < decay →
    ∀ (T : FirstDualOriginalWindows (hΓ := hΓ) C s.columns s.ideal s.block s.profiles
      s.radius s.mask sTail sZero k Z X normBound Lmax Nsave decay)
      (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ)
      (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0),
      s.dualZeroCost hDiff + Ctail * X ^ (1 - decay) * s.tailCost sTail ≤
        T.cost hB δ hδ ε (Ctail * (2 * firstTailFieldConstant K * idealCountConstant K ^ k)) Czero := by
  sorry

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
variable (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- A direct, pool-free first producer with both original terminal
costs proved from primitive windows. This includes zero original slots
without choosing a different schema or an auxiliary pool. -/
theorem actual_parent_direct_first_dual_terminal_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (rowBallSize normBound : ℝ) (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) (Lmax Nsave ξmax : ℝ) (hξmax : 0 < ξmax) :
    ∃ (decay : ℝ) (hdecay : 1 < decay),
      decay = tailDecayForWidth Lmax Nsave ξmax ∧
      firstTailCutoffExponent Lmax Nsave decay ≤ ξmax ∧
    ∃ sTail sZero : Finset (ℕ × ℕ), ∃ Cerror Czero : ℝ,
      0 ≤ Cerror ∧ 0 < Czero ∧
    ∀ (Z : ℝ),
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ s : ActualDirectFirstSource (E := E) hΓ μv C Z
      (rowBallFiniteFamily K A.Sf rowBallSize) centered d a t Y₁ Y₂ X hX,
    ∀ (coefficient : s.Column → ℂ),
      (∀ i j, s.profiles i j = (coefficient i * star (coefficient j)) •
        CanonicalRowBall.archTest K A.Sf rowBallSize) →
    ∀ T : FirstDualOriginalWindows (hΓ := hΓ) C s.columns s.ideal s.block s.profiles
      s.radius s.mask sTail sZero k Z X normBound Lmax Nsave decay,
      X ≤ Z ^ ξmax ∧
      pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
        (s.fiber : ℝ) * (T.cost hB δ hδ ε Cerror Czero + s.rawRowCost hDiff) ∧
      ∀ N : s.Normalization,
        pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
          (s.fiber : ℝ) * (T.cost hB δ hδ ε Cerror Czero + s.linearizedCost hDiff N) := by
  sorry

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_direct_first_dual_terminal_cost_bound
#print axioms HeckeSkeleton.Moments.EngineStep.actual_parent_direct_first_dual_terminal_bound
