import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstAllowanceNormalization

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Canonical direct first allowances and the literal parent weight

The normalization is computed from the original first common pair.
The complete parent scalar includes its original orbital fibre, the
first Cauchy half, the original literal direct-stage fibre, the second
orbital fibre, and both independent divisor and phase coefficients.

The formulas are exact on the original dependent source carrier and
remain exact after constant common-atom extraction. They provide the
outer identity required by the same-child pointwise mass theorem.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup

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
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {E W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
local instance canonicalDirectParentWeightsCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Z : ℝ}

variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX}

namespace ActualDirectFirstSource

/-- The direct entrance computes the same original first allowances,
with no prime-pool parameter or slot-count restriction. -/
def canonicalNormalization
    (s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX)
    (hZ : 1 < Z)
    (total : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ) : s.Normalization where
  left v D _ _ := firstLeftAllowance Z (total v D) v.val.1 v.val.2
  right v D _ _ := firstRightAllowance Z (total v D) v.val.1 v.val.2
  left_pos v D _ _ := firstLeftAllowance_pos Z _ (zero_lt_one.trans hZ) _ _
  right_pos v D _ _ := firstRightAllowance_pos Z _ (zero_lt_one.trans hZ) _ _

end ActualDirectFirstSource

namespace ActualFirstSource

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}

/-- Both entrances use the same original first common allowances. -/
def canonicalNormalization
    (s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX)
    (hZ : 1 < Z)
    (total : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ) : s.Normalization where
  left v D _ _ := firstLeftAllowance Z (total v D) v.val.1 v.val.2
  right v D _ _ := firstRightAllowance Z (total v D) v.val.1 v.val.2
  left_pos v D _ _ := firstLeftAllowance_pos Z _ (zero_lt_one.trans hZ) _ _
  right_pos v D _ _ := firstRightAllowance_pos Z _ (zero_lt_one.trans hZ) _ _

end ActualFirstSource
end HeckeSkeleton.Moments.EngineStepV2

