import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SignedFirstStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualFirstSource

/-!
# The original first-source record with pure dual-zero terminals

These estimates use the same actual source, common blocks, profile
charts, prime pool, and normalization as the ordinary first-source
interface.  They replace the absolute value of the signed Poisson zero
by the pure dual zero after proving the complete original-origin sum is
nonnegative.  Both the raw finite row sum and the original linearized
pool remain available for the subsequent source decomposition.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Lattice" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
local instance signedActualFirstSourceCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

section Costs

variable {hΓ μv}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Z ell eps : ℝ} {bad : Finset (HeightOneSpectrum (𝓞 K))}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {ω ψ : HeckeCharacter K} {centered : Bool} {d : MomentData K ω ψ}
variable {a : RealParameters} {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

/-- Only the genuine dual-frequency zero on the original common blocks. -/
def ActualFirstSource.dualZeroCost
    (s : ActualFirstSource (E := E) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0) : ℝ :=
  ∑ v : s.CommonLabel, ‖(s.source v).dualZeroTerm μv hDiff finiteTest‖

/-- The raw finite row expression, before its Fourier Cauchy estimate. -/
def ActualFirstSource.rawRowCost
    (s : ActualFirstSource (E := E) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0) : ℝ :=
  ∑ v : s.CommonLabel, (s.source v).rawRowCost μv hDiff finiteTest

end Costs

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
variable (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
theorem actual_parent_first_dual_raw
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (rowBallSize : ℝ) (decay : ℝ) (hdecay : 1 < decay) (order : ℕ)
    (horder : Module.finrank ℤ Lattice < order)
    (hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ order) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ Ctail : ℝ, 0 ≤ Ctail ∧
    ∀ (Z ell eps : ℝ) (bad : Finset (HeightOneSpectrum (𝓞 K)))
      (P : PowerScaleExteriorPool A bad Z ell eps),
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ s : ActualFirstSource (E := E) hΓ μv C P
      (rowBallFiniteFamily K A.Sf rowBallSize) centered d a t Y₁ Y₂ X hX,
    ∀ (coefficient : s.Column → ℂ),
      (∀ i j, s.profiles i j = (coefficient i * star (coefficient j)) •
        CanonicalRowBall.archTest K A.Sf rowBallSize) →
      pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
        (s.fiber : ℝ) * (s.dualZeroCost hDiff + s.rawRowCost hDiff +
          Ctail * X ^ (1 - decay) * s.tailCost seminorms) := by
  obtain ⟨seminorms, Ctail, hC, hbound⟩ :=
    parent_first_stage_dual_raw_bound (ν := ν) (μ := μ) hΓ μv
      C hDiff rowBallSize decay hdecay order horder hdegree
  refine ⟨seminorms, Ctail, hC, ?_⟩
  intro Z ell eps bad P ω ψ centered d a t Y₁ Y₂ X hX s coefficient hprofiles
  have hb := hbound s.columns coefficient s.ideal s.generator s.generates
    s.profiles hprofiles s.radius s.mask X hX centered d a Z t Y₁ Y₂
    s.fiber s.calibration
  simpa only [ActualFirstSource.dualZeroCost, ActualFirstSource.rawRowCost,
    ActualFirstSource.tailCost, ActualFirstSource.source, ActualFirstSource.block,
    Finset.sum_add_distrib, ← Finset.mul_sum] using hb

include ν μ in
/-- The unchanged original normalization acts on the same single pool
after the genuine signed first transform. -/
theorem actual_parent_first_dual_linearized
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (rowBallSize : ℝ) (decay : ℝ) (hdecay : 1 < decay) (order : ℕ)
    (horder : Module.finrank ℤ Lattice < order)
    (hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ order) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ Ctail : ℝ, 0 ≤ Ctail ∧
    ∀ (Z ell eps : ℝ) (bad : Finset (HeightOneSpectrum (𝓞 K)))
      (P : PowerScaleExteriorPool A bad Z ell eps),
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ s : ActualFirstSource (E := E) hΓ μv C P
      (rowBallFiniteFamily K A.Sf rowBallSize) centered d a t Y₁ Y₂ X hX,
    ∀ (coefficient : s.Column → ℂ),
      (∀ i j, s.profiles i j = (coefficient i * star (coefficient j)) •
        CanonicalRowBall.archTest K A.Sf rowBallSize) →
    ∀ N : s.Normalization,
      pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
        (s.fiber : ℝ) * (s.dualZeroCost hDiff + s.linearizedCost N +
          Ctail * X ^ (1 - decay) * s.tailCost seminorms) := by
  obtain ⟨seminorms, Ctail, hCtail, hbound⟩ :=
    parent_first_stage_pool_dual_bound (E := E) (ν := ν) (μ := μ) hΓ μv
      C hDiff rowBallSize decay hdecay order horder hdegree
  refine ⟨seminorms, Ctail, hCtail, ?_⟩
  intro Z ell eps bad P ω ψ centered d a t Y₁ Y₂ X hX s coefficient hprofiles N
  have hb := hbound Z ell eps bad P s.columns coefficient s.ideal s.generator s.generates
    s.profiles hprofiles s.radius s.mask X hX s.charts s.pools centered d a t Y₁ Y₂
    s.fiber s.calibration
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg s.fiber)
  simp only [ActualFirstSource.dualZeroCost, ActualFirstSource.linearizedCost,
    ActualFirstSource.tailCost, Finset.sum_add_distrib, ← Finset.mul_sum]
  apply add_le_add _ le_rfl
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro v _
  apply Finset.sum_le_sum
  intro D _
  exact (s.pools v D).pooledCost_le_linearized (N.left v D) (N.right v D)
    (N.left_pos v D) (N.right_pos v D)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_parent_first_dual_raw
#print axioms HeckeSkeleton.Moments.EngineStep.actual_parent_first_dual_linearized
