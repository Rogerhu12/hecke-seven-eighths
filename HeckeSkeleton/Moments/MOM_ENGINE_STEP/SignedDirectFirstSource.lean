import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SignedFirstStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualDirectFirstSource

/-!
# The direct first source with its original-origin sign

The direct entrance has no prime-pool parameter. It uses the same
complete first common-support decomposition and fixed row-ball tensor.
The signed first bound therefore applies uniformly to every original
slot count, including zero, and keeps the actual finite rows for the
subsequent ordinary/exceptional decomposition.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

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
local instance signedDirectFirstSourceCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

section Costs

variable {hΓ μv}
variable {C : A.GeneralArithmeticContext σ η hS} {Z : ℝ}
variable {ω ψ : HeckeCharacter K} {centered : Bool} {d : MomentData K ω ψ}
variable {a : RealParameters} {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

def ActualDirectFirstSource.dualZeroCost
    (s : ActualDirectFirstSource (E := E) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0) : ℝ :=
  ∑ v : s.CommonLabel, ‖(s.source v).dualZeroTerm μv hDiff finiteTest‖

def ActualDirectFirstSource.rawRowCost
    (s : ActualDirectFirstSource (E := E) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0) : ℝ :=
  ∑ v : s.CommonLabel, (s.source v).rawRowCost μv hDiff finiteTest

/-- Direct row enlargement and the original positive normalization,
with no pool scalar and no additional choice of rows. -/
theorem ActualDirectFirstSource.rawRowCost_le_linearized
    (s : ActualDirectFirstSource (E := E) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (N : s.Normalization) : s.rawRowCost hDiff ≤ s.linearizedCost hDiff N := by
  unfold ActualDirectFirstSource.rawRowCost ActualDirectFirstSource.linearizedCost
  apply Finset.sum_le_sum
  intro v _
  change (∑ D : ((s.block v).mask s.mask).powerset,
      ‖∑ q ∈ (s.source v).divisorRows D.val,
        ∑ i ∈ (s.source v).leftColumns, ∑ j ∈ (s.source v).rightColumns,
          ((s.source v).pairs i j).transformedRow μv hDiff finiteTest s.radius D.val q‖) ≤ _
  apply Finset.sum_le_sum
  intro D _
  exact ((s.charts v D).kernel_bound_of_phase_one hDiff s.mask X hX (fun i j hc =>
    canonicalFirstCommonBlock_phase_one hΓ C s.columns s.columns s.ideal s.ideal
      v.val v.property i j hc)).trans
    ((s.pieces v D).kernelCost_le_linearized hDiff (N.left v D) (N.right v D)
      (N.left_pos v D) (N.right_pos v D))

end Costs

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
variable (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- Both direct exits use the same original source and fixed row-ball
test. The whole original-origin square is proved by the raw first-stage
theorem, and the direct branch requires no prime pool. -/
theorem actual_parent_first_direct_dual
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (rowBallSize : ℝ) (decay : ℝ) (hdecay : 1 < decay) (order : ℕ)
    (horder : Module.finrank ℤ Lattice < order)
    (hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ order) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ Ctail : ℝ, 0 ≤ Ctail ∧
    ∀ (Z : ℝ),
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ s : ActualDirectFirstSource (E := E) hΓ μv C Z
      (rowBallFiniteFamily K A.Sf rowBallSize) centered d a t Y₁ Y₂ X hX,
    ∀ (coefficient : s.Column → ℂ),
      (∀ i j, s.profiles i j = (coefficient i * star (coefficient j)) •
        CanonicalRowBall.archTest K A.Sf rowBallSize) →
      pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
        (s.fiber : ℝ) * (s.dualZeroCost hDiff + s.rawRowCost hDiff +
          Ctail * X ^ (1 - decay) * s.tailCost seminorms) ∧
      ∀ N : s.Normalization,
        pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
          (s.fiber : ℝ) * (s.dualZeroCost hDiff + s.linearizedCost hDiff N +
            Ctail * X ^ (1 - decay) * s.tailCost seminorms) := by
  obtain ⟨seminorms, Ctail, hC, hbound⟩ :=
    parent_first_stage_dual_raw_bound (ν := ν) (μ := μ) hΓ μv
      C hDiff rowBallSize decay hdecay order horder hdegree
  refine ⟨seminorms, Ctail, hC, ?_⟩
  intro Z ω ψ centered d a t Y₁ Y₂ X hX s coefficient hprofiles
  have hb := hbound s.columns coefficient s.ideal s.generator s.generates
    s.profiles hprofiles s.radius s.mask X hX centered d a Z t Y₁ Y₂
    s.fiber s.calibration
  have hraw : pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
      (s.fiber : ℝ) * (s.dualZeroCost hDiff + s.rawRowCost hDiff +
        Ctail * X ^ (1 - decay) * s.tailCost seminorms) := by
    simpa only [ActualDirectFirstSource.dualZeroCost, ActualDirectFirstSource.rawRowCost,
      ActualDirectFirstSource.tailCost, ActualDirectFirstSource.source, ActualDirectFirstSource.block,
      Finset.sum_add_distrib, ← Finset.mul_sum] using hb
  refine ⟨hraw, ?_⟩
  intro N
  exact hraw.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add le_rfl (s.rawRowCost_le_linearized hDiff N)) le_rfl)
    (Nat.cast_nonneg s.fiber))

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.rawRowCost_le_linearized
#print axioms HeckeSkeleton.Moments.EngineStep.actual_parent_first_direct_dual
