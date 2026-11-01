import HeckeSkeleton.Moments.MOM_ENGINE_STEP.LiveSourceConditions
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectSupportedLeaves

/-!
# The exact outer scalar of every original parent leaf

Each original finite key determines its bare second-transform leaf.
The original first normalization, both orbital fibres and the genuine
pool scalar only multiply its outer weight. These identities read the
stored source definitions, without selecting another label or changing
any coefficient, location, row or Fourier kernel.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments

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
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local instance originalParentLeafScalingCircleCharacterFintype :
    Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

namespace ActualHybridLeaf

@[simp] theorem scale_scale {H : Type*} (B : ActualHybridLeaf K H W E)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (B.scale a ha).scale b hb = B.scale (b * a) (mul_nonneg hb ha) := by
  cases B
  simp only [scale, mul_assoc]

end ActualHybridLeaf

section PoolStages

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}
variable {d : FirstGaussPoolData C P ι} {c : ι → ℂ}

namespace ActualPoolStages

variable (s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest)
variable (B : d.SourceCovers c)

/-- The original main/error key, with precisely the same underlying
second-transform leaf and no outer source multiplier. -/
def unscaledCoveredLeaf (exceptional : s.CoverHybridPredicates B)
    (F : SchwartzMap W ℂ) (x : ι → W) : s.CoveredLeafKey B → ActualHybridLeaf K Q W E
  | .inl b => s.main.coveredLeaf B.main B.main exceptional.main F x b
  | .inr (.inl ⟨p, b⟩) =>
      (s.one p).coveredLeaf (B.residual p 1) (B.residual p 1) (exceptional.one p)
        F (fun i => x i.val) b
  | .inr (.inr (.inl ⟨p, b⟩)) =>
      (s.six p).coveredLeaf (B.residual p 6) (B.residual p 6) (exceptional.six p)
        F (fun i => x i.val) b
  | .inr (.inr (.inr ⟨p, b⟩)) =>
      (s.seven p).coveredLeaf (B.residual p 7) (B.residual p 7) (exceptional.seven p)
        F (fun i => x i.val) b

def coveredOuterScalar : s.CoveredLeafKey B → ℝ
  | .inl _ => ((4 / d.density) * d.multiplicity) * (s.main.fiber : ℝ)
  | .inr (.inl ⟨p, _⟩) =>
      ((4 / d.density) * FirstGaussPoolData.localErrorWeight p.val 1) * ((s.one p).fiber : ℝ)
  | .inr (.inr (.inl ⟨p, _⟩)) =>
      ((4 / d.density) * FirstGaussPoolData.localErrorWeight p.val 6) * ((s.six p).fiber : ℝ)
  | .inr (.inr (.inr ⟨p, _⟩)) =>
      ((4 / d.density) * FirstGaussPoolData.localErrorWeight p.val 7) * ((s.seven p).fiber : ℝ)

theorem coveredOuterScalar_nonneg (b : s.CoveredLeafKey B) :
    0 ≤ s.coveredOuterScalar B b := by
  rcases b with b | (⟨p, b⟩ | (⟨p, b⟩ | ⟨p, b⟩))
  · exact mul_nonneg
      (mul_nonneg (div_nonneg (by norm_num) d.density_pos.le) d.multiplicity_nonneg)
      (Nat.cast_nonneg _)
  · exact mul_nonneg
      (mul_nonneg (div_nonneg (by norm_num) d.density_pos.le)
        (FirstGaussPoolData.localErrorWeight_nonneg p.val 1)) (Nat.cast_nonneg _)
  · exact mul_nonneg
      (mul_nonneg (div_nonneg (by norm_num) d.density_pos.le)
        (FirstGaussPoolData.localErrorWeight_nonneg p.val 6)) (Nat.cast_nonneg _)
  · exact mul_nonneg
      (mul_nonneg (div_nonneg (by norm_num) d.density_pos.le)
        (FirstGaussPoolData.localErrorWeight_nonneg p.val 7)) (Nat.cast_nonneg _)

theorem coveredLeaf_eq_unscaled_scale (exceptional : s.CoverHybridPredicates B)
    (F : SchwartzMap W ℂ) (x : ι → W) (b : s.CoveredLeafKey B) :
    s.coveredLeaf B exceptional F x b =
      (s.unscaledCoveredLeaf B exceptional F x b).scale
        (s.coveredOuterScalar B b) (s.coveredOuterScalar_nonneg B b) := by
  rcases b with b | (⟨p, b⟩ | (⟨p, b⟩ | ⟨p, b⟩)) <;>
    simp only [coveredLeaf, unscaledCoveredLeaf, coveredOuterScalar,
      ActualGaussStage.fiberCoveredLeaf, ActualHybridLeaf.scale_scale]

theorem unscaledCoveredLeaf_live (exceptional : s.CoverHybridPredicates B)
    (F : SchwartzMap W ℂ) (x : ι → W) (b : s.CoveredLeafKey B)
    (h : (s.coveredLeaf B exceptional F x b).Live) :
    (s.unscaledCoveredLeaf B exceptional F x b).Live := by
  rw [s.coveredLeaf_eq_unscaled_scale B exceptional F x b] at h
  exact (s.unscaledCoveredLeaf B exceptional F x b).live_of_scale_live _ _ h

end ActualPoolStages
end PoolStages

section DirectBlocks

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockDirectData chart M X hX}

namespace FirstBlockDirectData.SecondStages

variable (s : p.SecondStages (E := E) (hDiff := hDiff))
variable (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ)

def unscaledCoveredLeaf (exceptional : s.CoverHybridPredicates LA RA)
    (j : s.CoveredLeafKey LA RA) : ActualHybridLeaf K Q W E :=
  match j with
  | ⟨S, χ, .inl b⟩ =>
      (s.left S χ).coveredLeaf (p.leftSourceCover LA S χ) (p.leftSourceCover LA S χ)
        (exceptional.left S χ) chart.kernel chart.leftPoint b
  | ⟨S, χ, .inr b⟩ =>
      (s.right S χ).coveredLeaf (p.rightSourceCover RA S χ) (p.rightSourceCover RA S χ)
        (exceptional.right S χ) chart.kernel (fun i => -chart.rightPoint i) b

variable
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)

def coveredOuterScalar : s.CoveredLeafKey LA RA → ℝ
  | ⟨S, χ, .inl _⟩ => (classWeight (p := p) NL NR S χ / NL S χ) * ((s.left S χ).fiber : ℝ)
  | ⟨S, χ, .inr _⟩ => (classWeight (p := p) NL NR S χ / NR S χ) * ((s.right S χ).fiber : ℝ)

include hNL hNR in
theorem coveredOuterScalar_nonneg (j : s.CoveredLeafKey LA RA) :
    0 ≤ s.coveredOuterScalar LA RA NL NR j := by
  rcases j with ⟨S, χ, j | j⟩
  · exact mul_nonneg (div_nonneg (classWeight_nonneg NL NR S χ) (hNL S χ).le)
      (Nat.cast_nonneg _)
  · exact mul_nonneg (div_nonneg (classWeight_nonneg NL NR S χ) (hNR S χ).le)
      (Nat.cast_nonneg _)

theorem coveredLeaf_eq_unscaled_scale (exceptional : s.CoverHybridPredicates LA RA)
    (j : s.CoveredLeafKey LA RA) :
    s.coveredLeaf LA RA NL NR hNL hNR exceptional j =
      (s.unscaledCoveredLeaf LA RA exceptional j).scale
        (s.coveredOuterScalar LA RA NL NR j)
        (s.coveredOuterScalar_nonneg LA RA NL NR hNL hNR j) := by
  rcases j with ⟨S, χ, j | j⟩ <;>
    simp only [coveredLeaf, classLeaf, unscaledCoveredLeaf, coveredOuterScalar,
      ActualGaussStage.fiberCoveredLeaf, ActualHybridLeaf.scale_scale]

theorem unscaledCoveredLeaf_live (exceptional : s.CoverHybridPredicates LA RA)
    (j : s.CoveredLeafKey LA RA)
    (h : (s.coveredLeaf LA RA NL NR hNL hNR exceptional j).Live) :
    (s.unscaledCoveredLeaf LA RA exceptional j).Live := by
  rw [s.coveredLeaf_eq_unscaled_scale LA RA NL NR hNL hNR exceptional j] at h
  exact (s.unscaledCoveredLeaf LA RA exceptional j).live_of_scale_live _ _ h

end FirstBlockDirectData.SecondStages
end DirectBlocks

section PoolBlocks

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockPoolData chart P M X hX}

namespace FirstBlockPoolData.SecondStages

variable (s : p.SecondStages (E := E) (hDiff := hDiff))
variable (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ)

def unscaledCoveredLeaf (exceptional : s.CoverHybridPredicates LA RA)
    (j : s.CoveredLeafKey LA RA) : ActualHybridLeaf K Q W E :=
  match j with
  | ⟨S, χ, .inl b⟩ =>
      (s.left S χ).unscaledCoveredLeaf (p.leftSourceCovers LA S χ)
        (exceptional.left S χ) chart.kernel chart.leftPoint b
  | ⟨S, χ, .inr b⟩ =>
      (s.right S χ).unscaledCoveredLeaf (p.rightSourceCovers RA S χ)
        (exceptional.right S χ) chart.kernel (fun i => -chart.rightPoint i) b

variable
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)

def coveredOuterScalar : s.CoveredLeafKey LA RA → ℝ
  | ⟨S, χ, .inl b⟩ =>
      (classWeight (p := p) NL NR S χ / NL S χ) *
        (s.left S χ).coveredOuterScalar (p.leftSourceCovers LA S χ) b
  | ⟨S, χ, .inr b⟩ =>
      (classWeight (p := p) NL NR S χ / NR S χ) *
        (s.right S χ).coveredOuterScalar (p.rightSourceCovers RA S χ) b

include hNL hNR in
theorem coveredOuterScalar_nonneg (j : s.CoveredLeafKey LA RA) :
    0 ≤ s.coveredOuterScalar LA RA NL NR j := by
  rcases j with ⟨S, χ, j | j⟩
  · exact mul_nonneg (div_nonneg (classWeight_nonneg NL NR S χ) (hNL S χ).le)
      ((s.left S χ).coveredOuterScalar_nonneg (p.leftSourceCovers LA S χ) j)
  · exact mul_nonneg (div_nonneg (classWeight_nonneg NL NR S χ) (hNR S χ).le)
      ((s.right S χ).coveredOuterScalar_nonneg (p.rightSourceCovers RA S χ) j)

theorem coveredLeaf_eq_unscaled_scale (exceptional : s.CoverHybridPredicates LA RA)
    (j : s.CoveredLeafKey LA RA) :
    s.coveredLeaf LA RA NL NR hNL hNR exceptional j =
      (s.unscaledCoveredLeaf LA RA exceptional j).scale
        (s.coveredOuterScalar LA RA NL NR j)
        (s.coveredOuterScalar_nonneg LA RA NL NR hNL hNR j) := by
  rcases j with ⟨S, χ, j | j⟩
  · simp only [coveredLeaf, classLeaf, unscaledCoveredLeaf, coveredOuterScalar]
    rw [(s.left S χ).coveredLeaf_eq_unscaled_scale (p.leftSourceCovers LA S χ)
      (exceptional.left S χ) chart.kernel chart.leftPoint j, ActualHybridLeaf.scale_scale]
  · simp only [coveredLeaf, classLeaf, unscaledCoveredLeaf, coveredOuterScalar]
    rw [(s.right S χ).coveredLeaf_eq_unscaled_scale (p.rightSourceCovers RA S χ)
      (exceptional.right S χ) chart.kernel (fun i => -chart.rightPoint i) j,
      ActualHybridLeaf.scale_scale]

theorem unscaledCoveredLeaf_live (exceptional : s.CoverHybridPredicates LA RA)
    (j : s.CoveredLeafKey LA RA)
    (h : (s.coveredLeaf LA RA NL NR hNL hNR exceptional j).Live) :
    (s.unscaledCoveredLeaf LA RA exceptional j).Live := by
  rw [s.coveredLeaf_eq_unscaled_scale LA RA NL NR hNL hNR exceptional j] at h
  exact (s.unscaledCoveredLeaf LA RA exceptional j).live_of_scale_live _ _ h

end FirstBlockPoolData.SecondStages
end PoolBlocks

section DirectParents

variable {Z : ℝ}
variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX}

namespace ActualDirectFirstSource.SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)

def unscaledParentLeaf (exceptional : R.CoverHybridPredicates L)
    (j : R.CoveredLeafKey L) : ActualHybridLeaf K Q W E :=
  (R j.1 j.2.1).unscaledCoveredLeaf L L (exceptional j.1 j.2.1) j.2.2

def parentOuterScalar (N : s.Normalization) (j : R.CoveredLeafKey L) : ℝ :=
  (s.fiber : ℝ) * (R j.1 j.2.1).coveredOuterScalar L L
    (N.left j.1 j.2.1) (N.right j.1 j.2.1) j.2.2

theorem parentOuterScalar_nonneg (N : s.Normalization) (j : R.CoveredLeafKey L) :
    0 ≤ R.parentOuterScalar L N j :=
  mul_nonneg (Nat.cast_nonneg _)
    ((R j.1 j.2.1).coveredOuterScalar_nonneg L L
      (N.left j.1 j.2.1) (N.right j.1 j.2.1)
      (N.left_pos j.1 j.2.1) (N.right_pos j.1 j.2.1) j.2.2)

/-- All original normalizations and source multiplicities are one
outer scalar on the same stored second-transform leaf. -/
theorem parentLeaf_eq_unscaled_scale (exceptional : R.CoverHybridPredicates L)
    (N : s.Normalization) (j : R.CoveredLeafKey L) :
    R.parentLeaf L exceptional N j =
      (R.unscaledParentLeaf L exceptional j).scale
        (R.parentOuterScalar L N j) (R.parentOuterScalar_nonneg L N j) := by
  unfold parentLeaf unscaledParentLeaf parentOuterScalar
  rw [(R j.1 j.2.1).coveredLeaf_eq_unscaled_scale L L
    (N.left j.1 j.2.1) (N.right j.1 j.2.1)
    (N.left_pos j.1 j.2.1) (N.right_pos j.1 j.2.1)
    (exceptional j.1 j.2.1) j.2.2, ActualHybridLeaf.scale_scale]

theorem unscaledParentLeaf_live (exceptional : R.CoverHybridPredicates L)
    (N : s.Normalization) (j : R.CoveredLeafKey L)
    (h : (R.parentLeaf L exceptional N j).Live) :
    (R.unscaledParentLeaf L exceptional j).Live := by
  rw [R.parentLeaf_eq_unscaled_scale L exceptional N j] at h
  exact (R.unscaledParentLeaf L exceptional j).live_of_scale_live _ _ h

theorem live_unscaledParentLeaf (exceptional : R.CoverHybridPredicates L)
    (N : s.Normalization) (j : R.liveLeaves L exceptional N) :
    (R.unscaledParentLeaf L exceptional j.val).Live :=
  R.unscaledParentLeaf_live L exceptional N j.val (R.liveLeaves_spec L exceptional N j)

theorem parentLeaf_ordinaryCost_unscaled (exceptional : R.CoverHybridPredicates L)
    (N : s.Normalization) (j : R.CoveredLeafKey L) :
    (R.parentLeaf L exceptional N j).ordinaryCost =
      R.parentOuterScalar L N j * (R.unscaledParentLeaf L exceptional j).ordinaryCost := by
  rw [R.parentLeaf_eq_unscaled_scale L exceptional N j, ActualHybridLeaf.scale_ordinaryCost]

theorem parentLeaf_weight_unscaled (exceptional : R.CoverHybridPredicates L)
    (N : s.Normalization) (j : R.CoveredLeafKey L) :
    (R.parentLeaf L exceptional N j).weight =
      R.parentOuterScalar L N j * (R.unscaledParentLeaf L exceptional j).weight := by
  rw [R.parentLeaf_eq_unscaled_scale L exceptional N j]
  rfl

end ActualDirectFirstSource.SecondStages
end DirectParents

section AmplifiedParents

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}

namespace ActualFirstSource.SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)

def unscaledParentLeaf (exceptional : R.CoverHybridPredicates L)
    (j : R.CoveredLeafKey L) : ActualHybridLeaf K Q W E :=
  (R j.1 j.2.1).unscaledCoveredLeaf L L (exceptional j.1 j.2.1) j.2.2

def parentOuterScalar (N : s.Normalization) (j : R.CoveredLeafKey L) : ℝ :=
  (s.fiber : ℝ) * (R j.1 j.2.1).coveredOuterScalar L L
    (N.left j.1 j.2.1) (N.right j.1 j.2.1) j.2.2

theorem parentOuterScalar_nonneg (N : s.Normalization) (j : R.CoveredLeafKey L) :
    0 ≤ R.parentOuterScalar L N j :=
  mul_nonneg (Nat.cast_nonneg _)
    ((R j.1 j.2.1).coveredOuterScalar_nonneg L L
      (N.left j.1 j.2.1) (N.right j.1 j.2.1)
      (N.left_pos j.1 j.2.1) (N.right_pos j.1 j.2.1) j.2.2)

/-- All original normalizations and source multiplicities are one
outer scalar on the same stored second-transform leaf. -/
theorem parentLeaf_eq_unscaled_scale (exceptional : R.CoverHybridPredicates L)
    (N : s.Normalization) (j : R.CoveredLeafKey L) :
    R.parentLeaf L exceptional N j =
      (R.unscaledParentLeaf L exceptional j).scale
        (R.parentOuterScalar L N j) (R.parentOuterScalar_nonneg L N j) := by
  unfold parentLeaf coveredLeaf unscaledParentLeaf parentOuterScalar
  rw [(R j.1 j.2.1).coveredLeaf_eq_unscaled_scale L L
    (N.left j.1 j.2.1) (N.right j.1 j.2.1)
    (N.left_pos j.1 j.2.1) (N.right_pos j.1 j.2.1)
    (exceptional j.1 j.2.1) j.2.2, ActualHybridLeaf.scale_scale]

theorem unscaledParentLeaf_live (exceptional : R.CoverHybridPredicates L)
    (N : s.Normalization) (j : R.CoveredLeafKey L)
    (h : (R.parentLeaf L exceptional N j).Live) :
    (R.unscaledParentLeaf L exceptional j).Live := by
  rw [R.parentLeaf_eq_unscaled_scale L exceptional N j] at h
  exact (R.unscaledParentLeaf L exceptional j).live_of_scale_live _ _ h

theorem live_unscaledParentLeaf (exceptional : R.CoverHybridPredicates L)
    (N : s.Normalization) (j : R.liveLeaves L exceptional N) :
    (R.unscaledParentLeaf L exceptional j.val).Live :=
  R.unscaledParentLeaf_live L exceptional N j.val (R.liveLeaves_spec L exceptional N j)

theorem parentLeaf_ordinaryCost_unscaled (exceptional : R.CoverHybridPredicates L)
    (N : s.Normalization) (j : R.CoveredLeafKey L) :
    (R.parentLeaf L exceptional N j).ordinaryCost =
      R.parentOuterScalar L N j * (R.unscaledParentLeaf L exceptional j).ordinaryCost := by
  rw [R.parentLeaf_eq_unscaled_scale L exceptional N j, ActualHybridLeaf.scale_ordinaryCost]

theorem parentLeaf_weight_unscaled (exceptional : R.CoverHybridPredicates L)
    (N : s.Normalization) (j : R.CoveredLeafKey L) :
    (R.parentLeaf L exceptional N j).weight =
      R.parentOuterScalar L N j * (R.unscaledParentLeaf L exceptional j).weight := by
  rw [R.parentLeaf_eq_unscaled_scale L exceptional N j]
  rfl

end ActualFirstSource.SecondStages
end AmplifiedParents

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.scale_scale
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.coveredLeaf_eq_unscaled_scale
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.SecondStages.coveredLeaf_eq_unscaled_scale
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.SecondStages.coveredLeaf_eq_unscaled_scale

#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.parentLeaf_eq_unscaled_scale
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.parentLeaf_eq_unscaled_scale
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.live_unscaledParentLeaf
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.live_unscaledParentLeaf
