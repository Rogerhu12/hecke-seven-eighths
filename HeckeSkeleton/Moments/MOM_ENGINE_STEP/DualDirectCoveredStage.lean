import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualDirectSecondStages

/-!
# The direct signed source reaches its original finite hybrid leaves

The raw signed reduction is refined by the already existing Cartesian
covers, using the same double Fourier integrals. The finite labels,
left/right normalizers, complete coefficients and `parentLeaf` objects
are exactly those of the original direct entrance.

The first pure-dual terminal windows and the second pure-dual terminal
windows are kept distinct. No positive prime-pool witness, vanishing
test profile, or aggregate terminal/source estimate is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckePort.Moments HeckePort.Moments.MobiusRegroup MeasureTheory

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
variable {W E : Type*}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

local instance dualDirectCoveredStageCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Z : ℝ}

namespace FirstBlockDirectData

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockDirectData chart M X hX}

namespace SecondStages.DualTerminalCalibration

variable {s : p.SecondStages (E := E) (hDiff := hDiff)}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

/-- The original first-measure mass and each original normalizer stay
attached to the exact side of the actual pure-dual zero. -/
def classZeroBudget (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (ε Czero : ℝ)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) : ℝ :=
  classWeight NL NR S χ *
    ((actualFourierMeasure chart.kernel).real Set.univ * (T.left S χ).zeroBudget ε Czero / NL S χ +
      (actualFourierMeasure chart.kernel).real Set.univ * (T.right S χ).zeroBudget ε Czero / NR S χ)

def classTailBudget (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (Cerror : ℝ)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) : ℝ :=
  classWeight NL NR S χ *
    ((actualFourierMeasure chart.kernel).real Set.univ * (T.left S χ).tailBudget Cerror / NL S χ +
      (actualFourierMeasure chart.kernel).real Set.univ * (T.right S χ).tailBudget Cerror / NR S χ)

def zeroBudget (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ) (ε Czero : ℝ) : ℝ :=
  ∑ S, ∑ χ, T.classZeroBudget NL NR ε Czero S χ

def tailBudget (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ) (Cerror : ℝ) : ℝ :=
  ∑ S, ∑ χ, T.classTailBudget NL NR Cerror S χ

/-- The same original `coveredLeaf` objects; only the justified signed
terminal bounds replace the old absolute transformed-zero estimate. -/
def finiteCost (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ)
    (exceptional : s.CoverHybridPredicates LA RA)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)
    (ε Cerror Czero : ℝ) : ℝ :=
  T.zeroBudget NL NR ε Czero + T.tailBudget NL NR Cerror +
    ∑ j : s.CoveredLeafKey LA RA,
      (s.coveredLeaf LA RA NL NR hNL hNR exceptional j).cost

/-- The proved finite cover decomposition is applied inside the same
first integral. This step does not require any source or leaf bound. -/
theorem rawCost_le_finiteCost
    (T : s.DualTerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ)
    (exceptional : s.CoverHybridPredicates LA RA)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)
    (ε Cerror Czero : ℝ) :
    T.rawCost NL NR ε Cerror Czero ≤
      T.finiteCost LA RA exceptional NL NR hNL hNR ε Cerror Czero := by
  unfold rawCost finiteCost zeroBudget tailBudget
  simp only [Finset.mul_sum, Fintype.sum_sigma, coveredLeaf]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro S _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro χ _
  have hl := (T.left S χ).integral_rawPhaseCost_le_cover
    (p.leftSourceCover LA S χ) (p.leftSourceCover LA S χ)
    (exceptional.left S χ) chart.kernel chart.leftPoint ε Cerror Czero
  rw [(T.left S χ).integral_phase_cost_eq_budgets_leaves
    (p.leftSourceCover LA S χ) (p.leftSourceCover LA S χ)
    (exceptional.left S χ) chart.kernel chart.leftPoint ε Cerror Czero] at hl
  have hr := (T.right S χ).integral_rawPhaseCost_le_cover
    (p.rightSourceCover RA S χ) (p.rightSourceCover RA S χ)
    (exceptional.right S χ) chart.kernel (fun j => -chart.rightPoint j) ε Cerror Czero
  rw [(T.right S χ).integral_phase_cost_eq_budgets_leaves
    (p.rightSourceCover RA S χ) (p.rightSourceCover RA S χ)
    (exceptional.right S χ) chart.kernel (fun j => -chart.rightPoint j) ε Cerror Czero] at hr
  rw [integral_div, integral_div]
  have hh := mul_le_mul_of_nonneg_left
    (add_le_add (div_le_div_of_nonneg_right hl (hNL S χ).le)
      (div_le_div_of_nonneg_right hr (hNR S χ).le))
    (classWeight_nonneg NL NR S χ)
  convert hh using 1
  · dsimp only [classWeight]
    ring
  · simp only [Fintype.sum_sum_type, classLeaf, ActualHybridLeaf.scale_cost]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    unfold classZeroBudget classTailBudget
    ring

end SecondStages.DualTerminalCalibration
end FirstBlockDirectData

variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}

namespace ActualDirectFirstSource.SecondStages

variable {s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX}
variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def dualFiniteCost (T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (L : SourceCartesianAtlas s.columns s.ideal)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (ε Cerror Czero : ℝ) : ℝ :=
  ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
    (T v D).finiteCost L L (exceptional v D)
      (N.left v D) (N.right v D) (N.left_pos v D) (N.right_pos v D) ε Cerror Czero

def dualSecondZeroBudget (T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (N : s.Normalization) (ε Czero : ℝ) : ℝ :=
  (s.fiber : ℝ) * ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
    (T v D).zeroBudget (N.left v D) (N.right v D) ε Czero

def dualSecondTailBudget (T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (N : s.Normalization) (Cerror : ℝ) : ℝ :=
  (s.fiber : ℝ) * ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
    (T v D).tailBudget (N.left v D) (N.right v D) Cerror

/-- The parent fibre occurs exactly once. Every nonzero summand is the
pre-existing original parent leaf on its complete original carrier. -/
theorem dualFiniteCost_eq_budgets_leaves
    (T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (L : SourceCartesianAtlas s.columns s.ideal)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (ε Cerror Czero : ℝ) :
    (s.fiber : ℝ) * R.dualFiniteCost T L exceptional N ε Cerror Czero =
      R.dualSecondZeroBudget T N ε Czero + R.dualSecondTailBudget T N Cerror +
      ∑ j : R.CoveredLeafKey L, (R.parentLeaf L exceptional N j).cost := by
  simp only [dualFiniteCost, FirstBlockDirectData.SecondStages.DualTerminalCalibration.finiteCost,
    dualSecondZeroBudget, dualSecondTailBudget, Fintype.sum_sigma, parentLeaf,
    ActualHybridLeaf.scale_cost, Finset.sum_add_distrib, Finset.mul_sum, mul_add]

theorem dualRawCost_le_finiteCost
    (T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (L : SourceCartesianAtlas s.columns s.ideal)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (ε Cerror Czero : ℝ) :
    R.dualRawCost T N ε Cerror Czero ≤ R.dualFiniteCost T L exceptional N ε Cerror Czero := by
  unfold dualRawCost dualFiniteCost
  apply Finset.sum_le_sum
  intro v _
  apply Finset.sum_le_sum
  intro D _
  exact (T v D).rawCost_le_finiteCost L L (exceptional v D)
    (N.left v D) (N.right v D) (N.left_pos v D) (N.right_pos v D) ε Cerror Czero

end ActualDirectFirstSource.SecondStages

variable (hΓ μv hDiff)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- Both original signed transforms, followed by the literal canonical
finite hybrid leaves. The raw theorem chooses the constants once;
covering and finite reindexing make no new analytic choices. -/
theorem actual_parent_direct_two_stage_dual_finite_leaf_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
    (rowBallSize normBound : ℝ) (hB : 0 ≤ normBound) (δ : ℝ) (hδ : 0 < δ)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) (Lmax Nsave ξmax : ℝ) (hξmax : 0 < ξmax) :
    ∃ (decay : ℝ) (hdecay : 1 < decay),
      decay = tailDecayForWidth Lmax Nsave ξmax ∧
      firstTailCutoffExponent Lmax Nsave decay ≤ ξmax ∧
    ∃ sFirst sFirstZero sTail sZero : Finset (ℕ × ℕ),
    ∃ CfirstError CfirstZero Cerror Czero : ℝ,
      0 ≤ CfirstError ∧ 0 < CfirstZero ∧ 0 ≤ Cerror ∧ 0 < Czero ∧
    ∀ (Z : ℝ), ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ s : ActualDirectFirstSource (E := W) hΓ μv C Z
      (rowBallFiniteFamily K A.Sf rowBallSize) centered d a t Y₁ Y₂ X hX,
    ∀ coefficient : s.Column → ℂ,
      (∀ i j, s.profiles i j = (coefficient i * star (coefficient j)) •
        CanonicalRowBall.archTest K A.Sf rowBallSize) →
    ∀ N : s.Normalization,
    ∀ R : s.SecondStages (E := E) (hDiff := hDiff),
    ∀ conditions : R.DualSourceConditions,
    ∀ T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay,
    ∀ F : FirstDualOriginalWindows (hΓ := hΓ) C s.columns s.ideal s.block s.profiles
      s.radius s.mask sFirst sFirstZero k Z X normBound Lmax Nsave decay,
    ∀ (L : SourceCartesianAtlas s.columns s.ideal) (exceptional : R.CoverHybridPredicates L),
      X ≤ Z ^ ξmax ∧
      pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
        (s.fiber : ℝ) * F.cost hB δ hδ ε CfirstError CfirstZero +
        R.dualSecondZeroBudget T N ε Czero + R.dualSecondTailBudget T N Cerror +
        ∑ j : R.CoveredLeafKey L, (R.parentLeaf L exceptional N j).cost := by
  obtain ⟨decay, hdecay, hchoice, hq, sFirst, sFirstZero, sTail, sZero,
      CfirstError, CfirstZero, Cerror, Czero, hCfE, hCfZ, hCE, hCZ, hparent⟩ :=
    actual_parent_direct_two_stage_dual_raw_terminal_bound
      (W := W) (E := E) (ν := ν) (μ := μ) hΓ μv hDiff C Drecipe hD
      rowBallSize normBound hB δ hδ k ε hε Lmax Nsave ξmax hξmax
  refine ⟨decay, hdecay, hchoice, hq, sFirst, sFirstZero, sTail, sZero,
    CfirstError, CfirstZero, Cerror, Czero, hCfE, hCfZ, hCE, hCZ, ?_⟩
  intro Z ω ψ centered d a t Y₁ Y₂ X hX s coefficient hprofiles N R conditions T F L exceptional
  obtain ⟨hcutoff, hraw⟩ :=
    hparent Z centered d a t Y₁ Y₂ X hX s coefficient hprofiles N R conditions T F
  refine ⟨hcutoff, hraw.trans ?_⟩
  calc
    _ ≤ (s.fiber : ℝ) * (F.cost hB δ hδ ε CfirstError CfirstZero +
        R.dualFiniteCost T L exceptional N ε Cerror Czero) :=
      mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (R.dualRawCost_le_finiteCost T L exceptional N ε Cerror Czero))
        (Nat.cast_nonneg s.fiber)
    _ = _ := by
      rw [mul_add, R.dualFiniteCost_eq_budgets_leaves T L exceptional N ε Cerror Czero]
      ring

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.SecondStages.DualTerminalCalibration.rawCost_le_finiteCost
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.dualFiniteCost_eq_budgets_leaves
#print axioms HeckeSkeleton.Moments.EngineStep.actual_parent_direct_two_stage_dual_finite_leaf_bound
