import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualFirstSecondCoveredSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualPoolFiniteLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstBlockFiniteLeaves

/-!
# Pure-dual first-block budgets on the original hybrid leaves

The original internal divisor and finite phase still precede the two
actual pool sides. The exact same `classWeight`, positive normalizers,
first Fourier measure, and negative right location scale the existing
`classLeaf` and `coveredLeaf`. Both pure-dual terminal budgets are
computed on those same labels; no carrier or source comparison is
assumed or reconstructed.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments HeckePort.Moments.MobiusRegroup

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
local instance dualFirstBlockFiniteLeavesCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}

namespace FirstBlockPoolData

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockPoolData chart P M X hX}

namespace SecondStages

namespace DualTerminalCalibration

variable {s : p.SecondStages (E := E) (hDiff := hDiff)}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def classZeroBudget (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (ε Czero : ℝ)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) : ℝ :=
  classWeight NL NR S χ *
    ((actualFourierMeasure chart.kernel).real Set.univ * (T.left S χ).zeroBudget ε Czero / NL S χ +
      (actualFourierMeasure chart.kernel).real Set.univ * (T.right S χ).zeroBudget ε Czero / NR S χ)

def classTailBudget (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (Cerror : ℝ)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) : ℝ :=
  classWeight NL NR S χ *
    ((actualFourierMeasure chart.kernel).real Set.univ * (T.left S χ).tailBudget Cerror / NL S χ +
      (actualFourierMeasure chart.kernel).real Set.univ * (T.right S χ).tailBudget Cerror / NR S χ)

def zeroBudget (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (ε Czero : ℝ) : ℝ :=
  ∑ S, ∑ χ, T.classZeroBudget NL NR ε Czero S χ

def tailBudget (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (Cerror : ℝ) : ℝ :=
  ∑ S, ∑ χ, T.classTailBudget NL NR Cerror S χ

/-- No source comparison is assumed: this is an exact evaluation of
the two original integrals by the proven per-pool finite-leaf identity. -/
theorem class_cost_eq_budgets_leaves
    (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ)
    (exceptional : s.CoverHybridPredicates LA RA)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)
    (ε Cerror Czero : ℝ)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) :
    classWeight NL NR S χ *
      ((∫ ξ, (T.left S χ).coverHybridPhaseCost
          (p.leftSourceCovers LA S χ) (exceptional.left S χ)
          chart.leftPoint ξ ε Cerror Czero / NL S χ ∂actualFourierMeasure chart.kernel) +
        ∫ ξ, (T.right S χ).coverHybridPhaseCost
          (p.rightSourceCovers RA S χ) (exceptional.right S χ)
          (fun j => -chart.rightPoint j) ξ ε Cerror Czero / NR S χ
          ∂actualFourierMeasure chart.kernel) =
      T.classZeroBudget NL NR ε Czero S χ + T.classTailBudget NL NR Cerror S χ +
        ∑ j : s.CoveredClassKey LA RA S χ,
          (s.classLeaf LA RA NL NR hNL hNR exceptional S χ j).cost := by
  rw [integral_div, integral_div,
    (T.left S χ).integral_phase_cost_eq_budgets_leaves
      (p.leftSourceCovers LA S χ) (exceptional.left S χ) chart.kernel chart.leftPoint,
    (T.right S χ).integral_phase_cost_eq_budgets_leaves
      (p.rightSourceCovers RA S χ) (exceptional.right S χ) chart.kernel (fun j => -chart.rightPoint j)]
  simp only [Fintype.sum_sum_type, classLeaf, ActualHybridLeaf.scale_cost]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  unfold classZeroBudget classTailBudget
  ring

/-- The actual first block is exactly its computed second zero budget,
computed second tail budget, and finite genuine hybrid leaves. -/
theorem coveredCost_eq_budgets_leaves
    (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ)
    (exceptional : s.CoverHybridPredicates LA RA)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)
    (ε Cerror Czero : ℝ) :
    T.coveredCost LA RA exceptional NL NR ε Cerror Czero =
      T.zeroBudget NL NR ε Czero + T.tailBudget NL NR Cerror +
        ∑ j : s.CoveredLeafKey LA RA,
          (s.coveredLeaf LA RA NL NR hNL hNR exceptional j).cost := by
  unfold coveredCost
  simp only [Finset.mul_sum]
  have he := T.class_cost_eq_budgets_leaves LA RA exceptional NL NR hNL hNR ε Cerror Czero
  calc
    _ = ∑ S, ∑ χ, (T.classZeroBudget NL NR ε Czero S χ +
        T.classTailBudget NL NR Cerror S χ +
        ∑ j : s.CoveredClassKey LA RA S χ,
          (s.classLeaf LA RA NL NR hNL hNR exceptional S χ j).cost) := by
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro χ _
      simpa only [classWeight, mul_assoc] using he S χ
    _ = _ := by
      simp only [zeroBudget, tailBudget, Fintype.sum_sigma, coveredLeaf, Finset.sum_add_distrib]

end DualTerminalCalibration
end SecondStages
end FirstBlockPoolData
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.SecondStages.DualTerminalCalibration.class_cost_eq_budgets_leaves
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.SecondStages.DualTerminalCalibration.coveredCost_eq_budgets_leaves
