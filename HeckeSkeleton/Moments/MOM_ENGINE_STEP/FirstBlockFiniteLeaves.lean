import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstSecondCoveredSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolFiniteLeaves

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

/-!
# Actual left/right pool leaves of one original first-transform block

The common Möbius divisor and finite phase remain in the carrier before
choosing either actual side.  Its scalar is the original Cauchy
normalization, and is multiplied into each genuine nested-measure leaf.
The only extra premises are positivity of the two selected scales.
-/

noncomputable section
open UniqueFactorizationMonoid
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
local instance firstBlockFiniteLeavesCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

private abbrev firstBlock_sum_fintype {α β : Type*} [Fintype α] [Fintype β] :
    Fintype (α ⊕ β) :=
  inferInstance

private abbrev firstBlock_sigma_sigma_fintype {S X : Type*} {F : S → X → Type*}
    [Fintype S] [Fintype X] [∀ a b, Fintype (F a b)] :
    Fintype (Σ a : S, Σ b : X, F a b) :=
  inferInstance

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

variable (s : p.SecondStages (E := E) (hDiff := hDiff))
variable (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ)

/-- The actual first internal divisor and finite phase precede the
left/right choice and all genuine pool/second-transform labels. -/
abbrev CoveredClassKey
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) :=
  (s.left S χ).CoveredLeafKey (p.leftSourceCovers LA S χ) ⊕
    (s.right S χ).CoveredLeafKey (p.rightSourceCovers RA S χ)

abbrev CoveredLeafKey :=
  Σ S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val),
    Σ χ : (PUnit × PUnit) →* Circle, s.CoveredClassKey LA RA S χ

abbrev coveredClassKeyFintype
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) : Fintype (s.CoveredClassKey LA RA S χ) :=
  firstBlock_sum_fintype

attribute [instance] coveredClassKeyFintype

abbrev coveredLeafKeyFintype : Fintype (s.CoveredLeafKey LA RA) :=
  firstBlock_sigma_sigma_fintype

attribute [instance] coveredLeafKeyFintype

variable
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)

def classWeight
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) : ℝ :=
  ‖(moebius S.val : ℂ)‖ *
    ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖ *
      (p.rowBound * Real.sqrt (NL S χ) * Real.sqrt (NR S χ) / 2)

theorem classWeight_nonneg
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) : 0 ≤ classWeight (p := p) NL NR S χ := by
  sorry

theorem classWeight_eq_zero_of_not_squarefree
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) (hS : ¬Squarefree S.val) :
    classWeight (p := p) NL NR S χ = 0 := by
  sorry

def classLeaf (exceptional : s.CoverHybridPredicates LA RA)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) :
    s.CoveredClassKey LA RA S χ → ActualHybridLeaf K Q W E
  | .inl j =>
      ((s.left S χ).coveredLeaf (p.leftSourceCovers LA S χ) (exceptional.left S χ)
        chart.kernel chart.leftPoint j).scale
        (classWeight (p := p) NL NR S χ / NL S χ)
        (div_nonneg (classWeight_nonneg NL NR S χ) (hNL S χ).le)
  | .inr j =>
      ((s.right S χ).coveredLeaf (p.rightSourceCovers RA S χ) (exceptional.right S χ)
        chart.kernel (fun j => -chart.rightPoint j) j).scale
        (classWeight (p := p) NL NR S χ / NR S χ)
        (div_nonneg (classWeight_nonneg NL NR S χ) (hNR S χ).le)

def coveredLeaf (exceptional : s.CoverHybridPredicates LA RA)
    (j : s.CoveredLeafKey LA RA) : ActualHybridLeaf K Q W E :=
  s.classLeaf LA RA NL NR hNL hNR exceptional j.1 j.2.1 j.2.2

/-- The original nonsquarefree first divisors are genuinely zero
weight leaves; no squarefreeness premise is imposed on the pool. -/
theorem coveredLeaf_weight_eq_zero_of_not_squarefree
    (exceptional : s.CoverHybridPredicates LA RA) (j : s.CoveredLeafKey LA RA)
    (hj : ¬Squarefree j.1.val) :
    (s.coveredLeaf LA RA NL NR hNL hNR exceptional j).weight = 0 := by
  sorry

theorem coveredLeaf_weight_nonzero_squarefree
    (exceptional : s.CoverHybridPredicates LA RA) (j : s.CoveredLeafKey LA RA)
    (hj : (s.coveredLeaf LA RA NL NR hNL hNR exceptional j).weight ≠ 0) :
    Squarefree j.1.val := by
  sorry

namespace TerminalCalibration

variable {s LA RA NL NR hNL hNR}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def classZeroBudget (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (ε Czero : ℝ)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) : ℝ :=
  classWeight NL NR S χ *
    ((actualFourierMeasure chart.kernel).real Set.univ * (T.left S χ).zeroBudget ε Czero / NL S χ +
      (actualFourierMeasure chart.kernel).real Set.univ * (T.right S χ).zeroBudget ε Czero / NR S χ)

def classTailBudget (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (Cerror : ℝ)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) : ℝ :=
  classWeight NL NR S χ *
    ((actualFourierMeasure chart.kernel).real Set.univ * (T.left S χ).tailBudget Cerror / NL S χ +
      (actualFourierMeasure chart.kernel).real Set.univ * (T.right S χ).tailBudget Cerror / NR S χ)

def zeroBudget (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (ε Czero : ℝ) : ℝ :=
  ∑ S, ∑ χ, T.classZeroBudget NL NR ε Czero S χ

def tailBudget (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (Cerror : ℝ) : ℝ :=
  ∑ S, ∑ χ, T.classTailBudget NL NR Cerror S χ

/-- No source comparison is assumed: this is an exact evaluation of
the two original integrals by the proven per-pool finite-leaf identity. -/
theorem class_cost_eq_budgets_leaves
    (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
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
  sorry

/-- The actual first block is exactly its computed second zero budget,
computed second tail budget, and finite genuine hybrid leaves. -/
theorem coveredCost_eq_budgets_leaves
    (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
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
  sorry

end TerminalCalibration
end SecondStages
end FirstBlockPoolData
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.SecondStages.TerminalCalibration.coveredCost_eq_budgets_leaves

