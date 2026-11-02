import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectSecondStages
set_option linter.unusedSectionVars false

/-!
# Actual canonical leaves of the direct entrance

The first divisor and finite phase precede the actual left/right source
choice. Both direct sources produce the same `ActualHybridLeaf` as the
amplified entrance. Original row multiplicities and normalizers occur
exactly once, with the original double Fourier measure retained.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments HeckePort.Moments.MobiusRegroup

private theorem direct_finite_scalar_bound
    {I J X : Type*} [Fintype I] [Fintype J] [MeasurableSpace X]
    {L R : I → J → Type*}
    [instL : ∀ i j, Fintype (L i j)] [instR : ∀ i j, Fintype (R i j)]
    (μ : Measure X) (mass : ℝ)
    (a : I → ℝ) (b : J → ℝ)
    (c NL NR zL zR tL tR : I → J → ℝ)
    (fL fR gL gR : I → J → X → ℝ)
    (costL : ∀ i j, L i j → ℝ) (costR : ∀ i j, R i j → ℝ)
    (leaf : (Σ i, Σ j, L i j ⊕ R i j) → ℝ)
    (hNL : ∀ i j, 0 ≤ NL i j) (hNR : ∀ i j, 0 ≤ NR i j)
    (hweight : ∀ i j, 0 ≤ a i * b j * c i j)
    (hphaseL : ∀ i j x, gL i j x = fL i j x)
    (hphaseR : ∀ i j x, gR i j x = fR i j x)
    (hleft : ∀ i j, (∫ x, gL i j x ∂μ) ≤
      mass * (zL i j + tL i j) + ∑ k, costL i j k)
    (hright : ∀ i j, (∫ x, gR i j x ∂μ) ≤
      mass * (zR i j + tR i j) + ∑ k, costR i j k)
    (hleafL : ∀ i j k, leaf ⟨i, j, .inl k⟩ =
      (a i * b j * c i j / NL i j) * costL i j k)
    (hleafR : ∀ i j k, leaf ⟨i, j, .inr k⟩ =
      (a i * b j * c i j / NR i j) * costR i j k) :
    (∑ i, a i * ∑ j, b j * c i j *
      ((∫ x, fL i j x / NL i j ∂μ) + ∫ x, fR i j x / NR i j ∂μ)) ≤
      (∑ i, ∑ j, (a i * b j * c i j) *
        (mass * zL i j / NL i j + mass * zR i j / NR i j)) +
      (∑ i, ∑ j, (a i * b j * c i j) *
        (mass * tL i j / NL i j + mass * tR i j / NR i j)) +
      ∑ q, leaf q := by
  simp only [Finset.mul_sum, Fintype.sum_sigma]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  have hl : (∫ x, fL i j x ∂μ) ≤
      mass * (zL i j + tL i j) + ∑ k, costL i j k := by
    calc
      _ = ∫ x, gL i j x ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => (hphaseL i j x).symm)
      _ ≤ _ := hleft i j
  have hr : (∫ x, fR i j x ∂μ) ≤
      mass * (zR i j + tR i j) + ∑ k, costR i j k := by
    calc
      _ = ∫ x, gR i j x ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => (hphaseR i j x).symm)
      _ ≤ _ := hright i j
  rw [integral_div, integral_div]
  have hh := mul_le_mul_of_nonneg_left
    (add_le_add (div_le_div_of_nonneg_right hl (hNL i j))
      (div_le_div_of_nonneg_right hr (hNR i j))) (hweight i j)
  convert hh using 1
  · ring
  · simp only [Fintype.sum_sum_type, hleafL, hleafR]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    ring

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
local instance directFiniteLeavesCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Z : ℝ}

namespace FirstBlockDirectData

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockDirectData chart M X hX}

namespace SecondStages

variable (s : p.SecondStages (E := E) (hDiff := hDiff))
variable (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ)

/-- The actual first internal divisor and finite phase precede the
left/right choice and all genuine second-transform labels. -/
abbrev CoveredClassKey
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) :=
  (s.left S χ).CoveredLeafKey (p.leftSourceCover LA S χ) (p.leftSourceCover LA S χ) ⊕
    (s.right S χ).CoveredLeafKey (p.rightSourceCover RA S χ) (p.rightSourceCover RA S χ)

abbrev CoveredLeafKey :=
  Σ S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val),
    Σ χ : (PUnit × PUnit) →* Circle, s.CoveredClassKey LA RA S χ

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
    (χ : (PUnit × PUnit) →* Circle) : 0 ≤ classWeight (p := p) NL NR S χ :=
  mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (div_nonneg (mul_nonneg (mul_nonneg p.rowBound_nonneg (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)) (by norm_num))

theorem classWeight_eq_zero_of_not_squarefree
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) (hS : ¬Squarefree S.val) :
    classWeight (p := p) NL NR S χ = 0 := by
  simp only [classWeight, moebius_of_not_squarefree hS, Int.cast_zero,
    norm_zero, zero_mul]

def classLeaf (exceptional : s.CoverHybridPredicates LA RA)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) :
    s.CoveredClassKey LA RA S χ → ActualHybridLeaf K Q W E
  | .inl j =>
      ((s.left S χ).fiberCoveredLeaf (p.leftSourceCover LA S χ) (p.leftSourceCover LA S χ) (exceptional.left S χ)
        chart.kernel chart.leftPoint j).scale
        (classWeight (p := p) NL NR S χ / NL S χ)
        (div_nonneg (classWeight_nonneg NL NR S χ) (hNL S χ).le)
  | .inr j =>
      ((s.right S χ).fiberCoveredLeaf (p.rightSourceCover RA S χ) (p.rightSourceCover RA S χ) (exceptional.right S χ)
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
  rcases j with ⟨S, χ, j | j⟩ <;>
    simp only [coveredLeaf, classLeaf, ActualHybridLeaf.scale,
      classWeight_eq_zero_of_not_squarefree NL NR S χ hj, zero_div, zero_mul]

theorem coveredLeaf_weight_nonzero_squarefree
    (exceptional : s.CoverHybridPredicates LA RA) (j : s.CoveredLeafKey LA RA)
    (hj : (s.coveredLeaf LA RA NL NR hNL hNR exceptional j).weight ≠ 0) :
    Squarefree j.1.val := by
  by_contra hS
  exact hj (s.coveredLeaf_weight_eq_zero_of_not_squarefree LA RA NL NR hNL hNR exceptional j hS)

namespace TerminalCalibration

variable {s LA RA NL NR hNL hNR}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def classZeroBudget (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (ε Czero : ℝ)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) : ℝ :=
  classWeight NL NR S χ *
    ((actualFourierMeasure chart.kernel).real Set.univ * (T.left S χ).zeroBudget ε Czero / NL S χ +
      (actualFourierMeasure chart.kernel).real Set.univ * (T.right S χ).zeroBudget ε Czero / NR S χ)

def classTailBudget (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (Cerror : ℝ)
    (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) : ℝ :=
  classWeight NL NR S χ *
    ((actualFourierMeasure chart.kernel).real Set.univ * (T.left S χ).tailBudget Cerror / NL S χ +
      (actualFourierMeasure chart.kernel).real Set.univ * (T.right S χ).tailBudget Cerror / NR S χ)

def zeroBudget (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (ε Czero : ℝ) : ℝ :=
  ∑ S, ∑ χ, T.classZeroBudget NL NR ε Czero S χ

def tailBudget (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (Cerror : ℝ) : ℝ :=
  ∑ S, ∑ χ, T.classTailBudget NL NR Cerror S χ


/-- The direct first-block total is formed from the canonical actual
terminal budgets and the actual second-transform hybrid leaves. -/
def finiteCost
    (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ)
    (exceptional : s.CoverHybridPredicates LA RA)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)
    (ε Cerror Czero : ℝ) : ℝ :=
  T.zeroBudget NL NR ε Czero + T.tailBudget NL NR Cerror +
    ∑ j : s.CoveredLeafKey LA RA,
      (s.coveredLeaf LA RA NL NR hNL hNR exceptional j).cost

/-- The source substitution here is instantiated by the proved
universal direct/second-stage bound in the parent theorem below. No
aggregate source or leaf estimate is part of the source calibration. -/
theorem linearized_le_finiteCost
    (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ)
    (exceptional : s.CoverHybridPredicates LA RA)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)
    (ε Cerror Czero : ℝ)
    (hstageLeft : ∀ (G : ActualGaussSource C ι)
      (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
      (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)
      (LC RC : SourceCartesianCover G.columns G.ideal)
      (ex : s.CoverHybridPredicates LC RC) (F : SchwartzMap W ℂ) (x : ι → W),
      (∫ ξ, G.phaseEnergy (hDiff := hDiff) x ξ ∂actualFourierMeasure F) ≤
        (actualFourierMeasure F).real Set.univ *
          (T.zeroBudget ε Czero + T.tailBudget Cerror) +
        ∑ j : s.CoveredLeafKey LC RC,
          (s.fiberCoveredLeaf LC RC ex F x j).cost)
    (hstageRight : ∀ (G : ActualGaussSource C κ)
      (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
      (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)
      (LC RC : SourceCartesianCover G.columns G.ideal)
      (ex : s.CoverHybridPredicates LC RC) (F : SchwartzMap W ℂ) (x : κ → W),
      (∫ ξ, G.phaseEnergy (hDiff := hDiff) x ξ ∂actualFourierMeasure F) ≤
        (actualFourierMeasure F).real Set.univ *
          (T.zeroBudget ε Czero + T.tailBudget Cerror) +
        ∑ j : s.CoveredLeafKey LC RC,
          (s.fiberCoveredLeaf LC RC ex F x j).cost) :
    p.linearizedCost hDiff NL NR ≤
      T.finiteCost LA RA exceptional NL NR hNL hNR ε Cerror Czero := by
  have hleftStage :=
    fun (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
      (χ : (PUnit × PUnit) →* Circle) =>
      hstageLeft (p.leftData.directSource (p.leftDivisorCoefficient S χ))
        (s.left S χ) (T.left S χ)
        (p.leftSourceCover LA S χ) (p.leftSourceCover LA S χ)
        (exceptional.left S χ) chart.kernel chart.leftPoint
  have hrightStage :=
    fun (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
      (χ : (PUnit × PUnit) →* Circle) =>
      hstageRight (p.rightData.directSource (p.rightDivisorCoefficient S χ))
        (s.right S χ) (T.right S χ)
        (p.rightSourceCover RA S χ) (p.rightSourceCover RA S χ)
        (exceptional.right S χ) chart.kernel (fun j => -chart.rightPoint j)
  exact direct_finite_scalar_bound
    (I := divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
    (J := (PUnit × PUnit) →* Circle)
    (L := fun S χ => (s.left S χ).CoveredLeafKey
      (p.leftSourceCover LA S χ) (p.leftSourceCover LA S χ))
    (R := fun S χ => (s.right S χ).CoveredLeafKey
      (p.rightSourceCover RA S χ) (p.rightSourceCover RA S χ))
    (instL := fun S χ => inferInstance) (instR := fun S χ => inferInstance)
    (μ := actualFourierMeasure chart.kernel)
    (mass := (actualFourierMeasure chart.kernel).real Set.univ)
    (a := fun S => ‖(moebius S.val : ℂ)‖)
    (b := fun χ => ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) χ‖)
    (c := fun S χ => p.rowBound * Real.sqrt (NL S χ) * Real.sqrt (NR S χ) / 2)
    (NL := NL) (NR := NR)
    (zL := fun S χ => (T.left S χ).zeroBudget ε Czero)
    (zR := fun S χ => (T.right S χ).zeroBudget ε Czero)
    (tL := fun S χ => (T.left S χ).tailBudget Cerror)
    (tR := fun S χ => (T.right S χ).tailBudget Cerror)
    (fL := fun S χ ξ => (p.leftData.directSource
      (FirstGaussPoolData.twistedCoefficient
        (p.leftDivisorCoefficient S χ) chart.leftPoint ξ)).energy hDiff)
    (fR := fun S χ ξ => (p.rightData.directSource
      (FirstGaussPoolData.twistedCoefficient
        (p.rightDivisorCoefficient S χ) (fun j => -chart.rightPoint j) ξ)).energy hDiff)
    (gL := fun S χ ξ => (p.leftData.directSource (p.leftDivisorCoefficient S χ)).phaseEnergy
      (hDiff := hDiff) chart.leftPoint ξ)
    (gR := fun S χ ξ => (p.rightData.directSource (p.rightDivisorCoefficient S χ)).phaseEnergy
      (hDiff := hDiff) (fun j => -chart.rightPoint j) ξ)
    (costL := fun S χ j => ((s.left S χ).fiberCoveredLeaf
      (p.leftSourceCover LA S χ) (p.leftSourceCover LA S χ) (exceptional.left S χ)
      chart.kernel chart.leftPoint j).cost)
    (costR := fun S χ j => ((s.right S χ).fiberCoveredLeaf
      (p.rightSourceCover RA S χ) (p.rightSourceCover RA S χ) (exceptional.right S χ)
      chart.kernel (fun j => -chart.rightPoint j) j).cost)
    (leaf := fun j : s.CoveredLeafKey LA RA =>
      (s.coveredLeaf LA RA NL NR hNL hNR exceptional j).cost)
    (hNL := fun S χ => (hNL S χ).le)
    (hNR := fun S χ => (hNR S χ).le)
    (hweight := fun S χ => classWeight_nonneg (p := p) NL NR S χ)
    (hphaseL := fun S χ ξ =>
      p.leftData.directSource_phaseEnergy (p.leftDivisorCoefficient S χ) chart.leftPoint ξ)
    (hphaseR := fun S χ ξ =>
      p.rightData.directSource_phaseEnergy (p.rightDivisorCoefficient S χ)
        (fun j => -chart.rightPoint j) ξ)
    (hleft := hleftStage)
    (hright := hrightStage)
    (hleafL := fun S χ j => ((s.left S χ).fiberCoveredLeaf
      (p.leftSourceCover LA S χ) (p.leftSourceCover LA S χ) (exceptional.left S χ)
      chart.kernel chart.leftPoint j).scale_cost
        (classWeight NL NR S χ / NL S χ)
        (div_nonneg (classWeight_nonneg NL NR S χ) (hNL S χ).le))
    (hleafR := fun S χ j => ((s.right S χ).fiberCoveredLeaf
      (p.rightSourceCover RA S χ) (p.rightSourceCover RA S χ) (exceptional.right S χ)
      chart.kernel (fun j => -chart.rightPoint j) j).scale_cost
        (classWeight NL NR S χ / NR S χ)
        (div_nonneg (classWeight_nonneg NL NR S χ) (hNR S χ).le))

end TerminalCalibration
end SecondStages
end FirstBlockDirectData
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.SecondStages.TerminalCalibration.linearized_le_finiteCost
