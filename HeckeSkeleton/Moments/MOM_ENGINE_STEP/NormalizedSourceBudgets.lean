import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstSourceTerminalNonneg

/-!
# The four actual terminal budgets in parent normalization

Each quantity is the existing source budget divided by the original
parent width exactly once. The signs come from the original finite
source definitions. The regrouping identities are algebraic consequences
of the proved exact finite-leaf decomposition, with no terminal estimate
among their inputs.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments

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
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {omega psi : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K omega psi} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}
variable {sFirst sFirstZero sTail sZero : Finset (ℕ × ℕ)}
variable {k : ℕ} {Lmax Nsave decay : ℝ}

namespace ActualFirstSource.SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))

def normalizedFirstZeroBudget
    (F : s.TerminalCalibration sFirst sFirstZero k Lmax Nsave decay)
    (ε CfirstZero : ℝ) : ℝ :=
  firstZeroBudget F ε CfirstZero / Z ^ (a.m + a.q)

def normalizedSecondZeroBudget
    (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (N : s.Normalization) (ε Czero : ℝ) : ℝ :=
  R.secondZeroBudget T N ε Czero / Z ^ (a.m + a.q)

def normalizedExceptionalBudget
    (L : SourceCartesianAtlas s.columns s.ideal)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization) : ℝ :=
  R.exceptionalBudget L exceptional N / Z ^ (a.m + a.q)

def normalizedTailBudget
    (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (F : s.TerminalCalibration sFirst sFirstZero k Lmax Nsave decay)
    (N : s.Normalization) (CfirstError Cerror : ℝ) : ℝ :=
  R.totalTailBudget T F N CfirstError Cerror / Z ^ (a.m + a.q)

def normalizedTerminalTotal
    (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (F : s.TerminalCalibration sFirst sFirstZero k Lmax Nsave decay)
    (L : SourceCartesianAtlas s.columns s.ideal)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (ε CfirstError CfirstZero Cerror Czero : ℝ) : ℝ :=
  normalizedFirstZeroBudget F ε CfirstZero +
    R.normalizedSecondZeroBudget T N ε Czero +
    R.normalizedExceptionalBudget L exceptional N +
    R.normalizedTailBudget T F N CfirstError Cerror

variable {R}

theorem normalizedFirstZeroBudget_nonneg
    (F : s.TerminalCalibration sFirst sFirstZero k Lmax Nsave decay)
    (ε CfirstZero : ℝ) (hC : 0 ≤ CfirstZero) :
    0 ≤ normalizedFirstZeroBudget F ε CfirstZero :=
  div_nonneg (firstZeroBudget_nonneg F ε CfirstZero hC)
    (Real.rpow_nonneg (zero_le_one.trans P.base_gt_one.le) _)

theorem normalizedSecondZeroBudget_nonneg
    (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (N : s.Normalization) (ε Czero : ℝ) (hC : 0 ≤ Czero) :
    0 ≤ R.normalizedSecondZeroBudget T N ε Czero :=
  div_nonneg (secondZeroBudget_nonneg T N ε Czero hC)
    (Real.rpow_nonneg (zero_le_one.trans P.base_gt_one.le) _)

theorem normalizedExceptionalBudget_nonneg
    (L : SourceCartesianAtlas s.columns s.ideal)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization) :
    0 ≤ R.normalizedExceptionalBudget L exceptional N :=
  div_nonneg (R.exceptionalBudget_nonneg L exceptional N)
    (Real.rpow_nonneg (zero_le_one.trans P.base_gt_one.le) _)

theorem normalizedTailBudget_nonneg
    (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (F : s.TerminalCalibration sFirst sFirstZero k Lmax Nsave decay)
    (N : s.Normalization) (CfirstError Cerror : ℝ)
    (hfirst : 0 ≤ CfirstError) (hsecond : 0 ≤ Cerror) :
    0 ≤ R.normalizedTailBudget T F N CfirstError Cerror :=
  div_nonneg (totalTailBudget_nonneg T N F CfirstError Cerror hfirst hsecond)
    (Real.rpow_nonneg (zero_le_one.trans P.base_gt_one.le) _)

theorem normalizedTerminalTotal_nonneg
    (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (F : s.TerminalCalibration sFirst sFirstZero k Lmax Nsave decay)
    (L : SourceCartesianAtlas s.columns s.ideal)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (ε CfirstError CfirstZero Cerror Czero : ℝ)
    (hFE : 0 ≤ CfirstError) (hFZ : 0 ≤ CfirstZero)
    (hE : 0 ≤ Cerror) (hZ : 0 ≤ Czero) :
    0 ≤ R.normalizedTerminalTotal T F L exceptional N ε CfirstError CfirstZero Cerror Czero :=
  add_nonneg
    (add_nonneg
      (add_nonneg (normalizedFirstZeroBudget_nonneg F ε CfirstZero hFZ)
        (normalizedSecondZeroBudget_nonneg T N ε Czero hZ))
      (normalizedExceptionalBudget_nonneg L exceptional N))
    (normalizedTailBudget_nonneg T F N CfirstError Cerror hFE hE)

/-- The raw and normalized terminal sums use the same four source
quantities and the same single parent denominator. -/
theorem normalizedTerminalTotal_eq_div
    (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (F : s.TerminalCalibration sFirst sFirstZero k Lmax Nsave decay)
    (L : SourceCartesianAtlas s.columns s.ideal)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (ε CfirstError CfirstZero Cerror Czero : ℝ) :
    R.normalizedTerminalTotal T F L exceptional N ε CfirstError CfirstZero Cerror Czero =
      (firstZeroBudget F ε CfirstZero + R.secondZeroBudget T N ε Czero +
        R.exceptionalBudget L exceptional N + R.totalTailBudget T F N CfirstError Cerror) /
          Z ^ (a.m + a.q) := by
  simp only [normalizedTerminalTotal, normalizedFirstZeroBudget,
    normalizedSecondZeroBudget, normalizedExceptionalBudget, normalizedTailBudget, add_div]

/-- This is the original two-transform finite-source identity after
parent normalization. The ordinary remainder is the same live-leaf sum
consumed by the normalized child producer. -/
theorem normalized_totalCost_eq_live
    (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (F : s.TerminalCalibration sFirst sFirstZero k Lmax Nsave decay)
    (L : SourceCartesianAtlas s.columns s.ideal)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (ε CfirstError CfirstZero Cerror Czero : ℝ) :
    ((s.fiber : ℝ) * (F.cost ε CfirstError CfirstZero +
      R.coveredCost T L exceptional N ε Cerror Czero)) / Z ^ (a.m + a.q) =
      R.normalizedTerminalTotal T F L exceptional N ε CfirstError CfirstZero Cerror Czero +
        R.ordinaryBudget L exceptional N / Z ^ (a.m + a.q) := by
  rw [R.totalCost_eq_live T F L exceptional N ε CfirstError CfirstZero Cerror Czero,
    normalizedTerminalTotal_eq_div, add_div]

/-- A raw estimate is equivalent to its parent-normalized estimate;
this lemma adds no estimate as a source input. -/
theorem normalizedTerminalTotal_le_iff
    (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (F : s.TerminalCalibration sFirst sFirstZero k Lmax Nsave decay)
    (L : SourceCartesianAtlas s.columns s.ideal)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (ε CfirstError CfirstZero Cerror Czero B : ℝ) :
    R.normalizedTerminalTotal T F L exceptional N ε CfirstError CfirstZero Cerror Czero ≤ B ↔
      firstZeroBudget F ε CfirstZero + R.secondZeroBudget T N ε Czero +
        R.exceptionalBudget L exceptional N + R.totalTailBudget T F N CfirstError Cerror ≤
          B * Z ^ (a.m + a.q) := by
  rw [normalizedTerminalTotal_eq_div,
    div_le_iff₀ (Real.rpow_pos_of_pos (zero_lt_one.trans P.base_gt_one) _)]

end ActualFirstSource.SecondStages
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.normalizedTerminalTotal_nonneg
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.normalized_totalCost_eq_live

