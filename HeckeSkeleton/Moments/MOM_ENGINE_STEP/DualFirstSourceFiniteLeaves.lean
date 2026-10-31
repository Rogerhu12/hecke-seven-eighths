import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualFirstBlockFiniteLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstSourceFiniteLeaves

/-!
# The signed original parent and its same finite live family

Every original common label, mask divisor, internal divisor, phase,
pool tag, covered occurrence, second row label and allocation remains
in the pre-existing finite carrier. The zero-weight removal and the
ordinary/exceptional partition are the existing proved `liveLeaves`
identities, independent of either Fourier parameter.

The two pure-dual zeros and the two physical tails come from the new
signed calibrations. The original `parentLeaf`, `exceptionalBudget`,
and `ordinaryBudget` are reused verbatim. No whole-source, terminal,
or finite-family identity is introduced as a primitive hypothesis.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

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

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {omega psi : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K omega psi} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}

namespace ActualFirstSource.SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)

variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def dualZeroBudget (T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (N : s.Normalization) (ε Czero : ℝ) : ℝ :=
  ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
    (T v D).zeroBudget (N.left v D) (N.right v D) ε Czero

def dualTailBudget (T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (N : s.Normalization) (Cerror : ℝ) : ℝ :=
  ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
    (T v D).tailBudget (N.left v D) (N.right v D) Cerror

/-- The original covered cost itself is exactly flattened; no
finite-family identity is included among primitive inputs. -/
theorem dualCoveredCost_eq_budgets_leaves
    (T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (L : SourceCartesianAtlas s.columns s.ideal)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (ε Cerror Czero : ℝ) :
    R.dualCoveredCost T L exceptional N ε Cerror Czero =
      R.dualZeroBudget T N ε Czero + R.dualTailBudget T N Cerror +
        ∑ j : R.CoveredLeafKey L, (R.coveredLeaf L exceptional N j).cost := by
  unfold dualCoveredCost
  calc
    _ = ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
        ((T v D).zeroBudget (N.left v D) (N.right v D) ε Czero +
          (T v D).tailBudget (N.left v D) (N.right v D) Cerror +
          ∑ j : (R v D).CoveredLeafKey L L,
            ((R v D).coveredLeaf L L (N.left v D) (N.right v D)
              (N.left_pos v D) (N.right_pos v D) (exceptional v D) j).cost) := by
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro D _
      exact (T v D).coveredCost_eq_budgets_leaves L L (exceptional v D)
        (N.left v D) (N.right v D) (N.left_pos v D) (N.right_pos v D) ε Cerror Czero
    _ = _ := by
      simp only [dualZeroBudget, dualTailBudget, Fintype.sum_sigma, coveredLeaf, Finset.sum_add_distrib]

def dualSecondZeroBudget (T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (N : s.Normalization) (ε Czero : ℝ) : ℝ :=
  (s.fiber : ℝ) * R.dualZeroBudget T N ε Czero

def dualSecondTailBudget (T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (N : s.Normalization) (Cerror : ℝ) : ℝ :=
  (s.fiber : ℝ) * R.dualTailBudget T N Cerror

variable {sFirst sFirstZero : Finset (ℕ × ℕ)}

def dualFirstZeroBudget
    (F : s.DualTerminalCalibration sFirst sFirstZero k Lmax Nsave decay) (ε CfirstZero : ℝ) : ℝ :=
  (s.fiber : ℝ) * CfirstZero * F.zeroAmplitude * Z ^ (F.zeroProductExponent * ε)

def dualFirstTailBudget
    (F : s.DualTerminalCalibration sFirst sFirstZero k Lmax Nsave decay) (CfirstError : ℝ) : ℝ :=
  (s.fiber : ℝ) * CfirstError * F.tailAmplitude * Z ^ (-Nsave)

def dualTotalTailBudget (T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (F : s.DualTerminalCalibration sFirst sFirstZero k Lmax Nsave decay)
    (N : s.Normalization) (CfirstError Cerror : ℝ) : ℝ :=
  (s.fiber : ℝ) * (CfirstError * F.tailAmplitude * Z ^ (-Nsave) + R.dualTailBudget T N Cerror)

/-- Both original physical tails retain the same parent fibre. -/
theorem dualTotalTailBudget_eq_first_add_second
    (T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (F : s.DualTerminalCalibration sFirst sFirstZero k Lmax Nsave decay)
    (N : s.Normalization) (CfirstError Cerror : ℝ) :
    R.dualTotalTailBudget T F N CfirstError Cerror =
      dualFirstTailBudget F CfirstError + R.dualSecondTailBudget T N Cerror := by
  unfold dualTotalTailBudget dualFirstTailBudget dualSecondTailBudget
  ring

/-- Exact five-part decomposition of the true original source exit.
The live carrier is selected before both continuous parameters. -/
theorem dualTotalCost_eq_live
    (T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (F : s.DualTerminalCalibration sFirst sFirstZero k Lmax Nsave decay)
    (L : SourceCartesianAtlas s.columns s.ideal)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (ε CfirstError CfirstZero Cerror Czero : ℝ) :
    (s.fiber : ℝ) * (F.cost ε CfirstError CfirstZero +
      R.dualCoveredCost T L exceptional N ε Cerror Czero) =
      dualFirstZeroBudget F ε CfirstZero + R.dualSecondZeroBudget T N ε Czero +
        R.exceptionalBudget L exceptional N + R.dualTotalTailBudget T F N CfirstError Cerror +
        R.ordinaryBudget L exceptional N := by
  have hleaves :
      (s.fiber : ℝ) * (∑ j : R.CoveredLeafKey L, (R.coveredLeaf L exceptional N j).cost) =
        R.exceptionalBudget L exceptional N + R.ordinaryBudget L exceptional N := by
    calc
      _ = ∑ j : R.CoveredLeafKey L, (R.parentLeaf L exceptional N j).cost := by
        simp only [parentLeaf, ActualHybridLeaf.scale_cost, Finset.mul_sum]
      _ = ∑ j : R.liveLeaves L exceptional N, (R.parentLeaf L exceptional N j.val).cost :=
        ActualHybridFamily.sum_cost_eq_live _
      _ = _ := by
        simp only [exceptionalBudget, ordinaryBudget, ActualHybridLeaf.cost, Finset.sum_add_distrib]
  rw [R.dualCoveredCost_eq_budgets_leaves T L exceptional N ε Cerror Czero]
  calc
    _ = dualFirstZeroBudget F ε CfirstZero + R.dualSecondZeroBudget T N ε Czero +
        R.dualTotalTailBudget T F N CfirstError Cerror +
        (s.fiber : ℝ) * (∑ j : R.CoveredLeafKey L, (R.coveredLeaf L exceptional N j).cost) := by
      unfold ActualFirstSource.DualTerminalCalibration.cost dualFirstZeroBudget dualSecondZeroBudget dualTotalTailBudget
      ring
    _ = _ := by rw [hleaves]; ring

end ActualFirstSource.SecondStages

variable (hΓ μv hDiff)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- Uniform signed parent-to-finite-source reduction. The same live
ordinary leaves are left for the capacity producer; the two pure-dual
zeros, exceptional part, and both original cutoff tails are the four
explicit terminal contributions. No finite-family decomposition or
aggregate terminal bound is assumed. -/
theorem actual_parent_two_stage_dual_finite_leaf_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
    (rowBallSize : ℝ) (k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (Lmax Nsave ξmax : ℝ) (hξmax : 0 < ξmax) :
    ∃ (decay : ℝ) (hdecay : 1 < decay),
      decay = tailDecayForWidth Lmax Nsave ξmax ∧
      firstTailCutoffExponent Lmax Nsave decay ≤ ξmax ∧
    ∃ sFirst sFirstZero sTail sZero : Finset (ℕ × ℕ),
    ∃ CfirstError CfirstZero Cerror Czero : ℝ,
      0 ≤ CfirstError ∧ 0 < CfirstZero ∧ 0 ≤ Cerror ∧ 0 < Czero ∧
    ∀ (Z ell eps : ℝ) (bad : Finset (HeightOneSpectrum (𝓞 K)))
      (P : PowerScaleExteriorPool A bad Z ell eps),
    ∀ {omega psi : HeckeCharacter K} (centered : Bool) (d : MomentData K omega psi)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ s : ActualFirstSource (E := W) hΓ μv C P
      (rowBallFiniteFamily K A.Sf rowBallSize) centered d a t Y₁ Y₂ X hX,
    ∀ coefficient : s.Column → ℂ,
      (∀ i j, s.profiles i j = (coefficient i * star (coefficient j)) •
        CanonicalRowBall.archTest K A.Sf rowBallSize) →
    ∀ N : s.Normalization, ∀ R : s.SecondStages (E := E) (hDiff := hDiff),
    ∀ conditions : R.DualSourceConditions,
    ∀ T : R.DualTerminalCalibration sTail sZero k Lmax Nsave decay,
    ∀ F : s.DualTerminalCalibration sFirst sFirstZero k Lmax Nsave decay,
    ∀ (L : SourceCartesianAtlas s.columns s.ideal) (exceptional : R.CoverHybridPredicates L),
      X ≤ Z ^ ξmax ∧
      pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
        ActualFirstSource.SecondStages.dualFirstZeroBudget F ε CfirstZero +
          R.dualSecondZeroBudget T N ε Czero + R.exceptionalBudget L exceptional N +
          R.dualTotalTailBudget T F N CfirstError Cerror + R.ordinaryBudget L exceptional N := by
  obtain ⟨decay, hdecay, hchoice, hq, sFirst, sFirstZero, sTail, sZero,
      CfirstError, CfirstZero, Cerror, Czero, hCfE, hCfZ, hCE, hCZ, hb⟩ :=
    actual_parent_two_stage_dual_covered_terminal_bound
      (W := W) (E := E) (ν := ν) (μ := μ) hΓ μv hDiff
      C Drecipe hD rowBallSize k ε hε Lmax Nsave ξmax hξmax
  refine ⟨decay, hdecay, hchoice, hq, sFirst, sFirstZero, sTail, sZero,
    CfirstError, CfirstZero, Cerror, Czero, hCfE, hCfZ, hCE, hCZ, ?_⟩
  intro Z ell eps bad P omega psi centered d a t Y₁ Y₂ X hX s coefficient hprofiles
    N R conditions T F L exceptional
  obtain ⟨hcutoff, hp⟩ := hb Z ell eps bad P centered d a t Y₁ Y₂ X hX s
    coefficient hprofiles N R conditions T F L exceptional
  rw [R.dualTotalCost_eq_live T F L exceptional N ε CfirstError CfirstZero Cerror Czero] at hp
  exact ⟨hcutoff, hp⟩

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.dualCoveredCost_eq_budgets_leaves
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.dualTotalCost_eq_live
#print axioms HeckeSkeleton.Moments.EngineStep.actual_parent_two_stage_dual_finite_leaf_bound

