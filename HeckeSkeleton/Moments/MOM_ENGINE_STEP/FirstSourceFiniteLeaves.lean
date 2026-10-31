import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstBlockFiniteLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.GatedGaussStages
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridLeafSupport

/-!
# The original parent reaches its actual finite live two-transform leaves

The dependent finite carrier keeps every original first common label,
mask divisor, internal divisor and phase, side, pool main/error prime
and valuation, second common label and mask, both cover and occurrence
keys, row label, second Möbius divisor, phase and both allocations.
Zero weights and identically zero whole columns are removed by proved
identities.  All remaining leaves retain the original two fixed kernels
and their actual common positive Fourier measure.

The displayed first-zero, second-zero and tail budgets are the exact
previous terminal budgets, not new assumptions on an aggregate source.
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

/-- The actual original first labels precede all previously constructed
finite labels of both pool sides. -/
abbrev CoveredLeafKey :=
  Σ v : s.CommonLabel, Σ D : ((s.block v).mask s.mask).powerset,
    (R v D).CoveredLeafKey L L

def coveredLeaf (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.CoveredLeafKey L) : ActualHybridLeaf K Q W E :=
  (R j.1 j.2.1).coveredLeaf L L (N.left j.1 j.2.1) (N.right j.1 j.2.1)
    (N.left_pos j.1 j.2.1) (N.right_pos j.1 j.2.1)
    (exceptional j.1 j.2.1) j.2.2

def parentLeaf (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.CoveredLeafKey L) : ActualHybridLeaf K Q W E :=
  (R.coveredLeaf L exceptional N j).scale (s.fiber : ℝ) (Nat.cast_nonneg _)

def liveLeaves (exceptional : R.CoverHybridPredicates L) (N : s.Normalization) :
    Finset (R.CoveredLeafKey L) :=
  ActualHybridFamily.live (R.parentLeaf L exceptional N)

theorem liveLeaves_spec (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.liveLeaves L exceptional N) :
    (R.parentLeaf L exceptional N j.val).Live :=
  ActualHybridFamily.live_spec _ j

/-- A retained label's first internal divisor is squarefree because
the actual original Möbius weight is nonzero, not because the divisor
pool was assumed squarefree. -/
theorem live_first_divisor_squarefree
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.liveLeaves L exceptional N) : Squarefree j.val.2.2.1.val := by
  have hw := (R.liveLeaves_spec L exceptional N j).1
  change (s.fiber : ℝ) * (R.coveredLeaf L exceptional N j.val).weight ≠ 0 at hw
  exact (R j.val.1 j.val.2.1).coveredLeaf_weight_nonzero_squarefree L L
    (N.left j.val.1 j.val.2.1) (N.right j.val.1 j.val.2.1)
    (N.left_pos j.val.1 j.val.2.1) (N.right_pos j.val.1 j.val.2.1)
    (exceptional j.val.1 j.val.2.1) j.val.2.2 (mul_ne_zero_iff.mp hw).2

variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def zeroBudget (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (N : s.Normalization) (ε Czero : ℝ) : ℝ :=
  ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
    (T v D).zeroBudget (N.left v D) (N.right v D) ε Czero

def tailBudget (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (N : s.Normalization) (Cerror : ℝ) : ℝ :=
  ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
    (T v D).tailBudget (N.left v D) (N.right v D) Cerror

/-- The original covered cost itself is exactly flattened; no
finite-family identity is included among primitive inputs. -/
theorem coveredCost_eq_budgets_leaves
    (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (L : SourceCartesianAtlas s.columns s.ideal)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (ε Cerror Czero : ℝ) :
    R.coveredCost T L exceptional N ε Cerror Czero =
      R.zeroBudget T N ε Czero + R.tailBudget T N Cerror +
        ∑ j : R.CoveredLeafKey L, (R.coveredLeaf L exceptional N j).cost := by
  unfold coveredCost
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
      simp only [zeroBudget, tailBudget, Fintype.sum_sigma, coveredLeaf, Finset.sum_add_distrib]

def secondZeroBudget (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (N : s.Normalization) (ε Czero : ℝ) : ℝ :=
  (s.fiber : ℝ) * R.zeroBudget T N ε Czero

def exceptionalBudget (exceptional : R.CoverHybridPredicates L) (N : s.Normalization) : ℝ :=
  ∑ j : R.liveLeaves L exceptional N, (R.parentLeaf L exceptional N j.val).exceptionalCost

def ordinaryBudget (exceptional : R.CoverHybridPredicates L) (N : s.Normalization) : ℝ :=
  ∑ j : R.liveLeaves L exceptional N, (R.parentLeaf L exceptional N j.val).ordinaryCost

variable {sFirst sFirstZero : Finset (ℕ × ℕ)}

def firstZeroBudget
    (F : s.TerminalCalibration sFirst sFirstZero k Lmax Nsave decay) (ε CfirstZero : ℝ) : ℝ :=
  (s.fiber : ℝ) * CfirstZero * F.zeroAmplitude * Z ^ (F.productExponent * ε)

def totalTailBudget (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (F : s.TerminalCalibration sFirst sFirstZero k Lmax Nsave decay)
    (N : s.Normalization) (CfirstError Cerror : ℝ) : ℝ :=
  (s.fiber : ℝ) * (CfirstError * F.tailAmplitude * Z ^ (-Nsave) + R.tailBudget T N Cerror)

/-- Exact five-part decomposition of the true original source exit.
The live carrier is selected before both continuous parameters. -/
theorem totalCost_eq_live
    (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (F : s.TerminalCalibration sFirst sFirstZero k Lmax Nsave decay)
    (L : SourceCartesianAtlas s.columns s.ideal)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (ε CfirstError CfirstZero Cerror Czero : ℝ) :
    (s.fiber : ℝ) * (F.cost ε CfirstError CfirstZero +
      R.coveredCost T L exceptional N ε Cerror Czero) =
      firstZeroBudget F ε CfirstZero + R.secondZeroBudget T N ε Czero +
        R.exceptionalBudget L exceptional N + R.totalTailBudget T F N CfirstError Cerror +
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
  rw [R.coveredCost_eq_budgets_leaves T L exceptional N ε Cerror Czero]
  calc
    _ = firstZeroBudget F ε CfirstZero + R.secondZeroBudget T N ε Czero +
        R.totalTailBudget T F N CfirstError Cerror +
        (s.fiber : ℝ) * (∑ j : R.CoveredLeafKey L, (R.coveredLeaf L exceptional N j).cost) := by
      unfold ActualFirstSource.TerminalCalibration.cost firstZeroBudget secondZeroBudget totalTailBudget
      ring
    _ = _ := by rw [hleaves]; ring

theorem exceptionalBudget_nonneg (exceptional : R.CoverHybridPredicates L) (N : s.Normalization) :
    0 ≤ R.exceptionalBudget L exceptional N :=
  Finset.sum_nonneg fun j _ => (R.parentLeaf L exceptional N j.val).exceptionalCost_nonneg

theorem ordinaryBudget_nonneg (exceptional : R.CoverHybridPredicates L) (N : s.Normalization) :
    0 ≤ R.ordinaryBudget L exceptional N :=
  Finset.sum_nonneg fun j _ => (R.parentLeaf L exceptional N j.val).ordinaryCost_nonneg

end ActualFirstSource.SecondStages

variable (hΓ μv hDiff)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- Uniform actual parent-to-finite-source theorem.  Gating is performed
by the engine and the terminal terms are the earlier proved zero/tail
budgets.  The remaining ordinary terms are actual finite-polynomial
paired energies under each leaf's fixed positive nested measure. -/
theorem actual_parent_two_stage_finite_leaf_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) (Lmax Nsave ξmax : ℝ) (hξmax : 0 < ξmax) :
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
    ∀ s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX,
    ∀ N : s.Normalization, ∀ R : s.SecondStages (E := E) (hDiff := hDiff),
    ∀ T : R.TerminalCalibration sTail sZero k Lmax Nsave decay,
    ∀ F : s.TerminalCalibration sFirst sFirstZero k Lmax Nsave decay,
    ∀ (L : SourceCartesianAtlas s.columns s.ideal) (exceptional : R.gated.CoverHybridPredicates L),
      X ≤ Z ^ ξmax ∧
      pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
        ActualFirstSource.SecondStages.firstZeroBudget F ε CfirstZero +
          R.gated.secondZeroBudget T.gated N ε Czero +
          R.gated.exceptionalBudget L exceptional N +
          R.gated.totalTailBudget T.gated F N CfirstError Cerror +
          R.gated.ordinaryBudget L exceptional N := by
  obtain ⟨decay, hdecay, hchoice, hq, sFirst, sFirstZero, sTail, sZero,
    CfirstError, CfirstZero, Cerror, Czero, hCfE, hCfZ, hCE, hCZ, hb⟩ :=
    actual_parent_gated_two_stage_covered_terminal_bound (W := W) (E := E) (ν := ν) (μ := μ)
      hΓ μv hDiff C Drecipe hD finiteTest hlc hcs k ε hε Lmax Nsave ξmax hξmax
  refine ⟨decay, hdecay, hchoice, hq, sFirst, sFirstZero, sTail, sZero,
    CfirstError, CfirstZero, Cerror, Czero, hCfE, hCfZ, hCE, hCZ, ?_⟩
  intro Z ell eps bad P omega psi centered d a t Y₁ Y₂ X hX s N R T F L exceptional
  obtain ⟨hcutoff, hp⟩ := hb Z ell eps bad P centered d a t Y₁ Y₂ X hX s N R T F L exceptional
  rw [R.gated.totalCost_eq_live T.gated F L exceptional N ε CfirstError CfirstZero Cerror Czero] at hp
  exact ⟨hcutoff, hp⟩

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.totalCost_eq_live
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.live_first_divisor_squarefree
#print axioms HeckeSkeleton.Moments.EngineStep.actual_parent_two_stage_finite_leaf_bound

