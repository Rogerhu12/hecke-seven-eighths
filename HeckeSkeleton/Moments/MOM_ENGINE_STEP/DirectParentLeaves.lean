import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectFiniteLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectFirstTerminal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

/-!
# The original direct parent produces the canonical finite hybrid leaves

No positive prime-pool witness is required. The original first source,
its true internal divisor/phase labels, and the same universal second
transform give the actual finite hybrid family. Both zero terms and the
original physical tails are bounded before this family is normalized.
The common capacity producer therefore receives the same leaf type for
both direct and amplified entrances.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup MeasureTheory

private theorem direct_parent_sigma_sum_cost
    {I : Type*} {D : I → Type*} {J : (i : I) → D i → Type*}
    [Fintype I] [instD : ∀ i, Fintype (D i)]
    [instJ : ∀ i d, Fintype (J i d)]
    (w : ℝ) (zero tail : ∀ i, D i → ℝ)
    (leaf : ∀ i d, J i d → ℝ)
    (parent : (Σ i, Σ d : D i, J i d) → ℝ)
    (hparent : ∀ i d j, parent ⟨i, d, j⟩ = w * leaf i d j) :
    w * (∑ i, ∑ d, (zero i d + tail i d + ∑ j, leaf i d j)) =
      w * (∑ i, ∑ d, zero i d) + w * (∑ i, ∑ d, tail i d) +
        ∑ j, parent j := by
  simp only [Fintype.sum_sigma, hparent, Finset.sum_add_distrib,
    Finset.mul_sum, mul_add]

private theorem direct_parent_sum_le_sum
    {I : Type*} {D : I → Type*}
    [Fintype I] [instD : ∀ i, Fintype (D i)]
    (f g : ∀ i, D i → ℝ) (h : ∀ i d, f i d ≤ g i d) :
    (∑ i, ∑ d, f i d) ≤ ∑ i, ∑ d, g i d := by
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun d _ => h i d

private theorem direct_parent_scalar_bound
    (energy w zero linearCost tail firstCost secondCost
      zeroBudget tailBudget leaves : ℝ)
    (hw : 0 ≤ w)
    (hparent : energy ≤ w * (zero + linearCost + tail))
    (hfirst : zero + tail ≤ firstCost)
    (hsecond : linearCost ≤ secondCost)
    (hcost : w * secondCost = zeroBudget + tailBudget + leaves) :
    energy ≤ w * firstCost + zeroBudget + tailBudget + leaves := by
  calc
    energy ≤ w * (zero + linearCost + tail) := hparent
    _ = w * ((zero + tail) + linearCost) := by ring
    _ ≤ w * (firstCost + secondCost) :=
      mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hw
    _ = w * firstCost + zeroBudget + tailBudget + leaves := by
      rw [mul_add, hcost]
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
variable {W E : Type*}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local instance directParentLeavesCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Z : ℝ}


variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

namespace ActualDirectFirstSource

variable (s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX)

abbrev SecondStages := ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
  (s.pieces v D).SecondStages (E := E) (hDiff := hDiff)

namespace SecondStages

variable {s} (R : s.SecondStages (E := E) (hDiff := hDiff))

abbrev TerminalCalibration (sTail sZero : Finset (ℕ × ℕ))
    (k : ℕ) (Lmax Nsave decay : ℝ) :=
  ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    (R v D).TerminalCalibration sTail sZero k Z Lmax Nsave decay

abbrev CoverHybridPredicates (L : SourceCartesianAtlas s.columns s.ideal) :=
  ∀ v : s.CommonLabel, ∀ D : ((s.block v).mask s.mask).powerset,
    (R v D).CoverHybridPredicates L L

abbrev CoveredLeafKey (L : SourceCartesianAtlas s.columns s.ideal) :=
  Σ v : s.CommonLabel, Σ D : ((s.block v).mask s.mask).powerset,
    (R v D).CoveredLeafKey L L

def parentLeaf (L : SourceCartesianAtlas s.columns s.ideal)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.CoveredLeafKey L) : ActualHybridLeaf K Q W E :=
  ((R j.1 j.2.1).coveredLeaf L L (N.left j.1 j.2.1) (N.right j.1 j.2.1)
    (N.left_pos j.1 j.2.1) (N.right_pos j.1 j.2.1)
    (exceptional j.1 j.2.1) j.2.2).scale (s.fiber : ℝ) (Nat.cast_nonneg _)

variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def finiteCost (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (L : SourceCartesianAtlas s.columns s.ideal)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (ε Cerror Czero : ℝ) : ℝ :=
  ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
    (T v D).finiteCost L L (exceptional v D)
      (N.left v D) (N.right v D) (N.left_pos v D) (N.right_pos v D) ε Cerror Czero

def secondZeroBudget (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (N : s.Normalization) (ε Czero : ℝ) : ℝ :=
  (s.fiber : ℝ) * ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
    (T v D).zeroBudget (N.left v D) (N.right v D) ε Czero

def secondTailBudget (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (N : s.Normalization) (Cerror : ℝ) : ℝ :=
  (s.fiber : ℝ) * ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
    (T v D).tailBudget (N.left v D) (N.right v D) Cerror

/-- Exact finite identity on the same actual second-transform leaves;
the parent fibre is paid once and the first divisor remains explicit. -/
theorem finiteCost_eq_budgets_leaves
    (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (L : SourceCartesianAtlas s.columns s.ideal)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (ε Cerror Czero : ℝ) :
    (s.fiber : ℝ) * R.finiteCost T L exceptional N ε Cerror Czero =
      R.secondZeroBudget T N ε Czero + R.secondTailBudget T N Cerror +
      ∑ j : R.CoveredLeafKey L, (R.parentLeaf L exceptional N j).cost := by
  exact direct_parent_sigma_sum_cost
    (I := s.CommonLabel)
    (D := fun v => ((s.block v).mask s.mask).powerset)
    (J := fun v D => (R v D).CoveredLeafKey L L)
    (instD := fun v => inferInstance) (instJ := fun v D => inferInstance)
    (w := (s.fiber : ℝ))
    (zero := fun v D => (T v D).zeroBudget (N.left v D) (N.right v D) ε Czero)
    (tail := fun v D => (T v D).tailBudget (N.left v D) (N.right v D) Cerror)
    (leaf := fun v D j => ((R v D).coveredLeaf L L
      (N.left v D) (N.right v D) (N.left_pos v D) (N.right_pos v D)
      (exceptional v D) j).cost)
    (parent := fun j => (R.parentLeaf L exceptional N j).cost)
    (hparent := fun v D j => ((R v D).coveredLeaf L L
      (N.left v D) (N.right v D) (N.left_pos v D) (N.right_pos v D)
      (exceptional v D) j).scale_cost (s.fiber : ℝ) (Nat.cast_nonneg _))

end SecondStages
end ActualDirectFirstSource

variable (hΓ μv hDiff)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]
local notation "Lattice" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

include ν μ in
/-- The literal original parent reaches the same canonical hybrid
family without an artificial positive prime pool. All analytic choices
precede the moving source, first/second labels and Fourier parameters. -/
theorem actual_parent_direct_two_stage_finite_leaf_bound
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
    ∀ (Z : ℝ), ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X),
    ∀ s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX,
    ∀ N : s.Normalization,
    ∀ R : s.SecondStages (E := E) (hDiff := hDiff),
    ∀ T : R.TerminalCalibration sTail sZero k Lmax Nsave decay,
    ∀ F : s.TerminalCalibration sFirst sFirstZero k Lmax Nsave decay,
    ∀ (L : SourceCartesianAtlas s.columns s.ideal) (exceptional : R.CoverHybridPredicates L),
      X ≤ Z ^ ξmax ∧
      pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
        (s.fiber : ℝ) * F.cost ε CfirstError CfirstZero +
        R.secondZeroBudget T N ε Czero + R.secondTailBudget T N Cerror +
        ∑ j : R.CoveredLeafKey L, (R.parentLeaf L exceptional N j).cost := by
  have hsecondData :=
    actual_direct_fourier_covered_terminal_bound (W := W) (E := E) (ν := ν) (μ := μ)
      hΓ μv hDiff C Drecipe hD finiteTest hlc hcs k ε hε Lmax Nsave ξmax hξmax
  obtain ⟨decay, hdecay, hchoice, hq, sTail, sZero, Cerror, Czero,
      hCerror, hCzero, hsecond⟩ := hsecondData
  obtain ⟨order, horder⟩ := exists_nat_gt
    (max (Module.finrank ℤ Lattice : ℝ) ((Module.finrank ℚ K : ℝ) * decay))
  have hlattice : Module.finrank ℤ Lattice < order := by
    exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) horder)
  have hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ order :=
    (lt_of_le_of_lt (le_max_right _ _) horder).le
  have hparentData :=
    actual_parent_first_direct_linearized (E := W) (ν := ν) (μ := μ) hΓ μv
      C hDiff finiteTest hlc hcs decay hdecay order hlattice hdegree
  obtain ⟨sFirst, Cfirst, hCfirst, hparent⟩ := hparentData
  have hterminalData :=
    actual_direct_first_terminal_cost_bound (E := W) (C := C) (hΓ := hΓ) (μv := μv)
      finiteTest k ε hε
  obtain ⟨sFirstZero, CfirstZero, hCfirstZero, hterminal⟩ := hterminalData
  let Cnum := 2 * firstTailFieldConstant K * idealCountConstant K ^ k
  have hCnum : 0 ≤ Cnum := mul_nonneg
    (mul_nonneg (by norm_num) firstTailFieldConstant_nonneg)
    (pow_nonneg (zero_le_one.trans (one_le_idealCountConstant K)) k)
  refine ⟨decay, hdecay, hchoice, hq, sFirst, sFirstZero, sTail, sZero,
    Cfirst * Cnum, CfirstZero, Cerror, Czero, mul_nonneg hCfirst hCnum,
    hCfirstZero, hCerror, hCzero, ?_⟩
  intro Z ω ψ centered d a t Y₁ Y₂ X hX s N R T F L exceptional
  have hp := hparent Z centered d a t Y₁ Y₂ X hX s N
  have ht := hterminal sFirst Cfirst hCfirst Z
    centered d a t Y₁ Y₂ X hX s Lmax Nsave decay hdecay F hDiff
  have hf : s.linearizedCost hDiff N ≤ R.finiteCost T L exceptional N ε Cerror Czero := by
    exact direct_parent_sum_le_sum
      (I := s.CommonLabel)
      (D := fun v => ((s.block v).mask s.mask).powerset)
      (instD := fun v => inferInstance)
      (f := fun v D => (s.pieces v D).linearizedCost hDiff (N.left v D) (N.right v D))
      (g := fun v D => (T v D).finiteCost L L (exceptional v D)
        (N.left v D) (N.right v D) (N.left_pos v D) (N.right_pos v D) ε Cerror Czero)
      (h := fun v D => (T v D).linearized_le_finiteCost L L (exceptional v D)
        (N.left v D) (N.right v D) (N.left_pos v D) (N.right_pos v D)
        ε Cerror Czero
        (fun G S T LC RC ex F x => (hsecond Z G S T LC RC ex F x).2)
        (fun G S T LC RC ex F x => (hsecond Z G S T LC RC ex F x).2))
  refine ⟨?_, ?_⟩
  · exact F.cutoff_eq.trans_le
      (Real.rpow_le_rpow_of_exponent_le F.windows.base_ge_one hq)
  · exact direct_parent_scalar_bound
      (energy := pairedStageEnergy centered d a Z t Y₁ Y₂)
      (w := (s.fiber : ℝ))
      (zero := s.zeroCost hDiff)
      (linearCost := s.linearizedCost hDiff N)
      (tail := Cfirst * X ^ (1 - decay) * s.tailCost sFirst)
      (firstCost := F.cost ε (Cfirst * Cnum) CfirstZero)
      (secondCost := R.finiteCost T L exceptional N ε Cerror Czero)
      (zeroBudget := R.secondZeroBudget T N ε Czero)
      (tailBudget := R.secondTailBudget T N Cerror)
      (leaves := ∑ j : R.CoveredLeafKey L, (R.parentLeaf L exceptional N j).cost)
      (hw := Nat.cast_nonneg s.fiber)
      (hparent := hp) (hfirst := ht) (hsecond := hf)
      (hcost := R.finiteCost_eq_budgets_leaves T L exceptional N ε Cerror Czero)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.finiteCost_eq_budgets_leaves
#print axioms HeckeSkeleton.Moments.EngineStep.actual_parent_direct_two_stage_finite_leaf_bound
