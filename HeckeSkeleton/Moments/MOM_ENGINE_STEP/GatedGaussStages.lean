import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstSecondCoveredSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualGaussFiniteLeaves

/-!
# Actual source support is imposed before either kernel estimate

An arbitrary valid profile chart need not preserve the original
coefficient support.  The engine therefore inserts the original
coefficient-zero gates into both chart coefficients.  The per-pair
profile identity is proved from genuine Fourier/orbital linearity.
Kernels, Fourier locations, physical rows, cutoffs and terminal windows
are all retained.  This gives the support implication needed for the
actual common-divisor mass carrier without a new arithmetic hypothesis.
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

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

namespace ActualGaussStage

variable {ι : Type*} {G : ActualGaussSource C ι}
variable (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)

/-- The gates are derived from the original coefficient function,
not from a post-Cauchy energy or a bound on a whole source. -/
def gated : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest :=
  { s with charts := fun DE D =>
      { s.charts DE D with
        leftCoefficient := fun i => if G.coefficient i = 0 then 0 else (s.charts DE D).leftCoefficient i
        rightCoefficient := fun j => if G.coefficient j = 0 then 0 else (s.charts DE D).rightCoefficient j
        profile := by
          intro q i hi j hj hcop
          by_cases hi0 : G.coefficient i = 0
          · rw [OrbitalGaussColumn.secondProfile_smul]
            simp only [hi0, if_pos, zero_mul, mul_zero]
          · by_cases hj0 : G.coefficient j = 0
            · rw [OrbitalGaussColumn.secondProfile_smul]
              simp only [hj0, if_pos, star_zero, mul_zero, zero_mul]
            · simpa only [if_neg hi0, if_neg hj0] using
                (s.charts DE D).profile q i hi j hj hcop } }

@[simp] theorem gated_kernel
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : s.mask.powerset) :
    (s.gated.charts DE D).kernel = (s.charts DE D).kernel := rfl

@[simp] theorem gated_sources
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val)) :
    s.gated.sources DE = s.sources DE := rfl

theorem gated_leftCoefficient_nonzero
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : s.mask.powerset) (i : ι)
    (hi : (s.gated.charts DE D).leftCoefficient i ≠ 0) : G.coefficient i ≠ 0 := by
  intro hi0
  exact hi (by simp only [gated, if_pos hi0])

theorem gated_rightCoefficient_nonzero
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : s.mask.powerset) (i : ι)
    (hi : (s.gated.charts DE D).rightCoefficient i ≠ 0) : G.coefficient i ≠ 0 := by
  intro hi0
  exact hi (by simp only [gated, if_pos hi0])

theorem gated_sourceLeftCoefficient_nonzero
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : s.mask.powerset) (i : ι)
    (hi : (s.gated.charts DE D).sourceLeftCoefficient i ≠ 0) : G.coefficient i ≠ 0 := by
  exact s.gated_leftCoefficient_nonzero DE D i (mul_ne_zero_iff.mp hi).1

theorem gated_sourceRightCoefficient_nonzero
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : s.mask.powerset) (i : ι)
    (hi : (s.gated.charts DE D).sourceRightCoefficient i ≠ 0) : G.coefficient i ≠ 0 := by
  exact s.gated_rightCoefficient_nonzero DE D i (mul_ne_zero_iff.mp hi).1

namespace TerminalCalibration

variable {s}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Z Lmax Nsave decay : ℝ}

/-- Raw zero and tail calibrations concern the original profiles and
are unchanged by the engine's support gates. -/
def gated (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay) :
    s.gated.TerminalCalibration sTail sZero k Z Lmax Nsave decay :=
  { T with }

end TerminalCalibration

variable (LC RC : SourceCartesianCover G.columns G.ideal)
variable (exceptional : s.gated.CoverHybridPredicates LC RC)

/-- A live literal left leaf coefficient now gives a nonzero
coefficient of the original whole Gauss source. -/
theorem gated_leaf_left_nonzero
    (F : SchwartzMap W ℂ) (x : ι → W)
    (j : s.gated.CoveredLeafKey LC RC) (h : Q)
    (i : AllocationColumn K (s.gated.coveredLeaf LC RC exceptional F x j).leftSlots)
    (hi : (s.gated.coveredLeaf LC RC exceptional F x j).leftCoefficient h i ≠ 0) :
    G.coefficient (j.1.leftReindex.index i) ≠ 0 := by
  apply s.gated_sourceLeftCoefficient_nonzero j.1.1 j.1.2.1 _
  exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hi).1).1

theorem gated_leaf_right_nonzero
    (F : SchwartzMap W ℂ) (x : ι → W)
    (j : s.gated.CoveredLeafKey LC RC) (h : Q)
    (i : AllocationColumn K (s.gated.coveredLeaf LC RC exceptional F x j).rightSlots)
    (hi : (s.gated.coveredLeaf LC RC exceptional F x j).rightCoefficient h i ≠ 0) :
    G.coefficient (j.1.rightReindex.index i) ≠ 0 := by
  apply s.gated_sourceRightCoefficient_nonzero j.1.1 j.1.2.1 _
  exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hi).1).1

end ActualGaussStage

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}
variable {dpool : FirstGaussPoolData C P ι} {c : ι → ℂ}

namespace ActualPoolStages

def gated (s : ActualPoolStages (E := E) hΓ μv hDiff dpool c finiteTest) :
    ActualPoolStages (E := E) hΓ μv hDiff dpool c finiteTest where
  main := s.main.gated
  one p := (s.one p).gated
  six p := (s.six p).gated
  seven p := (s.seven p).gated

namespace TerminalCalibration

variable {s : ActualPoolStages (E := E) hΓ μv hDiff dpool c finiteTest}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def gated (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay) :
    s.gated.TerminalCalibration sTail sZero k Lmax Nsave decay where
  main := T.main.gated
  one p := (T.one p).gated
  six p := (T.six p).gated
  seven p := (T.seven p).gated

end TerminalCalibration
end ActualPoolStages

namespace FirstBlockPoolData.SecondStages

variable {κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockPoolData chart P M X hX}

def gated (s : p.SecondStages (E := E) (hDiff := hDiff)) : p.SecondStages (E := E) (hDiff := hDiff) where
  left S χ := (s.left S χ).gated
  right S χ := (s.right S χ).gated

namespace TerminalCalibration

variable {s : p.SecondStages (E := E) (hDiff := hDiff)}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def gated (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay) :
    s.gated.TerminalCalibration sTail sZero k Lmax Nsave decay where
  left S χ := (T.left S χ).gated
  right S χ := (T.right S χ).gated

end TerminalCalibration
end FirstBlockPoolData.SecondStages

variable {omega psi : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K omega psi} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}

namespace ActualFirstSource.SecondStages

variable {s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}

def gated (R : s.SecondStages (E := E) (hDiff := hDiff)) :
    s.SecondStages (E := E) (hDiff := hDiff) := fun v D => (R v D).gated

namespace TerminalCalibration

variable {R : s.SecondStages (E := E) (hDiff := hDiff)}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

def gated (T : R.TerminalCalibration sTail sZero k Lmax Nsave decay) :
    R.gated.TerminalCalibration sTail sZero k Lmax Nsave decay := fun v D => (T v D).gated

end TerminalCalibration
end ActualFirstSource.SecondStages

variable (hΓ μv hDiff)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- The original parent is routed through the engine-built support
gates.  No comparison with a previously ungated kernel cost is assumed. -/
theorem actual_parent_gated_two_stage_covered_terminal_bound
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
    ∀ N : s.Normalization,
    ∀ R : s.SecondStages (E := E) (hDiff := hDiff),
    ∀ T : R.TerminalCalibration sTail sZero k Lmax Nsave decay,
    ∀ F : s.TerminalCalibration sFirst sFirstZero k Lmax Nsave decay,
    ∀ (L : SourceCartesianAtlas s.columns s.ideal) (exceptional : R.gated.CoverHybridPredicates L),
      X ≤ Z ^ ξmax ∧
      pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
        (s.fiber : ℝ) * (F.cost ε CfirstError CfirstZero +
          R.gated.coveredCost T.gated L exceptional N ε Cerror Czero) := by
  obtain ⟨decay, hdecay, hchoice, hq, sFirst, sFirstZero, sTail, sZero,
    CfirstError, CfirstZero, Cerror, Czero, hCfE, hCfZ, hCE, hCZ, hb⟩ :=
    actual_parent_two_stage_covered_terminal_bound (W := W) (E := E) (ν := ν) (μ := μ)
      hΓ μv hDiff C Drecipe hD finiteTest hlc hcs k ε hε Lmax Nsave ξmax hξmax
  refine ⟨decay, hdecay, hchoice, hq, sFirst, sFirstZero, sTail, sZero,
    CfirstError, CfirstZero, Cerror, Czero, hCfE, hCfZ, hCE, hCZ, ?_⟩
  intro Z ell eps bad P omega psi centered d a t Y₁ Y₂ X hX s N R T F L exceptional
  exact hb Z ell eps bad P centered d a t Y₁ Y₂ X hX s N R.gated T.gated F L exceptional

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.gated
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.gated_leaf_left_nonzero
#print axioms HeckeSkeleton.Moments.EngineStep.actual_parent_gated_two_stage_covered_terminal_bound

