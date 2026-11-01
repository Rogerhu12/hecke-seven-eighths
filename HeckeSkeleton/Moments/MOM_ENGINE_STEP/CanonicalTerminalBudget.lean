import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolTerminalMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolFiniteLeaves

/-!
# The canonical finite leaves use the proved original terminal sums

The zero and tail budgets in `PoolFiniteLeaves` are exactly the sums of
the original calibrated parts.  The following bridges therefore apply
the raw-profile estimates to the canonical source decomposition, with
the same tags, local weights, fibre multiplicities and single density.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments MeasureTheory

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {ι : Type*} {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ}
variable {Z Lmax Nsave decay : ℝ}

namespace ActualGaussStage.TerminalCalibration

variable {G : ActualGaussSource C ι}
variable {s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest}
variable (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)

@[simp] theorem zeroBudget_eq_zeroPart (ε Czero : ℝ) :
    T.zeroBudget ε Czero = T.zeroPart ε Czero := rfl

@[simp] theorem tailBudget_eq_tailPart (Cerror : ℝ) :
    T.tailBudget Cerror = T.tailPart Cerror := rfl

end ActualGaussStage.TerminalCalibration

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {d : FirstGaussPoolData C P ι} {c : ι → ℂ}
variable {s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest}

namespace ActualPoolStages.TerminalCalibration

variable (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)

theorem zeroBudget_eq_sum_parts (ε Czero : ℝ) :
    T.zeroBudget ε Czero = (4 / d.density) *
      ∑ b : PoolSourceTag P, d.tagWeight b * (T.tag b).zeroPart ε Czero := by
  simp only [zeroBudget, PoolSourceTag, Fintype.sum_sum_type, Fintype.sum_unique,
    FirstGaussPoolData.tagWeight, tag,
    ActualGaussStage.TerminalCalibration.zeroBudget_eq_zeroPart]
  ring

theorem tailBudget_eq_sum_parts (Cerror : ℝ) :
    T.tailBudget Cerror = (4 / d.density) *
      ∑ b : PoolSourceTag P, d.tagWeight b * (T.tag b).tailPart Cerror := by
  simp only [tailBudget, PoolSourceTag, Fintype.sum_sum_type, Fintype.sum_unique,
    FirstGaussPoolData.tagWeight, tag,
    ActualGaussStage.TerminalCalibration.tailBudget_eq_tailPart]
  ring

theorem zeroBudget_nonneg (ε Czero : ℝ) (hC : 0 ≤ Czero) :
    0 ≤ T.zeroBudget ε Czero := by
  rw [T.zeroBudget_eq_sum_parts]
  exact mul_nonneg (div_nonneg (by norm_num) d.density_pos.le)
    (Finset.sum_nonneg fun b _ =>
      mul_nonneg (d.tagWeight_nonneg b) ((T.tag b).zeroPart_nonneg ε Czero hC))

theorem tailBudget_nonneg (Cerror : ℝ) (hC : 0 ≤ Cerror) :
    0 ≤ T.tailBudget Cerror := by
  rw [T.tailBudget_eq_sum_parts]
  exact mul_nonneg (div_nonneg (by norm_num) d.density_pos.le)
    (Finset.sum_nonneg fun b _ =>
      mul_nonneg (d.tagWeight_nonneg b) ((T.tag b).tailPart_nonneg Cerror hC))

/-- This is the zero budget occurring in the canonical integral/leaf
identity, bounded from the original individual profile windows. -/
theorem zeroBudget_le (ε Czero profileConstant budget Mmax : ℝ)
    (profileExponent : PoolSourceTag P → ℝ) (fiberBound : ℕ)
    (hC : 0 ≤ Czero) (hprofile : 0 ≤ profileConstant)
    (hrow : d.rowExponent ≤ Mmax)
    (hlarge : 2 * (d.rowExponent / (ell / 2) +
      d.frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps))
    (hfiber : ∀ b, (s.tag b).fiber ≤ fiberBound)
    (hmult : ∀ b, (T.tag b).windows.multiplicity ≤ 15 ^ k)
    (hAmplitude : ∀ b, (T.tag b).zeroAmplitude ≤
      (profileConstant * poolTagNormCharge P b) * Z ^ profileExponent b)
    (hbudget : ∀ b, profileExponent b + (T.tag b).productExponent * ε ≤ budget) :
    T.zeroBudget ε Czero ≤ poolTerminalConstant K ell Mmax *
      ((fiberBound : ℝ) * (15 ^ k : ℕ) * Czero * profileConstant) * Z ^ (budget + eps) := by
  rw [T.zeroBudget_eq_sum_parts]
  exact T.zeroPart_sum_le ε Czero profileConstant budget Mmax profileExponent fiberBound
    hC hprofile hrow hlarge hfiber hmult hAmplitude hbudget

/-- The canonical tail budget has exactly the same original pool
normalization.  The chosen decay appears only in the raw exponent ledger. -/
theorem tailBudget_le (Cerror profileConstant budget Mmax : ℝ)
    (profileExponent : PoolSourceTag P → ℝ) (fiberBound : ℕ)
    (hC : 0 ≤ Cerror) (hprofile : 0 ≤ profileConstant)
    (hrow : d.rowExponent ≤ Mmax)
    (hlarge : 2 * (d.rowExponent / (ell / 2) +
      d.frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps))
    (hfiber : ∀ b, (s.tag b).fiber ≤ fiberBound)
    (hmult : ∀ b, (T.tag b).windows.multiplicity ≤ 15 ^ k)
    (hAmplitude : ∀ b, (T.tag b).tailAmplitude ≤
      (profileConstant * poolTagNormCharge P b) * Z ^ profileExponent b)
    (hbudget : ∀ b, profileExponent b - Nsave ≤ budget) :
    T.tailBudget Cerror ≤ poolTerminalConstant K ell Mmax *
      ((fiberBound : ℝ) * (15 ^ k : ℕ) * Cerror * profileConstant) * Z ^ (budget + eps) := by
  rw [T.tailBudget_eq_sum_parts]
  exact T.tailPart_sum_le Cerror profileConstant budget Mmax profileExponent fiberBound
    hC hprofile hrow hlarge hfiber hmult hAmplitude hbudget

end ActualPoolStages.TerminalCalibration
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.TerminalCalibration.zeroBudget_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.TerminalCalibration.tailBudget_le
