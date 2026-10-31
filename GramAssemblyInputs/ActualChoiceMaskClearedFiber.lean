import ActualChoiceMaskCompactOpenExtension
import ActualClearedSIntegerPairReindex
import ActualFixedSBoxDenominator

/-!
UNCOMPILED / native 0. Freeze the original generator-choice mask on genuine
cleared residue fibers. Both the divisor and the column are cleared by
D^H. A residue depth 2H+J leaves the actual ORIGINAL product difference
D^J*a*t after those two clearing factors have been canceled. Here J is
fixed from the actual local sixth-power depths, before all moving data.
The divisorColumn is multiplication by d; no unit replacement is made.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualGeneratorChoiceDraft

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Arithmetic.AllowedGeneratorConstruction
open HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft
open ActualGramJointChartDraft ActualGramJointChartCoverDraft
open ActualClearedPairReindexDraft ActualGramFixedDenominatorDraft
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

section Clearing

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "OS" => Set.integer S K
local notation "NZ" => NonzeroRingElements OS
local notation "D" => finiteSIntegerDenominator K S

/-- Explicit cancellation of BOTH D^H factors. The remaining increment
is ordinary and has a genuine D^J factor. -/
theorem divisorColumn_sub_eq_of_deep_cleared_congruence
    (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (H J : ℕ)
    (d m m₀ : NZ) (a z z₀ : 𝓞 K)
    (hd : algebraMap (𝓞 K) OS (D ^ H) * d.val = algebraMap (𝓞 K) OS a)
    (hm : algebraMap (𝓞 K) OS (D ^ H) * m.val = algebraMap (𝓞 K) OS z)
    (h₀ : algebraMap (𝓞 K) OS (D ^ H) * m₀.val = algebraMap (𝓞 K) OS z₀)
    (hz : z - z₀ ∈ clearedSModulus K S ζ hζ (H + H + J)) :
    ∃ t : 𝓞 K, t ∈ sIntegerSexticSPlaceModulus K S ζ hζ ∧
      (divisorColumn K S d m).val - (divisorColumn K S d m₀).val =
        algebraMap (𝓞 K) OS (D ^ J * (a * t)) := by
  obtain ⟨t, ht, he⟩ := Ideal.mem_span_singleton_mul.mp hz
  refine ⟨t, ht, ?_⟩
  have hD : algebraMap (𝓞 K) OS (D ^ (H + H)) ≠ 0 := by
    rw [← commonDenominatorUnit_val K S (H + H)]
    exact Units.ne_zero _
  have clear (m : NZ) (z : 𝓞 K)
      (hm : algebraMap (𝓞 K) OS (D ^ H) * m.val = algebraMap (𝓞 K) OS z) :
      algebraMap (𝓞 K) OS (D ^ (H + H)) * (divisorColumn K S d m).val =
        algebraMap (𝓞 K) OS (a * z) := by
    change algebraMap (𝓞 K) OS (D ^ (H + H)) * (d.val * m.val) = _
    calc
      _ = (algebraMap (𝓞 K) OS (D ^ H) * d.val) *
          (algebraMap (𝓞 K) OS (D ^ H) * m.val) := by
        rw [pow_add, map_mul]
        ring
      _ = _ := by rw [hd, hm, map_mul]
  apply mul_left_cancel₀ hD
  calc
    _ = algebraMap (𝓞 K) OS (a * z) - algebraMap (𝓞 K) OS (a * z₀) := by
      rw [mul_sub, clear m z hm, clear m₀ z₀ h₀]
    _ = algebraMap (𝓞 K) OS (a * (D ^ (H + H + J) * t)) := by
      rw [← map_sub, ← mul_sub, ← he]
    _ = _ := by
      simp only [pow_add, map_mul]
      ring

end Clearing

variable (w : GeneratorMaskWitness K)

local notation "S" => (w.S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer S K
local notation "NZ" => NonzeroRingElements OS
local notation "D" => finiteSIntegerDenominator K S

/-- Fixed before H and all moving arithmetic or analytic parameters. -/
def choiceJointPrincipalDepth : ℕ := ∑ v : w.S, choiceMaskLocalDepth K v.val

theorem choiceMaskLocalDepth_le_joint (v : w.S) :
    choiceMaskLocalDepth K v.val ≤ choiceJointPrincipalDepth K w :=
  Finset.single_le_sum (f := fun v : w.S => choiceMaskLocalDepth K v.val)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)

/-- In the M+L fiber notation, M=H and L=H+J. -/
def choiceClearedExtraDepth (H : ℕ) : ℕ := H + choiceJointPrincipalDepth K w

theorem le_choiceClearedExtraDepth (H : ℕ) : H ≤ choiceClearedExtraDepth K w H :=
  Nat.le_add_right _ _

/-- Actual D^J times ANY ordinary integer is small at each local sixth-power
depth. The class-number factor in valuation(D) only strengthens the bound. -/
theorem valuation_choiceJointPrincipalDepth_mul_le (b : 𝓞 K) (v : w.S) :
    (Valued.v (algebraMap (𝓞 K) (v.val.adicCompletion K)
      (D ^ choiceJointPrincipalDepth K w * b)) : WithZero (Multiplicative ℤ)) ≤
        WithZero.exp (-(choiceMaskLocalDepth K v.val : ℤ)) := by
  rw [HeckeGeneral.Arithmetic.AllowedGeneratorConstruction.valued_algebraMap_integer]
  have hclass : (1 : ℤ) ≤ (classNumber K : ℤ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (classNumber_pos K).ne')
  have hJ : (choiceMaskLocalDepth K v.val : ℤ) ≤ (choiceJointPrincipalDepth K w : ℤ) := by
    exact_mod_cast choiceMaskLocalDepth_le_joint K w v
  have hpow : v.val.valuation K (algebraMap (𝓞 K) K (D ^ choiceJointPrincipalDepth K w)) =
      WithZero.exp (-((choiceJointPrincipalDepth K w : ℤ) * (classNumber K : ℤ))) := by
    rw [map_pow, map_pow, valuation_exactSDenominator K S v, ← WithZero.exp_nsmul]
    simp only [nsmul_eq_mul, mul_neg]
  rw [map_mul, map_mul]
  calc
    _ ≤ WithZero.exp (-((choiceJointPrincipalDepth K w : ℤ) * (classNumber K : ℤ))) * 1 :=
      mul_le_mul' hpow.le (v.val.valuation_le_one b)
    _ = WithZero.exp (-((choiceJointPrincipalDepth K w : ℤ) * (classNumber K : ℤ))) :=
      mul_one _
    _ ≤ WithZero.exp (-(choiceMaskLocalDepth K v.val : ℤ)) := by
      apply WithZero.exp_le_exp.mpr
      have hJ0 : (0 : ℤ) ≤ (choiceJointPrincipalDepth K w : ℤ) := Int.natCast_nonneg _
      have hCJ : (choiceJointPrincipalDepth K w : ℤ) ≤
          (choiceJointPrincipalDepth K w : ℤ) * (classNumber K : ℤ) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hclass hJ0
      exact neg_le_neg (hJ.trans hCJ)

/-- The SAME actual choice mask is constant on the genuine sufficiently deep
fiber. Only the base product column needs to be active; no replacement of d,
generator, complement, original subgroup, or mask definition occurs. -/
theorem choiceFiniteMask_divisorColumn_eq_on_clearedFiber
    (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (H : ℕ) (d m₀ m : NZ) (a z₀ : 𝓞 K)
    (hd : algebraMap (𝓞 K) OS (D ^ H) * d.val = algebraMap (𝓞 K) OS a)
    (h₀ : algebraMap (𝓞 K) OS (D ^ H) * m₀.val = algebraMap (𝓞 K) OS z₀)
    (hbase : (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₀)).2 ∈
      finiteLocalValuationBox K S H)
    (hfiber : clearedColumnFiber K S ζ hζ H (H + choiceClearedExtraDepth K w H) z₀ m) :
    choiceFiniteMask K w (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m)).2 =
      choiceFiniteMask K w (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₀)).2 := by
  obtain ⟨z, hm, hz⟩ := hfiber
  have hz' : z - z₀ ∈ clearedSModulus K S ζ hζ (H + H + choiceJointPrincipalDepth K w) := by
    simpa only [choiceClearedExtraDepth, Nat.add_assoc] using hz
  obtain ⟨t, _, hdiff⟩ := divisorColumn_sub_eq_of_deep_cleared_congruence
    K S ζ hζ H (choiceJointPrincipalDepth K w) d m m₀ a z z₀ hd hm h₀ hz'
  apply choiceFiniteMask_eq_of_small_sub K w H _ _ hbase
  intro v
  have hfield := congrArg (fun x : OS => (x : K)) hdiff
  change (Valued.v
    (algebraMap K (v.val.adicCompletion K) ((divisorColumn K S d m).val : K) -
      algebraMap K (v.val.adicCompletion K) ((divisorColumn K S d m₀).val : K)) :
        WithZero (Multiplicative ℤ)) ≤ _
  have h2 : ((divisorColumn K S d m).val : K) - ((divisorColumn K S d m₀).val : K) =
      algebraMap (𝓞 K) K (D ^ choiceJointPrincipalDepth K w * (a * t)) := by
    simpa using hfield
  rw [← map_sub, h2, ← IsScalarTower.algebraMap_apply (𝓞 K) K (v.val.adicCompletion K)]
  exact valuation_choiceJointPrincipalDepth_mul_le K w (a * t) v

end HeckeGeneral.ThetaSkeleton.Physical.ActualGeneratorChoiceDraft
