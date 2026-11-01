import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualPoolFiniteLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DualTerminalPower
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDivisorPoolTerminal

/-!
# Original coefficient atoms pay the pure-dual pool terminals

The new calibration uses the same original first-divisor atoms on
each physical main or valuation-one, -six, or -seven tag. The original
support-extraction factor `τ(D²)^k` is retained alongside the amplifier
tuple factors. Its constant is selected from the fixed original norm
window, before the source, scale, and prime pool.

The bounds below prove the actual zero and tail budget sums. Their
inputs are original atom constants, row fibres, mask cardinalities,
and numerical profile windows. No terminal sum or descendant bound
is supplied, and the literal `1 / Norm S` is preserved throughout.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.LargeSieve
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.CenteredMomentCounting MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}

/-- A fixed arithmetic constant, chosen before all moving ideals and
scales. The original factor `15^k` remains explicit in its bound. -/
def dualPoolTupleConstant (k : ℕ) (Bnorm δ : ℝ)
    (hBnorm : 0 ≤ Bnorm) (hδ : 0 < δ) : ℝ :=
  Classical.choose (first_terminal_tuple_multiplicity_subpower (K := K) k Bnorm δ hBnorm hδ)

theorem dualPoolTupleConstant_pos (k : ℕ) (Bnorm δ : ℝ)
    (hBnorm : 0 ≤ Bnorm) (hδ : 0 < δ) :
    0 < dualPoolTupleConstant (K := K) k Bnorm δ hBnorm hδ :=
  (Classical.choose_spec
    (first_terminal_tuple_multiplicity_subpower (K := K) k Bnorm δ hBnorm hδ)).1

theorem dualPoolTupleConstant_bound (k : ℕ) (Bnorm δ : ℝ)
    (hBnorm : 0 ≤ Bnorm) (hδ : 0 < δ) (Z : ℝ) (hZ : 1 ≤ Z)
    (D : Ideal (𝓞 K)) (hD : (Ideal.absNorm D : ℝ) ≤ Z ^ Bnorm) :
    (idealDivisorCount (D ^ 2) ^ k * 15 ^ k : ℕ) ≤
      (dualPoolTupleConstant (K := K) k Bnorm δ hBnorm hδ * (15 ^ k : ℕ)) * Z ^ δ :=
  (Classical.choose_spec
    (first_terminal_tuple_multiplicity_subpower (K := K) k Bnorm δ hBnorm hδ)).2 Z hZ D hD

private theorem dual_terminal_tuple_power_le (k : ℕ) (Bnorm δ : ℝ)
    (hBnorm : 0 ≤ Bnorm) (hδ : 0 < δ) (Z : ℝ) (hZ : 1 ≤ Z)
    (D : Ideal (𝓞 K)) (hD : (Ideal.absNorm D : ℝ) ≤ Z ^ Bnorm)
    (coefficient exponent : ℝ) (hcoefficient : 0 ≤ coefficient) :
    coefficient * (idealDivisorCount (D ^ 2) ^ k * 15 ^ k : ℕ) * Z ^ exponent ≤
      coefficient *
        (dualPoolTupleConstant (K := K) k Bnorm δ hBnorm hδ * (15 ^ k : ℕ)) *
          Z ^ (exponent + δ) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  calc
    _ ≤ coefficient *
        ((dualPoolTupleConstant (K := K) k Bnorm δ hBnorm hδ * (15 ^ k : ℕ)) *
          Z ^ δ) * Z ^ exponent :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (dualPoolTupleConstant_bound k Bnorm δ hBnorm hδ Z hZ D hD) hcoefficient)
        (Real.rpow_nonneg hz.le _)
    _ = _ := by rw [Real.rpow_add hz]; ring

private theorem dual_terminal_pool_sum
    (d : FirstGaussPoolData C P ι) (f : PoolSourceTag P → ℝ)
    (H budget Mmax : ℝ) (hH : 0 ≤ H) (hrow : d.rowExponent ≤ Mmax)
    (hlarge : 2 * (d.rowExponent / (ell / 2) +
      d.frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps))
    (hterm : ∀ b, f b ≤ H * poolTagNormCharge P b * Z ^ budget) :
    (4 / d.density) * (∑ b, d.tagWeight b * f b) ≤
      poolTerminalConstant K ell Mmax * H * Z ^ (budget + eps) := by
  have hz : 0 < Z := zero_lt_one.trans P.base_gt_one
  calc
    _ ≤ (4 / d.density) *
        ∑ b, d.tagWeight b * (H * poolTagNormCharge P b * Z ^ budget) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun b _ =>
          mul_le_mul_of_nonneg_left (hterm b) (d.tagWeight_nonneg b))
        (div_nonneg (by norm_num) d.density_pos.le)
    _ = (4 / d.density) * ∑ b,
        (d.tagWeight b * poolTagNormCharge P b) * (H * Z ^ budget) := by
      congr 1
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = ((4 / d.density) * ∑ b, d.tagWeight b * poolTagNormCharge P b) *
        (H * Z ^ budget) := by rw [← Finset.sum_mul]; ring
    _ ≤ (poolTerminalConstant K ell Mmax * Z ^ eps) * (H * Z ^ budget) :=
      mul_le_mul_of_nonneg_right (d.tag_norm_charge_mass_le Mmax hrow hlarge)
        (mul_nonneg hH (Real.rpow_nonneg hz.le _))
    _ = _ := by rw [Real.rpow_add hz]; ring

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

namespace ActualPoolStages

variable {d : FirstGaussPoolData C P ι} {c : ι → ℂ}
variable {s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

namespace DualTerminalCalibration

theorem zeroBudget_nonneg
    (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (ε Czero : ℝ) (hC : 0 ≤ Czero) : 0 ≤ T.zeroBudget ε Czero := by
  unfold zeroBudget
  exact mul_nonneg (div_nonneg (by norm_num) d.density_pos.le)
    (Finset.sum_nonneg fun b _ =>
      mul_nonneg (d.tagWeight_nonneg b) ((T.tag b).zeroBudget_nonneg ε Czero hC))

theorem tailBudget_nonneg
    (T : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay)
    (Cerror : ℝ) (hC : 0 ≤ Cerror) : 0 ≤ T.tailBudget Cerror := by
  unfold tailBudget
  exact mul_nonneg (div_nonneg (by norm_num) d.density_pos.le)
    (Finset.sum_nonneg fun b _ =>
      mul_nonneg (d.tagWeight_nonneg b) ((T.tag b).tailBudget_nonneg Cerror hC))

end DualTerminalCalibration

/-- Original per-tag atoms and their pure-dual residual calibration.
The source at each tag is the unchanged main or amplified source. -/
structure DualFirstDivisorWindows
    (s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest)
    (S : Ideal (𝓞 K)) (slots : ℕ) (B : ℝ)
    (sTail sZero : Finset (ℕ × ℕ)) (k : ℕ) (Lmax Nsave decay : ℝ) where
  atoms : ∀ b : PoolSourceTag P,
    FirstDivisorCoefficientAtoms (A := A) (σ := σ)
      (d.tagSource c b).columns (d.tagSource c b).coefficient S slots B
  profile : ∀ b : PoolSourceTag P,
    (s.tag b).DualResidualTerminalWindows (atoms b) sTail sZero k Z Lmax Nsave decay

namespace DualFirstDivisorWindows

variable {S : Ideal (𝓞 K)} {slots : ℕ} {B : ℝ}
variable (T : s.DualFirstDivisorWindows S slots B sTail sZero k Lmax Nsave decay)

def calibration : s.DualTerminalCalibration sTail sZero k Lmax Nsave decay :=
  DualTerminalCalibration.ofTag (fun b => (T.profile b).calibration)

@[simp] theorem calibration_tag (b : PoolSourceTag P) :
    T.calibration.tag b = (T.profile b).calibration := by
  exact DualTerminalCalibration.ofTag_tag _ b

/-- The exact support-tuple and residual-tuple multiplicities. These
are the values returned by the original support extraction constructors. -/
structure OriginalTupleMultiplicities (D : Ideal (𝓞 K)) : Prop where
  main : (T.profile (.inl ())).windows.multiplicity = idealDivisorCount (D ^ 2) ^ k
  one : ∀ p : P.primes, (T.profile (.inr (.inl p))).windows.multiplicity =
    idealDivisorCount (D ^ 2) ^ k * 3 ^ k
  six : ∀ p : P.primes, (T.profile (.inr (.inr (.inl p)))).windows.multiplicity =
    idealDivisorCount (D ^ 2) ^ k * 13 ^ k
  seven : ∀ p : P.primes, (T.profile (.inr (.inr (.inr p)))).windows.multiplicity =
    idealDivisorCount (D ^ 2) ^ k * 15 ^ k

theorem OriginalTupleMultiplicities.tag_le {D : Ideal (𝓞 K)}
    (Q : T.OriginalTupleMultiplicities D) (b : PoolSourceTag P) :
    (T.profile b).windows.multiplicity ≤ idealDivisorCount (D ^ 2) ^ k * 15 ^ k := by
  rcases b with ⟨⟩ | p | p | p
  · rw [Q.main]
    exact Nat.le_mul_of_pos_right _ (pow_pos (by decide : 0 < (15 : ℕ)) k)
  · rw [Q.one p]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) k)
  · rw [Q.six p]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) k)
  · rw [Q.seven p]

def zeroExponent (b : PoolSourceTag P) : ℝ := (T.profile b).zeroExponent

theorem zeroAmplitude_le_original
    (b : PoolSourceTag P) (profileConstant : ℝ) (hprofile : 0 ≤ profileConstant)
    (maskCap : ℕ) (hmask : (s.tag b).mask.card ≤ maskCap)
    (hraw : (T.profile b).zeroProfileConstant ≤ profileConstant * poolTagNormCharge P b) :
    (T.calibration.tag b).zeroAmplitude ≤
      ((B ^ slots * profileConstant * (2 : ℝ) ^ maskCap / (Ideal.absNorm S : ℝ)) *
        poolTagNormCharge P b) * Z ^ T.zeroExponent b := by
  rw [T.calibration_tag, (T.profile b).calibration_zeroAmplitude_power]
  have hB : 0 ≤ B ^ slots := pow_nonneg
    (zero_le_one.trans (T.atoms b).bound_ge_one) _
  have hpow : (2 : ℝ) ^ (s.tag b).mask.card ≤ (2 : ℝ) ^ maskCap :=
    pow_le_pow_right₀ (by norm_num) hmask
  have hnum := mul_le_mul
    (mul_le_mul_of_nonneg_left hraw hB) hpow (pow_nonneg (by norm_num) _)
      (mul_nonneg hB (mul_nonneg hprofile (poolTagNormCharge_nonneg b)))
  have hs := div_le_div_of_nonneg_right hnum (Nat.cast_nonneg (Ideal.absNorm S))
  apply mul_le_mul_of_nonneg_right _
    (Real.rpow_nonneg (zero_le_one.trans P.base_gt_one.le) _)
  convert hs using 1 <;> ring

/-- The actual pure-dual zero budget is proved from the individual
original coefficient profiles, with both tuple multiplicities intact. -/
theorem zeroBudget_le_original_profiles
    (D : Ideal (𝓞 K)) (Q : T.OriginalTupleMultiplicities D)
    (ε Czero profileConstant budget Mmax : ℝ) (fiberCap maskCap : ℕ)
    (hC : 0 ≤ Czero) (hprofile : 0 ≤ profileConstant)
    (hrow : d.rowExponent ≤ Mmax)
    (hlarge : 2 * (d.rowExponent / (ell / 2) +
      d.frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps))
    (hfiber : ∀ b, (s.tag b).fiber ≤ fiberCap)
    (hmask : ∀ b, (s.tag b).mask.card ≤ maskCap)
    (hraw : ∀ b, (T.profile b).zeroProfileConstant ≤ profileConstant * poolTagNormCharge P b)
    (hbudget : ∀ b, T.zeroExponent b + (T.profile b).productExponent * ε ≤ budget) :
    T.calibration.zeroBudget ε Czero ≤
      poolTerminalConstant K ell Mmax *
        ((fiberCap : ℝ) * (idealDivisorCount (D ^ 2) ^ k * 15 ^ k : ℕ) * Czero *
          (B ^ slots * profileConstant * (2 : ℝ) ^ maskCap / (Ideal.absNorm S : ℝ))) *
        Z ^ (budget + eps) := by
  have hB : 0 ≤ B ^ slots := pow_nonneg
    (zero_le_one.trans (T.atoms (.inl ())).bound_ge_one) _
  have hcost : 0 ≤ B ^ slots * profileConstant * (2 : ℝ) ^ maskCap /
      (Ideal.absNorm S : ℝ) := by positivity
  unfold ActualPoolStages.DualTerminalCalibration.zeroBudget
  apply dual_terminal_pool_sum d _ _ budget Mmax (by positivity) hrow hlarge
  intro b
  have hpart := (T.calibration.tag b).zeroBudget_le_power ε Czero
    ((B ^ slots * profileConstant * (2 : ℝ) ^ maskCap / (Ideal.absNorm S : ℝ)) *
      poolTagNormCharge P b) (T.zeroExponent b) budget hC
    (mul_nonneg hcost (poolTagNormCharge_nonneg b))
    (T.zeroAmplitude_le_original b profileConstant hprofile maskCap (hmask b) (hraw b))
    (by simpa only [T.calibration_tag] using hbudget b)
  have hcounts : ((s.tag b).fiber : ℝ) * (T.calibration.tag b).windows.multiplicity ≤
      (fiberCap : ℝ) * (idealDivisorCount (D ^ 2) ^ k * 15 ^ k : ℕ) := by
    rw [T.calibration_tag]
    exact mul_le_mul (by exact_mod_cast hfiber b) (by exact_mod_cast Q.tag_le b)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  apply hpart.trans
  convert mul_le_mul_of_nonneg_right hcounts
    (mul_nonneg
      (mul_nonneg hC (mul_nonneg hcost (poolTagNormCharge_nonneg b)))
      (Real.rpow_nonneg (zero_le_one.trans P.base_gt_one.le) budget)) using 1 <;> ring

/-- The original first-divisor denominator and the same tuple fibres
also pay the actual tail sum; only the raw profile decay ledger differs. -/
theorem tailBudget_le_original_profiles
    (D : Ideal (𝓞 K)) (Q : T.OriginalTupleMultiplicities D)
    (Cerror profileConstant budget Mmax : ℝ) (fiberCap : ℕ)
    (profileExponent : PoolSourceTag P → ℝ)
    (hC : 0 ≤ Cerror) (hprofile : 0 ≤ profileConstant)
    (hrow : d.rowExponent ≤ Mmax)
    (hlarge : 2 * (d.rowExponent / (ell / 2) +
      d.frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps))
    (hfiber : ∀ b, (s.tag b).fiber ≤ fiberCap)
    (hraw : ∀ b, (T.profile b).tailProfileConstant ≤
      profileConstant * poolTagNormCharge P b * Z ^ profileExponent b)
    (hbudget : ∀ b, profileExponent b - Nsave ≤ budget) :
    T.calibration.tailBudget Cerror ≤
      poolTerminalConstant K ell Mmax *
        ((fiberCap : ℝ) * (idealDivisorCount (D ^ 2) ^ k * 15 ^ k : ℕ) * Cerror *
          (B ^ slots * profileConstant / (Ideal.absNorm S : ℝ))) * Z ^ (budget + eps) := by
  have hB : 0 ≤ B ^ slots := pow_nonneg
    (zero_le_one.trans (T.atoms (.inl ())).bound_ge_one) _
  have hcost : 0 ≤ B ^ slots * profileConstant / (Ideal.absNorm S : ℝ) := by positivity
  unfold ActualPoolStages.DualTerminalCalibration.tailBudget
  apply dual_terminal_pool_sum d _ _ budget Mmax (by positivity) hrow hlarge
  intro b
  have hAmplitude : (T.calibration.tag b).tailAmplitude ≤
      ((B ^ slots * profileConstant / (Ideal.absNorm S : ℝ)) * poolTagNormCharge P b) *
        Z ^ profileExponent b := by
    rw [T.calibration_tag, (T.profile b).calibration_tailAmplitude]
    convert mul_le_mul_of_nonneg_left (hraw b) (T.atoms b).scalarCost_nonneg using 1 <;>
      dsimp only [FirstDivisorCoefficientAtoms.scalarCost] <;> ring
  have hpart := (T.calibration.tag b).tailBudget_le_power Cerror
    ((B ^ slots * profileConstant / (Ideal.absNorm S : ℝ)) * poolTagNormCharge P b)
    (profileExponent b) budget hC (mul_nonneg hcost (poolTagNormCharge_nonneg b))
    hAmplitude (hbudget b)
  have hcounts : ((s.tag b).fiber : ℝ) * (T.calibration.tag b).windows.multiplicity ≤
      (fiberCap : ℝ) * (idealDivisorCount (D ^ 2) ^ k * 15 ^ k : ℕ) := by
    rw [T.calibration_tag]
    exact mul_le_mul (by exact_mod_cast hfiber b) (by exact_mod_cast Q.tag_le b)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  apply hpart.trans
  convert mul_le_mul_of_nonneg_right hcounts
    (mul_nonneg
      (mul_nonneg hC (mul_nonneg hcost (poolTagNormCharge_nonneg b)))
      (Real.rpow_nonneg (zero_le_one.trans P.base_gt_one.le) budget)) using 1 <;> ring

/-- The original common-ideal norm window pays the retained tuple
count. The arithmetic constant is independent of the source and scale. -/
theorem zeroBudget_le_original_norm_window
    (Bnorm δ : ℝ) (hBnorm : 0 ≤ Bnorm) (hδ : 0 < δ)
    (D : Ideal (𝓞 K)) (hD : (Ideal.absNorm D : ℝ) ≤ Z ^ Bnorm)
    (Q : T.OriginalTupleMultiplicities D)
    (ε Czero profileConstant budget Mmax : ℝ) (fiberCap maskCap : ℕ)
    (hC : 0 ≤ Czero) (hprofile : 0 ≤ profileConstant)
    (hrow : d.rowExponent ≤ Mmax)
    (hlarge : 2 * (d.rowExponent / (ell / 2) +
      d.frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps))
    (hfiber : ∀ b, (s.tag b).fiber ≤ fiberCap)
    (hmask : ∀ b, (s.tag b).mask.card ≤ maskCap)
    (hraw : ∀ b, (T.profile b).zeroProfileConstant ≤ profileConstant * poolTagNormCharge P b)
    (hbudget : ∀ b, T.zeroExponent b + (T.profile b).productExponent * ε ≤ budget) :
    T.calibration.zeroBudget ε Czero ≤
      poolTerminalConstant K ell Mmax *
        ((fiberCap : ℝ) *
          (dualPoolTupleConstant (K := K) k Bnorm δ hBnorm hδ * (15 ^ k : ℕ)) * Czero *
          (B ^ slots * profileConstant * (2 : ℝ) ^ maskCap / (Ideal.absNorm S : ℝ))) *
        Z ^ (budget + eps + δ) := by
  have hpool : 0 ≤ poolTerminalConstant K ell Mmax :=
    (poolTerminalConstant_pos (K := K) ell Mmax P.exponent_pos
      (d.rowExponent_nonneg.trans hrow)).le
  have hB : 0 ≤ B ^ slots := pow_nonneg
    (zero_le_one.trans (T.atoms (.inl ())).bound_ge_one) _
  let coefficient : ℝ := poolTerminalConstant K ell Mmax *
    ((fiberCap : ℝ) * Czero *
      (B ^ slots * profileConstant * (2 : ℝ) ^ maskCap / (Ideal.absNorm S : ℝ)))
  have hcoefficient : 0 ≤ coefficient := by dsimp [coefficient]; positivity
  have htuple := dual_terminal_tuple_power_le k Bnorm δ hBnorm hδ Z P.base_gt_one.le
    D hD coefficient (budget + eps) hcoefficient
  apply (T.zeroBudget_le_original_profiles D Q ε Czero profileConstant budget Mmax
    fiberCap maskCap hC hprofile hrow hlarge hfiber hmask hraw hbudget).trans
  convert htuple using 1 <;> dsimp only [coefficient] <;> ring

/-- The tail has the same fixed arithmetic tuple cost and the same
literal first-divisor denominator. -/
theorem tailBudget_le_original_norm_window
    (Bnorm δ : ℝ) (hBnorm : 0 ≤ Bnorm) (hδ : 0 < δ)
    (D : Ideal (𝓞 K)) (hD : (Ideal.absNorm D : ℝ) ≤ Z ^ Bnorm)
    (Q : T.OriginalTupleMultiplicities D)
    (Cerror profileConstant budget Mmax : ℝ) (fiberCap : ℕ)
    (profileExponent : PoolSourceTag P → ℝ)
    (hC : 0 ≤ Cerror) (hprofile : 0 ≤ profileConstant)
    (hrow : d.rowExponent ≤ Mmax)
    (hlarge : 2 * (d.rowExponent / (ell / 2) +
      d.frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps))
    (hfiber : ∀ b, (s.tag b).fiber ≤ fiberCap)
    (hraw : ∀ b, (T.profile b).tailProfileConstant ≤
      profileConstant * poolTagNormCharge P b * Z ^ profileExponent b)
    (hbudget : ∀ b, profileExponent b - Nsave ≤ budget) :
    T.calibration.tailBudget Cerror ≤
      poolTerminalConstant K ell Mmax *
        ((fiberCap : ℝ) *
          (dualPoolTupleConstant (K := K) k Bnorm δ hBnorm hδ * (15 ^ k : ℕ)) * Cerror *
          (B ^ slots * profileConstant / (Ideal.absNorm S : ℝ))) *
        Z ^ (budget + eps + δ) := by
  have hpool : 0 ≤ poolTerminalConstant K ell Mmax :=
    (poolTerminalConstant_pos (K := K) ell Mmax P.exponent_pos
      (d.rowExponent_nonneg.trans hrow)).le
  have hB : 0 ≤ B ^ slots := pow_nonneg
    (zero_le_one.trans (T.atoms (.inl ())).bound_ge_one) _
  let coefficient : ℝ := poolTerminalConstant K ell Mmax *
    ((fiberCap : ℝ) * Cerror * (B ^ slots * profileConstant / (Ideal.absNorm S : ℝ)))
  have hcoefficient : 0 ≤ coefficient := by dsimp [coefficient]; positivity
  have htuple := dual_terminal_tuple_power_le k Bnorm δ hBnorm hδ Z P.base_gt_one.le
    D hD coefficient (budget + eps) hcoefficient
  apply (T.tailBudget_le_original_profiles D Q Cerror profileConstant budget Mmax
    fiberCap profileExponent hC hprofile hrow hlarge hfiber hraw hbudget).trans
  convert htuple using 1 <;> dsimp only [coefficient] <;> ring

end DualFirstDivisorWindows
end ActualPoolStages

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.dualPoolTupleConstant_bound
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.DualFirstDivisorWindows.zeroBudget_le_original_profiles
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.DualFirstDivisorWindows.tailBudget_le_original_profiles
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.DualFirstDivisorWindows.zeroBudget_le_original_norm_window
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.DualFirstDivisorWindows.tailBudget_le_original_norm_window
