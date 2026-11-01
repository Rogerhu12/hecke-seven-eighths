import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDivisorTerminalCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalTerminalBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalMaskCardinality

/-!
# Actual pooled terminal sums from the first-divisor profile atoms

The four genuine source tags are calibrated from their original
coefficient atoms and residual profile windows.  The canonical finite
zero and tail budgets are then estimated internally.  Their one pool
density, their first-divisor denominator, and their support-extraction
tuple multiplicity are all retained.

In particular the factor `τ(D²)^k` belonging to first common extraction
is not discarded when the three amplifier valuations contribute
`3^k`, `13^k` and `15^k`.  Its small-power bound follows from the original
norm window on `D`.
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

private theorem actual_terminal_pool_sum
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
variable (s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest)

/-- Only original per-tag coefficient atoms and residual-profile
windows occur here.  Each window concerns the literal source at that
tag, including its original amplifier quotient and its original gate. -/
structure FirstDivisorWindows (S : Ideal (𝓞 K)) (slots : ℕ) (B : ℝ)
    (sTail sZero : Finset (ℕ × ℕ)) (k : ℕ) (Lmax Nsave decay : ℝ) where
  atoms : ∀ b : PoolSourceTag P,
    FirstDivisorCoefficientAtoms (A := A) (σ := σ)
      (d.tagSource c b).columns (d.tagSource c b).coefficient S slots B
  profile : ∀ b : PoolSourceTag P,
    (s.tag b).ResidualTerminalWindows (atoms b) sTail sZero k Z Lmax Nsave decay

namespace FirstDivisorWindows

variable {s} {S : Ideal (𝓞 K)} {slots : ℕ} {B : ℝ}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}
variable (T : s.FirstDivisorWindows S slots B sTail sZero k Lmax Nsave decay)

def calibration : s.TerminalCalibration sTail sZero k Lmax Nsave decay where
  main := (T.profile (.inl ())).calibration
  one p := (T.profile (.inr (.inl p))).calibration
  six p := (T.profile (.inr (.inr (.inl p)))).calibration
  seven p := (T.profile (.inr (.inr (.inr p)))).calibration

@[simp] theorem calibration_tag (b : PoolSourceTag P) :
    T.calibration.tag b = (T.profile b).calibration := by
  rcases b with ⟨⟩ | p | p | p <;> rfl

/-- These are the exact multiplicities produced by
`SecondTailWindows.ofSupportResidual` and `ofSupportAmplifier`.
The common ideal is the one extracted from the original occurrences. -/
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

def zeroExponent (b : PoolSourceTag P) : ℝ :=
  (T.profile b).zeroProfileExponent + (T.profile b).zeroColumnExponent +
    (T.profile b).inverseRadiusExponent + (T.profile b).productExponent / 2

private theorem zeroAmplitude_le_raw
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

/-- The full canonical zero budget, derived from original per-profile
windows, with the true common-extraction and amplifier tuple fibres. -/
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
  rw [T.calibration.zeroBudget_eq_sum_parts]
  apply actual_terminal_pool_sum d _ _ budget Mmax (by positivity) hrow hlarge
  intro b
  have hpart := (T.calibration.tag b).zeroPart_le_power ε Czero
    ((B ^ slots * profileConstant * (2 : ℝ) ^ maskCap / (Ideal.absNorm S : ℝ)) *
      poolTagNormCharge P b) (T.zeroExponent b) budget hC
    (mul_nonneg hcost (poolTagNormCharge_nonneg b))
    (T.zeroAmplitude_le_raw b profileConstant hprofile maskCap (hmask b) (hraw b))
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

/-- The tail uses the same actual first-divisor atoms and tuple fibres.
Only the original residual-profile constant and numerical decay window
are used, not a bound on the resulting tail amplitude. -/
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
  rw [T.calibration.tailBudget_eq_sum_parts]
  apply actual_terminal_pool_sum d _ _ budget Mmax (by positivity) hrow hlarge
  intro b
  have hAmplitude : (T.calibration.tag b).tailAmplitude ≤
      ((B ^ slots * profileConstant / (Ideal.absNorm S : ℝ)) * poolTagNormCharge P b) *
        Z ^ profileExponent b := by
    rw [T.calibration_tag, (T.profile b).calibration_tailAmplitude]
    convert mul_le_mul_of_nonneg_left (hraw b) (T.atoms b).scalarCost_nonneg using 1 <;>
      dsimp only [FirstDivisorCoefficientAtoms.scalarCost] <;> ring
  have hpart := (T.calibration.tag b).tailPart_le_power Cerror
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

end FirstDivisorWindows
end ActualPoolStages

/-- The actual common-support factor, with its original squared ideal,
has a uniform small-power cost.  Constants precede every source and
scale; the only window is the original norm of the common ideal. -/
theorem first_terminal_tuple_multiplicity_subpower (k : ℕ) (B ε : ℝ)
    (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ Ccount : ℝ, 0 < Ccount ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ D : Ideal (𝓞 K), (Ideal.absNorm D : ℝ) ≤ Z ^ B →
        (idealDivisorCount (D ^ 2) ^ k * 15 ^ k : ℕ) ≤
          (Ccount * (15 ^ k : ℕ)) * Z ^ ε := by
  obtain ⟨Ccount, hC, hcount⟩ :=
    support_tuple_multiplicity_subpower (K := K) k (2 * B) ε (by positivity) hε
  refine ⟨Ccount, hC, ?_⟩
  intro Z hZ D hD
  have hz : 0 ≤ Z := zero_le_one.trans hZ
  have hD2 : (Ideal.absNorm (D ^ 2) : ℝ) ≤ Z ^ (2 * B) := by
    calc
      _ = (Ideal.absNorm D : ℝ) ^ 2 := by simp only [map_pow, Nat.cast_pow]
      _ ≤ (Z ^ B) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hD 2
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hz]; congr 1; ring
  have h := mul_le_mul_of_nonneg_right (hcount Z hZ (D ^ 2) hD2)
    (Nat.cast_nonneg (15 ^ k))
  simpa only [Nat.cast_mul, Nat.cast_pow, mul_assoc, mul_left_comm, mul_comm] using h

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.FirstDivisorWindows.zeroBudget_le_original_profiles
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.FirstDivisorWindows.tailBudget_le_original_profiles
#print axioms HeckeSkeleton.Moments.EngineStep.first_terminal_tuple_multiplicity_subpower
