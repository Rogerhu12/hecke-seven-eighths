import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCoveredLabels
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SameCarrierTerminalBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ResidualTerminalCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolMass

/-!
# The zero and tail budgets on the original four pool branches

The main source has its one pool-length allowance.  Each of the three
residual sources has the actual moving norm paid by its original local
error weight.  Both statements use the earlier pool and its one density.

The terminal conclusions below start with individual profile amplitudes,
the original row fibre bound, and the residual factor multiplicities.
The finite sum of terminal parts is proved here, rather than supplied as
an additional parent or terminal estimate.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments HeckePort.CenteredMomentCounting
open MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}

/-- The literal norm allowance of a main or residual pool tag. -/
def poolTagNormCharge (P : PowerScaleExteriorPool A bad Z ell eps) :
    PoolSourceTag P → ℝ
  | .inl _ => Z ^ ell
  | .inr (.inl p) => Q p.val ^ amplifierMovingExponent 1
  | .inr (.inr (.inl p)) => Q p.val ^ amplifierMovingExponent 6
  | .inr (.inr (.inr p)) => Q p.val ^ amplifierMovingExponent 7

theorem poolTagNormCharge_nonneg (b : PoolSourceTag P) :
    0 ≤ poolTagNormCharge P b := by
  rcases b with u | p | p | p
  · exact Real.rpow_nonneg (zero_le_one.trans P.base_gt_one.le) _
  all_goals
    exact pow_nonneg (by change (0 : ℝ) ≤ (Ideal.absNorm _ : ℝ); positivity) _

/-- This fixed numerical constant is independent of the original
columns, the pool, and all Fourier and divisor labels. -/
def poolTerminalConstant (K : Type) [Field K] [NumberField K]
    (ell Mmax : ℝ) : ℝ :=
  4 * (2 * ((Mmax + 6 * ell) / (ell / 2)) + 6 * idealCountConstant K)

theorem poolTerminalConstant_pos (ell Mmax : ℝ) (hell : 0 < ell)
    (hMmax : 0 ≤ Mmax) : 0 < poolTerminalConstant K ell Mmax := by
  have hI : 0 < idealCountConstant K :=
    zero_lt_one.trans_le (one_le_idealCountConstant K)
  unfold poolTerminalConstant
  positivity

namespace FirstGaussPoolData

variable (d : FirstGaussPoolData C P ι)

theorem sum_tag_norm_charge :
    (∑ b : PoolSourceTag P, d.tagWeight b * poolTagNormCharge P b) =
      d.multiplicity * Z ^ ell +
      (∑ p ∈ P.primes, localErrorWeight p 1 * Q p ^ amplifierMovingExponent 1) +
      (∑ p ∈ P.primes, localErrorWeight p 6 * Q p ^ amplifierMovingExponent 6) +
      (∑ p ∈ P.primes, localErrorWeight p 7 * Q p ^ amplifierMovingExponent 7) := by
  simp only [PoolSourceTag, Fintype.sum_sum_type, Fintype.sum_unique,
    tagWeight, poolTagNormCharge]
  rw [← Finset.sum_subtype P.primes (fun _ => Iff.rfl)
      (fun p => localErrorWeight p 1 * Q p ^ amplifierMovingExponent 1),
    ← Finset.sum_subtype P.primes (fun _ => Iff.rfl)
      (fun p => localErrorWeight p 6 * Q p ^ amplifierMovingExponent 6),
    ← Finset.sum_subtype P.primes (fun _ => Iff.rfl)
      (fun p => localErrorWeight p 7 * Q p ^ amplifierMovingExponent 7)]
  ring

/-- Actual main and 1/6/7 labels, with a single original pool density. -/
theorem tag_norm_charge_mass_le (Mmax : ℝ) (hrow : d.rowExponent ≤ Mmax)
    (hlarge : 2 * (d.rowExponent / (ell / 2) +
      d.frozenExponent / (ell / 2)) ≤ Z ^ (ell - eps)) :
    (4 / d.density) *
        (∑ b : PoolSourceTag P, d.tagWeight b * poolTagNormCharge P b) ≤
      poolTerminalConstant K ell Mmax * Z ^ eps := by
  have hz : 0 < Z := zero_lt_one.trans P.base_gt_one
  let T : ℝ := (Mmax + 6 * ell) / (ell / 2)
  have hMmax := d.rowExponent_nonneg.trans hrow
  have hell := P.exponent_pos
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hmult : d.multiplicity ≤ T := by
    unfold multiplicity T
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hmainPrefactor : Z ^ ell / d.density ≤ 2 * Z ^ eps := by
    calc
      _ = Z ^ ell * (1 / d.density) := by ring
      _ ≤ Z ^ ell * (2 * Z ^ (-ell + eps)) :=
        mul_le_mul_of_nonneg_left
          (P.density_inverse d.rowExponent d.frozenExponent hlarge)
          (Real.rpow_nonneg hz.le _)
      _ = _ := by
        rw [show Z ^ ell * (2 * Z ^ (-ell + eps)) =
          2 * (Z ^ ell * Z ^ (-ell + eps)) by ring, ← Real.rpow_add hz]
        congr 2
        ring
  have hmain : d.multiplicity * Z ^ ell / d.density ≤ 2 * T * Z ^ eps := by
    calc
      _ = d.multiplicity * (Z ^ ell / d.density) := by ring
      _ ≤ T * (2 * Z ^ eps) :=
        mul_le_mul hmult hmainPrefactor
          (div_nonneg (Real.rpow_nonneg hz.le _) d.density_pos.le) hT
      _ = _ := by ring
  have herror (n : ℕ) :
      (∑ p ∈ P.primes, localErrorWeight p n * Q p ^ amplifierMovingExponent n) /
        d.density ≤ 2 * idealCountConstant K * Z ^ eps :=
    actual_error_pool_mass P d.rowExponent d.frozenExponent hlarge n
  rw [d.sum_tag_norm_charge]
  calc
    _ = 4 * (d.multiplicity * Z ^ ell / d.density +
        (∑ p ∈ P.primes, localErrorWeight p 1 * Q p ^ amplifierMovingExponent 1) /
          d.density +
        (∑ p ∈ P.primes, localErrorWeight p 6 * Q p ^ amplifierMovingExponent 6) /
          d.density +
        (∑ p ∈ P.primes, localErrorWeight p 7 * Q p ^ amplifierMovingExponent 7) /
          d.density) := by ring
    _ ≤ 4 * (2 * T * Z ^ eps +
        2 * idealCountConstant K * Z ^ eps +
        2 * idealCountConstant K * Z ^ eps +
        2 * idealCountConstant K * Z ^ eps) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add (add_le_add hmain (herror 1)) (herror 6)) (herror 7))
        (by norm_num)
    _ = _ := by unfold poolTerminalConstant; dsimp [T]; ring

/-- Only the raw row and frozen-ideal exponent box is used to choose
the scale threshold.  It precedes the actual source and the prime pool. -/
theorem uniform_tag_norm_charge_mass (ell eps Mmax Bmax : ℝ)
    (hell : 0 < ell) (hepsell : eps < ell) (hMmax : 0 ≤ Mmax) (hBmax : 0 ≤ Bmax) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ∀ bad : Finset (HeightOneSpectrum (𝓞 K)),
      ∀ P : PowerScaleExteriorPool A bad Z ell eps,
      ∀ d : FirstGaussPoolData C P ι,
      d.rowExponent ≤ Mmax → d.frozenExponent ≤ Bmax →
        (2 * (d.rowExponent / (ell / 2) + d.frozenExponent / (ell / 2)) ≤
          Z ^ (ell - eps)) ∧
        (4 / d.density) *
            (∑ b : PoolSourceTag P, d.tagWeight b * poolTagNormCharge P b) ≤
          poolTerminalConstant K ell Mmax * Z ^ eps := by
  have hevent := (_root_.tendsto_rpow_atTop (sub_pos.mpr hepsell)).eventually
    (Filter.eventually_ge_atTop (2 * (Mmax / (ell / 2) + Bmax / (ell / 2))))
  obtain ⟨Z₁, hZ₁⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨max Z₁ 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro Z hZ bad P d hrow hfrozen
  have hlarge : 2 * (d.rowExponent / (ell / 2) + d.frozenExponent / (ell / 2)) ≤
      Z ^ (ell - eps) := by
    apply le_trans _ (hZ₁ Z ((le_max_left _ _).trans hZ))
    exact mul_le_mul_of_nonneg_left
      (add_le_add (div_le_div_of_nonneg_right hrow (by positivity))
        (div_le_div_of_nonneg_right hfrozen (by positivity))) (by norm_num)
  exact ⟨hlarge, d.tag_norm_charge_mass_le Mmax hrow hlarge⟩

private theorem sum_le_tag_norm_charge (f : PoolSourceTag P → ℝ)
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
      intro b hb
      ring
    _ = ((4 / d.density) * ∑ b, d.tagWeight b * poolTagNormCharge P b) *
        (H * Z ^ budget) := by rw [← Finset.sum_mul]; ring
    _ ≤ (poolTerminalConstant K ell Mmax * Z ^ eps) * (H * Z ^ budget) :=
      mul_le_mul_of_nonneg_right (d.tag_norm_charge_mass_le Mmax hrow hlarge)
        (mul_nonneg hH (Real.rpow_nonneg hz.le _))
    _ = _ := by rw [Real.rpow_add hz]; ring

end FirstGaussPoolData

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

namespace ActualPoolStages.TerminalCalibration

variable {d : FirstGaussPoolData C P ι} {c : ι → ℂ}
variable {s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}
variable (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)

/-- The constructor `residualTailWindows` has these exact multiplicities.
This deduction uses their values, without asking for a residual injection. -/
theorem tag_multiplicity_le
    (hmain : T.main.windows.multiplicity ≤ 1)
    (hone : ∀ p, (T.one p).windows.multiplicity = 3 ^ k)
    (hsix : ∀ p, (T.six p).windows.multiplicity = 13 ^ k)
    (hseven : ∀ p, (T.seven p).windows.multiplicity = 15 ^ k)
    (b : PoolSourceTag P) : (T.tag b).windows.multiplicity ≤ 15 ^ k := by
  rcases b with u | p | p | p
  · exact hmain.trans (by simpa using Nat.pow_le_pow_left (by norm_num : 1 ≤ 15) k)
  · change (T.one p).windows.multiplicity ≤ 15 ^ k
    rw [hone p]
    exact Nat.pow_le_pow_left (by norm_num) k
  · change (T.six p).windows.multiplicity ≤ 15 ^ k
    rw [hsix p]
    exact Nat.pow_le_pow_left (by norm_num) k
  · change (T.seven p).windows.multiplicity ≤ 15 ^ k
    rw [hseven p]

/-- The original zero-profile amplitudes, with their numerical
exponent ledger, imply the full same-pool zero budget. -/
theorem zeroPart_sum_le (ε Czero profileConstant budget Mmax : ℝ)
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
    (4 / d.density) *
        (∑ b : PoolSourceTag P, d.tagWeight b * (T.tag b).zeroPart ε Czero) ≤
      poolTerminalConstant K ell Mmax *
        ((fiberBound : ℝ) * (15 ^ k : ℕ) * Czero * profileConstant) * Z ^ (budget + eps) := by
  apply d.sum_le_tag_norm_charge _ _ _ Mmax (by positivity) hrow hlarge
  intro b
  have hcounts : ((s.tag b).fiber : ℝ) * (T.tag b).windows.multiplicity ≤
      (fiberBound : ℝ) * (15 ^ k : ℕ) :=
    mul_le_mul (by exact_mod_cast hfiber b) (by exact_mod_cast hmult b)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hscalar := mul_le_mul_of_nonneg_right hcounts
    (mul_nonneg hC (mul_nonneg hprofile (poolTagNormCharge_nonneg b)))
  have hpart := (T.tag b).zeroPart_le_power ε Czero
    (profileConstant * poolTagNormCharge P b) (profileExponent b) budget hC
    (mul_nonneg hprofile (poolTagNormCharge_nonneg b)) (hAmplitude b) (hbudget b)
  apply hpart.trans
  convert mul_le_mul_of_nonneg_right hscalar
    (Real.rpow_nonneg (zero_le_one.trans P.base_gt_one.le) budget) using 1 <;> ring

/-- The tail conclusion uses the same actual tags and multiplicities.
Only the original profile amplitude and the chosen tail decay enter. -/
theorem tailPart_sum_le (Cerror profileConstant budget Mmax : ℝ)
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
    (4 / d.density) *
        (∑ b : PoolSourceTag P, d.tagWeight b * (T.tag b).tailPart Cerror) ≤
      poolTerminalConstant K ell Mmax *
        ((fiberBound : ℝ) * (15 ^ k : ℕ) * Cerror * profileConstant) * Z ^ (budget + eps) := by
  apply d.sum_le_tag_norm_charge _ _ _ Mmax (by positivity) hrow hlarge
  intro b
  have hcounts : ((s.tag b).fiber : ℝ) * (T.tag b).windows.multiplicity ≤
      (fiberBound : ℝ) * (15 ^ k : ℕ) :=
    mul_le_mul (by exact_mod_cast hfiber b) (by exact_mod_cast hmult b)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hscalar := mul_le_mul_of_nonneg_right hcounts
    (mul_nonneg hC (mul_nonneg hprofile (poolTagNormCharge_nonneg b)))
  have hpart := (T.tag b).tailPart_le_power Cerror
    (profileConstant * poolTagNormCharge P b) (profileExponent b) budget hC
    (mul_nonneg hprofile (poolTagNormCharge_nonneg b)) (hAmplitude b) (hbudget b)
  apply hpart.trans
  convert mul_le_mul_of_nonneg_right hscalar
    (Real.rpow_nonneg (zero_le_one.trans P.base_gt_one.le) budget) using 1 <;> ring

end ActualPoolStages.TerminalCalibration
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.uniform_tag_norm_charge_mass
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.TerminalCalibration.zeroPart_sum_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.TerminalCalibration.tailPart_sum_le
