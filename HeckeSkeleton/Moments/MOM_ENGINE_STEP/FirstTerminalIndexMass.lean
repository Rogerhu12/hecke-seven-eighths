import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FiniteBranchIndex

/-!
# The actual first labels of second-zero and tail terminals

These terminals stop before a second common-support or divisor label
exists.  Their arithmetic carrier is therefore precisely the first
common label and its first shared divisor.  The first Cauchy allowance
is retained literally, and the divisor density is the actual `1 / N(S)`.

The theorem below derives the finite mass from original ideal windows.
It does not create second labels.  When used for a source, its divisor
density must be supplied by the original individual coefficient or
profile normalization; no total terminal estimate is assumed here.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep.CommonSupportMass

open NumberField UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]

abbrev FirstTerminalIndex (first : Finset (Label K))
    (divisors : Label K → Finset (Ideal (𝓞 K))) :=
  Σ v : first, divisors v.val

def firstTerminalIndexWeight (Z : ℝ) (first : Finset (Label K))
    (divisors : Label K → Finset (Ideal (𝓞 K)))
    (i : FirstTerminalIndex first divisors) : ℝ :=
  firstCommonWeight Z i.1.val.1.1 i.1.val.1.2 *
    ‖(moebius i.2.val : ℂ)‖ / (Ideal.absNorm i.2.val : ℝ)

theorem firstTerminalIndexWeight_nonneg (Z : ℝ) (first : Finset (Label K))
    (divisors : Label K → Finset (Ideal (𝓞 K))) (hZ : 0 ≤ Z)
    (i : FirstTerminalIndex first divisors) :
    0 ≤ firstTerminalIndexWeight Z first divisors i :=
  div_nonneg (mul_nonneg (Real.rpow_nonneg hZ _) (norm_nonneg _)) (Nat.cast_nonneg _)

theorem sum_firstTerminalIndexWeight (Z : ℝ) (first : Finset (Label K))
    (divisors : Label K → Finset (Ideal (𝓞 K))) :
    (∑ i : FirstTerminalIndex first divisors, firstTerminalIndexWeight Z first divisors i) =
      ∑ v ∈ first, firstCommonWeight Z v.1.1 v.1.2 *
        ∑ S ∈ divisors v, ‖(moebius S : ℂ)‖ / (Ideal.absNorm S : ℝ) := by
  simp only [FirstTerminalIndex, Fintype.sum_sigma, firstTerminalIndexWeight,
    mul_div_assoc, ← Finset.mul_sum]
  have hS (v : Label K) :
      (∑ S : divisors v, ‖(moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) =
        ∑ S ∈ divisors v, ‖(moebius S : ℂ)‖ / (Ideal.absNorm S : ℝ) :=
    Finset.sum_coe_sort (divisors v)
      (fun S => ‖(moebius S : ℂ)‖ / (Ideal.absNorm S : ℝ))
  simp_rw [hS]
  exact Finset.sum_coe_sort first (fun v => firstCommonWeight Z v.1.1 v.1.2 *
    ∑ S ∈ divisors v, ‖(moebius S : ℂ)‖ / (Ideal.absNorm S : ℝ))

/-- The constant precedes every moving source carrier and every
decorating phase, sector, mask or side label.  Only their actual finite
fibres are counted. -/
theorem uniform_first_terminal_index_mass (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 < Z →
      ∀ oldMask : Ideal (𝓞 K), Squarefree oldMask → oldMask ≠ 0 →
      ∀ first : Finset (Label K),
      (∀ v ∈ first, Valid oldMask v) →
      (∀ v ∈ first, (Ideal.absNorm v.1.1 : ℝ) ≤ Z ^ B ∧
        (Ideal.absNorm v.1.2 : ℝ) ≤ Z ^ B) →
      ∀ divisors : Label K → Finset (Ideal (𝓞 K)),
      (∀ v ∈ first, ∀ S ∈ divisors v, S ≠ 0) →
      (∀ v ∈ first, ∀ S ∈ divisors v, (Ideal.absNorm S : ℝ) ≤ Z ^ B) →
      ∀ {I : Type*} [Fintype I] (index : I → FirstTerminalIndex first divisors)
        (multiplicity : ℝ), 0 ≤ multiplicity →
      (∀ j, ((Finset.univ.filter (fun i => index i = j)).card : ℝ) ≤ multiplicity) →
      (∑ i : I, firstTerminalIndexWeight Z first divisors (index i)) ≤
        multiplicity * C * Z ^ ε / (Ideal.absNorm oldMask : ℝ) := by
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Ccommon, hCcommon, hcommon⟩ := actual_first_common_mass (K := K) B δ hB hδ
  obtain ⟨Cdivisor, hCdivisor, hdivisor⟩ := ideal_inverse_norm_subpower (K := K) B δ hB hδ
  refine ⟨Ccommon * Cdivisor, mul_pos hCcommon hCdivisor, ?_⟩
  intro Z hZ oldMask hmask hmask0 first hvalid hnorm divisors hdiv0 hdivN
    I inst index multiplicity hmult hcard
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hinner (v : Label K) (hv : v ∈ first) :
      (∑ S ∈ divisors v, ‖(moebius S : ℂ)‖ / (Ideal.absNorm S : ℝ)) ≤
        Cdivisor * Z ^ δ := by
    calc
      _ ≤ ∑ S ∈ divisors v, 1 / (Ideal.absNorm S : ℝ) := by
        apply Finset.sum_le_sum
        intro S hS
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        unfold UniqueFactorizationMonoid.moebius
        split_ifs <;> simp
      _ ≤ _ := hdivisor Z hZ.le (divisors v) (hdiv0 v hv) (hdivN v hv)
  have hbase :
      (∑ i : FirstTerminalIndex first divisors, firstTerminalIndexWeight Z first divisors i) ≤
        (Ccommon * Cdivisor) * Z ^ ε / (Ideal.absNorm oldMask : ℝ) := by
    rw [sum_firstTerminalIndexWeight]
    calc
      _ ≤ ∑ v ∈ first, firstCommonWeight Z v.1.1 v.1.2 * (Cdivisor * Z ^ δ) :=
        Finset.sum_le_sum fun v hv => mul_le_mul_of_nonneg_left (hinner v hv)
          (Real.rpow_nonneg hz.le _)
      _ = (∑ v ∈ first, firstCommonWeight Z v.1.1 v.1.2) * (Cdivisor * Z ^ δ) := by
        rw [Finset.sum_mul]
      _ ≤ (Ccommon * Z ^ δ / (Ideal.absNorm oldMask : ℝ)) * (Cdivisor * Z ^ δ) :=
        mul_le_mul_of_nonneg_right
          (hcommon Z hZ oldMask hmask hmask0 first hvalid hnorm)
          (mul_nonneg hCdivisor.le (Real.rpow_nonneg hz.le _))
      _ = _ := by
        have hεeq : ε = δ + δ := by dsimp [δ]; ring
        rw [hεeq, Real.rpow_add hz]
        ring
  have hfibre := sum_weighted_fibres_le index (firstTerminalIndexWeight Z first divisors)
    (firstTerminalIndexWeight_nonneg Z first divisors hz.le) multiplicity (fun j => by
      convert hcard j using 1 <;> congr 2 <;> ext i <;> simp)
  exact hfibre.trans ((mul_le_mul_of_nonneg_left hbase hmult).trans_eq (by ring))

end HeckeSkeleton.Moments.EngineStep.CommonSupportMass

#print axioms HeckeSkeleton.Moments.EngineStep.CommonSupportMass.sum_firstTerminalIndexWeight
#print axioms HeckeSkeleton.Moments.EngineStep.CommonSupportMass.uniform_first_terminal_index_mass
