import HeckeSkeleton.HighBinSupport.ActualEulerData
import HeckeSkeleton.HighBinSupport.ActualRegularEuler
import HeckeSkeleton.HighBinSupport.EulerMarkedSubpower

/-!
# The actual finite-table Euler product throughout the high-bin move

The local equalities below identify all four regular/ramified and
marked/unmarked branches of the constructed `RowEulerData`. Ideal counting
then supplies normal convergence, joint continuity, s-holomorphy and
uniform conductor-subpower bounds for the repository's `rowCorrection`.
The Fourier-to-Euler initial calibration remains a separate arithmetic
identity; none of the results below assume it.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinActualEuler

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds
open HeckeSkeleton.HighBinContinuation
open HighBinBoundary.CoarseEuler
open Set Filter
open scoped Classical BigOperators Topology ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def rowIndex (u : FrequencyRow K S) (p : ExteriorPrime K S) : Fin 5 :=
  if hp : p ∈ exteriorSupport K S u.ideal then rowRamifiedIndex K S u p hp else 0

def rowW (P : ProbeData K S) (u : FrequencyRow K S) (p : ExteriorPrime K S) : ℂ :=
  primeCoefficient K (arithmeticRowCharacter K S P u) p.val

def rowD (P : ProbeData K S) (ψ : HeckeCharacter K)
    (u : FrequencyRow K S) (p : ExteriorPrime K S) : ℂ :=
  primeCoefficient K ψ p.val * conj (rowW K S P u p)

def rowE (P : ProbeData K S) (ψ : HeckeCharacter K) (p : ExteriorPrime K S) : ℂ :=
  primeCoefficient K (thetaPeriod K S P ψ) p.val ^ 6

theorem rowW_norm (P : ProbeData K S) (u : FrequencyRow K S) (p : ExteriorPrime K S) :
    ‖rowW K S P u p‖ ≤ 1 := norm_primeCoefficient_le_one K _ p.val

theorem rowD_norm (P : ProbeData K S) (ψ : HeckeCharacter K)
    (u : FrequencyRow K S) (p : ExteriorPrime K S) : ‖rowD K S P ψ u p‖ ≤ 1 :=
  actualEuler_D_phase_norm K S ψ (arithmeticRowCharacter K S P u) p

theorem rowE_norm (P : ProbeData K S) (ψ : HeckeCharacter K) (p : ExteriorPrime K S) :
    ‖rowE K S P ψ p‖ ≤ 1 := actualEuler_E_phase_norm K S P ψ p

def localFactor (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (p : ExteriorPrime K S) (v : ℂ × ℂ × ℂ) : ℂ :=
  if hp : p ∈ rowExceptionalPrimes K S Q u then
    finiteEulerRationalValue
      ((arithmeticHighEulerData K S P ψ).exceptionalFactor Q u ⟨p, hp⟩)
      (p.val.asIdeal.absNorm : ℝ) v.1 v.2.1 v.2.2
  else localRowCorrection K S P ψ (arithmeticRowCharacter K S P u) p v.1 v.2.1 v.2.2

/-- Literal finite-table evaluation identifies every branch on the open
swept tube. No quotient by a local Gauss polynomial is introduced. -/
theorem localFactor_eq_explicit (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    {a e : ℝ} (ha : 51 / 100 ≤ a) (he : 0 ≤ e)
    (p : ExteriorPrime K S) (v : ℂ × ℂ × ℂ) (hv : v ∈ sweptTube a e) :
    localFactor K S P ψ Q u p v =
      explicitLocalEuler (exteriorSupport K S u.ideal) Q
        (fun p : ExteriorPrime K S => (p.val.asIdeal.absNorm : ℝ))
        (rowW K S P u) (rowD K S P ψ u) (rowE K S P ψ)
        (rowPhaseData K S P ψ u) (rowIndex K S u) p v := by
  have hq := exteriorPrime_norm_two_le K S p
  have hq0 : (0 : ℝ) < p.val.asIdeal.absNorm := by linarith
  by_cases hR : p ∈ exteriorSupport K S u.ideal
  · have hp : p ∈ rowExceptionalPrimes K S Q u := Finset.mem_union_left Q hR
    have hden : 1 - coordR (rowPhaseData K S P ψ u p)
        (p.val.asIdeal.absNorm : ℝ) v.1 v.2.2 ≠ 0 :=
      one_sub_R_ne_zero _ (coordR_swept_half _ _ a e hq (by linarith) he
        v.1 v.2.2 hv.1.le hv.2.2.le)
    have hvalue := HighBinFiniteTables.ramified_value (rowPhaseData K S P ψ u p)
      (p.val.asIdeal.absNorm : ℝ) hq0 v.1 v.2.1 v.2.2
      (rowRamifiedIndex K S u p hR) (decide (p ∈ Q)) hden
    by_cases hQ : p ∈ Q
    · simpa [localFactor, arithmeticHighEulerData, exceptionalFactor, explicitLocalEuler,
        rowIndex, hp, hR, hQ] using hvalue
    · simpa [localFactor, arithmeticHighEulerData, exceptionalFactor, explicitLocalEuler,
        rowIndex, hp, hR, hQ] using hvalue
  · by_cases hQ : p ∈ Q
    · have hp : p ∈ rowExceptionalPrimes K S Q u :=
        Finset.mem_union_right (exteriorSupport K S u.ideal) hQ
      have hden := phaseRowEuler_denominators_ne_zero hq ha he
        (rowD K S P ψ u p) (rowE K S P ψ p) v.1 v.2.2
        (rowD_norm K S P ψ u p) (rowE_norm K S P ψ p) hv.1.le hv.2.2.le
      have hvalue := HighBinFiniteTables.regular_value (p.val.asIdeal.absNorm : ℝ) hq0
        (rowW K S P u p) (rowD K S P ψ u p) (rowE K S P ψ p)
        v.1 v.2.1 v.2.2 true hden.1 hden.2
      simpa [localFactor, arithmeticHighEulerData, exceptionalFactor, explicitLocalEuler,
        rowW, rowD, rowE, hp, hR, hQ] using hvalue
    · have hp : p ∉ rowExceptionalPrimes K S Q u := by
        simp [rowExceptionalPrimes, hR, hQ]
      simpa only [localFactor, dif_neg hp, explicitLocalEuler, if_neg hR, if_neg hQ,
        sub_zero, rowW, rowD, rowE] using
        localRowCorrection_eq_phase K S P ψ (arithmeticRowCharacter K S P u)
          p v.1 v.2.1 v.2.2

theorem rowCorrection_eq_explicitEuler (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    {a e : ℝ} (ha : 51 / 100 ≤ a) (he : 0 ≤ e)
    (v : ℂ × ℂ × ℂ) (hv : v ∈ sweptTube a e) :
    rowCorrection K S P ψ (arithmeticHighEulerData K S P ψ) Q u v.1 v.2.1 v.2.2 =
      ∏' p : ExteriorPrime K S,
        explicitLocalEuler (exteriorSupport K S u.ideal) Q
          (fun p : ExteriorPrime K S => (p.val.asIdeal.absNorm : ℝ))
          (rowW K S P u) (rowD K S P ψ u) (rowE K S P ψ)
          (rowPhaseData K S P ψ u) (rowIndex K S u) p v := by
  change (∏' p : ExteriorPrime K S, localFactor K S P ψ Q u p v) = _
  apply tprod_congr
  intro p
  exact localFactor_eq_explicit K S P ψ Q u ha he p v hv

/-- The constructed actual row correction is jointly continuous on the
whole open tube, including zeros of its finite exceptional numerators. -/
theorem rowCorrection_continuousOn_sweptTube (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    {a e : ℝ} (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1) (he : 0 < e) (he1 : e ≤ 1 / 10000) :
    ContinuousOn (fun v : ℂ × ℂ × ℂ =>
      rowCorrection K S P ψ (arithmeticHighEulerData K S P ψ) Q u v.1 v.2.1 v.2.2)
      (sweptTube a e) := by
  have h := explicitEuler_continuousOn (exteriorSupport K S u.ideal) Q
    (fun p : ExteriorPrime K S => (p.val.asIdeal.absNorm : ℝ))
    (rowW K S P u) (rowD K S P ψ u) (rowE K S P ψ)
    (rowPhaseData K S P ψ u) (rowIndex K S u)
    (exteriorPrime_norm_two_le K S) ha ha1 he.le he1
    (rowW_norm K S P u) (rowD_norm K S P ψ u) (rowE_norm K S P ψ)
    (summable_exteriorPrime_swept_error K S he)
  exact h.congr (fun v hv => rowCorrection_eq_explicitEuler K S P ψ Q u ha he.le v hv)

/-- Holomorphy in the actual moving s variable follows from normal
convergence; no reciprocal-L or Euler-product holomorphy premise appears. -/
theorem rowCorrection_differentiableOn_s (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    {a e : ℝ} (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1) (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (w z : ℂ) (hw : 1 - a - 7 * e < w.re) (hz : 17 / 50 - e < z.re) :
    DifferentiableOn ℂ
      (fun s => rowCorrection K S P ψ (arithmeticHighEulerData K S P ψ) Q u s w z)
      {s | a + 15 * e < s.re} := by
  have h := explicitEuler_differentiableOn_s (exteriorSupport K S u.ideal) Q
    (fun p : ExteriorPrime K S => (p.val.asIdeal.absNorm : ℝ))
    (rowW K S P u) (rowD K S P ψ u) (rowE K S P ψ)
    (rowPhaseData K S P ψ u) (rowIndex K S u)
    (exteriorPrime_norm_two_le K S) ha ha1 he.le he1
    (rowW_norm K S P u) (rowD_norm K S P ψ u) (rowE_norm K S P ψ)
    (summable_exteriorPrime_swept_error K S he) w z hw hz
  exact h.congr (fun s hs =>
    rowCorrection_eq_explicitEuler K S P ψ Q u ha he.le (s, w, z) ⟨hs, hw, hz⟩)

/-- The norm product of the actual row-prime support is bounded by the
actual ideal norm; no conductor/radical estimate is supplied as data. -/
theorem rowSupport_norm_product_le (u : FrequencyRow K S) :
    (∏ p ∈ exteriorSupport K S u.ideal, (p.val.asIdeal.absNorm : ℝ)) ≤
      frequencyRowNorm K S u := by
  have hprod :
      (∏ p ∈ exteriorSupport K S u.ideal, (p.val.asIdeal.absNorm : ℝ)) =
        ∏ p ∈ (primeExponents u.ideal.val).support, (p.asIdeal.absNorm : ℝ) := by
    apply Finset.prod_bij (fun p _ => p.val)
    · intro p hp
      exact (mem_idealPrimeSupport_iff K u.ideal.val p.val).mpr
        ((mem_exteriorSupport_iff K S u.ideal p).mp hp)
    · intro p _ q _ hpq
      exact Subtype.ext hpq
    · intro p hp
      have hdiv : p.asIdeal ∣ u.ideal.val.val :=
        (mem_idealPrimeSupport_iff K u.ideal.val p).mp hp
      let p' : ExteriorPrime K S := ⟨p, u.ideal.property p hdiv⟩
      exact ⟨p', (mem_exteriorSupport_iff K S u.ideal p').mpr hdiv, rfl⟩
    · intro p _
      rfl
  have hnorm :
      (∏ p ∈ (primeExponents u.ideal.val).support,
        (p.asIdeal.absNorm : ℝ) ^ primeExponents u.ideal.val p) = frequencyRowNorm K S u := by
    have hrec := congrArg (fun I : NonzeroIdeal K => (I.val.absNorm : ℝ))
      (idealOfPrimeExponents_primeExponents u.ideal.val)
    simpa only [idealOfPrimeExponents, Finsupp.prod, map_prod, map_pow,
      Nat.cast_prod, Nat.cast_pow, frequencyRowNorm, exteriorNorm] using hrec
  rw [hprod, ← hnorm]
  apply Finset.prod_le_prod₀ (fun p _ => Nat.cast_nonneg _)
  intro p hp
  have hq : (1 : ℝ) ≤ p.asIdeal.absNorm :=
    one_le_idealNorm K ⟨p.asIdeal, mem_nonZeroDivisors_of_ne_zero p.ne_bot⟩
  have hn : 1 ≤ primeExponents u.ideal.val p :=
    Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
  simpa only [pow_one] using pow_le_pow_right₀ hq hn

/-- Polynomial majorant for the complete actual marked correction, uniform
in all three imaginary parts and in the row and mark sets. -/
theorem rowCorrection_coarse_bound (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    {a e : ℝ} (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1) (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (v : ℂ × ℂ × ℂ) (hv : v ∈ sweptTube a e) :
    ‖rowCorrection K S P ψ (arithmeticHighEulerData K S P ψ) Q u v.1 v.2.1 v.2.2‖ ≤
      (frequencyRowNorm K S u ^ 4 * markedBound ^ Q.card) *
        Real.exp (∑' p : ExteriorPrime K S,
          (11 / sweptTubeEulerMargin) * (p.val.asIdeal.absNorm : ℝ) ^ (-1 - 8 * e)) := by
  rw [rowCorrection_eq_explicitEuler K S P ψ Q u ha he.le v hv]
  have h := explicitEuler_coarse_bound (exteriorSupport K S u.ideal) Q
    (fun p : ExteriorPrime K S => (p.val.asIdeal.absNorm : ℝ))
    (rowW K S P u) (rowD K S P ψ u) (rowE K S P ψ)
    (rowPhaseData K S P ψ u) (rowIndex K S u)
    (exteriorPrime_norm_two_le K S) ha ha1 he.le he1
    (rowW_norm K S P u) (rowD_norm K S P ψ u) (rowE_norm K S P ψ)
    (summable_exteriorPrime_swept_error K S he) v hv
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans one_le_markedBound) _)
  exact pow_le_pow_left₀ (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)
    (rowSupport_norm_product_le K S u) 4

/-- A single conductor-subpower constant works for every actual probe,
target, row, mark set, bin endpoint and point of the swept tube. -/
theorem exists_uniform_rowCorrection_subpower {e η : ℝ}
    (he : 0 < e) (he1 : e ≤ 1 / 10000) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ProbeData K S) (ψ : HeckeCharacter K)
      (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) (a : ℝ),
      51 / 100 ≤ a → a ≤ 1 → ∀ v ∈ sweptTube a e,
        ‖rowCorrection K S P ψ (arithmeticHighEulerData K S P ψ) Q u v.1 v.2.1 v.2.2‖ ≤
          C * frequencyRowNorm K S u ^ η * markedBound ^ Q.card := by
  obtain ⟨C, hC, hbound⟩ := explicitEuler_marked_uniform_subpower
    (fun p : ExteriorPrime K S => (p.val.asIdeal.absNorm : ℝ))
    (exteriorPrime_norm_two_le K S) he.le he1 hη
    (summable_exteriorPrime_swept_error K S he)
  refine ⟨C, hC, ?_⟩
  intro P ψ Q u a ha ha1 v hv
  rw [rowCorrection_eq_explicitEuler K S P ψ Q u ha he.le v hv]
  exact hbound (exteriorSupport K S u.ideal) Q (frequencyRowNorm K S u) a
    (rowW K S P u) (rowD K S P ψ u) (rowE K S P ψ)
    (rowPhaseData K S P ψ u) (rowIndex K S u)
    (rowSupport_norm_product_le K S u) ha ha1
    (rowW_norm K S P u) (rowD_norm K S P ψ u) (rowE_norm K S P ψ) v hv

end HeckeSkeleton.HighBinActualEuler
