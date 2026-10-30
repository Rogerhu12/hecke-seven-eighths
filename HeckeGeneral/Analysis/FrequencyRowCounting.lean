import HeckeGeneral.Analysis.PhysicalProbeRows
import HeckeGeneral.Analysis.ExteriorIdealCounting

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain Set Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.Analysis.ActualSIntegerMoments
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem idealAvoidanceCount_empty_mono {X Y : ℝ}
    (hX : 0 ≤ X) (hXY : X ≤ Y) :
    idealAvoidanceCount K ∅ X ≤ idealAvoidanceCount K ∅ Y := by
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro I hI
  obtain ⟨hN, ha⟩ := (mem_idealAvoidanceFinset K hX I).mp hI
  exact (mem_idealAvoidanceFinset K (hX.trans hXY) I).mpr ⟨hN.trans hXY, ha⟩

/-- Uniform linear count of genuine nonzero integral ideals, including every
bounded initial scale. The constant is selected before the scale. -/
theorem dyadicIdealSupport_linear_count :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 1 ≤ U →
      ((dyadicIdealSupport K (U / 2)).card : ℝ) ≤ C * U := by
  have hev := (idealAvoidanceCount_empty_limit K).eventually
    (eventually_lt_nhds (lt_add_one (idealAvoidanceDensity K ∅)))
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hev
  let V := max 1 U₀
  let A := idealAvoidanceCount K ∅ V
  let B := idealAvoidanceDensity K ∅ + 1
  have hA : 0 ≤ A := Nat.cast_nonneg _
  have hB : 0 < B := by
    dsimp [B]
    linarith [idealAvoidanceDensity_pos K ∅]
  refine ⟨A + B, by positivity, ?_⟩
  intro U hU
  have hEq : ((dyadicIdealSupport K (U / 2)).card : ℝ) =
      idealAvoidanceCount K ∅ U := by
    have hfilter : (dyadicIdealSupport K (U / 2)).filter (avoidsIdealPrimes K ∅) =
        dyadicIdealSupport K (U / 2) := by
      apply Finset.filter_eq_self.mpr
      intro I _
      simp [avoidsIdealPrimes]
    simp only [idealAvoidanceCount, idealAvoidanceFinset, hfilter]
  rw [hEq]
  by_cases hUV : U ≤ V
  · have hsmall := idealAvoidanceCount_empty_mono K (by linarith : 0 ≤ U) hUV
    change idealAvoidanceCount K ∅ U ≤ A at hsmall
    exact hsmall.trans (by nlinarith)
  · have hlarge := hU₀ U ((le_max_right 1 U₀).trans (le_of_not_ge hUV))
    have hbound : idealAvoidanceCount K ∅ U < B * U :=
      (div_lt_iff₀ (by linarith : 0 < U)).mp hlarge
    exact hbound.le.trans (by nlinarith)

/-- Every sixth-unit sector is retained; deleting arithmetic filters only
enlarges the count. -/
theorem frequencyRows_card_le_support (U : ℝ) :
    ((frequencyRows K S U).card : ℝ) ≤
      (Nat.card (SixthUnitClasses K S) : ℝ) *
        ((dyadicIdealSupport K (U / 2)).card : ℝ) := by
  let : Fintype (SixthUnitClasses K S) := Fintype.ofFinite _
  unfold frequencyRows
  apply le_trans (Nat.cast_le.mpr (Finset.card_image_le))
  simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_attach,
    Finset.card_univ, Nat.cast_mul, Nat.card_eq_fintype_card]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_filter_le _ _))
    (Nat.cast_nonneg _)

/-- Fixed K and S determine the constant before U. No row-count input is used. -/
theorem frequencyRows_linear_count :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 1 ≤ U →
      ((frequencyRows K S U).card : ℝ) ≤ C * U := by
  obtain ⟨C, hC, hb⟩ := dyadicIdealSupport_linear_count K
  have hM : (0 : ℝ) < Nat.card (SixthUnitClasses K S) := by
    exact_mod_cast Nat.card_pos (α := SixthUnitClasses K S)
  refine ⟨(Nat.card (SixthUnitClasses K S) : ℝ) * C, mul_pos hM hC, ?_⟩
  intro U hU
  exact (frequencyRows_card_le_support K S U).trans
    (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (hb U hU) hM.le)

/-- An actual shell inclusion implies the linear count of any row subset. -/
theorem physicalRows_linear_count_of_subset {c : ℝ} (hc : 1 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 1 ≤ U →
      ∀ R : Finset (FrequencyRow K S), R ⊆ frequencyRows K S (c * U) →
        (R.card : ℝ) ≤ C * U := by
  obtain ⟨C, hC, hb⟩ := frequencyRows_linear_count K S
  refine ⟨C * c, mul_pos hC (by linarith), ?_⟩
  intro U hU R hR
  have hcU : 1 ≤ c * U := by nlinarith
  exact (Nat.cast_le.mpr (Finset.card_le_card hR)).trans
    (by simpa only [mul_assoc] using hb (c * U) hcU)

/-- At a physical shell U = Z^shell the linear estimate implies the floor
count with any nonnegative slack; the constant precedes Z and shell. -/
theorem physicalRows_floor_count_of_subset {c : ℝ} (hc : 1 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z shell lam : ℝ, 1 ≤ Z → 0 ≤ shell → 0 ≤ lam →
      ∀ R : Finset (FrequencyRow K S), R ⊆ frequencyRows K S (c * Z ^ shell) →
        (R.card : ℝ) ≤ C * (Z ^ shell) ^ (1 + lam) := by
  obtain ⟨C, hC, hb⟩ := physicalRows_linear_count_of_subset K S hc
  refine ⟨C, hC, ?_⟩
  intro Z shell lam hZ hs hl R hR
  have hU : 1 ≤ Z ^ shell := Real.one_le_rpow hZ hs
  apply (hb (Z ^ shell) hU R hR).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hU (by linarith : (1 : ℝ) ≤ 1 + lam)

end HeckeGeneral.ThetaSkeleton.Physical
