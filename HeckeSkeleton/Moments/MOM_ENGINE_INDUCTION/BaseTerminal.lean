import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Interface
import HeckePort.CenteredMoment.Counting
import HeckeGeneral.Analysis.PrimePolynomialAbsoluteBound

/-!
# Absolute terminal estimates at the actual width floor

This proves the small-width base in revised §4.8, lines 2771--2783, for
the literal `Node` coefficient.  Actual ideal counting, unitary Hecke
coefficients and the original common mask give the `sqrt N` bound for
each normalized plain polynomial.  Both formal rectangles retain their
common product, including positive scales below one.

The normalized exponent obtained from absolute prime counting is
`n₁ + n₂ + totalLength`, with slot cost `z`, not `κ*z`.  The positive
capacity `n₁ + n₂ + 6*κ*z ≤ M` and `κ ≥ 3/4` imply that this exponent is
at most `M`.  No prime-cancellation bound is used in that argument.
The zero-slot case uses the separately supplied reflected padded core.

The analytic inputs here are profile support and supremum bounds.  The
whole-family uniformity of those profile constants is a separate source
calibration obligation.  No moment bound or terminal energy estimate is
assumed in the constructors below.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.CenteredMomentCounting
open scoped BigOperators Classical

universe v

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- A count for the actual nonzero ideals, also valid below norm one. -/
theorem finite_ideal_rows_count (rows : Finset (NonzeroIdeal K)) (H : ℝ)
    (hH : 0 ≤ H) (hnorm : ∀ I ∈ rows, idealNorm K I ≤ H) :
    (rows.card : ℝ) ≤ idealCountConstant K * H := by
  by_cases hne : rows.Nonempty
  · obtain ⟨I, hI⟩ := hne
    have hHone : 1 ≤ H := (one_le_idealNorm K I).trans (hnorm I hI)
    have hinj : Function.Injective (fun J : NonzeroIdeal K => J.val) :=
      fun _ _ h => Subtype.ext h
    have hc := card_le_idealCountConstant K (rows.image fun J => J.val) H hHone (by
      intro J hJ
      obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hJ
      exact hnorm J hJ)
    simpa only [Finset.card_image_of_injective rows hinj] using hc
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (zero_le_one.trans (one_le_idealCountConstant K)) hH

/-- With norm-ratio support at most two, only `2*N < 1` forces emptiness.
In particular the proof does not incorrectly discard a possible unit ideal
when `1/2 < N < 1`. -/
theorem idealTest_support_empty_of_subunit (W : IdealTest K)
    (u : NonzeroIdeal K) (t N : ℝ) (hN : 0 < N) (hsmall : 2 * N < 1)
    (hann : Function.support (W.profile u t) ⊆ Set.Iic (2 : ℝ)) :
    W.support u t N = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro I hI
  have hratio : idealNorm K I / N ≤ 2 := hann ((W.support_spec u t N I).1 hI)
  have hnorm := (div_le_iff₀ hN).1 hratio
  linarith [one_le_idealNorm K I]

theorem idealTest_support_count (W : IdealTest K)
    (u : NonzeroIdeal K) (t N : ℝ) (hN : 0 < N)
    (hann : Function.support (W.profile u t) ⊆ Set.Iic (2 : ℝ)) :
    ((W.support u t N).card : ℝ) ≤ (2 * idealCountConstant K) * N := by
  have hc := finite_ideal_rows_count (W.support u t N) (2 * N) (by positivity) (by
    intro I hI
    exact (div_le_iff₀ hN).1 (hann ((W.support_spec u t N I).1 hI)))
  convert hc using 1 <;> ring

def plainAbsoluteConstant (K : Type) [Field K] [NumberField K] (B : ℝ) : ℝ :=
  2 * idealCountConstant K * B

theorem plainAbsoluteConstant_nonneg (B : ℝ) (hB : 0 ≤ B) :
    0 ≤ plainAbsoluteConstant K B := by
  have hc := one_le_idealCountConstant K
  unfold plainAbsoluteConstant
  positivity

/-- True square-root normalization for every positive real scale.  The
character and arbitrary original Boolean mask can only reduce a term. -/
theorem plainPolynomial_absolute_bound (d : MomentData K ω ψ) (W : IdealTest K)
    (u : NonzeroIdeal K) (N t B : ℝ) (hN : 0 < N) (hB : 0 ≤ B)
    (hann : Function.support (W.profile u t) ⊆ Set.Iic (2 : ℝ))
    (hprof : ∀ y, ‖W.profile u t y‖ ≤ B) :
    ‖plainPolynomial d W u N t‖ ≤ plainAbsoluteConstant K B * Real.sqrt N := by
  have hmask (I : Ideal (𝓞 K)) : ‖maskValue d u I‖ ≤ 1 := by
    unfold maskValue
    split_ifs <;> simp
  have hterm (I : NonzeroIdeal K) :
      ‖heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u) I *
          W.profile u t (idealNorm K I / N) * maskValue d u I.val‖ ≤ B := by
    simp only [norm_mul]
    calc
      _ ≤ 1 * B * 1 :=
        mul_le_mul
          (mul_le_mul (norm_heckeIdealCoefficient_le_one K _ I) (hprof _)
            (norm_nonneg _) zero_le_one)
          (hmask _) (norm_nonneg _) (by simpa only [one_mul] using hB)
      _ = B := by ring
  have hsum : ‖∑ I ∈ W.support u t N,
      heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u) I *
        W.profile u t (idealNorm K I / N) * maskValue d u I.val‖ ≤
      plainAbsoluteConstant K B * N := by
    calc
      _ ≤ ∑ I ∈ W.support u t N,
          ‖heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u) I *
            W.profile u t (idealNorm K I / N) * maskValue d u I.val‖ := norm_sum_le _ _
      _ ≤ ∑ _I ∈ W.support u t N, B := Finset.sum_le_sum (fun I _ => hterm I)
      _ = ((W.support u t N).card : ℝ) * B := by simp
      _ ≤ ((2 * idealCountConstant K) * N) * B :=
        mul_le_mul_of_nonneg_right (idealTest_support_count W u t N hN hann) hB
      _ = _ := by unfold plainAbsoluteConstant; ring
  unfold plainPolynomial
  rw [norm_mul, norm_inv, Complex.norm_of_nonneg (Real.sqrt_nonneg N), inv_mul_eq_div]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hN)).2
  calc
    _ ≤ plainAbsoluteConstant K B * N := hsum
    _ = (plainAbsoluteConstant K B * Real.sqrt N) * Real.sqrt N := by
      calc
        _ = plainAbsoluteConstant K B * (Real.sqrt N * Real.sqrt N) :=
          congrArg (fun x => plainAbsoluteConstant K B * x) (Real.mul_self_sqrt hN.le).symm
        _ = _ := by ring

theorem plainRectangle_absolute_bound (d : MomentData K ω ψ) (u : NonzeroIdeal K)
    (U t a b B₁ B₂ : ℝ) (hU : 0 < U) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hann₁ : Function.support (d.plainTest₁.profile u t) ⊆ Set.Iic (2 : ℝ))
    (hann₂ : Function.support (d.plainTest₂.profile u t) ⊆ Set.Iic (2 : ℝ))
    (hprof₁ : ∀ y, ‖d.plainTest₁.profile u t y‖ ≤ B₁)
    (hprof₂ : ∀ y, ‖d.plainTest₂.profile u t y‖ ≤ B₂) :
    ‖plainPolynomial d d.plainTest₁ u (U ^ a) t *
        plainPolynomial d d.plainTest₂ u (U ^ b) t‖ ≤
      (plainAbsoluteConstant K B₁ * plainAbsoluteConstant K B₂) *
        Real.sqrt (U ^ (a + b)) := by
  rw [norm_mul]
  calc
    _ ≤ (plainAbsoluteConstant K B₁ * Real.sqrt (U ^ a)) *
        (plainAbsoluteConstant K B₂ * Real.sqrt (U ^ b)) :=
      mul_le_mul
        (plainPolynomial_absolute_bound d d.plainTest₁ u (U ^ a) t B₁
          (Real.rpow_pos_of_pos hU _) hB₁ hann₁ hprof₁)
        (plainPolynomial_absolute_bound d d.plainTest₂ u (U ^ b) t B₂
          (Real.rpow_pos_of_pos hU _) hB₂ hann₂ hprof₂)
        (norm_nonneg _)
        (mul_nonneg (plainAbsoluteConstant_nonneg (K := K) B₁ hB₁) (Real.sqrt_nonneg _))
    _ = _ := by
      rw [Real.rpow_add hU a b, Real.sqrt_mul (Real.rpow_pos_of_pos hU a).le]
      ring

/-- The whole centered difference costs one factor two in amplitude.
The second rectangle uses the same product before taking absolute values. -/
theorem Node.plainPair_sq_absolute_bound (n : Node K ω ψ) (u : NonzeroIdeal K)
    (U t B₁ B₂ : ℝ) (hU : 0 < U) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hann₁ : Function.support (n.data.plainTest₁.profile u t) ⊆ Set.Iic (2 : ℝ))
    (hann₂ : Function.support (n.data.plainTest₂.profile u t) ⊆ Set.Iic (2 : ℝ))
    (hprof₁ : ∀ y, ‖n.data.plainTest₁.profile u t y‖ ≤ B₁)
    (hprof₂ : ∀ y, ‖n.data.plainTest₂.profile u t y‖ ≤ B₂) :
    ‖n.plainPair u U t‖ ^ 2 ≤
      (2 * plainAbsoluteConstant K B₁ * plainAbsoluteConstant K B₂) ^ 2 *
        U ^ (n.parameters.n₁ + n.parameters.n₂) := by
  let B := (plainAbsoluteConstant K B₁ * plainAbsoluteConstant K B₂) *
    Real.sqrt (U ^ (n.parameters.n₁ + n.parameters.n₂))
  have hB : 0 ≤ B := mul_nonneg
    (mul_nonneg (plainAbsoluteConstant_nonneg (K := K) B₁ hB₁)
      (plainAbsoluteConstant_nonneg (K := K) B₂ hB₂))
    (Real.sqrt_nonneg _)
  have hmain : ‖plainPolynomial n.data n.data.plainTest₁ u (U ^ n.parameters.n₁) t *
      plainPolynomial n.data n.data.plainTest₂ u (U ^ n.parameters.n₂) t‖ ≤ B :=
    plainRectangle_absolute_bound n.data u U t _ _ B₁ B₂ hU hB₁ hB₂
      hann₁ hann₂ hprof₁ hprof₂
  have hcomp : ‖plainPolynomial n.data n.data.plainTest₁ u (U ^ n.comparison₁) t *
      plainPolynomial n.data n.data.plainTest₂ u (U ^ n.comparison₂) t‖ ≤ B := by
    simpa only [n.comparison_sum] using plainRectangle_absolute_bound n.data u U t
      n.comparison₁ n.comparison₂ B₁ B₂ hU hB₁ hB₂ hann₁ hann₂ hprof₁ hprof₂
  have hpair : ‖n.plainPair u U t‖ ≤ 2 * B := by
    unfold Node.plainPair
    calc
      _ ≤ ‖plainPolynomial n.data n.data.plainTest₁ u (U ^ n.parameters.n₁) t *
          plainPolynomial n.data n.data.plainTest₂ u (U ^ n.parameters.n₂) t‖ +
          ‖if n.centered then
            plainPolynomial n.data n.data.plainTest₁ u (U ^ n.comparison₁) t *
              plainPolynomial n.data n.data.plainTest₂ u (U ^ n.comparison₂) t else 0‖ :=
        norm_sub_le _ _
      _ ≤ B + B := by
        apply add_le_add hmain
        split_ifs
        · exact hcomp
        · simpa using hB
      _ = 2 * B := by ring
  calc
    _ ≤ (2 * B) ^ 2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hpair
    _ = _ := by
      dsimp only [B]
      simp only [mul_pow, Real.sq_sqrt (Real.rpow_pos_of_pos hU _).le]
      ring

def nodeAbsoluteConstant (K : Type) [Field K] [NumberField K] (B₁ B₂ A : ℝ) : ℝ :=
  idealCountConstant K *
    (2 * plainAbsoluteConstant K B₁ * plainAbsoluteConstant K B₂) ^ 2 * A

theorem nodeAbsoluteConstant_nonneg (B₁ B₂ A : ℝ) (hA : 0 ≤ A) :
    0 ≤ nodeAbsoluteConstant K B₁ B₂ A := by
  have hc := one_le_idealCountConstant K
  unfold nodeAbsoluteConstant
  positivity

/-- A local prime-product estimate is used only at its stated exponent.
In the absolute specialization below that exponent is `totalLength`. -/
theorem Node.normalizedEnergy_absolute_bound (n : Node K ω ψ)
    (U t B₁ B₂ A slotExponent : ℝ) (hU : 0 < U)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hA : 0 ≤ A)
    (hann₁ : ∀ u ∈ pairedRows n.data n.parameters U,
      Function.support (n.data.plainTest₁.profile u t) ⊆ Set.Iic (2 : ℝ))
    (hann₂ : ∀ u ∈ pairedRows n.data n.parameters U,
      Function.support (n.data.plainTest₂.profile u t) ⊆ Set.Iic (2 : ℝ))
    (hprof₁ : ∀ u ∈ pairedRows n.data n.parameters U, ∀ y,
      ‖n.data.plainTest₁.profile u t y‖ ≤ B₁)
    (hprof₂ : ∀ u ∈ pairedRows n.data n.parameters U, ∀ y,
      ‖n.data.plainTest₂.profile u t y‖ ≤ B₂)
    (hslots : ∀ u ∈ pairedRows n.data n.parameters U,
      ‖slotProduct n.data u U t‖ ^ 2 ≤ A * U ^ slotExponent) :
    n.normalizedEnergy U t ≤ nodeAbsoluteConstant K B₁ B₂ A *
      U ^ (n.parameters.n₁ + n.parameters.n₂ + slotExponent) := by
  let Q := (2 * plainAbsoluteConstant K B₁ * plainAbsoluteConstant K B₂) ^ 2
  have hQ : 0 ≤ Q := sq_nonneg _
  have hterm (u : NonzeroIdeal K) (hu : u ∈ pairedRows n.data n.parameters U) :
      ‖n.plainPair u U t * slotProduct n.data u U t‖ ^ 2 ≤
        Q * A * U ^ (n.parameters.n₁ + n.parameters.n₂ + slotExponent) := by
    rw [norm_mul, mul_pow]
    calc
      _ ≤ (Q * U ^ (n.parameters.n₁ + n.parameters.n₂)) * (A * U ^ slotExponent) :=
        mul_le_mul (n.plainPair_sq_absolute_bound u U t B₁ B₂ hU hB₁ hB₂
          (hann₁ u hu) (hann₂ u hu) (hprof₁ u hu) (hprof₂ u hu))
          (hslots u hu) (sq_nonneg _) (mul_nonneg hQ (Real.rpow_pos_of_pos hU _).le)
      _ = _ := by
        rw [Real.rpow_add hU (n.parameters.n₁ + n.parameters.n₂) slotExponent]
        ring
  have hrows := finite_ideal_rows_count (pairedRows n.data n.parameters U)
    (U ^ n.width) (Real.rpow_pos_of_pos hU _).le (by
      intro u hu
      exact ((n.data.rows_spec _ u).1 (Finset.mem_filter.mp hu).1).2)
  have henergy : n.energy U t ≤ (idealCountConstant K * U ^ n.width) *
      (Q * A * U ^ (n.parameters.n₁ + n.parameters.n₂ + slotExponent)) := by
    calc
      _ ≤ ∑ _u ∈ pairedRows n.data n.parameters U,
          Q * A * U ^ (n.parameters.n₁ + n.parameters.n₂ + slotExponent) :=
        Finset.sum_le_sum hterm
      _ = ((pairedRows n.data n.parameters U).card : ℝ) *
          (Q * A * U ^ (n.parameters.n₁ + n.parameters.n₂ + slotExponent)) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hrows (by positivity)
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hU n.width)).2
  apply henergy.trans_eq
  unfold nodeAbsoluteConstant
  dsimp only [Q]
  ring

/-- A real base certificate from profile bounds and a lower-level slot
estimate.  Its only mass hypothesis concerns the explicit product of
profile constants and the field's ideal-count constant. -/
def Node.absoluteBaseComponents (n : Node K ω ψ)
    (U t T B₁ B₂ A slotExponent C H ρ padding σ boundary : ℝ)
    (hU : 0 < U) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hA : 0 ≤ A)
    (hann₁ : ∀ u ∈ pairedRows n.data n.parameters U,
      Function.support (n.data.plainTest₁.profile u t) ⊆ Set.Iic (2 : ℝ))
    (hann₂ : ∀ u ∈ pairedRows n.data n.parameters U,
      Function.support (n.data.plainTest₂.profile u t) ⊆ Set.Iic (2 : ℝ))
    (hprof₁ : ∀ u ∈ pairedRows n.data n.parameters U, ∀ y,
      ‖n.data.plainTest₁.profile u t y‖ ≤ B₁)
    (hprof₂ : ∀ u ∈ pairedRows n.data n.parameters U, ∀ y,
      ‖n.data.plainTest₂.profile u t y‖ ≤ B₂)
    (hslots : ∀ u ∈ pairedRows n.data n.parameters U,
      ‖slotProduct n.data u U t‖ ^ 2 ≤ A * U ^ slotExponent)
    (hbase : n.parameters.n₁ + n.parameters.n₂ + slotExponent ≤ ρ + padding + ρ / 6)
    (hmass : nodeAbsoluteConstant K B₁ B₂ A ≤ C * (1 + T) ^ H) :
    TerminalComponents.{v} (n.normalizedEnergy U t) U T C H ρ padding σ boundary where
  Label := ULift.{v} Unit
  terms := {⟨()⟩}
  coefficient _ := nodeAbsoluteConstant K B₁ B₂ A
  exponent _ := n.parameters.n₁ + n.parameters.n₂ + slotExponent
  coefficient_nonneg _ _ := nodeAbsoluteConstant_nonneg (K := K) B₁ B₂ A hA
  estimate := by
    simpa using n.normalizedEnergy_absolute_bound U t B₁ B₂ A slotExponent
      hU hB₁ hB₂ hA hann₁ hann₂ hprof₁ hprof₂ hslots
  mass := by simpa using hmass
  ledger _ _ := .base hbase

/-- Fixed actual annular profiles furnish the entire absolute base
certificate.  The constant precedes every later real scale and height. -/
theorem Node.exists_absolute_base_components (n : Node K ω ψ)
    (B₁ B₂ ρ padding σ boundary : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hann₁ : ∀ u t, Function.support (n.data.plainTest₁.profile u t) ⊆ Set.Iic (2 : ℝ))
    (hann₂ : ∀ u t, Function.support (n.data.plainTest₂.profile u t) ⊆ Set.Iic (2 : ℝ))
    (hprof₁ : ∀ u t y, ‖n.data.plainTest₁.profile u t y‖ ≤ B₁)
    (hprof₂ : ∀ u t y, ‖n.data.plainTest₂.profile u t y‖ ≤ B₂)
    (Bslots : Fin n.data.geometry.slotCount → ℝ) (hBslots : ∀ i, 0 ≤ Bslots i)
    (hannSlots : ∀ i t, Function.support ((n.data.geometry.slots i).profile t) ⊆
      Set.Ioo (1 : ℝ) 2)
    (hprofSlots : ∀ i t y, ‖(n.data.geometry.slots i).profile t y‖ ≤ Bslots i)
    (hbase : n.parameters.n₁ + n.parameters.n₂ + n.data.geometry.totalLength ≤
      ρ + padding + ρ / 6) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U T t : ℝ, 1 ≤ U →
      Nonempty (TerminalComponents.{v} (n.normalizedEnergy U t) U T C 0 ρ padding σ boundary) := by
  obtain ⟨A, hA, hslots⟩ := HeckeGeneral.ThetaSkeleton.Physical.slotProduct_sq_absolute_bound
    K n.data Bslots hBslots hannSlots hprofSlots
  refine ⟨nodeAbsoluteConstant K B₁ B₂ A,
    nodeAbsoluteConstant_nonneg (K := K) B₁ B₂ A hA, ?_⟩
  intro U T t hU
  exact ⟨n.absoluteBaseComponents U t T B₁ B₂ A n.data.geometry.totalLength
    (nodeAbsoluteConstant K B₁ B₂ A) 0 ρ padding σ boundary
    (zero_lt_one.trans_le hU) hB₁ hB₂ hA
    (fun u _ => hann₁ u t) (fun u _ => hann₂ u t)
    (fun u _ => hprof₁ u t) (fun u _ => hprof₂ u t)
    (fun u _ => hslots u U t hU) hbase (by simp)⟩

/-- Only the reflected padded core is used for zero slots; unrestricted
zero-slot lengths must first be reflected by the actual source producer. -/
theorem Node.zero_slot_base_exponent (n : Node K ω ψ) (ρ padding : ℝ)
    (hρ : 0 ≤ ρ) (hwidth : n.width ≤ ρ)
    (hslots : n.data.geometry.totalLength = 0)
    (hcore : n.parameters.n₁ + n.parameters.n₂ ≤ n.width + padding) :
    n.parameters.n₁ + n.parameters.n₂ + n.data.geometry.totalLength ≤ ρ + padding + ρ / 6 := by
  rw [hslots]
  linarith

/-- The absolute slot exponent is `z`.  The full positive capacity, rather
than an illicit substitution of `κ*z` for `z`, controls that cost. -/
theorem Node.positive_slot_base_exponent (n : Node K ω ψ) (ρ padding : ℝ)
    (hρ : 0 ≤ ρ) (hpadding : 0 ≤ padding) (hwidth : n.width ≤ ρ)
    (hslots : n.data.geometry.totalLength = n.parameters.z)
    (hz : 0 ≤ n.parameters.z) (hκ : 3 / 4 ≤ n.parameters.κ)
    (hcapacity : n.parameters.n₁ + n.parameters.n₂ +
      6 * n.parameters.κ * n.parameters.z ≤ n.width) :
    n.parameters.n₁ + n.parameters.n₂ + n.data.geometry.totalLength ≤ ρ + padding + ρ / 6 := by
  rw [hslots]
  have h := positive_capacity_total_length hz hκ hcapacity
  linarith

end HeckeSkeleton.Moments.EngineInduction
