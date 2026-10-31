import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.BaseUniformity

/-!
# Actual base certificates for a fixed general support upper bound

The source profile control supplies a common interval with upper endpoint
`b > 0`; it need not be the interval `(1,2)`. Only its upper endpoint is
used for absolute counting. All original profiles, rows, masks and slot
lengths are retained, including positive polynomial scales below one.

The established constants and height-growth theorem from `BaseUniformity`
are reused after fixed rescaling of their three numerical suprema. The
support endpoint is fixed before height, scale, characters and nodes.
The scale exponent of the actual slot product is still `totalLength`.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.CenteredMomentCounting
open HeckeGeneral.Analysis.SquarefreeAmplification
open scoped BigOperators Classical

universe v

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- Express the general prime-count coefficient using the already fixed
prime-envelope constant. This is independent of every moving parameter. -/
def supportProfileScale (K : Type) [Field K] [NumberField K] (b : ℝ) : ℝ :=
  idealCountConstant K * b / primeAbsoluteCountConstant K

def generalBaseConstant (K : Type) [Field K] [NumberField K] (cap : ℕ)
    (b B₁ B₂ Bslots : ℝ) : ℝ :=
  uniformBaseConstant K cap ((b / 2) * B₁) ((b / 2) * B₂)
    (supportProfileScale K b * Bslots)

/-- Count the exact ideal support at every positive scale. In particular,
scales below one are not discarded unless their norm cutoff is below one. -/
theorem idealTest_support_count_of_upper (W : IdealTest K)
    (u : NonzeroIdeal K) (t N b : ℝ) (hN : 0 < N) (hb : 0 ≤ b)
    (hann : Function.support (W.profile u t) ⊆ Set.Iic b) :
    ((W.support u t N).card : ℝ) ≤ (idealCountConstant K * b) * N := by
  have h := finite_ideal_rows_count (W.support u t N) (b * N) (mul_nonneg hb hN.le) (by
    intro I hI
    exact (div_le_iff₀ hN).1 (hann ((W.support_spec u t N I).1 hI)))
  simpa only [mul_assoc] using h

private theorem mask_norm_le_one (d : MomentData K ω ψ) (u : NonzeroIdeal K)
    (I : Ideal (𝓞 K)) : ‖maskValue d u I‖ ≤ 1 := by
  unfold maskValue
  split_ifs <;> simp

private theorem norm_term_le {c w m : ℂ} {B : ℝ}
    (hc : ‖c‖ ≤ 1) (hw : ‖w‖ ≤ B) (hm : ‖m‖ ≤ 1) (hB : 0 ≤ B) :
    ‖c * w * m‖ ≤ B := by
  simp only [norm_mul]
  have h := mul_le_mul (mul_le_mul hc hw (norm_nonneg _) zero_le_one)
    hm (norm_nonneg _) (by simpa only [one_mul] using hB)
  simpa only [one_mul, mul_one] using h

private theorem normalized_finite_sum_bound {ι : Type*} (rows : Finset ι)
    (f : ι → ℂ) (N D B : ℝ) (hN : 0 < N) (hB : 0 ≤ B)
    (hcard : (rows.card : ℝ) ≤ D * N) (hterm : ∀ i ∈ rows, ‖f i‖ ≤ B) :
    ‖(Real.sqrt N : ℂ)⁻¹ * ∑ i ∈ rows, f i‖ ≤ D * B * Real.sqrt N := by
  have hsum : ‖∑ i ∈ rows, f i‖ ≤ D * B * N := by
    calc
      _ ≤ ∑ i ∈ rows, ‖f i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ rows, B := Finset.sum_le_sum hterm
      _ = (rows.card : ℝ) * B := by simp
      _ ≤ (D * N) * B := mul_le_mul_of_nonneg_right hcard hB
      _ = _ := by ring
  rw [norm_mul, norm_inv, Complex.norm_of_nonneg (Real.sqrt_nonneg N), inv_mul_eq_div]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hN)).2
  apply hsum.trans_eq
  calc
    D * B * N = (D * B) * (Real.sqrt N * Real.sqrt N) :=
      congrArg (fun x => D * B * x) (Real.mul_self_sqrt hN.le).symm
    _ = _ := by ring

/-- The fixed endpoint `b` changes only the coefficient, not `sqrt N`.
The coefficient is written in the old convention to reuse its height law. -/
theorem plainPolynomial_absolute_bound_of_upper (d : MomentData K ω ψ)
    (W : IdealTest K) (u : NonzeroIdeal K) (N t b B : ℝ)
    (hN : 0 < N) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hann : Function.support (W.profile u t) ⊆ Set.Iic b)
    (hprof : ∀ y, ‖W.profile u t y‖ ≤ B) :
    ‖plainPolynomial d W u N t‖ ≤
      plainAbsoluteConstant K ((b / 2) * B) * Real.sqrt N := by
  have h := normalized_finite_sum_bound (W.support u t N)
    (fun I => heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u) I *
      W.profile u t (idealNorm K I / N) * maskValue d u I.val)
    N (idealCountConstant K * b) B hN hB
    (idealTest_support_count_of_upper W u t N b hN hb hann)
    (fun I _ => norm_term_le (norm_heckeIdealCoefficient_le_one K _ I)
      (hprof _) (mask_norm_le_one d u I.val) hB)
  apply h.trans_eq
  unfold plainAbsoluteConstant
  ring

/-- Actual prime counting requires only the common support upper bound.
There is no lower-annulus or prime-cancellation hypothesis. -/
theorem primePolynomial_absolute_bound_of_upper (d : MomentData K ω ψ)
    (i : Fin d.geometry.slotCount) (u : NonzeroIdeal K) (U t b B : ℝ)
    (hU : 0 < U) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hann : Function.support ((d.geometry.slots i).profile t) ⊆ Set.Iic b)
    (hprof : ∀ y, ‖(d.geometry.slots i).profile t y‖ ≤ B) :
    ‖primePolynomial d i u U t‖ ≤
      (primeAbsoluteCountConstant K * (supportProfileScale K b * B)) *
        Real.sqrt (U ^ (d.geometry.slots i).length) := by
  let P := U ^ (d.geometry.slots i).length
  let rows := (d.geometry.slots i).support t P
  have hP : 0 < P := Real.rpow_pos_of_pos hU _
  have hc := finite_ideal_rows_count (rows.image (primeNonzeroIdeal K)) (b * P)
    (mul_nonneg hb hP.le) (by
      intro I hI
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hI
      exact (div_le_iff₀ hP).1 (hann (((d.geometry.slots i).support_spec t P p).1 hp)))
  have hcard : (rows.card : ℝ) ≤ (idealCountConstant K * b) * P := by
    simpa only [Finset.card_image_of_injective rows (primeNonzeroIdeal_injective K),
      mul_assoc] using hc
  have h := normalized_finite_sum_bound rows
    (fun p => primeCoefficient K (d.rowCharacter u * d.slotCoefficient i) p *
      (d.geometry.slots i).profile t ((p.asIdeal.absNorm : ℝ) / P) * maskValue d u p.asIdeal)
    P (idealCountConstant K * b) B hP hB hcard
    (fun p _ => norm_term_le (norm_primeCoefficient_le_one K _ p)
      (hprof _) (mask_norm_le_one d u p.asIdeal) hB)
  apply h.trans_eq
  unfold supportProfileScale
  field_simp [(primeAbsoluteCountConstant_pos (K := K)).ne'] <;> ring

/-- One common coefficient covers all actual slot products below a fixed
slot-count cap, for the same unrestricted support upper endpoint. -/
theorem slotProduct_sq_uniform_bound_of_upper (cap : ℕ) (b B : ℝ)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (d : MomentData K ω ψ)
    (hcount : d.geometry.slotCount ≤ cap) (u : NonzeroIdeal K) (U t : ℝ) (hU : 0 < U)
    (hann : ∀ i, Function.support ((d.geometry.slots i).profile t) ⊆ Set.Iic b)
    (hprof : ∀ i y, ‖(d.geometry.slots i).profile t y‖ ≤ B) :
    ‖slotProduct d u U t‖ ^ 2 ≤
      uniformSlotAbsoluteConstant K cap (supportProfileScale K b * B) *
        U ^ d.geometry.totalLength := by
  let D := max 1 (primeAbsoluteCountConstant K * (supportProfileScale K b * B))
  have hD : 1 ≤ D := le_max_left _ _
  have hi (i : Fin d.geometry.slotCount) :
      ‖primePolynomial d i u U t‖ ^ 2 ≤ D ^ 2 * U ^ (d.geometry.slots i).length := by
    have hp : ‖primePolynomial d i u U t‖ ≤
        D * Real.sqrt (U ^ (d.geometry.slots i).length) :=
      (primePolynomial_absolute_bound_of_upper d i u U t b B hU hb hB
      (hann i) (hprof i)).trans
      (mul_le_mul_of_nonneg_right
        (le_max_right 1 (primeAbsoluteCountConstant K * (supportProfileScale K b * B)))
        (Real.sqrt_nonneg _))
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity :
      0 ≤ D * Real.sqrt (U ^ (d.geometry.slots i).length))).2 hp
    simpa only [mul_pow, Real.sq_sqrt (Real.rpow_nonneg hU.le _)] using hs
  calc
    _ = ∏ i, ‖primePolynomial d i u U t‖ ^ 2 := by
      rw [slotProduct, norm_prod, Finset.prod_pow]
    _ ≤ ∏ i, D ^ 2 * U ^ (d.geometry.slots i).length :=
      Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _) (fun i _ => hi i)
    _ = D ^ (2 * d.geometry.slotCount) * U ^ d.geometry.totalLength := by
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hU]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul,
        SlotGeometry.totalLength]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hD (Nat.mul_le_mul_left 2 hcount)) (Real.rpow_nonneg hU.le _)

private theorem plain_pair_bound_from_polynomials (n : Node K ω ψ)
    (u : NonzeroIdeal K) (U t P₁ P₂ : ℝ) (hU : 0 < U) (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂)
    (h₁ : ∀ N, 0 < N → ‖plainPolynomial n.data n.data.plainTest₁ u N t‖ ≤ P₁ * Real.sqrt N)
    (h₂ : ∀ N, 0 < N → ‖plainPolynomial n.data n.data.plainTest₂ u N t‖ ≤ P₂ * Real.sqrt N) :
    ‖n.plainPair u U t‖ ^ 2 ≤
      (2 * P₁ * P₂) ^ 2 * U ^ (n.parameters.n₁ + n.parameters.n₂) := by
  have hr (a c : ℝ) :
      ‖plainPolynomial n.data n.data.plainTest₁ u (U ^ a) t *
        plainPolynomial n.data n.data.plainTest₂ u (U ^ c) t‖ ≤
        (P₁ * P₂) * Real.sqrt (U ^ (a + c)) := by
    rw [norm_mul]
    apply (mul_le_mul (h₁ _ (Real.rpow_pos_of_pos hU _))
      (h₂ _ (Real.rpow_pos_of_pos hU _)) (norm_nonneg _)
      (mul_nonneg hP₁ (Real.sqrt_nonneg _))).trans_eq
    rw [Real.rpow_add hU a c, Real.sqrt_mul (Real.rpow_pos_of_pos hU a).le]
    ring
  let R := (P₁ * P₂) * Real.sqrt (U ^ (n.parameters.n₁ + n.parameters.n₂))
  have hR : 0 ≤ R := mul_nonneg (mul_nonneg hP₁ hP₂) (Real.sqrt_nonneg _)
  have hc : ‖plainPolynomial n.data n.data.plainTest₁ u (U ^ n.comparison₁) t *
      plainPolynomial n.data n.data.plainTest₂ u (U ^ n.comparison₂) t‖ ≤ R := by
    simpa only [n.comparison_sum] using hr n.comparison₁ n.comparison₂
  have hp : ‖n.plainPair u U t‖ ≤ 2 * R := by
    unfold Node.plainPair
    apply (norm_sub_le _ _).trans
    calc
      _ ≤ R + R := by
        apply add_le_add (hr n.parameters.n₁ n.parameters.n₂)
        split_ifs
        · exact hc
        · simpa using hR
      _ = _ := by ring
  apply ((sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hp).trans_eq
  dsimp only [R]
  simp only [mul_pow, Real.sq_sqrt (Real.rpow_pos_of_pos hU _).le]
  ring

private theorem normalized_energy_from_row_bound (n : Node K ω ψ) (U t Q e : ℝ)
    (hU : 0 < U) (hQ : 0 ≤ Q)
    (hrow : ∀ u ∈ pairedRows n.data n.parameters U,
      ‖n.plainPair u U t * slotProduct n.data u U t‖ ^ 2 ≤ Q * U ^ e) :
    n.normalizedEnergy U t ≤ idealCountConstant K * Q * U ^ e := by
  have hc := finite_ideal_rows_count (pairedRows n.data n.parameters U)
    (U ^ n.width) (Real.rpow_pos_of_pos hU _).le (by
      intro u hu
      exact ((n.data.rows_spec _ u).1 (Finset.mem_filter.mp hu).1).2)
  have he : n.energy U t ≤ (idealCountConstant K * U ^ n.width) * (Q * U ^ e) := by
    calc
      _ ≤ ∑ _u ∈ pairedRows n.data n.parameters U, Q * U ^ e := Finset.sum_le_sum hrow
      _ = ((pairedRows n.data n.parameters U).card : ℝ) * (Q * U ^ e) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
  unfold Node.normalizedEnergy
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hU n.width)).2
  exact he.trans_eq (by ring)

/-- The genuine normalized base energy for support bounded by arbitrary
fixed `b`; every arithmetic field and both original rectangles are used. -/
theorem Node.normalizedEnergy_absolute_bound_of_upper (n : Node K ω ψ)
    (cap : ℕ) (U t b B₁ B₂ Bslots : ℝ) (hU : 0 < U) (hb : 0 ≤ b)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hBslots : 0 ≤ Bslots)
    (hcount : n.data.geometry.slotCount ≤ cap)
    (hann₁ : ∀ u ∈ pairedRows n.data n.parameters U,
      Function.support (n.data.plainTest₁.profile u t) ⊆ Set.Iic b)
    (hann₂ : ∀ u ∈ pairedRows n.data n.parameters U,
      Function.support (n.data.plainTest₂.profile u t) ⊆ Set.Iic b)
    (hprof₁ : ∀ u ∈ pairedRows n.data n.parameters U, ∀ y,
      ‖n.data.plainTest₁.profile u t y‖ ≤ B₁)
    (hprof₂ : ∀ u ∈ pairedRows n.data n.parameters U, ∀ y,
      ‖n.data.plainTest₂.profile u t y‖ ≤ B₂)
    (hannSlots : ∀ i, Function.support ((n.data.geometry.slots i).profile t) ⊆ Set.Iic b)
    (hprofSlots : ∀ i y, ‖(n.data.geometry.slots i).profile t y‖ ≤ Bslots) :
    n.normalizedEnergy U t ≤ generalBaseConstant K cap b B₁ B₂ Bslots *
      U ^ (n.parameters.n₁ + n.parameters.n₂ + n.data.geometry.totalLength) := by
  let Q := (2 * plainAbsoluteConstant K ((b / 2) * B₁) *
    plainAbsoluteConstant K ((b / 2) * B₂)) ^ 2
  let A := uniformSlotAbsoluteConstant K cap (supportProfileScale K b * Bslots)
  have hA : 0 ≤ A := uniformSlotAbsoluteConstant_nonneg (K := K) _ _
  have h := normalized_energy_from_row_bound n U t (Q * A)
    (n.parameters.n₁ + n.parameters.n₂ + n.data.geometry.totalLength)
    hU (mul_nonneg (sq_nonneg _) hA) (by
      intro u hu
      have hp := plain_pair_bound_from_polynomials n u U t
        (plainAbsoluteConstant K ((b / 2) * B₁))
        (plainAbsoluteConstant K ((b / 2) * B₂)) hU
        (plainAbsoluteConstant_nonneg (K := K) _ (by positivity))
        (plainAbsoluteConstant_nonneg (K := K) _ (by positivity))
        (fun N hN => plainPolynomial_absolute_bound_of_upper n.data n.data.plainTest₁ u
          N t b B₁ hN hb hB₁ (hann₁ u hu) (hprof₁ u hu))
        (fun N hN => plainPolynomial_absolute_bound_of_upper n.data n.data.plainTest₂ u
          N t b B₂ hN hb hB₂ (hann₂ u hu) (hprof₂ u hu))
      have hs := slotProduct_sq_uniform_bound_of_upper cap b Bslots hb hBslots
        n.data hcount u U t hU hannSlots hprofSlots
      rw [norm_mul, mul_pow]
      apply (mul_le_mul hp hs (sq_nonneg _)
        (mul_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos hU _).le)).trans_eq
      rw [Real.rpow_add hU (n.parameters.n₁ + n.parameters.n₂) n.data.geometry.totalLength]
      dsimp only [Q, A]
      ring)
  apply h.trans_eq
  unfold generalBaseConstant uniformBaseConstant nodeAbsoluteConstant
  dsimp only [Q, A]
  ring

/-- Reuse the established polynomial-height law, with `b` fixed in the
three numerical profile constants before the moving height is chosen. -/
theorem generalBaseConstant_height_le (cap : ℕ) (b B₁ B₂ Bslots X H₁ H₂ Hslots : ℝ)
    (hX : 1 ≤ X) (hHslots : 0 ≤ Hslots) :
    generalBaseConstant K cap b (B₁ * X ^ H₁) (B₂ * X ^ H₂) (Bslots * X ^ Hslots) ≤
      generalBaseConstant K cap b B₁ B₂ Bslots * X ^ baseHeightDegree cap H₁ H₂ Hslots := by
  simpa only [generalBaseConstant, mul_assoc] using
    uniformBaseConstant_height_le (K := K) cap ((b / 2) * B₁) ((b / 2) * B₂)
      (supportProfileScale K b * Bslots) X H₁ H₂ Hslots hX hHslots

/-- Common absolute-base certificates for a source's genuine fixed upper
endpoint. Both coefficient and height degree precede `T`, every node,
all characters, all scales and the current profile time. -/
theorem general_uniform_polynomial_height_base_components (cap : ℕ)
    (b B₁ B₂ Bslots H₁ H₂ Hslots ρ padding σ boundary : ℝ)
    (hb : 0 < b) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hBslots : 0 ≤ Bslots)
    (hH₁ : 0 ≤ H₁) (hH₂ : 0 ≤ H₂) (hHslots : 0 ≤ Hslots) :
    ∃ C H : ℝ, C = generalBaseConstant K cap b B₁ B₂ Bslots ∧
      H = baseHeightDegree cap H₁ H₂ Hslots ∧ 0 ≤ C ∧ 0 ≤ H ∧
      ∀ T : ℝ, 0 ≤ T → ∀ {ω ψ : HeckeCharacter K} (n : Node K ω ψ)
        (U t : ℝ), 1 ≤ U → n.data.geometry.slotCount ≤ cap →
        (∀ u ∈ pairedRows n.data n.parameters U,
          Function.support (n.data.plainTest₁.profile u t) ⊆ Set.Iic b) →
        (∀ u ∈ pairedRows n.data n.parameters U,
          Function.support (n.data.plainTest₂.profile u t) ⊆ Set.Iic b) →
        (∀ u ∈ pairedRows n.data n.parameters U, ∀ y,
          ‖n.data.plainTest₁.profile u t y‖ ≤ B₁ * (1 + T) ^ H₁) →
        (∀ u ∈ pairedRows n.data n.parameters U, ∀ y,
          ‖n.data.plainTest₂.profile u t y‖ ≤ B₂ * (1 + T) ^ H₂) →
        (∀ i, Function.support ((n.data.geometry.slots i).profile t) ⊆ Set.Iic b) →
        (∀ i y, ‖(n.data.geometry.slots i).profile t y‖ ≤ Bslots * (1 + T) ^ Hslots) →
        n.parameters.n₁ + n.parameters.n₂ + n.data.geometry.totalLength ≤ ρ + padding + ρ / 6 →
        Nonempty (TerminalComponents.{v} (n.normalizedEnergy U t) U T C H
          ρ padding σ boundary) := by
  refine ⟨generalBaseConstant K cap b B₁ B₂ Bslots, baseHeightDegree cap H₁ H₂ Hslots,
    rfl, rfl, uniformBaseConstant_nonneg (K := K) cap _ _ _,
    baseHeightDegree_nonneg cap hH₁ hH₂ hHslots, ?_⟩
  intro T hT ω ψ n U t hU hcount hann₁ hann₂ hprof₁ hprof₂ hannSlots hprofSlots hbase
  have hheight : 1 ≤ 1 + T := by linarith
  have hb₁ : 0 ≤ B₁ * (1 + T) ^ H₁ := by positivity
  have hb₂ : 0 ≤ B₂ * (1 + T) ^ H₂ := by positivity
  have hbs : 0 ≤ Bslots * (1 + T) ^ Hslots := by positivity
  let D := generalBaseConstant K cap b
    (B₁ * (1 + T) ^ H₁) (B₂ * (1 + T) ^ H₂) (Bslots * (1 + T) ^ Hslots)
  refine ⟨{
    Label := ULift.{v} Unit
    terms := {⟨()⟩}
    coefficient := fun _ => D
    exponent := fun _ => n.parameters.n₁ + n.parameters.n₂ + n.data.geometry.totalLength
    coefficient_nonneg := fun _ _ => uniformBaseConstant_nonneg (K := K) cap _ _ _
    estimate := ?_
    mass := ?_
    ledger := fun _ _ => .base hbase }⟩
  · simpa only [Finset.sum_singleton] using
      n.normalizedEnergy_absolute_bound_of_upper cap U t b _ _ _
        (zero_lt_one.trans_le hU) hb.le hb₁ hb₂ hbs hcount
        hann₁ hann₂ hprof₁ hprof₂ hannSlots hprofSlots
  · simpa only [Finset.sum_singleton] using
      generalBaseConstant_height_le (K := K) cap b B₁ B₂ Bslots (1 + T)
        H₁ H₂ Hslots hheight hHslots

end HeckeSkeleton.Moments.EngineInduction
