import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalPrimitiveBounds

/-!
# Uniform exceptional row estimates from the original volume primitive

The actual residual row count and exponent ledger are unchanged.  This
version selects its orders and constant before both original profiles,
and keeps their fourfold seminorm factor explicit.  It internally
constructs the single-source bounds from the raw fixed-character ideal
series, with one centered saving for the literal left source and the
absolute bound for the literal right source.

The arithmetic hypotheses here describe original valuations and raw
frozen/slot masses; they are filled by the separate literal character,
classification and atom factories before the complete engine theorem.
There is no polynomial estimate or aggregate exceptional budget premise.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalRows

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.Moments.Twist HeckePort.CenteredMomentVolume
open HeckePort.CenteredMomentCounting UniqueFactorizationMonoid

set_option maxHeartbeats 4000000

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

private theorem positive_part_after_extraction (L r : ℝ) (hr : 0 ≤ r) :
    max (L - r) 0 = max (max L 0 - r) 0 := by
  rcases le_total 0 L with hL | hL
  · rw [max_eq_left hL]
  · have hLr : L - r ≤ 0 := by linarith
    have h0r : 0 - r ≤ 0 := by linarith
    simp only [max_eq_right hL, max_eq_right hLr, max_eq_right h0r]

theorem exists_original_paired_row_bound
    {Catalogue : Type*} [Fintype Catalogue]
    (χ : Catalogue → HeckeCharacter F)
    (density : Catalogue → 𝓢(ℝ, ℂ) → ℂ)
    (remainder : Catalogue → Seminorm ℂ (𝓢(ℝ, ℂ)))
    (hcontinuous : ∀ i, Continuous (remainder i))
    (hvolume : ∀ i (φ : 𝓢(ℝ, ℂ)) (X : ℝ), 0 < X →
      ‖(∑' I : Ideal (𝓞 F), CanonicalExceptionalVolume.coefficient (χ i) I *
          φ ((Ideal.absNorm I : ℝ) / X)) - (X : ℂ) * density i φ‖ ≤ remainder i φ)
    (window : Set ℝ) (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (ε maskExponent : ℝ) (hε : 0 < ε) (hmask : 0 ≤ maskExponent) :
    ∃ orders : Finset (ℕ × ℕ), (0, 0) ∈ orders ∧
    ∃ J : ℕ, ∃ Cbound : ℝ, 0 < Cbound ∧
    ∀ (iLeft iRight : Catalogue) (WL₁ WL₂ WR₁ WR₂ : 𝓢(ℝ, ℂ)),
    tsupport WL₁ ⊆ window → tsupport WL₂ ⊆ window →
    tsupport WR₁ ⊆ window → tsupport WR₂ ⊆ window →
    ∀ P : ℝ, 1 ≤ P →
    orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) WL₁ ≤ P →
    orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) WL₂ ≤ P →
    orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) WR₁ ≤ P →
    orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) WR₂ ≤ P →
    ∀ {ι HRows : Type*} [Fintype ι] [DecidableEq ι]
      (C : A.GeneralArithmeticContext σ η hS)
      (p : ι → ExteriorPrime A) (hp : Function.Injective p)
      (mult₁ mult₂ : ι → ℕ)
      (rows : Finset HRows) (Ih : HRows → A.Exterior) (frequency : HRows → A.R)
      (r : ∀ x, ActualExceptionalRow C p mult₁ mult₂ (Ih x) (frequency x))
      (base : Ideal (𝓞 F))
      (leftFactor rightFactor : HRows → A.R)
      (Z Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ v vStar
        r₁ r₂ divisorLower slotError sectors Cnormal height stepσ δ : ℝ),
    1 ≤ Z → 0 ≤ v → 0 ≤ r₁ → divisorLower - r₂ ≤ slotError →
    0 ≤ sectors → 0 ≤ Cnormal → 0 ≤ height →
    let a₀ := Aexp - c - w
    let K₀ := 2 * Aexp - c - d + R₀ + E₀ - m
    let mChild := 2 * a₀ - K - g - g₂ - V₀
    let qChild := q + R₀ + E₀ + wo + t₂ + V₀
    let Δ := b₂ - p₂ + w + Bcommon + ell
    let F₁ := firstSaving c (d + K₀ - K) w (q + R₀ + E₀) wo Bcommon g ell
    let F₂ := 2 * b₂ - 5 * g₂ / 6 - p₂ + t₂ + V₀ / 6 + (2 * v) / 6
    (∀ x ∈ rows, ∀ i ∈ multiplicityOneNonunitPrimes C p mult₁ mult₂ (frequency x),
      6 ∣ (normalizedFactors (Ih x).val).count (p i).val.asIdeal) →
    (∀ x ∈ rows, ∃ a : Ideal (𝓞 F), (r x).ideal.val = base * a ^ 6) →
    (∀ x ∈ rows, Z ^ v ≤
      A.exteriorNorm (multiplicityOneNonunitRadical C p mult₁ mult₂ (frequency x))) →
    (∀ x ∈ rows, A.exteriorNorm (Ih x) ≤
      ((Ideal.absNorm (gcd (primePowerProduct p mult₁).val (primePowerProduct p mult₂).val) : ℝ) *
        A.exteriorNorm (nonunitFrequencyRadical C p mult₁ mult₂ (frequency x))) * Z ^ mChild) →
    (∀ I ∈ rows.image (fun x => (r x).ideal.val),
      ((rows.filter (fun x => (r x).ideal.val = I)).card : ℝ) ≤ sectors) →
    2 * (c + w) / 3 - 3 * stepσ - 5 * δ / 6 ≤ F₁ →
    2 * b₂ / 3 ≤ F₂ → vStar ≤ c + w + b₂ →
    ∀ {kleft kright : ℕ}
      (left : ∀ x, AllocatedExceptionalSource (V := V) (σ := σ)
        (CanonicalExceptionalVolume.coefficient (χ iLeft)) WL₁ WL₂ (leftFactor x) (r x).element kleft)
      (right : ∀ x, AllocatedExceptionalSource (V := V) (σ := σ)
        (CanonicalExceptionalVolume.coefficient (χ iRight)) WR₁ WR₂ (rightFactor x) (r x).element kright),
    (∀ x ∈ rows, (left x).mask ≠ ⊥) →
    (∀ x ∈ rows, (Ideal.absNorm (left x).mask : ℝ) ≤ Z ^ maskExponent) →
    (∀ x ∈ rows, ‖(left x).time‖ ≤ height) →
    (∀ x ∈ rows, Z ^ ((m + q) / 4 - vStar - r₁) ≤ (left x).lower) →
    (∀ x ∈ rows, (left x).rawMass * (right x).rawMass ≤
      Cnormal * Z ^ (a₀ - b₂ - r₁ - r₂)) →
    Z ^ (-(mChild + qChild + Δ)) *
      (∑ x ∈ rows, ‖(left x).value‖ * ‖(right x).value‖) ≤
      (sectors * Cbound * Cnormal) * P ^ 4 * (1 + height) ^ J *
        Z ^ (max (Aexp - (m + q)) 0 + 3 * stepσ + 5 * δ / 6 + ε +
          slotError - divisorLower) := by
  obtain ⟨orders, hzero, J, Csource, hCsource, hsource⟩ :=
    CanonicalExceptionalVolume.exists_original_source_bounds (A := A) (V := V) (σ := σ)
      χ density remainder hcontinuous hvolume window hcompact hpositive
      ε maskExponent hε hmask
  have hcount : 0 < idealCountConstant F := zero_lt_one.trans_le (one_le_idealCountConstant F)
  let Cbound := Csource ^ 2 * idealCountConstant F
  have hCbound : 0 < Cbound := mul_pos (sq_pos_of_pos hCsource) hcount
  refine ⟨orders, hzero, J, Cbound, hCbound, ?_⟩
  intro iLeft iRight WL₁ WL₂ WR₁ WR₂ hsL₁ hsL₂ hsR₁ hsR₂ P hP hPL₁ hPL₂ hPR₁ hPR₂
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  obtain ⟨_, hleftBound⟩ := hsource iLeft WL₁ WL₂ hsL₁ hsL₂ P hP0 hPL₁ hPL₂
  obtain ⟨hrightBound, _⟩ := hsource iRight WR₁ WR₂ hsR₁ hsR₂ P hP0 hPR₁ hPR₂
  let Cleft := Csource * P ^ 2
  let Cright := Csource * P ^ 2
  have hCleft : 0 < Cleft := mul_pos hCsource (pow_pos (zero_lt_one.trans_le hP) _)
  have hCright : 0 < Cright := hCleft
  intro ι HRows instFintype instDecidableEq C p hp mult₁ mult₂ rows Ih frequency r base
    leftFactor rightFactor
    Z Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ v vStar
    r₁ r₂ divisorLower slotError sectors Cnormal height stepσ δ
    hZ hv hr₁ hdivisor hsectors hCnormal hheight
  dsimp only
  intro hclass hfactor hwindow hcutoff hfiber hF₁ hF₂ hvsum kleft kright
    left right hmask0 hmasknorm htime hminimum hnormal
  let a₀ := Aexp - c - w
  let K₀ := 2 * Aexp - c - d + R₀ + E₀ - m
  let mChild := 2 * a₀ - K - g - g₂ - V₀
  let qChild := q + R₀ + E₀ + wo + t₂ + V₀
  let Δ := b₂ - p₂ + w + Bcommon + ell
  let normExp := mChild + qChild + Δ
  let rawExp := a₀ - b₂ - r₁ - r₂
  let rowExp := (mChild - 2 * v) / 6
  let saving := max ((m + q) / 4 - vStar - r₁) 0
  let F₁ := firstSaving c (d + K₀ - K) w (q + R₀ + E₀) wo Bcommon g ell
  let F₂ := 2 * b₂ - 5 * g₂ / 6 - p₂ + t₂ + V₀ / 6 + (2 * v) / 6
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hrows : (rows.card : ℝ) ≤ sectors * idealCountConstant F * Z ^ rowExp :=
    actual_exceptional_sector_count C p hp mult₁ mult₂ rows Ih frequency r base
      hclass hfactor Z mChild v sectors hZ hv hsectors hwindow hcutoff hfiber
  have hheightpow : 0 ≤ (1 + height) ^ J := pow_nonneg (by linarith) J
  let U := (Cleft * Cright * Cnormal) * (1 + height) ^ J * Z ^ (rawExp + ε - saving)
  have hU : 0 ≤ U := mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg hCleft.le hCright.le) hCnormal) hheightpow)
    (Real.rpow_nonneg hZpos.le _)
  have hpoint (x) (hx : x ∈ rows) : ‖(left x).value‖ * ‖(right x).value‖ ≤ U := by
    have hl := hleftBound Z hZ (left x) (hmask0 x hx) (hmasknorm x hx)
      ((m + q) / 4 - vStar - r₁) (hminimum x hx)
    have hr := (hrightBound (right x)).2
    have hp : (1 + ‖(left x).time‖) ^ J ≤ (1 + height) ^ J :=
      pow_le_pow_left₀ (by positivity) (by linarith [htime x hx]) J
    have hl' : ‖(left x).value‖ ≤
        Cleft * Z ^ ε * (1 + height) ^ J * (left x).rawMass * Z ^ (-saving) :=
      hl.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp
            (mul_nonneg hCleft.le (Real.rpow_nonneg hZpos.le _)))
          (left x).rawMass_nonneg) (Real.rpow_nonneg hZpos.le _))
    have hl0 : 0 ≤ Cleft * Z ^ ε * (1 + height) ^ J *
        (left x).rawMass * Z ^ (-saving) :=
      mul_nonneg (mul_nonneg
        (mul_nonneg (mul_nonneg hCleft.le (Real.rpow_nonneg hZpos.le _)) hheightpow)
        (left x).rawMass_nonneg) (Real.rpow_nonneg hZpos.le _)
    have hraw := mul_le_mul_of_nonneg_right (hnormal x hx)
      (Real.rpow_nonneg hZpos.le (-saving))
    calc
      _ ≤ (Cleft * Z ^ ε * (1 + height) ^ J * (left x).rawMass * Z ^ (-saving)) *
          (Cright * (right x).rawMass) := mul_le_mul hl' hr (norm_nonneg _) hl0
      _ = (Cleft * Cright * Z ^ ε * (1 + height) ^ J) *
          (((left x).rawMass * (right x).rawMass) * Z ^ (-saving)) := by ring
      _ ≤ (Cleft * Cright * Z ^ ε * (1 + height) ^ J) *
          ((Cnormal * Z ^ rawExp) * Z ^ (-saving)) :=
        mul_le_mul_of_nonneg_left hraw
          (mul_nonneg (mul_nonneg (mul_nonneg hCleft.le hCright.le)
            (Real.rpow_nonneg hZpos.le _)) hheightpow)
      _ = U := by
        dsimp only [U]
        rw [show rawExp + ε - saving = ε + (rawExp + -saving) by ring,
          Real.rpow_add hZpos, Real.rpow_add hZpos]
        ring
  have hsum : (∑ x ∈ rows, ‖(left x).value‖ * ‖(right x).value‖) ≤ (rows.card : ℝ) * U := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hpoint
  have hid := exceptional_excess_identity
    Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ (2 * v)
  change (mChild - 2 * v) / 6 + a₀ - b₂ - normExp =
    Aexp - 5 * (m + q) / 6 - F₁ - F₂ at hid
  have hledger := exceptional_paired_exponent Aexp (m + q) c w b₂ vStar F₁ F₂ stepσ δ
    hF₁ hF₂ hvsum
  have hdiv := centered_divisor_saving divisorLower r₁ r₂
    (max ((m + q) / 4 - vStar) 0) slotError hdivisor
  rw [← positive_part_after_extraction ((m + q) / 4 - vStar) r₁ hr₁] at hdiv
  have he : -normExp + rowExp + (rawExp + ε - saving) ≤
      max (Aexp - (m + q)) 0 + 3 * stepσ + 5 * δ / 6 + ε +
        slotError - divisorLower := by
    dsimp only [rowExp, rawExp, saving]
    linarith [hid, hledger, hdiv]
  change Z ^ (-normExp) * (∑ x ∈ rows, ‖(left x).value‖ * ‖(right x).value‖) ≤ _
  calc
    _ ≤ Z ^ (-normExp) * ((rows.card : ℝ) * U) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hZpos.le _)
    _ ≤ Z ^ (-normExp) * ((sectors * idealCountConstant F * Z ^ rowExp) * U) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrows hU)
        (Real.rpow_nonneg hZpos.le _)
    _ = (sectors * Cbound * Cnormal) * P ^ 4 * (1 + height) ^ J *
        Z ^ (-normExp + rowExp + (rawExp + ε - saving)) := by
      simp only [Real.rpow_add hZpos]
      dsimp only [U, Cbound, Cleft, Cright]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ he)
      (mul_nonneg (mul_nonneg
        (mul_nonneg (mul_nonneg hsectors hCbound.le) hCnormal)
        (pow_nonneg hP0 4)) hheightpow)

end HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalRows

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalRows.exists_original_paired_row_bound
