import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OrdinaryExceptionalAmplitude

/-!
# Absolute exceptional contribution in the ordinary range

The genuine sixth-power frequency count and the two original absolute
volume estimates give the ordinary terminal exponent. All divisor
extraction and live-slot normalizations are retained. There is no
centered minimum-length premise.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.CenteredMomentCounting UniqueFactorizationMonoid

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ΨL ΨR : Ideal (𝓞 F) →* ℂ} {WL₁ WL₂ WR₁ WR₂ : ℝ → ℂ}

/-- This constant precedes the base, row family, allocation and all
formal scale windows. -/
def ordinaryExceptionalConstant
    (HL : ExceptionalVolumeControl ΨL WL₁ WL₂)
    (HR : ExceptionalVolumeControl ΨR WR₁ WR₂) : ℝ :=
  (1 + HL.absoluteConstant) * (1 + HR.absoluteConstant) * idealCountConstant F

theorem ordinaryExceptionalConstant_pos
    (HL : ExceptionalVolumeControl ΨL WL₁ WL₂)
    (HR : ExceptionalVolumeControl ΨR WR₁ WR₂) :
    0 < ordinaryExceptionalConstant HL HR := by
  unfold ordinaryExceptionalConstant
  have hL : 0 < 1 + HL.absoluteConstant := by linarith [HL.absoluteConstant_nonneg]
  have hR : 0 < 1 + HR.absoluteConstant := by linarith [HR.absoluteConstant_nonneg]
  exact mul_pos (mul_pos hL hR) (zero_lt_one.trans_le (one_le_idealCountConstant F))

/-- Internal row assembly: the raw source masses here are the explicit
frozen scalar, retained prime masses and formal rectangle square root.
The next layer derives their bound from individual atoms. -/
theorem actual_ordinary_exceptional_contribution
    (HL : ExceptionalVolumeControl ΨL WL₁ WL₂)
    (HR : ExceptionalVolumeControl ΨR WR₁ WR₂)
    {ι HRows : Type*} [Fintype ι] [DecidableEq ι]
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p)
    (mult₁ mult₂ : ι → ℕ)
    (rows : Finset HRows) (Ih : HRows → A.Exterior) (frequency : HRows → A.R)
    (r : ∀ x, ActualExceptionalRow C p mult₁ mult₂ (Ih x) (frequency x))
    (base : Ideal (𝓞 F)) (leftFactor rightFactor : HRows → A.R)
    (Z Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ v
      r₁ r₂ divisorLower slotError sectors Cnormal stepσ δ : ℝ)
    (hZ : 1 ≤ Z) (hv : 0 ≤ v) (hr₁ : 0 ≤ r₁)
    (hdivisor : divisorLower - r₂ ≤ slotError)
    (hsectors : 0 ≤ sectors) (hCnormal : 0 ≤ Cnormal)
    (hA : Aexp ≤ 5 * (m + q) / 6) (hc : 0 ≤ c) (hw : 0 ≤ w) (hb₂ : 0 ≤ b₂)
    (hclass : ∀ x ∈ rows, ∀ i ∈ multiplicityOneNonunitPrimes C p mult₁ mult₂ (frequency x),
      6 ∣ (normalizedFactors (Ih x).val).count (p i).val.asIdeal)
    (hfactor : ∀ x ∈ rows, ∃ a : Ideal (𝓞 F), (r x).ideal.val = base * a ^ 6)
    (hwindow : ∀ x ∈ rows, Z ^ v ≤
      A.exteriorNorm (multiplicityOneNonunitRadical C p mult₁ mult₂ (frequency x)))
    (hcutoff : ∀ x ∈ rows, A.exteriorNorm (Ih x) ≤
      ((Ideal.absNorm (gcd (primePowerProduct p mult₁).val (primePowerProduct p mult₂).val) : ℝ) *
        A.exteriorNorm (nonunitFrequencyRadical C p mult₁ mult₂ (frequency x))) *
          Z ^ (2 * (Aexp - c - w) - K - g - g₂ - V₀))
    (hfiber : ∀ I ∈ rows.image (fun x => (r x).ideal.val),
      ((rows.filter (fun x => (r x).ideal.val = I)).card : ℝ) ≤ sectors)
    (hF₁ : 2 * (c + w) / 3 - 3 * stepσ - 5 * δ / 6 ≤
      firstSaving c (d + (2 * Aexp - c - d + R₀ + E₀ - m) - K)
        w (q + R₀ + E₀) wo Bcommon g ell)
    (hF₂ : 2 * b₂ / 3 ≤ 2 * b₂ - 5 * g₂ / 6 - p₂ + t₂ + V₀ / 6 + (2 * v) / 6)
    {kleft kright : ℕ}
    (left : ∀ x, AllocatedExceptionalSource (V := V) (σ := σ)
      ΨL WL₁ WL₂ (leftFactor x) (r x).element kleft)
    (right : ∀ x, AllocatedExceptionalSource (V := V) (σ := σ)
      ΨR WR₁ WR₂ (rightFactor x) (r x).element kright)
    (hnormal : ∀ x ∈ rows, (left x).rawMass * (right x).rawMass ≤
      Cnormal * Z ^ (Aexp - c - w - b₂ - r₁ - r₂)) :
    Z ^ (-((2 * (Aexp - c - w) - K - g - g₂ - V₀) +
      (q + R₀ + E₀ + wo + t₂ + V₀) + (b₂ - p₂ + w + Bcommon + ell))) *
      (∑ x ∈ rows, ‖(left x).ordinaryValue‖ * ‖(right x).ordinaryValue‖) ≤
      (sectors * ordinaryExceptionalConstant HL HR * Cnormal) *
        Z ^ (3 * stepσ + 5 * δ / 6 + slotError - divisorLower) := by
  let a₀ := Aexp - c - w
  let K₀ := 2 * Aexp - c - d + R₀ + E₀ - m
  let mChild := 2 * a₀ - K - g - g₂ - V₀
  let qChild := q + R₀ + E₀ + wo + t₂ + V₀
  let Δ := b₂ - p₂ + w + Bcommon + ell
  let normExp := mChild + qChild + Δ
  let rawExp := a₀ - b₂ - r₁ - r₂
  let rowExp := (mChild - 2 * v) / 6
  let F₁ := firstSaving c (d + K₀ - K) w (q + R₀ + E₀) wo Bcommon g ell
  let F₂ := 2 * b₂ - 5 * g₂ / 6 - p₂ + t₂ + V₀ / 6 + (2 * v) / 6
  let CL := 1 + HL.absoluteConstant
  let CR := 1 + HR.absoluteConstant
  have hCL : 0 ≤ CL := by dsimp only [CL]; linarith [HL.absoluteConstant_nonneg]
  have hCR : 0 ≤ CR := by dsimp only [CR]; linarith [HR.absoluteConstant_nonneg]
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hcount : 0 ≤ idealCountConstant F := zero_le_one.trans (one_le_idealCountConstant F)
  have hrows : (rows.card : ℝ) ≤ sectors * idealCountConstant F * Z ^ rowExp :=
    actual_exceptional_sector_count C p hp mult₁ mult₂ rows Ih frequency r base
      hclass hfactor Z mChild v sectors hZ hv hsectors hwindow hcutoff hfiber
  let U := (CL * CR * Cnormal) * Z ^ rawExp
  have hU : 0 ≤ U :=
    mul_nonneg (mul_nonneg (mul_nonneg hCL hCR) hCnormal) (Real.rpow_nonneg hz.le _)
  have hpoint (x) (hx : x ∈ rows) :
      ‖(left x).ordinaryValue‖ * ‖(right x).ordinaryValue‖ ≤ U := by
    have hl : ‖(left x).ordinaryValue‖ ≤ CL * (left x).rawMass :=
      ((left x).ordinary_absolute HL).trans
        (mul_le_mul_of_nonneg_right (by dsimp only [CL]; linarith) (left x).rawMass_nonneg)
    have hr : ‖(right x).ordinaryValue‖ ≤ CR * (right x).rawMass :=
      ((right x).ordinary_absolute HR).trans
        (mul_le_mul_of_nonneg_right (by dsimp only [CR]; linarith) (right x).rawMass_nonneg)
    calc
      _ ≤ (CL * (left x).rawMass) * (CR * (right x).rawMass) :=
        mul_le_mul hl hr (norm_nonneg _) (mul_nonneg hCL (left x).rawMass_nonneg)
      _ = (CL * CR) * ((left x).rawMass * (right x).rawMass) := by ring
      _ ≤ (CL * CR) * (Cnormal * Z ^ rawExp) :=
        mul_le_mul_of_nonneg_left (hnormal x hx) (mul_nonneg hCL hCR)
      _ = U := by dsimp only [U]; ring
  have hsum : (∑ x ∈ rows, ‖(left x).ordinaryValue‖ * ‖(right x).ordinaryValue‖) ≤
      (rows.card : ℝ) * U := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hpoint
  have hid := exceptional_excess_identity
    Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ (2 * v)
  change (mChild - 2 * v) / 6 + a₀ - b₂ - normExp =
    Aexp - 5 * (m + q) / 6 - F₁ - F₂ at hid
  have hledger := uncentered_exceptional_bound Aexp (m + q) c w b₂ F₁ F₂ stepσ δ
    hA hc hw hb₂ hF₁ hF₂
  have he : -normExp + rowExp + rawExp ≤
      3 * stepσ + 5 * δ / 6 + slotError - divisorLower := by
    dsimp only [rowExp, rawExp]
    linarith
  change Z ^ (-normExp) * (∑ x ∈ rows, ‖(left x).ordinaryValue‖ * ‖(right x).ordinaryValue‖) ≤ _
  calc
    _ ≤ Z ^ (-normExp) * ((rows.card : ℝ) * U) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hz.le _)
    _ ≤ Z ^ (-normExp) * ((sectors * idealCountConstant F * Z ^ rowExp) * U) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrows hU)
        (Real.rpow_nonneg hz.le _)
    _ = (sectors * ordinaryExceptionalConstant HL HR * Cnormal) *
        Z ^ (-normExp + rowExp + rawExp) := by
      simp only [Real.rpow_add hz]
      dsimp only [U, ordinaryExceptionalConstant, CL, CR]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ he)
      (mul_nonneg (mul_nonneg hsectors (ordinaryExceptionalConstant_pos HL HR).le) hCnormal)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_ordinary_exceptional_contribution

