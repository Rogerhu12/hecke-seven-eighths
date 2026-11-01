import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalPrimitiveBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OrdinaryExceptionalContribution

/-!
# Uniform ordinary exceptional rows with the original cutoff cost

The original range A ≤ 5M/6 uses absolute volume on both sides.
Fixed character primitives choose the constant and profile orders
before every moving profile. The actual physical cutoff is paid as
cutoffLoss/6, without changing the original child width or allowance.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalRows

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.CenteredMomentCounting UniqueFactorizationMonoid

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem exists_original_ordinary_paired_row_bound_with_cutoff
    {Catalogue : Type*} [Fintype Catalogue]
    (χ : Catalogue → HeckeCharacter F)
    (density : Catalogue → 𝓢(ℝ, ℂ) → ℂ)
    (remainder : Catalogue → Seminorm ℂ (𝓢(ℝ, ℂ)))
    (hcontinuous : ∀ i, Continuous (remainder i))
    (hvolume : ∀ i (φ : 𝓢(ℝ, ℂ)) (X : ℝ), 0 < X →
      ‖(∑' I : Ideal (𝓞 F), CanonicalExceptionalVolume.coefficient (χ i) I *
          φ ((Ideal.absNorm I : ℝ) / X)) - (X : ℂ) * density i φ‖ ≤ remainder i φ)
    (window : Set ℝ) (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0) :
    ∃ orders : Finset (ℕ × ℕ), (0, 0) ∈ orders ∧
    ∃ Cbound : ℝ, 0 < Cbound ∧
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
    (base : Ideal (𝓞 F)) (leftFactor rightFactor : HRows → A.R)
    (Z Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ v
      r₁ r₂ divisorLower slotError cutoffLoss sectors Cnormal stepσ δ : ℝ)
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
          Z ^ (2 * (Aexp - c - w) - K - g - g₂ - V₀ + cutoffLoss))
    (hfiber : ∀ I ∈ rows.image (fun x => (r x).ideal.val),
      ((rows.filter (fun x => (r x).ideal.val = I)).card : ℝ) ≤ sectors)
    (hF₁ : 2 * (c + w) / 3 - 3 * stepσ - 5 * δ / 6 ≤
      firstSaving c (d + (2 * Aexp - c - d + R₀ + E₀ - m) - K)
        w (q + R₀ + E₀) wo Bcommon g ell)
    (hF₂ : 2 * b₂ / 3 ≤ 2 * b₂ - 5 * g₂ / 6 - p₂ + t₂ + V₀ / 6 + (2 * v) / 6)
    {kleft kright : ℕ}
    (left : ∀ x, AllocatedExceptionalSource (V := V) (σ := σ)
      (CanonicalExceptionalVolume.coefficient (χ iLeft)) WL₁ WL₂ (leftFactor x) (r x).element kleft)
    (right : ∀ x, AllocatedExceptionalSource (V := V) (σ := σ)
      (CanonicalExceptionalVolume.coefficient (χ iRight)) WR₁ WR₂ (rightFactor x) (r x).element kright)
    (hnormal : ∀ x ∈ rows, (left x).rawMass * (right x).rawMass ≤
      Cnormal * Z ^ (Aexp - c - w - b₂ - r₁ - r₂)),
    Z ^ (-((2 * (Aexp - c - w) - K - g - g₂ - V₀) +
      (q + R₀ + E₀ + wo + t₂ + V₀) + (b₂ - p₂ + w + Bcommon + ell))) *
      (∑ x ∈ rows, ‖(left x).ordinaryValue‖ * ‖(right x).ordinaryValue‖) ≤
      (sectors * Cbound * Cnormal) * P ^ 4 *
        Z ^ (3 * stepσ + 5 * δ / 6 + slotError - divisorLower + cutoffLoss / 6) := by
  obtain ⟨orders, hzero, _order, Csource, hCsource, hsource⟩ :=
    CanonicalExceptionalVolume.exists_original_source_bounds (V := V) (σ := σ)
      χ density remainder hcontinuous hvolume window hcompact hpositive
      1 0 (by norm_num) (by norm_num)
  let Cbound := Csource ^ 2 * idealCountConstant F
  have hCbound : 0 < Cbound :=
    mul_pos (sq_pos_of_pos hCsource) (zero_lt_one.trans_le (one_le_idealCountConstant F))
  refine ⟨orders, hzero, Cbound, hCbound, ?_⟩
  intro iLeft iRight WL₁ WL₂ WR₁ WR₂ hsL₁ hsL₂ hsR₁ hsR₂ P hP hPL₁ hPL₂ hPR₁ hPR₂
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hleftBound := (hsource iLeft WL₁ WL₂ hsL₁ hsL₂ P hP0 hPL₁ hPL₂).1
  have hrightBound := (hsource iRight WR₁ WR₂ hsR₁ hsR₂ P hP0 hPR₁ hPR₂).1
  intro ι HRows instFintype instDecidableEq C p hp mult₁ mult₂ rows Ih frequency r base
    leftFactor rightFactor Z Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ v
    r₁ r₂ divisorLower slotError cutoffLoss sectors Cnormal stepσ δ
    hZ hv hr₁ hdivisor hsectors hCnormal hA hc hw hb₂
    hclass hfactor hwindow hcutoff hfiber hF₁ hF₂ kleft kright left right hnormal
  let a₀ := Aexp - c - w
  let K₀ := 2 * Aexp - c - d + R₀ + E₀ - m
  let mChild := 2 * a₀ - K - g - g₂ - V₀
  let qChild := q + R₀ + E₀ + wo + t₂ + V₀
  let Δ := b₂ - p₂ + w + Bcommon + ell
  let normExp := mChild + qChild + Δ
  let rawExp := a₀ - b₂ - r₁ - r₂
  let rowExp := (mChild + cutoffLoss - 2 * v) / 6
  let F₁ := firstSaving c (d + K₀ - K) w (q + R₀ + E₀) wo Bcommon g ell
  let F₂ := 2 * b₂ - 5 * g₂ / 6 - p₂ + t₂ + V₀ / 6 + (2 * v) / 6
  let CL := Csource * P ^ 2
  let CR := Csource * P ^ 2
  have hCL : 0 ≤ CL := mul_nonneg hCsource.le (sq_nonneg P)
  have hCR : 0 ≤ CR := hCL
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hcount : 0 ≤ idealCountConstant F := zero_le_one.trans (one_le_idealCountConstant F)
  have hrows : (rows.card : ℝ) ≤ sectors * idealCountConstant F * Z ^ rowExp :=
    actual_exceptional_sector_count C p hp mult₁ mult₂ rows Ih frequency r base
      hclass hfactor Z (mChild + cutoffLoss) v sectors hZ hv hsectors hwindow hcutoff hfiber
  let U := (CL * CR * Cnormal) * Z ^ rawExp
  have hU : 0 ≤ U :=
    mul_nonneg (mul_nonneg (mul_nonneg hCL hCR) hCnormal) (Real.rpow_nonneg hz.le _)
  have hpoint (x) (hx : x ∈ rows) :
      ‖(left x).ordinaryValue‖ * ‖(right x).ordinaryValue‖ ≤ U := by
    have hl : ‖(left x).ordinaryValue‖ ≤ CL * (left x).rawMass :=
      (hleftBound (left x)).1
    have hr : ‖(right x).ordinaryValue‖ ≤ CR * (right x).rawMass :=
      (hrightBound (right x)).1
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
      3 * stepσ + 5 * δ / 6 + slotError - divisorLower + cutoffLoss / 6 := by
    dsimp only [rowExp, rawExp]
    linarith
  change Z ^ (-normExp) * (∑ x ∈ rows, ‖(left x).ordinaryValue‖ * ‖(right x).ordinaryValue‖) ≤ _
  calc
    _ ≤ Z ^ (-normExp) * ((rows.card : ℝ) * U) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hz.le _)
    _ ≤ Z ^ (-normExp) * ((sectors * idealCountConstant F * Z ^ rowExp) * U) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrows hU)
        (Real.rpow_nonneg hz.le _)
    _ = (sectors * Cbound * Cnormal) * P ^ 4 *
        Z ^ (-normExp + rowExp + rawExp) := by
      simp only [Real.rpow_add hz]
      dsimp only [U, Cbound, CL, CR]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ he)
      (mul_nonneg (mul_nonneg (mul_nonneg hsectors hCbound.le) hCnormal) (pow_nonneg hP0 4))

end HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalRows

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalRows.exists_original_ordinary_paired_row_bound_with_cutoff
