import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondExceptionalBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondExceptionalPartition
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalAtomEnvelope

/-!
# The actual exceptional hybrid term reaches its terminal estimate

The row set is the original paired inducing-character predicate.  The
complete common correlation and original Gauss scales remain in its
weight.  The two actual exceptional charts have the same extracted row,
with the negative factor and negative locations on the right.  The raw
normalization is proved from the individual atom windows before the
valuation count and the single centered saving are applied.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Characters HeckeGeneral.Analysis HeckePort.Moments
open HeckePort.CenteredMomentCounting UniqueFactorizationMonoid

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The two original centered rectangles need only have the same
plain-scale product.  Their complex Gauss normalizers then agree
before any norm or subtraction is taken. -/
theorem extraGaussNormalizer_plain_product_eq {k : ℕ}
    (N₁ N₂ M₁ M₂ : ℝ) (P : Fin k → ℝ)
    (hN₁ : 0 ≤ N₁) (hM₁ : 0 ≤ M₁) (hproduct : N₁ * N₂ = M₁ * M₂) :
    extraGaussNormalizer N₁ N₂ P = extraGaussNormalizer M₁ M₂ P := by
  unfold extraGaussNormalizer SecondCoefficientTermDictionary.centralNormalizer
  rw [← mul_inv, ← Complex.ofReal_mul, ← Real.sqrt_mul hN₁,
    ← mul_inv, ← Complex.ofReal_mul, ← Real.sqrt_mul hM₁, hproduct]

theorem SecondCoefficientComparison.centeredCoefficient_original_scales
    {Ray : Type*} [CommGroup Ray] {k : ℕ} {T : FixedChildCharacters F k}
    {phase : Ray →* Circle} {S₁ S₂ : Finset (Ideal (𝓞 F))}
    {S : Fin k → Finset (HeightOneSpectrum (𝓞 F))}
    {D : SecondCoefficientTermDictionary T phase S₁ S₂ S}
    (E : SecondCoefficientComparison D)
    (N₁ N₂ M₁ M₂ : ℝ) (P : Fin k → ℝ)
    (hN₁ : 0 ≤ N₁) (hM₁ : 0 ≤ M₁) (hproduct : N₁ * N₂ = M₁ * M₂)
    (i : AllocationColumn F k) :
    E.centeredCoefficient (Real.sqrt N₁ : ℂ)⁻¹ (Real.sqrt N₂ : ℂ)⁻¹
        (fun j => (Real.sqrt (P j) : ℂ)⁻¹) i =
      D.normalizedCoefficient (Real.sqrt N₁ : ℂ)⁻¹ (Real.sqrt N₂ : ℂ)⁻¹
        (fun j => (Real.sqrt (P j) : ℂ)⁻¹) i -
      E.dictionary.normalizedCoefficient (Real.sqrt M₁ : ℂ)⁻¹ (Real.sqrt M₂ : ℂ)⁻¹
        (fun j => (Real.sqrt (P j) : ℂ)⁻¹) i := by
  unfold SecondCoefficientComparison.centeredCoefficient
  congr 1
  rw [SecondCoefficientTermDictionary.normalizedCoefficient_eq,
    SecondCoefficientTermDictionary.normalizedCoefficient_eq]
  exact congrArg (fun z : ℂ => z * E.dictionary.coefficient i)
    (extraGaussNormalizer_plain_product_eq N₁ N₂ M₁ M₂ P hN₁ hM₁ hproduct)

namespace ActualSecondCorrelationRows

def exceptionalRows {H ι : Type*} [Fintype ι]
    (R : ActualSecondCorrelationRows A σ H ι)
    {theta : Finset (HeckeCharacter F)} (Q : PairedFiniteCharacters theta H) : Finset R.live :=
  Finset.univ.filter (fun h => Q.exceptional h.val)

theorem exceptionalRows_original_mem {H ι : Type*} [Fintype ι]
    (R : ActualSecondCorrelationRows A σ H ι)
    {theta : Finset (HeckeCharacter F)} (Q : PairedFiniteCharacters theta H)
    (h : R.exceptionalRows Q) : h.val.val ∈ R.rows.filter Q.exceptional :=
  Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp h.val.property).1, (Finset.mem_filter.mp h.property).2⟩

end ActualSecondCorrelationRows

variable {ΨL ΨR : Ideal (𝓞 F) →* ℂ} {WL₁ WL₂ WR₁ WR₂ : ℝ → ℂ}
variable (HL : ExceptionalVolumeControl ΨL WL₁ WL₂) (HR : ExceptionalVolumeControl ΨR WR₁ WR₂)
variable (ε maskExponent : ℝ) (hε : 0 < ε) (hmask : 0 ≤ maskExponent)

/-- Both choices precede every source, finite label, base and Fourier
parameter; only the fixed original volume profiles enter. -/
def exceptionalTerminalOrder
    {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
    (HL : ExceptionalVolumeControl ΨL WL₁ WL₂) (HR : ExceptionalVolumeControl ΨR WR₁ WR₂)
    (ε maskExponent : ℝ) (hε : 0 < ε) (hmask : 0 ≤ maskExponent) : ℕ :=
  (AllocatedExceptionalSource.centered_or_absolute_uniform (A := A) (V := V) (σ := σ)
    HL ε maskExponent hε hmask).choose

def exceptionalTerminalConstant
    {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
    (HL : ExceptionalVolumeControl ΨL WL₁ WL₂) (HR : ExceptionalVolumeControl ΨR WR₁ WR₂)
    (ε maskExponent : ℝ) (hε : 0 < ε) (hmask : 0 ≤ maskExponent) : ℝ :=
  (AllocatedExceptionalSource.centered_or_absolute_uniform (A := A) (V := V) (σ := σ)
    HL ε maskExponent hε hmask).choose_spec.choose *
      (1 + 2 * HR.absoluteConstant) * idealCountConstant F

theorem exceptionalTerminalConstant_pos :
    0 < exceptionalTerminalConstant (V := V) (σ := σ) (η := η) (hS := hS)
      HL HR ε maskExponent hε hmask := by
  have hleft := (AllocatedExceptionalSource.centered_or_absolute_uniform
    (A := A) (V := V) (σ := σ) HL ε maskExponent hε hmask).choose_spec.choose_spec.1
  have hright : 0 < 1 + 2 * HR.absoluteConstant := by
    linarith [HR.absoluteConstant_nonneg]
  exact mul_pos (mul_pos hleft hright)
    (zero_lt_one.trans_le (one_le_idealCountConstant F))

set_option maxHeartbeats 4000000 in
/-- The choices come from the single-source analytic statement, which
has no row or prime-index universe.  The actual classification/count
argument then works for arbitrary source carriers with those same choices. -/
private theorem exceptionalTerminal_selected_contribution :
    let J := exceptionalTerminalOrder (V := V) (σ := σ) (η := η) (hS := hS)
      HL HR ε maskExponent hε hmask
    let Cbound := exceptionalTerminalConstant (V := V) (σ := σ) (η := η) (hS := hS)
      HL HR ε maskExponent hε hmask
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
        ΨL WL₁ WL₂ (leftFactor x) (r x).element kleft)
      (right : ∀ x, AllocatedExceptionalSource (V := V) (σ := σ)
        ΨR WR₁ WR₂ (rightFactor x) (r x).element kright),
    (∀ x ∈ rows, (left x).mask ≠ ⊥) →
    (∀ x ∈ rows, (Ideal.absNorm (left x).mask : ℝ) ≤ Z ^ maskExponent) →
    (∀ x ∈ rows, ‖(left x).time‖ ≤ height) →
    (∀ x ∈ rows, Z ^ ((m + q) / 4 - vStar - r₁) ≤ (left x).lower) →
    (∀ x ∈ rows, (left x).rawMass * (right x).rawMass ≤
      Cnormal * Z ^ (a₀ - b₂ - r₁ - r₂)) →
    Z ^ (-(mChild + qChild + Δ)) *
      (∑ x ∈ rows, ‖(left x).value‖ * ‖(right x).value‖) ≤
      (sectors * Cbound * Cnormal) * (1 + height) ^ J *
        Z ^ (max (Aexp - (m + q)) 0 + 3 * stepσ + 5 * δ / 6 + ε +
          slotError - divisorLower) := by
  dsimp only
  let J := (AllocatedExceptionalSource.centered_or_absolute_uniform
    (A := A) (V := V) (σ := σ) HL ε maskExponent hε hmask).choose
  let Cleft := (AllocatedExceptionalSource.centered_or_absolute_uniform
    (A := A) (V := V) (σ := σ) HL ε maskExponent hε hmask).choose_spec.choose
  have hCleft : 0 < Cleft := (AllocatedExceptionalSource.centered_or_absolute_uniform
    (A := A) (V := V) (σ := σ) HL ε maskExponent hε hmask).choose_spec.choose_spec.1
  have hleftBound := (AllocatedExceptionalSource.centered_or_absolute_uniform
    (A := A) (V := V) (σ := σ) HL ε maskExponent hε hmask).choose_spec.choose_spec.2
  let Cright := 1 + 2 * HR.absoluteConstant
  have hCright : 0 < Cright := by
    dsimp only [Cright]
    linarith [HR.absoluteConstant_nonneg]
  have hcount : 0 < idealCountConstant F := zero_lt_one.trans_le (one_le_idealCountConstant F)
  let Cbound := Cleft * Cright * idealCountConstant F
  intro ι HRows instFintype instDecidableEq C p hp mult₁ mult₂ rows Ih frequency r base
    leftFactor rightFactor
    Z Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ v vStar
    r₁ r₂ divisorLower slotError sectors Cnormal height stepσ δ
    hZ hv hr₁ hdivisor hsectors hCnormal hheight
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
    have hr := (right x).absolute HR
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
  have hpart (L r : ℝ) (hr : 0 ≤ r) :
      max (L - r) 0 = max (max L 0 - r) 0 := by
    rcases le_total 0 L with hL | hL
    · rw [max_eq_left hL]
    · have hLr : L - r ≤ 0 := by linarith
      have h0r : 0 - r ≤ 0 := by linarith
      simp only [max_eq_right hL, max_eq_right hLr, max_eq_right h0r]
  rw [← hpart ((m + q) / 4 - vStar) r₁ hr₁] at hdiv
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
    _ = (sectors * Cbound * Cnormal) * (1 + height) ^ J *
        Z ^ (-normExp + rowExp + (rawExp + ε - saving)) := by
      simp only [Real.rpow_add hZpos]
      dsimp only [U, Cbound]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ he)
      (mul_nonneg (mul_nonneg (mul_nonneg hsectors
        (mul_nonneg (mul_nonneg hCleft.le hCright.le) hcount.le)) hCnormal) hheightpow)

namespace SecondSideFrame

variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable {C : A.GeneralArithmeticContext σ η hS}
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray] {k l : ℕ}

/-- This is the exceptional summand of the genuine hybrid kernel.
Its row weight, raw source normalization and row count are all derived.
The exponent equality concerns only the individual numerical windows,
and the actual second-divisor loss remains visible for its later sum. -/
theorem exceptional_magnitude_terminal_from_atoms
    (left : SecondSideFrame (V := V) C R Ray .left k)
    (right : SecondSideFrame (V := V) C R Ray .right l)
    (EL : SecondCoefficientComparison left.dictionary)
    (ER : SecondCoefficientComparison right.dictionary)
    {theta : Finset (HeckeCharacter F)} (Q : PairedFiniteCharacters theta H) (ξ : V)
    (TL : ∀ h : R.exceptionalRows Q, left.source.ExceptionalAt (σ := σ) EL.scale₁ EL.scale₂
      (fun _ => EL.leftWeight) (fun _ => EL.rightWeight) ΨL WL₁ WL₂ ξ h.val)
    (TR : ∀ h : R.exceptionalRows Q, right.source.ExceptionalAt (σ := σ) ER.scale₁ ER.scale₂
      (fun _ => ER.leftWeight) (fun _ => ER.rightWeight) ΨR WR₁ WR₂ ξ h.val)
    (UL : ExceptionalAtomicScales left.allocation) (UR : ExceptionalAtomicScales right.allocation)
    (Z Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ v vStar
      r₁ r₂ divisorLower slotError sectors height stepσ δ rowAmplitude : ℝ)
    (hZ : 1 ≤ Z) (hv : 0 ≤ v) (hr₁ : 0 ≤ r₁) (hdivisor : divisorLower - r₂ ≤ slotError)
    (hsectors : 0 ≤ sectors) (hheight : 0 ≤ height) (hrowAmplitude : 0 ≤ rowAmplitude)
    (hleftAtoms : ∀ h, (TL h).source.AtomicControl Z UL)
    (hrightAtoms : ∀ h, (TR h).source.AtomicControl Z UR)
    (hexponent : UL.exponent + UR.exponent = Aexp - c - w - b₂ - r₁ - r₂)
    (hm : ∀ i, 0 < R.leftMultiplicity i)
    (hgcd : (Ideal.absNorm (gcd (primePowerProduct R.primes R.leftMultiplicity).val
      (primePowerProduct R.primes R.rightMultiplicity).val) : ℝ) ≤ Z ^ g₂)
    (hunit : ∀ h ∈ R.rows.filter Q.exceptional, Z ^ t₂ ≤ A.exteriorNorm
      (unitFrequencyRadical C R.primes R.leftMultiplicity R.rightMultiplicity (R.frequency h)))
    (hweight : ∀ h ∈ R.rows.filter Q.exceptional, ‖R.weight h‖ ≤ rowAmplitude)
    (base : Ideal (𝓞 F))
    (hclass : ∀ h : R.exceptionalRows Q, ∀ i ∈ multiplicityOneNonunitPrimes C R.primes
      R.leftMultiplicity R.rightMultiplicity (R.frequency h.val.val),
      6 ∣ (normalizedFactors (R.originalIdeal h.val.val).val).count (R.primes i).val.asIdeal)
    (hfactor : ∀ h : R.exceptionalRows Q, ∃ a : Ideal (𝓞 F),
      (R.extractedRow C h.val).ideal.val = base * a ^ 6)
    (hwindow : ∀ h : R.exceptionalRows Q, Z ^ v ≤ A.exteriorNorm
      (multiplicityOneNonunitRadical C R.primes R.leftMultiplicity R.rightMultiplicity
        (R.frequency h.val.val)))
    (hcutoff : ∀ h : R.exceptionalRows Q, A.exteriorNorm (R.originalIdeal h.val.val) ≤
      R.normFactor C h.val.val * Z ^ (2 * (Aexp - c - w) - K - g - g₂ - V₀))
    (hfiber : ∀ I ∈ (Finset.univ : Finset (R.exceptionalRows Q)).image
      (fun h => (R.extractedRow C h.val).ideal.val),
      (((Finset.univ : Finset (R.exceptionalRows Q)).filter
        (fun h => (R.extractedRow C h.val).ideal.val = I)).card : ℝ) ≤ sectors)
    (hF₁ : 2 * (c + w) / 3 - 3 * stepσ - 5 * δ / 6 ≤
      firstSaving c (d + (2 * Aexp - c - d + R₀ + E₀ - m) - K)
        w (q + R₀ + E₀) wo Bcommon g ell)
    (hF₂ : 2 * b₂ / 3 ≤ 2 * b₂ - 5 * g₂ / 6 - p₂ + t₂ + V₀ / 6 + (2 * v) / 6)
    (hvsum : vStar ≤ c + w + b₂)
    (hmask0 : ∀ h, (TL h).source.mask ≠ ⊥)
    (hmasknorm : ∀ h, (Ideal.absNorm (TL h).source.mask : ℝ) ≤ Z ^ maskExponent)
    (htime : ∀ h, ‖(TL h).source.time‖ ≤ height)
    (hminimum : ∀ h, Z ^ ((m + q) / 4 - vStar - r₁) ≤ (TL h).source.lower) :
    let mChild := 2 * (Aexp - c - w) - K - g - g₂ - V₀
    let qChild := q + R₀ + E₀ + wo + t₂ + V₀
    let Δ := b₂ - p₂ + w + Bcommon + ell
    let rowFactor := rowAmplitude * Z ^ (g₂ - t₂) /
      (Real.sqrt left.normalizationScale * Real.sqrt right.normalizationScale)
    Z ^ (-(mChild + qChild + Δ)) *
      jointColumnPairMagnitude (R.exceptionalRows Q) left.allocation.columns right.allocation.columns
        (fun h : R.live => R.weight h.val * R.correlation h.val)
        (fun h => left.centeredCoefficient EL h.val)
        (fun h => right.centeredCoefficient ER h.val)
        (fun h => rawSourceLocation (left.leftLocation h.val) (left.rightLocation h.val)
          (left.slotLocation h.val))
        (fun h => rawSourceLocation (right.leftLocation h.val) (right.rightLocation h.val)
          (right.slotLocation h.val)) ξ ≤
      rowFactor * (sectors * exceptionalTerminalConstant (V := V) (σ := σ) (η := η) (hS := hS)
        HL HR ε maskExponent hε hmask * (UL.constant * UR.constant)) *
      (1 + height) ^ exceptionalTerminalOrder (V := V) (σ := σ) (η := η) (hS := hS)
        HL HR ε maskExponent hε hmask *
      Z ^ (max (Aexp - (m + q)) 0 + 3 * stepσ + 5 * δ / 6 + ε + slotError - divisorLower) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hnormal (h : R.exceptionalRows Q) :
      (TL h).source.rawMass * (TR h).source.rawMass ≤
        (UL.constant * UR.constant) * Z ^ (Aexp - c - w - b₂ - r₁ - r₂) := by
    have hl := (TL h).source.rawMass_le_atomic_power C Z hZ UL (hleftAtoms h)
    have hr := (TR h).source.rawMass_le_atomic_power C Z hZ UR (hrightAtoms h)
    calc
      _ ≤ (UL.constant * Z ^ UL.exponent) * (UR.constant * Z ^ UR.exponent) :=
        mul_le_mul hl hr (TR h).source.rawMass_nonneg
          (mul_nonneg UL.constant_nonneg (Real.rpow_nonneg hz.le _))
      _ = (UL.constant * UR.constant) * Z ^ (UL.exponent + UR.exponent) := by
        rw [Real.rpow_add hz UL.exponent UR.exponent]
        ac_rfl
      _ = _ := by rw [hexponent]
  have hb := exceptionalTerminal_selected_contribution (A := A) (V := V) (σ := σ)
    (η := η) (hS := hS)
    HL HR ε maskExponent hε hmask (ι := ι) (HRows := R.exceptionalRows Q)
  have hp := hb C R.primes R.primes_injective R.leftMultiplicity R.rightMultiplicity
    (Finset.univ : Finset (R.exceptionalRows Q))
    (fun h => R.originalIdeal h.val.val) (fun h => R.frequency h.val.val)
    (fun h => R.exceptionalRow C h.val) base
    (fun h => R.factor C h.val.val) (fun h => -R.factor C h.val.val)
    Z Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ v vStar
    r₁ r₂ divisorLower slotError sectors (UL.constant * UR.constant) height stepσ δ
    hZ hv hr₁ hdivisor hsectors (mul_nonneg UL.constant_nonneg UR.constant_nonneg) hheight
    (fun h _ => hclass h) (fun h _ => hfactor h) (fun h _ => hwindow h)
    (fun h _ => hcutoff h) hfiber hF₁ hF₂ hvsum
    (fun h => (TL h).source) (fun h => (TR h).source)
    (fun h _ => hmask0 h) (fun h _ => hmasknorm h) (fun h _ => htime h)
    (fun h _ => hminimum h) (fun h _ => hnormal h)
  have hw := R.weighted_correlation_norm_le_of_windows C hm (R.rows.filter Q.exceptional)
    Z g₂ t₂ rowAmplitude hz hrowAmplitude hgcd hunit hweight
  have hs := left.centered_pair_magnitude_le_exceptionalValues right EL ER
    (R.exceptionalRows Q) ξ TL TR (rowAmplitude * Z ^ (g₂ - t₂))
    (fun h => hw h.val.val (R.exceptionalRows_original_mem Q h))
  dsimp only
  have hrow0 : 0 ≤ rowAmplitude * Z ^ (g₂ - t₂) /
      (Real.sqrt left.normalizationScale * Real.sqrt right.normalizationScale) := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hp hrow0
  apply (mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hz.le _)).trans
  convert hmul using 1 <;>
    (try dsimp only [exceptionalTerminalConstant, exceptionalTerminalOrder]) <;> ring

end SecondSideFrame

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.exceptional_magnitude_terminal_from_atoms
