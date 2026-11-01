import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalFrames
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAllocatedWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralQuotientScales
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalExceptionalPlainWindows

/-!
# Windows for the actual literal exceptional frames

The Fourier height is the displayed linear expression in the two
original modes.  The complete mask is the original row ideal times
the full moving/remaining support, with the fixed S ideal included
once.  The two pre-allocation plain divisors are read from actual
occurrence labels. Their divisibility follows from the two atlas
product identities; no final exceptional window is an input.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalWindows

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open CanonicalLiteralExceptionalCharts

local notation "Joint" => WithLp 2 (ℝ × ℝ)

/-- Both original Fourier coordinates are retained. -/
theorem time_coordinates (firstSign : ℝ) (ξ : Joint) :
    time firstSign ξ = -(2 * Real.pi *
      ((WithLp.ofLp ξ).1 * firstSign + (WithLp.ofLp ξ).2)) := by
  simp only [time, CanonicalLiteralLocations.direction, WithLp.prod_inner_apply,
    WithLp.ofLp_toLp, Real.inner_apply, mul_one]

theorem time_neg (firstSign : ℝ) (ξ : Joint) :
    time firstSign (-ξ) = -time firstSign ξ := by
  simp only [time, inner_neg_left]
  ring

/-- Changing the whole column orientation does not change its height. -/
theorem orientedTime_abs (firstSign : ℝ) (negative : Bool) (ξ : Joint) :
    |time firstSign (orientedMode negative ξ)| = |time firstSign ξ| := by
  cases negative <;> simp only [orientedMode, Bool.false_eq_true, if_false,
    if_true, time_neg, abs_neg]

def fourierHeight (ξ : Joint) : ℝ :=
  2 * Real.pi * (|(WithLp.ofLp ξ).1| + |(WithLp.ofLp ξ).2|)

theorem fourierHeight_nonneg (ξ : Joint) : 0 ≤ fourierHeight ξ := by
  exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
    (add_nonneg (abs_nonneg _) (abs_nonneg _))

/-- The literal first signs are 1 and -1. The slightly more general
closed unit interval is useful when reading either original side. -/
theorem time_le_fourierHeight (firstSign : ℝ) (hsign : |firstSign| ≤ 1)
    (negative : Bool) (ξ : Joint) :
    |time firstSign (orientedMode negative ξ)| ≤ fourierHeight ξ := by
  rw [orientedTime_abs, time_coordinates, abs_neg, abs_mul,
    abs_of_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) Real.pi_pos.le)
  calc
    |(WithLp.ofLp ξ).1 * firstSign + (WithLp.ofLp ξ).2| ≤
        |(WithLp.ofLp ξ).1 * firstSign| + |(WithLp.ofLp ξ).2| := abs_add_le _ _
    _ = |(WithLp.ofLp ξ).1| * |firstSign| + |(WithLp.ofLp ξ).2| := by rw [abs_mul]
    _ ≤ _ := add_le_add_right
      (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hsign (abs_nonneg (WithLp.ofLp ξ).1)) _

theorem fourierHeight_polynomial (order : ℕ) (ξ : Joint) :
    (1 + fourierHeight ξ) ^ order ≤
      (1 + 2 * Real.pi) ^ order *
        (1 + ‖(WithLp.ofLp ξ).1‖) ^ order *
        (1 + ‖(WithLp.ofLp ξ).2‖) ^ order := by
  have hp : 0 ≤ 2 * Real.pi := mul_nonneg (by norm_num) Real.pi_pos.le
  have hx := abs_nonneg (WithLp.ofLp ξ).1
  have hy := abs_nonneg (WithLp.ofLp ξ).2
  have hsum : 1 + fourierHeight ξ ≤
      (1 + 2 * Real.pi) *
        ((1 + |(WithLp.ofLp ξ).1|) * (1 + |(WithLp.ofLp ξ).2|)) := by
    calc
      _ ≤ (1 + 2 * Real.pi) *
          (1 + |(WithLp.ofLp ξ).1| + |(WithLp.ofLp ξ).2|) := by
        dsimp only [fourierHeight]
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by nlinarith [mul_nonneg hx hy]) (by positivity)
  have h := pow_le_pow_left₀
    (add_nonneg zero_le_one (fourierHeight_nonneg ξ)) hsum order
  simpa only [mul_pow, Real.norm_eq_abs, mul_assoc] using h

/-- Multiplying the original profile polynomial by the time growth
only increases the two original Fourier orders. Its amplitude remains
the displayed original P; it is not hidden in a new constant. -/
theorem profile_time_polynomial (P : ℝ) (hP : 0 ≤ P)
    (degree J₁ J₂ order : ℕ) (ξ : Joint) :
    (P * (1 + ‖(WithLp.ofLp ξ).1‖) ^ J₁ *
        (1 + ‖(WithLp.ofLp ξ).2‖) ^ J₂) ^ degree *
        (1 + fourierHeight ξ) ^ order ≤
      (1 + 2 * Real.pi) ^ order * P ^ degree *
        (1 + ‖(WithLp.ofLp ξ).1‖) ^ (J₁ * degree + order) *
        (1 + ‖(WithLp.ofLp ξ).2‖) ^ (J₂ * degree + order) := by
  calc
    _ ≤ (P * (1 + ‖(WithLp.ofLp ξ).1‖) ^ J₁ *
          (1 + ‖(WithLp.ofLp ξ).2‖) ^ J₂) ^ degree *
        ((1 + 2 * Real.pi) ^ order *
          (1 + ‖(WithLp.ofLp ξ).1‖) ^ order *
          (1 + ‖(WithLp.ofLp ξ).2‖) ^ order) :=
      mul_le_mul_of_nonneg_left (fourierHeight_polynomial order ξ) (by positivity)
    _ = _ := by simp only [mul_pow, pow_add, pow_mul]; ring

variable {K : Type} [Field K] [NumberField K]

/-- The fixed S factor is absorbed at an explicit threshold, without
claiming that it equals one. This bound is uniform in all row data. -/
theorem fixed_mask_threshold {A : SArithmeticData K} (Z width : ℝ)
    (hZ : max 2 (Ideal.absNorm A.cS : ℝ) ≤ Z) :
    (Ideal.absNorm A.cS : ℝ) * Z ^ width ≤ Z ^ (width + 1) := by
  have hz : 0 < Z := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
    ((le_max_left _ _).trans hZ)
  calc
    _ ≤ Z * Z ^ width := mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans hZ) (Real.rpow_nonneg hz.le _)
    _ = _ := by rw [Real.rpow_add hz, Real.rpow_one]; ring

section ActualPreDivisors

variable {A : SArithmeticData K} {ι : Type*}
variable {columns : Finset ι} {ideal : ι → A.Exterior}

/-- The first plain divisor belongs to the actual extracted whole
ideal, by the stored original occurrence product. -/
theorem atlas_plain_left_dvd (T : SourceCartesianAtlas columns ideal)
    (support : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K)) (label : T.labels support D) :
    (T.branch support D label).plainDivisor₁.val ∣ D := by
  refine ⟨(T.branch support D label).plainExtract₂ *
    ∏ i, (T.branch support D label).slotExtract i, ?_⟩
  simpa only [SupportCartesianBranch.plainDivisor₁, mul_assoc] using
    (T.branch_product support D label).symm

theorem atlas_plain_right_dvd (T : SourceCartesianAtlas columns ideal)
    (support : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K)) (label : T.labels support D) :
    (T.branch support D label).plainDivisor₂.val ∣ D := by
  refine ⟨(T.branch support D label).plainExtract₁ *
    ∏ i, (T.branch support D label).slotExtract i, ?_⟩
  simpa only [SupportCartesianBranch.plainDivisor₂, mul_assoc, mul_left_comm, mul_comm] using
    (T.branch_product support D label).symm

variable {κ : Type*} {columns₂ : Finset κ} {ideal₂ : κ → A.Exterior}
variable {a : RealParameters} {Z step : ℝ}
variable (G : OriginalNominalGeometry (K := K) a Z step)
variable (first : SourceCartesianAtlas columns ideal)
variable (second : SourceCartesianAtlas columns₂ ideal₂)
variable (firstSupport secondSupport : Finset (Ideal (𝓞 K)))
variable (firstLabel : first.labels firstSupport
  (G.ideals.first * G.tag.extractionIdeal).val)
variable (secondLabel : second.labels secondSupport G.centeredSecondIdeal.val)

local notation "b₁" => first.branch firstSupport
  (G.ideals.first * G.tag.extractionIdeal).val firstLabel
local notation "b₂" => second.branch secondSupport G.centeredSecondIdeal.val secondLabel

/-- Pool errors use their complete first common ideal, including the
actual removed prime power. The second atlas is the smaller actual
common side selected by the original geometry. -/
theorem actual_preDivisors_dvd :
    (b₁.plainDivisor₁ * b₂.plainDivisor₁).val ∣ G.centeredCommonIdeal.val ∧
      (b₁.plainDivisor₂ * b₂.plainDivisor₂).val ∣ G.centeredCommonIdeal.val := by
  constructor
  · exact mul_dvd_mul (atlas_plain_left_dvd first _ _ firstLabel)
      (atlas_plain_left_dvd second _ _ secondLabel)
  · exact mul_dvd_mul (atlas_plain_right_dvd first _ _ firstLabel)
      (atlas_plain_right_dvd second _ _ secondLabel)

/-- The complete four quotient minimum follows from the original
domain and the two original occurrence labels. No bound on either
pre-divisor or on the final minimum is assumed. -/
theorem actual_fourPlain_minimum {k : ℕ} (B : ActualColumnAllocation K k)
    {ω ψ : HeckeCharacter K} {parent : MomentData K ω ψ}
    {Y₁ Y₂ floor padding : ℝ}
    (domain : PairedEngineDomain true parent a Z Y₁ Y₂ floor padding)
    (length : Fin k → ℝ) (hlength : ∀ i, 0 ≤ length i) :
    Z ^ ((a.m + a.q) / 4 - G.centeredExtractionLength -
      B.rawExtractionLength Z length) ≤
      B.fourPlainLower
        (Z ^ a.n₁ / idealNorm K (b₁.plainDivisor₁ * b₂.plainDivisor₁))
        (Z ^ a.n₂ / idealNorm K (b₁.plainDivisor₂ * b₂.plainDivisor₂))
        (Y₁ / idealNorm K (b₁.plainDivisor₁ * b₂.plainDivisor₁))
        (Y₂ / idealNorm K (b₁.plainDivisor₂ * b₂.plainDivisor₂)) := by
  have hp := actual_preDivisors_dvd G first second firstSupport secondSupport
    firstLabel secondLabel
  exact G.fourPlain_minimum_window_of_domain B domain _ _ hp.1 hp.2 length hlength

end ActualPreDivisors

section LiteralQuotients

variable {A : SArithmeticData K} {σ : K →+* ℂ} {k : ℕ}
variable (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable {support₁ : Finset (Ideal (𝓞 K))}
variable (b₁ : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support₁)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (power firstFixed poolFixed unitFixed : A.Exterior)
variable (firstElement poolElement unitElement : A.R)
variable (hfirst : A.Generates firstFixed firstElement)
variable (hpool : A.Generates poolFixed poolElement)
variable (hunit : A.Generates unitFixed unitElement)
variable (δ₁ δ₂ : ℝ)

local notation "beforeSecond" => d.secondInput (σ := σ) b₁ P R
  power firstFixed poolFixed unitFixed firstElement poolElement unitElement
    hfirst hpool hunit δ₁ δ₂

variable {support₂ : Finset (Ideal (𝓞 K))}
variable (b₂ : SupportCartesianBranch beforeSecond.plain₁ beforeSecond.plain₂
  beforeSecond.slots support₂)

/-- The real first phase/norm constructor leaves the formal scale
unchanged. Its two literal extractions give exactly this quotient. -/
theorem actual_twice_left_scale (rectangle : Bool) :
    (beforeSecond.extract b₂).scale₁ rectangle =
      d.scale₁ rectangle / idealNorm K (b₁.plainDivisor₁ * b₂.plainDivisor₁) := by
  change (d.scale₁ rectangle / idealNorm K b₁.plainDivisor₁) /
      idealNorm K b₂.plainDivisor₁ = _
  rw [CanonicalLiteralProfileData.idealNorm_mul, div_div]

theorem actual_twice_right_scale (rectangle : Bool) :
    (beforeSecond.extract b₂).scale₂ rectangle =
      d.scale₂ rectangle / idealNorm K (b₁.plainDivisor₂ * b₂.plainDivisor₂) := by
  change (d.scale₂ rectangle / idealNorm K b₁.plainDivisor₂) /
      idealNorm K b₂.plainDivisor₂ = _
  rw [CanonicalLiteralProfileData.idealNorm_mul, div_div]

variable {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior}
variable (atlas : SourceCartesianAtlas columns ideal) (count : b₂.keep.card = atlas.slotCount)
variable (scalar : ℂ) (balance : Bool → ℝ)

/-- The actual atlas transport, common scalar extraction and plain
balance retain this same quotient; no profile nonvanishing is used. -/
theorem actual_final_left_scale (rectangle : Bool) :
    ((((beforeSecond.extract b₂).onAtlas atlas count).scale scalar).balancePlain balance).scale₁
        rectangle =
      d.scale₁ rectangle / idealNorm K (b₁.plainDivisor₁ * b₂.plainDivisor₁) := by
  change ((beforeSecond.extract b₂).onAtlas atlas count).scale₁ rectangle = _
  rw [CanonicalLiteralRectangles.Atoms.onAtlas_left_scale]
  exact actual_twice_left_scale d b₁ P R power firstFixed poolFixed unitFixed
    firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ b₂ rectangle

theorem actual_final_right_scale (rectangle : Bool) :
    ((((beforeSecond.extract b₂).onAtlas atlas count).scale scalar).balancePlain balance).scale₂
        rectangle =
      d.scale₂ rectangle / idealNorm K (b₁.plainDivisor₂ * b₂.plainDivisor₂) := by
  change ((beforeSecond.extract b₂).onAtlas atlas count).scale₂ rectangle = _
  rw [CanonicalLiteralRectangles.Atoms.onAtlas_right_scale]
  exact actual_twice_right_scale d b₁ P R power firstFixed poolFixed unitFixed
    firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ b₂ rectangle

end LiteralQuotients

section Frames

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable {ω ψ : HeckeCharacter K}
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable (C : A.GeneralArithmeticContext σ η hS)
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (S : ActualSecondCorrelationRows A σ H ι) (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (hone : (1 : HeckeCharacter K) ∈ parent.theta)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (row : CanonicalOriginalPhaseCalibration.PatternSector P S C pattern ν)
variable {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (recipe : CanonicalLiteralActualCharacters.Recipe P R F parent oldMoving
  correction remaining extra d)
variable {W : d.ProfileData} {window : Set ℝ} (E : W.SchwartzModel window)
variable (firstSupport : Finset (Ideal (𝓞 K)))
variable (hfirst : ∀ q ∈ firstSupport, Prime q)
variable (hextra : extra = literalDeletionIdeal firstSupport hfirst)
variable (hm : ∀ i, 0 < S.leftMultiplicity i) (hn : ∀ i, 0 < S.rightMultiplicity i)
variable (support : d.SupportData ((primeSupport A.cS ∪ firstSupport) ∪
  primeSupport (primePowerProduct S.primes S.leftMultiplicity).val))
variable (side : SecondColumnSide) (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
variable (ideal : AllocationColumn K k → A.Exterior)
variable (hideal : ∀ i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots,
  (ideal i).val = allocationColumnIdeal i)
variable (firstSign : ℝ) (L : Ideal (𝓞 K))
variable (selection : primeSupport L → Finset (Fin (k + 2)))
variable (hne : (pairedAllocatedColumns L selection d.plain₁ d.plain₂ d.slots
  id id HeightOneSpectrum.asIdeal).Nonempty)
variable (θ : parent.theta)
variable (hθ : S.literalCharacter C P R F oldMoving correction pattern ν
  row.val.val.val = θ.val)

local notation "frame" =>
  (d.factors S side χ ideal hideal firstSign false).frame C L selection hne
local notation "actualMask" => CanonicalLiteralExceptionalCharacters.rowMask
  P R F oldMoving C S.primes S.leftMultiplicity S.rightMultiplicity pattern
    (remaining * extra) (S.extractedRow C row.val.val).momentIdeal
local notation "centeredFrame" => CanonicalLiteralExceptionalFrames.centeredAtTheta
  P R F parent oldMoving correction hcorr C S pattern ν remaining extra hone hroot hemb
  row recipe E firstSupport hfirst hextra hm hn support side χ ideal hideal firstSign
  L selection hne θ hθ
local notation "ordinaryFrame" => CanonicalLiteralExceptionalFrames.ordinaryAtTheta
  P R F parent oldMoving correction hcorr C S pattern ν remaining extra hone hroot hemb
  row recipe E firstSupport hfirst hextra hm hn support side χ ideal hideal firstSign
  L selection hne θ hθ

/-- Catalogue transport preserves the three explicitly computed
window fields of this actual centered frame. -/
theorem centered_fields (hc : SamePlainProfiles E)
    (hscale : d.scale₁ true * d.scale₂ true = d.scale₁ false * d.scale₂ false)
    (ξ : Joint) :
    (centeredFrame hc hscale ξ).source.mask = actualMask ∧
      (centeredFrame hc hscale ξ).source.time =
        time firstSign (orientedMode side.literalNegative ξ) ∧
      (centeredFrame hc hscale ξ).source.lower =
        frame.allocation.fourPlainLower
          (d.scale₁ false) (d.scale₂ false) (d.scale₁ true) (d.scale₂ true) := by
  rcases θ with ⟨θ, hmem⟩
  dsimp only at hθ
  subst θ
  cases side <;> exact ⟨rfl, rfl, rfl⟩

theorem ordinary_fields (ξ : Joint) :
    (ordinaryFrame ξ).source.mask = actualMask ∧
      (ordinaryFrame ξ).source.time =
        time firstSign (orientedMode side.literalNegative ξ) ∧
      (ordinaryFrame ξ).source.lower =
        min (d.scale₁ false / idealNorm K (frame.allocation.plainDivisor 0))
          (d.scale₂ false / idealNorm K (frame.allocation.plainDivisor (Fin.succ 0))) := by
  rcases θ with ⟨θ, hmem⟩
  dsimp only at hθ
  subst θ
  cases side <;> exact ⟨rfl, rfl, rfl⟩

theorem centered_mask_ne_zero (hc : SamePlainProfiles E)
    (hscale : d.scale₁ true * d.scale₂ true = d.scale₁ false * d.scale₂ false)
    (ξ : Joint) : (centeredFrame hc hscale ξ).source.mask ≠ 0 := by
  rw [(centered_fields P R F parent oldMoving correction hcorr C S pattern ν
    remaining extra hone hroot hemb row recipe E firstSupport hfirst hextra hm hn support
    side χ ideal hideal firstSign L selection hne θ hθ hc hscale ξ).1]
  exact CanonicalLiteralExceptionalCharacters.rowMask_ne_zero _ _ _ _ _ _ _ _ _ _ _

theorem ordinary_mask_ne_zero (ξ : Joint) : (ordinaryFrame ξ).source.mask ≠ 0 := by
  rw [(ordinary_fields P R F parent oldMoving correction hcorr C S pattern ν
    remaining extra hone hroot hemb row recipe E firstSupport hfirst hextra hm hn support
    side χ ideal hideal firstSign L selection hne θ hθ ξ).1]
  exact CanonicalLiteralExceptionalCharacters.rowMask_ne_zero _ _ _ _ _ _ _ _ _ _ _

/-- The variable factor is exactly the already paid full joint row
budget, not a second or enlarged support norm. -/
theorem centered_mask_norm (hc : SamePlainProfiles E)
    (hscale : d.scale₁ true * d.scale₂ true = d.scale₁ false * d.scale₂ false)
    (ξ : Joint) :
    (Ideal.absNorm (centeredFrame hc hscale ξ).source.mask : ℝ) =
      (Ideal.absNorm A.cS : ℝ) *
        (idealNorm K (S.extractedRow C row.val.val).momentIdeal *
          idealNorm K (((F.moving P R oldMoving).appendSecondFactor C S.primes
            S.leftMultiplicity S.rightMultiplicity pattern).fullMaskSupport
              (remainingMaskIdeal A (remaining * extra) *
                exteriorMomentIdeal (secondSixthRootIdeal S.primes
                  S.leftMultiplicity S.rightMultiplicity)))) := by
  rw [(centered_fields P R F parent oldMoving correction hcorr C S pattern ν
    remaining extra hone hroot hemb row recipe E firstSupport hfirst hextra hm hn support
    side χ ideal hideal firstSign L selection hne θ hθ hc hscale ξ).1]
  exact CanonicalLiteralExceptionalCharacters.completeMask_norm _ _ _

theorem ordinary_mask_norm (ξ : Joint) :
    (Ideal.absNorm (ordinaryFrame ξ).source.mask : ℝ) =
      (Ideal.absNorm A.cS : ℝ) *
        (idealNorm K (S.extractedRow C row.val.val).momentIdeal *
          idealNorm K (((F.moving P R oldMoving).appendSecondFactor C S.primes
            S.leftMultiplicity S.rightMultiplicity pattern).fullMaskSupport
              (remainingMaskIdeal A (remaining * extra) *
                exteriorMomentIdeal (secondSixthRootIdeal S.primes
                  S.leftMultiplicity S.rightMultiplicity)))) := by
  rw [(ordinary_fields P R F parent oldMoving correction hcorr C S pattern ν
    remaining extra hone hroot hemb row recipe E firstSupport hfirst hextra hm hn support
    side χ ideal hideal firstSign L selection hne θ hθ ξ).1]
  exact CanonicalLiteralExceptionalCharacters.completeMask_norm _ _ _

theorem centered_time_window (hsign : |firstSign| ≤ 1) (hc : SamePlainProfiles E)
    (hscale : d.scale₁ true * d.scale₂ true = d.scale₁ false * d.scale₂ false)
    (ξ : Joint) : |(centeredFrame hc hscale ξ).source.time| ≤ fourierHeight ξ := by
  rw [(centered_fields P R F parent oldMoving correction hcorr C S pattern ν
    remaining extra hone hroot hemb row recipe E firstSupport hfirst hextra hm hn support
    side χ ideal hideal firstSign L selection hne θ hθ hc hscale ξ).2.1]
  exact time_le_fourierHeight firstSign hsign side.literalNegative ξ

theorem ordinary_time_window (hsign : |firstSign| ≤ 1) (ξ : Joint) :
    |(ordinaryFrame ξ).source.time| ≤ fourierHeight ξ := by
  rw [(ordinary_fields P R F parent oldMoving correction hcorr C S pattern ν
    remaining extra hone hroot hemb row recipe E firstSupport hfirst hextra hm hn support
    side χ ideal hideal firstSign L selection hne θ hθ ξ).2.1]
  exact time_le_fourierHeight firstSign hsign side.literalNegative ξ

variable {a : RealParameters} {Z step Y₁ Y₂ floor padding : ℝ}
variable (G : OriginalNominalGeometry (K := K) a Z step)
variable {α β : Type*} {columns₁ : Finset α} {columns₂ : Finset β}
variable {ideal₁ : α → A.Exterior} {ideal₂ : β → A.Exterior}
variable (first : SourceCartesianAtlas columns₁ ideal₁)
variable (second : SourceCartesianAtlas columns₂ ideal₂)
variable (support₁ support₂ : Finset (Ideal (𝓞 K)))
variable (label₁ : first.labels support₁ (G.ideals.first * G.tag.extractionIdeal).val)
variable (label₂ : second.labels support₂ G.centeredSecondIdeal.val)

local notation "b₁" => first.branch support₁ (G.ideals.first * G.tag.extractionIdeal).val label₁
local notation "b₂" => second.branch support₂ G.centeredSecondIdeal.val label₂

/-- Only the literal one-scale identities are used at this interface.
The two actual common products, all pre-divisor inequalities and the
final minimum are proved internally from the original labels/domain. -/
theorem centered_minimum_window
    (domain : PairedEngineDomain true parent a Z Y₁ Y₂ floor padding)
    (hscale₁ : ∀ r, d.scale₁ r =
      (if r then Y₁ else Z ^ a.n₁) / idealNorm K (b₁.plainDivisor₁ * b₂.plainDivisor₁))
    (hscale₂ : ∀ r, d.scale₂ r =
      (if r then Y₂ else Z ^ a.n₂) / idealNorm K (b₁.plainDivisor₂ * b₂.plainDivisor₂))
    (hc : SamePlainProfiles E)
    (hscale : d.scale₁ true * d.scale₂ true = d.scale₁ false * d.scale₂ false)
    (ξ : Joint) :
    Z ^ ((a.m + a.q) / 4 - G.centeredExtractionLength -
      frame.allocation.rawExtractionLength Z d.length) ≤
        (centeredFrame hc hscale ξ).source.lower := by
  rw [(centered_fields P R F parent oldMoving correction hcorr C S pattern ν
    remaining extra hone hroot hemb row recipe E firstSupport hfirst hextra hm hn support
    side χ ideal hideal firstSign L selection hne θ hθ hc hscale ξ).2.2,
    hscale₁ false, hscale₂ false, hscale₁ true, hscale₂ true]
  exact actual_fourPlain_minimum G first second support₁ support₂ label₁ label₂
    frame.allocation domain d.length (fun i => (d.length_pos i).le)

end Frames

section PhysicalMask

open MeasureTheory LocalFiniteSums

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {α β : Type*} {fullI : α → A.Exterior} {fullJ : β → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {C : A.GeneralArithmeticContext σ η hS} {left : Finset α} {right : Finset β}
variable {profiles : α → β → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}}
variable {D : (∅ : Finset (HeightOneSpectrum A.R)).powerset}
variable (chart : SecondBlockProfileChart (E := V) hΓ μv hDiff b C left right
  profiles finiteTest radius D.val)
variable (hclass : chart.NonunitLabelStable)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (oldMoving : OriginalMovingFactors A P R)
variable (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
variable (retainedScale Z g a₀ q wo cutoffExponent : ℝ)
variable (hscale : 0 < retainedScale) (hZ : 1 < Z)
variable (hradius : radius = CanonicalRowBall.gaussRadius retainedScale Z g hscale
  (zero_lt_one.trans hZ))
variable (hcutoff : X ≤ Z ^ cutoffExponent)
variable (hproduct : ∀ i ∈ left, ∀ j ∈ right, profiles i j ≠ 0 →
  (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤ Z ^ (2 * a₀))
variable (hold : A.exteriorNorm ((F.moving P R oldMoving).effectiveFullSupport remaining) ≤
  Z ^ (q + wo))

local notation "S" => chart.actualRows ∅ X hX label
local notation "pattern" => chart.originalNonunitPattern ∅ X hX label
local notation "width" =>
  secondCommonChildWidth Z a₀ q wo (Real.log retainedScale / Real.log Z) g
    (primePowerProduct b.primes b.leftMultiplicity).val
    (primePowerProduct b.primes b.rightMultiplicity).val
    (secondPatternUnitIdeal b.primes b.leftMultiplicity b.rightMultiplicity pattern).val
    (secondPatternNonunitIdeal b.primes pattern).val +
      idealLogLength Z (secondSixthRootIdeal b.primes
        b.leftMultiplicity b.rightMultiplicity).val + cutoffExponent

include hclass hradius hcutoff hproduct hold in
/-- The physical source supplies the complete joint budget on its
own live rows. The first deleted ideal is included in `remaining`
(literally `oldRemaining * extra` at the raw frame call site). -/
theorem actualRows_mask_norm_window (h : S.live) :
    (Ideal.absNorm (CanonicalLiteralExceptionalCharacters.rowMask P R F oldMoving C
      b.primes b.leftMultiplicity b.rightMultiplicity pattern remaining
        (S.extractedRow C h).momentIdeal) : ℝ) ≤
      (Ideal.absNorm A.cS : ℝ) * Z ^ (width) := by
  have hjoint := chart.actualRows_appended_active_pair_fullDeletion_joint_window hclass
    (F.moving P R oldMoving) remaining X hX label retainedScale Z g a₀ q wo cutoffExponent
    hscale hZ hradius hcutoff hproduct hold h
  exact CanonicalLiteralExceptionalCharacters.completeMask_norm_le _ _ _ _ hjoint

include hclass hradius hcutoff hproduct hold in
theorem actualRows_mask_power_window (hthreshold : max 2 (Ideal.absNorm A.cS : ℝ) ≤ Z)
    (h : S.live) :
    (Ideal.absNorm (CanonicalLiteralExceptionalCharacters.rowMask P R F oldMoving C
      b.primes b.leftMultiplicity b.rightMultiplicity pattern remaining
        (S.extractedRow C h).momentIdeal) : ℝ) ≤ Z ^ ((width) + 1) :=
  (actualRows_mask_norm_window chart hclass P R F oldMoving remaining X hX label
    retainedScale Z g a₀ q wo cutoffExponent hscale hZ hradius hcutoff hproduct hold h).trans
      (fixed_mask_threshold Z (width) hthreshold)

include hclass hradius hcutoff hproduct hold in
/-- Actual common-scalar reweighting and both original row
restrictions keep the arithmetic row and its complete mask. -/
theorem actualRestrictedRows_mask_norm_window
    (weight : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → ℂ)
    (keep₁ keep₂ : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Prop)
    (h : ((({ S with weight := weight }).restrictRows keep₁).restrictRows keep₂).live) :
    let T := (({ S with weight := weight }).restrictRows keep₁).restrictRows keep₂
    (Ideal.absNorm (CanonicalLiteralExceptionalCharacters.rowMask P R F oldMoving C
      T.primes T.leftMultiplicity T.rightMultiplicity pattern remaining
        (T.extractedRow C h).momentIdeal) : ℝ) ≤
      (Ideal.absNorm A.cS : ℝ) * Z ^ (width) := by
  let R₁ := { S with weight := weight }
  let R₂ := R₁.restrictRows keep₁
  let h₁ : R₂.live := R₂.liveInclusion keep₂ h
  let h₀ : S.live := R₁.liveInclusion keep₁ h₁
  exact actualRows_mask_norm_window chart hclass P R F oldMoving remaining X hX label
    retainedScale Z g a₀ q wo cutoffExponent hscale hZ hradius hcutoff hproduct hold h₀

end PhysicalMask

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalWindows

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalWindows.time_coordinates
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalWindows.profile_time_polynomial
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalWindows.actual_preDivisors_dvd
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalWindows.centered_fields
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalWindows.centered_minimum_window
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalWindows.actualRows_mask_norm_window
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalWindows.actualRestrictedRows_mask_norm_window
