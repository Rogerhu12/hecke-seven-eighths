import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OrdinaryActualExceptionalTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalRelativeBudget

/-!
# Ordinary exceptional columns with their original relative scalar

The actual common atoms, original-ideal fibres, orbital radius and both
Gauss normalizers pay the original relative normalization. The result
keeps the true second-divisor dyad for its same-carrier sum.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis HeckePort.Moments
open HeckeGeneral.Analysis.ConditionalMoments CommonSupportMass
open UniqueFactorizationMonoid

private theorem ordinary_exceptional_relative_scalar
    (Z magnitude rowFactor envelope radical C childWidth actualWidth parentWidth
      remaining widthError margin divisorLower : ℝ)
    (hZ : 1 ≤ Z) (hC : 0 ≤ C) (henvelope : 0 ≤ envelope) (hradical : 0 ≤ radical)
    (hsource : Z ^ (-childWidth) * magnitude ≤
      rowFactor * C * Z ^ (margin - divisorLower))
    (hrow : rowFactor * Z ^ actualWidth / Z ^ parentWidth ≤
      envelope * Z ^ remaining / radical)
    (hwidth : childWidth - actualWidth ≤ widthError) :
    magnitude / Z ^ parentWidth ≤
      envelope * C * Z ^ (remaining + widthError + margin) / radical * Z ^ (-divisorLower) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hpowc : Z ^ childWidth ≠ 0 := (Real.rpow_pos_of_pos hz _).ne'
  have hpowp : Z ^ parentWidth ≠ 0 := (Real.rpow_pos_of_pos hz _).ne'
  have hscale := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsource (Real.rpow_nonneg hz.le childWidth))
    (Real.rpow_nonneg hz.le parentWidth)
  have hrecover : Z ^ childWidth * (Z ^ (-childWidth) * magnitude) / Z ^ parentWidth =
      magnitude / Z ^ parentWidth := by
    rw [Real.rpow_neg hz.le]
    field_simp [hpowc, hpowp] <;> ring
  rw [hrecover] at hscale
  have hsplit : Z ^ childWidth = Z ^ actualWidth * Z ^ (childWidth - actualWidth) := by
    rw [← Real.rpow_add hz]
    congr 1
    ring
  calc
    _ ≤ Z ^ childWidth * (rowFactor * C * Z ^ (margin - divisorLower)) / Z ^ parentWidth := hscale
    _ = (rowFactor * Z ^ actualWidth / Z ^ parentWidth) * C *
        Z ^ ((childWidth - actualWidth) + (margin - divisorLower)) := by
      rw [hsplit, Real.rpow_add hz]
      ring
    _ ≤ (envelope * Z ^ remaining / radical) * C *
        Z ^ (widthError + (margin - divisorLower)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hrow hC)
        (Real.rpow_le_rpow_of_exponent_le hZ (add_le_add hwidth le_rfl))
        (Real.rpow_nonneg hz.le _)
        (mul_nonneg (div_nonneg (mul_nonneg henvelope (Real.rpow_nonneg hz.le _)) hradical) hC)
    _ = _ := by
      simp only [Real.rpow_add hz, Real.rpow_sub hz, Real.rpow_neg hz.le]
      ring

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable [IsPrincipalIdealRing A.R]
variable {C : A.GeneralArithmeticContext σ η hS}
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {kCommonLeft kCommonRight : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray] {k l : ℕ}
variable {ΨL ΨR : Ideal (𝓞 F) →* ℂ} {WL₁ WL₂ WR₁ WR₂ : ℝ → ℂ}
variable (HL : ExceptionalVolumeControl ΨL WL₁ WL₂) (HR : ExceptionalVolumeControl ΨR WR₁ WR₂)

namespace SecondSideFrame

theorem ordinary_exceptional_relative_terminal_from_atoms
    (left : SecondSideFrame (V := V) C R Ray .left k)
    (right : SecondSideFrame (V := V) C R Ray .right l)
    (W : ActualSecondRowMass R C kCommonLeft kCommonRight)
    {theta : Finset (HeckeCharacter F)} (Q : PairedFiniteCharacters theta H) (ξ : V)
    (TL : ∀ h : R.exceptionalRows Q, left.source.OrdinaryExceptionalAt (σ := σ) ΨL WL₁ WL₂ ξ h.val)
    (TR : ∀ h : R.exceptionalRows Q, right.source.OrdinaryExceptionalAt (σ := σ) ΨR WR₁ WR₂ ξ h.val)
    (UL : ExceptionalAtomicScales left.allocation) (UR : ExceptionalAtomicScales right.allocation)
    (Z Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ v
      r₁ r₂ divisorLower slotError stepσ δ parentWidth remaining rowError widthError : ℝ)
    (hZ : 1 < Z) (hv : 0 ≤ v) (hr₁ : 0 ≤ r₁) (hdivisor : divisorLower - r₂ ≤ slotError)
    (hA : Aexp ≤ 5 * (m + q) / 6) (hc : 0 ≤ c) (hw : 0 ≤ w) (hb₂ : 0 ≤ b₂)
    (hleftAtoms : ∀ h, (TL h).source.AtomicControl Z UL)
    (hrightAtoms : ∀ h, (TR h).source.AtomicControl Z UR)
    (hexponent : UL.exponent + UR.exponent = Aexp - c - w - b₂ - r₁ - r₂)
    (hgcd : (Ideal.absNorm (gcd W.leftIdeal W.rightIdeal) : ℝ) ≤ Z ^ g₂)
    (hunit : Z ^ t₂ ≤ A.exteriorNorm W.unitIdeal)
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
    (hF₁ : 2 * (c + w) / 3 - 3 * stepσ - 5 * δ / 6 ≤
      firstSaving c (d + (2 * Aexp - c - d + R₀ + E₀ - m) - K)
        w (q + R₀ + E₀) wo Bcommon g ell)
    (hF₂ : 2 * b₂ / 3 ≤ 2 * b₂ - 5 * g₂ / 6 - p₂ + t₂ + V₀ / 6 + (2 * v) / 6)
    (hradius : Z ^ (-K - g) ≤
      W.radius.val * (sIntegerElementNorm F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
        (sIntegerMaskGenerator F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) W.mask)).val)
    (hcentral : Z ^ (Aexp - c - w) ≤
      Real.sqrt left.normalizationScale * Real.sqrt right.normalizationScale)
    (hdyad : g₂ - t₂ ≤ idealLogLength Z (gcd W.leftIdeal W.rightIdeal) -
      idealLogLength Z W.unitIdeal.val + rowError)
    (hremaining : (Aexp - c - w) + (q + R₀ + E₀) + w + Bcommon + wo + ell + rowError -
      parentWidth ≤ remaining)
    (hwidth :
      ((2 * (Aexp - c - w) - K - g - g₂ - V₀) +
        (q + R₀ + E₀ + wo + t₂ + V₀) + (b₂ - p₂ + w + Bcommon + ell)) -
      (secondCommonChildWidth Z (Aexp - c - w) (q + R₀ + E₀) wo K g
          W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val +
        secondCommonChildAllowance Z w Bcommon ell W.leftIdeal W.rightIdeal) ≤ widthError) :
    jointColumnPairMagnitude (R.exceptionalRows Q) left.allocation.columns right.allocation.columns
        (fun h : R.live => R.weight h.val * R.correlation h.val)
        (fun h => left.coefficient h.val)
        (fun h => right.coefficient h.val)
        (fun h => rawSourceLocation (left.leftLocation h.val) (left.rightLocation h.val)
          (left.slotLocation h.val))
        (fun h => rawSourceLocation (right.leftLocation h.val) (right.rightLocation h.val)
          (right.slotLocation h.val)) ξ / Z ^ parentWidth ≤
      (W.commonEnvelope * orbitalFieldFactor F) *
        ((W.originalFiber : ℝ) * ordinaryExceptionalConstant HL HR * (UL.constant * UR.constant)) *
        Z ^ (remaining + widthError + (3 * stepσ + 5 * δ / 6 + slotError)) /
        (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ) * Z ^ (-divisorLower) := by
  have hsource := ordinary_exceptional_magnitude_terminal_from_atoms
    (HL := HL) (HR := HR)
    left right Q ξ TL TR UL UR
    Z Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ v
    r₁ r₂ divisorLower slotError (W.originalFiber : ℝ) stepσ δ W.originalRowAmplitude
    hZ.le hv hr₁ hdivisor (Nat.cast_nonneg _) W.originalRowAmplitude_nonneg
    hA hc hw hb₂ hleftAtoms hrightAtoms hexponent W.left_positive hgcd
    (fun h hh => by rw [W.unit_ideal h (Finset.mem_filter.mp hh).1]; exact hunit)
    (fun h hh => W.original_row_weight_bound h (Finset.mem_filter.mp hh).1)
    base hclass hfactor hwindow hcutoff (W.exceptional_extracted_fibers Q) hF₁ hF₂
  have hrow := W.original_rowFactor_budget_relative_allowance Z hZ
    (Aexp - c - w) (q + R₀ + E₀) wo w Bcommon K g ell
    left.normalizationScale right.normalizationScale parentWidth remaining g₂ t₂ rowError
    hradius hcentral hdyad hremaining
  let Cvolume := (W.originalFiber : ℝ) * ordinaryExceptionalConstant HL HR *
    (UL.constant * UR.constant)
  have hCvolume : 0 ≤ Cvolume :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ordinaryExceptionalConstant_pos HL HR).le)
      (mul_nonneg UL.constant_nonneg UR.constant_nonneg)
  apply ordinary_exceptional_relative_scalar Z _ _ (W.commonEnvelope * orbitalFieldFactor F) _
    Cvolume _ _ parentWidth remaining widthError _ divisorLower hZ.le hCvolume
    (mul_nonneg W.commonEnvelope_nonneg (orbitalFieldFactor_nonneg F)) (Nat.cast_nonneg _)
    _ hrow hwidth
  dsimp only at hsource
  convert hsource using 1 <;> dsimp only [Cvolume] <;> ring

end SecondSideFrame
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.ordinary_exceptional_relative_terminal_from_atoms

