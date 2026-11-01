import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualExceptionalTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalRowScalar
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalSameCarrierMass

/-!
# Actual exceptional atoms pay their original row normalization

The original frozen common atoms supply the row amplitude.  The actual
original-ideal fibre bound supplies the exceptional residual fibre bound.
The centered volume estimate and valuation count are then applied to
the same two allocated source columns.  Finally the two original Gauss
normalizers, true orbital radius and first normalization are canceled.

The output retains the actual second-divisor dyad, ready for the proved
same-carrier harmonic mass.  No exceptional norm, summed row bound,
terminal bound, or source-to-child inequality is a primitive input.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis HeckePort.Moments
open HeckeGeneral.Analysis.ConditionalMoments CommonSupportMass
open UniqueFactorizationMonoid

private theorem exceptional_relative_scalar
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

namespace ActualSecondRowMass

/-- Filtering to exceptional rows creates no new ideal fibre.  The
bound is inherited from the actual original-ideal fibres through the
proved extracted-ideal identity. -/
theorem exceptional_extracted_fibers (W : ActualSecondRowMass R C kCommonLeft kCommonRight)
    {theta : Finset (HeckeCharacter F)} (Q : PairedFiniteCharacters theta H)
    (I : Ideal (𝓞 F))
    (hI : I ∈ (Finset.univ : Finset (R.exceptionalRows Q)).image
      (fun h => (R.extractedRow C h.val).ideal.val)) :
    (((Finset.univ : Finset (R.exceptionalRows Q)).filter
      (fun h => (R.extractedRow C h.val).ideal.val = I)).card : ℝ) ≤ W.originalFiber := by
  obtain ⟨h, hh, hI⟩ := Finset.mem_image.mp hI
  let J : HeckeGeneral.Analysis.NonzeroIdeal F := (R.extractedRow C h.val).momentIdeal
  let selected : Finset (R.exceptionalRows Q) := Finset.univ.filter
    (fun h => (R.extractedRow C h.val).ideal.val = I)
  have hincl : selected.image (fun h => h.val) ⊆
      (Finset.univ : Finset R.live).filter (fun h => (R.extractedRow C h).momentIdeal = J) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    exact (Finset.mem_filter.mp hy).2.trans hI.symm
  have hcard := (Finset.card_le_card hincl).trans (W.extracted_fibers J)
  rw [Finset.card_image_of_injective selected Subtype.val_injective] at hcard
  exact_mod_cast hcard

end ActualSecondRowMass

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray] {k l : ℕ}
variable {ΨL ΨR : Ideal (𝓞 F) →* ℂ} {WL₁ WL₂ WR₁ WR₂ : ℝ → ℂ}
variable (HL : ExceptionalVolumeControl ΨL WL₁ WL₂) (HR : ExceptionalVolumeControl ΨR WR₁ WR₂)
variable (ε maskExponent : ℝ) (hε : 0 < ε) (hmask : 0 ≤ maskExponent)

namespace SecondSideFrame

/-- The actual exceptional columns now have the original relative
normalization and second common-radical weight.  The sole remaining
divisor factor is its genuine dyadic saving, not an assumed `1 / N(L)`.
All comparison inputs are single-atom or numerical-window data. -/
theorem exceptional_relative_terminal_from_atoms
    (left : SecondSideFrame (V := V) C R Ray .left k)
    (right : SecondSideFrame (V := V) C R Ray .right l)
    (EL : SecondCoefficientComparison left.dictionary)
    (ER : SecondCoefficientComparison right.dictionary)
    (W : ActualSecondRowMass R C kCommonLeft kCommonRight)
    {theta : Finset (HeckeCharacter F)} (Q : PairedFiniteCharacters theta H) (ξ : V)
    (TL : ∀ h : R.exceptionalRows Q, left.source.ExceptionalAt (σ := σ) EL.scale₁ EL.scale₂
      (fun _ => EL.leftWeight) (fun _ => EL.rightWeight) ΨL WL₁ WL₂ ξ h.val)
    (TR : ∀ h : R.exceptionalRows Q, right.source.ExceptionalAt (σ := σ) ER.scale₁ ER.scale₂
      (fun _ => ER.leftWeight) (fun _ => ER.rightWeight) ΨR WR₁ WR₂ ξ h.val)
    (UL : ExceptionalAtomicScales left.allocation) (UR : ExceptionalAtomicScales right.allocation)
    (Z Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ v vStar
      r₁ r₂ divisorLower slotError height stepσ δ parentWidth remaining rowError widthError : ℝ)
    (hZ : 1 < Z) (hv : 0 ≤ v) (hr₁ : 0 ≤ r₁) (hdivisor : divisorLower - r₂ ≤ slotError)
    (hheight : 0 ≤ height)
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
    (hvsum : vStar ≤ c + w + b₂)
    (hmask0 : ∀ h, (TL h).source.mask ≠ ⊥)
    (hmasknorm : ∀ h, (Ideal.absNorm (TL h).source.mask : ℝ) ≤ Z ^ maskExponent)
    (htime : ∀ h, ‖(TL h).source.time‖ ≤ height)
    (hminimum : ∀ h, Z ^ ((m + q) / 4 - vStar - r₁) ≤ (TL h).source.lower)
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
        (fun h => left.centeredCoefficient EL h.val)
        (fun h => right.centeredCoefficient ER h.val)
        (fun h => rawSourceLocation (left.leftLocation h.val) (left.rightLocation h.val)
          (left.slotLocation h.val))
        (fun h => rawSourceLocation (right.leftLocation h.val) (right.rightLocation h.val)
          (right.slotLocation h.val)) ξ / Z ^ parentWidth ≤
      (W.commonEnvelope * orbitalFieldFactor F) *
        ((W.originalFiber : ℝ) * exceptionalTerminalConstant (V := V) (σ := σ) (η := η) (hS := hS)
          HL HR ε maskExponent hε hmask * (UL.constant * UR.constant) *
          (1 + height) ^ exceptionalTerminalOrder (V := V) (σ := σ) (η := η) (hS := hS)
            HL HR ε maskExponent hε hmask) *
        Z ^ (remaining + widthError +
          (max (Aexp - (m + q)) 0 + 3 * stepσ + 5 * δ / 6 + ε + slotError)) /
        (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ) * Z ^ (-divisorLower) := by
  have hsource := exceptional_magnitude_terminal_from_atoms
    (HL := HL) (HR := HR) (ε := ε) (maskExponent := maskExponent) (hε := hε) (hmask := hmask)
    left right EL ER Q ξ TL TR UL UR
    Z Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ v vStar
    r₁ r₂ divisorLower slotError (W.originalFiber : ℝ) height stepσ δ W.originalRowAmplitude
    hZ.le hv hr₁ hdivisor (Nat.cast_nonneg _) hheight W.originalRowAmplitude_nonneg
    hleftAtoms hrightAtoms hexponent W.left_positive hgcd
    (fun h hh => by rw [W.unit_ideal h (Finset.mem_filter.mp hh).1]; exact hunit)
    (fun h hh => W.original_row_weight_bound h (Finset.mem_filter.mp hh).1)
    base hclass hfactor hwindow hcutoff (W.exceptional_extracted_fibers Q)
    hF₁ hF₂ hvsum hmask0 hmasknorm htime hminimum
  have hrow := W.original_rowFactor_budget_relative_allowance Z hZ
    (Aexp - c - w) (q + R₀ + E₀) wo w Bcommon K g ell
    left.normalizationScale right.normalizationScale parentWidth remaining g₂ t₂ rowError
    hradius hcentral hdyad hremaining
  let Cvolume := (W.originalFiber : ℝ) *
    exceptionalTerminalConstant (V := V) (σ := σ) (η := η) (hS := hS)
      HL HR ε maskExponent hε hmask * (UL.constant * UR.constant) *
    (1 + height) ^ exceptionalTerminalOrder (V := V) (σ := σ) (η := η) (hS := hS)
      HL HR ε maskExponent hε hmask
  have hCvolume : 0 ≤ Cvolume := by
    have hC := (exceptionalTerminalConstant_pos (V := V) (σ := σ) (η := η) (hS := hS)
      HL HR ε maskExponent hε hmask).le
    have hUL := UL.constant_nonneg
    have hUR := UR.constant_nonneg
    dsimp [Cvolume]
    positivity
  apply exceptional_relative_scalar Z _ _ (W.commonEnvelope * orbitalFieldFactor F) _
    Cvolume _ _ parentWidth remaining widthError _ divisorLower hZ.le hCvolume
    (mul_nonneg W.commonEnvelope_nonneg (orbitalFieldFactor_nonneg F)) (Nat.cast_nonneg _)
    _ hrow hwidth
  dsimp only at hsource
  convert hsource using 1 <;> dsimp only [Cvolume] <;> ring

end SecondSideFrame
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondRowMass.exceptional_extracted_fibers
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.exceptional_relative_terminal_from_atoms
