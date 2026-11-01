import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalPaidOrdinaryRows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OrdinaryActualExceptionalTerminal

/-!
# The original ordinary exceptional magnitude with uniform constants

Fixed raw single-series primitives select the seminorm orders and
constant before all moving profiles and frames. Both original ordinary
columns use absolute volume, the actual row classification supplies the
sixth-power count, and the original physical cutoff cost is paid once.
The source, Gauss denominators, child width and allowance are unchanged.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalTerminal

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.CenteredMomentCounting UniqueFactorizationMonoid

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private theorem paidOrdinaryTerminal_weighted_bound
    {normalization rowFactor pairValue sourceValue coefficient profileFactor scaleFactor : ℝ}
    (hnormalization : 0 ≤ normalization) (hrowFactor : 0 ≤ rowFactor)
    (hpair : pairValue ≤ rowFactor * sourceValue)
    (hsource : normalization * sourceValue ≤ coefficient * profileFactor * scaleFactor) :
    normalization * pairValue ≤ rowFactor * coefficient * profileFactor * scaleFactor := by
  calc
    normalization * pairValue ≤ normalization * (rowFactor * sourceValue) :=
      mul_le_mul_of_nonneg_left hpair hnormalization
    _ = rowFactor * (normalization * sourceValue) := mul_left_comm _ _ _
    _ ≤ rowFactor * (coefficient * profileFactor * scaleFactor) :=
      mul_le_mul_of_nonneg_left hsource hrowFactor
    _ = rowFactor * coefficient * profileFactor * scaleFactor := by ac_rfl

theorem exists_original_ordinary_magnitude_terminal_with_cutoff
    {Catalogue : Type*} [Fintype Catalogue]
    (χ : Catalogue → HeckeCharacter F)
    (density : Catalogue → 𝓢(ℝ, ℂ) → ℂ)
    (remainder : Catalogue → Seminorm ℂ (𝓢(ℝ, ℂ)))
    (hcontinuous : ∀ i, Continuous (remainder i))
    (window : Set ℝ)
    (hvolume : ∀ i (φ : 𝓢(ℝ, ℂ)) (X : ℝ), 0 < X → tsupport φ ⊆ window →
      ‖(∑' I : Ideal (𝓞 F), CanonicalExceptionalVolume.coefficient (χ i) I *
          φ ((Ideal.absNorm I : ℝ) / X)) - (X : ℂ) * density i φ‖ ≤ remainder i φ)
    (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0) :
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
    ∀ {H ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : A.GeneralArithmeticContext σ η hS) (R : ActualSecondCorrelationRows A σ H ι)
    {Ray : Type*} [CommGroup Ray] [Fintype Ray] {k l : ℕ}
    (left : SecondSideFrame (V := V) C R Ray .left k)
    (right : SecondSideFrame (V := V) C R Ray .right l)
    {theta : Finset (HeckeCharacter F)} (Q : PairedFiniteCharacters theta H) (ξ : V)
    (TL : ∀ h : R.exceptionalRows Q, left.source.OrdinaryExceptionalAt (σ := σ) (CanonicalExceptionalVolume.coefficient (χ iLeft)) WL₁ WL₂ ξ h.val)
    (TR : ∀ h : R.exceptionalRows Q, right.source.OrdinaryExceptionalAt (σ := σ) (CanonicalExceptionalVolume.coefficient (χ iRight)) WR₁ WR₂ ξ h.val)
    (UL : ExceptionalAtomicScales left.allocation) (UR : ExceptionalAtomicScales right.allocation)
    (Z Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ v
      r₁ r₂ divisorLower slotError cutoffLoss sectors stepσ δ rowAmplitude : ℝ)
    (hZ : 1 ≤ Z) (hv : 0 ≤ v) (hr₁ : 0 ≤ r₁) (hdivisor : divisorLower - r₂ ≤ slotError)
    (hsectors : 0 ≤ sectors) (hrowAmplitude : 0 ≤ rowAmplitude)
    (hA : Aexp ≤ 5 * (m + q) / 6) (hc : 0 ≤ c) (hw : 0 ≤ w) (hb₂ : 0 ≤ b₂)
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
      R.normFactor C h.val.val * Z ^ (2 * (Aexp - c - w) - K - g - g₂ - V₀ + cutoffLoss))
    (hfiber : ∀ I ∈ (Finset.univ : Finset (R.exceptionalRows Q)).image
      (fun h => (R.extractedRow C h.val).ideal.val),
      (((Finset.univ : Finset (R.exceptionalRows Q)).filter
        (fun h => (R.extractedRow C h.val).ideal.val = I)).card : ℝ) ≤ sectors)
    (hF₁ : 2 * (c + w) / 3 - 3 * stepσ - 5 * δ / 6 ≤
      firstSaving c (d + (2 * Aexp - c - d + R₀ + E₀ - m) - K)
        w (q + R₀ + E₀) wo Bcommon g ell)
    (hF₂ : 2 * b₂ / 3 ≤ 2 * b₂ - 5 * g₂ / 6 - p₂ + t₂ + V₀ / 6 + (2 * v) / 6),
    let mChild := 2 * (Aexp - c - w) - K - g - g₂ - V₀
    let qChild := q + R₀ + E₀ + wo + t₂ + V₀
    let Δ := b₂ - p₂ + w + Bcommon + ell
    let rowFactor := rowAmplitude * Z ^ (g₂ - t₂) /
      (Real.sqrt left.normalizationScale * Real.sqrt right.normalizationScale)
    Z ^ (-(mChild + qChild + Δ)) *
      jointColumnPairMagnitude (R.exceptionalRows Q) left.allocation.columns right.allocation.columns
        (fun h : R.live => R.weight h.val * R.correlation h.val)
        (fun h => left.coefficient h.val)
        (fun h => right.coefficient h.val)
        (fun h => rawSourceLocation (left.leftLocation h.val) (left.rightLocation h.val)
          (left.slotLocation h.val))
        (fun h => rawSourceLocation (right.leftLocation h.val) (right.rightLocation h.val)
          (right.slotLocation h.val)) ξ ≤
      rowFactor * (sectors * Cbound * (UL.constant * UR.constant)) * P ^ 4 *
      Z ^ (3 * stepσ + 5 * δ / 6 + slotError - divisorLower + cutoffLoss / 6) := by
  obtain ⟨orders, hzero, Cbound, hCbound, hrows⟩ :=
    CanonicalExceptionalRows.exists_original_ordinary_paired_row_bound_with_cutoff
      (V := V) (σ := σ) (η := η) (hS := hS)
      χ density remainder hcontinuous window hvolume hcompact hpositive
  refine ⟨orders, hzero, Cbound, hCbound, ?_⟩
  intro iLeft iRight WL₁ WL₂ WR₁ WR₂ hsL₁ hsL₂ hsR₁ hsR₂ P hP hPL₁ hPL₂ hPR₁ hPR₂
    H ι instFintype instDecidableEq C R Ray instCommGroup instFintypeRay k l
    left right theta Q ξ TL TR UL UR
    Z Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ v
    r₁ r₂ divisorLower slotError cutoffLoss sectors stepσ δ rowAmplitude
    hZ hv hr₁ hdivisor hsectors hrowAmplitude hA hc hw hb₂
    hleftAtoms hrightAtoms hexponent hm hgcd hunit hweight base hclass hfactor hwindow
    hcutoff hfiber hF₁ hF₂
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
  have hp := hrows iLeft iRight WL₁ WL₂ WR₁ WR₂ hsL₁ hsL₂ hsR₁ hsR₂
    P hP hPL₁ hPL₂ hPR₁ hPR₂ C R.primes R.primes_injective R.leftMultiplicity R.rightMultiplicity
    (Finset.univ : Finset (R.exceptionalRows Q))
    (fun h => R.originalIdeal h.val.val) (fun h => R.frequency h.val.val)
    (fun h => R.exceptionalRow C h.val) base
    (fun h => R.factor C h.val.val) (fun h => -R.factor C h.val.val)
    Z Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ v
    r₁ r₂ divisorLower slotError cutoffLoss sectors (UL.constant * UR.constant) stepσ δ
    hZ hv hr₁ hdivisor hsectors (mul_nonneg UL.constant_nonneg UR.constant_nonneg)
    hA hc hw hb₂
    (fun h _ => hclass h) (fun h _ => hfactor h) (fun h _ => hwindow h)
    (fun h _ => hcutoff h) hfiber hF₁ hF₂
    (fun h => (TL h).source) (fun h => (TR h).source) (fun h _ => hnormal h)
  have hweighted := R.weighted_correlation_norm_le_of_windows C hm (R.rows.filter Q.exceptional)
    Z g₂ t₂ rowAmplitude hz hrowAmplitude hgcd hunit hweight
  have hs := left.ordinary_pair_magnitude_le_exceptionalValues right
    (R.exceptionalRows Q) ξ TL TR (rowAmplitude * Z ^ (g₂ - t₂))
    (fun h => hweighted h.val.val (R.exceptionalRows_original_mem Q h))
  dsimp only
  have hrow0 : 0 ≤ rowAmplitude * Z ^ (g₂ - t₂) /
      (Real.sqrt left.normalizationScale * Real.sqrt right.normalizationScale) := by
    positivity
  exact paidOrdinaryTerminal_weighted_bound
    (Real.rpow_nonneg hz.le _) hrow0 hs hp

end HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalTerminal

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalTerminal.exists_original_ordinary_magnitude_terminal_with_cutoff
