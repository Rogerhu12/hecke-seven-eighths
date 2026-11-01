import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalUniformRows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualExceptionalTerminal

/-!
# The actual paired exceptional magnitude with uniform original controls

A fixed-character single-series primitive selects the seminorms, height
order and constant before every moving source.  The actual side frames,
full correlation, frozen allocations, four rectangles, extracted rows
and raw atomic windows then yield the exceptional magnitude.  The four
original profile factors remain explicit as `P^4`.

This construction supplies no finished catalogue or terminal estimate as
an input.  Its raw per-ideal charts and arithmetic windows are filled by
the literal factories when assembling the complete engine step.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalTerminal

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.Moments.Twist HeckePort.CenteredMomentVolume
open HeckePort.CenteredMomentCounting UniqueFactorizationMonoid

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

theorem exists_original_magnitude_terminal
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
    ∃ order : ℕ, ∃ Cbound : ℝ, 0 < Cbound ∧
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
    (EL : SecondCoefficientComparison left.dictionary)
    (ER : SecondCoefficientComparison right.dictionary)
    {theta : Finset (HeckeCharacter F)} (Q : PairedFiniteCharacters theta H) (ξ : V)
    (TL : ∀ h : R.exceptionalRows Q, left.source.ExceptionalAt (σ := σ) EL.scale₁ EL.scale₂
      (fun _ => EL.leftWeight) (fun _ => EL.rightWeight) (CanonicalExceptionalVolume.coefficient (χ iLeft)) WL₁ WL₂ ξ h.val)
    (TR : ∀ h : R.exceptionalRows Q, right.source.ExceptionalAt (σ := σ) ER.scale₁ ER.scale₂
      (fun _ => ER.leftWeight) (fun _ => ER.rightWeight) (CanonicalExceptionalVolume.coefficient (χ iRight)) WR₁ WR₂ ξ h.val)
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
    (hminimum : ∀ h, Z ^ ((m + q) / 4 - vStar - r₁) ≤ (TL h).source.lower),
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
      rowFactor * (sectors * Cbound * (UL.constant * UR.constant)) * P ^ 4 *
      (1 + height) ^ order *
      Z ^ (max (Aexp - (m + q)) 0 + 3 * stepσ + 5 * δ / 6 + ε + slotError - divisorLower) := by
  obtain ⟨orders, hzero, order, Cbound, hCbound, hrows⟩ :=
    CanonicalExceptionalRows.exists_original_paired_row_bound (V := V) (σ := σ)
      (η := η) (hS := hS) χ density remainder hcontinuous hvolume
      window hcompact hpositive ε maskExponent hε hmask
  refine ⟨orders, hzero, order, Cbound, hCbound, ?_⟩
  intro iLeft iRight WL₁ WL₂ WR₁ WR₂ hsL₁ hsL₂ hsR₁ hsR₂ P hP hPL₁ hPL₂ hPR₁ hPR₂
    H ι instFintype instDecidableEq C R Ray instCommGroup instFintypeRay k l
    left right EL ER theta Q ξ TL TR UL UR
    Z Aexp m q c d R₀ E₀ K w wo Bcommon g ell b₂ p₂ g₂ t₂ V₀ v vStar
    r₁ r₂ divisorLower slotError sectors height stepσ δ rowAmplitude
    hZ hv hr₁ hdivisor hsectors hheight hrowAmplitude
    hleftAtoms hrightAtoms hexponent hm hgcd hunit hweight base hclass hfactor hwindow
    hcutoff hfiber hF₁ hF₂ hvsum hmask0 hmasknorm htime hminimum
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hnormal (h : R.exceptionalRows Q) :
      (TL h).source.rawMass * (TR h).source.rawMass ≤
        (UL.constant * UR.constant) * Z ^ (Aexp - c - w - b₂ - r₁ - r₂) := by
    have hl := (TL h).source.rawMass_le_atomic_power C Z hZ UL (hleftAtoms h)
    have hr := (TR h).source.rawMass_le_atomic_power C Z hZ UR (hrightAtoms h)
    apply (mul_le_mul hl hr (TR h).source.rawMass_nonneg
      (mul_nonneg UL.constant_nonneg (Real.rpow_nonneg hz.le _))).trans_eq
    rw [← hexponent, Real.rpow_add hz]
    ring
  have hb := hrows iLeft iRight WL₁ WL₂ WR₁ WR₂ hsL₁ hsL₂ hsR₁ hsR₂
    P hP hPL₁ hPL₂ hPR₁ hPR₂
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
  convert hmul using 1 <;> ring

end HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalTerminal

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalTerminal.exists_original_magnitude_terminal
