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
open UniqueFactorizationMonoid

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
def exceptionalTerminalOrder : ℕ :=
  (actual_exceptional_paired_contribution (V := V) (σ := σ) (η := η) (hS := hS)
    HL HR ε maskExponent hε hmask).choose

def exceptionalTerminalConstant : ℝ :=
  (actual_exceptional_paired_contribution (V := V) (σ := σ) (η := η) (hS := hS)
    HL HR ε maskExponent hε hmask).choose_spec.choose

theorem exceptionalTerminalConstant_pos :
    0 < exceptionalTerminalConstant (V := V) (σ := σ) (η := η) (hS := hS)
      HL HR ε maskExponent hε hmask :=
  (actual_exceptional_paired_contribution (V := V) (σ := σ) (η := η) (hS := hS)
    HL HR ε maskExponent hε hmask).choose_spec.choose_spec.1

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
    apply (mul_le_mul hl hr (TR h).source.rawMass_nonneg
      (mul_nonneg UL.constant_nonneg (Real.rpow_nonneg hz.le _))).trans_eq
    rw [← hexponent, Real.rpow_add hz]
    ring
  have hb := (actual_exceptional_paired_contribution (V := V) (σ := σ)
    HL HR ε maskExponent hε hmask).choose_spec.choose_spec.2
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
    dsimp only [exceptionalTerminalConstant, exceptionalTerminalOrder] <;> ring

end SecondSideFrame

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.exceptional_magnitude_terminal_from_atoms
