import HeckeGeneral.Characters.InfinityType

/-!+# Infinity parameters throughout a fixed Hecke packet

Finite-order twists do not change the complex weights or radial parameters.
A norm twist translates every normalized radial parameter by the same amount.
The relative radial parameters therefore survive; there is no assumption that
one twist removes all of them. The last result gives the nonzero angular
choice between a target and its inverse when a fixed Gauss weight is nonzero.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

theorem complexHeckeComponent_mul (v : InfinitePlace K) (hv : v.IsComplex)
    (χ ψ : HeckeCharacter K) :
    complexHeckeComponent K v hv (χ * ψ) =
      complexHeckeComponent K v hv χ * complexHeckeComponent K v hv ψ := by
  ext u
  rfl

theorem realHeckeComponent_mul (v : InfinitePlace K) (hv : v.IsReal)
    (χ ψ : HeckeCharacter K) :
    realHeckeComponent K v hv (χ * ψ) =
      realHeckeComponent K v hv χ * realHeckeComponent K v hv ψ := by
  ext u
  rfl

theorem heckeComplexWeight_mul (v : InfinitePlace K) (hv : v.IsComplex)
    (χ ψ : HeckeCharacter K) :
    heckeComplexWeight K v hv (χ * ψ) =
      heckeComplexWeight K v hv χ + heckeComplexWeight K v hv ψ := by
  unfold heckeComplexWeight
  rw [complexHeckeComponent_mul, complexWeight_mul]

theorem heckeComplexParameter_mul (v : InfinitePlace K) (hv : v.IsComplex)
    (χ ψ : HeckeCharacter K) :
    heckeComplexParameter K v hv (χ * ψ) =
      heckeComplexParameter K v hv χ + heckeComplexParameter K v hv ψ := by
  unfold heckeComplexParameter
  rw [complexHeckeComponent_mul, complexFrequency_mul, add_div]

theorem heckeRealParameter_mul (v : InfinitePlace K) (hv : v.IsReal)
    (χ ψ : HeckeCharacter K) :
    heckeRealParameter K v hv (χ * ψ) =
      heckeRealParameter K v hv χ + heckeRealParameter K v hv ψ := by
  unfold heckeRealParameter
  rw [realHeckeComponent_mul, realUnitFrequency_mul]

theorem heckeComplexWeight_inv (v : InfinitePlace K) (hv : v.IsComplex) (χ : HeckeCharacter K) :
    heckeComplexWeight K v hv χ⁻¹ = -heckeComplexWeight K v hv χ := by
  unfold heckeComplexWeight
  have hinv : complexHeckeComponent K v hv χ⁻¹ = (complexHeckeComponent K v hv χ)⁻¹ := by
    ext z
    rfl
  rw [hinv, complexWeight_inv]

theorem heckeComplexParameter_inv (v : InfinitePlace K) (hv : v.IsComplex)
    (χ : HeckeCharacter K) :
    heckeComplexParameter K v hv χ⁻¹ = -heckeComplexParameter K v hv χ := by
  unfold heckeComplexParameter
  rw [show complexHeckeComponent K v hv χ⁻¹ = (complexHeckeComponent K v hv χ)⁻¹ from rfl,
    complexFrequency_inv, neg_div]

theorem heckeComplexWeight_zpow (v : InfinitePlace K) (hv : v.IsComplex)
    (χ : HeckeCharacter K) (e : ℤ) :
    heckeComplexWeight K v hv (χ ^ e) = e * heckeComplexWeight K v hv χ := by
  have hpow : ∀ n : ℕ, heckeComplexWeight K v hv (χ ^ n) = n * heckeComplexWeight K v hv χ := by
    intro n
    induction n with
    | zero => simp [heckeComplexWeight, complexHeckeComponent, infiniteComponent]
    | succ n ih => rw [pow_succ, heckeComplexWeight_mul, ih]; push_cast; ring
  cases e with
  | ofNat n => simpa using hpow n
  | negSucc n =>
    rw [zpow_negSucc, heckeComplexWeight_inv, hpow, Int.negSucc_eq]
    push_cast
    ring

/-- The normalized radial parameter at any infinite place of the original number field. -/
def heckeRadialParameter (v : InfinitePlace K) (χ : HeckeCharacter K) : ℝ :=
  if hv : v.IsReal then heckeRealParameter K v hv χ
  else heckeComplexParameter K v (v.not_isReal_iff_isComplex.mp hv) χ

theorem heckeRadialParameter_of_real (v : InfinitePlace K) (hv : v.IsReal)
    (χ : HeckeCharacter K) : heckeRadialParameter K v χ = heckeRealParameter K v hv χ := by
  simp [heckeRadialParameter, hv]

theorem heckeRadialParameter_of_complex (v : InfinitePlace K) (hv : v.IsComplex)
    (χ : HeckeCharacter K) : heckeRadialParameter K v χ = heckeComplexParameter K v hv χ := by
  simp [heckeRadialParameter, v.not_isReal_iff_isComplex.mpr hv]

theorem heckeRadialParameter_mul (v : InfinitePlace K) (χ ψ : HeckeCharacter K) :
    heckeRadialParameter K v (χ * ψ) = heckeRadialParameter K v χ + heckeRadialParameter K v ψ := by
  by_cases hv : v.IsReal
  · simp only [heckeRadialParameter_of_real K v hv, heckeRealParameter_mul]
  · have hc := v.not_isReal_iff_isComplex.mp hv
    simp only [heckeRadialParameter_of_complex K v hc, heckeComplexParameter_mul]

@[simp] theorem heckeRadialParameter_one (v : InfinitePlace K) :
    heckeRadialParameter K v (1 : HeckeCharacter K) = 0 := by
  have h := heckeRadialParameter_mul K v 1 1
  simp only [mul_one] at h
  linarith

theorem heckeRadialParameter_inv (v : InfinitePlace K) (χ : HeckeCharacter K) :
    heckeRadialParameter K v χ⁻¹ = -heckeRadialParameter K v χ := by
  have h := heckeRadialParameter_mul K v χ χ⁻¹
  rw [mul_inv_cancel, heckeRadialParameter_one] at h
  linarith

theorem heckeRadialParameter_zpow (v : InfinitePlace K) (χ : HeckeCharacter K) (e : ℤ) :
    heckeRadialParameter K v (χ ^ e) = e * heckeRadialParameter K v χ := by
  have hpow : ∀ n : ℕ, heckeRadialParameter K v (χ ^ n) = n * heckeRadialParameter K v χ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, heckeRadialParameter_mul, ih]; push_cast; ring
  cases e with
  | ofNat n => simpa using hpow n
  | negSucc n => rw [zpow_negSucc, heckeRadialParameter_inv, hpow]; push_cast; ring

theorem heckeRadialParameter_finiteOrder (v : InfinitePlace K)
    {χ : HeckeCharacter K} (hχ : FiniteOrder χ) : heckeRadialParameter K v χ = 0 := by
  by_cases hv : v.IsReal
  · rw [heckeRadialParameter_of_real K v hv, heckeRealParameter_finiteOrder K v hv hχ]
  · have hc := v.not_isReal_iff_isComplex.mp hv
    rw [heckeRadialParameter_of_complex K v hc, heckeComplexParameter_finiteOrder K v hc hχ]

theorem heckeRadialParameter_normTwist (v : InfinitePlace K) (t : ℝ) :
    heckeRadialParameter K v (heckeNormTwist K t) = -t := by
  by_cases hv : v.IsReal
  · rw [heckeRadialParameter_of_real K v hv, heckeRealParameter_normTwist]
  · have hc := v.not_isReal_iff_isComplex.mp hv
    rw [heckeRadialParameter_of_complex K v hc, heckeComplexParameter_normTwist]

/-- Relative radial frequencies are defined for real and complex places together. -/
def heckeRelativeParameter (v w : InfinitePlace K) (χ : HeckeCharacter K) : ℝ :=
  heckeRadialParameter K v χ - heckeRadialParameter K w χ

theorem heckeRelativeParameter_normTwist (v w : InfinitePlace K) (χ : HeckeCharacter K) (t : ℝ) :
    heckeRelativeParameter K v w (χ * heckeNormTwist K t) = heckeRelativeParameter K v w χ := by
  unfold heckeRelativeParameter
  rw [heckeRadialParameter_mul, heckeRadialParameter_mul,
    heckeRadialParameter_normTwist, heckeRadialParameter_normTwist]
  ring

/-- Exact infinity parameters for the actual packet presentation. -/
theorem heckeRadialParameter_packet (v : InfinitePlace K) (ω θ : HeckeCharacter K)
    (hθ : FiniteOrder θ) (e : ℤ) (t : ℝ) :
    heckeRadialParameter K v (θ * ω ^ e * heckeNormTwist K t) =
      e * heckeRadialParameter K v ω - t := by
  rw [heckeRadialParameter_mul, heckeRadialParameter_mul,
    heckeRadialParameter_finiteOrder K v hθ, heckeRadialParameter_zpow,
    heckeRadialParameter_normTwist, zero_add, sub_eq_add_neg]

theorem heckeComplexWeight_packet (v : InfinitePlace K) (hv : v.IsComplex)
    (ω θ : HeckeCharacter K) (hθ : FiniteOrder θ) (e : ℤ) (t : ℝ) :
    heckeComplexWeight K v hv (θ * ω ^ e * heckeNormTwist K t) =
      e * heckeComplexWeight K v hv ω := by
  rw [heckeComplexWeight_mul, heckeComplexWeight_mul,
    heckeComplexWeight_finiteOrder K v hv hθ, heckeComplexWeight_zpow,
    heckeComplexWeight_normTwist, zero_add, add_zero]

theorem heckeRelativeParameter_packet (v w : InfinitePlace K) (ω θ : HeckeCharacter K)
    (hθ : FiniteOrder θ) (e : ℤ) (t : ℝ) :
    heckeRelativeParameter K v w (θ * ω ^ e * heckeNormTwist K t) =
      e * heckeRelativeParameter K v w ω := by
  unfold heckeRelativeParameter
  rw [heckeRadialParameter_packet K v ω θ hθ, heckeRadialParameter_packet K w ω θ hθ]
  ring

/-- A norm twist can remove all radial parameters exactly when they already agree. -/
theorem exists_normTwist_all_radial_zero_iff (χ : HeckeCharacter K) (w : InfinitePlace K) :
    (∃ t : ℝ, ∀ v, heckeRadialParameter K v (χ * heckeNormTwist K t) = 0) ↔
      ∀ v, heckeRelativeParameter K v w χ = 0 := by
  simp only [heckeRadialParameter_mul, heckeRadialParameter_normTwist]
  constructor
  · rintro ⟨t, ht⟩ v
    unfold heckeRelativeParameter
    have hv := ht v
    have hw := ht w
    linarith
  · intro h
    refine ⟨heckeRadialParameter K w χ, fun v => ?_⟩
    simpa [heckeRelativeParameter, sub_eq_add_neg] using h v

/-- A nonzero fixed angular correction cannot kill both a target and its inverse. -/
theorem exists_nonzero_corrected_angular_weight (v : InfinitePlace K) (hv : v.IsComplex)
    (ω β : HeckeCharacter K) (hβ : heckeComplexWeight K v hv β ≠ 0) :
    heckeComplexWeight K v hv (ω * β⁻¹) ≠ 0 ∨
      heckeComplexWeight K v hv (ω⁻¹ * β⁻¹) ≠ 0 := by
  rw [heckeComplexWeight_mul, heckeComplexWeight_mul,
    heckeComplexWeight_inv, heckeComplexWeight_inv]
  by_contra h
  push Not at h
  apply hβ
  omega

end HeckeGeneral.Characters
