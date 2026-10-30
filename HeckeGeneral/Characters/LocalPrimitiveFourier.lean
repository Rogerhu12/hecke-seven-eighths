import HeckeGeneral.Characters.LocalPrimitiveAdditive
import HeckeGeneral.Characters.LocalConductorFrequency

/-! Additive orthogonality for the constructed primitive local residue character.
The character is chosen by finite duality; identifying this choice with a trace/different
normalization is a separate compatibility problem. -/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

local instance primitiveResidueFintype (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Fintype (LocalResidueRing K v n) := Fintype.ofFinite _

local instance primitiveResidueUnitFintype (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Fintype (LocalResidueRing K v n)ˣ := Fintype.ofFinite _

/-- Every frequency of the actual primitive character has the usual additive sum. -/
theorem sum_localPrimitiveAddCharacter (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (a : LocalResidueRing K v n) :
    (∑ b : LocalResidueRing K v n, (localPrimitiveAddCharacter K v n (a * b) : ℂ)) =
      if a = 0 then (Nat.card (LocalResidueRing K v n) : ℂ) else 0 := by
  let ψ := Circle.coeHom.compAddChar (localPrimitiveAddCharacter K v n)
  have hψ : ψ.IsPrimitive :=
    (localPrimitiveAddCharacter_isPrimitive K v n).compMulHom_of_isPrimitive
      Circle.coe_injective
  have h := AddChar.sum_mulShift a hψ
  change (∑ b : LocalResidueRing K v n,
    (localPrimitiveAddCharacter K v n (b * a) : ℂ)) =
    ((if a = 0 then Fintype.card (LocalResidueRing K v n) else 0 : ℕ) : ℂ) at h
  simpa [Nat.card_eq_fintype_card, mul_comm] using h

/-- The perfect pairing separates two residue classes by complex orthogonality. -/
theorem sum_localPrimitiveAddCharacter_mul_conj (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (a c : LocalResidueRing K v n) :
    (∑ b : LocalResidueRing K v n,
      (localPrimitiveAddCharacter K v n (b * a) : ℂ) *
        star (localPrimitiveAddCharacter K v n (b * c) : ℂ)) =
      if a = c then (Nat.card (LocalResidueRing K v n) : ℂ) else 0 := by
  have hsum := sum_localPrimitiveAddCharacter K v n (a - c)
  have hinv (z : Circle) : (z : ℂ)⁻¹ = star (z : ℂ) := Circle.coe_inv_eq_conj z
  simpa only [sub_mul, mul_comm a, mul_comm c, AddChar.map_sub_eq_div,
    div_eq_mul_inv, Circle.coe_mul, Circle.coe_inv, hinv,
    sub_eq_zero] using hsum

/-- Finite Parseval identity for sums restricted to local residue units. -/
theorem localPrimitive_unit_parseval (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (F : (LocalResidueRing K v n)ˣ → ℂ) :
    (∑ b : LocalResidueRing K v n,
      (∑ u : (LocalResidueRing K v n)ˣ,
        F u * (localPrimitiveAddCharacter K v n (b * u.val) : ℂ)) *
      star (∑ u : (LocalResidueRing K v n)ˣ,
        F u * (localPrimitiveAddCharacter K v n (b * u.val) : ℂ))) =
      (Nat.card (LocalResidueRing K v n) : ℂ) * ∑ u, F u * star (F u) := by
  have he (u w : (LocalResidueRing K v n)ˣ) :
      (∑ b : LocalResidueRing K v n,
        F u * (localPrimitiveAddCharacter K v n (b * u.val) : ℂ) *
          (star (F w) * star (localPrimitiveAddCharacter K v n (b * w.val) : ℂ))) =
        F u * star (F w) *
          (if u = w then (Nat.card (LocalResidueRing K v n) : ℂ) else 0) := by
    have hs := sum_localPrimitiveAddCharacter_mul_conj K v n u.val w.val
    simp only [Units.val_inj] at hs
    rw [← hs, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  calc
    _ = ∑ b : LocalResidueRing K v n, ∑ u : (LocalResidueRing K v n)ˣ,
        ∑ w : (LocalResidueRing K v n)ˣ,
          F u * (localPrimitiveAddCharacter K v n (b * u.val) : ℂ) *
            (star (F w) * star (localPrimitiveAddCharacter K v n (b * w.val) : ℂ)) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [star_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      rw [star_mul]
      ring
    _ = ∑ u : (LocalResidueRing K v n)ˣ, ∑ w : (LocalResidueRing K v n)ˣ,
        F u * star (F w) *
          (if u = w then (Nat.card (LocalResidueRing K v n) : ℂ) else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun w _ => he u w)
    _ = _ := by simp [Finset.mul_sum, mul_comm, mul_left_comm]

/-- Orthogonality gives the total Gauss energy, without a conductor assumption. -/
theorem localPrimitive_gauss_energy (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (χ : LocalResidueDual K v n) :
    (∑ b : LocalResidueRing K v n,
      localResidueGaussFrequency K v n χ (localPrimitiveAddCharacter K v n) b *
        star (localResidueGaussFrequency K v n χ (localPrimitiveAddCharacter K v n) b)) =
      (Nat.card (LocalResidueRing K v n) : ℂ) * Nat.card (LocalResidueRing K v n)ˣ := by
  have h := localPrimitive_unit_parseval K v n (fun u => (χ u : ℂ))
  have hu (u : (LocalResidueRing K v n)ˣ) : (χ u : ℂ) * star (χ u : ℂ) = 1 := by
    have hi : (χ u : ℂ)⁻¹ = star (χ u : ℂ) := Circle.coe_inv_eq_conj _
    rw [← hi, mul_inv_cancel₀ (Circle.coe_ne_zero _)]
  simp only [hu] at h
  simpa only [localResidueGaussFrequency, localResidueGauss, AddChar.mulShift_apply,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card] using h

/-- The support and unit dilation identities collapse total energy to one Gauss sum. -/
theorem localResidueGauss_energy_on_units (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (χ : LocalResidueDual K v n) (hχ : PrimitiveLocalResidueCharacter K v n χ)
    (η : AddChar (LocalResidueRing K v n) Circle) :
    (∑ b : LocalResidueRing K v n,
      localResidueGaussFrequency K v n χ η b * star (localResidueGaussFrequency K v n χ η b)) =
      (Nat.card (LocalResidueRing K v n)ˣ : ℂ) *
        (localResidueGauss K v n χ η * star (localResidueGauss K v n χ η)) := by
  have he := Fintype.sum_of_injective Units.val Units.val_injective
    (fun _ : (LocalResidueRing K v n)ˣ =>
      localResidueGauss K v n χ η * star (localResidueGauss K v n χ η))
    (fun b : LocalResidueRing K v n =>
      localResidueGaussFrequency K v n χ η b * star (localResidueGaussFrequency K v n χ η b))
    (by
      intro b hb
      have hbu : ¬ IsUnit b := fun ⟨u, hu⟩ => hb ⟨u, hu⟩
      rw [localResidueGaussFrequency_nonunit_allDepth K v n χ hχ η b hbu, zero_mul])
    (by
      intro u
      symm
      rw [localResidueGaussFrequency_unit]
      have hinv : (χ u : ℂ)⁻¹ = star (χ u : ℂ) := Circle.coe_inv_eq_conj _
      rw [hinv, star_mul, star_star]
      have hu : star (χ u : ℂ) * (χ u : ℂ) = 1 := by
        rw [← hinv, inv_mul_cancel₀ (Circle.coe_ne_zero _)]
      calc
        _ = (star (χ u : ℂ) * (χ u : ℂ)) *
            (localResidueGauss K v n χ η * star (localResidueGauss K v n χ η)) := by ring
        _ = _ := by rw [hu, one_mul])
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card] using he.symm

/-- The primitive conductor Gauss sum has exact squared norm `#(O_v / m_v^n)`. -/
theorem localPrimitiveGauss_norm_sq (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (χ : LocalResidueDual K v n) (hχ : PrimitiveLocalResidueCharacter K v n χ) :
    ‖localResidueGauss K v n χ (localPrimitiveAddCharacter K v n)‖ ^ 2 =
      (Nat.card (LocalResidueRing K v n) : ℝ) := by
  have he := localPrimitive_gauss_energy K v n χ
  rw [localResidueGauss_energy_on_units K v n χ hχ] at he
  have hc : (Nat.card (LocalResidueRing K v n)ˣ : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.card_pos (α := (LocalResidueRing K v n)ˣ)).ne'
  rw [mul_comm (Nat.card (LocalResidueRing K v n) : ℂ)] at he
  have hh := mul_left_cancel₀ hc he
  change localResidueGauss K v n χ (localPrimitiveAddCharacter K v n) *
    (starRingEnd ℂ) (localResidueGauss K v n χ (localPrimitiveAddCharacter K v n)) = _ at hh
  rw [Complex.mul_conj'] at hh
  exact Complex.ofReal_injective (by exact_mod_cast hh)

theorem localPrimitiveGauss_norm (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (χ : LocalResidueDual K v n) (hχ : PrimitiveLocalResidueCharacter K v n χ) :
    ‖localResidueGauss K v n χ (localPrimitiveAddCharacter K v n)‖ =
      Real.sqrt ((residueCard K v : ℝ) ^ n) := by
  have h := localPrimitiveGauss_norm_sq K v n χ hχ
  rw [natCard_localResidueRing, Nat.cast_pow] at h
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

theorem localPrimitiveGauss_ne_zero (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (χ : LocalResidueDual K v n) (hχ : PrimitiveLocalResidueCharacter K v n χ) :
    localResidueGauss K v n χ (localPrimitiveAddCharacter K v n) ≠ 0 := by
  intro hz
  have h := localPrimitiveGauss_norm_sq K v n χ hχ
  rw [hz, norm_zero, zero_pow (by omega)] at h
  have hp : (0 : ℝ) < Nat.card (LocalResidueRing K v n) :=
    Nat.cast_pos.mpr (Nat.card_pos (α := LocalResidueRing K v n))
  linarith

/-- All primitive additive characters differ by a unique unit frequency. -/
theorem exists_unique_localPrimitiveAddCharacter_unit (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (η : AddChar (LocalResidueRing K v n) Circle) (hη : η.IsPrimitive) :
    ∃! u : (LocalResidueRing K v n)ˣ,
      (localPrimitiveAddCharacter K v n).mulShift u.val = η := by
  obtain ⟨a, ha, huniq⟩ := exists_unique_localResidue_additive_frequency K v n η
  have hau : IsUnit a := by
    by_contra h
    apply AddChar.not_isPrimitive_mulShift (localPrimitiveAddCharacter K v n) h
    rw [ha]
    exact hη
  obtain ⟨u, hu⟩ := hau
  refine ⟨u, ?_, fun w hw => Units.val_injective ?_⟩
  · change (localPrimitiveAddCharacter K v n).mulShift u.val = η
    rw [hu]
    exact ha
  · exact (huniq w.val hw).trans hu.symm

/-- The exact norm is independent of the choice of primitive additive character. -/
theorem localResidueGauss_primitive_norm_sq (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (χ : LocalResidueDual K v n) (hχ : PrimitiveLocalResidueCharacter K v n χ)
    (η : AddChar (LocalResidueRing K v n) Circle) (hη : η.IsPrimitive) :
    ‖localResidueGauss K v n χ η‖ ^ 2 = (Nat.card (LocalResidueRing K v n) : ℝ) := by
  obtain ⟨u, hu, _⟩ := exists_unique_localPrimitiveAddCharacter_unit K v n η hη
  rw [← hu]
  change ‖localResidueGaussFrequency K v n χ (localPrimitiveAddCharacter K v n) u.val‖ ^ 2 = _
  rw [localResidueGaussFrequency_unit_norm]
  exact localPrimitiveGauss_norm_sq K v n χ hχ

theorem localResidueGauss_primitive_norm (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (χ : LocalResidueDual K v n) (hχ : PrimitiveLocalResidueCharacter K v n χ)
    (η : AddChar (LocalResidueRing K v n) Circle) (hη : η.IsPrimitive) :
    ‖localResidueGauss K v n χ η‖ = Real.sqrt ((residueCard K v : ℝ) ^ n) := by
  have h := localResidueGauss_primitive_norm_sq K v n χ hχ η hη
  rw [natCard_localResidueRing, Nat.cast_pow] at h
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

/-- The Gauss sum of an actual Hecke character at its least local conductor depth. -/
def primitiveConductorResidueGauss (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) : ℂ :=
  localResidueGauss K v (localConductorExponent K χ v) (conductorResidueCharacter K v χ)
    (localPrimitiveAddCharacter K v (localConductorExponent K χ v))

theorem primitiveConductorResidueGauss_norm (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) :
    ‖primitiveConductorResidueGauss K v χ‖ =
      Real.sqrt ((residueCard K v : ℝ) ^ localConductorExponent K χ v) :=
  localPrimitiveGauss_norm K v _ _ (conductorResidueCharacter_isPrimitive K v χ)

theorem primitiveConductorResidueGauss_ne_zero (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) : primitiveConductorResidueGauss K v χ ≠ 0 :=
  localPrimitiveGauss_ne_zero K v _ _ (conductorResidueCharacter_isPrimitive K v χ)

end HeckeGeneral.Characters
