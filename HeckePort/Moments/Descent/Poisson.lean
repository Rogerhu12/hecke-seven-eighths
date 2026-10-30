import HeckePort.Moments.Descent.Marks
import HeckePort.Moments.Descent.LocalReflection
import HeckePort.Moments.Descent.IdealMasks
import HeckeGeneral.Characters.SexticResidueCharacter

/-!
# Local and cross-slot phases of the marked reflection

Port of the arithmetic part of openai/math `OAI/NumberTheory/DirichletL/Descent/Poisson.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`.

* The local marked statements `actual_marked_active_eq/norm/formula/gauss_phase_norm` are about
  the quotient field `ℤ[ω]/P` and the sextic character `actualSextic P hg`, and are proved in
  openai from the bracket machinery `LocalReflectionBrackets` of the `ℤ[ω]` Gauss-sum pipeline.
  Here they are proved directly, for an arbitrary finite field `F`, any multiplicative character `χ`
  with `χ ^ 2 ≠ 1` (true for characters of order six), via the Gauss sum of `χ ^ 2`
  (`active_formula`, `active_norm`, `gauss_phase_norm`); `sexticResidue_marked_active_norm`
  instantiates them at the skeleton's sextic residue character.
* `ideal_divisibility_local_zeroMark`: the residue of the generator vanishes iff `P ∣ A`
  (hypothesis `hres`, which for the allowed generator is `P ∣ A ↔ generator ∈ P`).
* `row_slot_cross_phase`/`row_slot_product_phase` take the cross symbols as an arbitrary table
  `cross i k` (openai `MixedCrossSeparation.crossSymbol p hg i k`; over a general field
  `idealSymbol K S D (P i) (D.generator (P k))`), and the sixth-power and square-reciprocity
  facts (openai `canonicalSextic_sixth_power_mask`, `canonicalSextic_sq_reciprocity_primary`;
  here `AllowedGeneratorInput.reciprocity` gives the stronger `cross i k = cross k i`) as hypotheses.
* Not ported: `canonicalSourceCoefficient_mark_priority` and `marked_disjoint_source_poisson`
  (they are about `canonicalSourceCoefficient`/`disjointCanonicalSource`, the specific
  Poisson source of the `ℤ[ω]` Gauss pipeline, with `GaussSum` imports outside S0).
-/

noncomputable section

namespace HeckePort.Moments

open scoped Classical BigOperators

theorem ideal_divisibility_local_zeroMark {F : Type*} [Field F] {I : Type*} [Dvd I]
    (r : I → F) (P A : I) (hres : r A = 0 ↔ P ∣ A) :
    zeroMark (r A) = if P ∣ A then (1 : ℂ) else 0 := by
  simp only [zeroMark, hres]

variable {F : Type*} [Field F] [Fintype F]

theorem active_unfold (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (σ ε : Fˣ) (x : F) :
    localReflectionActive zeroMark χ ψ σ ε x =
      (Fintype.card F : ℂ)⁻¹ * ∑ h : Fˣ, ((χ⁻¹) ^ 2) ((σ : F) * (h : F)) * ψ (((ε : F) * x) * ((h⁻¹ : Fˣ) : F)) := by
  unfold localReflectionActive
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  rw [localFourier_zeroMark, one_mul]

theorem sum_units_eq (f : F → ℂ) (h0 : f 0 = 0) : ∑ u : Fˣ, f (u : F) = ∑ a : F, f a := by
  rw [← Finset.sum_image (f := f) (g := Units.val) (s := Finset.univ) (fun a _ b _ h => Units.ext h)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a _ ha
  have : a = 0 := by
    by_contra hne
    exact ha (Finset.mem_image.mpr ⟨Units.mk0 a hne, Finset.mem_univ _, rfl⟩)
  rw [this, h0]

theorem inv_sq_apply (χ : MulChar F ℂ) (a : F) : ((χ⁻¹) ^ 2) a = (χ ^ 2) a⁻¹ := by
  rw [← MulChar.inv_apply', ← inv_pow]

theorem active_gauss (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (σ ε : Fˣ) (x : F) :
    localReflectionActive zeroMark χ ψ σ ε x =
      (Fintype.card F : ℂ)⁻¹ * ((χ⁻¹) ^ 2) (σ : F) *
        ∑ u : F, (χ ^ 2) u * ψ (((ε : F) * x) * u) := by
  rw [active_unfold, mul_assoc]
  congr 1
  rw [← sum_units_eq (fun u : F => (χ ^ 2) u * ψ (((ε : F) * x) * u)) (by simp [MulChar.map_zero]),
    Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.inv Fˣ) _ _ (fun h => ?_)
  simp only [Equiv.inv_apply, Units.val_inv_eq_inv_val]
  rw [map_mul, inv_sq_apply χ (h : F)]
  ring

theorem gauss_norm (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ) (hχ : χ ≠ 1) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F) := by
  have h := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq] at h
  have hr := congrArg Complex.re h
  have h2 : ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
    simpa [Complex.mul_conj', pow_two] using hr
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ Fintype.card F by positivity)
  have hn := norm_nonneg (gaussSum χ ψ)
  have hr := Real.sqrt_nonneg (Fintype.card F : ℝ)
  nlinarith

theorem norm_mulChar_of_ne_zero (χ : MulChar F ℂ) {a : F} (ha : a ≠ 0) : ‖χ a‖ = 1 := by
  have := Complex.norm_eq_one_of_mem_rootsOfUnity (MulChar.apply_mem_rootsOfUnity (χ := χ) (Units.mk0 a ha))
  simpa using this

theorem active_formula (χ : MulChar F ℂ) (hχ : χ ^ 2 ≠ 1) (ψ : AddChar F ℂ) (σ ε : Fˣ) (x : F) :
    localReflectionActive zeroMark χ ψ σ ε x =
      (Fintype.card F : ℂ)⁻¹ * gaussSum (χ ^ 2) ψ * ((χ⁻¹) ^ 2) ((σ : F) * (ε : F) * x) := by
  rw [active_gauss]
  by_cases hx : x = 0
  · subst hx
    have h0 : ∑ u : F, (χ ^ 2) u * ψ (((ε : F) * 0) * u) = 0 := by
      simp only [mul_zero, zero_mul, AddChar.map_zero_eq_one, mul_one]
      exact MulChar.sum_eq_zero_of_ne_one hχ
    rw [h0]
    simp [MulChar.map_zero]
  · have hu : IsUnit ((ε : F) * x) := (Units.isUnit ε).mul (isUnit_iff_ne_zero.mpr hx)
    obtain ⟨a, ha⟩ := hu
    have hT : ∑ u : F, (χ ^ 2) u * ψ (((ε : F) * x) * u) = gaussSum (χ ^ 2) (ψ.mulShift (a : F)) := by
      rw [← ha]
      simp [gaussSum, AddChar.mulShift_apply]
    have hG := gaussSum_mulShift (χ ^ 2) ψ a
    have hne : (χ ^ 2) (a : F) ≠ 0 := by
      rw [MulChar.pow_apply' _ (by norm_num : (2:ℕ) ≠ 0)]
      exact pow_ne_zero _ (by
        have := norm_mulChar_of_ne_zero χ (Units.ne_zero a)
        intro h0; rw [h0] at this; simp at this)
    rw [hT]
    have : gaussSum (χ ^ 2) (ψ.mulShift (a : F)) = gaussSum (χ ^ 2) ψ / (χ ^ 2) (a : F) := by
      rw [eq_div_iff hne, mul_comm]; exact hG
    have hinv : ((χ⁻¹) ^ 2) (a : F) = ((χ ^ 2) (a : F))⁻¹ := by
      rw [inv_sq_apply]
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, inv_mul_cancel₀ (Units.ne_zero a), map_one]
    have e : (σ : F) * (ε : F) * x = (σ : F) * (a : F) := by rw [mul_assoc, ha]
    rw [this, e, map_mul, hinv]
    field_simp

theorem sq_ne_one_of_orderOf_six (χ : MulChar F ℂ) (h : orderOf χ = 6) : χ ^ 2 ≠ 1 := by
  intro h2
  have := orderOf_dvd_of_pow_eq_one h2
  rw [h] at this
  omega

/-- openai `actual_marked_active_norm`. -/
theorem active_norm (χ : MulChar F ℂ) (hχ : χ ^ 2 ≠ 1) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (σ ε : Fˣ) (x : F) :
    ‖localReflectionActive zeroMark χ ψ σ ε x‖ =
      (Real.sqrt (Fintype.card F))⁻¹ * (if x = 0 then 0 else 1) := by
  rw [active_formula χ hχ ψ σ ε x, norm_mul, norm_mul, gauss_norm ψ hψ (χ ^ 2) hχ]
  have hcard : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt (Fintype.card F) ^ 2 = Fintype.card F := Real.sq_sqrt hcard.le
  have hs0 : 0 < Real.sqrt (Fintype.card F) := Real.sqrt_pos.mpr hcard
  have hc : ‖(Fintype.card F : ℂ)⁻¹‖ = (Real.sqrt (Fintype.card F))⁻¹ * (Real.sqrt (Fintype.card F))⁻¹ := by
    rw [norm_inv, Complex.norm_natCast, ← mul_inv, ← pow_two, hs]
  by_cases hx : x = 0
  · simp [hx, MulChar.map_zero]
  · have hne : (σ : F) * (ε : F) * x ≠ 0 := mul_ne_zero (mul_ne_zero σ.ne_zero ε.ne_zero) hx
    rw [norm_mulChar_of_ne_zero (χ⁻¹ ^ 2) hne, hc]
    simp only [hx, ite_false, mul_one]
    field_simp

/-- openai `actual_marked_gauss_phase_norm`. -/
theorem gauss_phase_norm (χ : MulChar F ℂ) (hχ : χ ^ 2 ≠ 1) (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) :
    ‖(Real.sqrt (Fintype.card F) : ℂ)⁻¹ * gaussSum (χ ^ 2) ψ‖ = 1 := by
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, gauss_norm ψ hψ (χ ^ 2) hχ,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hcard : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hs0 : 0 < Real.sqrt (Fintype.card F) := Real.sqrt_pos.mpr hcard
  field_simp

/-- The marked active norm at the skeleton's sextic residue character
(`HeckeGeneral.Characters.sexticResidueCharacter`): this replaces `actualSextic P hg`. -/
theorem sexticResidue_marked_active_norm {K : Type} [Field K] [NumberField K] (ζ : K)
    (hζ : IsPrimitiveRoot ζ 6) (σ₀ : K →+* ℂ)
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hp : (6 : NumberField.RingOfIntegers K) ∉ p.asIdeal) :
    letI : Field (NumberField.RingOfIntegers K ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
    letI : Fintype (NumberField.RingOfIntegers K ⧸ p.asIdeal) := Fintype.ofFinite _
    ∀ (ψ : AddChar (NumberField.RingOfIntegers K ⧸ p.asIdeal) ℂ), ψ.IsPrimitive →
    ∀ (σ ε : (NumberField.RingOfIntegers K ⧸ p.asIdeal)ˣ)
      (x : NumberField.RingOfIntegers K ⧸ p.asIdeal),
    ‖localReflectionActive zeroMark
        (HeckeGeneral.Characters.sexticResidueCharacter K ζ hζ σ₀ p hp) ψ σ ε x‖ =
      (Real.sqrt (Fintype.card (NumberField.RingOfIntegers K ⧸ p.asIdeal)))⁻¹ *
        (if x = 0 then 0 else 1) := by
  intro ψ hψ σ ε x
  letI : Field (NumberField.RingOfIntegers K ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
  letI : Fintype (NumberField.RingOfIntegers K ⧸ p.asIdeal) := Fintype.ofFinite _
  exact active_norm _ (sq_ne_one_of_orderOf_six _
    (HeckeGeneral.Characters.sexticResidueCharacter_order K ζ hζ σ₀ p hp)) ψ hψ σ ε x

section CrossPhase

variable {ι : Type*}

theorem row_slot_cross_phase (cross : ι → ι → ℂ)
    (h6 : ∀ i k, i ≠ k → cross i k ^ 6 = 1)
    (hsq : ∀ i k, i ≠ k → cross i k ^ 2 = cross k i ^ 2) (i k : ι) (hik : i ≠ k) :
    cross i k ^ 4 * cross k i ^ 2 = 1 := by
  calc
    _ = cross i k ^ 6 := by rw [← hsq i k hik]; ring
    _ = 1 := h6 i k hik

theorem row_slot_product_phase (cross : ι → ι → ℂ)
    (h6 : ∀ i k, i ≠ k → cross i k ^ 6 = 1)
    (hsq : ∀ i k, i ≠ k → cross i k ^ 2 = cross k i ^ 2) (R P : Finset ι)
    (hRP : Disjoint R P) :
    (∏ i ∈ R, ∏ k ∈ P, cross i k ^ 4 * cross k i ^ 2) = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  apply Finset.prod_eq_one
  intro k hk
  exact row_slot_cross_phase cross h6 hsq i k (fun h =>
    (Finset.disjoint_left.mp hRP) hi (h.symm ▸ hk))

end CrossPhase

end HeckePort.Moments

end
