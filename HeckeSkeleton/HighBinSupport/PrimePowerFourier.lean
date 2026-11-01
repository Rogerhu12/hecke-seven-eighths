import HeckeSkeleton.HighBinSupport.FiniteResidueFourier
/-!
# Prime-power Gauss support and values from an actual residue map

For a finite local ring R with residue field F, the functions used by the
sextic probe are the actual pullbacks of multiplicative characters of F.
Theorems below prove support in the annihilator of the residue kernel,
construct the descended additive character rather than assume it, and
compute the principal/nonprincipal branches exactly. These statements apply
to O/p^n after the residue map and primitive trace character are instantiated.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

noncomputable section
namespace HighBin.PrimePowerFourier
open HighBin.FiniteResidueFourier
open scoped Classical BigOperators ComplexConjugate

variable {R F : Type*} [CommRing R] [Field F] [Fintype R] [Fintype F]

/-- The algebraic support of every lifted residue Fourier coefficient. -/
def InFrequencySupport (π : R →+* F) (h : R) : Prop :=
  ∀ a : R, π a = 0 → h * a = 0

/-- Multiplication by an active frequency kills the residue kernel and
therefore defines a genuine additive character of the residue field. -/
def residueFrequency (π : R →+* F) (hπ : Function.Surjective π)
    (ψ : AddChar R ℂ) (h : R) (hh : InFrequencySupport π h) : AddChar F ℂ where
  toFun y := ψ (h * Classical.choose (hπ y))
  map_zero_eq_one' := by
    rw [hh _ (Classical.choose_spec (hπ 0)), ψ.map_zero_eq_one]
  map_add_eq_mul' a b := by
    have hz : π (Classical.choose (hπ (a + b)) - Classical.choose (hπ a) -
        Classical.choose (hπ b)) = 0 := by
      rw [map_sub, map_sub, Classical.choose_spec (hπ (a + b)),
        Classical.choose_spec (hπ a), Classical.choose_spec (hπ b)]
      abel
    have he : h * Classical.choose (hπ (a + b)) =
        h * Classical.choose (hπ a) + h * Classical.choose (hπ b) := by
      have hk := hh _ hz
      linear_combination hk
    rw [he, ψ.map_add_eq_mul]

@[simp] theorem residueFrequency_apply_residue (π : R →+* F)
    (hπ : Function.Surjective π) (ψ : AddChar R ℂ) (h : R)
    (hh : InFrequencySupport π h) (x : R) :
    residueFrequency π hπ ψ h hh (π x) = ψ (h * x) := by
  have hz : π (x - Classical.choose (hπ (π x))) = 0 := by
    rw [map_sub, Classical.choose_spec (hπ (π x)), sub_self]
  have he : h * Classical.choose (hπ (π x)) = h * x := by
    have hk := hh _ hz
    linear_combination -hk
  change ψ (h * Classical.choose (hπ (π x))) = _
  rw [he]

/-- Primitivity of the original ring pairing forces every nonzero active
frequency to be a nontrivial residue-field additive character. -/
theorem residueFrequency_ne_one (π : R →+* F) (hπ : Function.Surjective π)
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (h : R)
    (hh : InFrequencySupport π h) (h0 : h ≠ 0) :
    residueFrequency π hπ ψ h hh ≠ 1 := by
  intro he
  apply hψ h0
  ext x
  change ψ (h * x) = 1
  rw [← residueFrequency_apply_residue π hπ ψ h hh x, he]
  rfl

/-- No chosen Gauss scalar appears: cancellation follows from primitive
additive orthogonality inside the actual residue kernel. -/
theorem fourier_eq_zero_of_not_supported (π : R →+* F) (ψ : AddChar R ℂ)
    (hψ : ψ.IsPrimitive) (f : F → ℂ) (h : R)
    (hh : ¬ InFrequencySupport π h) :
    fourier ψ (fun x => f (π x)) h = 0 := by
  simp only [InFrequencySupport, not_forall, not_imp] at hh
  obtain ⟨a, ha, hha⟩ := hh
  obtain ⟨b, hb⟩ := AddChar.ne_one_iff.mp (hψ hha)
  apply fourier_pullback_eq_zero π f ψ h (a * b)
  · rw [map_mul, ha, zero_mul]
  · simpa only [AddChar.mulShift_apply, mul_assoc] using hb

/-- Exact finite-ring Gauss evaluation on its algebraic support. -/
theorem fourier_eq_card_mul_residue_gauss (π : R →+* F)
    (hπ : Function.Surjective π) (ψ : AddChar R ℂ) (χ : MulChar F ℂ)
    (h : R) (hh : InFrequencySupport π h) :
    fourier ψ (fun x => χ (π x)) h =
      (Nat.card {x : R // π x = 0} : ℂ) * gaussSum χ (residueFrequency π hπ ψ h hh) := by
  exact fourier_pullback_of_descends π hπ χ ψ
    (residueFrequency π hπ ψ h hh) h
    (fun x => (residueFrequency_apply_residue π hπ ψ h hh x).symm)

/-- The principal multiplicative character on a nonzero active frequency
contributes minus the kernel cardinality. This is the `-q^(n-1)` branch. -/
theorem principal_nonzero_active (π : R →+* F) (hπ : Function.Surjective π)
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (h : R)
    (hh : InFrequencySupport π h) (h0 : h ≠ 0) :
    fourier ψ (fun x => (1 : MulChar F ℂ) (π x)) h = -(Nat.card {x : R // π x = 0} : ℂ) := by
  rw [fourier_eq_card_mul_residue_gauss π hπ ψ 1 h hh,
    gaussSum_one_left (residueFrequency_ne_one π hπ ψ hψ h hh h0)]
  ring

/-- The principal zero-frequency branch is `#ker * (#F-1)`. -/
theorem principal_zero (π : R →+* F) (hπ : Function.Surjective π)
    (ψ : AddChar R ℂ) :
    fourier ψ (fun x => (1 : MulChar F ℂ) (π x)) 0 =
      (Nat.card {x : R // π x = 0} : ℂ) * ((Fintype.card F : ℂ) - 1) := by
  have hdesc : ∀ x : R, ψ (0 * x) = (1 : AddChar F ℂ) (π x) := by simp
  rw [fourier_pullback_of_descends π hπ (1 : MulChar F ℂ) ψ 1 0 hdesc]
  change (Nat.card {x : R // π x = 0} : ℂ) * gaussSum (1 : MulChar F ℂ) 1 = _
  rw [gaussSum_one_one, Nat.card_eq_fintype_card (α := Fˣ), Fintype.card_units]
  congr 1
  rw [Nat.cast_sub (show 1 ≤ Fintype.card F from Fintype.card_pos), Nat.cast_one]

/-- A nonprincipal residue character gives exactly zero at zero frequency. -/
theorem nonprincipal_zero (π : R →+* F) (hπ : Function.Surjective π)
    (ψ : AddChar R ℂ) (χ : MulChar F ℂ) (hχ : χ ≠ 1) :
    fourier ψ (fun x => χ (π x)) 0 = 0 := by
  have hdesc : ∀ x : R, ψ (0 * x) = (1 : AddChar F ℂ) (π x) := by simp
  rw [fourier_pullback_of_descends π hπ χ ψ 1 0 hdesc]
  change (Nat.card {x : R // π x = 0} : ℂ) * gaussSum χ 1 = _
  rw [gaussSum_one_right hχ, mul_zero]

/-- Exact square-root size of every nonprincipal active residue Gauss sum. -/
theorem nonprincipal_active_norm (π : R →+* F) (hπ : Function.Surjective π)
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    (h : R) (hh : InFrequencySupport π h) (h0 : h ≠ 0) :
    ‖fourier ψ (fun x => χ (π x)) h‖ =
      (Nat.card {x : R // π x = 0} : ℝ) * Real.sqrt (Fintype.card F) := by
  rw [fourier_eq_card_mul_residue_gauss π hπ ψ χ h hh, norm_mul,
    Complex.norm_natCast, gauss_norm χ hχ _
      (AddChar.IsPrimitive.of_ne_one (residueFrequency_ne_one π hπ ψ hψ h hh h0))]

/-- A fixed compatible primitive residue character identifies the local
unit phase by change of variables, with no Gauss-norm premise. -/
theorem unit_frequency_exact (π : R →+* F) (hπ : Function.Surjective π)
    (ψ : AddChar R ℂ) (φ : AddChar F ℂ) (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    (h₀ a : R) (hdesc : ∀ x : R, ψ (h₀ * x) = φ (π x)) :
    fourier ψ (fun x => χ (π x)) (h₀ * a) =
      (Nat.card {x : R // π x = 0} : ℂ) * (χ⁻¹ (π a) * gaussSum χ φ) := by
  have hd : ∀ x : R, ψ ((h₀ * a) * x) = (φ.mulShift (π a)) (π x) := by
    intro x
    rw [mul_assoc, hdesc, map_mul]
    rfl
  rw [fourier_pullback_of_descends π hπ χ ψ (φ.mulShift (π a)) (h₀ * a) hd]
  change (Nat.card {x : R // π x = 0} : ℂ) * gaussAt χ φ (π a) = _
  rw [gaussAt_eq_inv_mul χ hχ]

#print axioms fourier_eq_zero_of_not_supported
#print axioms fourier_eq_card_mul_residue_gauss
#print axioms principal_nonzero_active
#print axioms principal_zero
#print axioms nonprincipal_active_norm
#print axioms unit_frequency_exact

end HighBin.PrimePowerFourier
