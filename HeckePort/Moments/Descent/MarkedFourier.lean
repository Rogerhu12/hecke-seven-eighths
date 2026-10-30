import HeckePort.Moments.Descent.Completion

/-!
# Fourier expansion of marked completed sums

Port of openai/math `OAI/NumberTheory/DirichletL/Descent/MarkedFourier.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`, together with the finite additive Fourier
inversion it uses (`GaussSum/FiniteTranslations`, a statement about an arbitrary finite
commutative ring).

openai writes the residue of the primary generator as `Ideal.Quotient.mk (span {c}) (primaryGenerator A)`
and the frequency sums as `completedFixedFrequency Ψ c hc h W X`.  Here the residue is an
arbitrary function `r : Ideal (𝓞 K) → R` into a finite commutative ring `R` (over a general field:
`r A = Ideal.Quotient.mk _ (D.generator A)` for exterior `A`), the frequency sum is
`markedCompletedT s (fun A => ψ (h * r A))` (this *is* openai's `completedFixedFrequency`, whose
definition unfolds to this sum after multiplicativity of the phase), and the summand `s` is
abstract (`CompletedSummand`).  The divisor form (`markedCompletedT_divisor_fourier`) takes
the divisibility characterisation `D ∣ A ↔ r A = 0` as a hypothesis, which for the allowed generator
holds on exterior ideals.  The primary-support lemma `completed_summand_primary_support` is the
hypothesis `hsupp` of `Completion.markedCompletedT_congr_exterior`.
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators
open HeckePort.CenteredMomentGenerator

def finiteAdditiveFourierCoeff {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (φ : R → ℂ) (h : R) : ℂ :=
  (∑ x, φ x * ψ (-h * x)) / (Fintype.card R : ℂ)

lemma finiteAdditiveFourier_inversion {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (φ : R → ℂ) (x : R) :
    (∑ h, finiteAdditiveFourierCoeff ψ φ h * ψ (h * x)) = φ x := by
  have hN : (Fintype.card R : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ = (∑ h, ∑ y, φ y * ψ (-h * y) * ψ (h * x)) / (Fintype.card R : ℂ) := by
      simp only [finiteAdditiveFourierCoeff, div_mul_eq_mul_div, Finset.sum_mul, Finset.sum_div]
    _ = (∑ y, φ y * ∑ h, ψ (h * (x - y))) / (Fintype.card R : ℂ) := by
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      rw [mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    _ = (∑ y, φ y * (if x - y = 0 then (Fintype.card R : ℂ) else 0)) / (Fintype.card R : ℂ) := by
      simp only [AddChar.sum_mulShift _ hψ, apply_ite, Nat.cast_zero]
    _ = φ x := by
      have he : (∑ y, φ y * (if x - y = 0 then (Fintype.card R : ℂ) else 0)) =
          φ x * (Fintype.card R : ℂ) := by
        simp [sub_eq_zero]
      rw [he, mul_div_cancel_right₀ _ hN]

lemma finiteAdditiveFourierCoeff_zero_delta {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (h : R) :
    finiteAdditiveFourierCoeff ψ (fun x => if x = 0 then 1 else 0) h =
      (Fintype.card R : ℂ)⁻¹ := by
  simp [finiteAdditiveFourierCoeff]

variable {K : Type} [Field K] [NumberField K] {s : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ}

/-- The abstract content of openai's `markedCompletedT_quotient_fourier`: a pointwise finite
Fourier expansion commutes with the completed sum. -/
theorem markedCompletedT_finite_expansion (hs : CompletedSummand s) {ι : Type*} (t : Finset ι)
    (c : ι → ℂ) (ψ : ι → Ideal (𝓞 K) → ℂ) (d : Ideal (𝓞 K) → ℂ)
    (hd : ∀ A, d A = ∑ i ∈ t, c i * ψ i A) :
    markedCompletedT s d = ∑ i ∈ t, c i * markedCompletedT s (ψ i) := by
  have h1 : markedCompletedT s d = markedCompletedT s (fun A => ∑ i ∈ t, c i * ψ i A) := by
    unfold markedCompletedT
    simp only [hd]
  rw [h1, markedCompletedT_finset_sum hs t (fun i A => c i * ψ i A)]
  simp only [markedCompletedT_const_mul]

/-- openai `markedCompletedT_quotient_fourier`. -/
theorem markedCompletedT_quotient_fourier (hs : CompletedSummand s)
    {R : Type*} [CommRing R] [Fintype R] (r : Ideal (𝓞 K) → R)
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (F : R → ℂ) :
    markedCompletedT s (fun A => F (r A)) =
      ∑ h : R, finiteAdditiveFourierCoeff ψ F h *
        markedCompletedT s (fun A => ψ (h * r A)) :=
  markedCompletedT_finite_expansion hs Finset.univ _ (fun h A => ψ (h * r A)) _
    (fun A => (finiteAdditiveFourier_inversion ψ hψ F (r A)).symm)

/-- openai `markedCompletedT_divisor_fourier`; `hdiv` is the characterisation of divisibility by
the residue (`P ∣ A ↔ A ≤ P ↔ generator ∈ P`), valid on the ideals met by the summand. -/
theorem markedCompletedT_divisor_fourier (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hs : CompletedSummand s) (D : Ideal (𝓞 K))
    (hsupp : ∀ I J, s I J ≠ 0 → IsExterior K S (I * J ^ 3))
    {R : Type*} [CommRing R] [Fintype R] (r : Ideal (𝓞 K) → R)
    (hdiv : ∀ A, IsExterior K S A → (D ∣ A ↔ r A = 0))
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    markedCompletedT s (fun A => if D ∣ A then 1 else 0) =
      (Fintype.card R : ℂ)⁻¹ * ∑ h : R, markedCompletedT s (fun A => ψ (h * r A)) := by
  have hmark : markedCompletedT s (fun A => if D ∣ A then 1 else 0) =
      markedCompletedT s (fun A => if r A = 0 then 1 else 0) := by
    apply markedCompletedT_congr_exterior S _ _ hsupp
    intro A hA
    simp only [hdiv A hA]
  rw [hmark, markedCompletedT_quotient_fourier hs r ψ hψ (fun x : R => if x = 0 then (1 : ℂ) else 0)]
  simp only [finiteAdditiveFourierCoeff_zero_delta, Finset.mul_sum]

end HeckePort.Moments

end
