import HeckePort.Moments.Descent.Hybrid

/-!
# Quotient supports

Port of openai/math `OAI/NumberTheory/DirichletL/Descent/Quotients.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`.

Verbatim in shape: `quotientSupport`, `mem_quotientSupport`, `sum_quotientSupport`,
`quotientSupport_nonzero`, `quotientSupport_norm_le`, `quotientSupport_shell`.

Generalized: the two admissibility statements (`CanonicalQuadraticSieve.Admissible`,
`CubicSieve.Admissible`) are replaced by the single `quotientSupport_admissible` for an arbitrary
predicate `Adm` closed under divisors (the closure property, openai `admissible_of_dvd` /
`cubic_admissible_of_dvd`, is the hypothesis `hAdm`).  The energy bound
`quotient_hybridCubicCoefficient_energy` has the constant `256 = 2 * 128` replaced by
`2 * idealCountConstant K` and the kernel by an abstract `CubicKernelAxioms` kernel.
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators
open HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]

def quotientSupport (D : Ideal (𝓞 K)) (S : Finset (Ideal (𝓞 K))) : Finset (Ideal (𝓞 K)) :=
  (S.filter (fun I => D ∣ I)).image (idealQuotient D)

theorem idealQuotient_injective_on (D : Ideal (𝓞 K)) {I J : Ideal (𝓞 K)} (hI : D ∣ I)
    (hJ : D ∣ J) (h : idealQuotient D I = idealQuotient D J) : I = J := by
  rw [← idealQuotient_mul hI, ← idealQuotient_mul hJ, h]

@[simp] theorem mem_quotientSupport (D J : Ideal (𝓞 K)) (hD : D ≠ ⊥)
    (S : Finset (Ideal (𝓞 K))) :
    J ∈ quotientSupport D S ↔ D * J ∈ S := by
  constructor
  · intro hJ
    obtain ⟨I, hI, he⟩ := Finset.mem_image.mp hJ
    obtain ⟨hIS, hDI⟩ := Finset.mem_filter.mp hI
    rw [← he, idealQuotient_mul hDI]
    exact hIS
  · intro hJ
    refine Finset.mem_image.mpr ⟨D * J, Finset.mem_filter.mpr ⟨hJ, dvd_mul_right _ _⟩, ?_⟩
    exact mul_left_cancel₀ hD (idealQuotient_mul (dvd_mul_right D J))

theorem sum_quotientSupport {A : Type*} [AddCommMonoid A]
    (D : Ideal (𝓞 K)) (S : Finset (Ideal (𝓞 K))) (f : Ideal (𝓞 K) → A) :
    (∑ I ∈ S with D ∣ I, f I) = ∑ J ∈ quotientSupport D S, f (D * J) := by
  rw [quotientSupport, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro I hI
    rw [idealQuotient_mul (Finset.mem_filter.mp hI).2]
  · intro I hI J hJ he
    exact idealQuotient_injective_on D (Finset.mem_filter.mp hI).2
      (Finset.mem_filter.mp hJ).2 he

theorem quotientSupport_nonzero (D : Ideal (𝓞 K)) (hD : D ≠ ⊥)
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ I ∈ S, I ≠ ⊥)
    (J : Ideal (𝓞 K)) (hJ : J ∈ quotientSupport D S) : J ≠ ⊥ := by
  have h := hS (D * J) ((mem_quotientSupport D J hD S).mp hJ)
  exact (mul_ne_zero_iff.mp h).2

/-- openai `quotientSupport_quadratic_admissible` and `quotientSupport_cubic_admissible`, for
any predicate `Adm` closed under divisors (`hAdm`). -/
theorem quotientSupport_admissible (Adm : Ideal (𝓞 K) → Prop)
    (hAdm : ∀ I J : Ideal (𝓞 K), Adm I → J ∣ I → Adm J)
    (D : Ideal (𝓞 K)) (hD : D ≠ ⊥)
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ I ∈ S, Adm I)
    (J : Ideal (𝓞 K)) (hJ : J ∈ quotientSupport D S) : Adm J :=
  hAdm _ _ (hS (D * J) ((mem_quotientSupport D J hD S).mp hJ)) (dvd_mul_left _ _)

theorem quotientSupport_norm_le (D : Ideal (𝓞 K)) (hD : D ≠ ⊥)
    (S : Finset (Ideal (𝓞 K))) (N : ℝ)
    (hS0 : ∀ I ∈ S, I ≠ ⊥) (hS : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ N)
    (J : Ideal (𝓞 K)) (hJ : J ∈ quotientSupport D S) :
    (Ideal.absNorm J : ℝ) ≤ N := by
  have hDJ := (mem_quotientSupport D J hD S).mp hJ
  have hn : Ideal.absNorm J ≤ Ideal.absNorm (D * J) := by
    apply Nat.le_of_dvd
    · exact Nat.pos_of_ne_zero (fun hz => hS0 _ hDJ (Ideal.absNorm_eq_zero_iff.mp hz))
    · exact map_dvd Ideal.absNorm (dvd_mul_left J D)
  exact (Nat.cast_le.mpr hn).trans (hS _ hDJ)

theorem quotientSupport_shell (D : Ideal (𝓞 K)) (hD : D ≠ ⊥)
    (S : Finset (Ideal (𝓞 K))) (L : ℝ)
    (hS0 : ∀ I ∈ S, I ≠ ⊥)
    (hS : ∀ I ∈ S, L ≤ (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) ≤ 2 * L)
    (J : Ideal (𝓞 K)) (hJ : J ∈ quotientSupport D S) :
    max 1 (L / (Ideal.absNorm D : ℝ)) ≤ (Ideal.absNorm J : ℝ) ∧
      (Ideal.absNorm J : ℝ) ≤ 2 * max 1 (L / (Ideal.absNorm D : ℝ)) := by
  have hDJ := (mem_quotientSupport D J hD S).mp hJ
  have hnD : 0 < (Ideal.absNorm D : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hD (Ideal.absNorm_eq_zero_iff.mp hz))
  have hJ0 := quotientSupport_nonzero D hD S hS0 J hJ
  have hnJ : 1 ≤ (Ideal.absNorm J : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun hz => hJ0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hs := hS (D * J) hDJ
  simp only [map_mul, Nat.cast_mul] at hs
  constructor
  · refine max_le hnJ ((div_le_iff₀ hnD).mpr ?_)
    simpa only [mul_comm] using hs.1
  · have hj : (Ideal.absNorm J : ℝ) ≤ 2 * (L / (Ideal.absNorm D : ℝ)) := by
      have hj := (le_div_iff₀ hnD).mpr (show
          (Ideal.absNorm J : ℝ) * (Ideal.absNorm D : ℝ) ≤ 2 * L by
        simpa only [mul_comm] using hs.2)
      simpa only [mul_div_assoc] using hj
    exact hj.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num))

theorem quotient_hybridCubicCoefficient_energy {Ext : Ideal (𝓞 K) → Prop}
    {κ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ} (hκ : CubicKernelAxioms Ext κ)
    (R r h t : Ideal (𝓞 K)) (hR : R ≠ ⊥) (S : Finset (Ideal (𝓞 K))) (L : ℝ)
    (hS0 : ∀ I ∈ S, I ≠ ⊥)
    (hS : ∀ I ∈ S, L ≤ (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) ≤ 2 * L)
    (a : Ideal (𝓞 K) → ℂ) (ha : ∀ I ∈ S, ‖a I‖ ≤ 1) :
    (∑ P ∈ quotientSupport R S, ‖hybridCubicCoefficient κ Ext R r h t a P‖ ^ 2) ≤
      2 * idealCountConstant K := by
  apply hybridCubicCoefficient_energy hκ R r h t (quotientSupport R S)
    (max 1 (L / (Ideal.absNorm R : ℝ))) (le_max_left _ _)
  · exact quotientSupport_shell R hR S L hS0 hS
  · intro P hP
    exact ha (R * P) ((mem_quotientSupport R P hR S).mp hP)

end HeckePort.Moments

end
