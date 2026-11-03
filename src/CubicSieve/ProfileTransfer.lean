import CubicSieve.ProfileSeparation
import CubicSieve.CoprimeBilinear

/-! Parameter-separated Mellin transfer for a coprime-column Gram form. The
finite Gram cancellation is used at each spectral parameter before integration.
No entrywise estimate for the original weighted matrix is used. -/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.Profile

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open scoped Classical NumberField ComplexConjugate BigOperators

variable {K : Type} [Field K] [NumberField K] (A : SArithmeticData K)
variable {m n P : Type*} [Fintype m] [Fintype n] [DecidableEq P]

def profileWeightedRow (s : n → Finset P) (Q : m → n → ℂ)
    (r : m → ℝ) (x : n → ℝ) (z : n → ℂ) (i : m) : ℂ :=
  ∑ j, ∑ k, if Disjoint (s j) (s k) then
    (Q i j * z j) * star (Q i k * z k) * rawEnvelope A (r i / (x j * x k)) else 0

def separatedGram (s : n → Finset P) (Q : m → n → ℂ)
    (r : m → ℝ) (x : n → ℝ) (z : n → ℂ) (c : ℝ) (i : m) (τ : ℝ) : ℂ :=
  spectralDensity A c τ * rowPower c τ (r i) *
    CubicSieve.CoprimeBilinear.row s Q
      (fun j => z j * columnPower c τ (x j))
      (fun j => z j * columnPower c (-τ) (x j)) i

theorem profileWeightedRow_spectrum
    (s : n → Finset P) (Q : m → n → ℂ) (r : m → ℝ) (x : n → ℝ) (z : n → ℂ)
    (c : ℝ) (hc : 0 < c) (hr : ∀ i, 0 < r i) (hx : ∀ j, 0 < x j) :
    (∀ i, Integrable (separatedGram A s Q r x z c i)) ∧
      ∀ i, profileWeightedRow A s Q r x z i = ∫ τ : ℝ, separatedGram A s Q r x z c i τ := by
  let term (i : m) (j k : n) (τ : ℝ) : ℂ :=
    if Disjoint (s j) (s k) then
      ((Q i j * z j) * star (Q i k * z k)) *
        (spectralDensity A c τ * rowPower c τ (r i) *
          columnPower c τ (x j) * columnPower c τ (x k)) else 0
  have hi (i : m) (j k : n) : Integrable (term i j k) := by
    by_cases hd : Disjoint (s j) (s k)
    · simpa only [term, hd, if_true] using
        (separated_spectrum_integrable A c (r i) (x j) (x k) hc (hr i) (hx j) (hx k)).const_mul
          ((Q i j * z j) * star (Q i k * z k))
    · simp only [term, hd, if_false]
      exact integrable_zero _ _ _
  have hsum (i : m) : Integrable (fun τ => ∑ j, ∑ k, term i j k τ) :=
    integrable_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum Finset.univ (fun k _ => hi i j k))
  have hpoint (i : m) : separatedGram A s Q r x z c i =
      fun τ => ∑ j, ∑ k, term i j k τ := by
    funext τ
    simp only [separatedGram, CubicSieve.CoprimeBilinear.row, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    by_cases hd : Disjoint (s j) (s k)
    · simp only [hd, if_true, term, star_mul,
        columnPower_star c τ (x k) (hx k)]
      ring
    · simp [hd, term]
  constructor
  · intro i
    rw [hpoint i]
    exact hsum i
  · intro i
    rw [hpoint i,
      integral_finsetSum Finset.univ (fun j _ =>
        integrable_finsetSum Finset.univ (fun k _ => hi i j k))]
    unfold profileWeightedRow
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finsetSum Finset.univ (fun k _ => hi i j k)]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hd : Disjoint (s j) (s k)
    · simp only [term, hd, if_true]
      rw [integral_const_mul,
        ← dualProfile_separated A c (r i) (x j) (x k) hc (hr i) (hx j) (hx k),
        rawEnvelope_eq_dualProfile A _ (div_pos (hr i) (mul_pos (hx j) (hx k)))]
    · simp [term, hd]

theorem columnPower_energy_le (c τ : ℝ) (hc : 0 ≤ c)
    (x : n → ℝ) (hx : ∀ j, 0 < x j) (hx₁ : ∀ j, x j ≤ 1) (z : n → ℂ) :
    (∑ j, ‖z j * columnPower c τ (x j)‖ ^ 2) ≤ ∑ j, ‖z j‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul, mul_pow]
  have h₁ := columnPower_norm_le_one c τ (x j) hc (hx j) (hx₁ j)
  have h₂ : 0 ≤ ‖columnPower c τ (x j)‖ := norm_nonneg _
  have hp : ‖columnPower c τ (x j)‖ ^ 2 ≤ 1 := pow_le_one₀ h₂ h₁
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (sq_nonneg ‖z j‖)

/-- The operator bound survives both independently varying column norm factors.
The only additional cost is the true L1 norm of the Mellin density and a uniform
row-radius power bound. -/
theorem profileWeightedRow_spectral_bound
    (s : n → Finset P) (Q : m → n → ℂ) (r : m → ℝ) (x : n → ℝ) (z : n → ℂ)
    (c : ℝ) (hc : 0 < c) (hr : ∀ i, 0 < r i)
    (hx : ∀ j, 0 < x j) (hx₁ : ∀ j, x j ≤ 1)
    (U D E W : ℝ) (hU : 0 ≤ U) (hD : 0 ≤ D) (hE : 0 ≤ E) (hW : 0 ≤ W)
    (hcost : ∀ j, (2 : ℝ) ^ (s j).card ≤ D)
    (hQ : ∀ v : n → ℂ, (∑ i, ‖∑ j, Q i j * v j‖ ^ 2) ≤ U * ∑ j, ‖v j‖ ^ 2)
    (hz : (∑ j, ‖z j‖ ^ 2) ≤ E) (hrW : ∀ i, (r i) ^ (-c) ≤ W) :
    (∑ i, ‖profileWeightedRow A s Q r x z i‖) ≤
      (∫ τ : ℝ, ‖spectralDensity A c τ‖) * W * U * D * E := by
  obtain ⟨hint, heq⟩ := profileWeightedRow_spectrum A s Q r x z c hc hr hx
  have hb (τ : ℝ) :
      (∑ i, ‖separatedGram A s Q r x z c i τ‖) ≤
        ‖spectralDensity A c τ‖ * (W * (U * D * E)) := by
    have hbudget := CubicSieve.CoprimeBilinear.budget_bound s Q U D E hU hD hE hcost hQ
      (fun j => z j * columnPower c τ (x j))
      (fun j => z j * columnPower c (-τ) (x j))
      ((columnPower_energy_le c τ hc.le x hx hx₁ z).trans hz)
      ((columnPower_energy_le c (-τ) hc.le x hx hx₁ z).trans hz)
    simp only [separatedGram, norm_mul, mul_assoc]
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc
      (∑ i, ‖rowPower c τ (r i)‖ *
          ‖CubicSieve.CoprimeBilinear.row s Q
            (fun j => z j * columnPower c τ (x j))
            (fun j => z j * columnPower c (-τ) (x j)) i‖) ≤
          ∑ i, W * ‖CubicSieve.CoprimeBilinear.row s Q
            (fun j => z j * columnPower c τ (x j))
            (fun j => z j * columnPower c (-τ) (x j)) i‖ := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        rw [rowPower_norm c τ (r i) (hr i)]
        exact hrW i
      _ = W * ∑ i, ‖CubicSieve.CoprimeBilinear.row s Q
          (fun j => z j * columnPower c τ (x j))
          (fun j => z j * columnPower c (-τ) (x j)) i‖ := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbudget hW
  calc
    (∑ i, ‖profileWeightedRow A s Q r x z i‖) =
        ∑ i, ‖∫ τ : ℝ, separatedGram A s Q r x z c i τ‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [heq i]
    _ ≤ ∑ i, ∫ τ : ℝ, ‖separatedGram A s Q r x z c i τ‖ :=
      Finset.sum_le_sum fun i _ => norm_integral_le_integral_norm _
    _ = ∫ τ : ℝ, ∑ i, ‖separatedGram A s Q r x z c i τ‖ :=
      (integral_finsetSum Finset.univ (fun i _ => (hint i).norm)).symm
    _ ≤ ∫ τ : ℝ, ‖spectralDensity A c τ‖ * (W * (U * D * E)) :=
      integral_mono (integrable_finsetSum Finset.univ fun i _ => (hint i).norm)
        ((spectralDensity_integrable A c hc).norm.mul_const _) hb
    _ = (∫ τ : ℝ, ‖spectralDensity A c τ‖) * W * U * D * E := by
      rw [integral_mul_const]
      ring

theorem rowRadius_power_bound (c R r : ℝ) (hc : 0 ≤ c) (hR : 0 < R)
    (hr : R / 2 ≤ r) : r ^ (-c) ≤ (2 : ℝ) ^ c * R ^ (-c) := by
  calc
    r ^ (-c) ≤ (R / 2) ^ (-c) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hr (by linarith)
    _ = (2 : ℝ) ^ c * R ^ (-c) := by
      rw [Real.div_rpow hR.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [div_inv_eq_mul]
      ring

theorem decay_at_of_two_powers (v C₁ C₂ R : ℝ) (hR : 0 < R)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h₁ : v ≤ C₁ * R ^ (-(1 / 6 : ℝ)))
    (h₂ : v ≤ C₂ * R ^ (-(19 / 6 : ℝ))) :
    v ≤ (8 * (C₁ + C₂)) * R ^ (-(1 / 6 : ℝ)) / (1 + R) ^ 3 := by
  let f : ℝ → ℝ := fun t => if t = R then v else 0
  have hf₁ : ∀ t > 0, f t ≤ C₁ * t ^ (-(1 / 6 : ℝ)) := by
    intro t ht
    by_cases he : t = R
    · simpa [f, he] using h₁
    · simp only [f, he, if_false]
      positivity
  have hf₂ : ∀ t > 0, f t ≤ C₂ * t ^ (-(19 / 6 : ℝ)) := by
    intro t ht
    by_cases he : t = R
    · simpa [f, he] using h₂
    · simp only [f, he, if_false]
      positivity
  simpa [f] using decay_of_two_powers f C₁ C₂ hC₁ hC₂ hf₁ hf₂ R hR

def spectrumMass (c : ℝ) : ℝ := ∫ τ : ℝ, ‖spectralDensity A c τ‖

theorem spectrumMass_nonneg (c : ℝ) : 0 ≤ spectrumMass A c :=
  integral_nonneg fun _ => norm_nonneg _

/-- The common-profile transfer on an actual dyadic row-radius block. Both
column parameters remain in the kernel until the exact Mellin separation;
the Gram budget is then used on two independently contracted vectors. -/
theorem profileWeightedRow_block_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {m n P : Type*} [Fintype m] [Fintype n] [DecidableEq P]
      (s : n → Finset P) (Q : m → n → ℂ)
      (r : m → ℝ) (x : n → ℝ) (z : n → ℂ) (R U D E : ℝ),
      0 < R → 0 ≤ U → 0 ≤ D → 0 ≤ E →
      (∀ i, R / 2 ≤ r i) → (∀ j, 0 < x j) → (∀ j, x j ≤ 1) →
      (∀ j, (2 : ℝ) ^ (s j).card ≤ D) →
      (∀ v : n → ℂ, (∑ i, ‖∑ j, Q i j * v j‖ ^ 2) ≤ U * ∑ j, ‖v j‖ ^ 2) →
      (∑ j, ‖z j‖ ^ 2) ≤ E →
      (∑ i, ‖profileWeightedRow A s Q r x z i‖) ≤
        C * (R ^ (-(1 / 6 : ℝ)) / (1 + R) ^ 3) * U * D * E := by
  let C₁ := spectrumMass A (1 / 6) * (2 : ℝ) ^ (1 / 6 : ℝ)
  let C₂ := spectrumMass A (19 / 6) * (2 : ℝ) ^ (19 / 6 : ℝ)
  have hC₁ : 0 ≤ C₁ := mul_nonneg (spectrumMass_nonneg A _) (by positivity)
  have hC₂ : 0 ≤ C₂ := mul_nonneg (spectrumMass_nonneg A _) (by positivity)
  refine ⟨8 * (C₁ + C₂) + 1, by positivity, ?_⟩
  intro m n P _ _ _ s Q r x z R U D E hR hU hD hE hr hx hx₁ hcost hQ hz
  have hr₀ : ∀ i, 0 < r i := fun i => lt_of_lt_of_le (by positivity) (hr i)
  have hsmall := profileWeightedRow_spectral_bound A s Q r x z (1 / 6) (by norm_num)
    hr₀ hx hx₁ U D E ((2 : ℝ) ^ (1 / 6 : ℝ) * R ^ (-(1 / 6 : ℝ)))
    hU hD hE (by positivity) hcost hQ hz
    (fun i => rowRadius_power_bound (1 / 6) R (r i) (by norm_num) hR (hr i))
  have hlarge := profileWeightedRow_spectral_bound A s Q r x z (19 / 6) (by norm_num)
    hr₀ hx hx₁ U D E ((2 : ℝ) ^ (19 / 6 : ℝ) * R ^ (-(19 / 6 : ℝ)))
    hU hD hE (by positivity) hcost hQ hz
    (fun i => rowRadius_power_bound (19 / 6) R (r i) (by norm_num) hR (hr i))
  have h₁ : (∑ i, ‖profileWeightedRow A s Q r x z i‖) ≤
      (C₁ * (U * D * E)) * R ^ (-(1 / 6 : ℝ)) := by
    convert hsmall using 1 <;> dsimp [C₁, spectrumMass] <;> ring
  have h₂ : (∑ i, ‖profileWeightedRow A s Q r x z i‖) ≤
      (C₂ * (U * D * E)) * R ^ (-(19 / 6 : ℝ)) := by
    convert hlarge using 1 <;> dsimp [C₂, spectrumMass] <;> ring
  have hb := decay_at_of_two_powers _ (C₁ * (U * D * E)) (C₂ * (U * D * E)) R hR
    (by positivity) (by positivity) h₁ h₂
  calc
    (∑ i, ‖profileWeightedRow A s Q r x z i‖) ≤
        8 * (C₁ * (U * D * E) + C₂ * (U * D * E)) * R ^ (-(1 / 6 : ℝ)) /
          (1 + R) ^ 3 := hb
    _ = (8 * (C₁ + C₂)) *
        (R ^ (-(1 / 6 : ℝ)) / (1 + R) ^ 3 * (U * D * E)) := by ring
    _ ≤ (8 * (C₁ + C₂) + 1) *
        (R ^ (-(1 / 6 : ℝ)) / (1 + R) ^ 3 * (U * D * E)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (8 * (C₁ + C₂) + 1) *
        (R ^ (-(1 / 6 : ℝ)) / (1 + R) ^ 3) * U * D * E := by ring

end CubicSieve.Profile

namespace CubicSieve.Profile.Gaussian

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open scoped Classical NumberField ComplexConjugate BigOperators

variable {K : Type} [Field K] [NumberField K] (A : SArithmeticData K)
variable {m n P : Type*} [Fintype m] [Fintype n] [DecidableEq P]

def profileWeightedRow (s : n → Finset P) (Q : m → n → ℂ)
    (r : m → ℝ) (x : n → ℝ) (z : n → ℂ) (i : m) : ℂ :=
  ∑ j, ∑ k, if Disjoint (s j) (s k) then
    (Q i j * z j) * star (Q i k * z k) * rawEnvelope A (r i / (x j * x k)) else 0

def separatedGram (s : n → Finset P) (Q : m → n → ℂ)
    (r : m → ℝ) (x : n → ℝ) (z : n → ℂ) (c : ℝ) (i : m) (τ : ℝ) : ℂ :=
  spectralDensity A c τ * rowPower c τ (r i) *
    CubicSieve.CoprimeBilinear.row s Q
      (fun j => z j * columnPower c τ (x j))
      (fun j => z j * columnPower c (-τ) (x j)) i

theorem profileWeightedRow_spectrum
    (s : n → Finset P) (Q : m → n → ℂ) (r : m → ℝ) (x : n → ℝ) (z : n → ℂ)
    (c : ℝ) (hc : 0 < c) (hr : ∀ i, 0 < r i) (hx : ∀ j, 0 < x j) :
    (∀ i, Integrable (separatedGram A s Q r x z c i)) ∧
      ∀ i, profileWeightedRow A s Q r x z i = ∫ τ : ℝ, separatedGram A s Q r x z c i τ := by
  let term (i : m) (j k : n) (τ : ℝ) : ℂ :=
    if Disjoint (s j) (s k) then
      ((Q i j * z j) * star (Q i k * z k)) *
        (spectralDensity A c τ * rowPower c τ (r i) *
          columnPower c τ (x j) * columnPower c τ (x k)) else 0
  have hi (i : m) (j k : n) : Integrable (term i j k) := by
    by_cases hd : Disjoint (s j) (s k)
    · simpa only [term, hd, if_true] using
        (separated_spectrum_integrable A c (r i) (x j) (x k) hc (hr i) (hx j) (hx k)).const_mul
          ((Q i j * z j) * star (Q i k * z k))
    · simp only [term, hd, if_false]
      exact integrable_zero _ _ _
  have hsum (i : m) : Integrable (fun τ => ∑ j, ∑ k, term i j k τ) :=
    integrable_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum Finset.univ (fun k _ => hi i j k))
  have hpoint (i : m) : separatedGram A s Q r x z c i =
      fun τ => ∑ j, ∑ k, term i j k τ := by
    funext τ
    simp only [separatedGram, CubicSieve.CoprimeBilinear.row, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    by_cases hd : Disjoint (s j) (s k)
    · simp only [hd, if_true, term, star_mul,
        columnPower_star c τ (x k) (hx k)]
      ring
    · simp [hd, term]
  constructor
  · intro i
    rw [hpoint i]
    exact hsum i
  · intro i
    rw [hpoint i,
      integral_finsetSum Finset.univ (fun j _ =>
        integrable_finsetSum Finset.univ (fun k _ => hi i j k))]
    unfold profileWeightedRow
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finsetSum Finset.univ (fun k _ => hi i j k)]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hd : Disjoint (s j) (s k)
    · simp only [term, hd, if_true]
      rw [integral_const_mul,
        ← dualProfile_separated A c (r i) (x j) (x k) hc (hr i) (hx j) (hx k),
        rawEnvelope_eq_dualProfile A _ (div_pos (hr i) (mul_pos (hx j) (hx k)))]
    · simp [term, hd]

theorem columnPower_energy_le (c τ : ℝ) (hc : 0 ≤ c)
    (x : n → ℝ) (hx : ∀ j, 0 < x j) (hx₁ : ∀ j, x j ≤ 1) (z : n → ℂ) :
    (∑ j, ‖z j * columnPower c τ (x j)‖ ^ 2) ≤ ∑ j, ‖z j‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul, mul_pow]
  have h₁ := columnPower_norm_le_one c τ (x j) hc (hx j) (hx₁ j)
  have h₂ : 0 ≤ ‖columnPower c τ (x j)‖ := norm_nonneg _
  have hp : ‖columnPower c τ (x j)‖ ^ 2 ≤ 1 := pow_le_one₀ h₂ h₁
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (sq_nonneg ‖z j‖)

/-- The operator bound survives both independently varying column norm factors.
The only additional cost is the true L1 norm of the Mellin density and a uniform
row-radius power bound. -/
theorem profileWeightedRow_spectral_bound
    (s : n → Finset P) (Q : m → n → ℂ) (r : m → ℝ) (x : n → ℝ) (z : n → ℂ)
    (c : ℝ) (hc : 0 < c) (hr : ∀ i, 0 < r i)
    (hx : ∀ j, 0 < x j) (hx₁ : ∀ j, x j ≤ 1)
    (U D E W : ℝ) (hU : 0 ≤ U) (hD : 0 ≤ D) (hE : 0 ≤ E) (hW : 0 ≤ W)
    (hcost : ∀ j, (2 : ℝ) ^ (s j).card ≤ D)
    (hQ : ∀ v : n → ℂ, (∑ i, ‖∑ j, Q i j * v j‖ ^ 2) ≤ U * ∑ j, ‖v j‖ ^ 2)
    (hz : (∑ j, ‖z j‖ ^ 2) ≤ E) (hrW : ∀ i, (r i) ^ (-c) ≤ W) :
    (∑ i, ‖profileWeightedRow A s Q r x z i‖) ≤
      (∫ τ : ℝ, ‖spectralDensity A c τ‖) * W * U * D * E := by
  obtain ⟨hint, heq⟩ := profileWeightedRow_spectrum A s Q r x z c hc hr hx
  have hb (τ : ℝ) :
      (∑ i, ‖separatedGram A s Q r x z c i τ‖) ≤
        ‖spectralDensity A c τ‖ * (W * (U * D * E)) := by
    have hbudget := CubicSieve.CoprimeBilinear.budget_bound s Q U D E hU hD hE hcost hQ
      (fun j => z j * columnPower c τ (x j))
      (fun j => z j * columnPower c (-τ) (x j))
      ((columnPower_energy_le c τ hc.le x hx hx₁ z).trans hz)
      ((columnPower_energy_le c (-τ) hc.le x hx hx₁ z).trans hz)
    simp only [separatedGram, norm_mul, mul_assoc]
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc
      (∑ i, ‖rowPower c τ (r i)‖ *
          ‖CubicSieve.CoprimeBilinear.row s Q
            (fun j => z j * columnPower c τ (x j))
            (fun j => z j * columnPower c (-τ) (x j)) i‖) ≤
          ∑ i, W * ‖CubicSieve.CoprimeBilinear.row s Q
            (fun j => z j * columnPower c τ (x j))
            (fun j => z j * columnPower c (-τ) (x j)) i‖ := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        rw [rowPower_norm c τ (r i) (hr i)]
        exact hrW i
      _ = W * ∑ i, ‖CubicSieve.CoprimeBilinear.row s Q
          (fun j => z j * columnPower c τ (x j))
          (fun j => z j * columnPower c (-τ) (x j)) i‖ := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbudget hW
  calc
    (∑ i, ‖profileWeightedRow A s Q r x z i‖) =
        ∑ i, ‖∫ τ : ℝ, separatedGram A s Q r x z c i τ‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [heq i]
    _ ≤ ∑ i, ∫ τ : ℝ, ‖separatedGram A s Q r x z c i τ‖ :=
      Finset.sum_le_sum fun i _ => norm_integral_le_integral_norm _
    _ = ∫ τ : ℝ, ∑ i, ‖separatedGram A s Q r x z c i τ‖ :=
      (integral_finsetSum Finset.univ (fun i _ => (hint i).norm)).symm
    _ ≤ ∫ τ : ℝ, ‖spectralDensity A c τ‖ * (W * (U * D * E)) :=
      integral_mono (integrable_finsetSum Finset.univ fun i _ => (hint i).norm)
        ((spectralDensity_integrable A c hc).norm.mul_const _) hb
    _ = (∫ τ : ℝ, ‖spectralDensity A c τ‖) * W * U * D * E := by
      rw [integral_mul_const]
      ring

theorem rowRadius_power_bound (c R r : ℝ) (hc : 0 ≤ c) (hR : 0 < R)
    (hr : R / 2 ≤ r) : r ^ (-c) ≤ (2 : ℝ) ^ c * R ^ (-c) := by
  calc
    r ^ (-c) ≤ (R / 2) ^ (-c) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hr (by linarith)
    _ = (2 : ℝ) ^ c * R ^ (-c) := by
      rw [Real.div_rpow hR.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [div_inv_eq_mul]
      ring

theorem decay_at_of_two_powers (v C₁ C₂ R : ℝ) (hR : 0 < R)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h₁ : v ≤ C₁ * R ^ (-(1 / 6 : ℝ)))
    (h₂ : v ≤ C₂ * R ^ (-(19 / 6 : ℝ))) :
    v ≤ (8 * (C₁ + C₂)) * R ^ (-(1 / 6 : ℝ)) / (1 + R) ^ 3 := by
  let f : ℝ → ℝ := fun t => if t = R then v else 0
  have hf₁ : ∀ t > 0, f t ≤ C₁ * t ^ (-(1 / 6 : ℝ)) := by
    intro t ht
    by_cases he : t = R
    · simpa [f, he] using h₁
    · simp only [f, he, if_false]
      positivity
  have hf₂ : ∀ t > 0, f t ≤ C₂ * t ^ (-(19 / 6 : ℝ)) := by
    intro t ht
    by_cases he : t = R
    · simpa [f, he] using h₂
    · simp only [f, he, if_false]
      positivity
  simpa [f] using decay_of_two_powers f C₁ C₂ hC₁ hC₂ hf₁ hf₂ R hR

def spectrumMass (c : ℝ) : ℝ := ∫ τ : ℝ, ‖spectralDensity A c τ‖

theorem spectrumMass_nonneg (c : ℝ) : 0 ≤ spectrumMass A c :=
  integral_nonneg fun _ => norm_nonneg _

/-- The common-profile transfer on an actual dyadic row-radius block. Both
column parameters remain in the kernel until the exact Mellin separation;
the Gram budget is then used on two independently contracted vectors. -/
theorem profileWeightedRow_block_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {m n P : Type*} [Fintype m] [Fintype n] [DecidableEq P]
      (s : n → Finset P) (Q : m → n → ℂ)
      (r : m → ℝ) (x : n → ℝ) (z : n → ℂ) (R U D E : ℝ),
      0 < R → 0 ≤ U → 0 ≤ D → 0 ≤ E →
      (∀ i, R / 2 ≤ r i) → (∀ j, 0 < x j) → (∀ j, x j ≤ 1) →
      (∀ j, (2 : ℝ) ^ (s j).card ≤ D) →
      (∀ v : n → ℂ, (∑ i, ‖∑ j, Q i j * v j‖ ^ 2) ≤ U * ∑ j, ‖v j‖ ^ 2) →
      (∑ j, ‖z j‖ ^ 2) ≤ E →
      (∑ i, ‖profileWeightedRow A s Q r x z i‖) ≤
        C * (R ^ (-(1 / 6 : ℝ)) / (1 + R) ^ 3) * U * D * E := by
  let C₁ := spectrumMass A (1 / 6) * (2 : ℝ) ^ (1 / 6 : ℝ)
  let C₂ := spectrumMass A (19 / 6) * (2 : ℝ) ^ (19 / 6 : ℝ)
  have hC₁ : 0 ≤ C₁ := mul_nonneg (spectrumMass_nonneg A _) (by positivity)
  have hC₂ : 0 ≤ C₂ := mul_nonneg (spectrumMass_nonneg A _) (by positivity)
  refine ⟨8 * (C₁ + C₂) + 1, by positivity, ?_⟩
  intro m n P _ _ _ s Q r x z R U D E hR hU hD hE hr hx hx₁ hcost hQ hz
  have hr₀ : ∀ i, 0 < r i := fun i => lt_of_lt_of_le (by positivity) (hr i)
  have hsmall := profileWeightedRow_spectral_bound A s Q r x z (1 / 6) (by norm_num)
    hr₀ hx hx₁ U D E ((2 : ℝ) ^ (1 / 6 : ℝ) * R ^ (-(1 / 6 : ℝ)))
    hU hD hE (by positivity) hcost hQ hz
    (fun i => rowRadius_power_bound (1 / 6) R (r i) (by norm_num) hR (hr i))
  have hlarge := profileWeightedRow_spectral_bound A s Q r x z (19 / 6) (by norm_num)
    hr₀ hx hx₁ U D E ((2 : ℝ) ^ (19 / 6 : ℝ) * R ^ (-(19 / 6 : ℝ)))
    hU hD hE (by positivity) hcost hQ hz
    (fun i => rowRadius_power_bound (19 / 6) R (r i) (by norm_num) hR (hr i))
  have h₁ : (∑ i, ‖profileWeightedRow A s Q r x z i‖) ≤
      (C₁ * (U * D * E)) * R ^ (-(1 / 6 : ℝ)) := by
    convert hsmall using 1 <;> dsimp [C₁, spectrumMass] <;> ring
  have h₂ : (∑ i, ‖profileWeightedRow A s Q r x z i‖) ≤
      (C₂ * (U * D * E)) * R ^ (-(19 / 6 : ℝ)) := by
    convert hlarge using 1 <;> dsimp [C₂, spectrumMass] <;> ring
  have hb := decay_at_of_two_powers _ (C₁ * (U * D * E)) (C₂ * (U * D * E)) R hR
    (by positivity) (by positivity) h₁ h₂
  calc
    (∑ i, ‖profileWeightedRow A s Q r x z i‖) ≤
        8 * (C₁ * (U * D * E) + C₂ * (U * D * E)) * R ^ (-(1 / 6 : ℝ)) /
          (1 + R) ^ 3 := hb
    _ = (8 * (C₁ + C₂)) *
        (R ^ (-(1 / 6 : ℝ)) / (1 + R) ^ 3 * (U * D * E)) := by ring
    _ ≤ (8 * (C₁ + C₂) + 1) *
        (R ^ (-(1 / 6 : ℝ)) / (1 + R) ^ 3 * (U * D * E)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (8 * (C₁ + C₂) + 1) *
        (R ^ (-(1 / 6 : ℝ)) / (1 + R) ^ 3) * U * D * E := by ring


end CubicSieve.Profile.Gaussian
