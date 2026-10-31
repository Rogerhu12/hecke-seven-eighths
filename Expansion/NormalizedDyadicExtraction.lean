import Expansion.LogDyadicBridge

/-! Finite dyadic extraction and Fourier normalization in one theorem.
The coefficients, including all zero masks, are unchanged.  The displayed
error is the actual Fourier tail; no spike or factorization is an input. -/

set_option autoImplicit false
noncomputable section
namespace Expansion.Dyadic

open MeasureTheory
open scoped Classical BigOperators ContDiff FourierTransform SchwartzMap
open ExpansionDetector.Fourier

variable {ι κ : Type*}

def weightedCoefficient (c : ι → ℂ) (N : ι → ℝ) (s : ℂ) (i : ι) : ℂ :=
  c i * (N i : ℂ) ^ (-s)

def finitePairSource (S : Finset ι) (T : Finset κ)
    (c : ι → ℂ) (d : κ → ℂ) (N : ι → ℝ) (M : κ → ℝ)
    (F : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∑ i ∈ S, ∑ l ∈ T,
    weightedCoefficient c N s i * weightedCoefficient d M s l * F (N i * M l)

def normalizedDyadicRHS (S : Finset ι) (T : Finset κ)
    (c : ι → ℂ) (d : κ → ℂ) (N : ι → ℝ) (M : κ → ℝ)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (s : ℂ)
    (j k : ℕ) (R : ℝ) (order : ℕ) (t : ℝ) : ℝ :=
  let D := (2 : ℝ) ^ j
  let E := (2 : ℝ) ^ k
  let A := sourceCoefficient c N annularProfile D s
  let B := sourceCoefficient d M annularProfile E s
  let g := logProductSchwartz F hF D E
  ((∑ i ∈ S, ‖A i‖) * (∑ l ∈ T, ‖B l‖)) / R ^ order *
    (∫ u : ℝ, (1 + ‖u‖) ^ order * ‖(𝓕 g) u‖) +
  (∫ u : ℝ, ‖(𝓕 g) u‖) *
    (D ^ (1 / 2 - s.re) * E ^ (1 / 2 - s.re) *
      ‖normalizedPolynomial S c N annularProfile D s.re (2 * Real.pi * t - s.im) *
        normalizedPolynomial T d M annularProfile E s.re (2 * Real.pi * t - s.im)‖)

/-- One actual dyadic pair and one common bounded frequency, with the exact
normalizing powers.  This is the full finite-source-to-frequency identity
and extraction step.  Absorption of its explicit tail uses uniform Fourier
moments and the chosen power-height budget separately. -/
theorem exists_normalized_dyadic_frequency (S : Finset ι) (T : Finset κ)
    (c : ι → ℂ) (d : κ → ℂ) (N : ι → ℝ) (M : κ → ℝ)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (s : ℂ) (n m : ℕ)
    (hN : ∀ i ∈ S, 1 ≤ N i ∧ N i ≤ (2 : ℝ) ^ n)
    (hM : ∀ l ∈ T, 1 ≤ M l ∧ M l ≤ (2 : ℝ) ^ m)
    (R : ℝ) (hR : 0 < R) (order : ℕ) (q : ℝ)
    (hq : q ≤ ‖finitePairSource S T c d N M F s‖) :
    ∃ j ≤ n, ∃ k ≤ m, ∃ t : ℝ, ‖t‖ ≤ R ∧
      q ≤ ((n + 1 : ℕ) : ℝ) * (m + 1 : ℕ) *
        normalizedDyadicRHS S T c d N M F hF s j k R order t := by
  let a := weightedCoefficient c N s
  let b := weightedCoefficient d M s
  let coeff : ι × κ → ℂ := fun p => a p.1 * b p.2 * F (N p.1 * M p.2)
  have hq' : q ≤ ‖∑ p ∈ S ×ˢ T, coeff p‖ := by
    simpa only [coeff, a, b, Finset.sum_product, finitePairSource] using hq
  obtain ⟨j, hj, k, hk, hlarge⟩ := exists_large_pairBlock (S ×ˢ T) coeff N M n m
    (fun p hp _ => hN p.1 (Finset.mem_product.mp hp).1)
    (fun p hp _ => hM p.2 (Finset.mem_product.mp hp).2) hq'
  obtain ⟨t, ht, hfreq⟩ := exists_pairBlock_frequency S T a b N M F hF j k R hR order
  refine ⟨j, hj, k, hk, t, ht, hlarge.trans ?_⟩
  have hcoefA : annularCoefficient a N ((2 : ℝ) ^ j) =
      sourceCoefficient c N annularProfile ((2 : ℝ) ^ j) s := rfl
  have hcoefB : annularCoefficient b M ((2 : ℝ) ^ k) =
      sourceCoefficient d M annularProfile ((2 : ℝ) ^ k) s := rfl
  rw [hcoefA, hcoefB, pair_phase_norm S T c d N M
    (fun i hi => zero_lt_one.trans_le (hN i hi).1)
    (fun l hl => zero_lt_one.trans_le (hM l hl).1)
    annularProfile annularProfile _ _ (by positivity) (by positivity)] at hfreq
  exact mul_le_mul_of_nonneg_left hfreq (by positivity)

/-- A quantified, explicit Fourier-tail inequality turns the extraction
into a product spike.  The tail premise concerns the constructed Fourier
profile, not either target polynomial. -/
theorem product_lower_of_fourier_budget
    (q count tail mass D E β product : ℝ)
    (hsource : q ≤ count * (tail + mass * (D ^ (1 / 2 - β) * E ^ (1 / 2 - β) * product)))
    (htail : count * tail ≤ q / 2) :
    q / 2 ≤ count * mass * D ^ (1 / 2 - β) * E ^ (1 / 2 - β) * product := by
  nlinarith

end Expansion.Dyadic
