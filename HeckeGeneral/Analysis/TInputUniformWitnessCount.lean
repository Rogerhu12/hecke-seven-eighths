import HeckeGeneral.Analysis.TInputUniformMoments
import HeckeGeneral.Analysis.MomentWitnessCount

/-!
Uniform moment-to-threshold counting for a whole active label family.
The moment constants and height data remain common to every active label.
This is a consumer of UniformMI/P-type estimates, not a deduction of those
uniform estimates from the older fixed-parameter moment inputs. Summing
over a growing active family still requires a bound on its cardinality.
-/

noncomputable section
namespace HeckeGeneral.Analysis.ConditionalMoments

open NumberField IsDedekindDomain HeckeGeneral.Characters
open scoped Classical BigOperators

theorem uniformPolynomialHeightBound_power_mono {ι : Type}
    {active : ℝ → Finset ι} {E : ℝ → ℝ → ι → ℝ}
    {p q : ℝ → ι → ℝ} {ε : ℝ}
    (h : UniformPolynomialHeightBound active E p ε)
    (hpq : ∀ Z, 1 ≤ Z → ∀ i ∈ active Z, p Z i ≤ q Z i) :
    UniformPolynomialHeightBound active E q ε := by
  obtain ⟨C, Z₀, A, ceiling, hC, hZ₀, hA, hh, hb⟩ := h
  refine ⟨C, Z₀, A, ceiling, hC, hZ₀, hA, hh, ?_⟩
  intro Z t hZ ht i hi
  apply (hb Z t hZ ht i hi).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (hZ₀.trans hZ)
        (add_le_add (hpq Z (hZ₀.trans hZ) i hi) le_rfl)) hC.le)
    (Real.rpow_nonneg (by positivity) _)

/-- Exact subtraction of the squared-norm threshold exponent, even when
both exponents depend on scale and label. No new constants are chosen. -/
theorem uniformPolynomialHeightBound_energyWitnessRows {ι κ : Type}
    (active : ℝ → Finset ι) (F : ℝ → ℝ → ι → Finset κ)
    (z : ℝ → ℝ → ι → κ → ℂ) {p : ℝ → ι → ℝ} {ε : ℝ}
    (h : UniformPolynomialHeightBound active
      (fun Z t i => ∑ u ∈ F Z t i, ‖z Z t i u‖ ^ 2) p ε)
    (v : ℝ → ι → ℝ) :
    UniformPolynomialHeightBound active
      (fun Z t i => ((energyWitnessRows (F Z t i) (z Z t i) Z (v Z i)).card : ℝ))
      (fun Z i => p Z i - v Z i) ε := by
  obtain ⟨C, Z₀, A, ceiling, hC, hZ₀, hA, hh, hb⟩ := h
  refine ⟨C, Z₀, A, ceiling, hC, hZ₀, hA, hh, ?_⟩
  intro Z t hZ ht i hi
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one (hZ₀.trans hZ)
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hZpos (v Z i))).mp
  calc
    _ ≤ ∑ u ∈ F Z t i, ‖z Z t i u‖ ^ 2 := energyWitnessRows_card_mul_le ..
    _ ≤ C * Z ^ (p Z i + ε) * (1 + |t|) ^ A := hb Z t hZ ht i hi
    _ = _ := by
      have he : p Z i + ε = (p Z i - v Z i + ε) + v Z i := by ring
      rw [he, Real.rpow_add hZpos]
      ring

variable (K : Type) [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

theorem uniform_inverseWitnessRows_polynomialHeightBound {ι : Type}
    (active : ℝ → Finset ι) (d : ℝ → ι → MomentData K ω ψ)
    (a : ℝ → ι → RealParameters) {ε : ℝ}
    (h : UniformPolynomialHeightBound active
      (fun Z t i => inverseEnergy (d Z i) (a Z i) Z t)
      (fun Z i => (a Z i).m) ε) (v : ℝ → ι → ℝ) :
    UniformPolynomialHeightBound active
      (fun Z t i => ((inverseWitnessRows K (d Z i) (a Z i) Z t (v Z i)).card : ℝ))
      (fun Z i => (a Z i).m - v Z i) ε :=
  uniformPolynomialHeightBound_energyWitnessRows active
    (fun Z _ i => (d Z i).rows (Z ^ (a Z i).m))
    (fun Z t i u => inversePolynomial (d Z i) u (Z ^ (a Z i).r) t *
      slotProduct (d Z i) u Z t) h v

theorem uniform_pairedWitnessRows_polynomialHeightBound {ι : Type}
    (active : ℝ → Finset ι) (d : ℝ → ι → MomentData K ω ψ)
    (a : ℝ → ι → RealParameters) {ε : ℝ}
    (h : UniformPolynomialHeightBound active
      (fun Z t i => pairedEnergy (d Z i) (a Z i) Z t)
      (fun Z i => (a Z i).m + (a Z i).q) ε) (v : ℝ → ι → ℝ) :
    UniformPolynomialHeightBound active
      (fun Z t i => ((pairedWitnessRows K (d Z i) (a Z i) Z t (v Z i)).card : ℝ))
      (fun Z i => (a Z i).m + (a Z i).q - v Z i) ε :=
  uniformPolynomialHeightBound_energyWitnessRows active
    (fun Z _ i => pairedRows (d Z i) (a Z i) Z)
    (fun Z t i u => plainPolynomial (d Z i) (d Z i).plainTest₁ u (Z ^ (a Z i).n₁) t *
      plainPolynomial (d Z i) (d Z i).plainTest₂ u (Z ^ (a Z i).n₂) t *
      slotProduct (d Z i) u Z t) h v

end HeckeGeneral.Analysis.ConditionalMoments
