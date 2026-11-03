import HeckeSkeleton.HighBinSupport.FiniteLocalTable
/-!
# The unramified row from the same finite valuation table

The fifth Gauss factor is eliminated using the actual Gauss product relation
`G₁ G₅ = q`; the sixth-root unit phase is retained throughout. This is the
finite algebraic step used by the regular Euler factor.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

noncomputable section
namespace HighBin.UnramifiedFiniteTable
open HighBin.FiniteLocalTable
open scoped Classical BigOperators

lemma inverse_fifth_eq (ρ : ℂ) (hρ : ρ ^ 6 = 1) : ρ⁻¹ ^ 5 = ρ := by
  have hρ0 : ρ ≠ 0 := by intro h; simp [h] at hρ
  rw [inv_pow]
  apply mul_left_cancel₀ (pow_ne_zero 5 hρ0)
  rw [mul_inv_cancel₀ (pow_ne_zero 5 hρ0)]
  simpa only [← pow_succ] using hρ.symm

/-- The exact residue-class zero base row, before either geometric sum. -/
theorem baseMarked_unramified (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ)
    (hq : q ≠ 0) (hρ : ρ ^ 6 = 1) (hV : 1 - V ≠ 0)
    (hG : G 1 * G 5 = q) :
    (1 - V) * baseMarked q θ G ρ X Y V 0 =
      -eta q θ G * ρ⁻¹ * X * (1 - V) +
        ratio q θ X V * (1 - q⁻¹) - eta q θ G * (q - 1) * X * Y * V +
        ratio q θ X V * ρ * Y * (1 - V) := by
  have h1 : G 1 ≠ 0 := by intro h; rw [h, zero_mul] at hG; exact hq hG.symm
  have h5 : G 5 = q / G 1 := (eq_div_iff h1).2 (by simpa only [mul_comm] using hG)
  norm_num [baseMarked, baseAt, weightedTerm, positiveConvolution, valuationGauss,
    Fin.sum_univ_two, eta, ratio]
  have hi5 : (ρ ^ 5)⁻¹ = ρ := by simpa only [inv_pow] using inverse_fifth_eq ρ hρ
  rw [hi5, h5]
  field_simp [hq, hV, h1]
  ring

/-- The complete regular prime series written in its local coordinates. -/
def regularSeriesValue (q R V W D : ℂ) : ℂ :=
  1 / (1 - V) + W / (1 - W) +
    R / (1 - R) * ((1 - q⁻¹) / (1 - V) + W) -
    D / (1 - R) * (1 + (q - 1) * W * V / (1 - V))

/-- Adding the completed-unit contribution gives the standard regular local
series, with every normalization and sign visible. -/
theorem regular_base_identification (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ)
    (hq : q ≠ 0) (hρ : ρ ^ 6 = 1) (hV : 1 - V ≠ 0)
    (hR : 1 - ratio q θ X V ≠ 0) (hG : G 1 * G 5 = q) :
    1 / (1 - V) + (ρ * Y) / (1 - ρ * Y) +
      baseMarked q θ G ρ X Y V 0 / (1 - ratio q θ X V) =
      regularSeriesValue q (ratio q θ X V) V (ρ * Y) (eta q θ G * ρ⁻¹ * X) := by
  have hρ0 : ρ ≠ 0 := by intro h; simp [h] at hρ
  have hb := baseMarked_unramified q θ G ρ X Y V hq hρ hV hG
  have hbase : baseMarked q θ G ρ X Y V 0 =
      (-eta q θ G * ρ⁻¹ * X * (1 - V) +
        ratio q θ X V * (1 - q⁻¹) - eta q θ G * (q - 1) * X * Y * V +
        ratio q θ X V * ρ * Y * (1 - V)) / (1 - V) :=
    (eq_div_iff hV).2 (by simpa only [mul_comm] using hb)
  suffices hh : baseMarked q θ G ρ X Y V 0 / (1 - ratio q θ X V) =
      ratio q θ X V / (1 - ratio q θ X V) * ((1 - q⁻¹) / (1 - V) + ρ * Y) -
      (eta q θ G * ρ⁻¹ * X) / (1 - ratio q θ X V) *
        (1 + (q - 1) * (ρ * Y) * V / (1 - V)) by
    unfold regularSeriesValue
    rw [hh]
    ring
  rw [hbase]
  field_simp [hV, hR, hρ0]
  ring

#print axioms baseMarked_unramified
#print axioms regular_base_identification
end HighBin.UnramifiedFiniteTable
