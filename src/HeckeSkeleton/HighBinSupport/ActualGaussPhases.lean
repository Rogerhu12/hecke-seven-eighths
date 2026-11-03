import HeckeSkeleton.HighBinSupport.FiniteResidueFourier
import HeckeSkeleton.HighBinSupport.FiniteLocalTable
import HeckeSkeleton.HighBinSupport.HighEulerScalarBounds
import Lean.Elab.Tactic.Omega
/-!
# Five exceptional phases from actual sextic residue-field Gauss sums

This module constructs the previous scalar table's `PhaseData` from an
actual multiplicative character of exact order six and an actual primitive
additive character. Its six norm bounds are conclusions of finite Gauss
sum orthogonality. The root used in `neg_one_eq_one` is the reduction of the
chosen twelfth root of unity in the number-field application.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

noncomputable section
namespace HighBin.ActualGaussPhases
open HighBin.FiniteResidueFourier
open HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds
open scoped Classical BigOperators ComplexConjugate

variable {F : Type*} [Field F] [Fintype F]

def gaussFamily (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (r : ℕ) : ℂ :=
  gaussSum (χ ^ r) ψ

def normalizedFamily (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (r : ℕ) : ℂ :=
  normalizedGauss (χ ^ r) ψ

lemma pow_nonprincipal (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (r : ℕ) (hr : 0 < r) (hr6 : r < 6) : χ ^ r ≠ 1 :=
  pow_ne_one_of_lt_orderOf (by omega) (by simpa only [hχ] using hr6)

lemma character_nonprincipal (χ : MulChar F ℂ) (hχ : orderOf χ = 6) : χ ≠ 1 := by
  simpa only [pow_one] using pow_nonprincipal χ hχ 1 (by norm_num) (by norm_num)

lemma normalizedFamily_norm (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (r : ℕ) (hr : 0 < r) (hr6 : r < 6) :
    ‖normalizedFamily χ ψ r‖ = 1 :=
  normalizedGauss_norm (χ ^ r) (pow_nonprincipal χ hχ r hr hr6) ψ hψ

lemma unitPhase_norm (χ : MulChar F ℂ) (u : Fˣ) : ‖χ u‖ = 1 :=
  Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)

lemma unitPhase_six (χ : MulChar F ℂ) (hχ : orderOf χ = 6) (u : Fˣ) :
    χ u ^ 6 = 1 := by
  rw [← MulChar.pow_apply_coe, ← hχ, pow_orderOf_eq_one, MulChar.one_apply_coe]

/-- The μ₁₂ assumption is used precisely here to fix the sign at -1. -/
theorem neg_one_eq_one (χ : MulChar F ℂ) (hχ : χ ^ 6 = 1)
    (ξ : F) (hξ : ξ ^ 6 = -1) : χ (-1) = 1 := by
  have hξ0 : ξ ≠ 0 := by intro h; simp [h] at hξ
  calc
    χ (-1) = χ (ξ ^ 6) := congrArg χ hξ.symm
    _ = χ ξ ^ 6 := map_pow χ ξ 6
    _ = (χ ^ 6) ξ := (χ.pow_apply' (by norm_num) ξ).symm
    _ = 1 := by rw [hχ, MulChar.one_apply (isUnit_iff_ne_zero.mpr hξ0)]

/-- This exact product, not a norm estimate, calibrates the unramified row. -/
theorem gaussFamily_one_mul_five (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (hminus : χ (-1) = 1) :
    gaussFamily χ ψ 1 * gaussFamily χ ψ 5 = (Fintype.card F : ℂ) := by
  simpa only [gaussFamily, hχ, show 6 - 1 = 5 from rfl, pow_one, hminus, one_mul]
    using gaussSum_mul_gaussSum_pow_orderOf_sub_one (character_nonprincipal χ hχ) hψ

/-- All phases in the five rows are now computed from finite sums. -/
def phaseData (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (θ : ℂ) (hθ : ‖θ‖ = 1) (u : Fˣ) : PhaseData := by
  let γ := normalizedFamily χ ψ
  let ρ : ℂ := χ u
  have hγ1 : ‖γ 1‖ = 1 := normalizedFamily_norm χ hχ ψ hψ 1 (by norm_num) (by norm_num)
  have hγ2 : ‖γ 2‖ = 1 := normalizedFamily_norm χ hχ ψ hψ 2 (by norm_num) (by norm_num)
  have hγ3 : ‖γ 3‖ = 1 := normalizedFamily_norm χ hχ ψ hψ 3 (by norm_num) (by norm_num)
  have hγ4 : ‖γ 4‖ = 1 := normalizedFamily_norm χ hχ ψ hψ 4 (by norm_num) (by norm_num)
  have hρ : ‖ρ‖ = 1 := unitPhase_norm χ u
  refine {
    eta := -(θ * γ 1 * γ 2)
    alpha := θ ^ 3
    c2 := θ ^ 3 * γ 3 * ρ⁻¹ ^ 3
    c31 := θ ^ 3 * γ 1 * γ 2 * ρ⁻¹ ^ 2
    c32 := -(θ ^ 4 * γ 2 * γ 4 * ρ⁻¹ ^ 4)
    c4 := -(θ ^ 4 * γ 1 * γ 2 * γ 3 * ρ⁻¹ ^ 3)
    eta_bound := ?_
    alpha_bound := ?_
    c2_bound := ?_
    c31_bound := ?_
    c32_bound := ?_
    c4_bound := ?_
  } <;> simp [norm_mul, norm_pow, norm_inv, hθ, hγ1, hγ2, hγ3, hγ4, hρ]

/-- The principal coefficient is exactly the raw mixed-Gauss expression
used by the valuation table. The separate global mixed-Gauss calibration
then identifies it with the prescribed Hecke character at p. -/
theorem phaseData_eta (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (θ : ℂ) (hθ : ‖θ‖ = 1) (u : Fˣ) :
    (phaseData χ hχ ψ hψ θ hθ u).eta =
      HighBin.FiniteLocalTable.eta (Fintype.card F) θ (gaussFamily χ ψ) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hs : (Real.sqrt (Fintype.card F) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hq).ne'
  have hs2 : (Real.sqrt (Fintype.card F) : ℂ) ^ 2 = (Fintype.card F : ℂ) := by
    exact_mod_cast Real.sq_sqrt hq.le
  change -(θ * (gaussSum (χ ^ 1) ψ / (Real.sqrt (Fintype.card F) : ℂ)) *
      (gaussSum (χ ^ 2) ψ / (Real.sqrt (Fintype.card F) : ℂ))) =
    -(θ * gaussSum (χ ^ 1) ψ * gaussSum (χ ^ 2) ψ / (Fintype.card F : ℂ))
  rw [← hs2]
  field_simp [hs]

lemma cpow_three_halves (q : ℝ) (hq : 0 < q) :
    (q : ℂ) ^ ((3 / 2 : ℝ) : ℂ) = (q : ℂ) * (Real.sqrt q : ℂ) := by
  rw [← Complex.ofReal_cpow hq.le]
  have hr : q ^ (3 / 2 : ℝ) = q * Real.sqrt q := by
    calc
      _ = q ^ (1 : ℝ) * q ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hq]
        congr 1
        norm_num
      _ = _ := by rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hr, Complex.ofReal_mul]

lemma cpow_five_halves (q : ℝ) (hq : 0 < q) :
    (q : ℂ) ^ ((5 / 2 : ℝ) : ℂ) = (q : ℂ) ^ 2 * (Real.sqrt q : ℂ) := by
  rw [← Complex.ofReal_cpow hq.le]
  have hr : q ^ (5 / 2 : ℝ) = q ^ 2 * Real.sqrt q := by
    calc
      _ = q ^ (2 : ℝ) * q ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hq]
        congr 1
        norm_num
      _ = _ := by rw [Real.rpow_two, ← Real.sqrt_eq_rpow]
  rw [hr, Complex.ofReal_mul, Complex.ofReal_pow]

/-- Every raw exceptional coefficient is identified with the previous
phase-normalized table, including its fractional q-powers and both signs. -/
theorem raw_special_eq_normalized (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (θ : ℂ) (hθ : ‖θ‖ = 1) (u : Fˣ)
    (s w : ℂ) (j : Fin 5) :
    HighBin.FiniteLocalTable.special (Fintype.card F) θ (gaussFamily χ ψ) (χ u)
      ((Fintype.card F : ℂ) ^ (-s)) ((Fintype.card F : ℂ) ^ (-w)) j =
      specialTerm (phaseData χ hχ ψ hψ θ hθ u) (Fintype.card F) s w j := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hs : (Real.sqrt (Fintype.card F) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hq).ne'
  have hs2 : (Real.sqrt (Fintype.card F) : ℂ) ^ 2 = (Fintype.card F : ℂ) := by
    exact_mod_cast Real.sq_sqrt hq.le
  have h32 : (Fintype.card F : ℂ) ^ (3 / 2 : ℂ) =
      (Fintype.card F : ℂ) * (Real.sqrt (Fintype.card F) : ℂ) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat] using
      cpow_three_halves (Fintype.card F) hq
  have h52 : (Fintype.card F : ℂ) ^ (5 / 2 : ℂ) =
      (Fintype.card F : ℂ) ^ 2 * (Real.sqrt (Fintype.card F) : ℂ) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat] using
      cpow_five_halves (Fintype.card F) hq
  fin_cases j <;>
    norm_num [HighBin.FiniteLocalTable.special, specialTerm, phaseData,
      phaseMonomial_eq_factored (Fintype.card F) hq,
      normalizedFamily, normalizedGauss, gaussFamily, HighBin.FiniteLocalTable.eta,
      h32, h52]
  all_goals try simp only [← hs2]
  all_goals field_simp [hs] <;> ring

/-- The common geometric ratio also has the exact project normalization. -/
theorem raw_ratio_eq_normalized (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (θ : ℂ) (hθ : ‖θ‖ = 1) (u : Fˣ)
    (s z : ℂ) :
    HighBin.FiniteLocalTable.ratio (Fintype.card F) θ
      ((Fintype.card F : ℂ) ^ (-s)) (coordV (Fintype.card F) z) =
      coordR (phaseData χ hχ ψ hψ θ hθ u) (Fintype.card F) s z := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  rw [coordR_eq_original _ _ hq]
  change θ ^ 6 * (Fintype.card F : ℂ) ^ 4 * ((Fintype.card F : ℂ) ^ (-s)) ^ 6 *
    coordV (Fintype.card F) z = (θ ^ 3) ^ 2 * (Fintype.card F : ℂ) ^ 4 *
      ((Fintype.card F : ℂ) ^ (-s)) ^ 6 * coordV (Fintype.card F) z
  ring

/-- Exact arithmetic phase identification of the finite five-row table.
The remaining number-field bridge is the prime-power quotient instantiation,
not a free choice of bounded coefficients. -/
theorem finiteTable_eq_actualGaussTable (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (θ : ℂ) (hθ : ‖θ‖ = 1) (u : Fˣ)
    (s w z : ℂ) (j : Fin 5)
    (hV : 1 - coordV (Fintype.card F) z ≠ 0)
    (hR : 1 - coordR (phaseData χ hχ ψ hψ θ hθ u) (Fintype.card F) s z ≠ 0) :
    HighBin.FiniteLocalTable.finiteTableCorrection (Fintype.card F) θ (gaussFamily χ ψ)
      (χ u) ((Fintype.card F : ℂ) ^ (-s)) ((Fintype.card F : ℂ) ^ (-w))
      (coordV (Fintype.card F) z) j =
      ramifiedTableValue (phaseData χ hχ ψ hψ θ hθ u) (Fintype.card F) s w z j := by
  have hq : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hρ : χ u ≠ 0 := by
    intro hz
    have hh := unitPhase_norm χ u
    simp [hz] at hh
  have hR' : 1 - HighBin.FiniteLocalTable.ratio (Fintype.card F) θ
      ((Fintype.card F : ℂ) ^ (-s)) (coordV (Fintype.card F) z) ≠ 0 := by
    rw [raw_ratio_eq_normalized χ hχ ψ hψ θ hθ u s z]
    exact hR
  rw [HighBin.FiniteLocalTable.finiteTableCorrection_eq _ _ _ _ _ _ _ hq hρ hV hR' j,
    raw_ratio_eq_normalized χ hχ ψ hψ θ hθ u s z,
    raw_special_eq_normalized χ hχ ψ hψ θ hθ u s w j,
    ← phaseData_eta χ hχ ψ hψ θ hθ u]
  rfl

/-- The exceptional bound now applies to phases computed from actual
finite-field sums, rather than to freely supplied bounded phases. -/
theorem actualGaussTable_dynamic_bound (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (θ : ℂ) (hθ : ‖θ‖ = 1) (u : Fˣ)
    (a e : ℝ) (ha : 1 / 2 ≤ a) (he : 0 ≤ e) (s w z : ℂ)
    (hs : s.re = a + 16 * e) (hw : w.re = 1 - a - 6 * e) (hz : z.re = 17 / 50)
    (j : Fin 5) :
    ‖HighBin.FiniteLocalTable.finiteTableCorrection (Fintype.card F) θ (gaussFamily χ ψ)
      (χ u) ((Fintype.card F : ℂ) ^ (-s)) ((Fintype.card F : ℂ) ^ (-w))
      (coordV (Fintype.card F) z) j - 1‖ ≤ 9 * (Fintype.card F : ℝ) ^ (-10 * e) := by
  have hq : (2 : ℝ) ≤ Fintype.card F := by
    have hh : 2 ≤ Fintype.card F := Fintype.one_lt_card
    exact_mod_cast hh
  have hV : 1 - coordV (Fintype.card F) z ≠ 0 := by
    apply one_sub_R_ne_zero
    exact (coordV_norm_le_quarter (Fintype.card F) hq z hz).trans (by norm_num)
  have hR := one_sub_R_ne_zero _
    (coordR_norm_le_half (phaseData χ hχ ψ hψ θ hθ u) (Fintype.card F) a e hq ha he s z hs hz)
  rw [finiteTable_eq_actualGaussTable χ hχ ψ hψ θ hθ u s w z j hV hR]
  exact ramified_table_dynamic_bound (phaseData χ hχ ψ hψ θ hθ u)
    (Fintype.card F) a e hq ha he s w z hs hw hz j

#print axioms normalizedFamily_norm
#print axioms neg_one_eq_one
#print axioms gaussFamily_one_mul_five
#print axioms phaseData
#print axioms phaseData_eta
#print axioms raw_special_eq_normalized
#print axioms finiteTable_eq_actualGaussTable
#print axioms actualGaussTable_dynamic_bound
end HighBin.ActualGaussPhases
