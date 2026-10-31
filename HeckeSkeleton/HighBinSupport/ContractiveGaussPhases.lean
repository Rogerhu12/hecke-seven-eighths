import HeckeSkeleton.HighBinSupport.ActualGaussPhases

/-!
The actual prime coefficient can vanish at a ramified target prime.  The
finite Gauss table therefore needs the contractive case, including θ=0,
and must not impose an unramifiedness assumption merely to prove a bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HighBin.ActualGaussPhases

open HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds
open HighBin.FiniteResidueFourier

variable {F : Type*} [Field F] [Fintype F]

/-- Actual finite Gauss phases with a possibly zero theta coefficient.
All coefficient bounds follow from finite-field Gauss orthogonality and
the unitary-character bound ‖θ‖≤1. -/
def contractivePhaseData (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (θ : ℂ) (hθ : ‖θ‖ ≤ 1)
    (u : Fˣ) : PhaseData := by
  let B := phaseData χ hχ ψ hψ 1 (by simp) u
  have hp (n : ℕ) : ‖θ ^ n‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg θ) hθ
  have hm (n : ℕ) (c : ℂ) (hc : ‖c‖ ≤ 1) : ‖θ ^ n * c‖ ≤ 1 := by
    rw [norm_mul]
    exact mul_le_one₀ (hp n) (norm_nonneg _) hc
  refine {
    eta := θ * B.eta
    alpha := θ ^ 3 * B.alpha
    c2 := θ ^ 3 * B.c2
    c31 := θ ^ 3 * B.c31
    c32 := θ ^ 4 * B.c32
    c4 := θ ^ 4 * B.c4
    eta_bound := ?_
    alpha_bound := hm 3 _ B.alpha_bound
    c2_bound := hm 3 _ B.c2_bound
    c31_bound := hm 3 _ B.c31_bound
    c32_bound := hm 4 _ B.c32_bound
    c4_bound := hm 4 _ B.c4_bound }
  simpa only [pow_one] using hm 1 _ B.eta_bound

/-- With norm-one θ, this is literally the earlier table. Thus the new
construction extends it without selecting replacement values at θ=0. -/
theorem contractivePhaseData_eq_phaseData
    (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (θ : ℂ) (hθ : ‖θ‖ = 1)
    (u : Fˣ) :
    contractivePhaseData χ hχ ψ hψ θ hθ.le u = phaseData χ hχ ψ hψ θ hθ u := by
  simp only [contractivePhaseData, phaseData]
  congr 1 <;> ring

/-- The raw mixed Gauss coefficient remains exact when the target prime
coefficient vanishes; contractivity is used only to certify its bound. -/
theorem contractivePhaseData_eta
    (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (θ : ℂ) (hθ : ‖θ‖ ≤ 1)
    (u : Fˣ) :
    (contractivePhaseData χ hχ ψ hψ θ hθ u).eta =
      HighBin.FiniteLocalTable.eta (Fintype.card F) θ (gaussFamily χ ψ) := by
  change θ * (phaseData χ hχ ψ hψ 1 (by simp) u).eta = _
  rw [phaseData_eta]
  unfold HighBin.FiniteLocalTable.eta
  ring

/-- All five exceptional terms have the literal finite-Gauss value for
every contractive target coefficient, including θ=0. -/
theorem raw_special_eq_contractive
    (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (θ : ℂ) (hθ : ‖θ‖ ≤ 1)
    (u : Fˣ) (s w : ℂ) (j : Fin 5) :
    HighBin.FiniteLocalTable.special (Fintype.card F) θ (gaussFamily χ ψ) (χ u)
      ((Fintype.card F : ℂ) ^ (-s)) ((Fintype.card F : ℂ) ^ (-w)) j =
      specialTerm (contractivePhaseData χ hχ ψ hψ θ hθ u) (Fintype.card F) s w j := by
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
    norm_num [HighBin.FiniteLocalTable.special, specialTerm, contractivePhaseData, phaseData,
      phaseMonomial_eq_factored (Fintype.card F) hq,
      normalizedFamily, normalizedGauss, gaussFamily, HighBin.FiniteLocalTable.eta,
      h32, h52]
  all_goals try simp only [← hs2]
  all_goals field_simp [hs] <;> ring

theorem raw_ratio_eq_contractive
    (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (θ : ℂ) (hθ : ‖θ‖ ≤ 1)
    (u : Fˣ) (s z : ℂ) :
    HighBin.FiniteLocalTable.ratio (Fintype.card F) θ
      ((Fintype.card F : ℂ) ^ (-s)) (coordV (Fintype.card F) z) =
      coordR (contractivePhaseData χ hχ ψ hψ θ hθ u) (Fintype.card F) s z := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  rw [coordR_eq_original _ _ hq]
  change θ ^ 6 * (Fintype.card F : ℂ) ^ 4 * ((Fintype.card F : ℂ) ^ (-s)) ^ 6 *
    coordV (Fintype.card F) z = (θ ^ 3 * 1 ^ 3) ^ 2 * (Fintype.card F : ℂ) ^ 4 *
      ((Fintype.card F : ℂ) ^ (-s)) ^ 6 * coordV (Fintype.card F) z
  ring

/-- This exact equality connects the contractive finite Laurent table to
the Fourier-derived table, without any unramified-target restriction. -/
theorem finiteTable_eq_contractiveGaussTable
    (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (θ : ℂ) (hθ : ‖θ‖ ≤ 1)
    (u : Fˣ) (s w z : ℂ) (j : Fin 5)
    (hV : 1 - coordV (Fintype.card F) z ≠ 0)
    (hR : 1 - coordR (contractivePhaseData χ hχ ψ hψ θ hθ u)
      (Fintype.card F) s z ≠ 0) :
    HighBin.FiniteLocalTable.finiteTableCorrection (Fintype.card F) θ (gaussFamily χ ψ)
      (χ u) ((Fintype.card F : ℂ) ^ (-s)) ((Fintype.card F : ℂ) ^ (-w))
      (coordV (Fintype.card F) z) j =
      ramifiedTableValue (contractivePhaseData χ hχ ψ hψ θ hθ u)
        (Fintype.card F) s w z j := by
  have hq : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hρ : χ u ≠ 0 := by
    intro hz
    have hh := unitPhase_norm χ u
    simp [hz] at hh
  have hR' : 1 - HighBin.FiniteLocalTable.ratio (Fintype.card F) θ
      ((Fintype.card F : ℂ) ^ (-s)) (coordV (Fintype.card F) z) ≠ 0 := by
    rw [raw_ratio_eq_contractive χ hχ ψ hψ θ hθ u s z]
    exact hR
  rw [HighBin.FiniteLocalTable.finiteTableCorrection_eq _ _ _ _ _ _ _ hq hρ hV hR' j,
    raw_ratio_eq_contractive χ hχ ψ hψ θ hθ u s z,
    raw_special_eq_contractive χ hχ ψ hψ θ hθ u s w j,
    ← contractivePhaseData_eta χ hχ ψ hψ θ hθ u]
  rfl

#print axioms contractivePhaseData
#print axioms contractivePhaseData_eq_phaseData
#print axioms contractivePhaseData_eta
#print axioms raw_special_eq_contractive
#print axioms finiteTable_eq_contractiveGaussTable

end HighBin.ActualGaussPhases
