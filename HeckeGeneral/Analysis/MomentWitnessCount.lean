import HeckeGeneral.Analysis.MomentInputs

/-!
Threshold counting for the actual inverse and paired moment polynomials.
The original whole-scale and polynomial-height quantifiers are preserved.
This proves the moment-to-count consumer. It does not construct detector
witnesses, prove their coverage, or optimize the short/long witness crossing.
-/

noncomputable section
namespace HeckeGeneral.Analysis.ConditionalMoments

open NumberField IsDedekindDomain HeckeGeneral.Characters
open scoped Classical BigOperators

/-- The threshold exponent refers to squared norm, so it applies both to
the inverse second moment and the squared product in the paired moment. -/
def energyWitnessRows {ι : Type*} (F : Finset ι) (z : ι → ℂ) (Z v : ℝ) : Finset ι :=
  F.filter fun u => Z ^ v ≤ ‖z u‖ ^ 2

theorem energyWitnessRows_card_mul_le {ι : Type*}
    (F : Finset ι) (z : ι → ℂ) (Z v : ℝ) :
    ((energyWitnessRows F z Z v).card : ℝ) * Z ^ v ≤ ∑ u ∈ F, ‖z u‖ ^ 2 := by
  calc
    _ = ∑ u ∈ energyWitnessRows F z Z v, Z ^ v := by simp
    _ ≤ ∑ u ∈ energyWitnessRows F z Z v, ‖z u‖ ^ 2 :=
      Finset.sum_le_sum (fun u hu => (Finset.mem_filter.mp hu).2)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)

/-- No new threshold, height ceiling or height degree is selected here.
The exact constants of the supplied moment estimate work for every v. -/
theorem polynomialHeightBound_energyWitnessRows {ι : Type*}
    (F : ℝ → ℝ → Finset ι) (z : ℝ → ℝ → ι → ℂ) {p ε : ℝ}
    (h : PolynomialHeightBound (fun Z t => ∑ u ∈ F Z t, ‖z Z t u‖ ^ 2) p ε)
    (v : ℝ) :
    PolynomialHeightBound
      (fun Z t => ((energyWitnessRows (F Z t) (z Z t) Z v).card : ℝ)) (p - v) ε := by
  obtain ⟨C, Z₀, A, ceiling, hC, hZ₀, hA, hceiling, hbound⟩ := h
  refine ⟨C, Z₀, A, ceiling, hC, hZ₀, hA, hceiling, ?_⟩
  intro Z t hZ ht
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one (hZ₀.trans hZ)
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hZpos v)).mp
  calc
    _ ≤ ∑ u ∈ F Z t, ‖z Z t u‖ ^ 2 := energyWitnessRows_card_mul_le ..
    _ ≤ C * Z ^ (p + ε) * (1 + |t|) ^ A := hbound Z t hZ ht
    _ = _ := by
      have he : p + ε = (p - v + ε) + v := by ring
      rw [he, Real.rpow_add hZpos]
      ring

variable (K : Type) [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

def inverseWitnessRows (d : MomentData K ω ψ) (a : RealParameters)
    (Z t v : ℝ) : Finset (NonzeroIdeal K) :=
  energyWitnessRows (d.rows (Z ^ a.m))
    (fun u => inversePolynomial d u (Z ^ a.r) t * slotProduct d u Z t) Z v

/-- The existing exceptional-row exclusion is retained verbatim. -/
def pairedWitnessRows (d : MomentData K ω ψ) (a : RealParameters)
    (Z t v : ℝ) : Finset (NonzeroIdeal K) :=
  energyWitnessRows (pairedRows d a Z)
    (fun u => plainPolynomial d d.plainTest₁ u (Z ^ a.n₁) t *
      plainPolynomial d d.plainTest₂ u (Z ^ a.n₂) t * slotProduct d u Z t) Z v

theorem inverseWitnessRows_polynomialHeightBound
    (d : ℝ → MomentData K ω ψ) (a : RealParameters) {ε : ℝ}
    (h : PolynomialHeightBound (fun Z t => inverseEnergy (d Z) a Z t) a.m ε)
    (v : ℝ) :
    PolynomialHeightBound
      (fun Z t => ((inverseWitnessRows K (d Z) a Z t v).card : ℝ)) (a.m - v) ε :=
  polynomialHeightBound_energyWitnessRows
    (fun Z _ => (d Z).rows (Z ^ a.m))
    (fun Z t u => inversePolynomial (d Z) u (Z ^ a.r) t * slotProduct (d Z) u Z t) h v

theorem pairedWitnessRows_polynomialHeightBound
    (d : ℝ → MomentData K ω ψ) (a : RealParameters) {ε : ℝ}
    (h : PolynomialHeightBound (fun Z t => pairedEnergy (d Z) a Z t) (a.m + a.q) ε)
    (v : ℝ) :
    PolynomialHeightBound
      (fun Z t => ((pairedWitnessRows K (d Z) a Z t v).card : ℝ)) (a.m + a.q - v) ε :=
  polynomialHeightBound_energyWitnessRows
    (fun Z _ => pairedRows (d Z) a Z)
    (fun Z t u => plainPolynomial (d Z) (d Z).plainTest₁ u (Z ^ a.n₁) t *
      plainPolynomial (d Z) (d Z).plainTest₂ u (Z ^ a.n₂) t *
      slotProduct (d Z) u Z t) h v

end HeckeGeneral.Analysis.ConditionalMoments
