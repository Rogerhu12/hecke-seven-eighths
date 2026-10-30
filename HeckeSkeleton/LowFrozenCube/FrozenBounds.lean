import HeckeSkeleton.LowFrozenCube.FrozenReduction

/-!
# Bounded coefficients and the normalized frozen energy exit

The local-table input is only its original pointwise majorant `C/N(x)`.
All row phases and fixed-support mark/column phases are proved to have norm
one. The original `1/N(n')` denominator combines with `1/N(x)` through the
canonical product `b=x*n'`. A lower annulus bound `B <= N(b)` produces an
explicit unit-bounded coefficient and the exact outer scalar `C/B`.
-/

namespace HeckeSkeleton.LowFrozenCube.FrozenReduction

open scoped BigOperators Classical

noncomputable section

variable {ι A : Type*} [CommMonoid A]

namespace Data

variable (D : Data ι A)

@[simp] theorem valuation_prime (p : ι) :
    PrimeCoordinates.valuation D.coords (D.prime p) = Finsupp.single p 1 := by
  simp [prime, PrimeCoordinates.valuation]

theorem symbol_norm_of_coprime (a b : A)
    (hab : PrimeCoordinates.Coprime D.coords a b) : ‖D.symbol a b‖ = 1 := by
  apply Complex.norm_eq_one_of_pow_eq_one (n := 6)
  · simpa [hab] using D.sixth a b
  · decide

theorem ordinarySymbol_norm (a : A)
    (ha : PrimeCoordinates.Avoids D.coords D.ordinary a)
    (p : ι) (hp : p ∈ D.ordinary) : ‖D.ordinarySymbol p a‖ = 1 := by
  apply D.symbol_norm_of_coprime
  intro q
  by_cases hqp : q = p
  · subst q
    exact Or.inl (ha p hp)
  · right
    rw [D.valuation_prime]
    simp [Finsupp.single_apply, hqp, Ne.symm hqp]

theorem negativeInteraction_norm (v : ι → ℕ) (a : A)
    (ha : PrimeCoordinates.Avoids D.coords D.ordinary a) :
    ‖negativeOrdinaryInteraction D.ordinary D.ordinarySymbol D.digit v a‖ = 1 := by
  unfold negativeOrdinaryInteraction
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro p hp
  rw [norm_zpow, D.ordinarySymbol_norm a ha p hp]
  simp

theorem positiveInteraction_norm (v : ι → ℕ) (a : A)
    (ha : PrimeCoordinates.Avoids D.coords D.ordinary a) :
    ‖positiveOrdinaryInteraction D.ordinary D.ordinarySymbol D.digit v a‖ = 1 := by
  unfold positiveOrdinaryInteraction
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro p hp
  rw [norm_pow, D.ordinarySymbol_norm a ha p hp]
  simp

theorem mark_norm (a₀ : A → ℂ) (P : A)
    (hP : PrimeCoordinates.Avoids D.coords D.support P) :
    ‖D.mark a₀ P‖ = ‖a₀ P‖ := by
  have hcop := PrimeCoordinates.coprime_of_avoids_supported D.coords
    D.support P D.minimum hP D.minimum_supported
  unfold mark markCoefficient
  rw [norm_mul, norm_mul, norm_pow, D.symbol_norm_of_coprime P D.minimum hcop,
    D.negativeInteraction_norm _ P (D.avoids_ordinary_of_avoids_support P hP)]
  simp

theorem rowFactor_norm (ρ₀ : A → ℂ) (d : A)
    (hd : PrimeCoordinates.Avoids D.coords D.support d) :
    ‖D.rowFactor ρ₀ d‖ = ‖ρ₀ d‖ := by
  have hcop := PrimeCoordinates.coprime_of_avoids_supported D.coords
    D.support d D.minimum hd D.minimum_supported
  unfold rowFactor rowCoefficient
  rw [norm_mul, norm_mul, D.symbol_norm_of_coprime d D.minimum hcop,
    D.negativeInteraction_norm _ d (D.avoids_ordinary_of_avoids_support d hd)]
  simp

theorem column_norm (lam : A → ℂ) (c : A)
    (hc : PrimeCoordinates.Avoids D.coords D.ordinary c) :
    ‖D.column lam c‖ = ‖lam c‖ := by
  have hcop := PrimeCoordinates.coprime_of_avoids_supported D.coords
    D.ordinary c D.minimum hc D.minimum_ordinary
  unfold column columnCoefficient
  rw [norm_mul, norm_mul, norm_pow, D.symbol_norm_of_coprime c D.minimum hcop,
    D.positiveInteraction_norm _ c hc]
  simp

/-- The exact energy equality already follows from the primitive row phase's
norm one; the norm of the complete frozen row factor is derived here. -/
theorem source_energy_eq_hybridEnergy
    (normI : A → ℝ) (a₀ ρ₀ lam : A → ℂ) (Ω : A → A → A → ℂ)
    (rows marks columns : Finset A) (pairs : Finset (A × A))
    (hrows : ∀ d ∈ rows, PrimeCoordinates.Avoids D.coords D.support d)
    (hρ₀ : ∀ d ∈ rows, ‖ρ₀ d‖ = 1)
    (hmarks : ∀ P ∈ marks, PrimeCoordinates.Avoids D.coords D.support P)
    (hcolumns : ∀ c ∈ columns, PrimeCoordinates.Avoids D.coords D.ordinary c)
    (hpairs : ∀ q ∈ pairs, D.CanonicalCube q.1 ∧
      PrimeCoordinates.Avoids D.coords D.ordinary q.2) :
    (∑ d ∈ rows, ‖D.sourceRow normI a₀ ρ₀ lam Ω marks columns pairs d‖ ^ 2) =
      HeckeSkeleton.LowHybrid.hybridEnergy (fun a b => D.symbol a b)
        (PrimeCoordinates.Coprime D.coords) normI (D.mark a₀) (D.beta normI lam Ω)
        rows marks columns (pairs.image cubeProduct) := by
  unfold HeckeSkeleton.LowHybrid.hybridEnergy
  apply Finset.sum_congr rfl
  intro d hd
  rw [D.sourceRow_eq_hybridRow normI a₀ ρ₀ lam Ω marks columns pairs
    hmarks hcolumns hpairs d, norm_mul, D.rowFactor_norm ρ₀ d (hrows d hd),
    hρ₀ d hd, one_mul]

theorem residualCoefficient_norm_le
    (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a)
    (lam : A → ℂ) (Ω : A → A → A → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (c x n : A) (hc : PrimeCoordinates.Avoids D.coords D.ordinary c)
    (hlam : ‖lam c‖ ≤ 1) (hΩ : ‖Ω c x n‖ ≤ C / normI x) :
    ‖D.residualCoefficient normI lam Ω c x n‖ ≤ C / normI (x * n) := by
  unfold residualCoefficient
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (hpos n), D.column_norm lam c hc, map_mul]
  calc
    _ ≤ 1 * ((C / normI x) / normI n) :=
      mul_le_mul hlam
        (div_le_div_of_nonneg_right hΩ (hpos n).le)
        (div_nonneg (norm_nonneg _) (hpos n).le) zero_le_one
    _ = _ := by rw [one_mul, div_div]

/-- The old local decay and complementary-cube denominator combine into
the complete cube denominator on the inherited image support. -/
theorem beta_norm_le
    (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a)
    (lam : A → ℂ) (Ω : A → A → A → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (columns : Finset A) (pairs : Finset (A × A))
    (hcolumns : ∀ c ∈ columns, PrimeCoordinates.Avoids D.coords D.ordinary c)
    (hpairs : ∀ q ∈ pairs, D.CanonicalCube q.1 ∧
      PrimeCoordinates.Avoids D.coords D.ordinary q.2)
    (hlam : ∀ c ∈ columns, ‖lam c‖ ≤ 1)
    (hΩ : ∀ c ∈ columns, ∀ q ∈ pairs, ‖Ω c q.1 q.2‖ ≤ C / normI q.1)
    (c : A) (hc : c ∈ columns) (b : A) (hb : b ∈ pairs.image cubeProduct) :
    ‖D.beta normI lam Ω c b‖ ≤ C / normI b := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
  have hsplit := D.canonical_split q.1 q.2 (hpairs q hq).1 (hpairs q hq).2
  simpa only [beta, fullCubeCoefficient, cubeProduct, hsplit] using
    D.residualCoefficient_norm_le normI hpos lam Ω C hC c q.1 q.2
      (hcolumns c hc) (hlam c hc) (hΩ c hc q hq)

def unitBeta (normI : A → ℝ) (lam : A → ℂ) (Ω : A → A → A → ℂ)
    (B C : ℝ) (c b : A) : ℂ :=
  normalizedCubeCoefficient B C (D.beta normI lam Ω c b)

theorem beta_bound_of_lower_annulus
    (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a)
    (lam : A → ℂ) (Ω : A → A → A → ℂ) (B C : ℝ) (hB : 0 < B) (hC : 0 ≤ C)
    (columns : Finset A) (pairs : Finset (A × A))
    (hcolumns : ∀ c ∈ columns, PrimeCoordinates.Avoids D.coords D.ordinary c)
    (hpairs : ∀ q ∈ pairs, D.CanonicalCube q.1 ∧
      PrimeCoordinates.Avoids D.coords D.ordinary q.2)
    (hlam : ∀ c ∈ columns, ‖lam c‖ ≤ 1)
    (hΩ : ∀ c ∈ columns, ∀ q ∈ pairs, ‖Ω c q.1 q.2‖ ≤ C / normI q.1)
    (hlower : ∀ q ∈ pairs, B ≤ normI (cubeProduct q))
    (c : A) (hc : c ∈ columns) (b : A) (hb : b ∈ pairs.image cubeProduct) :
    ‖D.beta normI lam Ω c b‖ ≤ C / B := by
  apply (D.beta_norm_le normI hpos lam Ω C hC columns pairs
    hcolumns hpairs hlam hΩ c hc b hb).trans
  apply div_le_div_of_nonneg_left hC hB
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
  exact hlower q hq

theorem unitBeta_norm_le (normI : A → ℝ) (lam : A → ℂ)
    (Ω : A → A → A → ℂ) (B C : ℝ) (hB : 0 < B) (hC : 0 ≤ C)
    (c b : A) (hβ : ‖D.beta normI lam Ω c b‖ ≤ C / B) :
    ‖D.unitBeta normI lam Ω B C c b‖ ≤ 1 :=
  normalizedCubeCoefficient_norm_le B C _ hB hC hβ

/-- Exact normalization also covers the zero-majorant case. -/
theorem beta_eq_scalar_unitBeta (normI : A → ℝ) (lam : A → ℂ)
    (Ω : A → A → A → ℂ) (B C : ℝ) (hB : 0 < B) (hC : 0 ≤ C)
    (c b : A) (hβ : ‖D.beta normI lam Ω c b‖ ≤ C / B) :
    D.beta normI lam Ω c b = ((C : ℂ) / (B : ℂ)) * D.unitBeta normI lam Ω B C c b := by
  have h := normalizedCubeCoefficient_reassemble B 1 C
    (D.beta normI lam Ω c b) hB (by norm_num) hC hβ
  simpa only [Complex.ofReal_one, div_one, mul_one, inv_one, one_mul, unitBeta, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm] using h

theorem hybridRow_scale_beta (normI : A → ℝ) (β γ : A → A → ℂ)
    (aP : A → ℂ) (marks columns cubes : Finset A) (scalar : ℂ)
    (hβ : ∀ c ∈ columns, ∀ b ∈ cubes, β c b = scalar * γ c b) (d : A) :
    HeckeSkeleton.LowHybrid.hybridRow (fun a b => D.symbol a b)
      (PrimeCoordinates.Coprime D.coords) normI aP β marks columns cubes d =
    scalar * HeckeSkeleton.LowHybrid.hybridRow (fun a b => D.symbol a b)
      (PrimeCoordinates.Coprime D.coords) normI aP γ marks columns cubes d := by
  unfold HeckeSkeleton.LowHybrid.hybridRow
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro b hb
  rw [hβ c hc b hb]
  ring

/-- Complete normalized energy exit: the source is the unfrozen three-factor
reflected row, and both final coefficient bounds are derived. The only local
analytic input is the original pointwise coefficient majorant. -/
theorem normalized_frozen_exit
    (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a)
    (a₀ ρ₀ lam : A → ℂ) (Ω : A → A → A → ℂ)
    (B C : ℝ) (hB : 0 < B) (hC : 0 ≤ C)
    (rows marks columns : Finset A) (pairs : Finset (A × A))
    (hrows : ∀ d ∈ rows, PrimeCoordinates.Avoids D.coords D.support d)
    (hρ₀ : ∀ d ∈ rows, ‖ρ₀ d‖ = 1)
    (hmarks : ∀ P ∈ marks, PrimeCoordinates.Avoids D.coords D.support P)
    (ha₀ : ∀ P ∈ marks, ‖a₀ P‖ ≤ 1)
    (hcolumns : ∀ c ∈ columns, PrimeCoordinates.Avoids D.coords D.ordinary c)
    (hlam : ∀ c ∈ columns, ‖lam c‖ ≤ 1)
    (hpairs : ∀ q ∈ pairs, D.CanonicalCube q.1 ∧
      PrimeCoordinates.Avoids D.coords D.ordinary q.2)
    (hΩ : ∀ c ∈ columns, ∀ q ∈ pairs, ‖Ω c q.1 q.2‖ ≤ C / normI q.1)
    (hlower : ∀ q ∈ pairs, B ≤ normI (cubeProduct q)) :
    (∀ P ∈ marks, ‖D.mark a₀ P‖ ≤ 1) ∧
    (∀ c ∈ columns, ∀ b ∈ pairs.image cubeProduct,
      ‖D.unitBeta normI lam Ω B C c b‖ ≤ 1) ∧
    (∑ d ∈ rows, ‖D.sourceRow normI a₀ ρ₀ lam Ω marks columns pairs d‖ ^ 2) =
      (C / B) ^ 2 * HeckeSkeleton.LowHybrid.hybridEnergy
        (fun a b => D.symbol a b) (PrimeCoordinates.Coprime D.coords) normI
        (D.mark a₀) (D.unitBeta normI lam Ω B C)
        rows marks columns (pairs.image cubeProduct) := by
  have hβbound : ∀ c ∈ columns, ∀ b ∈ pairs.image cubeProduct,
      ‖D.beta normI lam Ω c b‖ ≤ C / B := by
    intro c hc b hb
    exact D.beta_bound_of_lower_annulus normI hpos lam Ω B C hB hC
      columns pairs hcolumns hpairs hlam hΩ hlower c hc b hb
  have hβ : ∀ c ∈ columns, ∀ b ∈ pairs.image cubeProduct,
      D.beta normI lam Ω c b =
        ((C : ℂ) / (B : ℂ)) * D.unitBeta normI lam Ω B C c b := by
    intro c hc b hb
    exact D.beta_eq_scalar_unitBeta normI lam Ω B C hB hC c b (hβbound c hc b hb)
  refine ⟨?_, ?_, ?_⟩
  · intro P hP
    rw [D.mark_norm a₀ P (hmarks P hP)]
    exact ha₀ P hP
  · intro c hc b hb
    exact D.unitBeta_norm_le normI lam Ω B C hB hC c b (hβbound c hc b hb)
  · have hscalar : ‖(C : ℂ) / (B : ℂ)‖ = C / B := by
      simp [norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hC, abs_of_pos hB]
    unfold HeckeSkeleton.LowHybrid.hybridEnergy
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [D.sourceRow_eq_hybridRow normI a₀ ρ₀ lam Ω marks columns pairs
      hmarks hcolumns hpairs d,
      D.hybridRow_scale_beta normI (D.beta normI lam Ω)
        (D.unitBeta normI lam Ω B C) (D.mark a₀)
        marks columns (pairs.image cubeProduct) ((C : ℂ) / (B : ℂ)) hβ d,
      norm_mul, D.rowFactor_norm ρ₀ d (hrows d hd), hρ₀ d hd, one_mul,
      norm_mul, hscalar, mul_pow]

/-- The complete cube substitution also gives the exact kernel numerator. -/
theorem kernel_numerator_frozen (normI : A →* ℝ) (X : ℝ) (c x n : A) :
    X * normI (D.minimum * x ^ 3) * normI c * normI n ^ 3 =
      X * normI D.minimum * normI c * normI (x * n) ^ 3 := by
  simp only [map_mul, map_pow]
  ring

end Data

end

end HeckeSkeleton.LowFrozenCube.FrozenReduction
