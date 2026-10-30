import HeckeGeneral.Analysis.MomentInputs

/-!
Finite unions of witness families preserve the pretarget power and loss.
All changes to constants, height degree, scale threshold and allowed height
ceiling take place after the entire finite family has been specified.
-/

noncomputable section
namespace HeckeGeneral.Analysis.ConditionalMoments

open scoped Classical BigOperators

theorem polynomialHeightBound_mono {E F : ℝ → ℝ → ℝ} {p ε : ℝ}
    (hF : PolynomialHeightBound F p ε)
    (hEF : ∀ Z t, 1 ≤ Z → E Z t ≤ F Z t) :
    PolynomialHeightBound E p ε := by
  obtain ⟨C, Z₀, A, h, hC, hZ₀, hA, hh, hb⟩ := hF
  exact ⟨C, Z₀, A, h, hC, hZ₀, hA, hh,
    fun Z t hZ ht => (hEF Z t (hZ₀.trans hZ)).trans (hb Z t hZ ht)⟩

theorem polynomialHeightBound_zero (p ε : ℝ) :
    PolynomialHeightBound (fun _ _ => 0) p ε := by
  refine ⟨1, 1, 0, 1, by norm_num, le_rfl, le_rfl, by norm_num, ?_⟩
  intro Z t hZ _
  simp only [Real.rpow_zero, mul_one, one_mul]
  exact Real.rpow_nonneg (by linarith) _

theorem polynomialHeightBound_add {E F : ℝ → ℝ → ℝ} {p ε : ℝ}
    (hE : PolynomialHeightBound E p ε) (hF : PolynomialHeightBound F p ε) :
    PolynomialHeightBound (fun Z t => E Z t + F Z t) p ε := by
  obtain ⟨C₁, Z₁, A₁, h₁, hC₁, hZ₁, hA₁, hh₁, hb₁⟩ := hE
  obtain ⟨C₂, Z₂, A₂, h₂, hC₂, hZ₂, hA₂, hh₂, hb₂⟩ := hF
  refine ⟨C₁ + C₂, max Z₁ Z₂, max A₁ A₂, min h₁ h₂,
    add_pos hC₁ hC₂, hZ₁.trans (le_max_left _ _),
    hA₁.trans (le_max_left _ _), lt_min hh₁ hh₂, ?_⟩
  intro Z t hZ ht
  have hZpos : 1 ≤ Z := hZ₁.trans ((le_max_left _ _).trans hZ)
  have hbase : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  have ht₁ : |t| ≤ Z ^ h₁ := ht.trans
    (Real.rpow_le_rpow_of_exponent_le hZpos (min_le_left _ _))
  have ht₂ : |t| ≤ Z ^ h₂ := ht.trans
    (Real.rpow_le_rpow_of_exponent_le hZpos (min_le_right _ _))
  have h₁' : E Z t ≤ C₁ * Z ^ (p + ε) * (1 + |t|) ^ (max A₁ A₂) := by
    apply (hb₁ Z t ((le_max_left _ _).trans hZ) ht₁).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hbase (le_max_left _ _))
      (mul_nonneg hC₁.le (Real.rpow_nonneg (by linarith) _))
  have h₂' : F Z t ≤ C₂ * Z ^ (p + ε) * (1 + |t|) ^ (max A₁ A₂) := by
    apply (hb₂ Z t ((le_max_right _ _).trans hZ) ht₂).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hbase (le_max_right _ _))
      (mul_nonneg hC₂.le (Real.rpow_nonneg (by linarith) _))
  calc
    _ ≤ C₁ * Z ^ (p + ε) * (1 + |t|) ^ (max A₁ A₂) +
      C₂ * Z ^ (p + ε) * (1 + |t|) ^ (max A₁ A₂) := add_le_add h₁' h₂'
    _ = _ := by ring

theorem polynomialHeightBound_finset_sum {ι : Type*} (S : Finset ι)
    (E : ι → ℝ → ℝ → ℝ) {p ε : ℝ}
    (hE : ∀ i ∈ S, PolynomialHeightBound (E i) p ε) :
    PolynomialHeightBound (fun Z t => ∑ i ∈ S, E i Z t) p ε := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using polynomialHeightBound_zero p ε
  | @insert i S hi ih =>
    have h₁ := hE i (Finset.mem_insert_self _ _)
    have h₂ := ih (fun j hj => hE j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using polynomialHeightBound_add h₁ h₂

/-- A witness may choose its finite expansion index separately in every
row and at every height. A single pre-specified finite index set covers
those choices; its entire family is quantified before constants. -/
theorem polynomialHeightBound_finite_cover {ι κ : Type*} (S : Finset ι)
    (R : ℝ → ℝ → Finset κ) (W : ι → ℝ → ℝ → Finset κ) {p ε : ℝ}
    (hcover : ∀ Z t, 1 ≤ Z → ∀ u ∈ R Z t, ∃ i ∈ S, u ∈ W i Z t)
    (hW : ∀ i ∈ S,
      PolynomialHeightBound (fun Z t => ((W i Z t).card : ℝ)) p ε) :
    PolynomialHeightBound (fun Z t => ((R Z t).card : ℝ)) p ε := by
  classical
  apply polynomialHeightBound_mono
    (polynomialHeightBound_finset_sum S (fun i Z t => ((W i Z t).card : ℝ)) hW)
  intro Z t hZ
  have hsub : R Z t ⊆ S.biUnion (fun i => W i Z t) := by
    intro u hu
    exact Finset.mem_biUnion.mpr (hcover Z t hZ u hu)
  have hc : (R Z t).card ≤ ∑ i ∈ S, (W i Z t).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  exact_mod_cast hc

end HeckeGeneral.Analysis.ConditionalMoments
