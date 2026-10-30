import HeckeGeneral.Analysis.MarkedThetaReflection

/-!
The actual cubic residue kernel on exterior ideals.  These are arithmetic
identities and finite energy identities, not a large sieve estimate.
-/

set_option autoImplicit false
noncomputable section

namespace CubicSieve.ExteriorKernel

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- Row first, column second, with the target's original sextic symbol. -/
def symbol (I J : ExteriorIdeal K S) : ℂ :=
  idealSymbol K S D J (D.generator I)

/-- The requested nonzero integer exponents retain common-prime zeros. -/
def kernel (e : ℤ) (I J : ExteriorIdeal K S) : ℂ :=
  symbol K S D I J ^ e

abbrev positiveKernel (I J : ExteriorIdeal K S) : ℂ := kernel K S D 2 I J

private theorem localEvaluation_seven
    (p : HeightOneSpectrum (𝓞 K)) (hpS : p ∉ S)
    (hp6 : (6 : 𝓞 K) ∉ p.asIdeal) (a : S.integer K) :
    sIntegerSexticEvaluation K S p hpS D.root6 D.primitive6 D.embedding hp6 a ^ 7 =
      sIntegerSexticEvaluation K S p hpS D.root6 D.primitive6 D.embedding hp6 a := by
  let χ := sexticResidueCharacter K D.root6 D.primitive6 D.embedding p hp6
  have h6 : χ ^ 6 = 1 := by
    have hh := pow_orderOf_eq_one χ
    rw [sexticResidueCharacter_order K D.root6 D.primitive6 D.embedding p hp6] at hh
    exact hh
  have h7 : χ ^ 7 = χ := by
    rw [show (7 : ℕ) = 6 + 1 by decide, pow_add, h6, one_mul, pow_one]
  change χ (sIntegerSexticResidueMap K S p hpS a) ^ 7 = _
  rw [← MulChar.pow_apply' χ (by decide : (7 : ℕ) ≠ 0), h7]
  rfl

/-- The genuine zero-extended sextic symbol, including nonunits, satisfies this identity. -/
theorem symbol_pow_seven (I J : ExteriorIdeal K S) :
    symbol K S D I J ^ 7 = symbol K S D I J := by
  simp only [symbol, idealSymbol, sIntegerSexticIdealEvaluation]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p _
  rw [← pow_mul, Nat.mul_comm _ 7, pow_mul, localEvaluation_seven]

/-- The actual squared sextic kernel is a cubic zero-extended kernel. -/
theorem positiveKernel_pow_four (I J : ExteriorIdeal K S) :
    positiveKernel K S D I J ^ 4 = positiveKernel K S D I J := by
  change (symbol K S D I J ^ (2 : ℕ)) ^ 4 = symbol K S D I J ^ (2 : ℕ)
  rw [← pow_mul, show (2 * 4 : ℕ) = 7 + 1 by decide, pow_add,
    symbol_pow_seven, pow_one, pow_two]

theorem positiveKernel_cube_zero_mask (I J : ExteriorIdeal K S) :
    positiveKernel K S D I J ^ 3 = if symbol K S D I J = 0 then 0 else 1 := by
  by_cases hz : symbol K S D I J = 0
  · simp [positiveKernel, kernel, hz]
  · rw [ite_eq_right hz]
    have h6 : symbol K S D I J ^ 6 = 1 := by
      apply mul_right_cancel₀ hz
      simpa only [← pow_succ, one_mul] using symbol_pow_seven K S D I J
    change (symbol K S D I J ^ (2 : ℕ)) ^ 3 = 1
    simpa only [← pow_mul] using h6

theorem symbol_eq_zero_or_norm_eq_one (I J : ExteriorIdeal K S) :
    symbol K S D I J = 0 ∨ ‖symbol K S D I J‖ = 1 := by
  by_cases hz : symbol K S D I J = 0
  · exact Or.inl hz
  · right
    apply norm_sIntegerSexticIdealEvaluation_eq_one K S D.root6 D.primitive6
      D.embedding J.val.val (nonZeroDivisors.coe_ne_zero J.val) J.property
      (fun q hq => D.away_six q (J.property q hq)) (D.generator I)
    intro p hp hzero
    apply hz
    exact sIntegerSexticIdealEvaluation_eq_zero_of_badPrime K S
      D.root6 D.primitive6 D.embedding J.val.val
      (nonZeroDivisors.coe_ne_zero J.val) J.property
      (fun q hq => D.away_six q (J.property q hq)) (D.generator I) p hp hzero

theorem norm_symbol_le_one (I J : ExteriorIdeal K S) :
    ‖symbol K S D I J‖ ≤ 1 := by
  exact norm_sIntegerSexticIdealEvaluation_le_one K S D.root6 D.primitive6
    D.embedding J.val.val (nonZeroDivisors.coe_ne_zero J.val) J.property
    (fun q hq => D.away_six q (J.property q hq)) (D.generator I)

/-- This includes zero; conjugation never erases a common-prime zero. -/
theorem symbol_inv_eq_conj (I J : ExteriorIdeal K S) :
    (symbol K S D I J)⁻¹ = conj (symbol K S D I J) := by
  rcases symbol_eq_zero_or_norm_eq_one K S D I J with hz | hn
  · simp [hz]
  · exact Complex.inv_eq_conj hn

theorem kernel_neg_two_eq_conj (I J : ExteriorIdeal K S) :
    kernel K S D (-2) I J = conj (kernel K S D 2 I J) := by
  change (symbol K S D I J ^ (2 : ℕ))⁻¹ = conj (symbol K S D I J ^ (2 : ℕ))
  rw [← inv_pow, symbol_inv_eq_conj, map_pow]

theorem norm_kernel_le_one (e : ℤ) (he : e = 2 ∨ e = -2)
    (I J : ExteriorIdeal K S) : ‖kernel K S D e I J‖ ≤ 1 := by
  have htwo : ‖kernel K S D 2 I J‖ ≤ 1 := by
    simpa only [kernel, zpow_ofNat, norm_pow] using
      (pow_le_one₀ (n := 2) (norm_nonneg (symbol K S D I J))
        (norm_symbol_le_one K S D I J))
  rcases he with rfl | rfl
  · exact htwo
  · rw [kernel_neg_two_eq_conj, Complex.norm_conj]
    exact htwo

/-- A common prime factor kills the original symbol for any generating section. -/
theorem symbol_eq_zero_of_not_coprime (I J : ExteriorIdeal K S)
    (h : ¬ IsCoprime I.val.val J.val.val) : symbol K S D I J = 0 := by
  have hsup : I.val.val ⊔ J.val.val ≠ ⊤ :=
    fun hs => h (Ideal.isCoprime_iff_sup_eq.mpr hs)
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hsup
  have hIM : I.val.val ≤ M := le_sup_left.trans hle
  have hJM : J.val.val ≤ M := le_sup_right.trans hle
  have hM0 : M ≠ ⊥ := by
    intro hzero
    exact nonZeroDivisors.coe_ne_zero I.val (eq_bot_iff.mpr (hzero ▸ hIM))
  let p : HeightOneSpectrum (𝓞 K) := ⟨M, hM.isPrime, hM0⟩
  have hp : p.asIdeal ∣ J.val.val := Ideal.dvd_iff_le.mpr hJM
  have hgen : D.generator I ∈ I.val.val.map (algebraMap (𝓞 K) (S.integer K)) := by
    rw [← D.generator_span I]
    exact Ideal.subset_span (by simp)
  have hmem : D.generator I ∈ p.asIdeal.map (algebraMap (𝓞 K) (S.integer K)) :=
    Ideal.map_mono hIM hgen
  apply sIntegerSexticIdealEvaluation_eq_zero_of_badPrime K S
    D.root6 D.primitive6 D.embedding J.val.val
    (nonZeroDivisors.coe_ne_zero J.val) J.property
    (fun q hq => D.away_six q (J.property q hq)) (D.generator I) p hp
  change (HeckeGeneral.Arithmetic.sIntegerResidueEquiv K S p.asIdeal
    (sIntegerSexticResidue_coprime K S p (J.property p hp))).symm
      (Ideal.Quotient.mk _ (D.generator I)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]

/-- The common-prime zeros are exact, for the original generating section. -/
theorem symbol_eq_zero_iff_not_coprime (I J : ExteriorIdeal K S) :
    symbol K S D I J = 0 ↔ ¬ IsCoprime I.val.val J.val.val := by
  refine ⟨?_, symbol_eq_zero_of_not_coprime K S D I J⟩
  intro hz hcop
  obtain ⟨p, hp, hzero⟩ := (sIntegerSexticIdealEvaluation_eq_zero_iff K S
    D.root6 D.primitive6 D.embedding J.val.val
    (nonZeroDivisors.coe_ne_zero J.val) J.property
    (fun q hq => D.away_six q (J.property q hq)) (D.generator I)).mp hz
  let e := HeckeGeneral.Arithmetic.sIntegerResidueEquiv K S p.asIdeal
    (sIntegerSexticResidue_coprime K S p (J.property p hp))
  have hmem : D.generator I ∈ p.asIdeal.map (algebraMap (𝓞 K) (S.integer K)) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply e.symm.injective
    simpa only [e, sIntegerSexticResidueMap, RingHom.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_zero] using hzero
  have hIle : I.val.val.map (algebraMap (𝓞 K) (S.integer K)) ≤
      p.asIdeal.map (algebraMap (𝓞 K) (S.integer K)) := by
    rw [← D.generator_span I]
    apply Ideal.span_le.mpr
    intro x hx
    have hx' : x = D.generator I := Set.mem_singleton_iff.mp hx
    rw [hx']
    exact hmem
  have hJle : J.val.val.map (algebraMap (𝓞 K) (S.integer K)) ≤
      p.asIdeal.map (algebraMap (𝓞 K) (S.integer K)) :=
    Ideal.map_mono (Ideal.dvd_iff_le.mp hp)
  have htop : p.asIdeal.map (algebraMap (𝓞 K) (S.integer K)) = ⊤ := by
    apply top_le_iff.mp
    have hsup : I.val.val.map (algebraMap (𝓞 K) (S.integer K)) ⊔
        J.val.val.map (algebraMap (𝓞 K) (S.integer K)) = ⊤ := by
      rw [← Ideal.map_sup, hcop.sup_eq, Ideal.map_top]
    rw [← hsup]
    exact sup_le hIle hJle
  have hone : sIntegerSexticResidueMap K S p (J.property p hp) 1 = 0 := by
    change e.symm (Ideal.Quotient.mk _ 1) = 0
    have hmemone : (1 : S.integer K) ∈
        p.asIdeal.map (algebraMap (𝓞 K) (S.integer K)) := by
      rw [htop]
      trivial
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmemone, map_zero]
  have : Nontrivial (𝓞 K ⧸ p.asIdeal) :=
    Ideal.Quotient.nontrivial_iff.mpr p.isPrime.ne_top
  exact one_ne_zero (by simpa only [map_one] using hone)

/-- A genuine coprimality mask, with no artificial unit value at a common prime. -/
theorem positiveKernel_cube_coprime_mask (I J : ExteriorIdeal K S) :
    positiveKernel K S D I J ^ 3 = if IsCoprime I.val.val J.val.val then 1 else 0 := by
  rw [positiveKernel_cube_zero_mask]
  by_cases h : IsCoprime I.val.val J.val.val
  · have hz : symbol K S D I J ≠ 0 :=
      fun hz => (symbol_eq_zero_iff_not_coprime K S D I J).mp hz h
    simp only [ite_eq_right hz, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_left
      ((symbol_eq_zero_iff_not_coprime K S D I J).mpr h)]

theorem kernel_eq_zero_of_not_coprime (e : ℤ) (he : e = 2 ∨ e = -2)
    (I J : ExteriorIdeal K S) (h : ¬ IsCoprime I.val.val J.val.val) :
    kernel K S D e I J = 0 := by
  rcases he with rfl | rfl <;>
    simp [kernel, symbol_eq_zero_of_not_coprime K S D I J h]

/-- Exact reciprocity is requested from the actual allowed-generator interface. -/
theorem kernel_reciprocity (hD : AllowedGeneratorInput K S D)
    (e : ℤ) (I J : ExteriorIdeal K S) :
    kernel K S D e I J = kernel K S D e J I := by
  unfold kernel symbol
  rw [hD.reciprocity J I]

def rowSum (e : ℤ) (B : Finset (ExteriorIdeal K S))
    (z : ExteriorIdeal K S → ℂ) (I : ExteriorIdeal K S) : ℂ :=
  ∑ J ∈ B, z J * kernel K S D e I J

def energy (e : ℤ) (A B : Finset (ExteriorIdeal K S))
    (z : ExteriorIdeal K S → ℂ) : ℝ :=
  ∑ I ∈ A, ‖rowSum K S D e B z I‖ ^ 2

/-- Changing the cubic orientation also conjugates the arbitrary column coefficients. -/
theorem rowSum_neg_two (B : Finset (ExteriorIdeal K S))
    (z : ExteriorIdeal K S → ℂ) (I : ExteriorIdeal K S) :
    rowSum K S D (-2) B z I =
      conj (rowSum K S D 2 B (fun J => conj (z J)) I) := by
  simp only [rowSum, map_sum, map_mul, Complex.conj_conj, kernel_neg_two_eq_conj]

theorem energy_neg_two (A B : Finset (ExteriorIdeal K S))
    (z : ExteriorIdeal K S → ℂ) :
    energy K S D (-2) A B z = energy K S D 2 A B (fun J => conj (z J)) := by
  simp only [energy, rowSum_neg_two, Complex.norm_conj]

omit [NumberField K] [Fintype S] in
theorem coefficient_energy_conj (B : Finset (ExteriorIdeal K S))
    (z : ExteriorIdeal K S → ℂ) :
    (∑ J ∈ B, ‖conj (z J)‖ ^ 2) = ∑ J ∈ B, ‖z J‖ ^ 2 := by
  simp only [Complex.norm_conj]

/-- A uniform positive-orientation estimate gives exactly both requested orientations.
The bound itself is an input here; no cubic sieve estimate is claimed. -/
theorem both_orientations_of_positive (A B : Finset (ExteriorIdeal K S)) (L : ℝ)
    (h : ∀ z : ExteriorIdeal K S → ℂ,
      energy K S D 2 A B z ≤ L * ∑ J ∈ B, ‖z J‖ ^ 2)
    (e : ℤ) (he : e = 2 ∨ e = -2) (z : ExteriorIdeal K S → ℂ) :
    energy K S D e A B z ≤ L * ∑ J ∈ B, ‖z J‖ ^ 2 := by
  rcases he with rfl | rfl
  · exact h z
  · simpa only [energy_neg_two, Complex.norm_conj] using h (fun J => conj (z J))

end CubicSieve.ExteriorKernel
