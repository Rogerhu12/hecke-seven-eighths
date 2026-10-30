import HeckeSkeleton.LowFrozenCube.ExteriorReflection

/-!
# Bounds for every actual reflected coefficient

`HeckeCharacter` already takes values in the unit circle.  The only
additional character condition below is that it is unramified outside S,
exactly the `exterior_unramified` field of the original reflection input.
The period values, unit evaluations, inverse residue phases, row Gauss
factor and inactive ordinary factors are bounded from their definitions.
The final constructor leaves only actual finite support and annulus data
for `AnnularSupport`; it asks for no phase or coefficient norm estimates.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowFrozenCube.Exterior

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowHybrid
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S) (hD : AllowedGeneratorInput K S D)

theorem primeEvaluation_unit_norm (p : ExteriorPrime K S) (u : S.unit K) :
    ‖primeEvaluation K S D p (S.unitEquivUnitsInteger K u).val‖ = 1 := by
  letI : Field (𝓞 K ⧸ p.val.asIdeal) := Ideal.Quotient.field _
  unfold primeEvaluation sIntegerSexticEvaluation
  exact sexticResidueCharacter_norm K D.root6 D.primitive6 D.embedding p.val
    (D.away_six p.val p.property) _ (sUnitSexticResidueUnit K S p.val p.property u).ne_zero

theorem idealSymbol_unit_norm (I : ExteriorIdeal K S) (u : S.unit K) :
    ‖idealSymbol K S D I (S.unitEquivUnitsInteger K u).val‖ = 1 := by
  apply norm_sIntegerSexticIdealEvaluation_eq_one K S D.root6 D.primitive6 D.embedding
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp))
  intro p hp
  letI : Field (𝓞 K ⧸ p.asIdeal) := Ideal.Quotient.field _
  exact (sUnitSexticResidueUnit K S p (I.property p hp) u).ne_zero

/-- Inverse powers retain the zero branch.  No coprimality assumption is
needed for the upper bound, including negative exponents. -/
theorem primeEvaluation_generator_zpow_norm_le_one
    (p : ExteriorPrime K S) (I : ExteriorIdeal K S) (e : ℤ) :
    ‖primeEvaluation K S D p (D.generator I) ^ e‖ ≤ 1 := by
  have hroot := sextic_symbol_zero_or_root (ExteriorSymbol.symbolHom K S D hD)
    (PrimeCoordinates.Coprime (ExteriorArithmetic.coords K S))
    (ExteriorSymbol.symbolHom_sixth K S D hD) (exteriorPrimeIdeal K S p) I
  change ExteriorSymbol.symbol K S D (exteriorPrimeIdeal K S p) I = 0 ∨
    ExteriorSymbol.symbol K S D (exteriorPrimeIdeal K S p) I ^ 6 = 1 at hroot
  simp only [ExteriorSymbol.symbol_prime_left] at hroot
  rcases hroot with hz | hz
  · by_cases he : e = 0 <;> simp [hz, he]
  · simp only [norm_zpow, Complex.norm_eq_one_of_pow_eq_one hz (by decide),
      one_zpow, le_refl]

theorem primeEvaluation_generator_norm_le_one
    (p : ExteriorPrime K S) (I : ExteriorIdeal K S) :
    ‖primeEvaluation K S D p (D.generator I)‖ ≤ 1 := by
  simpa only [zpow_one] using
    primeEvaluation_generator_zpow_norm_le_one K S D hD p I 1

theorem primeEvaluation_generator_norm_one
    (p : ExteriorPrime K S) (I : ExteriorIdeal K S)
    (hI : primeExponents I.val p.val = 0) :
    ‖primeEvaluation K S D p (D.generator I)‖ = 1 := by
  have hcop : PrimeCoordinates.Coprime (ExteriorArithmetic.coords K S)
      (exteriorPrimeIdeal K S p) I := by
    intro q
    by_cases he : q = p
    · subst q
      exact Or.inr hI
    · left
      rw [← ExteriorArithmetic.prime_coords K S p, PrimeCoordinates.valuation_primeElement]
      simp [Finsupp.single_apply, he, Ne.symm he]
  have h6 := ExteriorSymbol.symbol_sixth K S D (exteriorPrimeIdeal K S p) I
  rw [if_pos hcop, ExteriorSymbol.symbol_prime_left] at h6
  exact Complex.norm_eq_one_of_pow_eq_one h6 (by decide)

theorem primeExponents_removePrime_self (I : ExteriorIdeal K S) (p : ExteriorPrime K S) :
    primeExponents (removePrime K S I p).val p.val = 0 := by
  change primeExponents (idealOfPrimeExponents ((primeExponents I.val).erase p.val)) p.val = 0
  rw [primeExponents_idealOfPrimeExponents, Finsupp.erase_same]

theorem row_prime_scalar_norm (p : ExteriorPrime K S) :
    ‖localWeylScalar K S D p ⟨1, by decide⟩ 0‖ = 1 := by
  letI : Field (𝓞 K ⧸ p.val.asIdeal) := Ideal.Quotient.field _
  letI : Fintype (𝓞 K ⧸ p.val.asIdeal) := Fintype.ofFinite _
  rw [localWeylScalar_eq]
  exact ThetaLocal.ResidueField.row_prime_scalar_norm (thetaPrimeCharacter K S D p)
    (primeCharacter_order K S D p) (primeAddCharacter K S D p)
    (primeAddCharacter_primitive K S D p)

variable (θ : HeckeCharacter K)
variable (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)

/-- Unramified exterior Hecke coefficients have norm one by their actual
prime-factor product, using that every local component lands in `Circle`. -/
theorem heckeIdealCoefficient_norm_one (I : ExteriorIdeal K S) :
    ‖heckeIdealCoefficient K θ I.val‖ = 1 := by
  change ‖idealCoefficient (primeCoefficient K θ) I.val.val‖ = 1
  rw [idealCoefficient, if_neg (nonZeroDivisors.coe_ne_zero I.val), Multiset.norm_prod_map]
  apply Multiset.prod_eq_one
  intro z hz
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hz
  have hp : Prime P := prime_of_normalized_factor P hP
  let p : HeightOneSpectrum (𝓞 K) := HeightOneSpectrum.ofPrime hp
  have hpS : p ∉ S := I.property p (dvd_of_mem_normalizedFactors hP)
  rw [primeIdealValue, dif_pos hp, primeCoefficient_of_unramified K θ p (hθ p hpS)]
  simp

theorem periodValue_norm_one (d : MarkedDatum K S) (I : ExteriorIdeal K S) :
    ‖periodValue K S D d θ I‖ = 1 := by
  rw [periodValue, norm_mul, heckeIdealCoefficient_norm_one K S θ hθ,
    idealSymbol_unit_norm K S D, one_mul]

private theorem norm_mul_le_one {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖z * w‖ ≤ 1 := by
  rw [norm_mul]
  exact (mul_le_mul hz hw (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

private theorem norm_pow_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) (e : ℕ) :
    ‖z ^ e‖ ≤ 1 := by
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) hz

private theorem norm_prod_le_one {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ p ∈ s, ‖f p‖ ≤ 1) : ‖∏ p ∈ s, f p‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) h

theorem inactive_ordinary_norm_le_one (p : ExteriorPrime K S) :
    ‖1 - (p.val.asIdeal.absNorm : ℂ)⁻¹‖ ≤ 1 := by
  have hq : (1 : ℝ) ≤ p.val.asIdeal.absNorm := by
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm p.val).le
  have h0 : (0 : ℝ) ≤ (p.val.asIdeal.absNorm : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have h1 : (p.val.asIdeal.absNorm : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq
  have hcast : (1 : ℂ) - (p.val.asIdeal.absNorm : ℂ)⁻¹ =
      ((1 - (p.val.asIdeal.absNorm : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv,
      Complex.ofReal_natCast]
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h1)]
  linarith

variable (d : MarkedDatum K S) (i : ReflectionIndex K S d)

/-- The actual row base is a unit phase for every row avoiding the frozen
support.  The removed-prime numerator is coprime by construction. -/
theorem reflectionRowBase_norm_one (a : ExteriorIdeal K S)
    (ha : PrimeCoordinates.Avoids (ExteriorArithmetic.coords K S) (frozenPrimes K S d) a) :
    ‖reflectionRowBase K S D d i θ a‖ = 1 := by
  unfold reflectionRowBase
  rw [norm_mul, norm_pow, periodValue_norm_one K S D θ hθ, one_pow, one_mul, norm_prod]
  apply Finset.prod_eq_one
  intro p hp
  have hpF : p ∉ i.activeFrozen := by
    intro hF
    exact (mem_exteriorSupport_iff K S a p).mp hp (ha p (i.frozen_subset hF))
  have hactive : primeExponents (activeFrozenIdeal K S d i).val p.val = 0 := by
    change PrimeCoordinates.valuation (ExteriorArithmetic.coords K S)
      (primeSetIdeal K S i.activeFrozen) p = 0
    rw [valuation_primeSetIdeal, if_neg hpF]
  simp only [norm_mul, norm_zpow, row_prime_scalar_norm K S D,
    primeEvaluation_unit_norm K S D,
    primeEvaluation_generator_norm_one K S D p (removePrime K S a p)
      (primeExponents_removePrime_self K S a p),
    primeEvaluation_generator_norm_one K S D p (activeFrozenIdeal K S d i) hactive,
    one_zpow, one_mul]

theorem reflectionMarkBase_norm_le_one (a : ExteriorIdeal K S) :
    ‖reflectionMarkBase K S D d i θ a‖ ≤ 1 := by
  unfold reflectionMarkBase
  apply norm_mul_le_one
  · simp only [norm_pow, periodValue_norm_one K S D θ hθ, one_pow, le_refl]
  · apply norm_prod_le_one
    intro p _
    apply norm_mul_le_one (le_of_eq (thetaGamma_exteriorPrime_two_norm K S D p))
    apply norm_pow_le_one
    exact norm_mul_le_one
      (norm_mul_le_one (le_of_eq (primeEvaluation_unit_norm K S D p _))
        (primeEvaluation_generator_zpow_norm_le_one K S D hD p (removePrime K S a p) (-2)))
      (primeEvaluation_generator_zpow_norm_le_one K S D hD p (activeFrozenIdeal K S d i) (-2))

theorem reflectionColumnBase_norm_le_one (a : ExteriorIdeal K S) :
    ‖reflectionColumnBase K S D d i θ a‖ ≤ 1 := by
  unfold reflectionColumnBase
  apply norm_mul_le_one
  · simp only [norm_inv, periodValue_norm_one K S D θ hθ, inv_one, le_refl]
  · apply norm_prod_le_one
    intro p _
    apply norm_mul_le_one (le_of_eq (thetaGamma_exteriorPrime_two_norm K S D p))
    apply norm_pow_le_one
    exact norm_mul_le_one
      (norm_mul_le_one (le_of_eq (primeEvaluation_unit_norm K S D p _))
        (primeEvaluation_generator_norm_le_one K S D hD p (removePrime K S a p)))
      (primeEvaluation_generator_zpow_norm_le_one K S D hD p (activeFrozenIdeal K S d i) (-2))

theorem reflectionPhase_norm_le_one (c a n : ExteriorIdeal K S) :
    ‖reflectionPhase K S D d i θ c a n‖ ≤ 1 := by
  unfold reflectionPhase
  apply norm_mul_le_one
  · apply norm_mul_le_one
    · apply norm_mul_le_one
      · apply norm_mul_le_one
        · exact norm_prod_le_one _ _ (fun p _ => inactive_ordinary_norm_le_one K S p)
        · simp only [norm_inv, periodValue_norm_one K S D θ hθ, inv_one, le_refl]
      · simp only [norm_zpow, periodValue_norm_one K S D θ hθ, one_zpow, le_refl]
    · simp only [norm_pow, periodValue_norm_one K S D θ hθ, one_pow, le_refl]
  · apply norm_prod_le_one
    intro p _
    apply norm_pow_le_one
    apply norm_mul_le_one
    · apply norm_mul_le_one
      · exact norm_mul_le_one (le_of_eq (primeEvaluation_unit_norm K S D p _))
          (primeEvaluation_generator_norm_le_one K S D hD p (removePrime K S a p))
      · exact norm_pow_le_one (primeEvaluation_generator_norm_le_one K S D hD p n) 3
    · exact primeEvaluation_generator_zpow_norm_le_one K S D hD p
        (removePrime K S (activeFrozenIdeal K S d i) p) (-2)

/-- The actual source block satisfies all coefficient fields automatically.
Only the finite support, squarefreeness and annular cutoff facts remain. -/
theorem reflectionSourceBlock_annularSupport
    (pow sup : ExteriorIdeal K S) (rows marks columns : Finset (ExteriorIdeal K S))
    (inputs : Finset (ExteriorIdeal K S × ExteriorIdeal K S))
    (Z H v ell z rowBall : ℝ)
    (hrows : ∀ a ∈ rows, exteriorNorm K S a ≤ rowBall)
    (hresidual : ∀ a ∈ PrimeCoordinates.residualRows (ExteriorArithmetic.coords K S)
      (frozenPrimes K S d) pow sup rows, exteriorNorm K S a ≤ Z ^ H)
    (hmarks : ∀ P ∈ marks, ∀ p ∈ frozenPrimes K S d, ¬p.val.asIdeal ∣ P.val.val)
    (hmarks_sf : ∀ P ∈ marks, Squarefree P.val.val ∧ exteriorNorm K S P ≤ Z ^ z)
    (hcolumns : ∀ c ∈ columns, ∀ p ∈ i.activeFrozen, ¬p.val.asIdeal ∣ c.val.val)
    (hcolumns_sf : ∀ c ∈ columns, Squarefree c.val.val ∧ exteriorNorm K S c ≤ Z ^ v)
    (hcolumns_lower : ∀ c ∈ columns, Z ^ v / 2 ≤ exteriorNorm K S c)
    (hinput_support : ∀ q ∈ inputs, exteriorSupport K S q.1 ⊆ i.activeFrozen)
    (hinput_away : ∀ q ∈ inputs, ∀ p ∈ i.activeFrozen, ¬p.val.asIdeal ∣ q.2.val.val)
    (hcube_lower : ∀ q ∈ inputs, Z ^ ell / 2 ≤
      exteriorNorm K S (PrimeCoordinates.residualCubeFactor (ExteriorArithmetic.coords K S)
        q.1 * q.2))
    (hcube_upper : ∀ q ∈ inputs,
      exteriorNorm K S (PrimeCoordinates.residualCubeFactor (ExteriorArithmetic.coords K S)
        q.1 * q.2) ≤ Z ^ ell) :
    FrozenReduction.AnnularSupport ((ofReflectionIndex K S d i).toFrozen K S D hD)
      (ExteriorArithmetic.normHom K S) Z H v ell z
      (reflectionSourceBlock K S D d i θ pow sup rows marks columns inputs) where
  rowBall := rowBall
  rows_norm := hrows
  residual_norm := hresidual
  rho_norm a _ ha := reflectionRowBase_norm_one K S D θ hθ d i a ha
  marks_away P hP := (avoids_iff K S _ P).mpr (hmarks P hP)
  marks_sf_norm P hP :=
    ⟨(ExteriorArithmetic.coords_squarefree_iff K S P).mpr (hmarks_sf P hP).1,
      (hmarks_sf P hP).2⟩
  marks_coeff P _ := reflectionMarkBase_norm_le_one K S D hD θ hθ d i P
  columns_away c hc := (avoids_iff K S _ c).mpr (hcolumns c hc)
  columns_sf_norm c hc :=
    ⟨(ExteriorArithmetic.coords_squarefree_iff K S c).mpr (hcolumns_sf c hc).1,
      (hcolumns_sf c hc).2⟩
  columns_coeff c _ := reflectionColumnBase_norm_le_one K S D hD θ hθ d i c
  columns_lower := hcolumns_lower
  input_supported q hq := (supported_iff K S _ q.1).mpr (hinput_support q hq)
  input_away q hq := (avoids_iff K S _ q.2).mpr (hinput_away q hq)
  input_phase c _ q _ := reflectionPhase_norm_le_one K S D hD θ hθ d i c q.1 q.2
  cube_lower := hcube_lower
  cube_upper := hcube_upper

#print axioms periodValue_norm_one
#print axioms reflectionRowBase_norm_one
#print axioms reflectionMarkBase_norm_le_one
#print axioms reflectionColumnBase_norm_le_one
#print axioms reflectionPhase_norm_le_one
#print axioms reflectionSourceBlock_annularSupport

end HeckeSkeleton.LowFrozenCube.Exterior
