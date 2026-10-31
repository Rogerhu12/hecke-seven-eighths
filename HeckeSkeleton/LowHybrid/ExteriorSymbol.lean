import HeckeSkeleton.LowHybrid.ExteriorArithmetic
import CubicSieve.ExteriorKernel
import HeckeGeneral.Analysis.PrincipalGeneratorCalibration

/-!
# The actual sextic symbol on exterior ideals

The symbol is the repository's `idealSymbol`, evaluated at the allowed
generator of its second ideal.  Its multiplication law uses the sixth-power
S-unit error in `AllowedGeneratorInput.multiplicative`; the generators
themselves are never treated as strictly multiplicative.  The sixth-power
identity retains the exact zero at a common prime, including for ideals
with repeated prime factors.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowHybrid.ExteriorSymbol

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- Denominator first, allowed numerator generator second. -/
def symbol (I J : ExteriorIdeal K S) : ℂ :=
  idealSymbol K S D I (D.generator J)

@[simp] theorem symbol_apply (I J : ExteriorIdeal K S) :
    symbol K S D I J = idealSymbol K S D I (D.generator J) := rfl

/-- Exact reciprocity for the actual allowed section. -/
theorem symbol_reciprocity (hD : AllowedGeneratorInput K S D)
    (I J : ExteriorIdeal K S) :
    symbol K S D I J = symbol K S D J I :=
  hD.reciprocity I J

/-- The actual sixth-power S-unit discrepancy disappears under evaluation. -/
theorem symbol_mul_right (hD : AllowedGeneratorInput K S D)
    (I J L : ExteriorIdeal K S) :
    symbol K S D I (J * L) = symbol K S D I J * symbol K S D I L := by
  obtain ⟨u, hu⟩ := hD.multiplicative J L
  change idealSymbol K S D I (D.generator (exteriorMul K S J L)) = _
  dsimp only [symbol, idealSymbol]
  rw [hu, mul_assoc, sIntegerSexticIdealEvaluation_mul_sixth_power_unit,
    sIntegerSexticIdealEvaluation_mul]

/-- Multiplication in the denominator follows from actual full reciprocity. -/
theorem symbol_mul_left (hD : AllowedGeneratorInput K S D)
    (I J L : ExteriorIdeal K S) :
    symbol K S D (I * J) L = symbol K S D I L * symbol K S D J L := by
  rw [symbol_reciprocity K S D hD (I * J) L,
    symbol_mul_right K S D hD L I J,
    symbol_reciprocity K S D hD L I,
    symbol_reciprocity K S D hD L J]

theorem symbol_one_right (hD : AllowedGeneratorInput K S D)
    (I : ExteriorIdeal K S) : symbol K S D I 1 = 1 := by
  obtain ⟨u, hu⟩ :=
    AllowedGeneratorInput.generator_eq_sixth_power_of_ideal_eq_one K S D hD
      (1 : ExteriorIdeal K S) rfl
  dsimp only [symbol, idealSymbol]
  rw [hu]
  exact sIntegerSexticIdealEvaluation_sixth_power_unit K S
    D.root6 D.primitive6 D.embedding I.val.val
    (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp)) u

theorem symbol_one_left (hD : AllowedGeneratorInput K S D)
    (I : ExteriorIdeal K S) : symbol K S D 1 I = 1 := by
  rw [symbol_reciprocity K S D hD, symbol_one_right K S D hD]

theorem norm_symbol_le_one (I J : ExteriorIdeal K S) :
    ‖symbol K S D I J‖ ≤ 1 :=
  norm_sIntegerSexticIdealEvaluation_le_one K S D.root6 D.primitive6
    D.embedding I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp)) (D.generator J)

/-- This identity holds already for the original generating section.
No allowed-section compatibility is needed for the common-prime mask. -/
theorem symbol_sixth_ideal (I J : ExteriorIdeal K S) :
    symbol K S D I J ^ 6 =
      if IsCoprime I.val.val J.val.val then 1 else 0 := by
  have h := CubicSieve.ExteriorKernel.positiveKernel_cube_coprime_mask K S D J I
  change (symbol K S D I J ^ (2 : ℕ)) ^ (3 : ℕ) =
    (if IsCoprime J.val.val I.val.val then 1 else 0) at h
  rw [← pow_mul] at h
  by_cases hc : IsCoprime I.val.val J.val.val
  · simpa only [if_pos hc, if_pos hc.symm] using h
  · have hrev : ¬ IsCoprime J.val.val I.val.val := fun h => hc h.symm
    simpa only [if_neg hc, if_neg hrev] using h

/-- The sixth-power law in the precise prime-coordinate interface. -/
theorem symbol_sixth (I J : ExteriorIdeal K S) :
    symbol K S D I J ^ 6 =
      if LowFrozenCube.PrimeCoordinates.Coprime (ExteriorArithmetic.coords K S) I J
      then 1 else 0 := by
  rw [ExteriorArithmetic.coords_coprime_iff]
  exact symbol_sixth_ideal K S D I J

/-- The actual allowed-generator symbol as the right monoid homomorphism
consumed by the frozen-cube construction. -/
def symbolHom (hD : AllowedGeneratorInput K S D) (I : ExteriorIdeal K S) :
    ExteriorIdeal K S →* ℂ where
  toFun := symbol K S D I
  map_one' := symbol_one_right K S D hD I
  map_mul' := symbol_mul_right K S D hD I

@[simp] theorem symbolHom_apply (hD : AllowedGeneratorInput K S D)
    (I J : ExteriorIdeal K S) :
    symbolHom K S D hD I J = symbol K S D I J := rfl

theorem symbolHom_reciprocity (hD : AllowedGeneratorInput K S D)
    (I J : ExteriorIdeal K S) :
    symbolHom K S D hD I J = symbolHom K S D hD J I :=
  symbol_reciprocity K S D hD I J

theorem symbolHom_sixth (hD : AllowedGeneratorInput K S D)
    (I J : ExteriorIdeal K S) :
    symbolHom K S D hD I J ^ 6 =
      if LowFrozenCube.PrimeCoordinates.Coprime (ExteriorArithmetic.coords K S) I J
      then 1 else 0 :=
  symbol_sixth K S D I J

/-- Public dictionary from the global ideal product to the literal residue
evaluation at one exterior prime. -/
theorem idealSymbol_exteriorPrime (p : ExteriorPrime K S) (a : S.integer K) :
    idealSymbol K S D (exteriorPrimeIdeal K S p) a =
      primeEvaluation K S D p a := by
  let p0 : idealPrimeDivisors K p.val.asIdeal := ⟨p.val, dvd_refl _⟩
  letI : Fintype (idealPrimeDivisors K p.val.asIdeal) :=
    (idealPrimeDivisors_finite K p.val.asIdeal p.val.ne_bot).fintype
  have hsingle : ∀ q : idealPrimeDivisors K p.val.asIdeal, q = p0 := by
    intro q
    apply Subtype.ext
    have he : p.val.asIdeal = q.val.asIdeal :=
      p.val.isMaximal.eq_of_le q.val.isPrime.ne_top (Ideal.dvd_iff_le.mp q.property)
    exact HeightOneSpectrum.ext he.symm
  have hmult : idealPrimeMultiplicity K p.val p.val.asIdeal = 1 := by
    unfold idealPrimeMultiplicity
    exact Associates.count_self p.val.associates_irreducible
  change (∏ q : idealPrimeDivisors K p.val.asIdeal,
    sIntegerSexticEvaluation K S q.val
      ((exteriorPrimeIdeal K S p).property q.val q.property)
      D.root6 D.primitive6 D.embedding
      (D.away_six q.val ((exteriorPrimeIdeal K S p).property q.val q.property)) a ^
        idealPrimeMultiplicity K q.val p.val.asIdeal) = _
  rw [Finset.prod_eq_single_of_mem p0 (Finset.mem_univ p0)
    (fun q _ hne => False.elim (hne (hsingle q)))]
  change sIntegerSexticEvaluation K S p.val p.property D.root6 D.primitive6 D.embedding
    (D.away_six p.val p.property) a ^ idealPrimeMultiplicity K p.val p.val.asIdeal = _
  rw [hmult, pow_one, primeEvaluation]

theorem symbol_prime_left (p : ExteriorPrime K S) (I : ExteriorIdeal K S) :
    symbol K S D (exteriorPrimeIdeal K S p) I =
      primeEvaluation K S D p (D.generator I) :=
  idealSymbol_exteriorPrime K S D p (D.generator I)

theorem symbol_prime_right (hD : AllowedGeneratorInput K S D)
    (I : ExteriorIdeal K S) (p : ExteriorPrime K S) :
    symbol K S D I (exteriorPrimeIdeal K S p) =
      primeEvaluation K S D p (D.generator I) := by
  rw [symbol_reciprocity K S D hD, symbol_prime_left]

#print axioms symbol_mul_right
#print axioms symbol_mul_left
#print axioms symbol_one_right
#print axioms symbol_sixth
#print axioms symbolHom
#print axioms idealSymbol_exteriorPrime

end HeckeSkeleton.LowHybrid.ExteriorSymbol
