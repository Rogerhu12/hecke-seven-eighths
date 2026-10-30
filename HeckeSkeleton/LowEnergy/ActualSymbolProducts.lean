import HeckeSkeleton.LowEnergy.ActualReflection
import HeckeSkeleton.LowEnergy.ActualSymbols

/-! Exact aggregation of the literal prime evaluations into the actual ideal symbol. -/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowEnergy.ActualSymbolProducts

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.SquarefreeAmplification
open AlgebraicNumberTheory.PowerResidueSymbols
open HeckePort.CenteredMomentGenerator
open HeckeSkeleton.LowEnergy.ActualSymbols HeckeSkeleton.LowEnergy.ActualReflection
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

theorem primeSetIdeal_val (F : Finset (ExteriorPrime K S)) :
    (primeSetIdeal K S F).val.val = ∏ p ∈ F, p.val.asIdeal := by
  change (∏ p ∈ F.image Subtype.val, p.asIdeal) = _
  rw [Finset.prod_image]
  intro p _ q _ h
  exact Subtype.ext h

theorem exteriorSupport_image (I : ExteriorIdeal K S) :
    (exteriorSupport K S I).image Subtype.val = idealPrimeSupport K I.val := by
  simp only [exteriorSupport, Finset.image_image]
  exact Finset.attach_image_val

theorem primeSetIdeal_support (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) :
    primeSetIdeal K S (exteriorSupport K S I) = I := by
  apply Subtype.ext
  change squarefreeIdeal K ((exteriorSupport K S I).image Subtype.val) = I.val
  rw [exteriorSupport_image, squarefreeIdeal_primeSupport K I.val hI]

/-- The single-prime ideal evaluation is exactly the local prime evaluation. -/
theorem idealSymbol_prime (p : ExteriorPrime K S) (a : S.integer K) :
    idealSymbol K S D (exteriorPrimeIdeal K S p) a = primeEvaluation K S D p a := by
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
  change primeEvaluation K S D p a ^ idealPrimeMultiplicity K p.val p.val.asIdeal = _
  rw [hmult, pow_one]

/-- A fixed exterior numerator gives a genuine monoid hom in the denominator;
the nonexterior ideals remain zero as in `sexticSymbol`. -/
def denominatorSymbolHom (hD : AllowedGeneratorInput K S D) (J : ExteriorIdeal K S) :
    Ideal (𝓞 K) →* ℂ where
  toFun I := sexticSymbol K S D I J.val.val
  map_one' := by
    have h1 : IsExterior K S (1 : Ideal (𝓞 K)) := by
      refine ⟨one_ne_zero, ?_⟩
      intro p hp
      exact False.elim (p.prime.not_unit (isUnit_of_dvd_one hp))
    rw [sexticSymbol_of_exterior K S D _ _ h1
      ⟨nonZeroDivisors.coe_ne_zero J.val, J.property⟩]
    change sIntegerSexticIdealEvaluation K S D.root6 D.primitive6 D.embedding
      ⊤ _ _ _ (D.generator J) = 1
    exact sIntegerSexticIdealEvaluation_top K S D.root6 D.primitive6 D.embedding _ _ _
  map_mul' := by
    intro I L
    exact sexticSymbol_mul_left K S D hD I L J.val.val

/-- Prime-by-prime row phases aggregate into the actual ideal symbol,
using the actual squarefree ideal reconstruction. -/
theorem idealSymbol_generator_eq_prime_product (hD : AllowedGeneratorInput K S D)
    (I J : ExteriorIdeal K S) (hI : Squarefree I.val.val) :
    idealSymbol K S D I (D.generator J) =
      ∏ p ∈ exteriorSupport K S I, primeEvaluation K S D p (D.generator J) := by
  let f := denominatorSymbolHom K S D hD J
  have hvalue : ∀ A : ExteriorIdeal K S, f A.val.val = idealSymbol K S D A (D.generator J) := by
    intro A
    exact sexticSymbol_of_exterior K S D A.val.val J.val.val
      ⟨nonZeroDivisors.coe_ne_zero A.val, A.property⟩
      ⟨nonZeroDivisors.coe_ne_zero J.val, J.property⟩
  calc
    _ = f I.val.val := (hvalue I).symm
    _ = f (primeSetIdeal K S (exteriorSupport K S I)).val.val := by
      rw [primeSetIdeal_support K S I hI]
    _ = ∏ p ∈ exteriorSupport K S I, f p.val.asIdeal := by
      rw [primeSetIdeal_val, map_prod]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p _
      change f (exteriorPrimeIdeal K S p).val.val = _
      rw [hvalue, idealSymbol_prime]

end HeckeSkeleton.LowEnergy.ActualSymbolProducts
