import HeckeSkeleton.LowHybrid.ExteriorSymbol
import HeckeSkeleton.LowHybrid.SieveBounds
import HeckeSkeleton.AllowedGeneratorNorm
import HeckeAxiom.QuadraticSieve
import CubicSieve.Complete

/-!
# The proved quadratic and cubic sieves in the exterior arithmetic interface

The quadratic input is the repository's theorem for one `ArithmeticChoice`.
The cubic input is `CubicSieve.Complete.targetBound`, with its actual allowed
generator hypothesis.  Only the squarefree dictionary and the order of the
coefficient/exponent arguments change.  These adapters add no analytic input.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowHybrid.ExteriorSieve

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K]
variable {S₀ : Finset (HeightOneSpectrum (𝓞 K))} {root12 : K} {σ : K →+* ℂ}

/-- All three allowed-generator fields for the repository's arithmetic
choice, without importing the admitted top-level theta skeleton. -/
theorem allowedInput (X : HeckeAxiom.ArithmeticChoice K S₀ root12 σ) :
    AllowedGeneratorInput K (X.places : Set (HeightOneSpectrum (𝓞 K))) X.thetaData :=
  AllowedGeneratorInput.of_multiplicative_reciprocity K
    (X.places : Set (HeightOneSpectrum (𝓞 K))) X.thetaData
    X.thetaData_multiplicative X.idealSymbol_reciprocity

/-- The actual quadratic sieve, with coordinate squarefreeness proved from
the underlying ideal's squarefreeness. -/
theorem quadraticSieveInput (X : HeckeAxiom.ArithmeticChoice K S₀ root12 σ) :
    QuadraticSieveInput
      (ExteriorArithmetic.normHom K (X.places : Set (HeightOneSpectrum (𝓞 K))))
      (PrimeArithmetic.Squarefree
        (ExteriorArithmetic.coords K (X.places : Set (HeightOneSpectrum (𝓞 K)))))
      (ExteriorSymbol.symbol K (X.places : Set (HeightOneSpectrum (𝓞 K))) X.thetaData) := by
  intro eps heps
  obtain ⟨C, hC, hbound⟩ := HeckeAxiom.quadratic_sieve_bound X eps heps
  refine ⟨C, hC, ?_⟩
  intro R N hR hN rows columns hrows hcolumns a
  exact hbound R N hR hN rows columns
    (fun I hI => ⟨(ExteriorArithmetic.coords_squarefree_iff K _ I).mp (hrows I hI).1,
      (hrows I hI).2⟩)
    (fun I hI => ⟨(ExteriorArithmetic.coords_squarefree_iff K _ I).mp (hcolumns I hI).1,
      (hcolumns I hI).2⟩) a

/-- The actual cubic sieve for both integer exponents `2` and `-2`.
Its coefficient function is quantified independently of the row ideal. -/
theorem cubicSieveInput (A : SArithmeticData K)
    (D : ThetaArithmeticData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (hD : AllowedGeneratorInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D) :
    CubicSieveInput
      (ExteriorArithmetic.normHom K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (PrimeArithmetic.Squarefree
        (ExteriorArithmetic.coords K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))))
      (ExteriorSymbol.symbol K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D) := by
  intro eps heps
  obtain ⟨C, hC, hbound⟩ := CubicSieve.Complete.targetBound A D hD eps heps
  refine ⟨C, hC, ?_⟩
  intro R N hR hN rows columns hrows hcolumns a e he
  exact hbound R N hR hN rows columns
    (fun I hI => ⟨(ExteriorArithmetic.coords_squarefree_iff K _ I).mp (hrows I hI).1,
      (hrows I hI).2⟩)
    (fun I hI => ⟨(ExteriorArithmetic.coords_squarefree_iff K _ I).mp (hcolumns I hI).1,
      (hcolumns I hI).2⟩) e he a

#print axioms allowedInput
#print axioms quadraticSieveInput
#print axioms cubicSieveInput

end HeckeSkeleton.LowHybrid.ExteriorSieve
