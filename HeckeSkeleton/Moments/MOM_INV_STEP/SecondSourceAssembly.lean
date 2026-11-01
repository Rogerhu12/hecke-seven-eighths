import HeckeSkeleton.Moments.MOM_INV_STEP.SecondMarkedSource
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondCanonicalEnergy

/-!
# The complete original second coefficient becomes a fixed-common column

This combines the actual normalized divisor Fourier calculation with
the original mark, cutoff and puncture. The fresh common and residual
ideals are computed from the original pair. No source identity or
energy estimate is assumed.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondSourceAssembly

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
  HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools
  SecondSourceColumns SecondMarkedSource SecondCanonicalEnergy
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "OS" => Set.integer Sset K
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
variable {σ : Type*} [DecidableEq σ] {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

def sliceScalar (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (g j : Ext) (dk : NonzeroRingElements OS) : ℂ :=
  SecondSourceCharacters.commonZero K S g j dk.val *
    idealCoprimeMask (childPuncture C.originalPuncture γ) g.val.val

def slicedColumn (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (G : HeckeCharacter K) (g j I : Ext) (ξ : Sector)
    (dk d₂ : NonzeroRingElements OS) (z : Ext) : ℂ :=
  sourceTerm K S Γ D C.lambda (C.background γ * G⁻¹)
    g j (ActualDivisorSectors.divisorIdeal K S d₂) (newRowIdeal K S I dk d₂)
    (newSector K S Γ D dk d₂ ξ) (childPuncture C.originalPuncture γ)
    (C.survivors γ) C.primeLists C.primeWeights (C.cutoff γ)
    (C.base ^ C.columnLength γ / height K Sset g) z

theorem slicedColumn_eq (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (G : HeckeCharacter K) (g j I : Ext) (ξ : Sector)
    (dk d₂ : NonzeroRingElements OS) (z : Ext) :
    slicedColumn K S Γ D C γ G g j I ξ dk d₂ z =
      childCoefficient K S Γ D C.lambda (C.background γ * G⁻¹) z j I ξ dk d₂ *
        residualWeight K S C γ g z := by
  rw [SecondOverlapColumns.actual_childCoefficient]
  unfold slicedColumn sourceTerm residualWeight
  dsimp only [height, newLabel]
  ring

theorem slicedColumn_zero (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (G : HeckeCharacter K) (g j I : Ext) (ξ : Sector)
    (dk d₂ : NonzeroRingElements OS) (z : Ext) (hc : ¬IsCoprime g.val.val z.val.val) :
    slicedColumn K S Γ D C γ G g j I ξ dk d₂ z = 0 :=
  sourceTerm_zero K S Γ D C.lambda (C.background γ * G⁻¹) g j
    (ActualDivisorSectors.divisorIdeal K S d₂) (newRowIdeal K S I dk d₂)
    (newSector K S Γ D dk d₂ ξ) (childPuncture C.originalPuncture γ)
    (C.survivors γ) C.primeLists C.primeWeights (C.cutoff γ)
    (C.base ^ C.columnLength γ / height K Sset g) z hc

variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
    ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)

include hΓ hallowed in
theorem actual_marked_second_pair (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    {G : HeckeCharacter K} (hcal : ThetaCalibrationInput K Sset D C.lambda G)
    (hbg : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K (C.background γ) p)
    (x₁ x₂ j I : Ext) (hx₁ : Squarefree x₁.val.val) (hx₂ : Squarefree x₂.val.val)
    (ξ : Sector) (dk d₂ : NonzeroRingElements OS) :
    star (DivisorInverseColumn.coefficient K S D C γ j.val.val dk.val x₁) *
      DivisorInverseColumn.coefficient K S D C γ j.val.val dk.val x₂ *
      normalizedDivisorFourier K S D x₁ x₂ d₂.val
        (CanonicalSectors.rowElement K Sset Γ D (I, ξ)).val =
      sliceScalar K S C γ (ActualInverseFactors.common K Sset x₁ x₂) j dk *
        star (slicedColumn K S Γ D C γ G (ActualInverseFactors.common K Sset x₁ x₂)
          j I ξ dk d₂ (ActualInverseFactors.residual K Sset x₁ x₂)) *
        slicedColumn K S Γ D C γ G (ActualInverseFactors.common K Sset x₁ x₂)
          j I ξ dk d₂ (ActualInverseFactors.residual K Sset x₂ x₁) := by
  rw [coefficient_eq, coefficient_eq, slicedColumn_eq, slicedColumn_eq]
  have hp := actual_second_source_pair K S Γ D hΓ hallowed hcal
    (C.background γ) hbg x₁ x₂ j I hx₁ hx₂ ξ dk d₂
  have hw := actual_weight_pair K S C γ x₁ x₂ hx₁ hx₂
  calc
    _ = (star (sourceCoefficient K S D (C.background γ) x₁ j dk.val) *
          sourceCoefficient K S D (C.background γ) x₂ j dk.val *
          normalizedDivisorFourier K S D x₁ x₂ d₂.val
            (CanonicalSectors.rowElement K Sset Γ D (I, ξ)).val) *
        (star (originalWeight K S C γ x₁) * originalWeight K S C γ x₂) := by
      rw [star_mul]
      ring
    _ = _ := by
      rw [hp, hw]
      unfold sliceScalar
      rw [star_mul]
      ring

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondSourceAssembly

end
