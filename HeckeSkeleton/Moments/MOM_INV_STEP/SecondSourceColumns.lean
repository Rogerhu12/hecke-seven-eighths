import HeckeSkeleton.Moments.MOM_INV_STEP.SecondSourceCharacters

/-!
# The actual second source returns the literal forward child

The left side is the inverse-oriented pair of the original μν
coefficients, its retained first divisor and old fourth-power label,
multiplied by the actual normalized divisor Fourier transform. The
fresh common and residual ideals are computed from those source columns.

The result has a₀νG⁻¹ on each residual column, the label j d₂ and the
row d₂ dₖ k, with the exact original-sector translation. All common
coprimality zeros are retained. No source-to-child identity or arbitrary
coefficient on the moving residual column is assumed.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondSourceColumns

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open FirstInversePoisson PrimitivePoissonSource PrimitiveFourier ConductorMasks
  CanonicalSectorRows ActualDivisorSectors SecondSourceCharacters
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
local notation "e" => unitIdeal K S

def normalizedDivisorFourier (x₁ x₂ : Ext) (d a : OS) : ℂ :=
  sIntegerPeriodicDivisorFourier K Sset D.different_outside
    (primitiveModulus K S D (pairSupport K S D x₁ x₂ e e) (pairExponent K S x₁ x₂ e e))
    (primitiveModulus_ne_zero K S D (pairSupport K S D x₁ x₂ e e)
      (pairExponent K S x₁ x₂ e e))
    (primitiveCoefficient K S D (pairSupport K S D x₁ x₂ e e)
      (pairExponent K S x₁ x₂ e e)) d (Ideal.Quotient.mk _ a) /
    (Real.sqrt ((primitiveIdeal (pairSupport K S D x₁ x₂ e e).support
      (pairExponent K S x₁ x₂ e e)).absNorm : ℝ) : ℂ)

theorem normalized_divisor_fourier_split (x₁ x₂ : Ext) (d a : OS) :
    normalizedDivisorFourier K S D x₁ x₂ d a =
      (idealSymbol K Sset D (ActualInverseFactors.residual K Sset x₁ x₂) d *
        star (idealSymbol K Sset D (ActualInverseFactors.residual K Sset x₂ x₁) d)) *
      (star (idealSymbol K Sset D (ActualInverseFactors.residual K Sset x₁ x₂) a) *
        idealSymbol K Sset D (ActualInverseFactors.residual K Sset x₂ x₁) a) *
      normalizedPrimitiveGauss K S D (pairSupport K S D x₁ x₂ e e)
        (pairExponent K S x₁ x₂ e e) := by
  unfold normalizedDivisorFourier
  rw [divisor_fourier_split]
  simp only [normalizedPrimitiveGauss, div_eq_mul_inv]
  ring

def sourceCoefficient (ν : HeckeCharacter K) (x j : Ext) (dk : OS) : ℂ :=
  ((moebius x.val.val : ℂ) * heckeIdealCoefficient K ν x.val) *
    decoration K S D x j dk

def newLabel (j : Ext) (d₂ : NonzeroRingElements OS) : Ext :=
  exteriorMul K Sset j (divisorIdeal K S d₂)

def newRowIdeal (I : Ext) (dk d₂ : NonzeroRingElements OS) : Ext :=
  exteriorMul K Sset (divisorIdeal K S d₂)
    (exteriorMul K Sset (divisorIdeal K S dk) I)

def newSector (dk d₂ : NonzeroRingElements OS) (ξ : Sector) : Sector :=
  divisorTransport K S Γ D d₂ (directDivisorTransport K S Γ D dk ξ)

def childDecoration (n j I : Ext) (ξ : Sector) (dk d₂ : NonzeroRingElements OS) : ℂ :=
  idealSymbol K Sset D n (D.generator (newLabel K S j d₂)) ^ 4 *
    sectorCharacter K S Γ D n (newRowIdeal K S I dk d₂) (newSector K S Γ D dk d₂ ξ)

def childCoefficient (Λ ν : HeckeCharacter K) (n j I : Ext) (ξ : Sector)
    (dk d₂ : NonzeroRingElements OS) : ℂ :=
  (CoefficientCycle.canonicalCoefficient K Sset D Λ n *
    heckeIdealCoefficient K ν n.val) * childDecoration K S Γ D n j I ξ dk d₂

variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
    ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)

include hΓ hallowed in
theorem residual_rows_return_forward (z₁ z₂ j I : Ext) (ξ : Sector)
    (dk d₂ : NonzeroRingElements OS) :
    (star (decoration K S D z₁ j dk.val) * decoration K S D z₂ j dk.val) *
      (idealSymbol K Sset D z₁ d₂.val * star (idealSymbol K Sset D z₂ d₂.val)) *
      (star (sectorCharacter K S Γ D z₁ I ξ) * sectorCharacter K S Γ D z₂ I ξ) =
      star (childDecoration K S Γ D z₁ j I ξ dk d₂) *
        childDecoration K S Γ D z₂ j I ξ dk d₂ := by
  calc
    _ = (idealSymbol K Sset D z₁ d₂.val *
          star (idealSymbol K Sset D z₁ dk.val *
            idealSymbol K Sset D z₁ (D.generator j) ^ 4 *
              sectorCharacter K S Γ D z₁ I ξ)) *
        star (idealSymbol K Sset D z₂ d₂.val *
          star (idealSymbol K Sset D z₂ dk.val *
            idealSymbol K Sset D z₂ (D.generator j) ^ 4 *
              sectorCharacter K S Γ D z₂ I ξ)) := by
      simp only [decoration, star_mul, star_star]
      ring
    _ = _ := by
      rw [actual_two_divisors K S Γ D hΓ hallowed z₁ j I ξ dk d₂,
        actual_two_divisors K S Γ D hΓ hallowed z₂ j I ξ dk d₂, star_star]
      rfl

include hΓ hallowed in
/-- The actual second Fourier summand becomes the two literal forward
columns. The common-label and common-divisor zeros stay outside as
computed source factors; every residual character is inside its child. -/
theorem actual_second_source_pair {Λ G : HeckeCharacter K}
    (hcal : ThetaCalibrationInput K Sset D Λ G) (ν : HeckeCharacter K)
    (hν : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K ν p)
    (x₁ x₂ j I : Ext) (hx₁ : Squarefree x₁.val.val) (hx₂ : Squarefree x₂.val.val)
    (ξ : Sector) (dk d₂ : NonzeroRingElements OS) :
    star (sourceCoefficient K S D ν x₁ j dk.val) *
      sourceCoefficient K S D ν x₂ j dk.val *
      normalizedDivisorFourier K S D x₁ x₂ d₂.val
        (CanonicalSectors.rowElement K Sset Γ D (I, ξ)).val =
      commonZero K S (ActualInverseFactors.common K Sset x₁ x₂) j dk.val *
        star (childCoefficient K S Γ D Λ (ν * G⁻¹)
          (ActualInverseFactors.residual K Sset x₁ x₂) j I ξ dk d₂) *
        childCoefficient K S Γ D Λ (ν * G⁻¹)
          (ActualInverseFactors.residual K Sset x₂ x₁) j I ξ dk d₂ := by
  let z₁ := ActualInverseFactors.residual K Sset x₁ x₂
  let z₂ := ActualInverseFactors.residual K Sset x₂ x₁
  let b₁ := CoefficientCycle.canonicalCoefficient K Sset D Λ z₁ *
    heckeIdealCoefficient K (ν * G⁻¹) z₁.val
  let b₂ := CoefficientCycle.canonicalCoefficient K Sset D Λ z₂ *
    heckeIdealCoefficient K (ν * G⁻¹) z₂.val
  let c := commonZero K S (ActualInverseFactors.common K Sset x₁ x₂) j dk.val
  have hbase :
      star ((moebius x₁.val.val : ℂ) * heckeIdealCoefficient K ν x₁.val) *
        ((moebius x₂.val.val : ℂ) * heckeIdealCoefficient K ν x₂.val) *
        normalizedPrimitiveGauss K S D (pairSupport K S D x₁ x₂ e e)
          (pairExponent K S x₁ x₂ e e) = star b₁ * b₂ :=
    SecondSourceGauss.inverse_pair_returns_canonical K S D hallowed hcal ν hν x₁ x₂ hx₁ hx₂
  have hdec := actual_pair_decorations K S D x₁ x₂ j dk.val hx₁ hx₂
  calc
    _ = (star ((moebius x₁.val.val : ℂ) * heckeIdealCoefficient K ν x₁.val) *
          ((moebius x₂.val.val : ℂ) * heckeIdealCoefficient K ν x₂.val) *
          normalizedPrimitiveGauss K S D (pairSupport K S D x₁ x₂ e e)
            (pairExponent K S x₁ x₂ e e)) *
        (star (decoration K S D x₁ j dk.val) * decoration K S D x₂ j dk.val) *
        (idealSymbol K Sset D z₁ d₂.val * star (idealSymbol K Sset D z₂ d₂.val)) *
        (star (sectorCharacter K S Γ D z₁ I ξ) * sectorCharacter K S Γ D z₂ I ξ) := by
      rw [normalized_divisor_fourier_split]
      simp only [sourceCoefficient, star_mul, z₁, z₂, sectorCharacter]
      ring
    _ = c * (star b₁ * b₂) *
        ((star (decoration K S D z₁ j dk.val) * decoration K S D z₂ j dk.val) *
          (idealSymbol K Sset D z₁ d₂.val * star (idealSymbol K Sset D z₂ d₂.val)) *
          (star (sectorCharacter K S Γ D z₁ I ξ) * sectorCharacter K S Γ D z₂ I ξ)) := by
      rw [hbase, hdec]
      dsimp only [c, z₁, z₂]
      ring
    _ = c * (star b₁ * b₂) *
        (star (childDecoration K S Γ D z₁ j I ξ dk d₂) *
          childDecoration K S Γ D z₂ j I ξ dk d₂) := by
      rw [residual_rows_return_forward K S Γ D hΓ hallowed]
    _ = _ := by
      simp only [childCoefficient, star_mul, b₁, b₂, c, z₁, z₂]
      ring

include hΓ in
theorem normalizedFourier_actual_sector (x₁ x₂ : Ext) (d : OS)
    (k : NonzeroRingElements OS) :
    normalizedDivisorFourier K S D x₁ x₂ d k.val =
      normalizedDivisorFourier K S D x₁ x₂ d
        (CanonicalSectors.rowElement K Sset Γ D
          (divisorIdeal K S k, frequencySector K S Γ D k)).val := by
  simp only [normalized_divisor_fourier_split]
  rw [← sectorCharacter_actual_frequency K S Γ D hΓ
      (ActualInverseFactors.residual K Sset x₁ x₂) k,
    ← sectorCharacter_actual_frequency K S Γ D hΓ
      (ActualInverseFactors.residual K Sset x₂ x₁) k]
  rfl

include hΓ hallowed in
/-- Every nonzero frequency in the real second Poisson series is
covered, with its own computed ideal and original unit sector. -/
theorem actual_second_source_at_frequency {Λ G : HeckeCharacter K}
    (hcal : ThetaCalibrationInput K Sset D Λ G) (ν : HeckeCharacter K)
    (hν : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K ν p)
    (x₁ x₂ j : Ext) (hx₁ : Squarefree x₁.val.val) (hx₂ : Squarefree x₂.val.val)
    (dk d₂ k : NonzeroRingElements OS) :
    star (sourceCoefficient K S D ν x₁ j dk.val) *
      sourceCoefficient K S D ν x₂ j dk.val *
      normalizedDivisorFourier K S D x₁ x₂ d₂.val k.val =
      commonZero K S (ActualInverseFactors.common K Sset x₁ x₂) j dk.val *
        star (childCoefficient K S Γ D Λ (ν * G⁻¹)
          (ActualInverseFactors.residual K Sset x₁ x₂) j (divisorIdeal K S k)
          (frequencySector K S Γ D k) dk d₂) *
        childCoefficient K S Γ D Λ (ν * G⁻¹)
          (ActualInverseFactors.residual K Sset x₂ x₁) j (divisorIdeal K S k)
          (frequencySector K S Γ D k) dk d₂ := by
  rw [normalizedFourier_actual_sector K S Γ D hΓ]
  exact actual_second_source_pair K S Γ D hΓ hallowed hcal ν hν x₁ x₂ j
    (divisorIdeal K S k) hx₁ hx₂ (frequencySector K S Γ D k) dk d₂

/-- The returned ideal row has exactly the required first powers of
both actual mask divisors. -/
theorem newRowIdeal_val (I : Ext) (dk d₂ : NonzeroRingElements OS) :
    (newRowIdeal K S I dk d₂).val.val =
      (divisorIdeal K S dk).val.val * (divisorIdeal K S d₂).val.val * I.val.val := by
  change (divisorIdeal K S d₂).val.val * ((divisorIdeal K S dk).val.val * I.val.val) = _
  ring

/-- The actual nonzero output row has the exact product norm used by
the reconstruction fiber bound; no divisor power is lost. -/
theorem actual_new_row_norm (dk d₂ k : NonzeroRingElements OS) :
    ((newRowIdeal K S (divisorIdeal K S k) dk d₂).val.val.absNorm : ℝ) =
      (sIntegerElementNorm K Sset dk).val * (sIntegerElementNorm K Sset d₂).val *
        (sIntegerElementNorm K Sset k).val := by
  rw [newRowIdeal_val, map_mul, map_mul, Nat.cast_mul, Nat.cast_mul,
    divisorIdeal_norm, divisorIdeal_norm, divisorIdeal_norm]

theorem child_label_squarefree (x₁ x₂ j : Ext) (hj : Squarefree j.val.val)
    (dk d₂ : NonzeroRingElements OS)
    (hd₂ : (divisorIdeal K S d₂).val.val ∣ (ActualInverseFactors.common K Sset x₁ x₂).val.val)
    (hlive : commonZero K S (ActualInverseFactors.common K Sset x₁ x₂) j dk.val ≠ 0) :
    Squarefree (newLabel K S j d₂).val.val :=
  second_label_squarefree K S x₁ x₂ j dk.val hj (divisorIdeal K S d₂).val.val hd₂ hlive

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondSourceColumns

end
