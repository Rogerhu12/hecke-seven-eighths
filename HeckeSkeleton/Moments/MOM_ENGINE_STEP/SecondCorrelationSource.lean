import HeckeSkeleton.Moments.MOM_ENGINE_STEP.GaussSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstFiniteSource
import HeckeGeneral.Arithmetic.SIntegerModulusNorm

/-!
# The genuine second orbital summand is a full correlation

This connects the pair source of the actual Gauss polynomial to the
complete, nonprimitive finite correlation.  The product modulus is not
replaced by its radical.  Its actual quotient cardinality cancels the
modulus norm in Poisson, leaving exactly the old mask divisor density.
The dual radius, original profile and every original unit sector remain
in the resulting summand.  No summed transform calibration is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments HeckePort.Moments.CommonSupport
open UniqueFactorizationMonoid MeasureTheory

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "Q" => SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- The fixed field factor in the actual adelic Poisson formula. -/
def orbitalFieldFactor : ℝ :=
  (2 : ℝ) ^ InfinitePlace.nrComplexPlaces K / Real.sqrt |(discr K : ℝ)|

theorem orbitalFieldFactor_nonneg : 0 ≤ orbitalFieldFactor K := by
  exact div_nonneg (by positivity) (Real.sqrt_nonneg _)

variable {K S Γ}

/-- The complete correlation of the two original full quotient characters. -/
def OrbitalGaussColumn.correlation (c d : OrbitalGaussColumn K S Γ) (j : OS) : ℂ := by
  letI := finite_sIntegerPrincipalResidue K (S : Set _) c.modulus c.nonzero
  letI := finite_sIntegerPrincipalResidue K (S : Set _) d.modulus d.nonzero
  letI := Fintype.ofFinite (OS ⧸ Ideal.span ({c.modulus} : Set OS))
  letI := Fintype.ofFinite (OS ⧸ Ideal.span ({d.modulus} : Set OS))
  exact fullModulusCorrelation c.modulus d.modulus c.character d.character j

def OrbitalGaussColumn.divisorPhase (c : OrbitalGaussColumn K S Γ) (δ : OS) : ℂ :=
  c.character⁻¹ (Ideal.Quotient.mk _ δ)

/-- The exact divisor Fourier coefficient of the actual pair source.
The mask divisor may be a nonunit in the S-integer ring. -/
theorem OrbitalGaussColumn.pair_divisor_fourier
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (c d : OrbitalGaussColumn K S Γ) (φ : SchwartzMap V ℂ)
    (δ j : OS) (hcδ : IsCoprime c.modulus δ) (hdδ : IsCoprime d.modulus δ) :
    sIntegerPeriodicDivisorFourier K (S : Set _) hS
        (c.pair hS d φ).modulus (c.pair hS d φ).modulus_ne_zero
        (c.pair hS d φ).residue δ (Ideal.Quotient.mk _ j) =
      (c.divisorPhase δ * star (d.divisorPhase δ)) *
        ((Nat.card (OS ⧸ Ideal.span ({c.modulus * d.modulus} : Set OS)) : ℂ) *
          c.correlation d (-j)) := by
  have h := actual_gauss_pair_divisor_transform K (S : Set _) hS
    c.modulus d.modulus c.nonzero d.nonzero c.character d.character δ j hcδ hdδ
  letI := finite_sIntegerPrincipalResidue K (S : Set _) c.modulus c.nonzero
  letI := finite_sIntegerPrincipalResidue K (S : Set _) d.modulus d.nonzero
  letI := finite_sIntegerPrincipalResidue K (S : Set _)
    (c.modulus * d.modulus) (mul_ne_zero c.nonzero d.nonzero)
  letI := Fintype.ofFinite (OS ⧸ Ideal.span ({c.modulus} : Set OS))
  letI := Fintype.ofFinite (OS ⧸ Ideal.span ({d.modulus} : Set OS))
  letI := Fintype.ofFinite (OS ⧸ Ideal.span ({c.modulus * d.modulus} : Set OS))
  simpa only [OrbitalGaussColumn.pair, OrbitalGaussColumn.residue,
    OrbitalGaussColumn.divisorPhase, OrbitalGaussColumn.correlation,
    completeGaussPair, Nat.card_eq_fintype_card] using h

variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

/-- Quotient cardinality and product norm cancel exactly.  In particular
there is no residual column-count or modulus-density factor to charge. -/
theorem maskPoissonFactor_mul_card (a : OS) (ha : a ≠ 0)
    (r : {r : ℝ // 0 < r}) (δ : NonzeroRingElements OS) :
    sIntegerMaskPoissonFactor K S a ha r δ *
        (Nat.card (OS ⧸ Ideal.span ({a} : Set OS)) : ℂ) =
      ((r.val * (sIntegerElementNorm K (S : Set _) δ).val : ℝ) : ℂ)⁻¹ *
        (orbitalFieldFactor K : ℂ) := by
  have hcard := natCard_sIntegerPrincipalResidue_eq_productNorm
    K (S : Set (HeightOneSpectrum (𝓞 K))) a ha
  have hc : (Nat.card (OS ⧸ Ideal.span ({a} : Set OS)) : ℂ) =
      ((sIntegerElementNorm K (S : Set _) ⟨a, ha⟩).val : ℂ) := by
    exact_mod_cast hcard
  rw [hc]
  unfold sIntegerMaskPoissonFactor sIntegerMaskDilationRadius orbitalFieldFactor
  have hn : ((sIntegerElementNorm K (S : Set _) ⟨a, ha⟩).val : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (sIntegerElementNorm K (S : Set _) ⟨a, ha⟩).property)
  rw [mul_assoc, inv_mul_cancel₀ hn, mul_one]

/-- The second-transform scalar after exact cardinality cancellation. -/
def secondOrbitalScalar (r : {r : ℝ // 0 < r})
    (D : Finset (HeightOneSpectrum OS)) : ℂ :=
  (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
    (((r.val * (sIntegerElementNorm K (S : Set _)
      (sIntegerMaskGenerator K (S : Set _) D)).val) : ℝ) : ℂ)⁻¹ *
      (orbitalFieldFactor K : ℂ)

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [Γ.FiniteIndex]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- The original Fourier profile at the pair's true dual radius. -/
def OrbitalGaussColumn.secondProfile
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (c d : OrbitalGaussColumn K S Γ) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (r : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum OS)) (q : Q) : ℂ :=
  let ρ := (c.pair hS d φ).dualRadius r D
  sUnitOrbitalProfile K (S : Set (HeightOneSpectrum (𝓞 K)))
    (sLocalTensorTestFunction K (S : Set (HeightOneSpectrum (𝓞 K)))
      (traceSchwartzFourier K φ) (sIntegerFiniteFourierTestFunction K S μv h))
    ⟨ρ.val * (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val,
      mul_pos ρ.property (sIntegerOrbitNorm K (S : Set _) Γ q).property⟩

/-- The actual finite nonzero orbital summand is the complete correlation
at the negative frequency.  All masks, phases and original profiles are
visible, and the true cardinality cancellation is already performed. -/
theorem OrbitalGaussColumn.transformedRow_mk
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (c d : OrbitalGaussColumn K S Γ) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (r : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum OS))
    (hcD : IsCoprime c.modulus (sIntegerMaskGenerator K (S : Set _) D).val)
    (hdD : IsCoprime d.modulus (sIntegerMaskGenerator K (S : Set _) D).val)
    (j : NonzeroRingElements OS) :
    (c.pair hS d φ).transformedRow μv hS h r D (Quotient.mk _ j) =
      secondOrbitalScalar r D *
        (c.divisorPhase (sIntegerMaskGenerator K (S : Set _) D).val *
          star (d.divisorPhase (sIntegerMaskGenerator K (S : Set _) D).val)) *
        c.correlation d (-j.val) *
        c.secondProfile μv hS d φ h r D (Quotient.mk _ j) := by
  unfold ParentPeriodicPair.transformedRow sIntegerPeriodicFourierProfileTerm
  rw [sIntegerPeriodicFourierOrbitWeight_mk, c.pair_divisor_fourier hS d φ
    (sIntegerMaskGenerator K (S : Set _) D).val j.val hcD hdD]
  change (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
    sIntegerMaskPoissonFactor K S (c.modulus * d.modulus)
      (mul_ne_zero c.nonzero d.nonzero) r (sIntegerMaskGenerator K (S : Set _) D) *
    ((c.divisorPhase (sIntegerMaskGenerator K (S : Set _) D).val *
      star (d.divisorPhase (sIntegerMaskGenerator K (S : Set _) D).val)) *
      ((Nat.card (OS ⧸ Ideal.span ({c.modulus * d.modulus} : Set OS)) : ℂ) *
        c.correlation d (-j.val)) *
      c.secondProfile μv hS d φ h r D (Quotient.mk _ j)) = _
  have hc := maskPoissonFactor_mul_card (c.modulus * d.modulus)
    (mul_ne_zero c.nonzero d.nonzero) r (sIntegerMaskGenerator K (S : Set _) D)
  unfold secondOrbitalScalar
  calc
    _ = (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
      (sIntegerMaskPoissonFactor K S (c.modulus * d.modulus)
        (mul_ne_zero c.nonzero d.nonzero) r (sIntegerMaskGenerator K (S : Set _) D) *
        (Nat.card (OS ⧸ Ideal.span ({c.modulus * d.modulus} : Set OS)) : ℂ)) *
      (c.divisorPhase (sIntegerMaskGenerator K (S : Set _) D).val *
        star (d.divisorPhase (sIntegerMaskGenerator K (S : Set _) D).val)) *
      c.correlation d (-j.val) *
      c.secondProfile μv hS d φ h r D (Quotient.mk _ j) := by ring
    _ = _ := by rw [hc]; ring

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.maskPoissonFactor_mul_card
#print axioms HeckeSkeleton.Moments.EngineStep.OrbitalGaussColumn.transformedRow_mk
