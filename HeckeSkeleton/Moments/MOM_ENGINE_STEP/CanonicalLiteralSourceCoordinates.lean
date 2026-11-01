import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstRowGeometry
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.UnrestrictedSixthCapacity
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFirstPhase

/-!
# Original coordinates before and after the second transform

The first common ideals and the selected physical divisor determine the
retained first-row endpoint before any second common factor is known.
The original second pattern subsequently fills only the four second
ideal coordinates. In particular the retained scale, enlargement and
first allowance are unchanged by that operation.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.LocalFiniteSums (ExteriorPrime)
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments CommonSupportMass

variable {K : Type} [Field K] [NumberField K]

namespace OriginalNominalIdeals

/-- First-source coordinates with neutral second coordinates. This
record is used only to select the first row endpoint and enlargement. -/
def firstCoordinates (first opposite complementary : (Ideal (𝓞 K))⁰) :
    OriginalNominalIdeals K where
  first := first
  opposite := opposite
  complementary := complementary
  second := 1
  secondOpposite := 1
  unitPart := 1
  nonunitPart := 1
  unit_dvd_gcd := one_dvd _

end OriginalNominalIdeals

variable {A : SArithmeticData K} [IsPrincipalIdealRing A.R]
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

namespace FirstCommonCharacterBlock

variable (b : FirstCommonCharacterBlock fullI fullJ DE)

def literalLeftCoordinates (D : Finset (HeightOneSpectrum A.R)) :
    OriginalNominalIdeals K :=
  OriginalNominalIdeals.firstCoordinates
    ⟨(primePowerProduct b.primes b.leftMultiplicity).val,
      mem_nonZeroDivisors_of_ne_zero (primePowerProduct b.primes b.leftMultiplicity).property.1⟩
    ⟨(primePowerProduct b.primes b.rightMultiplicity).val,
      mem_nonZeroDivisors_of_ne_zero (primePowerProduct b.primes b.rightMultiplicity).property.1⟩
    ⟨(firstPhysicalDivisorIdeal D).val,
      mem_nonZeroDivisors_of_ne_zero (firstPhysicalDivisorIdeal D).property.1⟩

def literalRightCoordinates (D : Finset (HeightOneSpectrum A.R)) :
    OriginalNominalIdeals K :=
  OriginalNominalIdeals.firstCoordinates
    (b.literalLeftCoordinates D).opposite
    (b.literalLeftCoordinates D).first
    (b.literalLeftCoordinates D).complementary

@[simp] theorem literalLeftCoordinates_first (D : Finset (HeightOneSpectrum A.R)) :
    (b.literalLeftCoordinates D).first.val = DE.1 := b.common_left

@[simp] theorem literalLeftCoordinates_opposite (D : Finset (HeightOneSpectrum A.R)) :
    (b.literalLeftCoordinates D).opposite.val = DE.2 := b.common_right

@[simp] theorem literalRightCoordinates_first (D : Finset (HeightOneSpectrum A.R)) :
    (b.literalRightCoordinates D).first.val = DE.2 := b.common_right

@[simp] theorem literalRightCoordinates_opposite (D : Finset (HeightOneSpectrum A.R)) :
    (b.literalRightCoordinates D).opposite.val = DE.1 := b.common_left

@[simp] theorem literalLeftCoordinates_complementary (D : Finset (HeightOneSpectrum A.R)) :
    (b.literalLeftCoordinates D).complementary.val = (firstPhysicalDivisorIdeal D).val := rfl

@[simp] theorem literalRightCoordinates_complementary (D : Finset (HeightOneSpectrum A.R)) :
    (b.literalRightCoordinates D).complementary.val = (firstPhysicalDivisorIdeal D).val := rfl

theorem literalRightCoordinates_firstFrequency
    (D : Finset (HeightOneSpectrum A.R)) (a : RealParameters) (Z : ℝ) :
    (b.literalRightCoordinates D).firstFrequency a Z =
      (b.literalLeftCoordinates D).firstFrequency a Z := by
  simp only [OriginalNominalIdeals.firstFrequency,
    b.literalLeftCoordinates_first, b.literalLeftCoordinates_opposite,
    b.literalRightCoordinates_first, b.literalRightCoordinates_opposite,
    b.literalLeftCoordinates_complementary, b.literalRightCoordinates_complementary,
    firstActiveRadical_swap_of_support DE.1 DE.2 b.common_support_eq]
  ring

/-- The actual fixed first phase needs no chosen ideal or generator
identity from the caller. -/
def literalLeftFixed (D : Finset (HeightOneSpectrum A.R)) : A.Exterior :=
  CanonicalLiteralFirstPhase.leftIdeal b.primes b.leftMultiplicity b.rightMultiplicity
    (firstPhysicalDivisorIdeal D)

def literalRightFixed (D : Finset (HeightOneSpectrum A.R)) : A.Exterior :=
  CanonicalLiteralFirstPhase.rightIdeal b.primes b.leftMultiplicity b.rightMultiplicity
    (firstPhysicalDivisorIdeal D)

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}

theorem literalLeftFixed_generates (C : A.GeneralArithmeticContext σ η hS)
    (D : Finset (HeightOneSpectrum A.R)) :
    A.Generates (b.literalLeftFixed D)
      (CanonicalLiteralFirstPhase.leftElement C b.primes b.leftMultiplicity
        b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) :=
  CanonicalLiteralFirstPhase.leftElement_generates C b.primes b.leftMultiplicity
    b.rightMultiplicity (firstPhysicalDivisorIdeal D) _
    (originalFrequencyIdeal_generates _
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).property)

theorem literalRightFixed_generates (C : A.GeneralArithmeticContext σ η hS)
    (D : Finset (HeightOneSpectrum A.R)) :
    A.Generates (b.literalRightFixed D)
      (CanonicalLiteralFirstPhase.rightElement C b.primes b.leftMultiplicity
        b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) :=
  CanonicalLiteralFirstPhase.rightElement_generates C b.primes b.leftMultiplicity
    b.rightMultiplicity (firstPhysicalDivisorIdeal D) _
    (originalFrequencyIdeal_generates _
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).property)

end FirstCommonCharacterBlock

namespace OriginalNominalGeometry

variable {a : RealParameters} {Z step : ℝ}
variable (G : OriginalNominalGeometry (K := K) a Z step)
variable {j : Type*} [Fintype j] [DecidableEq j]
variable (p : j → ExteriorPrime A) (m n : j → ℕ)
variable (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (pattern : j → Bool)

/-- Fill the original second common and frequency-pattern coordinates.
No endpoint, width, or capacity is reselected. -/
def atSecondPattern : OriginalNominalGeometry (K := K) a Z step where
  ideals := OriginalNominalIdeals.ofSecondPattern
    G.ideals.first G.ideals.opposite G.ideals.complementary p m n hm hn pattern
  tag := G.tag
  retainedScale := G.retainedScale
  retainedScale_pos := G.retainedScale_pos
  supportError := G.supportError
  supportError_nonneg := G.supportError_nonneg
  retained_upper := G.retained_upper
  error_prime_lower := G.error_prime_lower

@[simp] theorem atSecondPattern_retainedScale :
    (G.atSecondPattern p m n hm hn pattern).retainedScale = G.retainedScale := rfl

@[simp] theorem atSecondPattern_enlargement :
    (G.atSecondPattern p m n hm hn pattern).enlargement = G.enlargement := rfl

@[simp] theorem atSecondPattern_first :
    (G.atSecondPattern p m n hm hn pattern).ideals.first = G.ideals.first := rfl

@[simp] theorem atSecondPattern_opposite :
    (G.atSecondPattern p m n hm hn pattern).ideals.opposite = G.ideals.opposite := rfl

@[simp] theorem atSecondPattern_complementary :
    (G.atSecondPattern p m n hm hn pattern).ideals.complementary = G.ideals.complementary := rfl

@[simp] theorem atSecondPattern_tag :
    (G.atSecondPattern p m n hm hn pattern).tag = G.tag := rfl

@[simp] theorem atSecondPattern_second :
    (G.atSecondPattern p m n hm hn pattern).ideals.second.val =
      (primePowerProduct p m).val := rfl

@[simp] theorem atSecondPattern_secondOpposite :
    (G.atSecondPattern p m n hm hn pattern).ideals.secondOpposite.val =
      (primePowerProduct p n).val := rfl

@[simp] theorem atSecondPattern_unitPart :
    (G.atSecondPattern p m n hm hn pattern).ideals.unitPart.val =
      (secondPatternUnitIdeal p m n pattern).val := rfl

@[simp] theorem atSecondPattern_nonunitPart :
    (G.atSecondPattern p m n hm hn pattern).ideals.nonunitPart.val =
      (secondPatternNonunitIdeal p pattern).val := rfl

@[simp] theorem atSecondPattern_boundary :
    (G.atSecondPattern p m n hm hn pattern).boundary = G.boundary := rfl

@[simp] theorem atSecondPattern_frequencyCenter :
    (G.atSecondPattern p m n hm hn pattern).frequencyCenter = G.frequencyCenter := rfl

@[simp] theorem atSecondPattern_supportCenter :
    (G.atSecondPattern p m n hm hn pattern).supportCenter = G.supportCenter := rfl

end OriginalNominalGeometry
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.literalRightCoordinates_firstFrequency
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.literalLeftFixed_generates
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.literalRightFixed_generates
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.atSecondPattern
