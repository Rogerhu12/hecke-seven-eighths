import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstPooledStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstWeightedReduction

/-!
# The actual first block enters the normalized second-stage sources

The coefficients below are computed from the original profile chart and
the actual divisor characters.  The internal divisor pools are the same
ones already used in the first source.  Positive normalization scales
are fixed before the first Fourier variable; weighted AM--GM then acts
on the two original pooled energies under their common Fourier measure.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory UniqueFactorizationMonoid
open HeckePort.Moments HeckePort.Moments.MobiusRegroup

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local instance : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

variable {hΓ μv}
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap V ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {chart : FirstBlockProfileChart (E := E) hΓ μv b C left right profiles finiteTest radius D}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}

namespace FirstBlockPoolData

def originalLeftCoefficient (p : FirstBlockPoolData chart P M X hX) (i : ι) : ℂ :=
  let a := generatedOriginalColumn (σ := σ) hΓ
    (b.leftResidual i) (b.leftGenerator i) (b.left_generates i)
  let r := actualActiveColumn hΓ C b.primes b.primes_injective
    b.leftMultiplicity b.rightMultiplicity
  let δ := (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
  chart.leftCoefficient i * firstLeftDivisorFactor a r δ

def originalRightCoefficient (p : FirstBlockPoolData chart P M X hX) (j : κ) : ℂ :=
  let a := generatedOriginalColumn (σ := σ) hΓ
    (b.rightResidual j) (b.rightGenerator j) (b.right_generates j)
  let r := actualActiveColumn hΓ C b.primes b.primes_injective
    b.leftMultiplicity b.rightMultiplicity
  let δ := (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
  chart.rightCoefficient j * firstRightDivisorFactor a r δ

def linearizedCost (p : FirstBlockPoolData chart P M X hX)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ) : ℝ :=
  firstDivisorLinearizedCost PUnit chart.kernel p.leftData p.rightData p.divisorPools
    (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => (1 : Circle)) p.rowBound
    NL NR p.originalLeftCoefficient p.originalRightCoefficient chart.leftPoint chart.rightPoint

/-- The literal actual first pooled cost is linearized, so every term
is an integral of a genuine normalized main-plus-1/6/7 source. -/
theorem pooledCost_le_linearized (p : FirstBlockPoolData chart P M X hX)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ) :
    p.pooledCost ≤ p.linearizedCost NL NR := by
  exact first_divisor_pool_le_linearized PUnit chart.kernel
    p.leftData p.rightData p.divisorPools
    (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => (1 : Circle))
    p.rowBound p.rowBound_nonneg NL NR hNL hNR
    p.originalLeftCoefficient p.originalRightCoefficient chart.leftPoint chart.rightPoint

theorem kernelCost_le_linearized (p : FirstBlockPoolData chart P M X hX)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ) :
    chart.kernelCost hDiff M X hX ≤ p.linearizedCost NL NR :=
  (p.kernelCost_le_pool hDiff).trans (p.pooledCost_le_linearized NL NR hNL hNR)

end FirstBlockPoolData

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.kernelCost_le_linearized
