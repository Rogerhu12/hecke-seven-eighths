import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLogOrbitalKernel
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstPoissonColumnNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentConstantSource

/-!
# The actual first common profile chart

The same log-radius Schwartz operator is used for every original row
and every original column.  The radius of the literal three-character
source is divided by the two actual column norms.  Its small Mellin
tilt is split exactly between the row and the two columns, while the
two inverse column norms from Poisson are retained by
`FirstBlockProfileChart.ofUnscaledProfile`.

The only analytic input is the original local test, with local
constancy and compact support.  Its Fourier regularity and the
translated common profile identity are constructed here.  Constant
original column coefficients are then inserted by the existing exact
scalar transport, including one whole centered coefficient.
-/

noncomputable section
open scoped Classical NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open DedekindZetaZeroFree

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
open HeckeGeneral.Characters

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalFirstLog

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
variable [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Q" => SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ

/-- The common dual row radius before either column norm is divided out. -/
def rowRadius (r : OrbitalGaussColumn K S Γ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum OS))
    (q : Q) : {r : ℝ // 0 < r} :=
  ⟨(sIntegerMaskDualRadius K S r.modulus r.nonzero radius
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val *
      (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val,
    mul_pos (sIntegerMaskDualRadius K S r.modulus r.nonzero radius
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).property
      (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).property⟩

/-- The literal product modulus gives the exact two-column radius. -/
theorem originalTriple_dualRadius
    (a b r : OrbitalGaussColumn K S Γ) (φ : 𝓢(V, ℂ))
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum OS))
    (q : Q) :
    ((a.originalTriple b r φ).dualRadius radius D).val *
        (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val =
      (rowRadius r radius D q).val /
        ((sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
            ⟨a.modulus, a.nonzero⟩).val *
          (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
            ⟨b.modulus, b.nonzero⟩).val) := by
  have hn :
      (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        ⟨a.modulus * (b.modulus * r.modulus),
          mul_ne_zero a.nonzero (mul_ne_zero b.nonzero r.nonzero)⟩).val =
        (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
          ⟨a.modulus, a.nonzero⟩).val *
        ((sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
          ⟨b.modulus, b.nonzero⟩).val *
         (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
          ⟨r.modulus, r.nonzero⟩).val) := by
    change (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerNonzeroMul K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨a.modulus, a.nonzero⟩
        (sIntegerNonzeroMul K (S : Set (HeightOneSpectrum (𝓞 K)))
          ⟨b.modulus, b.nonzero⟩ ⟨r.modulus, r.nonzero⟩))).val = _
    rw [sIntegerElementNorm_nonzeroMul, sIntegerElementNorm_nonzeroMul]
  dsimp only [ParentPeriodicPair.dualRadius, OrbitalGaussColumn.originalTriple,
    sIntegerMaskDualRadius, rowRadius]
  rw [hn]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (S : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (S : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]

/-- One common Schwartz kernel and an exact identity on every orbital row. -/
theorem originalTriple_unscaled_log_profile
    (a b r : OrbitalGaussColumn K S Γ) (φ : 𝓢(V, ℂ))
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hhat : Continuous (sIntegerFiniteFourierTestFunction K S μv finiteTest))
    (hhatcs : HasCompactSupport (sIntegerFiniteFourierTestFunction K S μv finiteTest))
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum OS))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (q : Q) :
    (a.originalTriple b r φ).unscaledTransformedProfile μv finiteTest radius D q =
      (((rowRadius r radius D q).val ^ (-δ) : ℝ) : ℂ) *
        ((((sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
              ⟨a.modulus, a.nonzero⟩).val ^ δ : ℝ) : ℂ) *
          star (((sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
              ⟨b.modulus, b.nonzero⟩).val ^ δ : ℝ) : ℂ)) *
        (CanonicalLogOrbital.fourierCLM K (S : Set (HeightOneSpectrum (𝓞 K))) Γ
          (sIntegerFiniteFourierTestFunction K S μv finiteTest) hhat hhatcs
          δ hδ hδ1 φ)
          (Real.log (rowRadius r radius D q).val +
            -Real.log (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
              ⟨a.modulus, a.nonzero⟩).val +
            -Real.log (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
              ⟨b.modulus, b.nonzero⟩).val) := by
  let ρ := rowRadius r radius D q
  let na := sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
    ⟨a.modulus, a.nonzero⟩
  let nb := sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
    ⟨b.modulus, b.nonzero⟩
  have hrad :
      (⟨((a.originalTriple b r φ).dualRadius radius D).val *
          (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val,
        mul_pos ((a.originalTriple b r φ).dualRadius radius D).property
          (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).property⟩ :
        {r : ℝ // 0 < r}) =
      ⟨ρ.val / (na.val * nb.val), div_pos ρ.property (mul_pos na.property nb.property)⟩ := by
    apply Subtype.ext
    exact originalTriple_dualRadius a b r φ radius D q
  unfold ParentPeriodicPair.unscaledTransformedProfile
  rw [hrad]
  have he := CanonicalLogOrbital.orbital_at_quotient K
    (S : Set (HeightOneSpectrum (𝓞 K))) Γ
    (sIntegerFiniteFourierTestFunction K S μv finiteTest) hhat hhatcs
    δ hδ hδ1 (traceSchwartzFourier K φ) ρ.val na.val nb.val
    ρ.property na.property nb.property
  simpa only [CanonicalLogOrbital.fourierCLM_apply,
    CanonicalLogOrbital.orbitalCLM_apply, OrbitalGaussColumn.originalTriple,
    Complex.real_smul, Complex.ofReal_mul,
    Complex.star_def, Complex.conj_ofReal, sub_eq_add_neg, mul_assoc, ρ, na, nb] using he

end CanonicalFirstLog

section ActualBlock

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
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- Construct the actual first chart from one original archimedean test.
The source identity is global in the row, and contains the actual
Poisson normalization of both residual columns. -/
def FirstBlockProfileChart.canonicalLog
    {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
    {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS) (left : Finset ι) (right : Finset κ)
    (φ : 𝓢(V, ℂ))
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    FirstBlockProfileChart (E := ℝ) hΓ μv b C left right (fun _ _ => φ)
      finiteTest radius D := by
  let hhat := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport
    K A.Sf ν μv finiteTest hlc hcs
  let r := actualActiveColumn hΓ C b.primes b.primes_injective
    b.leftMultiplicity b.rightMultiplicity
  let ρ := CanonicalFirstLog.rowRadius r radius D
  refine FirstBlockProfileChart.ofUnscaledProfile hΓ μv b C left right
    (fun _ _ => φ) finiteTest radius D
    (CanonicalLogOrbital.fourierCLM K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
      (sIntegerFiniteFourierTestFunction K A.Sf μv finiteTest) hhat.1.continuous hhat.2
      δ hδ hδ1 φ)
    (fun q => (((ρ q).val ^ (-δ) : ℝ) : ℂ))
    (fun i => ((A.exteriorNorm (b.leftResidual i) ^ δ : ℝ) : ℂ))
    (fun j => ((A.exteriorNorm (b.rightResidual j) ^ δ : ℝ) : ℂ))
    (fun i => -Real.log (A.exteriorNorm (b.leftResidual i)))
    (fun j => -Real.log (A.exteriorNorm (b.rightResidual j)))
    (fun q => Real.log (ρ q).val) ?_
  intro q i _ j _ _
  have he := CanonicalFirstLog.originalTriple_unscaled_log_profile μv
    (generatedOriginalColumn (σ := σ) hΓ (b.leftResidual i) (b.leftGenerator i)
      (b.left_generates i))
    (generatedOriginalColumn (σ := σ) hΓ (b.rightResidual j) (b.rightGenerator j)
      (b.right_generates j)) r φ finiteTest hhat.1.continuous hhat.2
    radius D δ hδ hδ1 q
  have hnleft := generates_sIntegerElementNorm (b.leftResidual i) _ (b.left_generates i)
  have hnright := generates_sIntegerElementNorm (b.rightResidual j) _ (b.right_generates j)
  change (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
    ⟨b.leftGenerator i, (b.left_generates i).1⟩).val = A.exteriorNorm (b.leftResidual i) at hnleft
  change (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
    ⟨b.rightGenerator j, (b.right_generates j).1⟩).val = A.exteriorNorm (b.rightResidual j) at hnright
  simpa only [generatedOriginalColumn, hnleft, hnright] using he

/-- The actual constant original coefficients, including the complete
centered difference, are carried by the very same common kernel. -/
def FirstBlockProfileChart.canonicalLogWithCoefficients
    {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
    {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS) (left : Finset ι) (right : Finset κ)
    (φ : 𝓢(V, ℂ)) (c : ι → ℂ) (e : κ → ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    FirstBlockProfileChart (E := ℝ) hΓ μv b C left right
      (fun i j => (c i * star (e j)) • φ) finiteTest radius D :=
  FirstBlockProfileChart.withCoefficients hΓ μv
    (FirstBlockProfileChart.canonicalLog hΓ μv ν b C left right φ finiteTest hlc hcs
      radius D δ hδ hδ1) c e

end ActualBlock

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalFirstLog.originalTriple_dualRadius
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalFirstLog.originalTriple_unscaled_log_profile
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockProfileChart.canonicalLog
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockProfileChart.canonicalLogWithCoefficients
