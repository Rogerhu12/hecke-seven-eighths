import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondTailBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolGaussDecomposition

/-!
# Column normalization from the literal first Poisson factor

The inverse column norms here are derived from the actual product
modulus in the first Poisson formula.  The primitive chart concerns the
unscaled dual orbital profile at that same modulus-dependent radius.
Its raw coefficients are retained explicitly.  No bound for those raw
coefficients, or for an already transformed source, is asserted here.

The final identity transports this normalization through the one actual
prime-pool residual presentation.  Its numerator contains the original
raw coefficient and the genuine unit phase, with no extra prime norm.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory

variable {K : Type} [Field K] [NumberField K]

section Orbital

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)} [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Q" => SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ

/-- The genuine orbital profile before multiplication by the Poisson
factor.  Its radius is still the actual radius of this precise pair. -/
def ParentPeriodicPair.unscaledTransformedProfile (p : ParentPeriodicPair K S Γ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum OS)) (q : Q) : ℂ :=
  sUnitOrbitalProfile K (S : Set (HeightOneSpectrum (𝓞 K)))
    (sLocalTensorTestFunction K (S : Set (HeightOneSpectrum (𝓞 K)))
      (traceSchwartzFourier K p.profile) (sIntegerFiniteFourierTestFunction K S μv finiteTest))
    ⟨(p.dualRadius radius D).val *
        (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val,
      mul_pos (p.dualRadius radius D).property (sIntegerOrbitNorm K _ Γ q).property⟩

/-- The two column norm inverses are an exact part of the original
Poisson factor; the common modulus remains in the row factor. -/
theorem originalTriple_transformedProfile_column_norms
    (a b r : OrbitalGaussColumn K S Γ) (φ : SchwartzMap V ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum OS)) (q : Q) :
    (a.originalTriple b r φ).transformedProfile μv finiteTest radius D q =
      sIntegerMaskPoissonFactor K S r.modulus r.nonzero radius
          (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D) *
        (((sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
            ⟨a.modulus, a.nonzero⟩).val : ℂ)⁻¹ *
          ((sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
            ⟨b.modulus, b.nonzero⟩).val : ℂ)⁻¹) *
        (a.originalTriple b r φ).unscaledTransformedProfile μv finiteTest radius D q := by
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
  change sIntegerMaskPoissonFactor K S (a.modulus * (b.modulus * r.modulus))
      (mul_ne_zero a.nonzero (mul_ne_zero b.nonzero r.nonzero)) radius
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D) *
      (a.originalTriple b r φ).unscaledTransformedProfile μv finiteTest radius D q = _
  unfold sIntegerMaskPoissonFactor
  rw [hn, Complex.ofReal_mul, Complex.ofReal_mul, mul_inv_rev, mul_inv_rev]
  ring

end Orbital

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

/-- A primitive unscaled-profile chart constructs the existing first
source chart with the actual inverse norm on each column.  The raw
coefficients must still be identified with the original source atoms
and bounded there; this constructor supplies only the genuine Poisson
normalization. -/
def FirstBlockProfileChart.ofUnscaledProfile
    {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
    {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS) (left : Finset ι) (right : Finset κ)
    (profiles : ι → κ → SchwartzMap V ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (F : 𝓢(E, ℂ)) (rawWeight : Q → ℂ) (rawLeft : ι → ℂ) (rawRight : κ → ℂ)
    (x : ι → E) (y : κ → E) (z : Q → E)
    (hprofile : ∀ t : Q, ∀ i ∈ b.leftColumns left, ∀ j ∈ b.rightColumns right,
      IsCoprime (b.leftResidual i).val (b.rightResidual j).val →
      ((generatedOriginalColumn (σ := σ) hΓ (b.leftResidual i) (b.leftGenerator i)
          (b.left_generates i)).originalTriple
        (generatedOriginalColumn (σ := σ) hΓ (b.rightResidual j) (b.rightGenerator j)
          (b.right_generates j))
        (actualActiveColumn hΓ C b.primes b.primes_injective
          b.leftMultiplicity b.rightMultiplicity) (profiles i j)).unscaledTransformedProfile
            μv finiteTest radius D t =
        rawWeight t * (rawLeft i * star (rawRight j)) * F (z t + x i + y j)) :
    FirstBlockProfileChart (E := E) hΓ μv b C left right profiles finiteTest radius D where
  kernel := F
  weight t :=
    sIntegerMaskPoissonFactor K A.Sf
      (firstActiveGenerator C b.primes b.leftMultiplicity b.rightMultiplicity)
      (firstActiveGenerator_generates C b.primes b.leftMultiplicity b.rightMultiplicity).1
      radius (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D) * rawWeight t
  leftCoefficient i := rawLeft i / (A.exteriorNorm (b.leftResidual i) : ℂ)
  rightCoefficient j := rawRight j / (A.exteriorNorm (b.rightResidual j) : ℂ)
  leftPoint := x
  rightPoint := y
  rowPoint := z
  profile t i hi j hj hc := by
    rw [originalTriple_transformedProfile_column_norms, hprofile t i hi j hj hc]
    have hnleft := generates_sIntegerElementNorm (b.leftResidual i) _ (b.left_generates i)
    have hnright := generates_sIntegerElementNorm (b.rightResidual j) _ (b.right_generates j)
    change (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨b.leftGenerator i, (b.left_generates i).1⟩).val = A.exteriorNorm (b.leftResidual i) at hnleft
    change (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨b.rightGenerator j, (b.right_generates j).1⟩).val = A.exteriorNorm (b.rightResidual j) at hnright
    change _ *
        (((sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
          ⟨b.leftGenerator i, (b.left_generates i).1⟩).val : ℂ)⁻¹ *
        ((sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
          ⟨b.rightGenerator j, (b.right_generates j).1⟩).val : ℂ)⁻¹) * _ = _
    rw [hnleft, hnright]
    have hreal : star (A.exteriorNorm (b.rightResidual j) : ℂ) =
        (A.exteriorNorm (b.rightResidual j) : ℂ) := Complex.conj_ofReal _
    dsimp only [actualActiveColumn]
    simp only [div_eq_mul_inv, star_mul, star_inv, hreal]
    ring

end ActualBlock

section Residual

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}

/-- When the input column is the actual inverse-norm first-Poisson
column, its adjusted coefficient is precisely its original numerator. -/
theorem FirstGaussPoolData.adjustedCoefficient_inverseNorm
    (d : FirstGaussPoolData C P ι) (raw : ι → ℂ) (i : ι) :
    d.adjustedCoefficient (fun i => raw i / (A.exteriorNorm (d.ideal i) : ℂ)) i = raw i := by
  have hn : (A.exteriorNorm (d.ideal i) : ℂ) ≠ 0 := by
    exact_mod_cast (A.exteriorNorm_pos (d.ideal i)).ne'
  exact div_mul_cancel₀ _ hn

/-- The exact residual coefficient after removing the actual prime
power.  No prime norm remains in its numerator. -/
theorem FirstGaussPoolData.residualCoefficient_inverseNorm
    (d : FirstGaussPoolData C P ι) (p : ExteriorPrime A) (n : ℕ)
    (raw : ι → ℂ) (i : d.valuationColumns p n) :
    d.residualCoefficient p n (fun i => raw i / (A.exteriorNorm (d.ideal i) : ℂ)) i =
      (raw i.val * (d.residualPresentation p n i).columnPhase) /
        (A.exteriorNorm (d.residualPresentation p n i).residual : ℂ) := by
  unfold FirstGaussPoolData.residualCoefficient
  rw [d.adjustedCoefficient_inverseNorm raw i.val]

/-- The numerator window after the actual residual extraction is the
original raw numerator window: the reciprocal phase has norm one. -/
theorem FirstGaussPoolData.residualCoefficient_inverseNorm_norm
    (d : FirstGaussPoolData C P ι) (p : ExteriorPrime A) (n : ℕ)
    (raw : ι → ℂ) (i : d.valuationColumns p n) :
    ‖d.residualCoefficient p n
      (fun i => raw i / (A.exteriorNorm (d.ideal i) : ℂ)) i‖ =
      ‖raw i.val‖ / A.exteriorNorm (d.residualPresentation p n i).residual := by
  rw [d.residualCoefficient_inverseNorm p n raw i, norm_div, norm_mul,
    (d.residualPresentation p n i).columnPhase_norm, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (A.exteriorNorm_pos _)]

end Residual

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.originalTriple_transformedProfile_column_norms
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockProfileChart.ofUnscaledProfile
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.residualCoefficient_inverseNorm
