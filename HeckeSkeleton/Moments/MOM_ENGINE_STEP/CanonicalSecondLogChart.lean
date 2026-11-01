import HeckeSkeleton.Moments.MOM_ENGINE_STEP.GaussStagePhaseTransport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondTailBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLogOrbitalKernel
import HeckeGeneral.Bridge.TraceSchwartzFourierBounds

/-!
# The common logarithmic chart of the actual second transform

The pair modulus is the product of the two original Gauss moduli.
Its norm is split before the logarithmic kernel is evaluated.  The
row radius retains the original mask divisor and every original orbit.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalSecondLogChart

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory

variable {K : Type} [Field K] [NumberField K]

section Orbital

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}

/-- The original arithmetic norm of one actual Gauss modulus. -/
def columnNorm (c : OrbitalGaussColumn K S Γ) : ℝ :=
  (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
    ⟨c.modulus, c.nonzero⟩).val

theorem columnNorm_pos (c : OrbitalGaussColumn K S Γ) : 0 < columnNorm c :=
  (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
    ⟨c.modulus, c.nonzero⟩).property

theorem pair_modulus_norm (c d : OrbitalGaussColumn K S Γ) :
    (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
      ⟨c.modulus * d.modulus, mul_ne_zero c.nonzero d.nonzero⟩).val =
        columnNorm c * columnNorm d := by
  change (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
    (sIntegerNonzeroMul K (S : Set (HeightOneSpectrum (𝓞 K)))
      ⟨c.modulus, c.nonzero⟩ ⟨d.modulus, d.nonzero⟩)).val = _
  exact sIntegerElementNorm_nonzeroMul K (S : Set (HeightOneSpectrum (𝓞 K))) _ _

variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

/-- Only the original row and mask occur in this radius.  The two column
norms remain separate, and no orbit class or physical cutoff is used. -/
def rowRadius (r : {r : ℝ // 0 < r})
    (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)))
    (q : SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ) : {ρ : ℝ // 0 < ρ} :=
  ⟨(sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val /
    (r.val * (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val),
    div_pos (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).property
      (mul_pos r.property (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).property)⟩

/-- The actual dual profile radius, with the full product modulus. -/
theorem pair_dualRadius_mul_orbitNorm
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (c d : OrbitalGaussColumn K S Γ)
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (r : {r : ℝ // 0 < r})
    (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)))
    (q : SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    ((c.pair hDiff d φ).dualRadius r D).val *
      (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val =
        (rowRadius r D q).val / (columnNorm c * columnNorm d) := by
  change ((r.val * (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val) *
    (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
      ⟨c.modulus * d.modulus, mul_ne_zero c.nonzero d.nonzero⟩).val)⁻¹ *
        (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val =
    ((sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val /
      (r.val * (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val)) /
      (columnNorm c * columnNorm d)
  rw [pair_modulus_norm]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Real tilt powers preserve the original complex coefficients and
their conjugation.  This is an equality before any norm or Cauchy bound. -/
theorem coefficient_split (ρ a b δ : ℝ) (l r z : ℂ) :
    (l * star r) * (((ρ ^ (-δ) * a ^ δ * b ^ δ : ℝ) : ℂ) * z) =
      ((ρ ^ (-δ) : ℝ) : ℂ) *
        ((l * ((a ^ δ : ℝ) : ℂ)) * star (r * ((b ^ δ : ℝ) : ℂ))) * z := by
  simp only [Complex.ofReal_mul, star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

variable [Γ.FiniteIndex]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- The profile uses the unchanged original trace and finite Fourier
transforms, at the exact quotient radius for every subgroup orbit. -/
theorem secondProfile_at_quotient
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (c d : OrbitalGaussColumn K S Γ)
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (r : {r : ℝ // 0 < r})
    (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)))
    (q : SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    c.secondProfile μv hDiff d φ finiteTest r D q =
      sUnitOrbitalProfile K (S : Set (HeightOneSpectrum (𝓞 K)))
        (sLocalTensorTestFunction K (S : Set (HeightOneSpectrum (𝓞 K)))
          (traceSchwartzFourier K φ) (sIntegerFiniteFourierTestFunction K S μv finiteTest))
        ⟨(rowRadius r D q).val / (columnNorm c * columnNorm d),
          div_pos (rowRadius r D q).property
            (mul_pos (columnNorm_pos c) (columnNorm_pos d))⟩ := by
  unfold OrbitalGaussColumn.secondProfile
  apply congrArg (sUnitOrbitalProfile K (S : Set (HeightOneSpectrum (𝓞 K)))
    (sLocalTensorTestFunction K (S : Set (HeightOneSpectrum (𝓞 K)))
      (traceSchwartzFourier K φ) (sIntegerFiniteFourierTestFunction K S μv finiteTest)))
  apply Subtype.ext
  exact pair_dualRadius_mul_orbitNorm hDiff c d φ r D q

variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (S : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (S : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]

/-- The same actual logarithmic kernel works on every original orbit.
The two full column norm powers and the row power remain explicit. -/
theorem secondProfile_log
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (c d : OrbitalGaussColumn K S Γ)
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hhat : Continuous (sIntegerFiniteFourierTestFunction K S μv finiteTest))
    (hhatcs : HasCompactSupport (sIntegerFiniteFourierTestFunction K S μv finiteTest))
    (r : {r : ℝ // 0 < r})
    (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (q : SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    c.secondProfile μv hDiff d φ finiteTest r D q =
      (((rowRadius r D q).val ^ (-δ) : ℝ) : ℂ) *
        (((columnNorm c ^ δ : ℝ) : ℂ) * star ((columnNorm d ^ δ : ℝ) : ℂ)) *
        (CanonicalLogOrbital.fourierCLM K (S : Set (HeightOneSpectrum (𝓞 K))) Γ
          (sIntegerFiniteFourierTestFunction K S μv finiteTest) hhat hhatcs δ hδ hδ1 φ)
          (Real.log (rowRadius r D q).val - Real.log (columnNorm c) -
            Real.log (columnNorm d)) := by
  rw [secondProfile_at_quotient μv hDiff c d φ finiteTest r D q]
  have he := CanonicalLogOrbital.orbital_at_quotient K
    (S : Set (HeightOneSpectrum (𝓞 K))) Γ
    (sIntegerFiniteFourierTestFunction K S μv finiteTest) hhat hhatcs
    δ hδ hδ1 (traceSchwartzFourier K φ) (rowRadius r D q).val
    (columnNorm c) (columnNorm d) (rowRadius r D q).property
    (columnNorm_pos c) (columnNorm_pos d)
  simpa only [CanonicalLogOrbital.fourierCLM_apply,
    CanonicalLogOrbital.orbitalCLM_apply, Complex.real_smul, Complex.ofReal_mul,
    Complex.star_def, Complex.conj_ofReal, mul_assoc] using he

/-- The exact finite Fourier scalar remains after its original quotient
cardinality cancellation.  The logarithmic change affects only the last
profile factor in this identity. -/
theorem transformedRow_log
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (c d : OrbitalGaussColumn K S Γ)
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hhat : Continuous (sIntegerFiniteFourierTestFunction K S μv finiteTest))
    (hhatcs : HasCompactSupport (sIntegerFiniteFourierTestFunction K S μv finiteTest))
    (r : {r : ℝ // 0 < r})
    (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)))
    (hcD : IsCoprime c.modulus
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (hdD : IsCoprime d.modulus
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (q : SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    (c.pair hDiff d φ).transformedRow μv hDiff finiteTest r D q =
      secondOrbitalScalar r D *
        (c.divisorPhase (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D).val *
          star (d.divisorPhase (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D).val)) *
        c.correlation d (-q.out.val) *
        ((((rowRadius r D q).val ^ (-δ) : ℝ) : ℂ) *
          (((columnNorm c ^ δ : ℝ) : ℂ) * star ((columnNorm d ^ δ : ℝ) : ℂ)) *
          (CanonicalLogOrbital.fourierCLM K (S : Set (HeightOneSpectrum (𝓞 K))) Γ
            (sIntegerFiniteFourierTestFunction K S μv finiteTest) hhat hhatcs δ hδ hδ1 φ)
            (Real.log (rowRadius r D q).val - Real.log (columnNorm c) -
              Real.log (columnNorm d))) := by
  rw [c.transformedRow_out μv hDiff d φ finiteTest r D hcD hdD q,
    secondProfile_log μv hDiff c d φ finiteTest hhat hhatcs r D δ hδ hδ1 q]

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

/-- The second common kernel is constructed from the original local
test.  It has no radius, mask, row, column, or classifier parameter. -/
def kernel
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ S, HasCompactSupport (finiteTest v))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ) : SchwartzMap ℝ ℂ :=
  let hhat := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport
    K S ν μv finiteTest hlc hcs
  CanonicalLogOrbital.fourierCLM K (S : Set (HeightOneSpectrum (𝓞 K))) Γ
    (sIntegerFiniteFourierTestFunction K S μv finiteTest) hhat.1.continuous hhat.2
    δ hδ hδ1 φ

/-- Finite original profile orders are selected before the archimedean
test and before every moving second-source datum. -/
theorem kernel_finite_seminorm_bound
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ S, HasCompactSupport (finiteTest v))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (t : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ,
        t.sup (schwartzSeminormFamily ℝ ℝ ℂ)
          (kernel (Γ := Γ) μv ν finiteTest hlc hcs δ hδ hδ1 φ) ≤
          C * s.sup (schwartzSeminormFamily ℝ (mixedEmbedding.euclidean.mixedSpace K) ℂ) φ := by
  let hhat := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport
    K S ν μv finiteTest hlc hcs
  exact CanonicalLogOrbital.fourier_finite_seminorm_bound K
    (S : Set (HeightOneSpectrum (𝓞 K))) Γ
    (sIntegerFiniteFourierTestFunction K S μv finiteTest) hhat.1.continuous hhat.2
    δ hδ hδ1 t

end Orbital

section Generated

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]

/-- The logarithmic coordinate of a generated column is the norm of its
original ideal, independent of the allowed generator used for that ideal. -/
theorem generated_columnNorm (I : A.Exterior) (a : A.R) (ha : A.Generates I a) :
    columnNorm (generatedOriginalColumn (σ := σ) hΓ I a ha) =
      (Ideal.absNorm I.val : ℝ) :=
  generates_sIntegerElementNorm I a ha

end Generated

end HeckeSkeleton.Moments.EngineStep.CanonicalSecondLogChart

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
open HeckeGeneral.Characters

variable {K : Type} [Field K] [NumberField K]

section ActualBlock

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)

section Coefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Insert whole original column coefficients without changing the
common kernel, the row partition, any mask, or either log location. -/
def SecondBlockProfileChart.withCoefficients
    {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
    {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
    {b : FirstCommonCharacterBlock fullI fullJ DE}
    {C : A.GeneralArithmeticContext σ η htrace} {left : Finset ι} {right : Finset κ}
    {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
    {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
    {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
    (chart : SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right
      profiles finiteTest radius D) (c : ι → ℂ) (e : κ → ℂ) :
    SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right
      (fun i j => (c i * star (e j)) • profiles i j) finiteTest radius D where
  kernel := chart.kernel
  weight := chart.weight
  leftCoefficient i := c i * chart.leftCoefficient i
  rightCoefficient j := e j * chart.rightCoefficient j
  leftPoint := chart.leftPoint
  rightPoint := chart.rightPoint
  rowLabelCount := chart.rowLabelCount
  rowLabel := chart.rowLabel
  left_mask := chart.left_mask
  right_mask := chart.right_mask
  profile q i hi j hj hcop := by
    rw [OrbitalGaussColumn.secondProfile_smul, chart.profile q i hi j hj hcop]
    simp only [star_mul]
    ring

end Coefficients

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

/-- Construct the second chart from the original test on the full log
axis.  The original row classifier and mask conditions are retained.
The Mellin tilt contributes the actual two full-ideal norm powers and
the inverse row-radius power; none is discarded by the chart. -/
def SecondBlockProfileChart.canonicalLog
    {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
    {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η htrace) (left : Finset ι) (right : Finset κ)
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (rowLabelCount : ℕ)
    (rowLabel : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
      Fin (rowLabelCount + 1))
    (hleft : ∀ i ∈ b.leftColumns left,
      IsCoprime (engineAllowedGenerator C b.commonLeftIdeal * b.leftGenerator i)
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (hright : ∀ j ∈ b.rightColumns right,
      IsCoprime (engineAllowedGenerator C b.commonRightIdeal * b.rightGenerator j)
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    SecondBlockProfileChart (E := ℝ) hΓ μv hDiff b C left right
      (fun _ _ => φ) finiteTest radius D where
  kernel := CanonicalSecondLogChart.kernel (Γ := Γ) μv ν finiteTest hlc hcs δ hδ hδ1 φ
  weight q := (((CanonicalSecondLogChart.rowRadius radius D q).val ^ (-δ) : ℝ) : ℂ)
  leftCoefficient i := ((A.exteriorNorm (b.secondLeftIdeal i) ^ δ : ℝ) : ℂ)
  rightCoefficient j := ((A.exteriorNorm (b.secondRightIdeal j) ^ δ : ℝ) : ℂ)
  leftPoint q i := Real.log (CanonicalSecondLogChart.rowRadius radius D q).val -
    Real.log (A.exteriorNorm (b.secondLeftIdeal i))
  rightPoint _ j := -Real.log (A.exteriorNorm (b.secondRightIdeal j))
  rowLabelCount := rowLabelCount
  rowLabel := rowLabel
  left_mask := hleft
  right_mask := hright
  profile q i _ j _ _ := by
    let hhat := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport
      K A.Sf ν μv finiteTest hlc hcs
    have he := CanonicalSecondLogChart.secondProfile_log μv hDiff
      (generatedOriginalColumn (σ := σ) hΓ (b.secondLeftIdeal i)
        (engineAllowedGenerator C b.commonLeftIdeal * b.leftGenerator i)
        (b.secondLeft_generates C i))
      (generatedOriginalColumn (σ := σ) hΓ (b.secondRightIdeal j)
        (engineAllowedGenerator C b.commonRightIdeal * b.rightGenerator j)
        (b.secondRight_generates C j))
      φ finiteTest hhat.1.continuous hhat.2 radius D δ hδ hδ1 q
    have hnl := CanonicalSecondLogChart.generated_columnNorm (σ := σ) hΓ
      (b.secondLeftIdeal i) _ (b.secondLeft_generates C i)
    have hnr := CanonicalSecondLogChart.generated_columnNorm (σ := σ) hΓ
      (b.secondRightIdeal j) _ (b.secondRight_generates C j)
    change CanonicalSecondLogChart.columnNorm _ = A.exteriorNorm (b.secondLeftIdeal i) at hnl
    change CanonicalSecondLogChart.columnNorm _ = A.exteriorNorm (b.secondRightIdeal j) at hnr
    simpa only [hnl, hnr, CanonicalSecondLogChart.kernel, sub_eq_add_neg] using he

/-- The genuine second chart for one whole original column polynomial,
including a centered coefficient and any previously fixed first Fourier
phase.  The common kernel remains independent of all these coefficients. -/
def SecondBlockProfileChart.canonicalLogWithCoefficients
    {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
    {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η htrace) (left : Finset ι) (right : Finset κ)
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (c : ι → ℂ) (e : κ → ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (rowLabelCount : ℕ)
    (rowLabel : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
      Fin (rowLabelCount + 1))
    (hleft : ∀ i ∈ b.leftColumns left,
      IsCoprime (engineAllowedGenerator C b.commonLeftIdeal * b.leftGenerator i)
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (hright : ∀ j ∈ b.rightColumns right,
      IsCoprime (engineAllowedGenerator C b.commonRightIdeal * b.rightGenerator j)
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    SecondBlockProfileChart (E := ℝ) hΓ μv hDiff b C left right
      (fun i j => (c i * star (e j)) • φ) finiteTest radius D :=
  SecondBlockProfileChart.withCoefficients hΓ μv hDiff
    (SecondBlockProfileChart.canonicalLog hΓ μv hDiff ν b C left right φ
      finiteTest hlc hcs radius D rowLabelCount rowLabel hleft hright δ hδ hδ1) c e

end ActualBlock

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondLogChart.pair_dualRadius_mul_orbitNorm
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondLogChart.secondProfile_log
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondLogChart.transformedRow_log
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondLogChart.kernel_finite_seminorm_bound
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.withCoefficients
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.canonicalLog
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.canonicalLogWithCoefficients
