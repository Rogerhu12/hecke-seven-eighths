import HeckeSkeleton.Moments.MOM_ENGINE_STEP.GeneratedCorrelation
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondGeneratorSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstZeroAmplitude

/-!
# The genuine second zero term and its full Euler diagonal

The complete finite correlation at frequency zero vanishes unless the
two original exterior ideals agree.  On the diagonal its norm is the
number of units of the full quotient, including every prime-power depth.
The actual orbital zero term is then identified with this correlation
after exact cancellation of the product-modulus cardinality.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments MeasureTheory
open UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}

theorem generated_correlation_zero_of_ne (I J : A.Exterior) (a b : A.R)
    (ha : A.Generates I a) (hb : A.Generates J b) (hIJ : I ≠ J) :
    generatedIdealCorrelation (σ := σ) I J a b ha hb 0 = 0 := by
  letI : Finite (A.R ⧸ Ideal.span {a}) := by rw [ha.2]; exact A.exteriorResidue_finite I
  letI : Finite (A.R ⧸ Ideal.span {b}) := by rw [hb.2]; exact A.exteriorResidue_finite J
  letI : Fintype (A.R ⧸ Ideal.span {a}) := Fintype.ofFinite _
  letI : Fintype (A.R ⧸ Ideal.span {b}) := Fintype.ofFinite _
  apply fullModulusCorrelation_zero_frequency_off_diagonal
  intro he
  apply hIJ
  apply A.exteriorIdealEquiv.injective
  apply Subtype.ext
  change A.extendIdeal I = A.extendIdeal J
  exact ha.2.symm.trans (he.trans hb.2)

/-- The full Euler function, independent of the chosen presentations of
the same exterior ideal.  There is no primitive-conductor replacement. -/
theorem generated_correlation_zero_diagonal_norm (I : A.Exterior) (a b : A.R)
    (ha : A.Generates I a) (hb : A.Generates I b) :
    ‖generatedIdealCorrelation (σ := σ) I I a b ha hb 0‖ =
      (Nat.card (A.R ⧸ Ideal.span {a})ˣ : ℝ) := by
  rw [generated_correlation_norm_generator_change I I a a a b ha ha ha hb]
  letI : Finite (A.R ⧸ Ideal.span {a}) := by rw [ha.2]; exact A.exteriorResidue_finite I
  letI : Fintype (A.R ⧸ Ideal.span {a}) := Fintype.ofFinite _
  change ‖fullModulusCorrelation a a (generatedIdealCharacter (σ := σ) I a ha)
    (generatedIdealCharacter (σ := σ) I a ha) 0‖ = _
  rw [fullModulusCorrelation_zero_frequency_diagonal a ha.1]
  simp [Nat.card_eq_fintype_card]

theorem generated_correlation_zero_norm_le (I J : A.Exterior) (a b : A.R)
    (ha : A.Generates I a) (hb : A.Generates J b) :
    ‖generatedIdealCorrelation (σ := σ) I J a b ha hb 0‖ ≤
      if I = J then A.exteriorNorm I else 0 := by
  by_cases hIJ : I = J
  · subst J
    rw [if_pos rfl, generated_correlation_zero_diagonal_norm I a b ha hb]
    letI : Finite (A.R ⧸ Ideal.span {a}) := by rw [ha.2]; exact A.exteriorResidue_finite I
    letI : Fintype (A.R ⧸ Ideal.span {a}) := Fintype.ofFinite _
    have hu : Nat.card (A.R ⧸ Ideal.span {a})ˣ ≤ Nat.card (A.R ⧸ Ideal.span {a}) := by
      simpa only [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective
        (fun u : (A.R ⧸ Ideal.span {a})ˣ => u.val) Units.val_injective
    have hcard : (Nat.card (A.R ⧸ Ideal.span {a}) : ℝ) = A.exteriorNorm I := by
      rw [ha.2, A.exteriorResidue_card]
      rfl
    exact (Nat.cast_le.mpr hu).trans_eq hcard
  · simp only [if_neg hIJ, generated_correlation_zero_of_ne I J a b ha hb hIJ,
      norm_zero, le_refl]

section Orbital

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [Γ.FiniteIndex] [IsPrincipalIdealRing OS]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- The literal second orbital zero term, after exact cardinality
cancellation and the original annular profile's primal zero subtraction. -/
theorem OrbitalGaussColumn.transformedZero_pair
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (c d : OrbitalGaussColumn K S Γ) (φ : SchwartzMap V ℂ) (hφ : φ 0 = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum OS))
    (hcδ : IsCoprime c.modulus
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (hdδ : IsCoprime d.modulus
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D).val) :
    (c.pair hDiff d φ).transformedZero μv hDiff finiteTest radius D =
      ((sUnitHaarCovolume K (S : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ) *
        secondOrbitalScalar radius D *
        (c.divisorPhase (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D).val *
          star (d.divisorPhase (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D).val)) *
        c.correlation d 0 *
        sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ) finiteTest 0 := by
  have hprimal : sIntegerTensorTerm K S (traceSchwartzToMixed K φ) finiteTest 0 = 0 := by
    simp only [sIntegerTensorTerm, map_zero, traceSchwartzToMixed_apply, hφ, zero_mul]
  have hf := c.pair_divisor_fourier hDiff d φ
    (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D).val 0 hcδ hdδ
  simp only [map_zero, neg_zero] at hf
  unfold ParentPeriodicPair.transformedZero
  change (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
    ((sUnitHaarCovolume K (S : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ) *
    (sIntegerMaskPoissonFactor K S (c.modulus * d.modulus) (mul_ne_zero c.nonzero d.nonzero)
        radius (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D) *
      (_ * sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ) finiteTest 0) -
      _ * sIntegerTensorTerm K S (traceSchwartzToMixed K φ) finiteTest 0) = _
  rw [hprimal, mul_zero, sub_zero, hf]
  let δ := sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D
  have hcard := maskPoissonFactor_mul_card (K := K) (S := S)
    (c.modulus * d.modulus) (mul_ne_zero c.nonzero d.nonzero) radius δ
  unfold secondOrbitalScalar
  calc
    _ = ((sUnitHaarCovolume K (S : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ) *
        (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
        (sIntegerMaskPoissonFactor K S (c.modulus * d.modulus) (mul_ne_zero c.nonzero d.nonzero)
            radius δ * (Nat.card (OS ⧸ Ideal.span {c.modulus * d.modulus}) : ℂ)) *
        (c.divisorPhase δ.val * star (d.divisorPhase δ.val)) * c.correlation d 0 *
          sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ) finiteTest 0 := by ring
    _ = _ := by rw [hcard]; ring

end Orbital

section Generated

variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- The actual second source has only the genuine equal-ideal diagonal
at frequency zero.  The original annular profile is retained. -/
theorem generated_second_zero_of_ne
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (I J : A.Exterior) (a b : A.R) (ha : A.Generates I a) (hb : A.Generates J b)
    (hIJ : I ≠ J) (φ : SchwartzMap V ℂ) (hφ : φ 0 = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (haδ : IsCoprime a (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (hbδ : IsCoprime b (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) :
    ((generatedOriginalColumn (σ := σ) hΓ I a ha).pair hDiff
      (generatedOriginalColumn (σ := σ) hΓ J b hb) φ).transformedZero
        μv hDiff finiteTest radius D = 0 := by
  rw [OrbitalGaussColumn.transformedZero_pair μv hDiff _ _ φ hφ finiteTest radius D haδ hbδ,
    generatedColumn_correlation, generated_correlation_zero_of_ne I J a b ha hb hIJ,
    mul_zero, zero_mul]

end Generated

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.generated_correlation_zero_diagonal_norm
#print axioms HeckeSkeleton.Moments.EngineStep.generated_second_zero_of_ne
