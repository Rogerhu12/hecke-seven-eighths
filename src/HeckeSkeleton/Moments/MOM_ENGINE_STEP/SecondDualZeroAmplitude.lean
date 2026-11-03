import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SignedPoissonZero
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondZeroAmplitude

/-!
# The pure second dual-zero term without an origin-vanishing condition

The dual zero is separated from the primal-origin subtraction before
any norm is taken. Its actual finite Fourier coefficient is the complete
correlation at zero. Orthogonality therefore gives the equal-ideal
support and the full quotient-unit Euler diagonal for every original
Schwartz profile, including a row-ball profile which is nonzero at zero.

The uniform amplitude retains the original covolume, divisor phases,
Möbius weight and inverse mask-dilation norm. Its seminorms and constant
are chosen before the moduli, generators, profiles, radius and divisor.
No profile-zero condition or terminal estimate is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments MeasureTheory UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]

section Orbital

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [Γ.FiniteIndex]
  [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- Exact cardinality cancellation for the pure dual zero. The primal
profile value does not occur in this identity. -/
theorem OrbitalGaussColumn.dualZero_pair
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (c d : OrbitalGaussColumn K S Γ)
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (radius : {r : ℝ // 0 < r})
    (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)))
    (hcδ : IsCoprime c.modulus
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (hdδ : IsCoprime d.modulus
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D).val) :
    (c.pair hDiff d φ).dualZero μv hDiff finiteTest radius D =
      ((sUnitHaarCovolume K (S : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ) *
        secondOrbitalScalar radius D *
        (c.divisorPhase (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D).val *
          star (d.divisorPhase (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D).val)) *
        c.correlation d 0 *
        sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ) finiteTest 0 := by
  have hf := c.pair_divisor_fourier hDiff d φ
    (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D).val 0 hcδ hdδ
  simp only [map_zero, neg_zero] at hf
  unfold ParentPeriodicPair.dualZero
  change (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
    ((sUnitHaarCovolume K (S : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ) *
    (sIntegerMaskPoissonFactor K S (c.modulus * d.modulus) (mul_ne_zero c.nonzero d.nonzero)
        radius (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D) *
      (_ * sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ) finiteTest 0)) = _
  rw [hf]
  let δ := sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D
  have hcard := maskPoissonFactor_mul_card (K := K) (S := S)
    (c.modulus * d.modulus) (mul_ne_zero c.nonzero d.nonzero) radius δ
  unfold secondOrbitalScalar
  calc
    _ = ((sUnitHaarCovolume K (S : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ) *
        (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
        (sIntegerMaskPoissonFactor K S (c.modulus * d.modulus) (mul_ne_zero c.nonzero d.nonzero)
            radius δ * (Nat.card ((Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) ⧸
              Ideal.span {c.modulus * d.modulus}) : ℂ)) *
        (c.divisorPhase δ.val * star (d.divisorPhase δ.val)) * c.correlation d 0 *
          sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ) finiteTest 0 := by ring
    _ = _ := by rw [hcard]; ring

end Orbital

section Generated

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

theorem generated_second_dualZero_of_ne
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (I J : A.Exterior) (a b : A.R) (ha : A.Generates I a) (hb : A.Generates J b)
    (hIJ : I ≠ J) (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (haδ : IsCoprime a (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (hbδ : IsCoprime b (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) :
    ((generatedOriginalColumn (σ := σ) hΓ I a ha).pair hDiff
      (generatedOriginalColumn (σ := σ) hΓ J b hb) φ).dualZero
        μv hDiff finiteTest radius D = 0 := by
  rw [OrbitalGaussColumn.dualZero_pair μv hDiff _ _ φ finiteTest radius D haδ hbδ,
    generatedColumn_correlation, generated_correlation_zero_of_ne (σ := σ) I J a b ha hb hIJ,
    mul_zero, zero_mul]

/-- The full Euler factor is the unit group of the original quotient,
with every prime-power depth. The original phases remain explicit. -/
theorem generated_second_dualZero_diagonal_norm
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (I : A.Exterior) (a b : A.R) (ha : A.Generates I a) (hb : A.Generates I b)
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (haδ : IsCoprime a (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (hbδ : IsCoprime b (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) :
    let c := generatedOriginalColumn (σ := σ) hΓ I a ha
    let d := generatedOriginalColumn (σ := σ) hΓ I b hb
    let δ := (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
    ‖(c.pair hDiff d φ).dualZero μv hDiff finiteTest radius D‖ =
      ‖((sUnitHaarCovolume K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ)‖ *
        ‖secondOrbitalScalar radius D‖ * ‖c.divisorPhase δ * star (d.divisorPhase δ)‖ *
        (Nat.card (A.R ⧸ Ideal.span {a})ˣ : ℝ) *
        ‖sIntegerDualTensorTerm K μv A.Sf (traceSchwartzToMixed K φ) finiteTest 0‖ := by
  dsimp only
  rw [OrbitalGaussColumn.dualZero_pair μv hDiff _ _ φ finiteTest radius D haδ hbδ]
  simp only [norm_mul, norm_star, generatedColumn_correlation,
    generated_correlation_zero_diagonal_norm (σ := σ) I a b ha hb]

/-- Uniform pure dual-zero amplitude. There is no restriction on the
original profile at zero, and no final terminal bound is assumed. -/
theorem second_dualZero_amplitude_uniform
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ (I J : A.Exterior) (a b : A.R) (ha : A.Generates I a) (hb : A.Generates J b),
    ∀ (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ),
    ∀ hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0,
    ∀ (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R)),
    IsCoprime a (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val →
    IsCoprime b (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val →
    ‖((generatedOriginalColumn (σ := σ) hΓ I a ha).pair hDiff
      (generatedOriginalColumn (σ := σ) hΓ J b hb) φ).dualZero
        μv hDiff finiteTest radius D‖ ≤
      C * s.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) φ *
        firstZeroDivisorWeight radius D * (if I = J then A.exteriorNorm I else 0) := by
  obtain ⟨s, C₀, hC₀, hzero⟩ :=
    dual_tensor_zero_seminorm_bound (K := K) (S := A.Sf) μv finiteTest
  let H : ℝ := ‖((sUnitHaarCovolume K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ)‖
  refine ⟨s, H * orbitalFieldFactor K * C₀,
    mul_nonneg (mul_nonneg (norm_nonneg _) (orbitalFieldFactor_nonneg K)) hC₀.le, ?_⟩
  intro I J a b ha hb φ hDiff radius D haδ hbδ
  let c := generatedOriginalColumn (σ := σ) hΓ I a ha
  let d := generatedOriginalColumn (σ := σ) hΓ J b hb
  let δ := (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
  let N : ℝ := if I = J then A.exteriorNorm I else 0
  have hN : 0 ≤ N := by
    dsimp only [N]
    split_ifs
    · change 0 ≤ (Ideal.absNorm I.val : ℝ)
      positivity
    · exact le_rfl
  have hphase : ‖c.divisorPhase δ * star (d.divisorPhase δ)‖ ≤ 1 := by
    rw [norm_mul, norm_star]
    exact (mul_le_mul (c.divisorPhase_norm_le_one δ) (d.divisorPhase_norm_le_one δ)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hcorr : ‖c.correlation d 0‖ ≤ N :=
    generated_correlation_zero_norm_le (σ := σ) I J a b ha hb
  have hphasecorr : ‖c.divisorPhase δ * star (d.divisorPhase δ)‖ *
      ‖c.correlation d 0‖ ≤ N :=
    (mul_le_mul hphase hcorr (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hdual := hzero φ
  have hprod :
      (‖c.divisorPhase δ * star (d.divisorPhase δ)‖ * ‖c.correlation d 0‖) *
        ‖sIntegerDualTensorTerm K μv A.Sf (traceSchwartzToMixed K φ) finiteTest 0‖ ≤
      N * (C₀ * s.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) φ) :=
    mul_le_mul hphasecorr hdual (norm_nonneg _) hN
  rw [OrbitalGaussColumn.dualZero_pair μv hDiff _ _ φ finiteTest radius D haδ hbδ]
  simp only [norm_mul]
  calc
    _ = (H * ‖secondOrbitalScalar radius D‖) *
        ((‖c.divisorPhase δ * star (d.divisorPhase δ)‖ * ‖c.correlation d 0‖) *
          ‖sIntegerDualTensorTerm K μv A.Sf (traceSchwartzToMixed K φ) finiteTest 0‖) := by
      simp only [norm_mul, norm_star]
      ring
    _ ≤ (H * ‖secondOrbitalScalar radius D‖) *
        (N * (C₀ * s.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) φ)) :=
      mul_le_mul_of_nonneg_left hprod (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
      rw [secondOrbitalScalar_norm_eq_zeroWeight]
      ring

end Generated
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OrbitalGaussColumn.dualZero_pair
#print axioms HeckeSkeleton.Moments.EngineStep.generated_second_dualZero_of_ne
#print axioms HeckeSkeleton.Moments.EngineStep.generated_second_dualZero_diagonal_norm
#print axioms HeckeSkeleton.Moments.EngineStep.second_dualZero_amplitude_uniform
