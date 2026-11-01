import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondZeroSupport

/-!
# Uniform amplitude of the actual second Euler diagonal

The original annular Schwartz test controls the genuine dual zero
value.  The complete correlation supplies its full Euler diagonal and
vanishes off equal exterior ideals.  All constants and seminorms are
chosen before the original moduli, generators, coefficients and mask.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments MeasureTheory UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]
variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}

theorem OrbitalGaussColumn.divisorPhase_norm_le_one
    (c : OrbitalGaussColumn K S Γ)
    (δ : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) : ‖c.divisorPhase δ‖ ≤ 1 := by
  letI : Finite ((Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) ⧸ Ideal.span {c.modulus}) :=
    finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K))) c.modulus c.nonzero
  letI : Fintype ((Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) ⧸ Ideal.span {c.modulus}) :=
    Fintype.ofFinite _
  exact finiteCharacter_norm_le_one c.character⁻¹ _

variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

theorem secondOrbitalScalar_norm_eq_zeroWeight
    (radius : {r : ℝ // 0 < r})
    (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K))) :
    ‖secondOrbitalScalar radius D‖ = orbitalFieldFactor K * firstZeroDivisorWeight radius D := by
  let r := sIntegerMaskDilationRadius K S radius
    (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)
  change ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ) * (r.val : ℂ)⁻¹ *
      (orbitalFieldFactor K : ℂ)‖ =
    orbitalFieldFactor K * (‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ * r.val⁻¹)
  simp only [norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg r.property.le, Real.norm_of_nonneg (orbitalFieldFactor_nonneg K)]
  ring

section Actual

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {Γ₀ : Subgroup A.U}
variable (hΓ₀ : ∀ u : Γ₀, ∃ v : A.U, u.val = v ^ 6)
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [Γ₀.FiniteIndex] [IsPrincipalIdealRing A.R]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- The actual second zero bound retains the equal-ideal indicator and
the genuine inverse mask norm.  Its only profile restriction is the
original annular value at zero. -/
theorem second_zero_amplitude_uniform
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ (I J : A.Exterior) (a b : A.R) (ha : A.Generates I a) (hb : A.Generates J b),
    ∀ (φ : SchwartzMap V ℂ), φ 0 = 0 →
    ∀ hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0,
    ∀ (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R)),
    IsCoprime a (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val →
    IsCoprime b (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val →
    ‖((generatedOriginalColumn (σ := σ) hΓ₀ I a ha).pair hDiff
      (generatedOriginalColumn (σ := σ) hΓ₀ J b hb) φ).transformedZero
        μv hDiff finiteTest radius D‖ ≤
      C * s.sup (schwartzSeminormFamily ℂ V ℂ) φ * firstZeroDivisorWeight radius D *
        (if I = J then A.exteriorNorm I else 0) := by
  obtain ⟨s, C₀, hC₀, hzero⟩ :=
    dual_tensor_zero_seminorm_bound (K := K) (S := A.Sf) μv finiteTest
  let H : ℝ := ‖((sUnitHaarCovolume K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ₀).toReal : ℂ)‖
  refine ⟨s, H * orbitalFieldFactor K * C₀,
    mul_nonneg (mul_nonneg (norm_nonneg _) (orbitalFieldFactor_nonneg K)) hC₀.le, ?_⟩
  intro I J a b ha hb φ hφ hDiff radius D haδ hbδ
  let c := generatedOriginalColumn (σ := σ) hΓ₀ I a ha
  let d := generatedOriginalColumn (σ := σ) hΓ₀ J b hb
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
    generated_correlation_zero_norm_le I J a b ha hb
  have hphasecorr : ‖c.divisorPhase δ * star (d.divisorPhase δ)‖ *
      ‖c.correlation d 0‖ ≤ N :=
    (mul_le_mul hphase hcorr (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hdual := hzero φ
  have hprod :
      (‖c.divisorPhase δ * star (d.divisorPhase δ)‖ * ‖c.correlation d 0‖) *
        ‖sIntegerDualTensorTerm K μv A.Sf (traceSchwartzToMixed K φ) finiteTest 0‖ ≤
      N * (C₀ * s.sup (schwartzSeminormFamily ℂ V ℂ) φ) :=
    mul_le_mul hphasecorr hdual (norm_nonneg _) hN
  rw [OrbitalGaussColumn.transformedZero_pair μv hDiff _ _ φ hφ finiteTest radius D haδ hbδ]
  simp only [norm_mul]
  calc
    _ = (H * ‖secondOrbitalScalar radius D‖) *
        ((‖c.divisorPhase δ * star (d.divisorPhase δ)‖ * ‖c.correlation d 0‖) *
          ‖sIntegerDualTensorTerm K μv A.Sf (traceSchwartzToMixed K φ) finiteTest 0‖) := by
      simp only [norm_mul, norm_star]
      ring
    _ ≤ (H * ‖secondOrbitalScalar radius D‖) *
        (N * (C₀ * s.sup (schwartzSeminormFamily ℂ V ℂ) φ)) :=
      mul_le_mul_of_nonneg_left hprod (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
      rw [secondOrbitalScalar_norm_eq_zeroWeight]
      ring

end Actual

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.second_zero_amplitude_uniform
