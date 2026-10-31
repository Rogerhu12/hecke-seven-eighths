import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonSupportSource
import HeckeGeneral.Bridge.TraceSchwartzFourierBounds
import HeckeGeneral.Arithmetic.SIntegerModulusNorm

/-!
# Actual zero-frequency amplitudes

A complete divisor Fourier coefficient is bounded by the cardinality of
its actual quotient, including nonunit divisor fibers. That cardinality
cancels the modulus factor in the genuine orbital Poisson normalization.
The remaining dual tensor value is bounded by fixed original Schwartz
seminorms through the actual trace Fourier operator.

For an original annular profile, the primal zero subtraction is zero.
The resulting pointwise bound has a constant and seminorms chosen before
the modulus, profile, radius, mask divisor, or original columns.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis UniqueFactorizationMonoid MeasureTheory
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]
variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}

theorem OrbitalGaussColumn.originalTriple_residue_norm_le_one
    (a b r : OrbitalGaussColumn K S Γ) (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (x : (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) ⧸ Ideal.span {(a.originalTriple b r φ).modulus}) :
    ‖(a.originalTriple b r φ).residue x‖ ≤ 1 := by
  letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K))) a.modulus a.nonzero
  letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K))) b.modulus b.nonzero
  letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K))) r.modulus r.nonzero
  letI := Fintype.ofFinite ((Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) ⧸ Ideal.span {a.modulus})
  letI := Fintype.ofFinite ((Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) ⧸ Ideal.span {b.modulus})
  letI := Fintype.ofFinite ((Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) ⧸ Ideal.span {r.modulus})
  unfold OrbitalGaussColumn.originalTriple
  rw [norm_mul, norm_mul]
  exact (mul_le_mul
    (mul_le_mul (finiteCharacter_norm_le_one a.character _)
      (finiteCharacter_norm_le_one b.character⁻¹ _) (norm_nonneg _) zero_le_one)
    (finiteCharacter_norm_le_one r.character _) (norm_nonneg _) (by norm_num)).trans_eq
      (by norm_num)

theorem ParentPeriodicPair.divisorFourier_norm_le_card
    (p : ParentPeriodicPair K S Γ) (hres : ∀ x, ‖p.residue x‖ ≤ 1)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (δ : (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)) (h : (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) ⧸ Ideal.span {p.modulus}) :
    ‖sIntegerPeriodicDivisorFourier K (S : Set (HeightOneSpectrum (𝓞 K))) hDiff
      p.modulus p.modulus_ne_zero p.residue δ h‖ ≤
      (Nat.card ((Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) ⧸ Ideal.span {p.modulus}) : ℝ) := by
  letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K))) p.modulus p.modulus_ne_zero
  letI := Fintype.ofFinite ((Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) ⧸ Ideal.span {p.modulus})
  apply (norm_sIntegerPeriodicDivisorFourier_le_pullback_L1 K (S : Set (HeightOneSpectrum (𝓞 K)))
    hDiff p.modulus p.modulus_ne_zero p.residue δ h).trans
  change (∑ x : (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) ⧸ Ideal.span {p.modulus}, ‖p.residue (Ideal.Quotient.mk _ δ * x)‖) ≤ _
  calc
    _ ≤ ∑ _x : (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) ⧸ Ideal.span {p.modulus}, (1 : ℝ) :=
      Finset.sum_le_sum (fun x _ => hres _)
    _ = _ := by simp [Nat.card_eq_fintype_card]

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [Γ.FiniteIndex] [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- The actual dual tensor at zero, with no profile or Fourier-bound input. -/
theorem dual_tensor_zero_seminorm_bound
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ,
      ‖sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ) finiteTest 0‖ ≤
        C * s.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) φ := by
  obtain ⟨s, D, hD, hbound⟩ := traceSchwartzFourier_seminorm_bound K 0 0
  let B : ℝ := ‖sIntegerLocalFourierProduct K μv S finiteTest 0‖
  refine ⟨s, 1 + (D : ℝ) * B, by dsimp [B]; positivity, ?_⟩
  intro φ
  have hz :
      sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ) finiteTest 0 =
        traceSchwartzFourier K φ 0 * sIntegerLocalFourierProduct K μv S finiteTest 0 := by
    unfold sIntegerDualTensorTerm
    simp only [map_zero, Prod.fst_zero, Prod.snd_zero]
    congr 1
    change AdelicFourier.fourierIntegral (standardMixedAddCharacter K) volume
      (traceSchwartzToMixed K φ)
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K) (0 : InfiniteAdeleRing K)) =
        traceSchwartzFourier K φ 0
    simpa only [map_zero] using fourierIntegral_traceSchwartzToMixed_traceToMixed K φ 0
  rw [hz, norm_mul]
  have hp := (SchwartzMap.norm_le_seminorm ℂ (traceSchwartzFourier K φ) 0).trans (hbound φ)
  have hs : 0 ≤ s.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) φ := apply_nonneg _ _
  calc
    _ ≤ ((D : ℝ) * s.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) φ) * B :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ ≤ _ := by nlinarith [D.coe_nonneg, norm_nonneg (sIntegerLocalFourierProduct K μv S finiteTest 0)]

/-- The complete quotient cardinal cancels its literal Poisson denominator. -/
theorem ParentPeriodicPair.poissonFactor_mul_card
    (p : ParentPeriodicPair K S Γ) (radius : {r : ℝ // 0 < r})
    (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K))) :
    ‖sIntegerMaskPoissonFactor K S p.modulus p.modulus_ne_zero radius
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)‖ *
      (Nat.card ((Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) ⧸ Ideal.span {p.modulus}) : ℝ) =
      (sIntegerMaskDilationRadius K S radius (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val⁻¹ *
        ‖(((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K /
          Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ)‖ := by
  let N := sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨p.modulus, p.modulus_ne_zero⟩
  let r := sIntegerMaskDilationRadius K S radius (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)
  rw [natCard_sIntegerPrincipalResidue_eq_productNorm]
  change ‖(r.val : ℂ)⁻¹ *
      (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K /
        Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) * (N.val : ℂ)⁻¹‖ * N.val = _
  simp only [norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos r.property, abs_of_pos N.property]
  rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt N.property), mul_one]

/-- The remaining divisor weight contains its genuine norm-dilated radius. -/
def firstZeroDivisorWeight (radius : {r : ℝ // 0 < r})
    (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K))) : ℝ :=
  ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ *
    (sIntegerMaskDilationRadius K S radius (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val⁻¹

theorem firstZeroDivisorWeight_nonneg (radius : {r : ℝ // 0 < r})
    (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K))) :
    0 ≤ firstZeroDivisorWeight radius D :=
  mul_nonneg (norm_nonneg _) (inv_nonneg.mpr
    (sIntegerMaskDilationRadius K S radius (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).property.le)

/-- A uniform actual first-zero amplitude, before any counting of columns.
The annular condition is on the original profile value, and the arithmetic
Fourier coefficient is bounded internally on the complete quotient. -/
theorem first_zero_amplitude_uniform
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ p : ParentPeriodicPair K S Γ,
      (∀ x, ‖p.residue x‖ ≤ 1) → p.profile 0 = 0 →
    ∀ hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0,
    ∀ (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K))),
      ‖p.transformedZero μv hDiff finiteTest radius D‖ ≤
        C * s.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) p.profile *
          firstZeroDivisorWeight radius D := by
  obtain ⟨s, C₀, hC₀, hzero⟩ :=
    dual_tensor_zero_seminorm_bound (K := K) (S := S) μv finiteTest
  let H : ℝ := ‖((sUnitHaarCovolume K (S : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ)‖
  let J : ℝ := ‖(((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K /
    Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ)‖
  refine ⟨s, H * J * C₀, mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hC₀.le, ?_⟩
  intro p hres hannular hDiff radius D
  have hprimal : sIntegerTensorTerm K S (traceSchwartzToMixed K p.profile) finiteTest 0 = 0 := by
    simp only [sIntegerTensorTerm, map_zero, traceSchwartzToMixed_apply, hannular, zero_mul]
  have hfourier := p.divisorFourier_norm_le_card hres hDiff
    (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D).val 0
  have hdual := hzero p.profile
  unfold ParentPeriodicPair.transformedZero
  rw [hprimal, mul_zero, sub_zero]
  simp only [norm_mul]
  calc
    _ ≤ ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ * H *
        (‖sIntegerMaskPoissonFactor K S p.modulus p.modulus_ne_zero radius
            (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)‖ *
          ((Nat.card ((Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) ⧸ Ideal.span {p.modulus}) : ℝ) *
            (C₀ * s.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) p.profile))) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact mul_le_mul hfourier hdual (norm_nonneg _) (Nat.cast_nonneg _)
    _ = ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ * H *
        ((‖sIntegerMaskPoissonFactor K S p.modulus p.modulus_ne_zero radius
            (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)‖ *
          (Nat.card ((Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) ⧸ Ideal.span {p.modulus}) : ℝ)) *
          (C₀ * s.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) p.profile)) := by ring
    _ = _ := by
      rw [p.poissonFactor_mul_card radius D]
      unfold firstZeroDivisorWeight
      dsimp only [H, J]
      ring

section ActualBlocks

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ₀ : Subgroup A.U}
variable (hΓ₀ : ∀ u : Γ₀, ∃ v : A.U, u.val = v ^ 6)

theorem FirstCommonCharacterBlock.residue_norm_le_one
    {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
    {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS) (profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (i : ι) (j : κ)
    (x : A.R ⧸ Ideal.span {(b.pair hΓ₀ C profiles i j).modulus}) :
    ‖(b.pair hΓ₀ C profiles i j).residue x‖ ≤ 1 := by
  unfold FirstCommonCharacterBlock.pair
  by_cases hc : IsCoprime (b.leftResidual i).val (b.rightResidual j).val
  · simp only [ParentPeriodicPair.gated, if_pos hc]
    exact OrbitalGaussColumn.originalTriple_residue_norm_le_one _ _ _ _ x
  · simp only [ParentPeriodicPair.gated, if_neg hc, norm_zero]
    exact zero_le_one

end ActualBlocks

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.dual_tensor_zero_seminorm_bound
#print axioms HeckeSkeleton.Moments.EngineStep.first_zero_amplitude_uniform

