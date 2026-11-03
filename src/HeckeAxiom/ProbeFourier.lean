import HeckeAxiom.ProbeUnits
import HeckeAxiom.TraceCharacterDictionary
import DedekindZetaZeroFree.Moments.Probes.TraceHaarCoordinates
import FLTReuse.Mfdd944592cac5200

/-!
# Axiom's probe Fourier transform in the skeleton's normalization

Let `W0 = g ∘ R · ∏ f_v` be a tensor on Axiom's `S`-local product, where `R` is the
infinite adele ring equivalence with the mixed space. With respect to Axiom's
Poisson additive measure built from local Haar measures `μ_v`, Axiom's Fourier
transform of `W0` at `y` is `2^{r₂}` times the archimedean Fourier transform of `g`
at `R y∞` times the local Fourier transforms of the `f_v` at `y_v`. The archimedean
transform is the skeleton's: the standard mixed character against Lebesgue
measure. The two archimedean characters agree because every infinite place is
complex. The local transforms use the skeleton's `psiLocal` and the same `μ_v`.
-/

noncomputable section

namespace HeckeAxiom

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Bridge NumberField.StandardAddChar
open scoped Classical

namespace ProbeFourier

variable {K : Type} [Field K] [NumberField K] (A : SArithmeticData K)

local notation "R" => InfiniteAdeleRing.ringEquiv_mixedSpace K

include A in
/-- Axiom's archimedean phase is the skeleton's standard mixed character. -/
theorem archPhase_symm (m : mixedEmbedding.mixedSpace K) :
    ProbeAdditive.archPhase K ((R).symm m) = standardMixedAddCharacter K m := by
  have hempty : IsEmpty {w : InfinitePlace K // w.IsReal} :=
    ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.mpr (A.complex_place w.1)) w.2⟩
  have htr : (∑ v : InfinitePlace K,
      2 * (InfinitePlace.Completion.extensionEmbedding v ((R).symm m v)).re) =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace K) m := by
    rw [mixedEmbedding.trace_mixedSpace_apply]
    simp only [Fintype.sum_empty, zero_add]
    rw [← (Equiv.subtypeUnivEquiv fun w => A.complex_place w).sum_comp]
    refine Finset.sum_congr rfl fun w _ => ?_
    have h : InfinitePlace.Completion.extensionEmbedding w.1 ((R).symm m w.1) = m.2 w := by
      conv_rhs => rw [← RingEquiv.apply_symm_apply (InfiniteAdeleRing.ringEquiv_mixedSpace K) m]
      rfl
    change 2 * (InfinitePlace.Completion.extensionEmbedding w.1 ((R).symm m w.1)).re =
      2 * (m.2 w).re
    rw [h]
  have htr' : (∑ v : InfinitePlace K,
      2 * ((InfinitePlace.Completion.extensionEmbedding v ((R).symm m v)).re : ℂ)) =
      ((Algebra.trace ℝ (mixedEmbedding.mixedSpace K) m : ℝ) : ℂ) := by
    rw [← htr]
    push_cast
    rfl
  unfold ProbeAdditive.archPhase
  rw [standardMixedAddCharacter_apply, Real.fourierChar_apply, htr']
  congr 1
  push_cast
  ring

local instance : MeasurableSpace (SLocalProduct K A.Sf) := borel _
local instance : BorelSpace (SLocalProduct K A.Sf) := ⟨rfl⟩
local instance (v : HeightOneSpectrum (𝓞 K)) : MeasurableSpace (v.adicCompletion K) := borel _
local instance (v : HeightOneSpectrum (𝓞 K)) : BorelSpace (v.adicCompletion K) := ⟨rfl⟩

/-- Axiom's Poisson coordinates, as a homeomorphism onto the `S`-local product. -/
def poissonHomeomorph : PoissonS.Space K A.Sf ≃ₜ SLocalProduct K A.Sf where
  toEquiv := (NormalizedProbe.poissonLocalEquiv A).toEquiv
  continuous_toFun := ((sArchModel_comparison K).2.1.comp
      (mixedEmbedding.euclidean.toMixed K).continuous).prodMap continuous_id
  continuous_invFun := ((mixedEmbedding.euclidean.toMixed K).symm.continuous.comp
      (sArchModel_comparison K).1).prodMap continuous_id

theorem poissonHomeomorph_apply (z : PoissonS.Space K A.Sf) :
    poissonHomeomorph A z = ((R).symm (mixedEmbedding.euclidean.toMixed K z.1), z.2) :=
  rfl

/-- Axiom's phase at `-(x * y)` for `x` in Poisson coordinates, in the skeleton's terms. -/
theorem phase_poisson (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion K) Circle)
    (he : ∀ v z, (e v z : ℂ) = psiLocal K v.val z)
    (z : PoissonS.Space K A.Sf) (y : SLocalProduct K A.Sf) :
    ProbeAdditive.phase K A.Sf e (-(poissonHomeomorph A z) * y) =
      standardMixedAddCharacter K (-(mixedEmbedding.euclidean.toMixed K z.1 * (R) y.1)) *
        ∏ v, psiLocal K v.val (-(z.2 v * y.2 v)) := by
  unfold ProbeAdditive.phase
  congr 1
  · rw [← archPhase_symm A]
    congr 1
    apply (InfiniteAdeleRing.ringEquiv_mixedSpace K).injective
    rw [RingEquiv.apply_symm_apply, poissonHomeomorph_apply]
    simp only [Prod.fst_mul, Prod.fst_neg, map_mul, map_neg, RingEquiv.apply_symm_apply]
    ring
  · refine Finset.prod_congr rfl fun v _ => ?_
    rw [he, poissonHomeomorph_apply]
    simp only [Prod.snd_mul, Prod.snd_neg, Pi.mul_apply, Pi.neg_apply, neg_mul]

/-- **Fourier factorization.** Axiom's Fourier transform of `g ∘ R · ∏ f_v` for the
Poisson additive measure of `μ` is `2^{r₂}` times the skeleton's archimedean and local
Fourier transforms. -/
theorem fourier_eq (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion K) Circle)
    (he : ∀ v z, (e v z : ℂ) = psiLocal K v.val z)
    (μ : (v : ↥A.Sf) → Measure (v.val.adicCompletion K)) [∀ v, SigmaFinite (μ v)]
    (g : mixedEmbedding.mixedSpace K → ℂ) (f : (v : ↥A.Sf) → v.val.adicCompletion K → ℂ)
    (W0 : SLocalProduct K A.Sf → ℂ) (hW : ∀ x, W0 x = g ((R) x.1) * ∏ v, f v (x.2 v))
    (y : SLocalProduct K A.Sf) :
    ProbeWeight.fourier K A.Sf e (NormalizedProbe.poissonAdditiveMeasure A μ) W0 y =
      (PoissonArch.haarScalar K : ℂ) *
        NumberField.AdelicFourier.fourierIntegral (standardMixedAddCharacter K) volume g
          ((R) y.1) *
        ∏ v, NumberField.AdelicFourier.fourierIntegral (psiLocal K v.val) (μ v) (f v) (y.2 v) := by
  have hpt : ∀ z : PoissonS.Space K A.Sf,
      W0 (poissonHomeomorph A z) * ProbeAdditive.phase K A.Sf e (-(poissonHomeomorph A z) * y) =
        (g (mixedEmbedding.euclidean.toMixed K z.1) *
          standardMixedAddCharacter K (-(mixedEmbedding.euclidean.toMixed K z.1 * (R) y.1))) *
        ∏ v, (f v (z.2 v) * psiLocal K v.val (-(z.2 v * y.2 v))) := by
    intro z
    rw [hW, phase_poisson A e he, Finset.prod_mul_distrib, poissonHomeomorph_apply,
      RingEquiv.apply_symm_apply]
    ring
  unfold ProbeWeight.fourier NormalizedProbe.poissonAdditiveMeasure
  change ∫ x, W0 x * ProbeAdditive.phase K A.Sf e (-x * y) ∂(Measure.map (poissonHomeomorph A)
    (PoissonS.productMeasure K A.Sf μ)) = _
  rw [(poissonHomeomorph A).measurableEmbedding.integral_map]
  simp_rw [hpt]
  unfold PoissonS.productMeasure PoissonArch.traceMeasure
  rw [integral_prod_mul (fun a : mixedEmbedding.euclidean.mixedSpace K =>
      g (mixedEmbedding.euclidean.toMixed K a) *
        standardMixedAddCharacter K (-(mixedEmbedding.euclidean.toMixed K a * (R) y.1)))
    (fun b : (v : ↥A.Sf) → v.val.adicCompletion K =>
      ∏ v, (f v (b v) * psiLocal K v.val (-(b v * y.2 v)))),
    integral_smul_measure,
    (mixedEmbedding.euclidean.volumePreserving_toMixed K).integral_comp
      (mixedEmbedding.euclidean.toMixed K).toHomeomorph.measurableEmbedding
      (fun m => g m * standardMixedAddCharacter K (-(m * (R) y.1))),
    ENNReal.toReal_ofReal (PoissonArch.haarScalar_pos K).le, Complex.real_smul]
  have hpi := integral_fintype_prod_eq_prod (𝕜 := ℂ) (ι := ↥A.Sf)
    (E := fun v : ↥A.Sf => v.val.adicCompletion K) (μ := μ)
    (fun v (b : v.val.adicCompletion K) => f v b * psiLocal K v.val (-(b * y.2 v)))
  congr 1
  · congr 1
    unfold NumberField.AdelicFourier.fourierIntegral
    exact integral_congr_ae (Filter.Eventually.of_forall fun m => mul_comm _ _)
  · calc _ = ∏ v, ∫ b, f v b * psiLocal K v.val (-(b * y.2 v)) ∂μ v := hpi
      _ = _ := Finset.prod_congr rfl fun v _ => by
        unfold NumberField.AdelicFourier.fourierIntegral
        exact integral_congr_ae (Filter.Eventually.of_forall fun b => mul_comm _ _)

end ProbeFourier

end HeckeAxiom
