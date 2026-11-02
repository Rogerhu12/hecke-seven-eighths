import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondZeroDivisor
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.EmptyGaussMask
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.GaussPhaseTerminal

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Signed second zero from the original individual coefficients

The two inverse column norms are retained literally. Their product
pays the original-origin modulus product, while the Euler diagonal
retains one inverse column norm. The first Fourier phase has norm one
on each original coefficient. These facts give a uniform bound for the
actual phase stage, with both signed contributions and its first
residual divisor still present.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory UniqueFactorizationMonoid
open HeckePort.IdealMobiusDivisorSum HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- This is an individual original Gram profile calculation. The
origin contributes the literal `1`, after the two inverse norms cancel. -/
theorem gram_signed_normalization
    (seminorms : Finset (ℕ × ℕ)) (φ : SchwartzMap V ℂ)
    (c d : ℂ) (NI NJ r L B : ℝ)
    (hNI : 0 < NI) (hNJ : 0 < NJ) (hr : 0 ≤ r) (hL : 0 < L)
    (hB : 0 ≤ B) (hlower : L ≤ NJ)
    (hc : ‖c‖ * NI ≤ B) (hd : ‖d‖ * NJ ≤ B) :
    seminorms.sup (schwartzSeminormFamily ℂ V ℂ) ((c * star d) • φ) *
        (r * NI + NI * NJ) ≤
      seminorms.sup (schwartzSeminormFamily ℂ V ℂ) φ * B ^ 2 * (r / L + 1) := by
  have hs : 0 ≤ seminorms.sup (schwartzSeminormFamily ℂ V ℂ) φ := apply_nonneg _ _
  have hpair : (‖c‖ * NI) * (‖d‖ * NJ) ≤ B ^ 2 := by
    simpa only [pow_two] using mul_le_mul hc hd
      (mul_nonneg (norm_nonneg _) hNJ.le) hB
  have hratio : r / NJ + 1 ≤ r / L + 1 := by
    simpa only [add_comm] using
      add_le_add_right (div_le_div_of_nonneg_left hr hL hlower) 1
  calc
    _ = seminorms.sup (schwartzSeminormFamily ℂ V ℂ) φ *
        ((‖c‖ * NI) * (‖d‖ * NJ)) * (r / NJ + 1) := by
      rw [map_smul_eq_mul, norm_mul, norm_star]
      field_simp [ne_of_gt hNJ]
      <;> ring
    _ ≤ seminorms.sup (schwartzSeminormFamily ℂ V ℂ) φ * B ^ 2 *
        (r / NJ + 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpair hs)
        (add_nonneg (div_nonneg hr hNJ.le) zero_le_one)
    _ ≤ _ := mul_le_mul_of_nonneg_left hratio (mul_nonneg hs (sq_nonneg B))

section GeneralStage

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- All constants precede the actual source and the first Fourier
parameter. Only original single-column bounds, an actual factor map
and its finite fibres are supplied; no terminal estimate is an input. -/
theorem second_signed_stage_bound_uniform
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (φ : SchwartzMap V ℂ) (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ Cbound : ℝ, 0 < Cbound ∧
    ∀ (C : A.GeneralArithmeticContext σ η hS) {ι : Type*}
      (G : ActualGaussSource C ι)
      (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
        HeckeGeneral.Characters.localDifferentExponent K v = 0)
      (stage : ActualGaussStage (E := ℝ) hΓ μv hDiff G finiteTest),
    stage.profile = φ → stage.mask = ∅ →
    ∀ (factors : ι × ι → Fin k → Ideal (𝓞 K)) (multiplicity : ℕ),
    (∀ v, ((G.columns ×ˢ G.columns).filter (fun ij => factors ij = v)).card ≤ multiplicity) →
    (∀ ij ∈ G.columns ×ˢ G.columns, PowerfulDiagonal.tupleIdeal (factors ij) =
      (G.ideal ij.1).val * (G.ideal ij.2).val) →
    ∀ (S : Ideal (𝓞 K)), Squarefree S →
    (∀ i ∈ G.columns, G.coefficient i ≠ 0 → S ∣ (G.ideal i).val) →
    ∀ N L B : ℝ, 1 ≤ N → 0 < L → 0 ≤ B →
    (∀ ij ∈ G.columns ×ˢ G.columns,
      G.coefficient ij.1 ≠ 0 → G.coefficient ij.2 ≠ 0 →
      (Ideal.absNorm ((G.ideal ij.1).val * (G.ideal ij.2).val) : ℝ) ≤ N) →
    (∀ i ∈ G.columns, G.coefficient i ≠ 0 → L ≤ A.exteriorNorm (G.ideal i)) →
    (∀ i ∈ G.columns, ‖G.coefficient i‖ * A.exteriorNorm (G.ideal i) ≤ B) →
    ∀ u : ι → ℂ, (∀ i, ‖u i‖ = 1) →
    (stage.withMultiplier u).rawZeroCost ≤
      Cbound * multiplicity * B ^ 2 * (stage.radius.val⁻¹ / L + 1) *
        Real.sqrt N * N ^ ε / (Ideal.absNorm S : ℝ) := by
  obtain ⟨seminorms, Czero, hCzero, hzero⟩ :=
    second_signedZero_diagonal_supported_of_squarefree_divisor
      (σ := σ) hΓ μv finiteTest k ε hε
  let P := seminorms.sup (schwartzSeminormFamily ℂ V ℂ) φ
  have hP : 0 ≤ P := apply_nonneg _ _
  refine ⟨Czero * (1 + P), mul_pos hCzero (by linarith), ?_⟩
  intro C ι G hDiff stage hφ hmask factors multiplicity hfiber hfactor
    S hSsquare hdiv N L B hN hL hB hnorm hlower hcoefficient u hu
  let profiles := fun i j => ((u i * G.coefficient i) *
    star (u j * G.coefficient j)) • stage.profile
  let blocks := fun DE : FirstZeroLabel G.columns G.columns G.ideal G.ideal =>
    canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property
  let Amp := P * B ^ 2 * (stage.radius.val⁻¹ / L + 1) * Real.sqrt N
  have hAmp : 0 ≤ Amp := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hP (sq_nonneg B))
      (add_nonneg (div_nonneg (inv_nonneg.mpr stage.radius.property.le) hL.le)
        zero_le_one)) (Real.sqrt_nonneg N)
  have hactive (i j : ι) (hnz : profiles i j ≠ 0) :
      G.coefficient i ≠ 0 ∧ G.coefficient j ≠ 0 := by
    constructor
    · intro hz
      apply hnz
      simp only [profiles, hz, mul_zero, zero_mul, zero_smul]
    · intro hz
      apply hnz
      simp only [profiles, hz, mul_zero, star_zero, zero_smul]
  have hcop (a : A.R) (D : Finset (HeightOneSpectrum A.R))
      (hD : D ∈ stage.mask.powerset) :
      IsCoprime a (sIntegerMaskGenerator K
        (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val := by
    have he : D = ∅ := by
      simpa only [hmask, Finset.powerset_empty, Finset.mem_singleton] using hD
    rw [he]
    exact emptyMask_column_coprime K A.Sf a
  have hweight : firstZeroDivisorWeight (K := K) (S := A.Sf) stage.radius ∅ =
      stage.radius.val⁻¹ := by
    simp only [firstZeroDivisorWeight, IdealMobiusMask.primeProduct, Finset.prod_empty,
      moebius_one, Int.cast_one, norm_one, sIntegerMaskDilationRadius_empty, one_mul]
  have hprofile (v) (hv : v ∈ firstZeroPairs G.columns G.columns G.ideal G.ideal) :
      seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
        (∑ D ∈ stage.mask.powerset,
          (firstZeroDivisorWeight stage.radius D * A.exteriorNorm (G.ideal v.2.1) +
            ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ *
              A.exteriorNorm (G.ideal v.2.1) * A.exteriorNorm (G.ideal v.2.2))) ≤
        Amp / Real.sqrt N := by
    have hm := (mem_firstZeroPairs G.columns G.columns G.ideal G.ideal v).mp hv
    have hsqrt : Real.sqrt N ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr
      (zero_lt_one.trans_le hN))
    have hAmpEq : Amp / Real.sqrt N = P * B ^ 2 *
        (stage.radius.val⁻¹ / L + 1) := by
      exact mul_div_cancel_right₀ _ hsqrt
    rw [hAmpEq, hmask]
    simp only [Finset.powerset_empty, Finset.sum_singleton, hweight,
      IdealMobiusMask.primeProduct, Finset.prod_empty, moebius_one,
      Int.cast_one, norm_one, one_mul]
    change seminorms.sup (schwartzSeminormFamily ℂ V ℂ)
      (((u v.2.1 * G.coefficient v.2.1) * star (u v.2.2 * G.coefficient v.2.2)) •
        stage.profile) * _ ≤ _
    rw [original_gram_seminorm_unit_multipliers seminorms _ _ _ _
      (hu v.2.1) (hu v.2.2), hφ]
    by_cases hjzero : G.coefficient v.2.2 = 0
    · simp only [hjzero, star_zero, mul_zero, zero_smul, map_zero, zero_mul]
      exact mul_nonneg (mul_nonneg hP (sq_nonneg B))
        (add_nonneg (div_nonneg (inv_nonneg.mpr stage.radius.property.le) hL.le)
          zero_le_one)
    · exact gram_signed_normalization seminorms φ _ _ _ _ _ L B
        (A.exteriorNorm_pos _) (A.exteriorNorm_pos _)
        (inv_nonneg.mpr stage.radius.property.le) hL hB
        (hlower _ hm.2.1 hjzero) (hcoefficient _ hm.1) (hcoefficient _ hm.2.1)
  have hz := hzero C G.columns G.columns G.ideal G.ideal blocks profiles hDiff
    stage.radius stage.mask stage.cutoff stage.cutoff_one factors multiplicity hfiber hfactor
    S hSsquare (fun ij hij hnz => hdiv ij.1 (Finset.mem_product.mp hij).1
      (hactive ij.1 ij.2 hnz).1) N Amp hN hAmp
    (fun ij hij hnz => hnorm ij hij (hactive ij.1 ij.2 hnz).1 (hactive ij.1 ij.2 hnz).2)
    (fun _ _ _ D hD => hcop _ D hD) (fun _ _ _ D hD => hcop _ D hD) hprofile
  change (stage.withMultiplier u).rawZeroCost ≤ _ at hz
  have hpay : 0 ≤ ((multiplicity : ℝ) * B ^ 2 * (stage.radius.val⁻¹ / L + 1) *
      Real.sqrt N * N ^ ε / (Ideal.absNorm S : ℝ)) := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (sq_nonneg B)) (add_nonneg
        (div_nonneg (inv_nonneg.mpr stage.radius.property.le) hL.le) zero_le_one))
      (Real.sqrt_nonneg N)) (Real.rpow_nonneg (zero_le_one.trans hN) ε)
  calc
    _ ≤ Czero * multiplicity * Amp * N ^ ε / (Ideal.absNorm S : ℝ) := hz
    _ = (Czero * P) * ((multiplicity : ℝ) * B ^ 2 * (stage.radius.val⁻¹ / L + 1) *
        Real.sqrt N * N ^ ε / (Ideal.absNorm S : ℝ)) := by dsimp only [Amp]; ring
    _ ≤ (Czero * (1 + P)) *
        ((multiplicity : ℝ) * B ^ 2 * (stage.radius.val⁻¹ / L + 1) *
          Real.sqrt N * N ^ ε / (Ideal.absNorm S : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith : P ≤ 1 + P) hCzero.le) hpay
    _ = _ := by ring

end GeneralStage

section OriginalSource

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

open EngineInduction EngineInduction.Source
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

/-- Apply the signed estimate to the literal V2 source and integrate
its genuine first Fourier phase. The only mass introduced is the
total mass of that source's original first Fourier measure. -/
theorem second_source_zero_bound_uniform
    (c : TargetContext K) (p : SourceParameters c)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ Cbound : ℝ, 0 < Cbound ∧
    ∀ {call : Call c} (source : SecondSource call p), source.Realizes →
    ∀ (factors : source.physical.Column × source.physical.Column → Fin k → Ideal (𝓞 K))
      (multiplicity : ℕ),
    (∀ v, ((source.physical.source.columns ×ˢ source.physical.source.columns).filter
      (fun ij => factors ij = v)).card ≤ multiplicity) →
    (∀ ij ∈ source.physical.source.columns ×ˢ source.physical.source.columns,
      PowerfulDiagonal.tupleIdeal (factors ij) =
        (source.physical.source.ideal ij.1).val * (source.physical.source.ideal ij.2).val) →
    Squarefree source.physical.first.residualDivisor.val →
    (∀ i ∈ source.physical.source.columns, source.physical.source.coefficient i ≠ 0 →
      source.physical.first.residualDivisor.val ∣ (source.physical.source.ideal i).val) →
    ∀ N L B : ℝ, 1 ≤ N → 0 < L → 0 ≤ B →
    (∀ ij ∈ source.physical.source.columns ×ˢ source.physical.source.columns,
      source.physical.source.coefficient ij.1 ≠ 0 →
      source.physical.source.coefficient ij.2 ≠ 0 →
      (Ideal.absNorm ((source.physical.source.ideal ij.1).val *
        (source.physical.source.ideal ij.2).val) : ℝ) ≤ N) →
    (∀ i ∈ source.physical.source.columns, source.physical.source.coefficient i ≠ 0 →
      L ≤ (Arithmetic.data c).exteriorNorm (source.physical.source.ideal i)) →
    (∀ i ∈ source.physical.source.columns,
      ‖source.physical.source.coefficient i‖ *
        (Arithmetic.data c).exteriorNorm (source.physical.source.ideal i) ≤ B) →
    source.zero ≤ source.physical.outerWeight * source.physical.orbitMultiplicity *
      (actualFourierMeasure source.physical.firstKernel).real Set.univ *
      (Cbound * multiplicity * B ^ 2 *
        (source.physical.first.retainedScale * call.base ^ source.physical.enlargement / L + 1) *
        Real.sqrt N * N ^ ε / (Ideal.absNorm source.physical.first.residualDivisor.val : ℝ)) := by
  obtain ⟨Cbound, hCbound, hstage⟩ := @second_signed_stage_bound_uniform K _ _
    (Arithmetic.data c) (Arithmetic.embedding c) (Arithmetic.choice c).η (Arithmetic.choice c).hS
    (Arithmetic.unitSubgroup c) inferInstance (Arithmetic.units_are_sixth c)
    (sourcePrincipal c) (sourceNormOneSpace c) (sourceNormOneBorel c)
    (Expansion.ActualProbeContext.localCompletionSpace K)
    (Expansion.ActualProbeContext.localCompletionBorel K)
    (Arithmetic.localMeasures (K := K))
    (Expansion.ActualProbeContext.allLocalMeasures_isAddHaar K)
    (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)
    (CanonicalRowBall.archTest K (Arithmetic.data c).Sf 1) k ε hε
  refine ⟨Cbound, hCbound, ?_⟩
  intro call source hsource factors multiplicity hfiber hfactor hSsquare hdiv
    N L B hN hL hB hnorm hlower hcoefficient
  let bound := Cbound * multiplicity * B ^ 2 *
    (source.stage.radius.val⁻¹ / L + 1) * Real.sqrt N * N ^ ε /
      (Ideal.absNorm source.physical.first.residualDivisor.val : ℝ)
  have hpoint (x : ℝ) : (source.phaseStage x).rawZeroCost ≤ bound :=
    hstage (Arithmetic.context c) source.physical.source (Arithmetic.different c)
      source.stage hsource.profile hsource.mask factors multiplicity hfiber hfactor
      source.physical.first.residualDivisor.val hSsquare hdiv N L B hN hL hB
      hnorm hlower hcoefficient (fun i => jointPhase x (source.physical.firstPoint i))
      (fun i => norm_jointPhase x (source.physical.firstPoint i))
  letI : IsFiniteMeasure (actualFourierMeasure source.physical.firstKernel) :=
    actualFourierMeasure_finite source.physical.firstKernel
  have hint :
      (∫ x, (source.phaseStage x).rawZeroCost ∂actualFourierMeasure source.physical.firstKernel) ≤
        (actualFourierMeasure source.physical.firstKernel).real Set.univ * bound := by
    have h := integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun x => (source.phaseStage x).rawZeroCost_nonneg))
      (integrable_const bound) (Filter.Eventually.of_forall hpoint)
    simpa only [integral_const, smul_eq_mul] using h
  have hradius : source.stage.radius.val⁻¹ =
      source.physical.first.retainedScale * call.base ^ source.physical.enlargement := by
    rw [hsource.radius, inv_inv]
  calc
    source.zero ≤ source.physical.outerWeight * (source.stage.fiber : ℝ) *
        ((actualFourierMeasure source.physical.firstKernel).real Set.univ * bound) :=
      mul_le_mul_of_nonneg_left hint
        (mul_nonneg source.physical.outerWeight_nonneg (Nat.cast_nonneg _))
    _ = _ := by rw [hsource.fiber]; dsimp only [bound]; rw [hradius]; ring

end OriginalSource

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof
