import HeckeSkeleton.Moments.MOM_INV_STEP.FirstProductionPoisson
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondAdaptiveProduction
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondProductionIntegral

/-!
# The actual first inverse energy reduced by the second Poisson step

The common second positive measure is used linearly after the elementary
two-root inequality. This permits all original first arithmetic sources
to be summed before their fixed-triple reconstruction is counted. The
only error terms below are the genuine additive zeros and the full
infinite frequency tail.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstSecondReduction

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools FirstParentRows FirstToSecondData
open scoped Classical BigOperators nonZeroDivisors

private theorem roots_le_half_sum (L R : ℝ) (hL : 0 ≤ L) (hR : 0 ≤ R) :
    Real.sqrt L * Real.sqrt R ≤ (L + R) / 2 := by
  nlinarith [sq_nonneg (Real.sqrt L - Real.sqrt R), Real.sq_sqrt hL, Real.sq_sqrt hR]

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "OS" => Set.integer Sset K
local notation "Varch" => mixedEmbedding.euclidean.mixedSpace K

variable {σ : Type*} [DecidableEq σ]
variable (T : FirstParentEnergy.Data K S (σ := σ))
variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
variable (hbase : 1 < T.columns.base)
variable (R : OuterIndex K S D T → {r : ℝ // 0 < r})
variable (U : {r : ℝ // 0 < r}) (J : Finset σ) (s : ℝ)
variable (H₂ : ∀ o : OuterIndex K S D T, (ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K)))) → Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)) → ℝ)

def errorAt (o : OuterIndex K S D T) (e : FirstOuterCenters.Overlap K S D T o) : ℝ :=
  let Q := data K S D T Θ ψ G hν hG hbase R U J s o e
  let a := DivisorInverseColumn.coefficient K S D Q.columns Q.triple Q.label.val.val Q.divisor.val
  ‖SecondPoissonSplit.additiveZeros K S D Γ hΓ μv a (Q.columns.columns Q.triple)
    Q.archTest Q.localTest Q.locallyConstant Q.compactSupport Q.radius‖ +
  ‖SecondAdaptiveCutoff.tailSourceAt K S D Γ hΓ μv a
    (Q.columns.columns Q.triple ×ˢ Q.columns.columns Q.triple)
    Q.archTest Q.localTest Q.locallyConstant Q.compactSupport Q.radius (H₂ o)‖

omit [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)] in
theorem errorAt_nonneg (o : OuterIndex K S D T)
    (e : FirstOuterCenters.Overlap K S D T o) :
    0 ≤ errorAt K S D Γ hΓ μv T Θ ψ G hν hG hbase R U J s H₂ o e := by
  exact add_nonneg (norm_nonneg _) (norm_nonneg _)

include hallowed ν μ in
/-- The second common-kernel constant is independent of every first
source, its physical scales, and its already frozen Mellin frequency. -/
theorem exists_pointwise_free_bound (ε : ℝ) (hε : 0 < ε) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {σ : Type*} [DecidableEq σ] (T : FirstParentEnergy.Data K S (σ := σ))
        (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
        (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
        (hbase : 1 < T.columns.base)
        (R : OuterIndex K S D T → {r : ℝ // 0 < r})
        (U : {r : ℝ // 0 < r}) (J : Finset σ) (s : ℝ)
        (H₂ : ∀ o : OuterIndex K S D T, Ext → Finset (HeightOneSpectrum OS) → ℝ),
      ThetaCalibrationInput K Sset D T.columns.lambda G →
      (∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset →
        UnramifiedAt K T.columns.background p) →
      (∀ k ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists k, Prime p) →
      ∀ (o : OuterIndex K S D T) (e : FirstOuterCenters.Overlap K S D T o),
      FirstFreeMellinEnergy.freeEnergyAt K S Γ D T.columns Θ ψ G hν hG J U.val
        (-(1 / 2 : ℝ)) (triple K S D T o e) (label K S D T o).val.val
        (FirstLocalizedEnergy.divisor K S D T o).val (R o) s ≤
      C / 2 *
        (SecondAdaptiveProduction.totalAt K S D Γ
          (data K S D T Θ ψ G hν hG hbase R U J s o e) (H₂ o) G hG ε m false +
         SecondAdaptiveProduction.totalAt K S D Γ
          (data K S D T Θ ψ G hν hG hbase R U J s o e) (H₂ o) G hG ε m true) +
      errorAt K S D Γ hΓ μv T Θ ψ G hν hG hbase R U J s H₂ o e := by
  let h := Physical.ActualGramMajorantDraft.rowBallFiniteFamily K S 1
  obtain ⟨q, A, hA, hb⟩ := SecondAdaptiveProduction.exists_retained_centered_bound
    K S D Γ μv ν hΓ hallowed h
    (Physical.ActualGramMajorantDraft.rowBallFiniteFamily_locallyConstant K S 1)
    (Physical.ActualGramMajorantDraft.rowBallFiniteFamily_compactSupport K S 1) ε hε m
  let C := A * q.sup (schwartzSeminormFamily ℝ Varch ℂ)
    (Physical.ActualGramMajorantDraft.rowBallArchTest K S 1)
  have hC : 0 ≤ C := mul_nonneg hA (apply_nonneg _ _)
  refine ⟨C, hC, ?_⟩
  intro σ _ T Θ ψ G hν hG hbase R U J s H₂ hcal hbg hprime o e
  let Q := data K S D T Θ ψ G hν hG hbase R U J s o e
  let a := DivisorInverseColumn.coefficient K S D Q.columns Q.triple Q.label.val.val Q.divisor.val
  let ret := SecondAdaptiveCutoff.retainedSourceAt K S D Γ hΓ μv a
    (Q.columns.columns Q.triple ×ˢ Q.columns.columns Q.triple)
    Q.archTest Q.localTest Q.locallyConstant Q.compactSupport Q.radius (H₂ o)
  let zeros := SecondPoissonSplit.additiveZeros K S D Γ hΓ μv a (Q.columns.columns Q.triple)
    Q.archTest Q.localTest Q.locallyConstant Q.compactSupport Q.radius
  let tail := SecondAdaptiveCutoff.tailSourceAt K S D Γ hΓ μv a
    (Q.columns.columns Q.triple ×ˢ Q.columns.columns Q.triple)
    Q.archTest Q.localTest Q.locallyConstant Q.compactSupport Q.radius (H₂ o)
  let L := SecondAdaptiveProduction.totalAt K S D Γ Q (H₂ o) G hG ε m false
  let E := SecondAdaptiveProduction.totalAt K S D Γ Q (H₂ o) G hG ε m true
  have hret : ‖ret‖ ≤ C * (Real.sqrt L * Real.sqrt E) := by
    apply hb Q rfl (H₂ o) G hG hcal
    · intro p hp
      change UnramifiedAt K (T.columns.background * G) p
      exact (hbg p hp).mul K (hcal.G_unramified p hp)
    · intro k hk p hp
      exact hprime k
        ((@Finset.mem_sdiff _ (fun a b => Classical.propDecidable (a = b)) _ _ _).mp hk).1 p hp
  have hroots := roots_le_half_sum L E
    (SecondAdaptiveProduction.totalAt_nonneg K S D Γ Q (H₂ o) G hG ε m false)
    (SecondAdaptiveProduction.totalAt_nonneg K S D Γ Q (H₂ o) G hG ε m true)
  have hbound : ‖ret‖ ≤ C / 2 * (L + E) :=
    (hret.trans (mul_le_mul_of_nonneg_left hroots hC)).trans_eq (by ring)
  have he := FirstProductionPoisson.first_free_split
    K S D Γ hΓ μv ν μ T Θ ψ G hν hG hbase R U J s H₂ o e
  change _ = (ret + zeros + tail).re at he
  rw [he]
  change (ret + zeros + tail).re ≤ C / 2 * (L + E) + (‖zeros‖ + ‖tail‖)
  exact (Complex.re_le_norm _).trans
    (((norm_add_le (ret + zeros) tail).trans
      (add_le_add (norm_add_le ret zeros) le_rfl)).trans
        (by linarith))

include hallowed ν μ in
/-- After the second two-root inequality, the whole first finite source
is linear in the two actual production totals. There is no second
count of the first arithmetic source or of the final frozen triples. -/
theorem exists_weighted_free_bound (ε : ℝ) (hε : 0 < ε) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {σ : Type*} [DecidableEq σ] (T : FirstParentEnergy.Data K S (σ := σ))
        (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
        (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
        (hbase : 1 < T.columns.base)
        (R : OuterIndex K S D T → {r : ℝ // 0 < r})
        (U : {r : ℝ // 0 < r}) (J : Finset σ) (s : ℝ)
        (H₂ : ∀ o : OuterIndex K S D T, Ext → Finset (HeightOneSpectrum OS) → ℝ),
      ThetaCalibrationInput K Sset D T.columns.lambda G →
      (∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset →
        UnramifiedAt K T.columns.background p) →
      (∀ k ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists k, Prime p) →
      ∀ (w : ∀ o : OuterIndex K S D T, FirstOuterCenters.Overlap K S D T o → ℝ),
      (∀ o e, 0 ≤ w o e) → ∀ side : Bool,
      (∑ o : OuterIndex K S D T, ∑ e : FirstOuterCenters.Overlap K S D T o,
        w o e * ‖SecondProductionIntegral.firstMark K S D T J side o e‖ ^ 2 *
        FirstFreeMellinEnergy.freeEnergyAt K S Γ D T.columns Θ ψ G hν hG J U.val
          (-(1 / 2 : ℝ)) (triple K S D T o e) (label K S D T o).val.val
          (FirstLocalizedEnergy.divisor K S D T o).val (R o) s) ≤
      C / 2 *
        (SecondProductionIntegral.actualTotal K S D Γ T Θ ψ G hν hG hbase R U J s H₂
          w ε side m false +
         SecondProductionIntegral.actualTotal K S D Γ T Θ ψ G hν hG hbase R U J s H₂
          w ε side m true) +
      ∑ o : OuterIndex K S D T, ∑ e : FirstOuterCenters.Overlap K S D T o,
        w o e * ‖SecondProductionIntegral.firstMark K S D T J side o e‖ ^ 2 *
        errorAt K S D Γ hΓ μv T Θ ψ G hν hG hbase R U J s H₂ o e := by
  obtain ⟨C, hC, hb⟩ := exists_pointwise_free_bound K S D Γ hΓ hallowed μv ν μ ε hε m
  refine ⟨C, hC, ?_⟩
  intro σ _ T Θ ψ G hν hG hbase R U J s H₂ hcal hbg hprime w hw side
  have hpoint := hb T Θ ψ G hν hG hbase R U J s H₂ hcal hbg hprime
  calc
    _ ≤ ∑ o : OuterIndex K S D T, ∑ e : FirstOuterCenters.Overlap K S D T o,
        w o e * ‖SecondProductionIntegral.firstMark K S D T J side o e‖ ^ 2 *
          (C / 2 *
            (SecondAdaptiveProduction.totalAt K S D Γ
              (data K S D T Θ ψ G hν hG hbase R U J s o e) (H₂ o) G hG ε m false +
             SecondAdaptiveProduction.totalAt K S D Γ
              (data K S D T Θ ψ G hν hG hbase R U J s o e) (H₂ o) G hG ε m true) +
            errorAt K S D Γ hΓ μv T Θ ψ G hν hG hbase R U J s H₂ o e) := by
      apply Finset.sum_le_sum
      intro o ho
      apply Finset.sum_le_sum
      intro e he
      exact mul_le_mul_of_nonneg_left (hpoint o e) (mul_nonneg (hw o e) (sq_nonneg _))
    _ = _ := by
      simp only [SecondProductionIntegral.actualTotal, mul_add, ← Finset.sum_add_distrib,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun e _ => ?_
      ring

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstSecondReduction

end

