import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCenteredErrorIntegrals

/-!
# Integrability of the actual second errors under the first spectral measure

The source weights have exactly frequency-independent norms.  Finite
source sums therefore have an actual uniform majorant for every fixed
geometry.  Together with their proved continuity this gives the inner
Mellin and outer Fourier integrability used by the complete reduction.
No coefficient-size, principal-source, or tail estimate is assumed.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstErrorIntegrability

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
  HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalBlock CanonicalNormPools
  FirstCenteredFamily FirstCenteredErrors FirstCommonEnvelope CommonKernel
  FirstCenteredErrorIntegrals
open scoped Classical BigOperators nonZeroDivisors Topology

/-- All integrability certificates needed to integrate a bounded
continuous nonnegative error twice. -/
theorem spectral_integrability (ρ : SchwartzMap ℝ ℂ) (m : ℕ)
    (coordinate : LogPlane → ℝ) (hc : Continuous coordinate)
    (F : ℝ → ℝ) (hF : Continuous F) (hF0 : ∀ t, 0 ≤ F t)
    (E : ℝ) (hbound : ∀ t, F t ≤ E) :
    (∀ s : ℝ, Integrable (fun t : ℝ => ‖ρ t‖ * F (t + s))) ∧
    Integrable (fun ξ : LogPlane =>
      frequencyEnvelope m ξ * ∫ t : ℝ, ‖ρ t‖ * F (t + coordinate ξ)) := by
  let A : ℝ → ℝ := fun s => ∫ t : ℝ, ‖ρ t‖ * F (t + s)
  have hi (s : ℝ) : Integrable (fun t : ℝ => ‖ρ t‖ * F (t + s)) := by
    apply ρ.integrable.norm.mul_bdd (c := E)
      (hF.comp (continuous_id.add continuous_const)).aestronglyMeasurable
    filter_upwards [] with t
    change ‖F (t + s)‖ ≤ E
    rw [Real.norm_of_nonneg (hF0 _)]
    exact hbound _
  have hA0 (s : ℝ) : 0 ≤ A s :=
    integral_nonneg (fun t => mul_nonneg (norm_nonneg _) (hF0 _))
  have hAbound (s : ℝ) : A s ≤ (∫ t : ℝ, ‖ρ t‖) * E := by
    have hb := integral_mono (hi s) (ρ.integrable.norm.mul_const E)
      (fun t => mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _))
    rwa [integral_mul_const] at hb
  have hAc : Continuous A := by
    apply continuous_of_dominated (fun s => (hi s).aestronglyMeasurable)
      (bound := fun t => ‖ρ t‖ * E)
    · intro s
      filter_upwards [] with t
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (hF0 _))]
      exact mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)
    · exact ρ.integrable.norm.mul_const E
    · filter_upwards [] with t
      exact continuous_const.mul (hF.comp (continuous_const.add continuous_id))
  refine ⟨hi, ?_⟩
  apply (frequencyEnvelope_integrable m).mul_bdd
    (c := (∫ t : ℝ, ‖ρ t‖) * E) (hAc.comp hc).aestronglyMeasurable
  filter_upwards [] with ξ
  change ‖A (coordinate ξ)‖ ≤ (∫ t : ℝ, ‖ρ t‖) * E
  rw [Real.norm_of_nonneg (hA0 _)]
  exact hAbound _

private theorem finite_source_bounded {ι : Type*} (P : Finset ι)
    (A : ℝ → ι → ℂ) (B : ι → ℂ)
    (hA : ∀ t i, ‖A t i‖ = ‖A 0 i‖) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ t : ℝ, ‖∑ i ∈ P, A t i * B i‖ ≤ E := by
  refine ⟨∑ i ∈ P, ‖A 0 i‖ * ‖B i‖,
    Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)), ?_⟩
  intro t
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro i hi
  rw [norm_mul, hA]

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
  [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset

variable {σ : Type*} (C : ColumnData K S σ)
variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ C.background) (hG : G ∈ Θ)
variable (J : Finset σ) (γ : OuterTriple K) (j : Ideal (𝓞 K))
  (d : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) (U a : ℝ)

theorem sourceWeight_norm_eq_zero (p : Ext × Ext) (t : ℝ) :
    ‖SecondPoissonSplit.sourceWeight K S
      (DivisorInverseColumn.coefficient K S D
        (family K S C Θ ψ G hν hG J U a t) γ j d) p‖ =
    ‖SecondPoissonSplit.sourceWeight K S
      (DivisorInverseColumn.coefficient K S D
        (family K S C Θ ψ G hν hG J U a 0) γ j d) p‖ := by
  simp only [SecondPoissonSplit.sourceWeight, norm_mul, norm_star,
    FirstCenteredMellinEnergy.coefficient_norm_eq_zero]

variable (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
variable (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
variable (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
variable (r : {r : ℝ // 0 < r})

/-- Boundedness follows from the actual finite source and the exact
norm-one frequency phases; no geometric window is required. -/
theorem principalCost_bounded :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ t : ℝ,
      principalCost K S D Γ hΓ μv C Θ ψ G hν hG J γ j d U a t φ h hlc hcs r ≤ E := by
  let N := squarefreePool K Sset (2 * U)
  let A : ℝ → Ext × Ext → ℂ := fun t =>
    SecondPoissonSplit.sourceWeight K S
      (DivisorInverseColumn.coefficient K S D (family K S C Θ ψ G hν hG J U a t) γ j d)
  have hA (t : ℝ) (p : Ext × Ext) : ‖A t p‖ = ‖A 0 p‖ :=
    sourceWeight_norm_eq_zero K S D C Θ ψ G hν hG J γ j d U a p t
  let Bp : Ext × Ext → ℂ := fun p =>
    (SecondPoissonSplit.pairBlock K S D Γ hΓ p φ h hlc hcs r).physical
  let Bz : Ext × Ext → ℂ := fun p =>
    CanonicalPoissonSplit.pairPrincipal K S D Γ hΓ μv
      (FirstInversePoisson.unitIdeal K S, p.1) (FirstInversePoisson.unitIdeal K S, p.2)
      φ h hlc hcs ∅ r
  obtain ⟨Ep,hEp,hp⟩ := finite_source_bounded (SecondPoissonSplit.principalPairs K S D N) A Bp hA
  obtain ⟨Ez,hEz,hz⟩ := finite_source_bounded (N ×ˢ N) A Bz hA
  refine ⟨2 * Ep + Ez, add_nonneg (mul_nonneg (by norm_num) hEp) hEz, ?_⟩
  intro t
  exact add_le_add (mul_le_mul_of_nonneg_left (hp t) (by norm_num : (0 : ℝ) ≤ 2)) (hz t)

theorem tailCost_bounded (P : Finset (Ext × Ext)) (Z tau : ℝ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ t : ℝ,
      tailCost K S D Γ hΓ μv C Θ ψ G hν hG J γ j d P U a t Z tau φ h hlc hcs r ≤ E := by
  let A : ℝ → Ext × Ext → ℂ := fun t =>
    SecondPoissonSplit.sourceWeight K S
      (DivisorInverseColumn.coefficient K S D (family K S C Θ ψ G hν hG J U a t) γ j d)
  have hA (t : ℝ) (p : Ext × Ext) : ‖A t p‖ = ‖A 0 p‖ :=
    sourceWeight_norm_eq_zero K S D C Θ ψ G hν hG J γ j d U a p t
  let B : Ext × Ext → ℂ := fun p =>
    CanonicalAdaptiveTail.dualTail K S D Γ μv
      (SecondPoissonSplit.pairBlock K S D Γ hΓ p φ h hlc hcs r)
      (SecondAdaptiveCutoff.fineCutoff K S r U Z tau
        (ActualInverseFactors.common K Sset p.1 p.2))
  exact finite_source_bounded P A B hA

/-- Inner Mellin and outer Fourier integrability for the actual
complete principal cost, with arbitrary positive physical radius. -/
theorem principalCost_integrable (ρ : SchwartzMap ℝ ℂ) (m : ℕ)
    (coordinate : LogPlane → ℝ) (hc : Continuous coordinate) :
    (∀ s : ℝ, Integrable (fun t : ℝ => ‖ρ t‖ *
      principalCost K S D Γ hΓ μv C Θ ψ G hν hG J γ j d U a (t + s) φ h hlc hcs r)) ∧
    Integrable (fun ξ : LogPlane => frequencyEnvelope m ξ *
      ∫ t : ℝ, ‖ρ t‖ * principalCost K S D Γ hΓ μv C Θ ψ G hν hG J γ j d U a
        (t + coordinate ξ) φ h hlc hcs r) := by
  obtain ⟨E,hE,hb⟩ := principalCost_bounded K S D Γ hΓ μv C Θ ψ G hν hG J γ j d U a φ h hlc hcs r
  exact spectral_integrability ρ m coordinate hc _
    (principalCost_continuous K S D Γ hΓ μv C Θ ψ G hν hG J γ j d U a φ h hlc hcs r)
    (fun t => principalCost_nonneg K S D Γ hΓ μv C Θ ψ G hν hG J γ j d U a t φ h hlc hcs r)
    E hb

/-- The actual infinite tail is evaluated before taking its finite
source sum. Its source-local cutoff is fixed independently of both
spectral frequencies, as required for this integrability statement. -/
theorem tailCost_integrable (P : Finset (Ext × Ext)) (Z tau : ℝ)
    (ρ : SchwartzMap ℝ ℂ) (m : ℕ) (coordinate : LogPlane → ℝ)
    (hc : Continuous coordinate) :
    (∀ s : ℝ, Integrable (fun t : ℝ => ‖ρ t‖ *
      tailCost K S D Γ hΓ μv C Θ ψ G hν hG J γ j d P U a (t + s) Z tau φ h hlc hcs r)) ∧
    Integrable (fun ξ : LogPlane => frequencyEnvelope m ξ *
      ∫ t : ℝ, ‖ρ t‖ * tailCost K S D Γ hΓ μv C Θ ψ G hν hG J γ j d P U a
        (t + coordinate ξ) Z tau φ h hlc hcs r) := by
  obtain ⟨E,hE,hb⟩ := tailCost_bounded K S D Γ hΓ μv C Θ ψ G hν hG J γ j d U a φ h hlc hcs r P Z tau
  exact spectral_integrability ρ m coordinate hc _
    (tailCost_continuous K S D Γ hΓ μv C Θ ψ G hν hG J γ j d U a φ h hlc hcs r P Z tau)
    (fun t => norm_nonneg _) E hb

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstErrorIntegrability

end

