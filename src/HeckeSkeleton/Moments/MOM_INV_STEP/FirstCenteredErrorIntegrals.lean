import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCenteredErrors
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstErrorIntegration

/-!
# Integrating the actual second errors under the first spectral measure

The error functions are the literal finite second sources, as functions
of the combined Mellin/Fourier frequency. Their continuity and the
proved uniform bounds establish all integrability. The common spectral
cost is exactly one Fourier mass and one Mellin L¹ mass here; the other
Mellin L¹ mass remains in the original first Cauchy factor.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstCenteredErrorIntegrals

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
  HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalBlock CanonicalNormPools
  FirstCenteredFamily FirstCenteredErrors FirstCommonEnvelope CommonKernel
  FirstErrorIntegration
open scoped Classical BigOperators nonZeroDivisors Topology

def spectralAverage (ρ : SchwartzMap ℝ ℂ) (m : ℕ)
    (coordinate : LogPlane → ℝ) (F : ℝ → ℝ) : ℝ :=
  ∫ ξ : LogPlane, frequencyEnvelope m ξ * ∫ t : ℝ, ‖ρ t‖ * F (t + coordinate ξ)

/-- The analytic comparison used below; its hypotheses will be
discharged by the actual finite principal and tail sources. -/
theorem spectralAverage_le (ρ : SchwartzMap ℝ ℂ) (m : ℕ)
    (coordinate : LogPlane → ℝ) (hcoordinate : Continuous coordinate)
    (F : ℝ → ℝ) (hF : Continuous F) (hF0 : ∀ t, 0 ≤ F t)
    (E : ℝ) (hE : 0 ≤ E) (hbound : ∀ t, F t ≤ E) :
    spectralAverage ρ m coordinate F ≤
      fourierMass m * (∫ t : ℝ, ‖ρ t‖) * E := by
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
  have houter : Integrable (fun ξ : LogPlane => frequencyEnvelope m ξ * A (coordinate ξ)) := by
    apply (frequencyEnvelope_integrable m).mul_bdd
      (c := (∫ t : ℝ, ‖ρ t‖) * E) (hAc.comp hcoordinate).aestronglyMeasurable
    filter_upwards [] with ξ
    change ‖A (coordinate ξ)‖ ≤ (∫ t : ℝ, ‖ρ t‖) * E
    rw [Real.norm_of_nonneg (hA0 _)]
    exact hAbound _
  have hb := integral_mono houter
    ((frequencyEnvelope_integrable m).mul_const ((∫ t : ℝ, ‖ρ t‖) * E))
    (fun ξ => mul_le_mul_of_nonneg_left (hAbound _) (frequencyEnvelope_nonneg m ξ))
  rw [integral_mul_const] at hb
  exact hb.trans_eq (by unfold fourierMass; ring)

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
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

section Continuity

variable {σ : Type*} (C : ColumnData K S σ)
variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ C.background) (hG : G ∈ Θ)
variable (J : Finset σ) (γ : OuterTriple K) (j : Ideal (𝓞 K))
  (d : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) (U a : ℝ)

theorem sourceWeight_continuous (p : Ext × Ext) :
    Continuous (fun t : ℝ => SecondPoissonSplit.sourceWeight K S
      (DivisorInverseColumn.coefficient K S D (family K S C Θ ψ G hν hG J U a t) γ j d) p) := by
  have hc (n : Ext) : Continuous (fun t : ℝ =>
      DivisorInverseColumn.coefficient K S D (family K S C Θ ψ G hν hG J U a t) γ j d n) := by
    simpa only [add_zero] using FirstCenteredMellinEnergy.coefficient_continuous
      K S D C Θ ψ G hν hG J U a γ j d n 0
  exact (hc p.1).star.mul (hc p.2)

variable (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
variable (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
variable (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
variable (r : {r : ℝ // 0 < r})

theorem principalCost_continuous :
    Continuous (fun t : ℝ =>
      principalCost K S D Γ hΓ μv C Θ ψ G hν hG J γ j d U a t φ h hlc hcs r) := by
  have hp : Continuous (fun t : ℝ => SecondPoissonSplit.physicalPrincipal K S D Γ hΓ
      (DivisorInverseColumn.coefficient K S D (family K S C Θ ψ G hν hG J U a t) γ j d)
      (squarefreePool K Sset (2 * U)) φ h hlc hcs r) := by
    unfold SecondPoissonSplit.physicalPrincipal
    apply continuous_finsetSum
    intro p hp
    exact (sourceWeight_continuous K S D C Θ ψ G hν hG J γ j d U a p).mul_const _
  have hz : Continuous (fun t : ℝ => SecondPoissonSplit.additiveZeros K S D Γ hΓ μv
      (DivisorInverseColumn.coefficient K S D (family K S C Θ ψ G hν hG J U a t) γ j d)
      (squarefreePool K Sset (2 * U)) φ h hlc hcs r) := by
    unfold SecondPoissonSplit.additiveZeros
    apply continuous_finsetSum
    intro p hp
    exact (sourceWeight_continuous K S D C Θ ψ G hν hG J γ j d U a p).mul_const _
  exact (hp.norm.const_mul 2).add hz.norm

theorem tailCost_continuous (P : Finset (Ext × Ext)) (Z tau : ℝ) :
    Continuous (fun t : ℝ =>
      tailCost K S D Γ hΓ μv C Θ ψ G hν hG J γ j d P U a t Z tau φ h hlc hcs r) := by
  unfold tailCost SecondAdaptiveCutoff.tailSourceAt
  apply Continuous.norm
  apply continuous_finsetSum
  intro p hp
  exact (sourceWeight_continuous K S D C Θ ψ G hν hG J γ j d U a p).mul_const _

end Continuity

/-- The actual principal error is integrated, not an assumed
frequency-independent principal bound. The chosen A is the same for
all original tests W, both frequencies, centers, labels and rows. -/
theorem exists_principal_integral_bound
    (slotCap : ℕ) (Hmax Umax loss a : ℝ)
    (hHmax : 0 ≤ Hmax) (hUmax : 0 ≤ Umax) (hloss : 0 < loss)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {σ : Type*} (C : ColumnData K S σ)
      (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
      (hν : BackgroundCycle.Admissible K Θ ψ C.background) (hG : G ∈ Θ)
      (J : Finset σ) (γ : OuterTriple K) (j : Ideal (𝓞 K)) (d : OS)
      (Z H U : ℝ), ∀ hZ : 1 < Z,
      0 ≤ H → H ≤ Hmax → 0 < U → U ≤ Z ^ Umax →
      C.slots.card ≤ slotCap →
      (∀ i ∈ C.slots, ∀ P ∈ C.primeLists i, ‖C.primeWeights i P‖ ≤ 1) →
      ∀ (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
      (m : ℕ) (coordinate : LogPlane → ℝ), Continuous coordinate →
      spectralAverage (MellinSeparation.density W hW) m coordinate
        (fun t => principalCost K S D Γ hΓ μv C Θ ψ G hν hG J γ j d U a t
          φ h hlc hcs ⟨Z ^ (-H), Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _⟩) ≤
        A * U * Z ^ (H + loss) * fourierMass m * mellinMass W hW := by
  obtain ⟨A,hA,hbound⟩ := FirstCenteredErrors.exists_uniform_principal_bound
    K S D Γ hΓ μv slotCap Hmax Umax loss a hHmax hUmax hloss φ h hlc hcs
  refine ⟨A,hA,?_⟩
  intro σ C Θ ψ G hν hG J γ j d Z H U hZ hH0 hH hU hUcap hslots hweights
    W hW m coordinate hc
  let r : {r : ℝ // 0 < r} :=
    ⟨Z ^ (-H), Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _⟩
  apply (spectralAverage_le (MellinSeparation.density W hW) m coordinate hc
    (fun t => principalCost K S D Γ hΓ μv C Θ ψ G hν hG J γ j d U a t φ h hlc hcs r)
    (principalCost_continuous K S D Γ hΓ μv C Θ ψ G hν hG J γ j d U a φ h hlc hcs r)
    (fun t => principalCost_nonneg K S D Γ hΓ μv C Θ ψ G hν hG J γ j d U a t φ h hlc hcs r)
    (A * U * Z ^ (H + loss))
    (mul_nonneg (mul_nonneg hA hU.le) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
    (fun t => hbound C Θ ψ G hν hG J γ j d Z H U t hZ
      hH0 hH hU hUcap hslots hweights)).trans_eq
  unfold mellinMass
  ring

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

include ν in
theorem exists_tail_integral_bound
    (slotCap : ℕ) (Hmax Umax tauMin saving a : ℝ)
    (hHmax : 0 ≤ Hmax) (hUmax : 0 ≤ Umax) (htauMin : 0 < tauMin) (hsaving : 0 ≤ saving)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {σ : Type*} (C : ColumnData K S σ)
      (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
      (hν : BackgroundCycle.Admissible K Θ ψ C.background) (hG : G ∈ Θ)
      (J : Finset σ) (γ : OuterTriple K) (j : Ideal (𝓞 K)) (d : OS)
      (P : Finset (Ext × Ext)) (Z H U tau : ℝ), ∀ hZ : 2 ≤ Z,
      0 ≤ H → H ≤ Hmax → 0 < U → U ≤ Z ^ Umax → tauMin ≤ tau →
      C.slots.card ≤ slotCap →
      (∀ i ∈ C.slots, ∀ Q ∈ C.primeLists i, ‖C.primeWeights i Q‖ ≤ 1) →
      P ⊆ squarefreePool K Sset (2 * U) ×ˢ squarefreePool K Sset (2 * U) →
      ∀ (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
      (m : ℕ) (coordinate : LogPlane → ℝ), Continuous coordinate →
      spectralAverage (MellinSeparation.density W hW) m coordinate
        (fun t => tailCost K S D Γ hΓ μv C Θ ψ G hν hG J γ j d P U a t Z tau
          φ h hlc hcs ⟨Z ^ (-H), Real.rpow_pos_of_pos (by linarith) _⟩) ≤
        A * U * Z ^ (-saving) * fourierMass m * mellinMass W hW := by
  obtain ⟨A,hA,hbound⟩ := FirstCenteredErrors.exists_uniform_tail_bound
    K S D Γ hΓ μv ν slotCap Hmax Umax tauMin saving a
      hHmax hUmax htauMin hsaving φ h hlc hcs
  refine ⟨A,hA,?_⟩
  intro σ C Θ ψ G hν hG J γ j d P Z H U tau hZ hH0 hH hU hUcap htau
    hslots hweights hP W hW m coordinate hc
  have hz : 0 < Z := by linarith
  let r : {r : ℝ // 0 < r} := ⟨Z ^ (-H), Real.rpow_pos_of_pos hz _⟩
  apply (spectralAverage_le (MellinSeparation.density W hW) m coordinate hc
    (fun t => tailCost K S D Γ hΓ μv C Θ ψ G hν hG J γ j d P U a t Z tau φ h hlc hcs r)
    (tailCost_continuous K S D Γ hΓ μv C Θ ψ G hν hG J γ j d U a φ h hlc hcs r P Z tau)
    (fun t => norm_nonneg _)
    (A * U * Z ^ (-saving))
    (mul_nonneg (mul_nonneg hA hU.le) (Real.rpow_nonneg hz.le _))
    (fun t => hbound C Θ ψ G hν hG J γ j d P Z H U t tau hZ
      hH0 hH hU hUcap htau hslots hweights hP)).trans_eq
  unfold mellinMass
  ring

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstCenteredErrorIntegrals

end
