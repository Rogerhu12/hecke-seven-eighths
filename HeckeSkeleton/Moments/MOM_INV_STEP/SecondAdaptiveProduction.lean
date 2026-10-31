import HeckeSkeleton.Moments.MOM_INV_STEP.SecondAdaptiveRetained

/-!
# Production of genuine positive child energies at the fine cutoff

The complete original common/divisor/sector index is retained. Each
term is the existing actual second source with the literal signed
sourceScalar, including its zeros. The sole change is the frozen
frequency radius, so the already proved density and Cauchy estimates
apply term by term with their original uniform constants.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondAdaptiveProduction

open NumberField IsDedekindDomain MeasureTheory UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
  HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools CanonicalFirstEnergy
  CommonKernel SecondSourceColumns SecondParentRetained ActualDivisorSectors
  SecondAdaptiveCutoff SecondAdaptiveRetained
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
variable {σ : Type*} [DecidableEq σ] {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

def weightAt (T : SecondParentProduction.Data K S σ Θ ψ)
    (H : Ext → Finset (HeightOneSpectrum OS) → ℝ) (i : IndexAt K S D Γ T H) : ℝ :=
  SecondParentProduction.weight K S D Γ (dataAt K S D Γ T H i) (oldIndexAt K S D Γ T H i)

theorem weightAt_nonneg (T : SecondParentProduction.Data K S σ Θ ψ)
    (H : Ext → Finset (HeightOneSpectrum OS) → ℝ) (i : IndexAt K S D Γ T H) :
    0 ≤ weightAt K S D Γ T H i := SecondParentProduction.weight_nonneg K S D Γ _ _

def centeredEnergyAt (T : SecondParentProduction.Data K S σ Θ ψ)
    (H : Ext → Finset (HeightOneSpectrum OS) → ℝ) (G : HeckeCharacter K) (hG : G ∈ Θ)
    (ε : ℝ) (m : ℕ) (side : Bool) (i : IndexAt K S D Γ T H) : ℝ :=
  SecondParentProduction.centeredEnergy K S D Γ (dataAt K S D Γ T H i)
    G hG ε m side (oldIndexAt K S D Γ T H i)

theorem centeredEnergyAt_nonneg (T : SecondParentProduction.Data K S σ Θ ψ)
    (H : Ext → Finset (HeightOneSpectrum OS) → ℝ) (G : HeckeCharacter K) (hG : G ∈ Θ)
    (ε : ℝ) (m : ℕ) (side : Bool) (i : IndexAt K S D Γ T H) :
    0 ≤ centeredEnergyAt K S D Γ T H G hG ε m side i :=
  SecondParentProduction.centeredEnergy_nonneg K S D Γ _ G hG ε m side _

def totalAt (T : SecondParentProduction.Data K S σ Θ ψ)
    (H : Ext → Finset (HeightOneSpectrum OS) → ℝ) (G : HeckeCharacter K) (hG : G ∈ Θ)
    (ε : ℝ) (m : ℕ) (side : Bool) : ℝ :=
  ∑ i : IndexAt K S D Γ T H,
    weightAt K S D Γ T H i * centeredEnergyAt K S D Γ T H G hG ε m side i

theorem totalAt_nonneg (T : SecondParentProduction.Data K S σ Θ ψ)
    (H : Ext → Finset (HeightOneSpectrum OS) → ℝ) (G : HeckeCharacter K) (hG : G ∈ Θ)
    (ε : ℝ) (m : ℕ) (side : Bool) : 0 ≤ totalAt K S D Γ T H G hG ε m side := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (weightAt_nonneg K S D Γ T H i)
    (centeredEnergyAt_nonneg K S D Γ T H G hG ε m side i)

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

def termAt (T : SecondParentProduction.Data K S σ Θ ψ)
    (H : Ext → Finset (HeightOneSpectrum OS) → ℝ) (G : HeckeCharacter K)
    (i : IndexAt K S D Γ T H) : ℂ :=
  SecondParentProduction.term K S D Γ μv ν (dataAt K S D Γ T H i)
    G (oldIndexAt K S D Γ T H i)

variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)

include hallowed in
theorem retained_eq_sum_at (T : SecondParentProduction.Data K S σ Θ ψ)
    (H : Ext → Finset (HeightOneSpectrum OS) → ℝ) (G : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset D T.columns.lambda G)
    (hbg : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset →
      UnramifiedAt K (T.columns.background T.triple) p) :
    retainedSourceAt K S D Γ hΓ μv
      (DivisorInverseColumn.coefficient K S D T.columns T.triple T.label.val.val T.divisor.val)
      (T.columns.columns T.triple ×ˢ T.columns.columns T.triple)
      T.archTest T.localTest T.locallyConstant T.compactSupport T.radius H =
      ∑ i : IndexAt K S D Γ T H, termAt K S D Γ μv ν T H G i := by
  rw [T.fullPool]
  rw [retainedSourceAt_eq_fixed_common K S D Γ hΓ μv ν hallowed T.columns T.triple G hcal hbg
    (SecondParentProduction.scale_pos K S T) T.cutoffSupport T.label T.divisor
    (2 * SecondParentProduction.scale K S T) (by positivity)
    T.archTest T.localTest T.locallyConstant T.compactSupport T.radius H]
  simp only [IndexAt, Fintype.sum_sigma, termAt, dataAt, oldIndexAt,
    SecondParentProduction.term, SecondParentProduction.selectedDivisor,
    SecondParentProduction.selectedRow, SecondParentProduction.selectedSector,
    SecondParentProduction.selectedProfile, SecondPhysicalEnergy.source,
    SecondPhysicalEnergy.sourcePool, SecondPhysicalEnergy.sourceCoefficient,
    forwardColumn, poweredFamily, SecondSourceAssembly.slicedColumn,
    SecondParentProduction.test, SecondParentProduction.scale, neg_div]
  rw [← Finset.sum_coe_sort
    (squarefreePool K Sset (2 * T.columns.base ^ T.columns.columnLength T.triple))]
  apply Finset.sum_congr rfl
  intro g hg
  rw [← Finset.sum_coe_sort (SecondSourceMasks.commonMask K S D g.val).powerset]
  apply Finset.sum_congr rfl
  intro δ hδ
  rw [← Finset.sum_coe_sort (FirstDualTruncation.sectorCutoff K S D Γ (H g.val δ.val))]; rfl

include ν hΓ hallowed in
/-- Every true fine frequency and original sector occurs once in the
positive source. The uniform density constant is selected before H. -/
theorem exists_retained_centered_bound
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (ε : ℝ) (hε : 0 < ε) (m : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ A : ℝ, 0 ≤ A ∧
      ∀ {σ₀ : Type*} [DecidableEq σ₀] {Θ₀ : Subgroup (HeckeCharacter K)} {ψ₀ : HeckeCharacter K},
      ∀ (T : SecondParentProduction.Data K S σ₀ Θ₀ ψ₀), T.localTest = h →
      ∀ (H : Ext → Finset (HeightOneSpectrum OS) → ℝ)
        (G : HeckeCharacter K) (hG : G ∈ Θ₀),
      ThetaCalibrationInput K Sset D T.columns.lambda G →
      (∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset →
        UnramifiedAt K (T.columns.background T.triple) p) →
      (∀ i ∈ T.columns.survivors T.triple, ∀ p ∈ T.columns.primeLists i, Prime p) →
      ‖retainedSourceAt K S D Γ hΓ μv
        (DivisorInverseColumn.coefficient K S D T.columns T.triple T.label.val.val T.divisor.val)
        (T.columns.columns T.triple ×ˢ T.columns.columns T.triple)
        T.archTest T.localTest T.locallyConstant T.compactSupport T.radius H‖ ≤
      (A * s.sup (schwartzSeminormFamily ℝ V ℂ) T.archTest) *
        (Real.sqrt (totalAt K S D Γ T H G hG ε m false) *
          Real.sqrt (totalAt K S D Γ T H G hG ε m true)) := by
  obtain ⟨s, A, hA, hb⟩ := SecondCommonEnvelope.exists_second_density_common_envelope
    K S D Γ μv ν h hlc hcs ε hε m
  refine ⟨s, A, hA, ?_⟩
  intro σ₀ _ Θ₀ ψ₀ T hlocal H G hG hcal hbg hprime
  subst h
  let M := A * s.sup (schwartzSeminormFamily ℝ V ℂ) T.archTest
  have hM : 0 ≤ M := mul_nonneg hA (apply_nonneg _ _)
  have hterm (i : IndexAt K S D Γ T H) :
      ‖termAt K S D Γ μv ν T H G i‖ ≤
        M * (weightAt K S D Γ T H i *
          (Real.sqrt (centeredEnergyAt K S D Γ T H G hG ε m false i) *
            Real.sqrt (centeredEnergyAt K S D Γ T H G hG ε m true i))) := by
    let Ti := dataAt K S D Γ T H i
    have hP (q : SecondParentProduction.Index K S D Γ Ti) (ξ : LogPlane) :
        ‖SecondPhysicalEnergy.density K S Γ
          (SecondParentProduction.selectedProfile K S D Γ μv ν Ti q) ξ‖ ≤
          (M * SecondParentProduction.radialScale K S D Γ Ti q ^ ε) *
            FirstCommonEnvelope.frequencyEnvelope m ξ :=
      hb Ti.archTest Ti.radius (SecondParentProduction.selectedDivisor K S D Γ Ti q)
        q.2.2.val.1
        (residualScale K S Ti.columns Ti.triple (SecondParentProduction.scale_pos K S Ti) q.1.val)
        (residualScale K S Ti.columns Ti.triple (SecondParentProduction.scale_pos K S Ti) q.1.val) ξ
    exact SecondParentProduction.term_bound K S D Γ μv ν hallowed Ti G hG
      hcal hprime ε m M hM hP (oldIndexAt K S D Γ T H i)
  rw [retained_eq_sum_at K S D Γ μv ν hΓ hallowed T H G hcal hbg]
  calc
    _ ≤ ∑ i : IndexAt K S D Γ T H, ‖termAt K S D Γ μv ν T H G i‖ := norm_sum_le _ _
    _ ≤ ∑ i : IndexAt K S D Γ T H, M * (weightAt K S D Γ T H i *
        (Real.sqrt (centeredEnergyAt K S D Γ T H G hG ε m false i) *
          Real.sqrt (centeredEnergyAt K S D Γ T H G hG ε m true i))) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = M * ∑ i : IndexAt K S D Γ T H, weightAt K S D Γ T H i *
        (Real.sqrt (centeredEnergyAt K S D Γ T H G hG ε m false i) *
          Real.sqrt (centeredEnergyAt K S D Γ T H G hG ε m true i)) :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (FullMobius.common_weighted_cauchy Finset.univ (weightAt K S D Γ T H)
        (centeredEnergyAt K S D Γ T H G hG ε m false)
        (centeredEnergyAt K S D Γ T H G hG ε m true)
        (fun i _ => weightAt_nonneg K S D Γ T H i)
        (fun i _ => centeredEnergyAt_nonneg K S D Γ T H G hG ε m false i)
        (fun i _ => centeredEnergyAt_nonneg K S D Γ T H G hG ε m true i)) hM

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondAdaptiveProduction

end
