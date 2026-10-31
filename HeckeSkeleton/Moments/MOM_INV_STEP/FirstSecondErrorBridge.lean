import HeckeSkeleton.Moments.MOM_INV_STEP.FirstSecondReduction
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstOuterErrors
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstErrorIntegrability

/-!
# The actual production error under its fine second cutoff

The cutoff is constructed from the actual reciprocal first row cap and
the actual fixed-center column scale.  The source is the complete first
centered family, with its literal triple, retained CJ label, first mask
divisor, and exponent -1/2.  The actual additive zeros and infinite tail
are identified before being compared with the proved principal and tail
costs.  Their common Mellin/Fourier integrals are genuine integrals of
these same functions; no cutoff or error identity is assumed.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstSecondErrorBridge

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools FirstParentRows FirstToSecondData
  FirstOuterErrors FirstCenteredErrors FirstCenteredErrorIntegrals FirstCommonEnvelope CommonKernel
open scoped Classical BigOperators nonZeroDivisors Topology

/-- Exact reciprocal radius for the predetermined physical row cap. -/
theorem rowRadius_rpow (Z H : ℝ) (hZ : 0 < Z) :
    InverseRowMajorant.rowRadius ⟨Z ^ H, Real.rpow_pos_of_pos hZ H⟩ =
      ⟨Z ^ (-H), Real.rpow_pos_of_pos hZ (-H)⟩ := by
  apply Subtype.ext
  change (Z ^ H)⁻¹ = Z ^ (-H)
  rw [Real.rpow_neg hZ.le]

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "OS" => Set.integer Sset K
local notation "φ₀" => Physical.ActualGramMajorantDraft.rowBallArchTest K S 1
local notation "h₀" => Physical.ActualGramMajorantDraft.rowBallFiniteFamily K S 1
local notation "hlc₀" => Physical.ActualGramMajorantDraft.rowBallFiniteFamily_locallyConstant K S 1
local notation "hcs₀" => Physical.ActualGramMajorantDraft.rowBallFiniteFamily_compactSupport K S 1

/-- The actual complete source pool is independent of both spectral
frequencies and of every later residual label and row. -/
def completePairs (U : {r : ℝ // 0 < r}) : Finset (Ext × Ext) :=
  squarefreePool K Sset (2 * U.val) ×ˢ squarefreePool K Sset (2 * U.val)

variable {σ : Type*} [DecidableEq σ]
variable (T : FirstParentEnergy.Data K S (σ := σ))

/-- This is constructed, not supplied as a free cutoff function. -/
def cutoff (R : OuterIndex K S D T → {r : ℝ // 0 < r})
    (U : {r : ℝ // 0 < r}) (Z tau : ℝ) (o : OuterIndex K S D T) :
    Ext → Finset (HeightOneSpectrum OS) → ℝ :=
  SecondAdaptiveCutoff.fineCutoff K S (InverseRowMajorant.rowRadius (R o)) U.val Z tau

theorem cutoff_eq_production (hbase : 1 < T.columns.base)
    (R : OuterIndex K S D T → {r : ℝ // 0 < r})
    (U : {r : ℝ // 0 < r}) (Z tau : ℝ) :
    cutoff K S D T R U Z tau = FirstToSecondData.fineCutoff K S D T R U Z tau := by
  funext o
  unfold cutoff FirstToSecondData.fineCutoff
  rw [FirstToSecondData.sourceScale_eq K S T hbase U]

theorem cutoff_at_rpow (U : {r : ℝ // 0 < r}) (Z H tau : ℝ) (hZ : 0 < Z)
    (o : OuterIndex K S D T) :
    cutoff K S D T (fun _ => ⟨Z ^ H, Real.rpow_pos_of_pos hZ H⟩) U Z tau o =
      SecondAdaptiveCutoff.fineCutoff K S
        ⟨Z ^ (-H), Real.rpow_pos_of_pos hZ (-H)⟩ U.val Z tau := by
  unfold cutoff
  rw [rowRadius_rpow]

variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
variable (hbase : 1 < T.columns.base)
variable (R : OuterIndex K S D T → {r : ℝ // 0 < r})
variable (U : {r : ℝ // 0 < r}) (J : Finset σ)

/-- The literal norm of the two actual additive zero terms. -/
def zerosAt (i : FirstErrorSource.Index K S D T) (s : ℝ) : ℝ :=
  let Q := data K S D T Θ ψ G hν hG hbase R U J s i.1 i.2
  let a := DivisorInverseColumn.coefficient K S D Q.columns Q.triple Q.label.val.val Q.divisor.val
  ‖SecondPoissonSplit.additiveZeros K S D Γ hΓ μv a (Q.columns.columns Q.triple)
    Q.archTest Q.localTest Q.locallyConstant Q.compactSupport Q.radius‖

/-- The complete physical principal source, including its nonzero
dual frequencies, is kept as the actual original source. -/
def physicalAt (i : FirstErrorSource.Index K S D T) (s : ℝ) : ℝ :=
  let Q := data K S D T Θ ψ G hν hG hbase R U J s i.1 i.2
  let a := DivisorInverseColumn.coefficient K S D Q.columns Q.triple Q.label.val.val Q.divisor.val
  ‖SecondPoissonSplit.physicalPrincipal K S D Γ hΓ a (Q.columns.columns Q.triple)
    Q.archTest Q.localTest Q.locallyConstant Q.compactSupport Q.radius‖

theorem physicalAt_nonneg (i : FirstErrorSource.Index K S D T) (s : ℝ) :
    0 ≤ physicalAt K S D Γ hΓ T Θ ψ G hν hG hbase R U J i s := norm_nonneg _

/-- Exact identification of the error in the actual production theorem.
The retained CJ, first divisor, complete source and -1/2 norm factor are
the ones already present in FirstToSecondData. -/
theorem errorAt_eq (Z tau : ℝ) (i : FirstErrorSource.Index K S D T) (s : ℝ) :
    FirstSecondReduction.errorAt K S D Γ hΓ μv T Θ ψ G hν hG hbase R U J s
      (cutoff K S D T R U Z tau) i.1 i.2 =
    zerosAt K S D Γ hΓ μv T Θ ψ G hν hG hbase R U J i s +
      tailTerm K S D Γ hΓ μv T Θ ψ G hν hG i J (completePairs K S U)
        U.val (-(1 / 2 : ℝ)) s Z tau φ₀ h₀ hlc₀ hcs₀
        (InverseRowMajorant.rowRadius (R i.1)) := rfl

theorem principalTerm_eq (i : FirstErrorSource.Index K S D T) (s : ℝ) :
    principalTerm K S D Γ hΓ μv T Θ ψ G hν hG i J U.val (-(1 / 2 : ℝ)) s
      φ₀ h₀ hlc₀ hcs₀ (InverseRowMajorant.rowRadius (R i.1)) =
    2 * physicalAt K S D Γ hΓ T Θ ψ G hν hG hbase R U J i s +
      zerosAt K S D Γ hΓ μv T Θ ψ G hν hG hbase R U J i s := rfl

/-- No physical principal term is silently erased: adding its actual
nonnegative cost is exactly what gives the aggregate error majorant. -/
theorem errorAt_le (Z tau : ℝ) (i : FirstErrorSource.Index K S D T) (s : ℝ) :
    FirstSecondReduction.errorAt K S D Γ hΓ μv T Θ ψ G hν hG hbase R U J s
      (cutoff K S D T R U Z tau) i.1 i.2 ≤
    principalTerm K S D Γ hΓ μv T Θ ψ G hν hG i J U.val (-(1 / 2 : ℝ)) s
      φ₀ h₀ hlc₀ hcs₀ (InverseRowMajorant.rowRadius (R i.1)) +
    tailTerm K S D Γ hΓ μv T Θ ψ G hν hG i J (completePairs K S U)
      U.val (-(1 / 2 : ℝ)) s Z tau φ₀ h₀ hlc₀ hcs₀
      (InverseRowMajorant.rowRadius (R i.1)) := by
  rw [errorAt_eq K S D Γ hΓ μv T Θ ψ G hν hG hbase R U J Z tau i s,
    principalTerm_eq K S D Γ hΓ μv T Θ ψ G hν hG hbase R U J i s]
  have hp := physicalAt_nonneg K S D Γ hΓ T Θ ψ G hν hG hbase R U J i s
  linarith

theorem zerosAt_continuous (i : FirstErrorSource.Index K S D T) :
    Continuous (fun s : ℝ => zerosAt K S D Γ hΓ μv T Θ ψ G hν hG hbase R U J i s) := by
  change Continuous (fun s : ℝ =>
    ‖SecondPoissonSplit.additiveZeros K S D Γ hΓ μv
      (DivisorInverseColumn.coefficient K S D
        (FirstCenteredFamily.family K S T.columns Θ ψ G hν hG J U.val (-(1 / 2 : ℝ)) s)
        (triple K S D T i.1 i.2) (label K S D T i.1).val.val
        (FirstLocalizedEnergy.divisor K S D T i.1).val)
      (squarefreePool K Sset (2 * U.val)) φ₀ h₀ hlc₀ hcs₀
      (InverseRowMajorant.rowRadius (R i.1))‖)
  unfold SecondPoissonSplit.additiveZeros
  apply Continuous.norm
  apply continuous_finsetSum
  intro p hp
  exact (sourceWeight_continuous K S D T.columns Θ ψ G hν hG J
    (triple K S D T i.1 i.2) (label K S D T i.1).val.val
    (FirstLocalizedEnergy.divisor K S D T i.1).val U.val (-(1 / 2 : ℝ)) p).mul_const _

theorem tailTerm_continuous (Z tau : ℝ) (i : FirstErrorSource.Index K S D T) :
    Continuous (fun s : ℝ =>
      tailTerm K S D Γ hΓ μv T Θ ψ G hν hG i J (completePairs K S U)
        U.val (-(1 / 2 : ℝ)) s Z tau φ₀ h₀ hlc₀ hcs₀
        (InverseRowMajorant.rowRadius (R i.1))) :=
  tailCost_continuous K S D Γ hΓ μv T.columns Θ ψ G hν hG J
    (triple K S D T i.1 i.2) (label K S D T i.1).val.val
    (FirstLocalizedEnergy.divisor K S D T i.1).val U.val (-(1 / 2 : ℝ))
    φ₀ h₀ hlc₀ hcs₀ (InverseRowMajorant.rowRadius (R i.1)) (completePairs K S U) Z tau

theorem errorAt_continuous (Z tau : ℝ) (i : FirstErrorSource.Index K S D T) :
    Continuous (fun s : ℝ =>
      FirstSecondReduction.errorAt K S D Γ hΓ μv T Θ ψ G hν hG hbase R U J s
        (cutoff K S D T R U Z tau) i.1 i.2) := by
  have he :
      (fun s : ℝ =>
        FirstSecondReduction.errorAt K S D Γ hΓ μv T Θ ψ G hν hG hbase R U J s
          (cutoff K S D T R U Z tau) i.1 i.2) =
      (fun s : ℝ =>
        zerosAt K S D Γ hΓ μv T Θ ψ G hν hG hbase R U J i s +
        tailTerm K S D Γ hΓ μv T Θ ψ G hν hG i J (completePairs K S U)
          U.val (-(1 / 2 : ℝ)) s Z tau φ₀ h₀ hlc₀ hcs₀
          (InverseRowMajorant.rowRadius (R i.1))) :=
    funext (errorAt_eq K S D Γ hΓ μv T Θ ψ G hν hG hbase R U J Z tau i)
  rw [he]
  exact (zerosAt_continuous K S D Γ hΓ μv T Θ ψ G hν hG hbase R U J i).add
    (tailTerm_continuous K S D Γ hΓ μv T Θ ψ G hν hG R U J Z tau i)

/-- Boundedness for each fixed genuine geometry follows from its finite
source and the unit-modulus spectral phases. It is not an error premise. -/
theorem errorAt_bounded (Z tau : ℝ) (i : FirstErrorSource.Index K S D T) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ s : ℝ,
      FirstSecondReduction.errorAt K S D Γ hΓ μv T Θ ψ G hν hG hbase R U J s
        (cutoff K S D T R U Z tau) i.1 i.2 ≤ E := by
  obtain ⟨Ep,hEp,hp⟩ := FirstErrorIntegrability.principalCost_bounded
    K S D Γ hΓ μv T.columns Θ ψ G hν hG J
    (triple K S D T i.1 i.2) (label K S D T i.1).val.val
    (FirstLocalizedEnergy.divisor K S D T i.1).val U.val (-(1 / 2 : ℝ))
    φ₀ h₀ hlc₀ hcs₀ (InverseRowMajorant.rowRadius (R i.1))
  obtain ⟨Et,hEt,ht⟩ := FirstErrorIntegrability.tailCost_bounded
    K S D Γ hΓ μv T.columns Θ ψ G hν hG J
    (triple K S D T i.1 i.2) (label K S D T i.1).val.val
    (FirstLocalizedEnergy.divisor K S D T i.1).val U.val (-(1 / 2 : ℝ))
    φ₀ h₀ hlc₀ hcs₀ (InverseRowMajorant.rowRadius (R i.1)) (completePairs K S U) Z tau
  refine ⟨Ep + Et, add_nonneg hEp hEt, ?_⟩
  intro s
  exact (errorAt_le K S D Γ hΓ μv T Θ ψ G hν hG hbase R U J Z tau i s).trans
    (add_le_add (hp s) (ht s))

/-- Both integrability certificates for the actual production error are
proved without norm-window or coefficient-size assumptions. -/
theorem errorAt_integrable (Z tau : ℝ) (i : FirstErrorSource.Index K S D T)
    (ρ : SchwartzMap ℝ ℂ) (m : ℕ) (coordinate : LogPlane → ℝ)
    (hc : Continuous coordinate) :
    (∀ v : ℝ, Integrable (fun t : ℝ => ‖ρ t‖ *
      FirstSecondReduction.errorAt K S D Γ hΓ μv T Θ ψ G hν hG hbase R U J
        (t + v) (cutoff K S D T R U Z tau) i.1 i.2)) ∧
    Integrable (fun ξ : LogPlane => frequencyEnvelope m ξ *
      ∫ t : ℝ, ‖ρ t‖ *
        FirstSecondReduction.errorAt K S D Γ hΓ μv T Θ ψ G hν hG hbase R U J
          (t + coordinate ξ) (cutoff K S D T R U Z tau) i.1 i.2) := by
  obtain ⟨E,hE,hb⟩ := errorAt_bounded K S D Γ hΓ μv T Θ ψ G hν hG hbase R U J Z tau i
  exact FirstErrorIntegrability.spectral_integrability ρ m coordinate hc _
    (errorAt_continuous K S D Γ hΓ μv T Θ ψ G hν hG hbase R U J Z tau i)
    (fun s => FirstSecondReduction.errorAt_nonneg K S D Γ hΓ μv T Θ ψ G hν hG
      hbase R U J s (cutoff K S D T R U Z tau) i.1 i.2) E hb

/-- The same two common integrals now consume exactly the principal and
fine-tail costs estimated by FirstErrorPhysicalBudget/FirstErrorTailBudget. -/
theorem spectralAverage_errorAt_le (Z tau : ℝ) (i : FirstErrorSource.Index K S D T)
    (ρ : SchwartzMap ℝ ℂ) (m : ℕ) (coordinate : LogPlane → ℝ)
    (hc : Continuous coordinate) :
    spectralAverage ρ m coordinate
      (fun s => FirstSecondReduction.errorAt K S D Γ hΓ μv T Θ ψ G hν hG
        hbase R U J s (cutoff K S D T R U Z tau) i.1 i.2) ≤
    spectralAverage ρ m coordinate
      (fun s => principalTerm K S D Γ hΓ μv T Θ ψ G hν hG i J U.val (-(1 / 2 : ℝ)) s
        φ₀ h₀ hlc₀ hcs₀ (InverseRowMajorant.rowRadius (R i.1))) +
    spectralAverage ρ m coordinate
      (fun s => tailTerm K S D Γ hΓ μv T Θ ψ G hν hG i J (completePairs K S U)
        U.val (-(1 / 2 : ℝ)) s Z tau φ₀ h₀ hlc₀ hcs₀
        (InverseRowMajorant.rowRadius (R i.1))) := by
  let E : ℝ → ℝ := fun s => FirstSecondReduction.errorAt K S D Γ hΓ μv T Θ ψ G hν hG
    hbase R U J s (cutoff K S D T R U Z tau) i.1 i.2
  let P : ℝ → ℝ := fun s => principalTerm K S D Γ hΓ μv T Θ ψ G hν hG i J
    U.val (-(1 / 2 : ℝ)) s φ₀ h₀ hlc₀ hcs₀ (InverseRowMajorant.rowRadius (R i.1))
  let Q : ℝ → ℝ := fun s => tailTerm K S D Γ hΓ μv T Θ ψ G hν hG i J
    (completePairs K S U) U.val (-(1 / 2 : ℝ)) s Z tau φ₀ h₀ hlc₀ hcs₀
    (InverseRowMajorant.rowRadius (R i.1))
  have he := errorAt_integrable K S D Γ hΓ μv T Θ ψ G hν hG hbase R U J Z tau i ρ m coordinate hc
  have hp := FirstErrorIntegrability.principalCost_integrable K S D Γ hΓ μv
    T.columns Θ ψ G hν hG J (triple K S D T i.1 i.2)
    (label K S D T i.1).val.val (FirstLocalizedEnergy.divisor K S D T i.1).val
    U.val (-(1 / 2 : ℝ)) φ₀ h₀ hlc₀ hcs₀ (InverseRowMajorant.rowRadius (R i.1)) ρ m coordinate hc
  have hq := FirstErrorIntegrability.tailCost_integrable K S D Γ hΓ μv
    T.columns Θ ψ G hν hG J (triple K S D T i.1 i.2)
    (label K S D T i.1).val.val (FirstLocalizedEnergy.divisor K S D T i.1).val
    U.val (-(1 / 2 : ℝ)) φ₀ h₀ hlc₀ hcs₀ (InverseRowMajorant.rowRadius (R i.1))
    (completePairs K S U) Z tau ρ m coordinate hc
  have hb (s : ℝ) : E s ≤ P s + Q s :=
    errorAt_le K S D Γ hΓ μv T Θ ψ G hν hG hbase R U J Z tau i s
  have hinner (ξ : LogPlane) :
      (∫ t : ℝ, ‖ρ t‖ * E (t + coordinate ξ)) ≤
      (∫ t : ℝ, ‖ρ t‖ * P (t + coordinate ξ)) +
        (∫ t : ℝ, ‖ρ t‖ * Q (t + coordinate ξ)) := by
    have hi := integral_mono (he.1 (coordinate ξ))
      ((hp.1 (coordinate ξ)).add (hq.1 (coordinate ξ))) (fun t => by
        calc
          ‖ρ t‖ * E (t + coordinate ξ) ≤
              ‖ρ t‖ * (P (t + coordinate ξ) + Q (t + coordinate ξ)) :=
            mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)
          _ = ‖ρ t‖ * P (t + coordinate ξ) + ‖ρ t‖ * Q (t + coordinate ξ) :=
            mul_add _ _ _)
    rwa [integral_add (hp.1 (coordinate ξ)) (hq.1 (coordinate ξ))] at hi
  have hout := integral_mono he.2 (hp.2.add hq.2) (fun ξ => by
    calc
      frequencyEnvelope m ξ * (∫ t : ℝ, ‖ρ t‖ * E (t + coordinate ξ)) ≤
          frequencyEnvelope m ξ *
            ((∫ t : ℝ, ‖ρ t‖ * P (t + coordinate ξ)) +
              (∫ t : ℝ, ‖ρ t‖ * Q (t + coordinate ξ))) :=
        mul_le_mul_of_nonneg_left (hinner ξ) (frequencyEnvelope_nonneg m ξ)
      _ = frequencyEnvelope m ξ * (∫ t : ℝ, ‖ρ t‖ * P (t + coordinate ξ)) +
          frequencyEnvelope m ξ * (∫ t : ℝ, ‖ρ t‖ * Q (t + coordinate ξ)) :=
        mul_add _ _ _)
  rw [integral_add hp.2 hq.2] at hout
  exact hout

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstSecondErrorBridge

end
