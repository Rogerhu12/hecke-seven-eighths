import HeckeSkeleton.Moments.MOM_INV_STEP.FirstNormalizedReduction
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstErrorBoxes
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstActualErrorPowers

/-!
# The real normalized second error over the live original source

The unique first-center indicator is eliminated by exact finite
regrouping. Each remaining source retains its assigned center, its
normalized first scalar, both original Mobius weights, the radial and
old-row powers, and both original spectral integrals. On an actual norm
box the prescribed row cap is constant; the proved first scalar and
weight costs then connect this literal error to the existing principal
and rapid-tail budgets.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstNormalizedErrorBudget

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools FirstParentRows
  FirstOuterCenters FirstToSecondData FirstPositiveSource FirstFreeMellinEnergy
  FirstErrorIntegration FirstCenteredErrorIntegrals CommonKernel InverseRowMajorant
  FirstSpectralAggregation FirstErrorSource FirstOuterErrors
open scoped Classical BigOperators nonZeroDivisors

private theorem reorder_centers {α β κ : Type*} [Fintype κ] [Fintype β]
    (P : Finset α) (F : κ → α → β → ℝ) :
    (∑ k : κ, ∑ J ∈ P, ∑ i : β, F k J i) =
      ∑ i : β, ∑ J ∈ P, ∑ k : κ, F k J i := by
  calc
    _ = ∑ k : κ, ∑ i : β, ∑ J ∈ P, F k J i := by
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_comm
    _ = ∑ i : β, ∑ k : κ, ∑ J ∈ P, F k J i := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "φ₀" => Physical.ActualGramMajorantDraft.rowBallArchTest K S 1
local notation "h₀" => Physical.ActualGramMajorantDraft.rowBallFiniteFamily K S 1
local notation "hlc₀" => Physical.ActualGramMajorantDraft.rowBallFiniteFamily_locallyConstant K S 1
local notation "hcs₀" => Physical.ActualGramMajorantDraft.rowBallFiniteFamily_compactSupport K S 1

variable {σ ι : Type*} [DecidableEq σ] [Fintype ι]
variable (T : FirstParentEnergy.Data K S (σ := σ))
variable (H : OuterIndex K S D T → {r : ℝ // 0 < r}) (labels : Finset Ext)
variable (grid : ι → {r : ℝ // 0 < r})
variable (centers : FirstOuterCenters.Centering K S D T grid) (side : Bool)
variable (R : OuterIndex K S D T → {r : ℝ // 0 < r}) (massEps ε : ℝ)
variable (Z r ell V tau : ℝ)
variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
variable (hbase : 1 < T.columns.base)
local notation "Idx" => FirstErrorSource.Index K S D T
local notation "U" k => FirstCenteredPositiveEnergy.centerScale T.scale (grid k)
local notation "Ui" i => FirstErrorBoxes.assignedScale K S D T grid centers side i
local notation "assigned" i => centers.assignment side i.1 i.2
local notation "weight" k i =>
  FirstNormalizedSource.liveWeight K S D Γ T H labels grid centers side R massEps ε
    Z r ell V k i

def liveSources : Finset Idx :=
  Finset.univ.filter (fun i => FirstLiveCappedFreeEnergy.alive K S D Γ T H labels i.1)

variable (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (m : ℕ)

def assignedErrorAverage (i : Idx) (J : Finset σ) : ℝ :=
  spectralAverage (MellinSeparation.density W hW) m (signedCoordinate side)
    (fun s => FirstSecondReduction.errorAt K S D Γ hΓ μv T Θ ψ G hν hG hbase
      R (Ui i) J s (FirstSecondErrorBridge.cutoff K S D T R (Ui i) Z tau) i.1 i.2)

theorem assignedErrorAverage_nonneg (i : Idx) (J : Finset σ) :
    0 ≤ assignedErrorAverage K S D Γ hΓ μv T grid centers side R Z tau
      Θ ψ G hν hG hbase W hW m i J := by
  apply integral_nonneg
  intro ξ
  apply mul_nonneg (FirstCommonEnvelope.frequencyEnvelope_nonneg m ξ)
  apply integral_nonneg
  intro s
  exact mul_nonneg (norm_nonneg _)
    (FirstSecondReduction.errorAt_nonneg K S D Γ hΓ μv T Θ ψ G hν hG hbase
      R (Ui i) J (s + signedCoordinate side ξ)
      (FirstSecondErrorBridge.cutoff K S D T R (Ui i) Z tau) i.1 i.2)

def outerCoefficient : ℝ :=
  ((T.columns.slots.powerset.card : ℝ) * (rowCovolume K S)⁻¹) * mellinMass W hW

theorem outerCoefficient_nonneg : 0 ≤ outerCoefficient K S T W hW :=
  mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr (rowCovolume_pos K S).le))
    (mellinMass_nonneg W hW)

def boxedTotal (I : Finset Idx) : ℝ :=
  outerCoefficient K S T W hW *
    ∑ i ∈ I, ∑ J ∈ T.columns.slots.powerset,
      FirstNormalizedSource.weight K S D T grid R massEps ε Z r ell V (assigned i) i *
        ‖mark K S D T side i J‖ ^ 2 *
        assignedErrorAverage K S D Γ hΓ μv T grid centers side R Z tau
          Θ ψ G hν hG hbase W hW m i J

/-- The complete actual normalized error has both spectral
integrability certificates. They come from the finite original source
and the already proved bounded continuous actual errors. -/
theorem error_spectral_integrability (hZ : 0 ≤ Z) (k : ι) (J : Finset σ)
    (ρ : SchwartzMap ℝ ℂ) :
    (∀ v : ℝ, Integrable (fun t : ℝ => ‖ρ t‖ *
      FirstNormalizedReduction.error K S D Γ T H labels grid centers side R massEps ε
        Z r ell V tau Θ ψ G hν hG hbase hΓ μv k J (t + v))) ∧
    Integrable (fun ξ : LogPlane => FirstCommonEnvelope.frequencyEnvelope m ξ *
      ∫ t : ℝ, ‖ρ t‖ * FirstNormalizedReduction.error K S D Γ T H labels grid centers side
        R massEps ε Z r ell V tau Θ ψ G hν hG hbase hΓ μv k J
        (t + signedCoordinate side ξ)) := by
  let c (i : Idx) : ℝ := weight k i * ‖mark K S D T side i J‖ ^ 2
  have hc (i : Idx) : 0 ≤ c i := mul_nonneg
    (FirstNormalizedSource.liveWeight_nonneg K S D Γ T H labels grid centers side
      R massEps ε Z r ell V hZ k i) (sq_nonneg _)
  choose B hB hb using fun i : Idx =>
    FirstSecondErrorBridge.errorAt_bounded K S D Γ hΓ μv T Θ ψ G hν hG hbase
      R (U k) J Z tau i
  have hec : Continuous (FirstNormalizedReduction.error K S D Γ T H labels grid centers side
      R massEps ε Z r ell V tau Θ ψ G hν hG hbase hΓ μv k J) := by
    unfold FirstNormalizedReduction.error
    apply continuous_finsetSum
    intro i hi
    exact (FirstSecondErrorBridge.errorAt_continuous K S D Γ hΓ μv
      T Θ ψ G hν hG hbase R (U k) J Z tau i).const_mul (c i)
  have heb (s : ℝ) : FirstNormalizedReduction.error K S D Γ T H labels grid centers side
      R massEps ε Z r ell V tau Θ ψ G hν hG hbase hΓ μv k J s ≤
        ∑ i : Idx, c i * B i := by
    unfold FirstNormalizedReduction.error
    exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hb i s) (hc i)
  exact FirstErrorIntegrability.spectral_integrability ρ m (signedCoordinate side)
    (signedCoordinate_continuous side) _ hec
    (FirstNormalizedReduction.error_nonneg K S D Γ T H labels grid centers side R
      massEps ε Z r ell V tau Θ ψ G hν hG hbase hΓ μv hZ k J) _ heb

/-- The genuine finite source is moved through the unchanged first
Mellin/Fourier integrals using its proved continuity and boundedness. -/
theorem error_average_eq (hZ : 0 ≤ Z) (k : ι) (J : Finset σ) :
    spectralAverage (MellinSeparation.density W hW) m (signedCoordinate side)
      (FirstNormalizedReduction.error K S D Γ T H labels grid centers side
        R massEps ε Z r ell V tau Θ ψ G hν hG hbase hΓ μv k J) =
    ∑ i : Idx, weight k i * ‖mark K S D T side i J‖ ^ 2 *
      spectralAverage (MellinSeparation.density W hW) m (signedCoordinate side)
        (fun s => FirstSecondReduction.errorAt K S D Γ hΓ μv T Θ ψ G hν hG hbase
          R (U k) J s (FirstSecondErrorBridge.cutoff K S D T R (U k) Z tau) i.1 i.2) := by
  let c (i : Idx) : ℝ := weight k i * ‖mark K S D T side i J‖ ^ 2
  have hc (i : Idx) : 0 ≤ c i := mul_nonneg
    (FirstNormalizedSource.liveWeight_nonneg K S D Γ T H labels grid centers side
      R massEps ε Z r ell V hZ k i) (sq_nonneg _)
  let f (i : Idx) (s : ℝ) : ℝ :=
    FirstSecondReduction.errorAt K S D Γ hΓ μv T Θ ψ G hν hG hbase R (U k) J s
      (FirstSecondErrorBridge.cutoff K S D T R (U k) Z tau) i.1 i.2
  choose B hB hb using fun i : Idx =>
    FirstSecondErrorBridge.errorAt_bounded K S D Γ hΓ μv T Θ ψ G hν hG hbase
      R (U k) J Z tau i
  have he := spectralAverage_finsetSum (Finset.univ : Finset Idx)
    (MellinSeparation.density W hW) m (signedCoordinate side) (signedCoordinate_continuous side)
    (fun i s => c i * f i s)
    (fun i _ => (FirstSecondErrorBridge.errorAt_continuous K S D Γ hΓ μv
      T Θ ψ G hν hG hbase R (U k) J Z tau i).const_mul (c i))
    (fun i _ s => mul_nonneg (hc i)
      (FirstSecondReduction.errorAt_nonneg K S D Γ hΓ μv T Θ ψ G hν hG hbase
        R (U k) J s (FirstSecondErrorBridge.cutoff K S D T R (U k) Z tau) i.1 i.2))
    (fun i => c i * B i) (fun i _ s => mul_le_mul_of_nonneg_left (hb i s) (hc i))
  simpa only [FirstNormalizedReduction.error, c, f, spectralAverage_const_mul] using he

/-- The first center contributes exactly once per actual source. The
sum over centers disappears by its original assignment indicator. -/
theorem error_total_eq (hZ : 0 ≤ Z) :
    outerCoefficient K S T W hW *
      (∑ k : ι, ∑ J ∈ T.columns.slots.powerset,
        spectralAverage (MellinSeparation.density W hW) m (signedCoordinate side)
          (FirstNormalizedReduction.error K S D Γ T H labels grid centers side
            R massEps ε Z r ell V tau Θ ψ G hν hG hbase hΓ μv k J)) =
      boxedTotal K S D Γ hΓ μv T grid centers side R massEps ε Z r ell V tau
        Θ ψ G hν hG hbase W hW m (liveSources K S D Γ T H labels) := by
  simp_rw [error_average_eq K S D Γ hΓ μv T H labels grid centers side R massEps ε
    Z r ell V tau Θ ψ G hν hG hbase W hW m hZ]
  unfold boxedTotal liveSources
  congr 1
  calc
    _ = ∑ i : Idx, ∑ J ∈ T.columns.slots.powerset, ∑ k : ι,
        weight k i * ‖mark K S D T side i J‖ ^ 2 *
          spectralAverage (MellinSeparation.density W hW) m (signedCoordinate side)
            (fun s => FirstSecondReduction.errorAt K S D Γ hΓ μv T Θ ψ G hν hG hbase
              R (U k) J s (FirstSecondErrorBridge.cutoff K S D T R (U k) Z tau) i.1 i.2) := by
      exact reorder_centers _ _
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases ha : FirstLiveCappedFreeEnergy.alive K S D Γ T H labels i.1
      · simp only [if_pos ha, FirstNormalizedSource.liveWeight, ha, true_and]
        apply Finset.sum_congr rfl
        intro J hJ
        simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rfl
      · simp only [if_neg ha, FirstNormalizedSource.liveWeight, ha, false_and,
          if_false, zero_mul, Finset.sum_const_zero]

/-- Exact arithmetic partition after the unique first center has been
retained at each source. -/
theorem boxedTotal_sum_boxes (hmask : T.mask = ∅) (I : Finset Idx) (L : ℝ) :
    boxedTotal K S D Γ hΓ μv T grid centers side R massEps ε Z r ell V tau
      Θ ψ G hν hG hbase W hW m I =
      ∑ j : ActualProductionBoxes.BoxIndex Z L,
        boxedTotal K S D Γ hΓ μv T grid centers side R massEps ε Z r ell V tau
          Θ ψ G hν hG hbase W hW m (FirstErrorBoxes.box K S D Γ T hmask I Z L j) := by
  unfold boxedTotal
  rw [FirstErrorBoxes.sum_boxes K S D Γ T hmask I Z L, Finset.mul_sum]

/-- Only geometric costs are premises: the actual physical scalar,
the radial and old-row powers, and the prescribed constant row cap in
this box. The error itself is the literal second Poisson error. -/
theorem boxedTotal_le_principal_add_tail
    (I : Finset Idx) (kappa Hexp scalarCost weightCost : ℝ)
    (hZ : 0 < Z) (hscalarCost : 0 ≤ scalarCost) (hweightCost : 0 ≤ weightCost)
    (hscalar : ∀ i ∈ I,
      FirstNormalizedSource.firstScalar K S D T grid Z r ell V (assigned i) i ≤
        scalarCost * Z ^ kappa)
    (hcost : ∀ i ∈ I,
      FirstLocalizedEnergy.radialScale K S D T i.1 ^ ε * (R i.1).val ^ massEps ≤ weightCost)
    (hrow : ∀ i ∈ I, (R i.1).val = Z ^ Hexp) :
    boxedTotal K S D Γ hΓ μv T grid centers side R massEps ε Z r ell V tau
      Θ ψ G hν hG hbase W hW m I ≤
      (scalarCost * weightCost) *
        (FirstErrorPhysicalBudget.principalTotal K S D Γ hΓ μv T Θ ψ G hν hG
          I side (fun i => (Ui i).val) W hW m (signedCoordinate side)
          φ₀ h₀ hlc₀ hcs₀ Z kappa Hexp (-(1 / 2 : ℝ)) hZ +
        FirstErrorTailBudget.tailTotal K S D Γ hΓ μv T Θ ψ G hν hG
          I side (fun i => (Ui i).val)
          (FirstActualErrorTotal.centerPairs K S D T (fun i => Ui i))
          W hW m (signedCoordinate side) φ₀ h₀ hlc₀ hcs₀
          Z kappa Hexp (-(1 / 2 : ℝ)) tau hZ) := by
  let p (i : Idx) (J : Finset σ) : ℝ :=
    spectralAverage (MellinSeparation.density W hW) m (signedCoordinate side)
      (fun s => principalTerm K S D Γ hΓ μv T Θ ψ G hν hG i J (Ui i).val
        (-(1 / 2 : ℝ)) s φ₀ h₀ hlc₀ hcs₀ ⟨Z ^ (-Hexp), Real.rpow_pos_of_pos hZ _⟩)
  let t (i : Idx) (J : Finset σ) : ℝ :=
    spectralAverage (MellinSeparation.density W hW) m (signedCoordinate side)
      (fun s => tailTerm K S D Γ hΓ μv T Θ ψ G hν hG i J
        (FirstSecondErrorBridge.completePairs K S (Ui i)) (Ui i).val (-(1 / 2 : ℝ)) s
        Z tau φ₀ h₀ hlc₀ hcs₀ ⟨Z ^ (-Hexp), Real.rpow_pos_of_pos hZ _⟩)
  have hav (i : Idx) (hi : i ∈ I) (J : Finset σ) :
      assignedErrorAverage K S D Γ hΓ μv T grid centers side R Z tau
        Θ ψ G hν hG hbase W hW m i J ≤ p i J + t i J := by
    have hb := FirstSecondErrorBridge.spectralAverage_errorAt_le K S D Γ hΓ μv
      T Θ ψ G hν hG hbase R (Ui i) J Z tau i (MellinSeparation.density W hW)
      m (signedCoordinate side) (signedCoordinate_continuous side)
    have hr : rowRadius (R i.1) = ⟨Z ^ (-Hexp), Real.rpow_pos_of_pos hZ _⟩ := by
      apply Subtype.ext
      change ((R i.1).val)⁻¹ = Z ^ (-Hexp)
      rw [hrow i hi, Real.rpow_neg hZ.le]
    rw [hr] at hb
    exact hb
  have hs (i : Idx) (hi : i ∈ I) :
      FirstNormalizedSource.weight K S D T grid R massEps ε Z r ell V (assigned i) i ≤
      (scalarCost * weightCost * Z ^ kappa) * mobiusWeight K S D T i := by
    have hgeom := mul_le_mul (hscalar i hi) (hcost i hi)
      (mul_nonneg (Real.rpow_nonneg (FirstLocalizedEnergy.radialScale_pos K S D T i.1).le _)
        (Real.rpow_nonneg (R i.1).property.le _))
      (mul_nonneg hscalarCost (Real.rpow_nonneg hZ.le _))
    have hh := mul_le_mul_of_nonneg_right hgeom (mobiusWeight_nonneg K S D T i)
    convert hh using 1 <;> simp only [FirstNormalizedSource.weight] <;> ring
  have hterm (i : Idx) (hi : i ∈ I) (J : Finset σ) :
      FirstNormalizedSource.weight K S D T grid R massEps ε Z r ell V (assigned i) i *
        ‖mark K S D T side i J‖ ^ 2 *
        assignedErrorAverage K S D Γ hΓ μv T grid centers side R Z tau
          Θ ψ G hν hG hbase W hW m i J ≤
      (scalarCost * weightCost * Z ^ kappa) *
        (mobiusWeight K S D T i * ‖mark K S D T side i J‖ ^ 2 * (p i J + t i J)) := by
    have hw := mul_le_mul_of_nonneg_right (hs i hi) (sq_nonneg ‖mark K S D T side i J‖)
    have hh := mul_le_mul hw (hav i hi J)
      (assignedErrorAverage_nonneg K S D Γ hΓ μv T grid centers side R Z tau
        Θ ψ G hν hG hbase W hW m i J)
      (by simpa only [mul_assoc] using
        (mul_nonneg (mul_nonneg (mul_nonneg hscalarCost hweightCost)
          (Real.rpow_nonneg hZ.le kappa))
          (mul_nonneg (mobiusWeight_nonneg K S D T i)
            (sq_nonneg ‖mark K S D T side i J‖))))
    exact hh.trans_eq (by ring)
  have hsum := Finset.sum_le_sum (s := I) (fun i hi =>
    Finset.sum_le_sum (s := T.columns.slots.powerset) (fun J _hJ => hterm i hi J))
  apply (mul_le_mul_of_nonneg_left hsum (outerCoefficient_nonneg K S T W hW)).trans_eq
  unfold FirstErrorPhysicalBudget.principalTotal FirstErrorTailBudget.tailTotal
    FirstActualErrorTotal.centerPairs outerCoefficient
  dsimp only [p, t]
  simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add,
    mul_assoc, mul_left_comm, mul_comm]

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

/-- The uniform quantitative bound for the literal normalized error.
Its only later assumptions concern the actual geometric windows,
individual prime weights and the two explicitly displayed small-power
factors. No principal, tail, source-energy, or error estimate is assumed.
`FirstErrorBoxes` supplies these windows for the predetermined boxes. -/
include ν in
theorem exists_boxedTotal_bound
    (slotCap : ℕ) (lengthCap Hmax Umax tauMin loss saving : ℝ)
    (hcap : 0 ≤ lengthCap) (hHmax : 0 ≤ Hmax) (hUmax : 0 ≤ Umax)
    (htauMin : 0 < tauMin) (hloss : 0 < loss) (hsaving : 0 ≤ saving) :
    ∃ q : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ {σ ι : Type*} [DecidableEq σ] [Fintype ι]
        (T : FirstParentEnergy.Data K S (σ := σ)) (hmask : T.mask = ∅)
        (grid : ι → {r : ℝ // 0 < r}) (centers : FirstOuterCenters.Centering K S D T grid)
        (side : Bool) (R : OuterIndex K S D T → {r : ℝ // 0 < r})
        (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
        (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
        (hbase : 1 < T.columns.base) (I : Finset (FirstErrorSource.Index K S D T))
        (Z M r ell V delta A B Rlen j t h tau massEps ε scalarCost weightCost : ℝ),
        ∀ hZ : 2 ≤ Z,
      ell ≤ lengthCap → Rlen ≤ lengthCap → B ≤ lengthCap →
      t ≤ lengthCap → h ≤ lengthCap → 0 ≤ j → tauMin ≤ tau →
      0 ≤ firstPhysicalHeight M r ell V delta B j + 12 * h + tau →
      firstPhysicalHeight M r ell V delta B j + 12 * h + tau ≤ Hmax →
      (∀ i ∈ I,
        (FirstErrorBoxes.assignedScale K S D T grid centers side i).val ≤ Z ^ Umax ∧
        (FirstErrorBoxes.assignedScale K S D T grid centers side i).val ≤
          Z ^ (r - A - B - t + 4 * h)) →
      (∀ a ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists a, Prime p) →
      (∀ a ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists a,
        ‖T.columns.primeWeights a p‖ ≤ 1) →
      T.columns.slots.card ≤ slotCap →
      (∀ i ∈ I,
        ((FirstErrorSource.bare K S D Γ T hmask i).b₁.val.val.absNorm : ℝ) ≤ Z ^ (ell + h) ∧
        ((FirstErrorSource.bare K S D Γ T hmask i).b₂.val.val.absNorm : ℝ) ≤ Z ^ (ell + h) ∧
        ((FirstErrorBudget.cubeConductor K S D Γ T hmask i).absNorm : ℝ) ≤ Z ^ (Rlen + h) ∧
        Z ^ (j - h) ≤ ((FirstErrorSource.bare K S D Γ T hmask i).cubeJ.absNorm : ℝ) ∧
        ((FirstErrorSource.bare K S D Γ T hmask i).cubeJ.absNorm : ℝ) ≤ Z ^ (j + h) ∧
        ((FirstErrorSource.bare K S D Γ T hmask i).firstCommon.absNorm : ℝ) ≤ Z ^ (B + h) ∧
        ((FirstErrorSource.bare K S D Γ T hmask i).quotient.val.val.absNorm : ℝ) ≤ Z ^ (t + h)) →
      0 ≤ scalarCost → 0 ≤ weightCost →
      (∀ i ∈ I, FirstNormalizedSource.firstScalar K S D T grid Z r ell V
        (centers.assignment side i.1 i.2) i ≤
          scalarCost * Z ^ (firstKappa M r ell V delta A B Rlen + 9 * h / 2)) →
      (∀ i ∈ I, FirstLocalizedEnergy.radialScale K S D T i.1 ^ ε *
        (R i.1).val ^ massEps ≤ weightCost) →
      (∀ i ∈ I, (R i.1).val =
        Z ^ (firstPhysicalHeight M r ell V delta B j + 12 * h + tau)) →
      ∀ (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (m : ℕ),
      boxedTotal K S D Γ hΓ μv T grid centers side R massEps ε Z r ell V tau
        Θ ψ G hν hG hbase W hW m I ≤
      scalarCost * weightCost * C *
        (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
        (Z ^ (r + 3 * ell + V - B - j + 26 * h + tau + loss) + Z ^ (r + 3 * ell + V - B - j + 26 * h + tau + loss - saving)) := by
  obtain ⟨qp, Cp, hCp, hp⟩ := FirstErrorPhysicalBudget.exists_principalTotal_bound
    K S D Γ hΓ μv slotCap lengthCap Hmax Umax loss (-(1 / 2 : ℝ))
      hcap hHmax hUmax hloss φ₀ h₀ hlc₀ hcs₀
  obtain ⟨qt, Ct, hCt, ht⟩ := FirstErrorTailBudget.exists_tailTotal_bound
    K S D Γ hΓ μv ν slotCap lengthCap Hmax Umax tauMin loss saving (-(1 / 2 : ℝ))
      hcap hHmax hUmax htauMin hloss hsaving φ₀ h₀ hlc₀ hcs₀
  refine ⟨qp ∪ qt, Cp + Ct, add_nonneg hCp hCt, ?_⟩
  intro σ ι _ _ T hmask grid centers side R Θ ψ G hν hG hbase I
    Z M r ell V delta A B Rlen j t h tau massEps ε scalarCost weightCost hZ
    hell hRlen hB htlen hhcap hj htau hH0 hH hU hprime hweights hslots hsource
    hscalarCost hweightCost hscalar hcost hrow W hW m
  have hz : 1 < Z := lt_of_lt_of_le (by norm_num) hZ
  let U : FirstErrorSource.Index K S D T → {r : ℝ // 0 < r} :=
    FirstErrorBoxes.assignedScale K S D T grid centers side
  have hUi (i : FirstErrorSource.Index K S D T) (hi : i ∈ I) :
      0 < (U i).val ∧ (U i).val ≤ Z ^ Umax ∧
        (U i).val ≤ Z ^ (r - A - B - t + 4 * h) :=
    ⟨(U i).property, (hU i hi).1, (hU i hi).2⟩
  have hp' := hp T hmask Θ ψ G hν hG I side (fun i => (U i).val)
    Z M r ell V delta A B Rlen j t h tau hz hell hRlen hB htlen hhcap hj
    hH0 hH hUi hprime hweights hslots hsource W hW m (signedCoordinate side)
    (signedCoordinate_continuous side)
  have ht' := ht T hmask Θ ψ G hν hG I side (fun i => (U i).val)
    (FirstActualErrorTotal.centerPairs K S D T U) Z M r ell V delta A B Rlen j t h tau hZ
    hell hRlen hB htlen hhcap hj htau hH0 hH hUi
    (fun i hi J hJ => Finset.Subset.refl _) hprime hweights hslots hsource
    W hW m (signedCoordinate side) (signedCoordinate_continuous side)
  have hb := boxedTotal_le_principal_add_tail K S D Γ hΓ μv T grid centers side R
    massEps ε Z r ell V tau Θ ψ G hν hG hbase W hW m I
    (firstKappa M r ell V delta A B Rlen + 9 * h / 2)
    (firstPhysicalHeight M r ell V delta B j + 12 * h + tau)
    scalarCost weightCost (zero_lt_one.trans hz) hscalarCost hweightCost hscalar hcost hrow
  let Q := (qp ∪ qt).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hqp : (qp.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 ≤ Q ^ 2 :=
    pow_le_pow_left₀ (apply_nonneg _ _)
      (Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_left) W) 2
  have hqt : (qt.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 ≤ Q ^ 2 :=
    pow_le_pow_left₀ (apply_nonneg _ _)
      (Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) W) 2
  have hp'' := hp'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hqp hCp) (Real.rpow_nonneg (zero_lt_one.trans hz).le _))
  have ht'' := ht'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hqt hCt) (Real.rpow_nonneg (zero_lt_one.trans hz).le _))
  have hsum := add_le_add hp'' ht''
  have hcombine : Cp * Q ^ 2 * Z ^ (r + 3 * ell + V - B - j + 26 * h + tau + loss) +
      Ct * Q ^ 2 * Z ^ (r + 3 * ell + V - B - j + 26 * h + tau + loss - saving) ≤
      (Cp + Ct) * Q ^ 2 *
        (Z ^ (r + 3 * ell + V - B - j + 26 * h + tau + loss) + Z ^ (r + 3 * ell + V - B - j + 26 * h + tau + loss - saving)) := by
    nlinarith [mul_nonneg (mul_nonneg hCp (sq_nonneg Q))
      (Real.rpow_nonneg (zero_lt_one.trans hz).le
        (r + 3 * ell + V - B - j + 26 * h + tau + loss - saving)),
      mul_nonneg (mul_nonneg hCt (sq_nonneg Q))
        (Real.rpow_nonneg (zero_lt_one.trans hz).le
          (r + 3 * ell + V - B - j + 26 * h + tau + loss))]
  exact hb.trans ((mul_le_mul_of_nonneg_left (hsum.trans hcombine)
    (mul_nonneg hscalarCost hweightCost)).trans_eq (by dsimp only [Q]; ring))

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstNormalizedErrorBudget

end
