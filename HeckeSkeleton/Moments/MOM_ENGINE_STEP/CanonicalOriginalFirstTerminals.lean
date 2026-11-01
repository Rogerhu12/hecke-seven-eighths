import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalParentFactory
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectFirstDualTerminal

/-!
# The original fixed-box first source with its two paid terminals

The actual first Poisson estimate and the sharp full-support zero bound
are applied to the same source produced by `directSource`.  Its fibre is
one by construction.  The original domain supplies all scale windows,
including the centered comparison rectangle, and the fixed threshold
pays the original annulus.  No transformed-source or terminal estimate
is a hypothesis.

The two finite orders, tail constant and numerical terminal constant are
chosen before the moving parent, profiles, scale and first logarithmic
partition.  The surviving term is the literal first nonzero source cost,
ready for its direct or once-pooled second transform.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalOriginalParentFactory

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
variable (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

local notation "Lattice" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

include μ in
/-- Uniform first-source production from the original data.  The zero
and tail quantities are those of the actual source in the parent bound;
neither is replaced by an unrelated positive majorant source. -/
theorem exists_original_parent_first_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (box : FixedBox) (degree : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hloss : box.loss ≤ ε / 4) (orders : Finset (ℕ × ℕ)) :
    ∃ (sTail sZero : Finset (ℕ × ℕ)) (Ctail Cterminal : ℝ),
      0 ≤ Ctail ∧ 0 < Cterminal ∧
    ∀ {ω ψ : HeckeCharacter K}
      {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
      {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
      {Index : Type*} {data : Index → MomentData K ω ψ}
      (Q : CompleteMovingRowRecipe A P R data) (W : NormProfileRecipe data) (index : Index)
      (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
      (a : RealParameters) (Z t Y₁ Y₂ amplitude control : ℝ),
      1 ≤ amplitude → 1 ≤ control → amplitude ≤ control ^ degree →
    ∀ (centered : Bool) {floor padding : ℝ}
      (domain : PairedEngineDomain centered (data index) a Z Y₁ Y₂ floor padding)
      (hfull : Q.FullJointBudget Z (a.m + a.q)),
      a.m + a.q ≤ box.widthMax → padding ≤ box.paddingMax →
      (data index).geometry.slotCount ≤ box.cap → box.threshold ≤ Z →
    ∀ {rowDomain : Set (NonzeroIdeal K)} {heightDomain window : Set ℝ}
      (profiles : RawProfileWindow rowDomain heightDomain window
        (OriginalProfileAtomBounds.profileOrders orders) (data index) amplitude),
      (∀ u ∈ pairedRows (data index) a Z, u ∈ rowDomain) →
      t ∈ heightDomain → window ⊆ Set.Iic box.annulus →
    ∀ (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2),
    let s := directSource μv ν box Q W index C hroot hemb a Z t Y₁ Y₂ domain.scale
      hfull centered δ hδ hδhalf;
    s.fiber = 1 ∧
    s.dualZeroCost hDiff / Z ^ (a.m + a.q) ≤
      Cterminal * control ^ firstDualOriginalProfileDegree box.cap degree * Z ^ ε ∧
    (Ctail * (box.cutoff Z) ^ (1 - box.decay) * s.tailCost sTail) /
        Z ^ (a.m + a.q) ≤
      Cterminal * control ^ firstDualOriginalProfileDegree box.cap degree *
        Z ^ (-box.tailSaving) ∧
    pairedStageEnergy centered (data index) a Z t Y₁ Y₂ / Z ^ (a.m + a.q) ≤
      Cterminal * control ^ firstDualOriginalProfileDegree box.cap degree * Z ^ ε +
        s.rawRowCost hDiff / Z ^ (a.m + a.q) := by
  obtain ⟨order, hord⟩ := exists_nat_gt
    (max (Module.finrank ℤ Lattice : ℝ) ((Module.finrank ℚ K : ℝ) * box.decay))
  have horder : Module.finrank ℤ Lattice < order := by
    exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hord)
  have hdegree : (Module.finrank ℚ K : ℝ) * box.decay ≤ (order : ℝ) :=
    (lt_of_le_of_lt (le_max_right _ _) hord).le
  obtain ⟨sTail, Ctail, hCtail, hparent⟩ :=
    actual_parent_first_direct_dual (E := ℝ)
      (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (μv := μv) (ν := ν) (μ := μ) C hDiff 1 box.decay box.decay_gt_one
      order horder hdegree
  obtain ⟨sZero, Czero, Cerror, Cterminal, hCzero, hCerror, herror, hCterminal, hterminals⟩ :=
    exists_canonical_full_support_first_terminal_bound (μv := μv)
      (σ := σ) (η := η) (hS := hS) (rowBallFiniteFamily K A.Sf 1)
      box.cap degree box.columnBound ε box.columnBound_nonneg hε orders sTail Ctail hCtail
      box.tailSaving box.decay box.tailSaving_nonneg box.decay_gt_one
  refine ⟨sTail, sZero, Ctail, Cterminal, hCtail, hCterminal, ?_⟩
  intro ω ψ P R Index data Q W index hroot hemb a Z t Y₁ Y₂ amplitude control
    hamplitude hcontrol hbound centered floor padding domain hfull hwidth hpadding
    hcap hlarge rowDomain heightDomain window profiles hrows ht hwindow δ hδ hδhalf
  let s := directSource μv ν box Q W index C hroot hemb a Z t Y₁ Y₂ domain.scale
    hfull centered δ hδ hδhalf
  have hfiber : s.fiber = 1 := rfl
  obtain ⟨hY₁, hY₂, hn₁, hn₂, hY₁le, hY₂le, hcolumn, hwidth'⟩ :=
    original_scale_windows box domain hwidth hpadding
  have hterminal := hterminals Q.exteriorRemaining W index a Z t
    (comparisonScale centered Z a.n₁ Y₁) (comparisonScale centered Z a.n₂ Y₂)
    C amplitude control box.annulus box.loss box.plainBound box.plainBound
    hamplitude hcontrol hbound box.annulus_ge_one box.loss_pos.le box.loss_le_one hloss
    hcap (box.annulus_bound hlarge) centered (originalComparisonDomain domain)
    hY₁ hY₂ hn₁ hn₂ hY₁le hY₂le profiles hrows ht hwindow hcolumn hwidth' hDiff
  change s.dualZeroCost hDiff / Z ^ (a.m + a.q) ≤
      Cterminal * control ^ firstDualOriginalProfileDegree box.cap degree * Z ^ ε ∧
    (Ctail * (box.cutoff Z) ^ (1 - box.decay) * s.tailCost sTail) /
        Z ^ (a.m + a.q) ≤
      Cterminal * control ^ firstDualOriginalProfileDegree box.cap degree *
        Z ^ (-box.tailSaving) ∧
    (s.dualZeroCost hDiff +
        Ctail * (box.cutoff Z) ^ (1 - box.decay) * s.tailCost sTail) /
        Z ^ (a.m + a.q) ≤
      Cterminal * control ^ firstDualOriginalProfileDegree box.cap degree * Z ^ ε
    at hterminal
  let atoms := (Q.exteriorRemaining.arithmeticAtoms index).constantAtoms (W.at index) a Z t
  let coefficient := (atoms.values (comparisonScale centered Z a.n₁ Y₁)
    (comparisonScale centered Z a.n₂ Y₂)).coefficient centered
  have hprofiles : ∀ i j, s.profiles i j = (coefficient i * star (coefficient j)) •
      CanonicalRowBall.archTest K A.Sf 1 := fun _ _ => rfl
  have hp := (hparent Z centered (data index) a t
    (comparisonScale centered Z a.n₁ Y₁) (comparisonScale centered Z a.n₂ Y₂)
    (box.cutoff Z) (box.cutoff_ge_one domain.scale.le) s coefficient hprofiles).1
  rw [hfiber, Nat.cast_one, one_mul] at hp
  rw [same_parent_energy centered (data index) a Z t Y₁ Y₂] at hp
  have hz : 0 < Z := zero_lt_one.trans domain.scale
  refine ⟨hfiber, hterminal.1, hterminal.2.1, ?_⟩
  calc
    _ ≤ (s.dualZeroCost hDiff + s.rawRowCost hDiff +
        Ctail * (box.cutoff Z) ^ (1 - box.decay) * s.tailCost sTail) /
        Z ^ (a.m + a.q) :=
      div_le_div_of_nonneg_right hp (Real.rpow_nonneg hz.le _)
    _ = (s.dualZeroCost hDiff +
        Ctail * (box.cutoff Z) ^ (1 - box.decay) * s.tailCost sTail) /
        Z ^ (a.m + a.q) + s.rawRowCost hDiff / Z ^ (a.m + a.q) := by ring
    _ ≤ _ := add_le_add hterminal.2.2 le_rfl

end HeckeSkeleton.Moments.EngineStep.CanonicalOriginalParentFactory

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalParentFactory.exists_original_parent_first_bound
