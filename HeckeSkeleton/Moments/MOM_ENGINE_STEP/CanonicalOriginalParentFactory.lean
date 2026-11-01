import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFullSupportFirstTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalRadiusParentSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalPool
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalComparisonScales

/-!
# The original parent source and its first windows in a fixed box

Only the original complete arithmetic recipe, norm profiles, raw
Schwartz window, engine domain and fixed parameter box enter this
factory.  The full-support radius and original column and row windows
are computed internally.  The original tuple, centered coefficient and
sharp active-product window are supplied by the existing canonical
first-window constructor.

The ordinary coefficient does not use comparison scales.  We set those
unused scales to the main scales before constructing its common union
carrier and prove that the original energy is unchanged.  The centered
comparison retains precisely the scales in the original domain.

All slot counts use the same construction.  An original prime pool is
an optional later attachment, determined by the amplification parameter.
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
open HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]

/-- Fixed scalar choices, made before the original scale, profiles or
Fourier parameters.  No transformed source estimate is a field. -/
structure FixedBox where
  cap : ℕ
  widthMax : ℝ
  paddingMax : ℝ
  width_nonneg : 0 ≤ widthMax
  padding_nonneg : 0 ≤ paddingMax
  annulus : ℝ
  annulus_ge_one : 1 ≤ annulus
  loss : ℝ
  loss_pos : 0 < loss
  loss_le_one : loss ≤ 1
  tailSaving : ℝ
  tailSaving_nonneg : 0 ≤ tailSaving
  decay : ℝ
  decay_gt_one : 1 < decay

namespace FixedBox

variable (box : FixedBox)

def plainBound : ℝ := box.widthMax + box.paddingMax

def columnBound : ℝ := 3 * box.plainBound + 1

def tailDegree : ℝ := originalFirstPhysicalDegree box.cap box.columnBound

def cutoffExponent : ℝ := firstTailCutoffExponent box.tailDegree box.tailSaving box.decay

def cutoff (Z : ℝ) : ℝ := Z ^ box.cutoffExponent

def rowBound : ℝ := max 0 (box.cutoffExponent + 3 * box.columnBound)

theorem plainBound_nonneg : 0 ≤ box.plainBound :=
  add_nonneg box.width_nonneg box.padding_nonneg

theorem columnBound_nonneg : 0 ≤ box.columnBound := by
  have h := box.plainBound_nonneg
  dsimp only [columnBound]
  linarith

theorem rowBound_nonneg : 0 ≤ box.rowBound := le_max_left _ _

theorem cutoff_ge_one {Z : ℝ} (hZ : 1 ≤ Z) : 1 ≤ box.cutoff Z :=
  Real.one_le_rpow hZ (firstTailCutoffExponent_nonneg _ _ _ box.decay_gt_one)

theorem exists_threshold :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      box.annulus ^ (box.cap + 2) ≤ Z ^ box.loss :=
  original_annulus_power_threshold box.cap box.annulus box.loss box.loss_pos

def threshold : ℝ := Classical.choose box.exists_threshold

theorem threshold_gt_one : 1 < box.threshold :=
  (Classical.choose_spec box.exists_threshold).1

theorem annulus_bound {Z : ℝ} (hZ : box.threshold ≤ Z) :
    box.annulus ^ (box.cap + 2) ≤ Z ^ box.loss :=
  (Classical.choose_spec box.exists_threshold).2 Z hZ

/-- One actual pool, with its original density and all original error
valuations. This is an output of the prime ideal theorem. -/
structure SelectedPool (A : SArithmeticData K)
    (bad : Finset (HeightOneSpectrum (𝓞 K))) (Z ell eps : ℝ) where
  pool : PowerScaleExteriorPool A bad Z ell eps
  density_pos : 0 < pool.rowDensity box.rowBound box.columnBound
  inverse_density : 1 / pool.rowDensity box.rowBound box.columnBound ≤
    2 * Z ^ (-ell + eps)
  cardinal_mass : (pool.primes.card : ℝ) / pool.rowDensity box.rowBound box.columnBound ≤
    2 * idealCountConstant K * Z ^ eps
  error_mass : ∀ n : ℕ,
    (∑ p ∈ pool.primes, FirstGaussPoolData.localErrorWeight p n *
      Q p ^ amplifierMovingExponent n) / pool.rowDensity box.rowBound box.columnBound ≤
        2 * idealCountConstant K * Z ^ eps

/-- The pool and annulus thresholds precede every moving parent and
all its original first rows and divisor branches. -/
theorem exists_pool_threshold (A : SArithmeticData K)
    (bad : Finset (HeightOneSpectrum (𝓞 K))) (ell eps : ℝ)
    (hell : 0 < ell) (heps : 0 < eps) (hepsell : eps < ell) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ box.threshold ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      Nonempty (box.SelectedPool A bad Z ell eps) := by
  obtain ⟨Zpool, hZpool, hpools⟩ := exists_uniform_original_pool A bad ell eps
    box.rowBound box.columnBound hell heps hepsell
    box.rowBound_nonneg box.columnBound_nonneg
  refine ⟨max box.threshold Zpool, hZpool.trans_le (le_max_right _ _),
    le_max_left _ _, ?_⟩
  intro Z hZ
  obtain ⟨pool, hp⟩ := hpools Z ((le_max_right _ _).trans hZ)
  have h := hp box.rowBound box.columnBound le_rfl le_rfl
  exact ⟨{ pool := pool, density_pos := h.1, inverse_density := h.2.1,
    cardinal_mass := h.2.2.1, error_mass := h.2.2.2 }⟩

def poolThreshold (A : SArithmeticData K)
    (bad : Finset (HeightOneSpectrum (𝓞 K))) (ell eps : ℝ)
    (hell : 0 < ell) (heps : 0 < eps) (hepsell : eps < ell) : ℝ :=
  Classical.choose (box.exists_pool_threshold A bad ell eps hell heps hepsell)

theorem threshold_le_poolThreshold (A : SArithmeticData K)
    (bad : Finset (HeightOneSpectrum (𝓞 K))) (ell eps : ℝ)
    (hell : 0 < ell) (heps : 0 < eps) (hepsell : eps < ell) :
    box.threshold ≤ box.poolThreshold A bad ell eps hell heps hepsell :=
  (Classical.choose_spec (box.exists_pool_threshold A bad ell eps hell heps hepsell)).2.1

def selectedPool (A : SArithmeticData K)
    (bad : Finset (HeightOneSpectrum (𝓞 K))) (ell eps : ℝ)
    (hell : 0 < ell) (heps : 0 < eps) (hepsell : eps < ell)
    (Z : ℝ) (hZ : box.poolThreshold A bad ell eps hell heps hepsell ≤ Z) :
    box.SelectedPool A bad Z ell eps :=
  Classical.choice
    ((Classical.choose_spec (box.exists_pool_threshold A bad ell eps hell heps hepsell)).2.2 Z hZ)

end FixedBox

abbrev comparisonScale (centered : Bool) (Z exponent comparison : ℝ) : ℝ :=
  canonicalComparisonScale centered (Z ^ exponent) comparison

variable {ω ψ : HeckeCharacter K}

theorem same_parent_energy (centered : Bool) (d : MomentData K ω ψ)
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) :
    pairedStageEnergy centered d a Z t
      (comparisonScale centered Z a.n₁ Y₁) (comparisonScale centered Z a.n₂ Y₂) =
        pairedStageEnergy centered d a Z t Y₁ Y₂ :=
  pairedStageEnergy_canonicalComparisonScales centered d a Z t Y₁ Y₂

abbrev originalComparisonDomain
    {centered : Bool} {d : MomentData K ω ψ} {a : RealParameters}
    {Z Y₁ Y₂ floor padding : ℝ}
    (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding) :
    PairedEngineDomain centered d a Z
      (comparisonScale centered Z a.n₁ Y₁) (comparisonScale centered Z a.n₂ Y₂)
      floor padding := domain.canonicalComparisonScales

/-- Every scalar premise about either original rectangle follows from
the domain and the fixed width and padding box. -/
theorem original_scale_windows
    (box : FixedBox) {centered : Bool} {d : MomentData K ω ψ} {a : RealParameters}
    {Z Y₁ Y₂ floor padding : ℝ}
    (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding)
    (hwidth : a.m + a.q ≤ box.widthMax) (hpadding : padding ≤ box.paddingMax) :
    0 < comparisonScale centered Z a.n₁ Y₁ ∧
    0 < comparisonScale centered Z a.n₂ Y₂ ∧
    a.n₁ ≤ box.plainBound ∧ a.n₂ ≤ box.plainBound ∧
    comparisonScale centered Z a.n₁ Y₁ ≤ Z ^ box.plainBound ∧
    comparisonScale centered Z a.n₂ Y₂ ≤ Z ^ box.plainBound ∧
    box.plainBound + box.plainBound + d.geometry.totalLength + box.loss ≤ box.columnBound ∧
    a.m + a.q ≤ box.columnBound := by
  have hz : 0 < Z := zero_lt_one.trans domain.scale
  have hlength : 0 ≤ d.geometry.totalLength :=
    Finset.sum_nonneg (fun i _ => (d.geometry.slots i).length_pos.le)
  have hcore : a.n₁ + a.n₂ + d.geometry.totalLength ≤ a.m + a.q + padding := by
    simpa only [domain.total_length] using domain.padded_core
  have htotal : a.n₁ + a.n₂ + d.geometry.totalLength ≤ box.plainBound := by
    dsimp only [FixedBox.plainBound]
    linarith
  have hplain : 0 ≤ box.plainBound := box.plainBound_nonneg
  have hleft : a.n₁ ≤ box.plainBound := by
    dsimp only [FixedBox.plainBound]
    linarith [domain.plain_right_nonneg]
  have hright : a.n₂ ≤ box.plainBound := by
    dsimp only [FixedBox.plainBound]
    linarith [domain.plain_left_nonneg]
  have hlengthBound : d.geometry.totalLength ≤ box.plainBound := by
    dsimp only [FixedBox.plainBound]
    linarith [domain.plain_left_nonneg, domain.plain_right_nonneg]
  have hwidthPlain : a.m + a.q ≤ box.plainBound := by
    dsimp only [FixedBox.plainBound]
    linarith [box.padding_nonneg]
  have hcolumn : box.plainBound + box.plainBound + d.geometry.totalLength + box.loss ≤
      box.columnBound := by
    dsimp only [FixedBox.columnBound]
    linarith [box.loss_le_one]
  have hwidthColumn : a.m + a.q ≤ box.columnBound := by
    dsimp only [FixedBox.columnBound]
    linarith
  have hs : 0 < comparisonScale centered Z a.n₁ Y₁ ∧
      0 < comparisonScale centered Z a.n₂ Y₂ ∧
      comparisonScale centered Z a.n₁ Y₁ ≤ Z ^ box.plainBound ∧
      comparisonScale centered Z a.n₂ Y₂ ≤ Z ^ box.plainBound := by
    cases centered with
    | false =>
      simp only [comparisonScale, canonicalComparisonScale_false]
      exact ⟨Real.rpow_pos_of_pos hz _, Real.rpow_pos_of_pos hz _,
        Real.rpow_le_rpow_of_exponent_le domain.scale.le hleft,
        Real.rpow_le_rpow_of_exponent_le domain.scale.le hright⟩
    | true =>
      simp only [comparisonScale, canonicalComparisonScale_true, domain.comparison_left rfl,
        domain.comparison_right rfl]
      refine ⟨Real.rpow_pos_of_pos hz _, Real.rpow_pos_of_pos hz _, ?_, ?_⟩
      · apply Real.rpow_le_rpow_of_exponent_le domain.scale.le
        linarith [domain.width_nonneg]
      · apply Real.rpow_le_rpow_of_exponent_le domain.scale.le
        linarith [domain.width_nonneg]
  exact ⟨hs.1, hs.2.1, hleft, hright, hs.2.2.1, hs.2.2.2, hcolumn, hwidthColumn⟩

section OriginalSource

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
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {Index : Type*} {data : Index → MomentData K ω ψ}

/-- Exterior normalization changes only the complete-row certificate.
The original data and every used coefficient stay the same. -/
def directSource
    (box : FixedBox) (Q : CompleteMovingRowRecipe A P R data)
    (W : NormProfileRecipe data) (index : Index)
    (C : A.GeneralArithmeticContext σ η hS)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (hZ : 1 < Z)
    (hfull : Q.FullJointBudget Z (a.m + a.q)) (centered : Bool)
    (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    ActualDirectFirstSource (E := ℝ)
      (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) μv C Z
      (rowBallFiniteFamily K A.Sf 1) centered (data index) a t
      (comparisonScale centered Z a.n₁ Y₁) (comparisonScale centered Z a.n₂ Y₂)
      (box.cutoff Z) (box.cutoff_ge_one hZ.le) :=
  Q.exteriorRemaining.canonicalFullSupportDirectFirstSource μv ν C hroot hemb W index a Z t
    (comparisonScale centered Z a.n₁ Y₁) (comparisonScale centered Z a.n₂ Y₂)
    (zero_lt_one.trans hZ) (Q.exteriorRemaining_fullJointBudget Z (a.m + a.q) hfull)
    centered (box.cutoff Z) (box.cutoff_ge_one hZ.le) δ hδ hδhalf

/-- The true original union-column estimate, including all centered
comparison columns.  Its exponent is fixed before the moving data. -/
theorem original_column_window
    (box : FixedBox) (Q : CompleteMovingRowRecipe A P R data)
    (W : NormProfileRecipe data) (index : Index)
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
    {floor padding : ℝ}
    (domain : PairedEngineDomain centered (data index) a Z Y₁ Y₂ floor padding)
    (hwidth : a.m + a.q ≤ box.widthMax) (hpadding : padding ≤ box.paddingMax)
    (hcap : (data index).geometry.slotCount ≤ box.cap) (hlarge : box.threshold ≤ Z)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
    {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}
    (profiles : RawProfileWindow rowDomain heightDomain window orders (data index) amplitude)
    (hrows : ∀ u ∈ pairedRows (data index) a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic box.annulus) :
    let atoms := (Q.exteriorRemaining.arithmeticAtoms index).constantAtoms (W.at index) a Z t
    let raw := atoms.raw (comparisonScale centered Z a.n₁ Y₁)
      (comparisonScale centered Z a.n₂ Y₂)
    ∀ i ∈ raw.exteriorColumns, A.exteriorNorm (raw.columnExterior i) ≤ Z ^ box.columnBound := by
  dsimp only
  let atoms := (Q.exteriorRemaining.arithmeticAtoms index).constantAtoms (W.at index) a Z t
  let raw := atoms.raw (comparisonScale centered Z a.n₁ Y₁)
    (comparisonScale centered Z a.n₂ Y₂)
  have hlength : a.n₁ + a.n₂ + a.z ≤ box.plainBound := by
    dsimp only [FixedBox.plainBound]
    linarith [domain.padded_core]
  intro i hi
  apply (raw.canonicalComparison_column_norm_le_fixed_power profiles domain box.cap
    box.annulus box.loss box.plainBound box.annulus_ge_one hcap
    (box.annulus_bound hlarge) hlength hrows ht hwindow i hi).trans
  apply Real.rpow_le_rpow_of_exponent_le domain.scale.le
  dsimp only [FixedBox.columnBound]
  linarith [box.plainBound_nonneg, box.loss_le_one]

/-- All tuple, coefficient, physical mask/modulus, radius and sharp
nonzero-product fields refer to the actual source just constructed. -/
def firstWindows
    (box : FixedBox) (Q : CompleteMovingRowRecipe A P R data)
    (W : NormProfileRecipe data) (index : Index)
    (C : A.GeneralArithmeticContext σ η hS)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
    {floor padding : ℝ}
    (domain : PairedEngineDomain centered (data index) a Z Y₁ Y₂ floor padding)
    (hfull : Q.FullJointBudget Z (a.m + a.q))
    (hwidth : a.m + a.q ≤ box.widthMax) (hpadding : padding ≤ box.paddingMax)
    (hcap : (data index).geometry.slotCount ≤ box.cap) (hlarge : box.threshold ≤ Z)
    (orders sTail sZero : Finset (ℕ × ℕ)) (amplitude : ℝ) (hamplitude : 1 ≤ amplitude)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
    (profiles : RawProfileWindow rowDomain heightDomain window
      (OriginalProfileAtomBounds.profileOrders orders) (data index) amplitude)
    (hrows : ∀ u ∈ pairedRows (data index) a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic box.annulus)
    (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    let s := directSource μv ν box Q W index C hroot hemb a Z t Y₁ Y₂ domain.scale
      hfull centered δ hδ hδhalf
    FirstDualOriginalWindows
      (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) C
      s.columns s.ideal s.block s.profiles s.radius s.mask sTail sZero
      (2 * (box.cap + 2)) Z (box.cutoff Z) box.columnBound box.tailDegree
      box.tailSaving box.decay := by
  obtain ⟨hY₁, hY₂, hn₁, hn₂, hY₁le, hY₂le, hcolumn, hwidth'⟩ :=
    original_scale_windows box domain hwidth hpadding
  exact Q.exteriorRemaining.canonicalFullSupportFirstWindows W index a Z t
    (comparisonScale centered Z a.n₁ Y₁) (comparisonScale centered Z a.n₂ Y₂) C
    box.cap orders amplitude box.annulus box.loss box.plainBound box.plainBound
    box.columnBound box.tailSaving box.decay hamplitude box.annulus_ge_one box.loss_pos.le
    box.columnBound_nonneg hcap (box.annulus_bound hlarge) centered
    (originalComparisonDomain domain) hY₁ hY₂ hn₁ hn₂ hY₁le hY₂le profiles hrows ht hwindow
    hcolumn hwidth' sTail sZero

/-- Each common label supplies an actual original column, hence an
actual original row. Its full joint budget makes the chosen radius at
most one. Empty original parents need no separate nonempty premise. -/
theorem original_row_windows
    (box : FixedBox) (Q : CompleteMovingRowRecipe A P R data)
    (W : NormProfileRecipe data) (index : Index)
    (C : A.GeneralArithmeticContext σ η hS)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
    {floor padding : ℝ}
    (domain : PairedEngineDomain centered (data index) a Z Y₁ Y₂ floor padding)
    (hfull : Q.FullJointBudget Z (a.m + a.q))
    (hwidth : a.m + a.q ≤ box.widthMax) (hpadding : padding ≤ box.paddingMax)
    (hcap : (data index).geometry.slotCount ≤ box.cap) (hlarge : box.threshold ≤ Z)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
    {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}
    (profiles : RawProfileWindow rowDomain heightDomain window orders (data index) amplitude)
    (hrows : ∀ u ∈ pairedRows (data index) a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic box.annulus)
    (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    let s := directSource μv ν box Q W index C hroot hemb a Z t Y₁ Y₂ domain.scale
      hfull centered δ hδ hδhalf
    (∀ DE D, ∀ h ∈ (s.pieces DE D).leftData.rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤ Z ^ box.rowBound) ∧
    (∀ DE D, ∀ h ∈ (s.pieces DE D).rightData.rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤ Z ^ box.rowBound) := by
  let atoms := (Q.exteriorRemaining.arithmeticAtoms index).constantAtoms (W.at index) a Z t
  let raw := atoms.raw (comparisonScale centered Z a.n₁ Y₁)
    (comparisonScale centered Z a.n₂ Y₂)
  let radius := Q.exteriorRemaining.fullSupportRadius Z (a.m + a.q)
    (zero_lt_one.trans domain.scale)
  let values := atoms.values (comparisonScale centered Z a.n₁ Y₁)
    (comparisonScale centered Z a.n₂ Y₂)
  have hcolumns := original_column_window box Q W index a Z t Y₁ Y₂ centered domain
    hwidth hpadding hcap hlarge profiles hrows ht hwindow
  have hfull' := Q.exteriorRemaining_fullJointBudget Z (a.m + a.q) hfull
  have hw
      (DE : commonSupportPool raw.exteriorColumns raw.exteriorColumns
        (fun i => (raw.columnExterior i).val) (fun j => (raw.columnExterior j).val))
      (D : ((canonicalFirstCommonBlock C raw.exteriorColumns raw.exteriorColumns
        raw.columnExterior raw.columnExterior DE.val DE.property).mask ∅).powerset) :
      let p := canonicalFirstDirectLogBlock
        (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) μv ν C
        raw.exteriorColumns raw.exteriorColumns raw.columnExterior raw.columnExterior
        DE.val DE.property (CanonicalRowBall.archTest K A.Sf 1)
        (values.coefficient centered) (values.coefficient centered)
        (rowBallFiniteFamily K A.Sf 1)
        (rowBallFiniteFamily_locallyConstant K A.Sf 1)
        (rowBallFiniteFamily_compactSupport K A.Sf 1)
        radius D.val ∅ (box.cutoff Z) (box.cutoff_ge_one domain.scale.le) δ hδ hδhalf
      (∀ h ∈ p.leftData.rows, A.exteriorNorm (originalFrequencyIdeal h) ≤ Z ^ box.rowBound) ∧
      (∀ h ∈ p.rightData.rows, A.exteriorNorm (originalFrequencyIdeal h) ≤ Z ^ box.rowBound) := by
    obtain ⟨ij, hij, _⟩ := Finset.mem_image.mp DE.property
    have hi := (Finset.mem_product.mp hij).1
    have hm := Finset.mem_product.mp (Finset.mem_filter.mp hi).1
    have hplain := Finset.mem_product.mp hm.1
    obtain ⟨u, hu, _⟩ := Finset.mem_biUnion.mp hplain.1
    have hmnonneg := Q.exteriorRemaining.fullSupportParameters_m_nonneg_of_pairedRow
      a Z domain.scale hfull' index u hu
    have hradius : radius.val ≤ Z ^ (-(0 : ℝ)) := by
      change (Q.exteriorRemaining.fullSupportRadius Z (a.m + a.q)
        (zero_lt_one.trans domain.scale)).val ≤ _
      rw [Q.exteriorRemaining.fullSupportRadius_eq_negative_m a Z domain.scale]
      apply Real.rpow_le_rpow_of_exponent_le domain.scale.le
      linarith
    have h := canonicalFirstDirectLogBlock_row_windows
      (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) μv ν C
      raw.exteriorColumns raw.exteriorColumns raw.columnExterior raw.columnExterior
      DE.val DE.property (CanonicalRowBall.archTest K A.Sf 1)
      (values.coefficient centered) (values.coefficient centered)
      (rowBallFiniteFamily K A.Sf 1)
      (rowBallFiniteFamily_locallyConstant K A.Sf 1)
      (rowBallFiniteFamily_compactSupport K A.Sf 1)
      radius D.val D.property (box.cutoff Z) (box.cutoff_ge_one domain.scale.le)
      δ hδ hδhalf Z 0 box.cutoffExponent box.columnBound domain.scale.le
      le_rfl hradius hcolumns hcolumns
    simpa only [sub_zero, FixedBox.rowBound] using h
  exact ⟨fun DE D => (hw DE D).1, fun DE D => (hw DE D).2⟩

/-- Attach the pool chosen at the earlier fixed threshold to this
exact direct source. Every actual divisor exclusion remains in
`withOriginalPool`. No additional fixed deletion is introduced; the
original complete mask is already present in the source coefficients
and full-support radius. -/
def pooledSource
    (box : FixedBox) (Q : CompleteMovingRowRecipe A P R data)
    (W : NormProfileRecipe data) (index : Index)
    (C : A.GeneralArithmeticContext σ η hS)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (bad : Finset (HeightOneSpectrum (𝓞 K))) (ell eps : ℝ)
    (hell : 0 < ell) (heps : 0 < eps) (hepsell : eps < ell)
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
    {floor padding : ℝ}
    (domain : PairedEngineDomain centered (data index) a Z Y₁ Y₂ floor padding)
    (hfull : Q.FullJointBudget Z (a.m + a.q))
    (hwidth : a.m + a.q ≤ box.widthMax) (hpadding : padding ≤ box.paddingMax)
    (hcap : (data index).geometry.slotCount ≤ box.cap)
    (hlarge : box.poolThreshold A bad ell eps hell heps hepsell ≤ Z)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
    {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}
    (profiles : RawProfileWindow rowDomain heightDomain window orders (data index) amplitude)
    (hrows : ∀ u ∈ pairedRows (data index) a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic box.annulus)
    (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    let chosen := box.selectedPool A bad ell eps hell heps hepsell Z hlarge
    ActualFirstSource (E := ℝ)
      (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) μv C
      chosen.pool (rowBallFiniteFamily K A.Sf 1) centered (data index) a t
      (comparisonScale centered Z a.n₁ Y₁) (comparisonScale centered Z a.n₂ Y₂)
      (box.cutoff Z) (box.cutoff_ge_one domain.scale.le) := by
  let chosen := box.selectedPool A bad ell eps hell heps hepsell Z hlarge
  let s := directSource μv ν box Q W index C hroot hemb a Z t Y₁ Y₂ domain.scale
    hfull centered δ hδ hδhalf
  have hlarge' : box.threshold ≤ Z :=
    (box.threshold_le_poolThreshold A bad ell eps hell heps hepsell).trans hlarge
  have hcols := original_column_window box Q W index a Z t Y₁ Y₂ centered domain
    hwidth hpadding hcap hlarge' profiles hrows ht hwindow
  have hrow := original_row_windows μv ν box Q W index C hroot hemb
    a Z t Y₁ Y₂ centered domain hfull hwidth hpadding hcap hlarge'
    profiles hrows ht hwindow δ hδ hδhalf
  have hone : (Ideal.absNorm (1 : Ideal (𝓞 K)) : ℝ) ≤ Z ^ (0 : ℝ) := by simp
  have hdensity : 0 < chosen.pool.rowDensity box.rowBound (0 + box.columnBound) := by
    simpa only [zero_add] using chosen.density_pos
  exact s.withOriginalPool chosen.pool 1 1 one_ne_zero one_ne_zero
    box.rowBound box.rowBound 0 0 box.columnBound box.rowBound_nonneg
    box.rowBound_nonneg box.columnBound_nonneg hrow.1 hrow.2 hone hone hcols
    hdensity hdensity

end OriginalSource

end HeckeSkeleton.Moments.EngineStep.CanonicalOriginalParentFactory

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalParentFactory.same_parent_energy
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalParentFactory.original_scale_windows
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalParentFactory.directSource
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalParentFactory.original_column_window
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalParentFactory.firstWindows
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalParentFactory.original_row_windows
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalParentFactory.pooledSource
