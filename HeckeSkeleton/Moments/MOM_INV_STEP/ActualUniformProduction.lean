import HeckeSkeleton.Moments.MOM_INV_STEP.ActualClosedBoxBudget
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstNormalizedReduction
import HeckeSkeleton.Moments.MOM_INV_STEP.UniformFirstWeightChoice

/-!
# Uniform pointwise production from the original normalized source

All counting, radial and spectral parameters precede the source. The
actual first scalar and both Mobius factors are retained until their
norm-box bounds are proved. The original physical cap is selected from
the first outer coordinates, so every later row and inverse-radius
bound uses that same cap. Both choices of each Cauchy side use the same
constants and the same spectral degree.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ActualUniformProduction

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools FirstParentRows
  FirstOuterCenters FirstToSecondData FirstCenteredPositiveEnergy CommonKernel
  ActualProductionBoxes ActualBoxGeometry
open DedekindZetaZeroFree.LargeSieve.Vendor
open scoped Classical BigOperators nonZeroDivisors

def boxCap (A : ℝ) : ℝ := 4 * A
def labelCap (A : ℝ) : ℝ := 12 * boxCap A + 4

theorem labelCap_nonneg (A : ℝ) (hA : 1 ≤ A) : 0 ≤ labelCap A := by
  unfold labelCap boxCap
  linarith

theorem label_length_le (A Z h : ℝ) (hA : 1 ≤ A) (hZ : 1 < Z) (hh : h ≤ 1)
    (j : BoxIndex Z (boxCap A)) :
    secondFormalLabel (length Z j .firstCommon) (length Z j .secondDivisor)
      (length Z j .secondOverlap) (length Z j .cubeLabel) + 4 * h ≤ labelCap A := by
  have hL : 0 ≤ boxCap A := by unfold boxCap; linarith
  have hB := (length_bounds Z (boxCap A) hZ hL j .firstCommon).2
  have ht := (length_bounds Z (boxCap A) hZ hL j .secondDivisor).2
  have hv := (length_bounds Z (boxCap A) hZ hL j .secondOverlap).2
  have hj := (length_bounds Z (boxCap A) hZ hL j .cubeLabel).2
  unfold secondFormalLabel labelCap
  linarith

def binConstant (A pi : ℝ) (hA : 1 ≤ A) (hpi : 0 < pi) : ℝ :=
  Classical.choose (DyadicSourcePartition.exists_bin_count_bound A 2 pi (by linarith) hpi)

theorem binConstant_one_le (A pi : ℝ) (hA : 1 ≤ A) (hpi : 0 < pi) :
    1 ≤ binConstant A pi hA hpi :=
  (Classical.choose_spec (DyadicSourcePartition.exists_bin_count_bound A 2 pi
    (by linarith) hpi)).1

theorem bins_le (A pi : ℝ) (hA : 1 ≤ A) (hpi : 0 < pi)
    (Z X : ℝ) (hZ : 2 ≤ Z) (hX : 0 < X) (hXcap : X ≤ Z ^ A) :
    (Fintype.card (SecondMobiusGeometry.Index X) : ℝ) ≤
      binConstant A pi hA hpi * Z ^ pi := by
  have hz : 0 < Z := by linarith
  have h4 : (4 : ℝ) ≤ Z ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    nlinarith
  have hcap : 4 * X ≤ Z ^ (A + 2) := by
    calc
      4 * X ≤ Z ^ (2 : ℝ) * Z ^ A :=
        mul_le_mul h4 hXcap hX.le (Real.rpow_nonneg hz.le _)
      _ = _ := by rw [← Real.rpow_add hz]; congr 1; ring
  have hlen : dyadicLength (4 * X) ≤ dyadicLength (Z ^ (A + 2)) := by
    unfold dyadicLength
    apply Nat.ceil_mono
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (by positivity) hcap) (Real.log_nonneg (by norm_num))
  have hcard : (Fintype.card (SecondMobiusGeometry.Index X) : ℝ) ≤
      (Fintype.card (DyadicSourcePartition.Index Z A 2) : ℝ) := by
    simp only [SecondMobiusGeometry.Index, DyadicSourcePartition.Index, Fintype.card_fin]
    exact_mod_cast Nat.add_le_add_right hlen 1
  exact hcard.trans ((Classical.choose_spec
    (DyadicSourcePartition.exists_bin_count_bound A 2 pi (by linarith) hpi)).2
      Z (by linarith))

def normBoxConstant (A pi : ℝ) (hA : 1 ≤ A) (hpi : 0 < pi) : ℝ :=
  Classical.choose (ActualProductionBoxes.exists_box_count_bound (boxCap A) pi
    (by unfold boxCap; linarith) hpi)

theorem normBoxConstant_one_le (A pi : ℝ) (hA : 1 ≤ A) (hpi : 0 < pi) :
    1 ≤ normBoxConstant A pi hA hpi :=
  (Classical.choose_spec (ActualProductionBoxes.exists_box_count_bound (boxCap A) pi
    (by unfold boxCap; linarith) hpi)).1

theorem normBoxes_le (A pi : ℝ) (hA : 1 ≤ A) (hpi : 0 < pi) (Z : ℝ) (hZ : 1 ≤ Z) :
    (Fintype.card (BoxIndex Z (boxCap A)) : ℝ) ≤ normBoxConstant A pi hA hpi * Z ^ pi :=
  (Classical.choose_spec (ActualProductionBoxes.exists_box_count_bound (boxCap A) pi
    (by unfold boxCap; linarith) hpi)).2 Z hZ

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

def secondEpsilon (A pi : ℝ) (hA : 1 ≤ A) (hpi : 0 < pi) : ℝ :=
  Classical.choose (ActualSingleBoxBudget.exists_uniform_radialWeight_bound
    K S D Γ (10 * boxCap A) pi (by unfold boxCap; linarith) hpi)

theorem secondEpsilon_pos (A pi : ℝ) (hA : 1 ≤ A) (hpi : 0 < pi) :
    0 < secondEpsilon K S D Γ A pi hA hpi :=
  (Classical.choose_spec (ActualSingleBoxBudget.exists_uniform_radialWeight_bound
    K S D Γ (10 * boxCap A) pi (by unfold boxCap; linarith) hpi)).1

def coordinateConstant (m : ℕ) : ℝ :=
  SecondSpectralCost.coordinateMoment m (SecondParentProduction.coordinate false) +
    SecondSpectralCost.coordinateMoment m (SecondParentProduction.coordinate true)

theorem coordinate_le (m : ℕ) (side : Bool) :
    SecondSpectralCost.coordinateMoment m (SecondParentProduction.coordinate side) ≤
      coordinateConstant m := by
  cases side
  · exact le_add_of_nonneg_right (SecondSpectralCost.coordinateMoment_nonneg _ _)
  · exact le_add_of_nonneg_left (SecondSpectralCost.coordinateMoment_nonneg _ _)

theorem coordinateConstant_nonneg (m : ℕ) : 0 ≤ coordinateConstant m :=
  add_nonneg (SecondSpectralCost.coordinateMoment_nonneg _ _)
    (SecondSpectralCost.coordinateMoment_nonneg _ _)

def massExponent (A pi : ℝ) : ℝ := ActualSingleBoxBudget.countingExponent (boxCap A) 1 pi

theorem massExponent_pos (A pi : ℝ) (hA : 1 ≤ A) (hpi : 0 < pi) :
    0 < massExponent A pi :=
  ActualSingleBoxBudget.countingExponent_pos (boxCap A) 1 pi
    (by unfold boxCap; linarith) (by norm_num) hpi

def degree (A : ℝ) (hA : 1 ≤ A) (slotCap : ℕ) (piTerm : ℝ) (hpiTerm : 0 < piTerm)
    (t : Finset (ℕ × ℕ)) : ℕ :=
  ActualClosedBoxBudget.spectralDegree K S D slotCap (labelCap A) piTerm
    (labelCap_nonneg A hA) hpiTerm t

/-- This coefficient is fixed before the source, the base, the mesh,
the two marked subsets and either frequency. -/
def productionConstant (A : ℝ) (hA : 1 ≤ A) (slotCap : ℕ)
    (piMass piTerm piBins piNorm : ℝ)
    (hpiMass : 0 < piMass) (hpiTerm : 0 < piTerm)
    (hpiBins : 0 < piBins) (hpiNorm : 0 < piNorm)
    (t : Finset (ℕ × ℕ)) (firstConstant : ℝ) : ℝ :=
  (binConstant A piBins hA hpiBins * (2 : ℝ) ^ slotCap *
    normBoxConstant A piNorm hA hpiNorm *
    ((ActualPoissonScale.fieldConstant K * firstConstant) *
      ActualPoissonScale.fieldConstant K *
      SecondProductionBudget.massConstant K S D Γ slotCap (massExponent A piMass)
        (massExponent_pos A piMass hA hpiMass))) *
    ((2 : ℝ) ^ slotCap *
      ActualClosedBoxBudget.closureConstant K S D slotCap (labelCap A) piTerm
        (labelCap_nonneg A hA) hpiTerm t *
      ActualClosedBoxBudget.spectralCoefficient K S D slotCap (labelCap A) piTerm
        (labelCap_nonneg A hA) hpiTerm t *
      coordinateConstant (degree K S D A hA slotCap piTerm hpiTerm t))

theorem productionConstant_nonneg (A : ℝ) (hA : 1 ≤ A) (slotCap : ℕ)
    (piMass piTerm piBins piNorm : ℝ)
    (hpiMass : 0 < piMass) (hpiTerm : 0 < piTerm)
    (hpiBins : 0 < piBins) (hpiNorm : 0 < piNorm)
    (t : Finset (ℕ × ℕ)) (firstConstant : ℝ) (hfirstConstant : 0 ≤ firstConstant) :
    0 ≤ productionConstant K S D Γ A hA slotCap piMass piTerm piBins piNorm
      hpiMass hpiTerm hpiBins hpiNorm t firstConstant := by
  have hbin := (binConstant_one_le A piBins hA hpiBins).trans' zero_le_one
  have hnorm := (normBoxConstant_one_le A piNorm hA hpiNorm).trans' zero_le_one
  have hfield := ActualPoissonScale.fieldConstant_nonneg K
  have hmass := (SecondProductionBudget.massConstant_pos K S D Γ slotCap
    (massExponent A piMass) (massExponent_pos A piMass hA hpiMass)).le
  have hclosure := (ActualClosedBoxBudget.closureConstant_pos K S D slotCap
    (labelCap A) piTerm (labelCap_nonneg A hA) hpiTerm t).le
  have hspectral := ActualClosedBoxBudget.spectralCoefficient_nonneg K S D slotCap
    (labelCap A) piTerm (labelCap_nonneg A hA) hpiTerm t
  have hcoordinate := coordinateConstant_nonneg (degree K S D A hA slotCap piTerm hpiTerm t)
  unfold productionConstant
  positivity

variable {σ : Type*} [DecidableEq σ]
variable (T : FirstParentEnergy.Data K S (σ := σ)) (hmask : T.mask = ∅)
variable (A Z M r ell V h tau : ℝ) (hA : 1 ≤ A) (hZ : 1 < Z)
local notation "Rcap" => FirstOuterPhysicalCap.radius K S D Γ T hmask
  Z (boxCap A) M r ell V h tau (zero_lt_one.trans hZ)

theorem radius_exponent_bounds
    (hM : M ∈ Set.Icc (0 : ℝ) A) (hr : r ∈ Set.Icc (0 : ℝ) A)
    (hell : ell ∈ Set.Icc (0 : ℝ) A) (hV : V ∈ Set.Icc (0 : ℝ) A)
    (hh : h ∈ Set.Icc (0 : ℝ) 1) (htau : tau ∈ Set.Icc (0 : ℝ) A)
    (o : OuterIndex K S D T) :
    let j := FirstOuterPhysicalCap.assignment K S D Γ T hmask Z (boxCap A) o
    let E := firstPhysicalHeight M r ell V (length Z j .firstDivisor)
      (length Z j .firstCommon) (length Z j .cubeLabel) + 12 * h + tau
    -(10 * boxCap A) ≤ E ∧ E ≤ 32 * boxCap A := by
  have hL : 0 ≤ boxCap A := by unfold boxCap; linarith
  have hd := length_bounds Z (boxCap A) hZ hL
    (FirstOuterPhysicalCap.assignment K S D Γ T hmask Z (boxCap A) o) .firstDivisor
  have hB := length_bounds Z (boxCap A) hZ hL
    (FirstOuterPhysicalCap.assignment K S D Γ T hmask Z (boxCap A) o) .firstCommon
  have hj := length_bounds Z (boxCap A) hZ hL
    (FirstOuterPhysicalCap.assignment K S D Γ T hmask Z (boxCap A) o) .cubeLabel
  dsimp only
  unfold firstPhysicalHeight boxCap at *
  constructor <;> linarith [hM.1, hM.2, hr.1, hr.2, hell.1, hell.2,
    hV.1, hV.2, hh.1, hh.2, htau.1, htau.2]

theorem inverse_radius_le
    (hM : M ∈ Set.Icc (0 : ℝ) A) (hr : r ∈ Set.Icc (0 : ℝ) A)
    (hell : ell ∈ Set.Icc (0 : ℝ) A) (hV : V ∈ Set.Icc (0 : ℝ) A)
    (hh : h ∈ Set.Icc (0 : ℝ) 1) (htau : tau ∈ Set.Icc (0 : ℝ) A)
    (o : OuterIndex K S D T) :
    (InverseRowMajorant.rowRadius (Rcap o)).val ≤ Z ^ (10 * boxCap A) := by
  have hb := (radius_exponent_bounds K S D Γ T hmask A Z M r ell V h tau hA hZ
    hM hr hell hV hh htau o).1
  change (Z ^ (firstPhysicalHeight M r ell V
    (length Z (FirstOuterPhysicalCap.assignment K S D Γ T hmask Z (boxCap A) o) .firstDivisor)
    (length Z (FirstOuterPhysicalCap.assignment K S D Γ T hmask Z (boxCap A) o) .firstCommon)
    (length Z (FirstOuterPhysicalCap.assignment K S D Γ T hmask Z (boxCap A) o) .cubeLabel) +
      12 * h + tau))⁻¹ ≤ _
  rw [← Real.rpow_neg (zero_lt_one.trans hZ).le]
  exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

theorem first_weight_cost (pi : ℝ)
    (choice : UniformFirstWeightChoice.Choice K S D (2 * A) (32 * boxCap A) pi)
    (hM : M ∈ Set.Icc (0 : ℝ) A) (hr : r ∈ Set.Icc (0 : ℝ) A)
    (hell : ell ∈ Set.Icc (0 : ℝ) A) (hV : V ∈ Set.Icc (0 : ℝ) A)
    (hh : h ∈ Set.Icc (0 : ℝ) 1) (htau : tau ∈ Set.Icc (0 : ℝ) A)
    (hradius : T.radius.val = Z ^ (-M)) (hscale : T.scale.val = Z ^ r)
    (hcube : ∀ q ∈ T.cubes, height K Sset q ≤ Z ^ (ell + h))
    (o : OuterIndex K S D T) :
    FirstLocalizedEnergy.radialScale K S D T o ^ choice.epsilon *
      (Rcap o).val ^ choice.massExponent ≤ choice.constant * Z ^ pi := by
  exact choice.bound T hmask Z (-M) (ell + h) r
    (firstPhysicalHeight M r ell V
      (length Z (FirstOuterPhysicalCap.assignment K S D Γ T hmask Z (boxCap A) o) .firstDivisor)
      (length Z (FirstOuterPhysicalCap.assignment K S D Γ T hmask Z (boxCap A) o) .firstCommon)
      (length Z (FirstOuterPhysicalCap.assignment K S D Γ T hmask Z (boxCap A) o) .cubeLabel) +
        12 * h + tau)
    hZ.le (by linarith [hM.1]) (by linarith [hell.2, hh.2]) (by linarith [hr.2])
    (radius_exponent_bounds K S D Γ T hmask A Z M r ell V h tau hA hZ
      hM hr hell hV hh htau o).2
    hradius.le hcube hscale.le o

variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
variable (hbase : 1 < T.columns.base)
variable (H : OuterIndex K S D T → {r : ℝ // 0 < r}) (oldLabels : Finset Ext)
local notation "Grid" => FirstParentCentering.grid Z A 1
variable (centers : FirstOuterCenters.Centering K S D T Grid)
variable (hprime : ∀ q ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists q, Prime p)
variable (hweights : ∀ q ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists q,
  ‖T.columns.primeWeights q p‖ ≤ 1)
variable (slotCap : ℕ) (hcap : T.columns.slots.card ≤ slotCap)
local notation "Alive" => FirstLiveCappedFreeEnergy.alive K S D Γ T H oldLabels

/-- The complete recursive premise for the original source. The first
and second marked subsets, both Cauchy branches, the real first center,
the second bin, the norm box and both frequencies are all quantified.
Only the nonnegative row and column pieces invoke induction. -/
def AllSmallerPieces (eps Cih : ℝ) (t : Finset (ℕ × ℕ)) : Prop :=
  ∀ (side₁ : Bool) (k : FirstParentCentering.CenterIndex Z A 1)
    (J₁ : Finset σ) (hJ₁ : J₁ ⊆ T.columns.slots) (s : ℝ) (side₂ : Bool),
    ∀ (b : SecondMobiusGeometry.Index (sourceScale K S T (centerScale T.scale (Grid k))))
      (J₂ : Finset σ) (hJ₂ : J₂ ⊆ T.columns.slots),
      J₂ ∈ (T.columns.slots \ J₁).powerset → ∀ j : BoxIndex Z (boxCap A),
      ActualClosedBoxBudget.SmallerPieceBound
        (K := K) (S := S) (D := D) (Γ := Γ) (T := T) (Θ := Θ) (ψ := ψ) (G := G)
        (hν := hν) (hG := hG) (hbase := hbase) (R := Rcap)
        (U := centerScale T.scale (Grid k)) (J₁ := J₁) (s := s)
        (H₂ := FirstSecondErrorBridge.cutoff K S D T Rcap (centerScale T.scale (Grid k)) Z tau)
        (hmask := hmask) (grid := Grid) (centers := centers) (alive := Alive)
        (k := k) (side₁ := side₁) (P := Finset.univ) (b := b)
        (Z := Z) (L := boxCap A) (j := j)
        (hprime := hprime) (hweights := hweights) (hJ₁ := hJ₁) (J₂ := J₂) (hJ₂ := hJ₂)
        (slotCap := slotCap) (hcap := hcap) (h := h) M ell V eps Cih t side₂

/-- The normalized original production is uniformly bounded by the
fixed second Mellin cost. All physical weights, radial powers, label
windows and finite bin counts are discharged from the parent window.
The same coefficient serves both first and second Cauchy branches. -/
theorem production_le
    (piRad1 piRad2 piMass piTerm piBins piNorm Q z c eta eps Cih : ℝ)
    (hpiRad2 : 0 < piRad2) (hpiMass : 0 < piMass) (hpiTerm : 0 < piTerm)
    (hpiBins : 0 < piBins) (hpiNorm : 0 < piNorm)
    (choice : UniformFirstWeightChoice.Choice K S D (2 * A) (32 * boxCap A) piRad1)
    (hM : M ∈ Set.Icc (0 : ℝ) A) (hr : r ∈ Set.Icc (0 : ℝ) A)
    (hell : ell ∈ Set.Icc (0 : ℝ) A) (hV : V ∈ Set.Icc (0 : ℝ) A)
    (hh : h ∈ Set.Icc (0 : ℝ) 1) (htau : tau ∈ Set.Icc (0 : ℝ) A)
    (hwidth : 2 ≤ Z ^ h) (hmesh : h ≤ eta / 32)
    (hbase_eq : T.columns.base = Z)
    (hradius : T.radius.val = Z ^ (-M)) (hscale : T.scale.val = Z ^ r)
    (hcube : ∀ q ∈ T.cubes, height K Sset q ≤ Z ^ (ell + h))
    (hparent : c ≤ r + 3 * ell + V - M - Q - z) (hc : 0 ≤ c) (hz : 0 ≤ z)
    (hRho : T.columns.puncture ≠ 0)
    (hRhoNorm : (Ideal.absNorm T.columns.puncture.radical : ℝ) ≤ Z ^ Q)
    (heps : 0 ≤ eps) (hCih : 0 ≤ Cih)
    (hcal : ThetaCalibrationInput K Sset D T.columns.lambda G)
    (t : Finset (ℕ × ℕ))
    (hih : AllSmallerPieces
      (K := K) (S := S) (D := D) (Γ := Γ) (T := T) (hmask := hmask)
      (A := A) (Z := Z) (M := M) (r := r) (ell := ell) (V := V) (h := h) (tau := tau)
      (hZ := hZ) (Θ := Θ) (ψ := ψ) (G := G) (hν := hν) (hG := hG) (hbase := hbase)
      (H := H) (oldLabels := oldLabels) (centers := centers)
      (hprime := hprime) (hweights := hweights) (slotCap := slotCap) (hcap := hcap) eps Cih t)
    (side₁ : Bool) (k : FirstParentCentering.CenterIndex Z A 1)
    (J₁ : Finset σ) (hJ₁ : J₁ ⊆ T.columns.slots) (side₂ : Bool) (s : ℝ) :
    FirstNormalizedReduction.production K S D Γ T H oldLabels Grid centers side₁
      Rcap choice.massExponent choice.epsilon Z r ell V tau Θ ψ G hν hG hbase
      (secondEpsilon K S D Γ A piRad2 hA hpiRad2)
      (degree K S D A hA slotCap piTerm hpiTerm t) k J₁ side₂ s ≤
      (productionConstant K S D Γ A hA slotCap piMass piTerm piBins piNorm
        hpiMass hpiTerm hpiBins hpiNorm t choice.constant *
        (Cih + (Fintype.card Sector : ℝ)) *
        Z ^ (r + 3 * ell + V + 40 * eta + tau + piMass + piTerm + piRad1 +
          piRad2 + piNorm + piBins + eps)) *
        NestedMellinBudget.cauchyCost (-(1 / 2 : ℝ)) s
          (degree K S D A hA slotCap piTerm hpiTerm t) := by
  let U := centerScale T.scale (Grid k)
  let H₂ := FirstSecondErrorBridge.cutoff K S D T Rcap U Z tau
  let w := fun o e => FirstNormalizedSource.weight K S D T Grid Rcap
    choice.massExponent choice.epsilon Z r ell V k ⟨o,e⟩
  let m₂ := degree K S D A hA slotCap piTerm hpiTerm t
  have hz0 : 0 < Z := zero_lt_one.trans hZ
  have hZ2 : 2 ≤ Z := by
    have hp := Real.rpow_le_rpow_of_exponent_le hZ.le hh.2
    rw [Real.rpow_one] at hp
    exact hwidth.trans hp
  have hL : 0 ≤ boxCap A := by unfold boxCap; linarith
  have hUscale : U.val = Z ^ r / (Grid k).val := by
    change T.scale.val / (Grid k).val = _
    rw [hscale]
  have hU : U.val ≤ Z ^ A := by
    change T.scale.val / (Grid k).val ≤ _
    apply (div_le_iff₀ (Grid k).property).mpr
    calc
      T.scale.val = Z ^ r := hscale
      _ ≤ Z ^ A := Real.rpow_le_rpow_of_exponent_le hZ.le hr.2
      _ ≤ _ := le_mul_of_one_le_right (Real.rpow_nonneg hz0.le _)
        (FirstParentCentering.grid_one_le Z A 1 k)
  have hX : sourceScale K S T U ≤ Z ^ A := by
    rwa [sourceScale_eq K S T hbase U]
  have hXpos : 0 < sourceScale K S T U := by
    rw [sourceScale_eq K S T hbase U]
    exact U.property
  have hb : ∀ q ∈ T.cubes, height K Sset q ≤ Z ^ boxCap A := by
    intro q hq
    exact (hcube q hq).trans (Real.rpow_le_rpow_of_exponent_le hZ.le
      (by unfold boxCap; linarith [hell.2, hh.2]))
  have hfirst : 2 * T.scale.val ≤ Z ^ boxCap A := by
    calc
      2 * T.scale.val ≤ Z * Z ^ r := mul_le_mul hZ2 hscale.le T.scale.property.le hz0.le
      _ = Z ^ (1 + r) := by rw [Real.rpow_add hz0, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by unfold boxCap; linarith [hr.2])
  have hsecond : 4 * sourceScale K S T U ≤ Z ^ boxCap A := by
    have h4 : (4 : ℝ) ≤ Z ^ (2 : ℝ) := by rw [Real.rpow_two]; nlinarith
    calc
      4 * sourceScale K S T U ≤ Z ^ (2 : ℝ) * Z ^ A :=
        mul_le_mul h4 hX hXpos.le (Real.rpow_nonneg hz0.le _)
      _ = Z ^ (2 + A) := (Real.rpow_add hz0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by unfold boxCap; linarith)
  have hradial := (Classical.choose_spec
    (ActualSingleBoxBudget.exists_uniform_radialWeight_bound K S D Γ
      (10 * boxCap A) piRad2 (by unfold boxCap; linarith) hpiRad2)).2
      T Θ ψ G hν hG hbase Rcap U J₁ s H₂ Z (10 * boxCap A) A hZ.le le_rfl
      (by unfold boxCap; linarith)
      (inverse_radius_le K S D Γ T hmask A Z M r ell V h tau hA hZ hM hr hell hV hh htau) hU
  have hweight : ∀ b : SecondMobiusGeometry.Index (sourceScale K S T U),
      ∀ j : BoxIndex Z (boxCap A), ∀ i ∈ ActualSingleBoxBudget.boxedSource
        K S D Γ T Θ ψ G hν hG hbase Rcap U J₁ s H₂ hmask
        Grid centers Alive k side₁ Finset.univ b Z (boxCap A) j,
      w i.1 i.2.1 ≤ (ActualPoissonScale.fieldConstant K * choice.constant * Z ^ piRad1) *
        Z ^ (firstKappa M r ell V (length Z j .firstDivisor) (extractedLength Z j side₁)
          (length Z j .firstCommon) (length Z j .activeConductor) + (9 / 2 : ℝ) * h) := by
    intro b j i hi
    have hs := ActualSingleBoxBudget.source_first_prefactor_le K S D Γ T Θ ψ G hν hG hbase
      Rcap U J₁ s H₂ hmask Grid centers Alive k side₁ Finset.univ b Z (boxCap A) j
      h hZ hh.1 hwidth hb hfirst hsecond M r ell V hradius hscale i hi
    have hscalar0 := ActualSingleBoxBudget.firstScalar_nonneg K S D T Grid k Z r ell V
      hz0.le i.1 i.2.1
    have hmob := mul_le_mul_of_nonneg_left
      (FirstErrorIntegration.mobiusWeight_le_one K S D T ⟨i.1,i.2.1⟩) hscalar0
    rw [mul_one] at hmob
    have hcost := first_weight_cost K S D Γ T hmask A Z M r ell V h tau hA hZ
      piRad1 choice hM hr hell hV hh htau hradius hscale hcube i.1
    have hc := mul_le_mul (hmob.trans hs) hcost
      (mul_nonneg (Real.rpow_nonneg (FirstLocalizedEnergy.radialScale_pos K S D T i.1).le _)
        (Real.rpow_nonneg (Rcap i.1).property.le _))
      (mul_nonneg (ActualPoissonScale.fieldConstant_nonneg K) (Real.rpow_nonneg hz0.le _))
    convert hc using 1 <;>
      dsimp only [w, FirstNormalizedSource.weight, FirstNormalizedSource.firstScalar,
        ActualSingleBoxBudget.firstScalar, FirstToSecondData.quotient] <;> ring
  have hchoice0 : 0 ≤ choice.constant := zero_le_one.trans choice.one_le_constant
  have hfield0 := ActualPoissonScale.fieldConstant_nonneg K
  have hclosed := ActualClosedBoxBudget.actualTotal_closed_le
    (K := K) (S := S) (D := D) (Γ := Γ) (T := T) (Θ := Θ) (ψ := ψ) (G := G)
    (hν := hν) (hG := hG) (hbase := hbase) (R := Rcap) (U := U) (J₁ := J₁) (s := s)
    (H₂ := H₂) (hmask := hmask) (grid := Grid) (centers := centers) (alive := Alive)
    (k := k) (side₁ := side₁) (Z := Z) (L := boxCap A)
    (hprime := hprime) (hweights := hweights) (hJ₁ := hJ₁)
    (slotCap := slotCap) (hcap := hcap) (h := h) (hZ := hZ) (hh := hh.1)
    (hwidth := hwidth) (hb := hb) (hfirst := hfirst) (hsecond := hsecond)
    (w := w) (ε := secondEpsilon K S D Γ A piRad2 hA hpiRad2)
    M r ell V Q z c eta tau piMass eps (labelCap A) piTerm Cih
    (ActualPoissonScale.fieldConstant K * choice.constant * Z ^ piRad1) (Z ^ piRad2)
    (massExponent A piMass) hbase_eq hL hV.1 hUscale hcube rfl
    (FirstSecondErrorBridge.cutoff_eq_production K S D T hbase Rcap U Z tau)
    hparent hc hz hRho hRhoNorm (labelCap_nonneg A hA) hpiTerm
    (label_length_le A Z h hA hZ hh.2) heps hCih hcal (massExponent_pos A piMass hA hpiMass)
    hmesh (mul_nonneg (mul_nonneg hfield0 hchoice0) (Real.rpow_nonneg hz0.le _))
    (Real.rpow_nonneg hz0.le _)
    (fun j => ActualSingleBoxBudget.counting_loss_le (boxCap A) 1 piMass hL
      (by norm_num) hpiMass Z hZ ell h (by unfold boxCap; linarith [hell.2]) hh.2 j)
    (fun i => FirstNormalizedSource.weight_nonneg K S D T Grid Rcap choice.massExponent
      choice.epsilon Z r ell V hz0.le k ⟨i.1,i.2.1⟩) hweight hradial t side₂
    (hih side₁ k J₁ hJ₁ s side₂)
  have hbins := bins_le A piBins hA hpiBins Z (sourceScale K S T U) hZ2 hXpos hX
  have hboxes := normBoxes_le A piNorm hA hpiNorm Z hZ.le
  have hcoord := coordinate_le m₂ side₂
  have hmass0 := (SecondProductionBudget.massConstant_pos K S D Γ slotCap
    (massExponent A piMass) (massExponent_pos A piMass hA hpiMass)).le
  have hclosure0 := (ActualClosedBoxBudget.closureConstant_pos K S D slotCap
    (labelCap A) piTerm (labelCap_nonneg A hA) hpiTerm t).le
  have hspectral0 := ActualClosedBoxBudget.spectralCoefficient_nonneg K S D slotCap
    (labelCap A) piTerm (labelCap_nonneg A hA) hpiTerm t
  have hcost0 := NestedMellinBudget.cauchyCost_nonneg (-(1 / 2 : ℝ)) s m₂
  have hbin0 : 0 ≤ binConstant A piBins hA hpiBins :=
    zero_le_one.trans (binConstant_one_le A piBins hA hpiBins)
  have hbox0 : 0 ≤ normBoxConstant A piNorm hA hpiNorm :=
    zero_le_one.trans (normBoxConstant_one_le A piNorm hA hpiNorm)
  have hcoeff0 : 0 ≤ Cih + (Fintype.card Sector : ℝ) := add_nonneg hCih (Nat.cast_nonneg _)
  have hp : Z ^ piBins * Z ^ piNorm * Z ^ piRad1 * Z ^ piRad2 *
      Z ^ (r + 3 * ell + V + 40 * eta + tau + piMass + piTerm + eps) =
      Z ^ (r + 3 * ell + V + 40 * eta + tau + piMass + piTerm + piRad1 +
        piRad2 + piNorm + piBins + eps) := by
    rw [← Real.rpow_add hz0, ← Real.rpow_add hz0, ← Real.rpow_add hz0, ← Real.rpow_add hz0]
    congr 1
    ring
  change FirstNormalizedReduction.production K S D Γ T H oldLabels Grid centers side₁
    Rcap choice.massExponent choice.epsilon Z r ell V tau Θ ψ G hν hG hbase
    (secondEpsilon K S D Γ A piRad2 hA hpiRad2) m₂ k J₁ side₂ s ≤ _
  apply hclosed.trans
  calc
    _ ≤ (binConstant A piBins hA hpiBins * Z ^ piBins * (2 : ℝ) ^ slotCap *
        (normBoxConstant A piNorm hA hpiNorm * Z ^ piNorm) *
        (((ActualPoissonScale.fieldConstant K * choice.constant * Z ^ piRad1) *
          Z ^ piRad2 * ActualPoissonScale.fieldConstant K) *
          SecondProductionBudget.massConstant K S D Γ slotCap (massExponent A piMass)
            (massExponent_pos A piMass hA hpiMass) *
          Z ^ (r + 3 * ell + V + 40 * eta + tau + piMass + piTerm + eps))) *
        (((2 : ℝ) ^ slotCap *
          (ActualClosedBoxBudget.closureConstant K S D slotCap (labelCap A) piTerm
            (labelCap_nonneg A hA) hpiTerm t * (Cih + (Fintype.card Sector : ℝ)) *
            ActualClosedBoxBudget.spectralCoefficient K S D slotCap (labelCap A) piTerm
              (labelCap_nonneg A hA) hpiTerm t) * coordinateConstant m₂) *
          NestedMellinBudget.cauchyCost (-(1 / 2 : ℝ)) s m₂) := by
      gcongr <;> assumption
    _ = (productionConstant K S D Γ A hA slotCap piMass piTerm piBins piNorm
        hpiMass hpiTerm hpiBins hpiNorm t choice.constant *
        (Cih + (Fintype.card Sector : ℝ)) *
        (Z ^ piBins * Z ^ piNorm * Z ^ piRad1 * Z ^ piRad2 *
          Z ^ (r + 3 * ell + V + 40 * eta + tau + piMass + piTerm + eps))) *
        NestedMellinBudget.cauchyCost (-(1 / 2 : ℝ)) s m₂ := by
      unfold productionConstant
      dsimp only [m₂]
      ring
    _ = _ := by rw [hp]

end HeckeSkeleton.Moments.MOM_INV_STEP.ActualUniformProduction

end
