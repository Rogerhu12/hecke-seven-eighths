import HeckeSkeleton.Moments.MOM_INV_STEP.ActualUniformProduction
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstIntegratedReduction
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualErrorBudget
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCanonicalCenters
import HeckeSkeleton.Moments.MOM_INV_STEP.FinalStepBounds

/-!
# The original normalized first total closes under the actual child IH

Production, the complete second error and the first center count are
integrated in the literal original source measure. Their common
parameters and the final finite test seminorm are selected before the
parent, its source ideals, its prime lists, the base and both frequency
variables. The first radial and row-count choice is shared with the
parent reduction and the error estimate.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ActualFirstTotalBudget

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open CanonicalNormPools FirstParentRows FirstOuterCenters FirstCenteredErrorIntegrals
  CommonKernel FirstNormalizedErrorBudget
open scoped Classical BigOperators nonZeroDivisors

universe uσ

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

def firstDegree (A : ℝ) (hA : 1 ≤ A) (slotCap : ℕ) (pi : ℝ) (hpi : 0 < pi)
    (t : Finset (ℕ × ℕ)) : ℕ :=
  FirstIntegratedReduction.degree
    (ActualUniformProduction.degree.{uσ} K S D A hA slotCap (pi / 8) (by positivity) t)

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
variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

include hΓ μv hallowed ν μ in
/-- A source-independent finite seminorm and constant bound the literal
normalized live first total. The only energy premise is the generated
smaller-piece induction hypothesis. -/
theorem exists_total_bound (slotCap : ℕ) (A pi tauMin : ℝ)
    (hA : 1 ≤ A) (hpi : 0 < pi) (htauMin : 0 < tauMin)
    (choice : UniformFirstWeightChoice.Choice.{uσ} K S D (2 * A) (32 * (4 * A)) (pi / 8))
    (t : Finset (ℕ × ℕ)) :
    ∃ q : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ {σ : Type uσ} [DecidableEq σ]
        (T : FirstParentEnergy.Data K S (σ := σ)) (hmask : T.mask = ∅)
        (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
        (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
        (hbase : 1 < T.columns.base) (labels : Finset Ext)
        (Z M r ell V h tau Q z c eta eps Cih : ℝ) (hZ : 2 ≤ Z),
      M ∈ Set.Icc (0 : ℝ) A → r ∈ Set.Icc (0 : ℝ) A →
      ell ∈ Set.Icc (0 : ℝ) A → V ∈ Set.Icc (0 : ℝ) A →
      h ∈ Set.Icc (0 : ℝ) 1 → tau ∈ Set.Icc (0 : ℝ) A → tauMin ≤ tau →
      2 ≤ Z ^ h → h ≤ eta / 32 → T.columns.base = Z →
      T.radius.val = Z ^ (-M) → T.scale.val = Z ^ r →
      (∀ b ∈ T.cubes, height K Sset b ≤ Z ^ (ell + h)) →
      (∀ f ∈ labels, height K Sset f ≤ Z ^ (V + h)) →
      c ≤ r + 3 * ell + V - M - Q - z → 0 ≤ c → 0 ≤ z →
      T.columns.puncture ≠ 0 →
      (Ideal.absNorm T.columns.puncture.radical : ℝ) ≤ Z ^ Q →
      0 ≤ eps → 0 ≤ Cih →
      ThetaCalibrationInput K Sset D T.columns.lambda G →
      (∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K T.columns.background p) →
      ∀ (hprime : ∀ a ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists a, Prime p)
        (hweights : ∀ a ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists a,
          ‖T.columns.primeWeights a p‖ ≤ 1)
        (hslots : T.columns.slots.card ≤ slotCap)
        (centers : FirstOuterCenters.Centering K S D T (FirstParentCentering.grid Z A 1)),
      let hz : 0 < Z := lt_of_lt_of_le (by norm_num) hZ
      let hz1 : 1 < Z := lt_of_lt_of_le (by norm_num) hZ
      let H := FirstLocalizedCutoff.sourceCutoff K S D T Z tau hz
      let R := FirstOuterPhysicalCap.radius K S D Γ T hmask Z (4 * A) M r ell V h tau hz
      ActualUniformProduction.AllSmallerPieces
        (K := K) (S := S) (D := D) (Γ := Γ) (T := T) (hmask := hmask)
        (A := A) (Z := Z) (M := M) (r := r) (ell := ell) (V := V) (h := h) (tau := tau)
        (hZ := hz1) (Θ := Θ) (ψ := ψ) (G := G) (hν := hν) (hG := hG) (hbase := hbase)
        (H := H) (oldLabels := labels) (centers := centers)
        (hprime := hprime) (hweights := hweights) (slotCap := slotCap) (hcap := hslots) eps Cih t →
      ∀ (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (side : Bool),
        FirstNormalizedSource.total K S D Γ T H labels (FirstParentCentering.grid Z A 1)
          centers side R choice.massExponent choice.epsilon Z r ell V Θ ψ G hν hG
          W hW (firstDegree.{uσ} K S D A hA slotCap pi hpi t) ≤
        C * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 * (Cih + 1) *
          Z ^ (r + 3 * ell + V + 40 * eta + tau + pi + eps) := by
  let p0 := pi / 8
  have hp0 : 0 < p0 := by dsimp only [p0]; positivity
  let m₂ := ActualUniformProduction.degree K S D A hA slotCap p0 hp0 t
  let epsilon₂ := ActualUniformProduction.secondEpsilon K S D Γ A p0 hA hp0
  have hepsilon₂ : 0 < epsilon₂ := ActualUniformProduction.secondEpsilon_pos K S D Γ A p0 hA hp0
  let Cp := ActualUniformProduction.productionConstant K S D Γ A hA slotCap p0 p0 p0 p0
    hp0 hp0 hp0 hp0 t choice.constant
  have hCp : 0 ≤ Cp := ActualUniformProduction.productionConstant_nonneg K S D Γ A hA slotCap
    p0 p0 p0 p0 hp0 hp0 hp0 hp0 t choice.constant (zero_le_one.trans choice.one_le_constant)
  let Ci := FirstIntegratedReduction.integrationConstant K S D Γ hΓ μv hallowed ν μ
    slotCap epsilon₂ hepsilon₂ m₂
  have hCi : 0 ≤ Ci := FirstIntegratedReduction.integrationConstant_nonneg
    K S D Γ hΓ μv hallowed ν μ slotCap epsilon₂ hepsilon₂ m₂
  let Cg := FirstCanonicalCenters.countConstant A p0 hA hp0
  have hCg : 0 ≤ Cg := zero_le_one.trans (FirstCanonicalCenters.countConstant_one_le A p0 hA hp0)
  let qp := FirstIntegratedReduction.testSeminorm m₂
  obtain ⟨qe, Ce, hCe, he⟩ := ActualErrorBudget.exists_actual_error_bound K S D Γ hΓ μv ν
    slotCap A p0 p0 p0 tauMin 1 hA hp0 hp0 htauMin (by norm_num) choice
  let Cprod := Ci * Cg * Cp * ((Fintype.card Sector : ℝ) + 1)
  have hCprod : 0 ≤ Cprod := by dsimp only [Cprod]; positivity
  refine ⟨qp ∪ qe, Cprod + 2 * Ce, by positivity, ?_⟩
  intro σ _ T hmask Θ ψ G hν hG hbase labels Z M r ell V h tau Q z c eta eps Cih hZ
    hM hr hell hV hh htau htauMin' hwidth hmesh hbase_eq hradius hscale hcube hlabels
    hparent hc hz hRho hRhoNorm heps hCih hcal hbg hprime hweights hslots centers
  dsimp only
  intro hih W hW side
  have hz0 : 0 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hz1 : 1 < Z := lt_of_lt_of_le (by norm_num) hZ
  let H := FirstLocalizedCutoff.sourceCutoff K S D T Z tau hz0
  let R := FirstOuterPhysicalCap.radius K S D Γ T hmask Z (4 * A) M r ell V h tau hz0
  let grid := FirstParentCentering.grid Z A 1
  let F := r + 3 * ell + V
  let Ep := F + 40 * eta + tau + p0 + p0 + p0 + p0 + p0 + p0 + eps
  let Et := F + 40 * eta + tau + pi + eps
  let Ee := F + 26 * h + tau + p0 + p0 + p0
  let Bprod := Cp * (Cih + (Fintype.card Sector : ℝ)) * Z ^ Ep
  let QW := (qp ∪ qe).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hQW : 0 ≤ QW := apply_nonneg _ _
  have hBprod : 0 ≤ Bprod := mul_nonneg
    (mul_nonneg hCp (add_nonneg hCih (Nat.cast_nonneg _))) (Real.rpow_nonneg hz0.le _)
  have hproduction (k : FirstParentCentering.CenterIndex Z A 1)
      (J : Finset σ) (hJ : J ∈ T.columns.slots.powerset) (side₂ : Bool) (s : ℝ) :
      FirstNormalizedReduction.production K S D Γ T H labels grid centers side R
        choice.massExponent choice.epsilon Z r ell V tau Θ ψ G hν hG hbase
        epsilon₂ m₂ k J side₂ s ≤ Bprod * NestedMellinBudget.cauchyCost (-(1 / 2 : ℝ)) s m₂ := by
    exact ActualUniformProduction.production_le
      (K := K) (S := S) (D := D) (Γ := Γ) (T := T) (hmask := hmask)
      (A := A) (Z := Z) (M := M) (r := r) (ell := ell) (V := V) (h := h) (tau := tau)
      (hA := hA) (hZ := hz1) (Θ := Θ) (ψ := ψ) (G := G)
      (hν := hν) (hG := hG) (hbase := hbase) (H := H) (oldLabels := labels) (centers := centers)
      (hprime := hprime) (hweights := hweights) (slotCap := slotCap) (hcap := hslots)
      p0 p0 p0 p0 p0 p0 Q z c eta eps Cih hp0 hp0 hp0 hp0 hp0 choice
      hM hr hell hV hh htau hwidth hmesh hbase_eq hradius hscale hcube hparent hc hz
      hRho hRhoNorm heps hCih hcal t hih side k J (Finset.mem_powerset.mp hJ) side₂ s
  have hi := FirstIntegratedReduction.total_le_of_production
    (K := K) (S := S) (D := D) (Γ := Γ) (hΓ := hΓ) (μv := μv)
    (hallowed := hallowed) (ν := ν) (μ := μ)
    (T := T) (H := H) (labels := labels) (grid := grid) (centers := centers) (side := side)
    (R := R) (massEps := choice.massExponent) (ε₁ := choice.epsilon)
    (Z := Z) (r := r) (ell := ell) (V := V) (tau := tau)
    (Θ := Θ) (ψ := ψ) (G := G) (hν := hν) (hG := hG) (hbase := hbase)
    slotCap hslots epsilon₂ hepsilon₂ m₂ Bprod hBprod hz0.le hcal hbg hprime hproduction W hW
  have herr := he T hmask grid centers (FirstParentCentering.grid_one_le Z A 1)
    side Θ ψ G hν hG hbase labels Z M r ell V h tau hZ
    hM.1 hr.2 hell.2 hV.2 hh.1 hh.2 htau.2 htauMin' hwidth hradius hscale hcube
    hlabels hprime hweights hslots W hW (FirstIntegratedReduction.degree m₂)
  dsimp only at herr
  rw [FirstNormalizedErrorBudget.error_total_eq K S D Γ hΓ μv T H labels grid centers
    side R choice.massExponent choice.epsilon Z r ell V tau Θ ψ G hν hG hbase W hW
    (FirstIntegratedReduction.degree m₂) hz0.le] at herr
  have hqp := FinalStepBounds.seminorm_sq_le_union_left qp qe W
  have hqe := FinalStepBounds.seminorm_sq_le_union_right qp qe W
  have hgrid := FirstCanonicalCenters.card_le A p0 hA hp0 Z hz1.le
  have hprodPower : Z ^ p0 * Z ^ Ep ≤ Z ^ Et := by
    rw [← Real.rpow_add hz0]
    apply Real.rpow_le_rpow_of_exponent_le hz1.le
    have hb := FinalStepBounds.production_exponent_le F eta tau pi eps hpi.le
    dsimp only [p0, Ep, Et]
    linarith
  have herrorPower : Z ^ Ee + Z ^ (Ee - 1) ≤ 2 * Z ^ Et := by
    have hee : Ee = F + 26 * h + tau + 3 * (pi / 8) := by dsimp only [Ee, p0]; ring
    rw [hee]
    exact FinalStepBounds.error_powers_le Z F h eta tau pi eps 1 hz1.le hh.1 hmesh
      hpi.le heps (by norm_num)
  have hsector : Cih + (Fintype.card Sector : ℝ) ≤
      ((Fintype.card Sector : ℝ) + 1) * (Cih + 1) := by
    nlinarith [mul_nonneg hCih (Nat.cast_nonneg (Fintype.card Sector))]
  have hprod : Ci * (Fintype.card (FirstParentCentering.CenterIndex Z A 1) : ℝ) *
      Bprod * (qp.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 ≤
      Cprod * QW ^ 2 * (Cih + 1) * Z ^ Et := by
    calc
      _ ≤ Ci * (Cg * Z ^ p0) * Bprod * QW ^ 2 := by gcongr <;> assumption
      _ = (Ci * Cg * Cp) * (Cih + (Fintype.card Sector : ℝ)) * QW ^ 2 *
          (Z ^ p0 * Z ^ Ep) := by dsimp only [Bprod]; ring
      _ ≤ (Ci * Cg * Cp) * (Cih + (Fintype.card Sector : ℝ)) * QW ^ 2 * Z ^ Et :=
        mul_le_mul_of_nonneg_left hprodPower (by positivity)
      _ ≤ (Ci * Cg * Cp) * (((Fintype.card Sector : ℝ) + 1) * (Cih + 1)) *
          QW ^ 2 * Z ^ Et := by gcongr <;> assumption
      _ = _ := by dsimp only [Cprod]; ring
  have herror : FirstNormalizedErrorBudget.boxedTotal K S D Γ hΓ μv T grid centers side
      R choice.massExponent choice.epsilon Z r ell V tau Θ ψ G hν hG hbase W hW
      (FirstIntegratedReduction.degree m₂) (liveSources K S D Γ T H labels) ≤
      (2 * Ce) * QW ^ 2 * (Cih + 1) * Z ^ Et := by
    calc
      _ ≤ Ce * (qe.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
          (Z ^ Ee + Z ^ (Ee - 1)) := herr
      _ ≤ Ce * QW ^ 2 * (2 * Z ^ Et) := by gcongr <;> assumption
      _ = (2 * Ce) * QW ^ 2 * Z ^ Et := by ring
      _ ≤ ((2 * Ce) * QW ^ 2 * Z ^ Et) * (Cih + 1) :=
        le_mul_of_one_le_right (by positivity) (by linarith)
      _ = _ := by ring
  apply hi.trans ((add_le_add hprod herror).trans_eq ?_)
  ring

end HeckeSkeleton.Moments.MOM_INV_STEP.ActualFirstTotalBudget

end
