import HeckeSkeleton.Moments.MOM_INV_STEP.FirstNormalizedErrorBudget
import HeckeSkeleton.Moments.MOM_INV_STEP.UniformFirstWeightChoice

/-!
# Uniform closure of the complete actual second error

The actual live first sources are partitioned by their predetermined
twelve norm coordinates. Liveness proves the nonnegative physical row
exponent in each nonempty box. Every remaining hypothesis below is an
original parent cap, individual prime-weight bound, or original test
support. The first radial choice is shared verbatim with production.
The three losses remain separate: radial weight, error count, and box
count. The rapid tail has an arbitrary further prescribed saving.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ActualErrorBudget

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open CanonicalNormPools FirstParentRows FirstOuterCenters FirstPositiveSource
  FirstErrorIntegration FirstCenteredErrorIntegrals CommonKernel
  FirstNormalizedErrorBudget ActualProductionBoxes ActualBoxGeometry
open scoped Classical BigOperators nonZeroDivisors

private theorem rpow_mul_pair (Z E p saving : ℝ) (hZ : 0 < Z) :
    Z ^ p * (Z ^ E + Z ^ (E - saving)) =
      Z ^ (E + p) + Z ^ (E + p - saving) := by
  rw [mul_add, ← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1 <;> congr 1 <;> ring

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
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset

include ν in
/-- The final error estimate is for the literal normalized live error,
with its genuine two first spectral integrals, selected first center,
constructed first physical radius, and constructed fine second cutoff.
The chosen constant is independent of the parent and all source data. -/
theorem exists_actual_error_bound
    (slotCap : ℕ) (A piRad piError piBox tauMin saving : ℝ)
    (hA : 1 ≤ A) (hpiError : 0 < piError) (hpiBox : 0 < piBox)
    (htauMin : 0 < tauMin) (hsaving : 0 ≤ saving)
    (choice : UniformFirstWeightChoice.Choice K S D (2 * A) (32 * (4 * A)) piRad) :
    ∃ q : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ {σ ι : Type*} [DecidableEq σ] [Fintype ι]
        (T : FirstParentEnergy.Data K S (σ := σ)) (hmask : T.mask = ∅)
        (grid : ι → {r : ℝ // 0 < r})
        (centers : FirstOuterCenters.Centering K S D T grid)
        (hgrid : ∀ k, 1 ≤ (grid k).val) (side : Bool)
        (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
        (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
        (hbase : 1 < T.columns.base) (labels : Finset Ext)
        (Z M r ell V h tau : ℝ) (hZ : 2 ≤ Z),
      0 ≤ M → r ≤ A → ell ≤ A → V ≤ A → 0 ≤ h → h ≤ 1 → tau ≤ A → tauMin ≤ tau →
      2 ≤ Z ^ h → T.radius.val = Z ^ (-M) → T.scale.val = Z ^ r →
      (∀ b ∈ T.cubes, height K Sset b ≤ Z ^ (ell + h)) →
      (∀ f ∈ labels, height K Sset f ≤ Z ^ (V + h)) →
      (∀ a ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists a, Prime p) →
      (∀ a ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists a,
        ‖T.columns.primeWeights a p‖ ≤ 1) → T.columns.slots.card ≤ slotCap →
      ∀ (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (m : ℕ),
      let hz : 0 < Z := lt_of_lt_of_le (by norm_num) hZ
      let H := FirstLocalizedCutoff.sourceCutoff K S D T Z tau hz
      let R := FirstOuterPhysicalCap.radius K S D Γ T hmask Z (4 * A) M r ell V h tau hz
      outerCoefficient K S T W hW *
        (∑ k : ι, ∑ J ∈ T.columns.slots.powerset,
          spectralAverage (MellinSeparation.density W hW) m (signedCoordinate side)
            (FirstNormalizedReduction.error K S D Γ T H labels grid centers side R
              choice.massExponent choice.epsilon Z r ell V tau Θ ψ G hν hG hbase hΓ μv k J)) ≤
      C * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
        (Z ^ (r + 3 * ell + V + 26 * h + tau + piRad + piError + piBox) +
          Z ^ (r + 3 * ell + V + 26 * h + tau + piRad + piError + piBox - saving)) := by
  have hAc : 0 ≤ A := zero_le_one.trans hA
  obtain ⟨q, C₀, hC₀, hb₀⟩ := FirstNormalizedErrorBudget.exists_boxedTotal_bound
    K S D Γ hΓ μv ν slotCap (32 * (4 * A)) (32 * (4 * A)) A tauMin piError saving
      (by positivity) (by positivity) hAc htauMin hpiError hsaving
  obtain ⟨Cbox, hCbox, hbbox⟩ := exists_box_count_bound (4 * A) piBox (by positivity) hpiBox
  let D₀ := ActualPoissonScale.fieldConstant K * choice.constant * C₀
  have hD₀ : 0 ≤ D₀ := mul_nonneg
    (mul_nonneg (ActualPoissonScale.fieldConstant_nonneg K)
      (zero_le_one.trans choice.one_le_constant)) hC₀
  refine ⟨q, Cbox * D₀, mul_nonneg (zero_le_one.trans hCbox) hD₀, ?_⟩
  intro σ ι _ _ T hmask grid centers hgrid side Θ ψ G hν hG hbase labels
    Z M r ell V h tau hZ hM hr hell hV hh hh1 htau htauMin' hwidth
    hradius hscale hcube hlabels hprime hweights hslots W hW m
  dsimp only
  let hz : 0 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hz1 : 1 < Z := lt_of_lt_of_le (by norm_num) hZ
  let L : ℝ := 4 * A
  let H := FirstLocalizedCutoff.sourceCutoff K S D T Z tau hz
  let R := FirstOuterPhysicalCap.radius K S D Γ T hmask Z L M r ell V h tau hz
  let I := liveSources K S D Γ T H labels
  let Q := q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let E := r + 3 * ell + V + 26 * h + tau + piError
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hcoarse : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ L := by
    intro b hb
    exact (hcube b hb).trans (Real.rpow_le_rpow_of_exponent_le hz1.le (by
      dsimp only [L]; linarith))
  have hfirst : 2 * T.scale.val ≤ Z ^ L := by
    rw [hscale]
    calc
      2 * Z ^ r ≤ Z ^ A * Z ^ r := mul_le_mul_of_nonneg_right
        (hZ.trans (by simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hz1.le hA)) (Real.rpow_nonneg hz.le _)
      _ = Z ^ (A + r) := (Real.rpow_add hz _ _).symm
      _ ≤ Z ^ L := Real.rpow_le_rpow_of_exponent_le hz1.le (by dsimp only [L]; linarith)
  have hUi (i : FirstErrorSource.Index K S D T) :
      (FirstErrorBoxes.assignedScale K S D T grid centers side i).val ≤ Z ^ A := by
    change T.scale.val / (grid (centers.assignment side i.1 i.2)).val ≤ _
    rw [hscale]
    exact (div_le_self (Real.rpow_nonneg hz.le _) (hgrid _)).trans
      (Real.rpow_le_rpow_of_exponent_le hz1.le hr)
  have hcap : ∀ o, (rowCap K S (cubeDilation K S (outerAnchor K S D T o).1
      (outerAnchor K S D T o).2 o.1.val o.2.1.val)
      ⟨Z ^ (V + h), Real.rpow_pos_of_pos hz _⟩ (H o)).val ≤ (R o).val := by
    intro o
    exact FirstOuterPhysicalCap.rowCap_le_radius K S D Γ T hmask Z L M r ell V h tau
      hz1 hL hh hwidth hcoarse hfirst hcube hradius hscale
      ⟨Z ^ (V + h), Real.rpow_pos_of_pos hz _⟩ le_rfl o
  let target := D₀ * Q ^ 2 * (Z ^ (E + piRad) + Z ^ (E + piRad - saving))
  have htarget : 0 ≤ target := by
    dsimp only [target]
    exact mul_nonneg (mul_nonneg hD₀ (sq_nonneg Q))
      (add_nonneg (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hz.le _))
  have hbox (j : BoxIndex Z L) :
      boxedTotal K S D Γ hΓ μv T grid centers side R choice.massExponent choice.epsilon
        Z r ell V tau Θ ψ G hν hG hbase W hW m (FirstErrorBoxes.box K S D Γ T hmask I Z L j)
        ≤ target := by
    let Ij := FirstErrorBoxes.box K S D Γ T hmask I Z L j
    by_cases hne : Ij.Nonempty
    swap
    · have he : Ij = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      change boxedTotal K S D Γ hΓ μv T grid centers side R choice.massExponent choice.epsilon
        Z r ell V tau Θ ψ G hν hG hbase W hW m Ij ≤ _
      simpa only [boxedTotal, he, Finset.sum_empty, mul_zero] using htarget
    have hlen (c : Coordinate) := length_bounds Z L hz1 hL j c
    let Hexp := firstPhysicalHeight M r ell V (length Z j .firstDivisor)
      (length Z j .firstCommon) (length Z j .cubeLabel) + 12 * h + tau
    have hrow (i : FirstErrorSource.Index K S D T) (hi : i ∈ Ij) :
        (R i.1).val = Z ^ Hexp :=
      FirstErrorBoxes.radius_eq_of_box K S D Γ T hmask I Z L M r ell V h tau hz j i hi
    have hH0 : 0 ≤ Hexp := by
      obtain ⟨i, hi⟩ := hne
      have halive : FirstLiveCappedFreeEnergy.alive K S D Γ T H labels i.1 :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
      exact FirstLiveCappedFreeEnergy.alive_exponent_nonneg K S D Γ T H labels
        ⟨Z ^ (V + h), Real.rpow_pos_of_pos hz _⟩ R hlabels hcap i.1 halive
        Z Hexp hz1 (hrow i hi)
    have hHmax : Hexp ≤ 32 * (4 * A) := by
      dsimp only [Hexp, firstPhysicalHeight]
      have hd := (hlen .firstDivisor).2
      have hb := (hlen .firstCommon).1
      have hj := (hlen .cubeLabel).1
      dsimp only [L] at hd
      linarith
    have hcost (i : FirstErrorSource.Index K S D T) (hi : i ∈ Ij) :
        FirstLocalizedEnergy.radialScale K S D T i.1 ^ choice.epsilon *
          (R i.1).val ^ choice.massExponent ≤ choice.constant * Z ^ piRad := by
      rw [hrow i hi]
      exact choice.bound T hmask Z (-M) (ell + h) r Hexp hz1.le
        (by linarith) (by linarith) (by linarith) hHmax
        hradius.le hcube hscale.le i.1
    have hb := hb₀ T hmask grid centers side R Θ ψ G hν hG hbase Ij
      Z M r ell V (length Z j .firstDivisor) (extractedLength Z j side)
      (length Z j .firstCommon) (length Z j .activeConductor) (length Z j .cubeLabel)
      (length Z j .firstOverlap) h tau choice.massExponent choice.epsilon
      (ActualPoissonScale.fieldConstant K) (choice.constant * Z ^ piRad) hZ
      (by linarith) (by have hh := (hlen .activeConductor).2; dsimp only [L] at hh; linarith)
      (by have hh := (hlen .firstCommon).2; dsimp only [L] at hh; linarith)
      (by have hh := (hlen .firstOverlap).2; dsimp only [L] at hh; linarith)
      (by linarith) (hlen .cubeLabel).1 htauMin' hH0 hHmax
      (fun i hi => ⟨hUi i, (FirstErrorBoxes.assignedScale_bounds K S D Γ T hmask
        grid centers side I Z L r h hz1 hL hh hwidth hcoarse hfirst hscale j i hi).2⟩)
      hprime hweights hslots
      (fun i hi => FirstErrorBoxes.count_windows K S D Γ T hmask I Z L ell h hz1 hL
        hh hwidth hcoarse hfirst hcube j i hi)
      (ActualPoissonScale.fieldConstant_nonneg K)
      (mul_nonneg (zero_le_one.trans choice.one_le_constant) (Real.rpow_nonneg hz.le _))
      (fun i hi => FirstErrorBoxes.assigned_firstScalar_le K S D Γ T hmask grid centers side
        I Z L M r ell V h hz1 hL hh hwidth hcoarse hfirst hradius hscale j i hi)
      hcost hrow W hW m
    have hE : r + 3 * ell + V - length Z j .firstCommon - length Z j .cubeLabel +
        26 * h + tau + piError ≤ E := by
      dsimp only [E]
      linarith [(hlen .firstCommon).1, (hlen .cubeLabel).1]
    have hpowers := add_le_add
      (Real.rpow_le_rpow_of_exponent_le hz1.le hE)
      (Real.rpow_le_rpow_of_exponent_le hz1.le (sub_le_sub_right hE saving))
    have hcoef : 0 ≤ ActualPoissonScale.fieldConstant K *
        (choice.constant * Z ^ piRad) * C₀ * Q ^ 2 := by
      exact mul_nonneg (mul_nonneg (mul_nonneg
        (ActualPoissonScale.fieldConstant_nonneg K)
        (mul_nonneg (zero_le_one.trans choice.one_le_constant) (Real.rpow_nonneg hz.le _))) hC₀)
        (sq_nonneg Q)
    apply hb.trans ((mul_le_mul_of_nonneg_left hpowers hcoef).trans_eq ?_)
    change _ = D₀ * Q ^ 2 * (Z ^ (E + piRad) + Z ^ (E + piRad - saving))
    rw [← rpow_mul_pair Z E piRad saving hz]
    dsimp only [D₀, Q]
    ring
  rw [error_total_eq K S D Γ hΓ μv T H labels grid centers side R choice.massExponent
    choice.epsilon Z r ell V tau Θ ψ G hν hG hbase W hW m hz.le]
  rw [boxedTotal_sum_boxes K S D Γ hΓ μv T grid centers side R choice.massExponent
    choice.epsilon Z r ell V tau Θ ψ G hν hG hbase W hW m hmask I L]
  calc
    _ ≤ ∑ _j : BoxIndex Z L, target := Finset.sum_le_sum fun j _ => hbox j
    _ = (Fintype.card (BoxIndex Z L) : ℝ) * target := by simp
    _ ≤ (Cbox * Z ^ piBox) * target :=
      mul_le_mul_of_nonneg_right (hbbox Z hz1.le) htarget
    _ = _ := by
      change (Cbox * Z ^ piBox) * (D₀ * Q ^ 2 *
        (Z ^ (E + piRad) + Z ^ (E + piRad - saving))) = _
      have he := rpow_mul_pair Z (E + piRad) piBox saving hz
      calc
        _ = (Cbox * D₀) * Q ^ 2 *
          (Z ^ piBox * (Z ^ (E + piRad) + Z ^ (E + piRad - saving))) := by ring
        _ = _ := by
          rw [he]
          dsimp only [E, Q]
          congr 2 <;> congr 1 <;> ring

end HeckeSkeleton.Moments.MOM_INV_STEP.ActualErrorBudget

end
