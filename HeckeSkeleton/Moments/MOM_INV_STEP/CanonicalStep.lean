import HeckeSkeleton.Moments.MOM_INV_STEP.ActualFirstTotalBudget
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualStepGeometry
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstNormalizedParent
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentErrorBudget
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCanonicalCenters
import HeckeSkeleton.Moments.MOM_INV_STEP.FinalStepBounds

/-!
# The actual canonical inverse single step

The theorem starts with the literal original squared orbital series.
Both Poisson transforms, their finite positive sources, their principal
restoration and their complete localized infinite tails are those
constructed from that parent. The only recursive energy premise is on
the actual smaller canonical pieces, with their original marked slots,
reconstructed punctures, labels, and fixed-triple fibers.

All constants, both finite seminorms, and both spectral degrees precede
the parent, base, original prime lists, physical lengths, and tests.
The prescribed first cap and the deterministic first centers are
constructed internally. The companion geometry conclusion concerns
exactly the same generation set as the recursive premise.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalStep

open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree.LargeSieve
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open CanonicalNormPools CanonicalBlock FirstParentRows FirstOuterCenters
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "Varch" => mixedEmbedding.euclidean.mixedSpace K

/-- The coarse coordinate box is derived from the original parent caps.
It is used solely to construct the first row cap, before the second
source exists. -/
theorem parent_coordinate_caps {σ : Type*} (T : FirstParentEnergy.Data K S (σ := σ))
    (A Z r ell h : ℝ) (hA : 1 ≤ A) (hZ : 2 ≤ Z)
    (hr : r ≤ A) (hell : ell ≤ A) (hh : h ≤ 1)
    (hscale : T.scale.val = Z ^ r)
    (hcube : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ (ell + h)) :
    (∀ b ∈ T.cubes, height K Sset b ≤ Z ^ (4 * A)) ∧
      2 * T.scale.val ≤ Z ^ (4 * A) := by
  have hz1 : 1 ≤ Z := le_trans (by norm_num) hZ
  have hz0 : 0 < Z := lt_of_lt_of_le (by norm_num) hZ
  constructor
  · intro b hb
    exact (hcube b hb).trans (Real.rpow_le_rpow_of_exponent_le hz1 (by linarith))
  · calc
      2 * T.scale.val ≤ Z * Z ^ r :=
        mul_le_mul hZ hscale.le T.scale.property.le hz0.le
      _ = Z ^ (1 + r) := by rw [Real.rpow_add hz0, Real.rpow_one]
      _ ≤ Z ^ (4 * A) := Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)

include hΓ μv hallowed ν μ in
/-- The complete one-step conclusion with constants before all source
data. The child predicate is the literal actual generation set, and its
geometric closure is proved as part of the conclusion. No parent row
estimate, reconstruction identity, source count, or physical scalar
bound is assumed. The empty extra orbital mask leaves the original
coefficient puncture arbitrary and nonzero. -/
theorem exists_uniform_step
    (localTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (localTest v))
    (hcs : ∀ v ∈ S, HasCompactSupport (localTest v))
    (slotCap a p : ℕ) (A pi tauMin : ℝ)
    (hA : 1 ≤ A) (hpi : 0 < pi) (htauMin : 0 < tauMin)
    (t : Finset (ℕ × ℕ)) :
    ∃ qArch qW : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ {σ : Type*} [DecidableEq σ] (T : FirstParentEnergy.Data K S (σ := σ)),
      T.localTest = localTest → ∀ hmask : T.mask = ∅,
      ∀ (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
        (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
        (hbase : 1 < T.columns.base)
        (hcal : ThetaCalibrationInput K Sset D T.columns.lambda G)
        (labels : Finset Ext) (w : Ext → ℝ)
        (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
        (Z M r ell V h tau Q z c d eta eps Cih Aw : ℝ) (hZ : 2 ≤ Z),
      M ∈ Set.Icc (0 : ℝ) A → ∀ hr0 : r ∈ Set.Icc (0 : ℝ) A,
      ell ∈ Set.Icc (0 : ℝ) A → V ∈ Set.Icc (0 : ℝ) A →
      ∀ hh : h ∈ Set.Icc (0 : ℝ) 1, tau ∈ Set.Icc (0 : ℝ) A → tauMin ≤ tau →
      ∀ hwidth : 2 ≤ Z ^ h, h ≤ eta / 32 → eta ≤ d / 16 → d ≤ ell + V →
      T.columns.base = Z → T.radius.val = Z ^ (-M) →
      ∀ hscale : T.scale.val = Z ^ r,
      T.columns.base ^ T.columns.length = T.scale.val → T.columns.cutoff = W →
      (∀ b ∈ T.cubes, height K Sset b ≤ Z ^ (ell + h)) →
      (∀ f ∈ labels, height K Sset f ≤ Z ^ (V + h)) →
      HeckePort.Moments.CanonicalMargins (r + 3 * ell + V) M Q z c →
      0 ≤ c → 0 ≤ z → T.columns.puncture ≠ 0 →
      (Ideal.absNorm T.columns.puncture.radical : ℝ) ≤ Z ^ Q →
      0 ≤ eps → 0 ≤ Cih → 0 ≤ Aw →
      (∀ f ∈ labels, 0 ≤ w f) →
      (∀ f ∈ labels, w f ≤ Aw * ((idealDivisors f.val.val).card : ℝ) ^ a) →
      (∀ b ∈ T.cubes, ∀ f ∈ labels,
        ‖T.columns.labelWeight b f‖ ≤ ((idealDivisors f.val.val).card : ℝ) ^ p) →
      (∀ b ∈ T.cubes, ∀ f ∈ labels, ‖T.columns.labelWeight b f‖ ≤ Z ^ h) →
      (∀ q : HeightOneSpectrum (𝓞 K), q ∉ Sset →
        UnramifiedAt K T.columns.background q) →
      ∀ (hprime : ∀ k ∈ T.columns.slots, ∀ q ∈ T.columns.primeLists k, Prime q)
        (hweights : ∀ k ∈ T.columns.slots, ∀ q ∈ T.columns.primeLists k,
          ‖T.columns.primeWeights k q‖ ≤ 1)
        (hslots : T.columns.slots.card ≤ slotCap),
      let hz1 : 1 < Z := lt_of_lt_of_le (by norm_num) hZ
      let H := FirstLocalizedCutoff.sourceCutoff K S D T Z tau (zero_lt_one.trans hz1)
      let centers := FirstCanonicalCenters.centers_of_power K S D T Z A h r
        hz1 hh.2 hwidth hscale hr0.2
      ActualUniformProduction.AllSmallerPieces
        (K := K) (S := S) (D := D) (Γ := Γ) (T := T) (hmask := hmask)
        (A := A) (Z := Z) (M := M) (r := r) (ell := ell) (V := V) (h := h) (tau := tau)
        (hZ := hz1) (Θ := Θ) (ψ := ψ) (G := G) (hν := hν) (hG := hG) (hbase := hbase)
        (H := H) (oldLabels := labels) (centers := centers)
        (hprime := hprime) (hweights := hweights) (slotCap := slotCap) (hcap := hslots)
        eps Cih t →
      (Z ^ (-r - 2 * ell - V) *
          (∑ f ∈ labels, w f * ‖FirstCappedProduction.parent K S D Γ T f‖) ≤
        C * Aw * qArch.sup (schwartzSeminormFamily ℝ Varch ℂ) T.archTest *
          (qW.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
          ((Cih + 1) * Z ^ (r + 3 * ell + V + 40 * eta + tau + pi + eps) +
            Z ^ (M + 5 * h + pi))) ∧
      ActualStepGeometry.AllChildrenGeometry K S D Γ T Θ ψ G hν hG hbase hmask
        A Z M r ell V h tau hz1 H labels centers hprime hweights slotCap hslots z c d eta := by
  have hpi0 : 0 < pi / 8 := by positivity
  let choice := UniformFirstWeightChoice.choose K S D (2 * A) (32 * (4 * A)) (pi / 8)
    (by linarith) (by linarith) hpi0
  let m := ActualFirstTotalBudget.firstDegree K S D A hA slotCap pi hpi t
  obtain ⟨sFirst, CFirst, hCFirst, hfirst⟩ := FirstNormalizedParent.exists_parent_source_bound
    K S D Γ hΓ hallowed μv ν μ localTest hlc hcs a p choice.epsilon choice.massExponent
      choice.epsilon_pos choice.mass_pos m
  obtain ⟨sError, CError, hCError, herror⟩ := FirstParentErrorBudget.exists_actualError_bound
    K S D Γ hΓ μv ν slotCap a A tauMin 1 (pi / 8) hA htauMin (by norm_num) hpi0
      localTest hlc hcs
  obtain ⟨sTotal, CTotal, hCTotal, htotal⟩ := ActualFirstTotalBudget.exists_total_bound
    K S D Γ hΓ μv hallowed ν μ slotCap A pi tauMin hA hpi htauMin choice t
  let C := CFirst * CTotal + 2 * CError
  have hC : 0 ≤ C := add_nonneg (mul_nonneg hCFirst hCTotal) (by positivity)
  refine ⟨sFirst ∪ sError, sTotal ∪ {(0,0)}, C, hC, ?_⟩
  intro σ _ T hlocal hmask Θ ψ G hν hG hbase hcal labels w W hW
    Z M r ell V h tau Q z c d eta eps Cih Aw hZ hM hr0 hell hV hh htau htauMin'
    hwidth hmesh hstep hnonterminal hbase_eq hradius hscale hcolumnScale hcut
    hcube hlabels hparent hc hz hRho hRhoNorm heps hCih hAw hw0 hw hbeta hbetaSmall
    hbg hprime hweights hslots
  dsimp only
  intro hih
  let hz1 : 1 < Z := lt_of_lt_of_le (by norm_num) hZ
  let hz0 : 0 < Z := zero_lt_one.trans hz1
  have hr : r ≤ A := hr0.2
  let grid := FirstCanonicalCenters.grid Z A
  let centers := FirstCanonicalCenters.centers_of_power K S D T Z A h r
    hz1 hh.2 hwidth hscale hr
  let H := FirstLocalizedCutoff.sourceCutoff K S D T Z tau hz0
  let R := FirstOuterPhysicalCap.radius K S D Γ T hmask Z (4 * A) M r ell V h tau hz0
  let F : {r : ℝ // 0 < r} := ⟨Z ^ (V + h), Real.rpow_pos_of_pos hz0 _⟩
  let qa := (sFirst ∪ sError).sup (schwartzSeminormFamily ℝ Varch ℂ) T.archTest
  let qw := (sTotal ∪ {(0,0)}).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let Emain := Z ^ (r + 3 * ell + V + 40 * eta + tau + pi + eps)
  let Eerror := Z ^ (M + 5 * h + pi)
  let B := CTotal * qw ^ 2 * (Cih + 1) * Emain
  have hqa : 0 ≤ qa := apply_nonneg _ _
  have hqw : 0 ≤ qw := apply_nonneg _ _
  have hEmain : 0 ≤ Emain := Real.rpow_nonneg hz0.le _
  have hEerror : 0 ≤ Eerror := Real.rpow_nonneg hz0.le _
  have hB : 0 ≤ B := mul_nonneg
    (mul_nonneg (mul_nonneg hCTotal (sq_nonneg _)) (by linarith)) hEmain
  have hsFirst : sFirst.sup (schwartzSeminormFamily ℝ Varch ℂ) T.archTest ≤ qa :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_left) _
  have hsError : sError.sup (schwartzSeminormFamily ℝ Varch ℂ) T.archTest ≤ qa :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) _
  have hsTotal : sTotal.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ qw :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_left) _
  have h00 : SchwartzMap.seminorm ℝ 0 0 W ≤ qw := by
    have hh := Seminorm.le_def.mp (Finset.le_sup
      (f := schwartzSeminormFamily ℝ ℝ ℂ)
      (show (0,0) ∈ sTotal ∪ {(0,0)} by simp)) W
    exact hh
  have hcaps := parent_coordinate_caps K S T A Z r ell h hA hZ hr hell.2 hh.2 hscale hcube
  have hrow : ∀ o, (rowCap K S (cubeDilation K S (outerAnchor K S D T o).1
      (outerAnchor K S D T o).2 o.1.val o.2.1.val) F (H o)).val ≤ (R o).val := by
    intro o
    exact FirstOuterPhysicalCap.rowCap_le_radius K S D Γ T hmask Z (4 * A) M r ell V h tau
      hz1 (by linarith) hh.1 hwidth hcaps.1 hcaps.2 hcube hradius hscale F le_rfl o
  have htot (side : Bool) :
      FirstNormalizedSource.total K S D Γ T H labels grid centers side R
        choice.massExponent choice.epsilon Z r ell V Θ ψ G hν hG W hW m ≤ B := by
    have hb := htotal T hmask Θ ψ G hν hG hbase labels Z M r ell V h tau Q z c eta eps Cih hZ
      hM hr0 hell hV hh htau htauMin' hwidth hmesh hbase_eq hradius hscale hcube hlabels
      hparent.1 hc hz hRho hRhoNorm heps hCih hcal hbg hprime hweights hslots
      centers hih W hW side
    apply hb.trans
    dsimp only [B, Emain]
    gcongr <;> exact hsTotal
  have hsource0 (side : Bool) :
      0 ≤ FirstNormalizedSource.total K S D Γ T H labels grid centers side R
        choice.massExponent choice.epsilon Z r ell V Θ ψ G hν hG W hW m :=
    FirstNormalizedSource.total_nonneg K S D Γ T H labels grid centers side R
      choice.massExponent choice.epsilon Z r ell V Θ ψ G hν hG W hW m hz0.le
  have hroots := FinalStepBounds.sqrt_product_le (hsource0 false) (hsource0 true) hB
    (htot false) (htot true)
  have hp := hfirst T hlocal Θ ψ G hν hG hcal Z r ell V tau hz0 labels w grid centers W hW F R Aw
    hAw hw0 hlabels hrow hw hbeta (fun q hq => hcal.G_unramified q hq)
    hcolumnScale hbase hcut hprime
  have he := herror T hlocal hmask G hcal labels w Z M r ell V h tau Aw hz1
    hM.1 hM.2 hr0.1 hr0.2 hell.1 hell.2 hV.1 hV.2 hh.1 hh.2 hwidth htauMin' hAw
    hradius hscale hslots hweights hcube hlabels hbetaSmall hw0 hw W hcut
  have hep := FinalStepBounds.parent_error_powers_le Z M h pi 1 hz1.le hM.1 hh.1 hpi.le
    (by norm_num)
  have he' : Z ^ (-r - 2 * ell - V) *
      (∑ f ∈ labels, w f * FirstCappedProduction.actualError K S D Γ hΓ μv T f Z tau) ≤
      (2 * CError) * Aw * qa * qw ^ 2 * Eerror := by
    apply he.trans
    calc
      _ ≤ CError * Aw * qw ^ 2 * qa * (2 * Eerror) := by
        gcongr <;> first | exact h00 | exact hsError | exact hep
      _ = _ := by ring
  constructor
  · have hmain := mul_le_mul_of_nonneg_left hroots
      (mul_nonneg (mul_nonneg hCFirst
        (apply_nonneg (sFirst.sup (schwartzSeminormFamily ℝ Varch ℂ)) T.archTest)) hAw)
    have hmain' :
        (CFirst * sFirst.sup (schwartzSeminormFamily ℝ Varch ℂ) T.archTest * Aw) * B ≤
        (CFirst * CTotal) * Aw * qa * qw ^ 2 * ((Cih + 1) * Emain) := by
      calc
        _ = (CFirst * CTotal) * Aw *
            sFirst.sup (schwartzSeminormFamily ℝ Varch ℂ) T.archTest * qw ^ 2 *
            ((Cih + 1) * Emain) := by dsimp only [B]; ring
        _ ≤ _ := by gcongr <;> exact hsFirst
    apply hp.trans ((add_le_add (hmain.trans hmain') he').trans ?_)
    have hCF : CFirst * CTotal ≤ C := by
      dsimp only [C]
      exact le_add_of_nonneg_right (by positivity)
    have hCE : 2 * CError ≤ C := by dsimp only [C]; exact le_add_of_nonneg_left (mul_nonneg hCFirst hCTotal)
    calc
      _ ≤ C * Aw * qa * qw ^ 2 * ((Cih + 1) * Emain) +
          C * Aw * qa * qw ^ 2 * Eerror := by
        gcongr <;> first | exact hCF | exact hCE
      _ = _ := by dsimp only [qa, qw, Emain, Eerror]; ring
  · exact ActualStepGeometry.all_children_geometry K S D Γ T Θ ψ G hν hG hbase hmask
      A Z M r ell V h tau hz1 H labels centers hprime hweights slotCap hslots Q z c d eta hA
      hr0 hell hV.1 hh hwidth (by linarith [hh.1]) hstep hbase_eq hscale hcube hparent
      hnonterminal hRho hRhoNorm

end HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalStep

end
