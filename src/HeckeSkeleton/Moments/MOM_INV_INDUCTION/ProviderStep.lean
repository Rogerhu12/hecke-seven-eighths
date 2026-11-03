import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalStep
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderRecursion

/-!
# The actual inverse step in the induction envelope

This theorem calls the published complete actual-parent provider. Its
only recursive premise is that provider's `AllSmallerPieces` statement
on the original generated children. It keeps those children and their
geometry unchanged, absorbs the primitive principal term using the
actual nonzero puncture norm, and returns the factor `3 C Cih` used by
backward induction. No parent reconstruction or energy identity is
assumed in this adapter.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderStep

open HeckeSkeleton.Moments.MOM_INV_STEP
open HeckeSkeleton.Moments.MOM_INV_INDUCTION

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

set_option maxHeartbeats 1600000 in
include hΓ μv hallowed ν μ in
/-- The authoritative one-step implication, normalized for finite
backward induction with a common child constant at least one. -/
theorem exists_uniform_normalized_step
    (localTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (localTest v))
    (hcs : ∀ v ∈ S, HasCompactSupport (localTest v))
    (slotCap a p : ℕ) (A pi tauMin : ℝ)
    (hA : 1 ≤ A) (hpi : 0 < pi) (htauMin : 0 < tauMin)
    (t : Finset (ℕ × ℕ)) :
    ∃ qArch qW : Finset (ℕ × ℕ), ∃ C : ℝ, 1 ≤ C ∧
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
      0 ≤ eps → 1 ≤ Cih → 0 ≤ Aw →
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
        3 * C * Aw * qArch.sup (schwartzSeminormFamily ℝ Varch ℂ) T.archTest *
          (qW.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 * Cih *
          Z ^ (r + 3 * ell + V + 40 * eta + tau + pi + eps)) ∧
      ActualStepGeometry.AllChildrenGeometry K S D Γ T Θ ψ G hν hG hbase hmask
        A Z M r ell V h tau hz1 H labels centers hprime hweights slotCap hslots z c d eta := by
  obtain ⟨qArch, qW, C, hC, hstep⟩ :=
    HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalStep.exists_uniform_step
      K S D Γ hΓ hallowed μv ν μ localTest hlc hcs slotCap a p A pi tauMin
      hA hpi htauMin t
  refine ⟨qArch, qW, max 1 C, le_max_left _ _, ?_⟩
  intro σ _ T hlocal hmask Θ ψ G hν hG hbase hcal labels w W hW
    Z M r ell V h tau Q z c d eta eps Cih Aw hZ hM hr0 hell hV hh htau htauMin'
    hwidth hmesh hstepsize hnonterminal hbase_eq hradius hscale hcolumnScale hcut
    hcube hlabels hparent hc hz hRho hRhoNorm heps hCih hAw hw0 hw hbeta hbetaSmall
    hbg hprime hweights hslots
  dsimp only
  intro hih
  have hCih0 : 0 ≤ Cih := zero_le_one.trans hCih
  have hb := hstep T hlocal hmask Θ ψ G hν hG hbase hcal labels w W hW
    Z M r ell V h tau Q z c d eta eps Cih Aw hZ hM hr0 hell hV hh htau htauMin'
    hwidth hmesh hstepsize hnonterminal hbase_eq hradius hscale hcolumnScale hcut
    hcube hlabels hparent hc hz hRho hRhoNorm heps hCih0 hAw hw0 hw hbeta hbetaSmall
    hbg hprime hweights hslots hih
  have hz1 : 1 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hRhoNorm1 : (1 : ℝ) ≤ (Ideal.absNorm T.columns.puncture.radical : ℝ) := by
    have hn : 0 < Ideal.absNorm T.columns.puncture.radical :=
      Nat.pos_of_ne_zero (fun he =>
        SourceLengths.radical_ne_zero T.columns.puncture hRho
          (Ideal.absNorm_eq_zero_iff.mp he))
    exact_mod_cast hn
  have hQ : 0 ≤ Q := by
    by_contra hQ
    have hp := Real.rpow_lt_one_of_one_lt_of_neg hz1 (lt_of_not_ge hQ)
    linarith
  have hMF : M ≤ r + 3 * ell + V := by linarith [hparent.1]
  have hS : 0 ≤ C * Aw * qArch.sup (schwartzSeminormFamily ℝ Varch ℂ) T.archTest *
      (qW.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hC hAw) (apply_nonneg _ _)) (sq_nonneg _)
  have hn := provider_step_bound
    (E := Z ^ (-r - 2 * ell - V) *
      (∑ f ∈ labels, w f * ‖FirstCappedProduction.parent K S D Γ T f‖))
    (F := r + 3 * ell + V) (M := M) (h := h) (eta := eta)
    (tau := tau) (pi := pi) (eps := eps) (B := Cih)
    (S := C * Aw * qArch.sup (schwartzSeminormFamily ℝ Varch ℂ) T.archTest *
      (qW.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2)
    hz1.le hMF hh.1 hmesh htau.1 heps hCih hS
    (by simpa only [stepLoss, add_assoc] using hb.1)
  refine ⟨hn.trans ?_, hb.2⟩
  simp only [stepLoss]
  calc
    _ = 3 * C * Aw * qArch.sup (schwartzSeminormFamily ℝ Varch ℂ) T.archTest *
        (qW.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 * Cih *
        Z ^ (r + 3 * ell + V + 40 * eta + tau + pi + eps) := by ring
    _ ≤ _ := by
      gcongr
      exact le_max_right (1 : ℝ) C

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderStep

end
