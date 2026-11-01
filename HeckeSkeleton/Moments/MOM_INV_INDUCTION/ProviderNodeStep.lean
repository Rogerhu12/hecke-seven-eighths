import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderUniformChildren
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderStep
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderChildParent

/-!
# The actual one-step theorem on a complete canonical node

A canonical node whose averaged label is nonterminal is put into the
provider using the proved fixed positive orbital majorant and the
singleton unit cube. All parent-data fields are constructed. The
provider's entire recursive premise is supplied by the uniform bound on
the genuine next node class, using `ProviderUniformChildren`.

The fixed orbital test seminorm and its covolume are absorbed into one
constant chosen before any node. Thus the only variable profile in the
conclusion is the original node's radial test.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderNodeStep

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckeSkeleton.Moments.MOMInvStep
open HeckeSkeleton.Moments.MOM_INV_STEP
open CanonicalNormPools FixedTripleEnergy FirstParentRows
open HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderNodes
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

include hΓ hallowed μv ν μ in
/-- A proved uniform successor implication on the literal complete
node class in the nonterminal-label range. No `StepEnergy` or assumed
parent reconstruction occurs in the statement. -/
theorem exists_uniform_long_label_step
    (slotCap : ℕ) (A pi tauMin : ℝ) (hA : 1 ≤ A)
    (hpi : 0 < pi) (htauMin : 0 < tauMin) (t : Finset (ℕ × ℕ)) :
    ∃ q : Finset (ℕ × ℕ), ∃ C : ℝ, 1 ≤ C ∧
      ∀ {σ : Type u} [DecidableEq σ] (Θ : Subgroup (HeckeCharacter K))
        (ψ Λ G : HeckeCharacter K), G ∈ Θ →
      ∀ (Z Fcap c z lo hi d eta h tau eps Cih Rmax : ℝ)
        (x : Node K S Γ Θ ψ σ),
      2 ≤ Z → Fcap ≤ A → 0 ≤ c → 0 ≤ z →
      x.Admissible D Λ G slotCap Z Fcap c z lo hi → x.rowLength ≤ Rmax →
      h ∈ Set.Icc (0 : ℝ) 1 → tau ∈ Set.Icc (0 : ℝ) A → tauMin ≤ tau →
      2 ≤ Z ^ h → h ≤ eta / 32 → eta ≤ d / 16 → d ≤ x.labelLength →
      0 ≤ eps → 1 ≤ Cih →
      UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
        (Fcap + 11 * eta) (c - 7 * eta) z lo hi eps (Rmax - d) Cih t →
      x.energy D slotCap ≤ (3 * C * Cih) *
        (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 *
          Z ^ (x.totalLength + 40 * eta + tau + pi + eps) := by
  obtain ⟨qArch, qW, C, hC, hstep⟩ :=
    ProviderStep.exists_uniform_normalized_step K S D Γ hΓ hallowed μv ν μ
      (rowBallFiniteFamily K S 1) (rowBallFiniteFamily_locallyConstant K S 1)
      (rowBallFiniteFamily_compactSupport K S 1) slotCap (9 + 4 * slotCap) 0
      A pi tauMin hA hpi htauMin t
  let Cnode := (InverseRowMajorant.rowCovolume K S)⁻¹ * C *
    qArch.sup (schwartzSeminormFamily ℝ Varch ℂ) (rowBallArchTest K S 1)
  refine ⟨qW, max 1 Cnode, le_max_left _ _, ?_⟩
  intro σ _ Θ ψ Λ G hG Z Fcap c z lo hi d eta h tau eps Cih Rmax x hZ hFcap hc hz
    hx hM hh htau htau' hwidth hmesh hstepsize hnonterminal heps hCih hih
  have hz1 : 1 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hz0 : 0 < Z := zero_lt_one.trans hz1
  have hCih0 : 0 ≤ Cih := zero_le_one.trans hCih
  have hbase : 1 < x.family.base := by rw [hx.base_eq]; exact hz1
  have hbase0 : 0 < x.family.base := zero_lt_one.trans hbase
  let Hrow : {r : ℝ // 0 < r} := ⟨Z ^ x.rowLength, Real.rpow_pos_of_pos hz0 _⟩
  let T := ProviderChildParent.parentData K S x.family x.triple hbase0 Hrow
  let labels := ProviderChildParent.exteriorLabels K S x.labels
  let w : Ext → ℝ := fun f => labelDivisorWeight slotCap f.val.val
  have hν : BackgroundCycle.Admissible K Θ ψ T.columns.background :=
    x.family.background_admissible x.triple
  have hTbase : 1 < T.columns.base := hbase
  have hmask : T.mask = ∅ := rfl
  have hTbase_eq : T.columns.base = Z := hx.base_eq
  have hcal : ThetaCalibrationInput K Sset D T.columns.lambda G := hx.calibration
  have hradius : T.radius.val = Z ^ (-x.rowLength) := by
    change (Z ^ x.rowLength)⁻¹ = Z ^ (-x.rowLength)
    rw [Real.rpow_neg hz0.le]
  have hscale : T.scale.val = Z ^ x.columnLength := by
    change x.family.base ^ x.columnLength = _
    rw [hx.base_eq]
  have hcolumnScale : T.columns.base ^ T.columns.length = T.scale.val := rfl
  have hcut : T.columns.cutoff = x.test := rfl
  have hlens := Node.Admissible.lengths_le x hx hz1 hc hz
  have hMr : x.rowLength ∈ Set.Icc (0 : ℝ) A :=
    ⟨hx.row_nonneg, hlens.1.trans hFcap⟩
  have hNr : x.columnLength ∈ Set.Icc (0 : ℝ) A :=
    ⟨hx.column_nonneg, hlens.2.1.trans hFcap⟩
  have hVr : x.labelLength ∈ Set.Icc (0 : ℝ) A :=
    ⟨hx.label_nonneg, hlens.2.2.trans hFcap⟩
  have hell : (0 : ℝ) ∈ Set.Icc (0 : ℝ) A := ⟨le_rfl, zero_le_one.trans hA⟩
  have heta : 0 ≤ eta := by linarith [hh.1]
  have hd : 0 ≤ d := by linarith
  have hcube : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ ((0 : ℝ) + h) := by
    intro b hb
    have hb' : b = FirstInversePoisson.unitIdeal K S := Finset.mem_singleton.mp hb
    subst b
    change ((Ideal.absNorm (1 : Ideal (𝓞 K)) : ℕ) : ℝ) ≤ Z ^ (0 + h)
    simpa only [map_one, Nat.cast_one, zero_add] using (le_trans (by norm_num : (1 : ℝ) ≤ 2) hwidth)
  have hlabels : ∀ f ∈ labels, height K Sset f ≤ Z ^ (x.labelLength + h) := by
    intro f hf
    have hf' : f.val.val ∈ x.labels := Finset.mem_preimage.mp hf
    exact (hx.label_bound f.val.val hf').trans
      (Real.rpow_le_rpow_of_exponent_le hz1.le (le_add_of_nonneg_right hh.1))
  have hparent : HeckePort.Moments.CanonicalMargins
      (x.columnLength + 3 * 0 + x.labelLength) x.rowLength
      (x.punctureLength Z) z c := by
    simpa only [mul_zero, add_zero, Node.totalLength] using hx.margins
  have hRho : T.columns.puncture ≠ 0 := hx.puncture_nonzero
  have hRhoNorm : (Ideal.absNorm T.columns.puncture.radical : ℝ) ≤ Z ^ x.punctureLength Z :=
    (Node.Admissible.puncture_norm x hx hz1).le
  have hw0 : ∀ f ∈ labels, 0 ≤ w f := fun f _ => labelDivisorWeight_nonneg slotCap _
  have hw : ∀ f ∈ labels,
      w f ≤ 1 * ((idealDivisors f.val.val).card : ℝ) ^ (9 + 4 * slotCap) := by
    intro f hf
    simp only [w, labelDivisorWeight, one_mul, le_refl]
  have hbeta : ∀ b ∈ T.cubes, ∀ f ∈ labels,
      ‖T.columns.labelWeight b f‖ ≤ ((idealDivisors f.val.val).card : ℝ) ^ 0 := by
    intro b hb f hf
    change ‖(1 : ℂ)‖ ≤ _
    simp
  have hbetaSmall : ∀ b ∈ T.cubes, ∀ f ∈ labels,
      ‖T.columns.labelWeight b f‖ ≤ Z ^ h := by
    intro b hb f hf
    change ‖(1 : ℂ)‖ ≤ _
    simpa only [norm_one] using (le_trans (by norm_num : (1 : ℝ) ≤ 2) hwidth)
  have hbg : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset →
      UnramifiedAt K T.columns.background p := hx.background_unramified
  have hprime : ∀ i ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists i, Prime p := hx.marks.prime
  have hweights : ∀ i ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists i,
      ‖T.columns.primeWeights i p‖ ≤ 1 := hx.marks.weights_le
  have hslots : T.columns.slots.card ≤ slotCap := hx.marks.card_le
  let H := FirstLocalizedCutoff.sourceCutoff K S D T Z tau hz0
  let centers := FirstCanonicalCenters.centers_of_power K S D T Z A h x.columnLength
    hz1 hh.2 hwidth hscale hNr.2
  have hsmall := ProviderUniformChildren.all_smaller_pieces_of_uniform K S D Γ T Θ ψ G
    hν hG hTbase hmask A Z x.rowLength x.columnLength 0 x.labelLength h tau hz1
    H labels centers hprime hweights slotCap hslots
    Λ (x.punctureLength Z) z c d eta Fcap lo hi Rmax eps Cih x.markLengths t
    hA hNr hell hx.label_nonneg hh hwidth (by linarith) hstepsize heta hd hM hTbase_eq
    hscale hcube hparent (by simpa using hnonterminal) hRho hRhoNorm hx.lambda_eq hcal hbg hx.marks
    (by simpa only [mul_zero, add_zero, Node.totalLength] using hx.total_le) hih
  have hp := (hstep T rfl hmask Θ ψ G hν hG hTbase hcal labels w x.test hx.test_support
    Z x.rowLength x.columnLength 0 x.labelLength h tau (x.punctureLength Z) z c d eta
    eps Cih 1 hZ hMr hNr hell hVr hh htau htau' hwidth hmesh hstepsize
    (by simpa using hnonterminal) hTbase_eq hradius hscale hcolumnScale hcut hcube hlabels
    hparent hc hz hRho hRhoNorm heps hCih zero_le_one hw0 hw hbeta hbetaSmall
    hbg hprime hweights hslots hsmall).1
  have hpool : x.family.columns x.triple =
      squarefreePool K Sset (2 * x.family.base ^ x.columnLength) := by
    simpa only [hx.base_eq] using hx.complete_pool
  have htransfer := ProviderChildParent.normalized_childEnergy_le_parent
    K S Γ D hΓ x.family x.triple hbase0 Hrow hpool hx.test_support
    slotCap x.labelLength x.labels x.rows hx.row_bound
  change x.energy D slotCap ≤ (InverseRowMajorant.rowCovolume K S)⁻¹ *
    (x.family.base ^ (-x.columnLength - x.labelLength) *
      ∑ f ∈ labels, w f * ‖FirstCappedProduction.parent K S D Γ T f‖) at htransfer
  rw [hx.base_eq] at htransfer
  have hcov : 0 ≤ (InverseRowMajorant.rowCovolume K S)⁻¹ :=
    inv_nonneg.mpr (InverseRowMajorant.rowCovolume_pos K S).le
  have hp' := mul_le_mul_of_nonneg_left hp hcov
  simp only [mul_zero, sub_zero, add_zero, mul_one] at hp'
  apply htransfer.trans (hp'.trans ?_)
  change _ ≤ (3 * max 1 Cnode * Cih) *
    (qW.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 *
      Z ^ (x.totalLength + 40 * eta + tau + pi + eps)
  calc
    _ = (3 * Cnode * Cih) *
        (qW.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 *
          Z ^ (x.totalLength + 40 * eta + tau + pi + eps) := by
      change _ = _
      dsimp only [Cnode, Node.totalLength, T, ProviderChildParent.parentData]
      ring
    _ ≤ _ := by
      gcongr
      exact le_max_right (1 : ℝ) Cnode

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderNodeStep

end
