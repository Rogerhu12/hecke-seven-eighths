import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionProvider
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionGeometry
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderStep
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderUniformChildren
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMonotonicity

/-!
# The genuine recursive estimate for each long cube annulus

This theorem constructs the literal canonical parent of every common
Mellin piece. Its complete recursive premise comes from the uniform
bound on the next actual node class. The step uses 2d/3 and eta/2:
the provider's proved 3d/2 row gain is exactly the original d, while
the fixed annular profile shift fits inside the prescribed next margin
and capacity. No polynomial-identification or smaller-energy premise
is added to the node class.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionNodeStep

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckeSkeleton.Moments.MOMInvStep HeckeSkeleton.Moments.MOM_INV_STEP
open CanonicalNormPools FixedTripleEnergy FirstParentRows
open ProviderNodes CubeCompletionGeometry CubeCompletionEnergy CubeCompletionMellin
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
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
local notation "Varch" => mixedEmbedding.euclidean.mixedSpace K

def coefficients {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}
    (x : Node K S Γ Θ ψ σ) (P : Ideal (𝓞 K) → Prop)
    (B : Finset Ext) (H : ℝ) (fk : Ext × (Ideal (𝓞 K) × Sector)) : Ext → Ext → ℂ :=
  CubeCompletionProvider.arithmeticCoefficient K S D
    (ProviderChildParent.columns K S x.family x.triple) P B H fk.1
    (fun I => CanonicalChildren.sectorRow K Sset D
      (CanonicalSectors.sectorUnit K Sset Γ) I fk.2)

def annularEnergy {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}
    (slotCap : ℕ) (x : Node K S Γ Θ ψ σ) (P : Ideal (𝓞 K) → Prop)
    (B : Finset Ext) (H : ℝ) (t : ℝ) (i : SchwartzTestPartition.Index) : ℝ :=
  CubeCompletionEnergy.annularEnergy
    ((ProviderChildParent.exteriorLabels K S x.labels) ×ˢ x.rows)
    (fun fk => labelDivisorWeight slotCap fk.1.val.val)
    B (squarefreePool K Sset (8 * x.family.base ^ x.columnLength))
    (height K Sset) (height K Sset) (coefficients K S D Γ x P B H)
    (x.family.base ^ x.columnLength / H ^ 3) t i

include hΓ hallowed μv ν μ in
/-- The recursive bound for the actual complete annular cube energy.
The constants and the finite seminorm precede every node, cube support,
Möbius selection, row, label, common frequency and smooth piece. -/
theorem exists_uniform_annular_step
    (slotCap : ℕ) (A pi tauMin : ℝ) (hA : 1 ≤ A)
    (hpi : 0 < pi) (htauMin : 0 < tauMin) (t : Finset (ℕ × ℕ)) :
    ∃ q : Finset (ℕ × ℕ), ∃ C : ℝ, 1 ≤ C ∧
      ∀ {σ : Type*} [DecidableEq σ] (Θ : Subgroup (HeckeCharacter K))
        (ψ Λ G : HeckeCharacter K), G ∈ Θ →
      ∀ (Z Fcap c z lo hi d eta h tau eps Cih Rmax : ℝ)
        (x : Node K S Γ Θ ψ σ),
      2 ≤ Z → Fcap ≤ A → 0 ≤ c - eta / 2 → 0 ≤ z →
      x.Admissible D Λ G slotCap Z Fcap c z lo hi → x.rowLength ≤ Rmax →
      h ∈ Set.Icc (0 : ℝ) 1 → tau ∈ Set.Icc (0 : ℝ) A → tauMin ≤ tau →
      2 ≤ Z ^ h → h ≤ eta / 128 → eta ≤ d / 16 →
      0 ≤ eps → 1 ≤ Cih →
      UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
        (Fcap + 11 * eta) (c - 7 * eta) z lo hi eps (Rmax - d) Cih t →
      ∀ (P : Ideal (𝓞 K) → Prop) (B : Finset Ext) (H : ℝ),
      1 ≤ H → H ^ 3 ≤ 2 * Z ^ x.columnLength →
      (∀ b ∈ B, height K Sset b ≤ 2 * H) → 2 * d / 3 ≤ cubeLength Z H →
      ∀ (s : ℝ) (i : SchwartzTestPartition.Index),
      |Real.logb Z (annularScale i)| ≤ eta / 8 →
      1 ≤ annularScale i * (Z ^ x.columnLength / H ^ 3) →
      annularEnergy K S D Γ slotCap x P B H s i ≤
        C * Cih * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) (annularTest s i)) ^ 2 *
          Z ^ (2 * annularLength Z x.columnLength H i + 5 * cubeLength Z H +
            2 * x.labelLength + 20 * eta + tau + pi + eps) := by
  obtain ⟨qArch, qW, C, hC, hstep⟩ :=
    ProviderStep.exists_uniform_normalized_step K S D Γ hΓ hallowed μv ν μ
      (rowBallFiniteFamily K S 1) (rowBallFiniteFamily_locallyConstant K S 1)
      (rowBallFiniteFamily_compactSupport K S 1) slotCap (9 + 4 * slotCap) 0
      (A + 4) pi tauMin (by linarith) hpi htauMin t
  let Ccube := 3 * (InverseRowMajorant.rowCovolume K S)⁻¹ * C *
    qArch.sup (schwartzSeminormFamily ℝ Varch ℂ) (rowBallArchTest K S 1)
  refine ⟨qW, max 1 Ccube, le_max_left _ _, ?_⟩
  intro σ _ Θ ψ Λ G hG Z Fcap c z lo hi d eta h tau eps Cih Rmax x
    hZ hFcap hc hz hx hM hh htau htau' hwidth hmesh hstepsize heps hCih hih
    P B H hH hsupport hB hlong s i hshift hnonneg
  have hz1 : 1 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hz0 := zero_lt_one.trans hz1
  have hb0 : 0 < x.family.base := hx.base_eq.symm ▸ hz0
  have heta : 0 ≤ eta := by linarith [hh.1]
  have hc0 : 0 ≤ c := by linarith
  have hd : 0 ≤ d := by linarith
  have hH0 := zero_lt_one.trans_le hH
  have hlens := Node.Admissible.lengths_le x hx hz1 hc0 hz
  let ell := cubeLength Z H
  let r := annularLength Z x.columnLength H i
  let C0 := ProviderChildParent.columns K S x.family x.triple
  let C' := CubeCompletionProvider.columns K S D C0 P B H r s i
  let Hrow : {r : ℝ // 0 < r} := ⟨Z ^ x.rowLength, Real.rpow_pos_of_pos hz0 _⟩
  let T := ProviderCubeParent.parentData K S C' B hb0 Hrow
  let labels := ProviderChildParent.exteriorLabels K S x.labels
  let w : Ext → ℝ := fun f => labelDivisorWeight slotCap f.val.val
  have hMr : x.rowLength ∈ Set.Icc (0 : ℝ) (A + 4) :=
    ⟨hx.row_nonneg, by linarith [hlens.1]⟩
  have hr : r ∈ Set.Icc (0 : ℝ) (A + 4) :=
    ⟨annularLength_nonneg hz1 i hnonneg,
      (annularLength_upper hZ hH i).trans (by linarith [hlens.2.1])⟩
  have hell : ell ∈ Set.Icc (0 : ℝ) (A + 4) :=
    ⟨cubeLength_nonneg hz1 hH,
      (cubeLength_upper hZ hH0 hsupport).trans (by linarith [hlens.2.1])⟩
  have hVr : x.labelLength ∈ Set.Icc (0 : ℝ) (A + 4) :=
    ⟨hx.label_nonneg, by linarith [hlens.2.2]⟩
  have hpars := provider_parameters hh.1 hmesh hstepsize
  have hbase : 1 < T.columns.base := by change 1 < x.family.base; rw [hx.base_eq]; exact hz1
  have hbase_eq : T.columns.base = Z := hx.base_eq
  have hν : BackgroundCycle.Admissible K Θ ψ T.columns.background :=
    x.family.background_admissible x.triple
  have hmask : T.mask = ∅ := rfl
  have hradius : T.radius.val = Z ^ (-x.rowLength) := by
    change (Z ^ x.rowLength)⁻¹ = Z ^ (-x.rowLength)
    rw [Real.rpow_neg hz0.le]
  have hscale : T.scale.val = Z ^ r := by
    change x.family.base ^ r = Z ^ r
    rw [hx.base_eq]
  have hannular : C0.base ^ r = annularScale i * (Z ^ x.columnLength / H ^ 3) := by
    change x.family.base ^ r = _
    rw [hx.base_eq]
    exact annularLength_scale hz1 hH0 i
  have hcube : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ (ell + h) := by
    intro b hb
    calc
      height K Sset b ≤ 2 * H := hB b hb
      _ ≤ Z ^ h * H := mul_le_mul_of_nonneg_right hwidth hH0.le
      _ = Z ^ (ell + h) := by
        rw [Real.rpow_add hz0, cubeLength_scale hz1 hH0]
        ring
  have hlabels : ∀ f ∈ labels, height K Sset f ≤ Z ^ (x.labelLength + h) := by
    intro f hf
    exact (hx.label_bound f.val.val (Finset.mem_preimage.mp hf)).trans
      (Real.rpow_le_rpow_of_exponent_le hz1.le (le_add_of_nonneg_right hh.1))
  have hparent : HeckePort.Moments.CanonicalMargins
      (r + 3 * ell + x.labelLength) x.rowLength (x.punctureLength Z) z (c - eta / 2) :=
    annular_margins hz1 hH0 i hshift hx.margins
  have hF : r + 3 * ell + x.labelLength ≤ Fcap + eta / 8 :=
    annular_capacity hz1 hH0 i hshift hx.total_le
  have hRho : T.columns.puncture ≠ 0 := hx.puncture_nonzero
  have hRhoNorm : (Ideal.absNorm T.columns.puncture.radical : ℝ) ≤ Z ^ x.punctureLength Z :=
    (Node.Admissible.puncture_norm x hx hz1).le
  have hw0 : ∀ f ∈ labels, 0 ≤ w f := fun _ _ => labelDivisorWeight_nonneg slotCap _
  have hw : ∀ f ∈ labels,
      w f ≤ 1 * ((idealDivisors f.val.val).card : ℝ) ^ (9 + 4 * slotCap) := by
    intro f hf
    simp only [w, labelDivisorWeight, one_mul, le_refl]
  have hbeta1 : ∀ b ∈ T.cubes, ∀ f ∈ labels, ‖T.columns.labelWeight b f‖ ≤ 1 := by
    intro b hb f hf
    exact CubeCompletionProvider.columns_labelWeight_le K S D C0 P B H r s i hH0 hB b hb f
  have hbeta : ∀ b ∈ T.cubes, ∀ f ∈ labels,
      ‖T.columns.labelWeight b f‖ ≤ ((idealDivisors f.val.val).card : ℝ) ^ 0 := by
    simpa only [pow_zero] using hbeta1
  have hbetaSmall : ∀ b ∈ T.cubes, ∀ f ∈ labels,
      ‖T.columns.labelWeight b f‖ ≤ Z ^ h :=
    fun b hb f hf => (hbeta1 b hb f hf).trans ((by norm_num : (1 : ℝ) ≤ 2).trans hwidth)
  have hbg : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset →
      UnramifiedAt K T.columns.background p := hx.background_unramified
  have hprime : ∀ j ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists j, Prime p := hx.marks.prime
  have hweights : ∀ j ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists j,
      ‖T.columns.primeWeights j p‖ ≤ 1 := hx.marks.weights_le
  have hslots : T.columns.slots.card ≤ slotCap := hx.marks.card_le
  have hih' : UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
      ((Fcap + eta / 8) + 11 * (eta / 2))
      ((c - eta / 2) - 7 * (eta / 2)) z lo hi eps
      (Rmax - 3 * (2 * d / 3) / 2) Cih t :=
    uniformBound_restrict (provider_child_capacity heta) (provider_child_margin heta)
      (by rw [provider_row_drop]) hih
  let cutoff := FirstLocalizedCutoff.sourceCutoff K S D T Z tau hz0
  let centers := FirstCanonicalCenters.centers_of_power K S D T Z (A + 4) h r
    hz1 hh.2 hwidth hscale hr.2
  have hsmall := ProviderUniformChildren.all_smaller_pieces_of_uniform_sharp
    K S D Γ T Θ ψ G hν hG hbase hmask (A + 4) Z x.rowLength r ell x.labelLength h tau hz1
    cutoff labels centers hprime hweights slotCap hslots
    Λ (x.punctureLength Z) z (c - eta / 2) (2 * d / 3) (eta / 2)
    (Fcap + eta / 8) lo hi Rmax eps Cih x.markLengths t
    (by linarith) hr hell hx.label_nonneg hh hwidth (by linarith) hpars.2.2.2
    hpars.1 hpars.2.1 hM hbase_eq hscale hcube hparent
    (by linarith [hx.label_nonneg]) hRho hRhoNorm hx.lambda_eq hx.calibration hbg hx.marks hF hih'
  have hp := (hstep T rfl hmask Θ ψ G hν hG hbase hx.calibration labels w
    (annularTest s i) (annularTest_support s i)
    Z x.rowLength r ell x.labelLength h tau (x.punctureLength Z) z (c - eta / 2)
    (2 * d / 3) (eta / 2) eps Cih 1 hZ hMr hr hell hVr hh
    ⟨htau.1, by linarith [htau.2]⟩ htau' hwidth hpars.2.2.1 hpars.2.2.2
    (by linarith [hx.label_nonneg]) hbase_eq hradius hscale rfl rfl hcube hlabels
    hparent hc hz hRho hRhoNorm heps hCih zero_le_one hw0 hw hbeta hbetaSmall
    hbg hprime hweights hslots hsmall).1
  have hcov : 0 ≤ (InverseRowMajorant.rowCovolume K S)⁻¹ :=
    inv_nonneg.mpr (InverseRowMajorant.rowCovolume_pos K S).le
  have htransfer := CubeCompletionProvider.annularEnergy_le_parent K S D Γ hΓ C0 P B H
    (x.family.base ^ x.columnLength) (x.family.base ^ x.columnLength / H ^ 3) r s i
    (Real.rpow_pos_of_pos hb0 _) hH rfl hb0
    (by simpa only [C0, ProviderChildParent.columns, hx.base_eq] using hannular)
    Hrow labels w hw0 x.rows hx.row_bound
  change annularEnergy K S D Γ slotCap x P B H s i ≤
    (InverseRowMajorant.rowCovolume K S)⁻¹ *
      ∑ f ∈ labels, w f * ‖FirstCappedProduction.parent K S D Γ T f‖ at htransfer
  have hp' := mul_le_mul_of_nonneg_left hp
    (mul_nonneg hcov (Real.rpow_nonneg hz0.le (r + 2 * ell + x.labelLength)))
  have hcancel : Z ^ (r + 2 * ell + x.labelLength) * Z ^ (-r - 2 * ell - x.labelLength) = 1 := by
    rw [← Real.rpow_add hz0]
    convert Real.rpow_zero Z using 1 <;> ring
  have hpower : Z ^ (r + 2 * ell + x.labelLength) *
      Z ^ (r + 3 * ell + x.labelLength + 40 * (eta / 2) + tau + pi + eps) =
      Z ^ (2 * r + 5 * ell + 2 * x.labelLength + 20 * eta + tau + pi + eps) := by
    rw [← Real.rpow_add hz0]
    congr 1
    ring
  have hraw : (InverseRowMajorant.rowCovolume K S)⁻¹ *
      ∑ f ∈ labels, w f * ‖FirstCappedProduction.parent K S D Γ T f‖ ≤
      Ccube * Cih * (qW.sup (schwartzSeminormFamily ℝ ℝ ℂ) (annularTest s i)) ^ 2 *
        Z ^ (2 * r + 5 * ell + 2 * x.labelLength + 20 * eta + tau + pi + eps) := by
    calc
      _ = ((InverseRowMajorant.rowCovolume K S)⁻¹ * Z ^ (r + 2 * ell + x.labelLength)) *
          (Z ^ (-r - 2 * ell - x.labelLength) *
            ∑ f ∈ labels, w f * ‖FirstCappedProduction.parent K S D Γ T f‖) := by
        rw [mul_assoc, ← mul_assoc (Z ^ _), hcancel, one_mul]
      _ ≤ _ := hp'
      _ = _ := by
        dsimp only [Ccube]
        change _ = _
        rw [show T.archTest = rowBallArchTest K S 1 from rfl]
        calc
          _ = (3 * (InverseRowMajorant.rowCovolume K S)⁻¹ * C *
              qArch.sup (schwartzSeminormFamily ℝ Varch ℂ) (rowBallArchTest K S 1)) *
            Cih * (qW.sup (schwartzSeminormFamily ℝ ℝ ℂ) (annularTest s i)) ^ 2 *
              (Z ^ (r + 2 * ell + x.labelLength) *
                Z ^ (r + 3 * ell + x.labelLength + 40 * (eta / 2) + tau + pi + eps)) := by ring
          _ = _ := by rw [hpower]
  apply htransfer.trans (hraw.trans ?_)
  change _ ≤ max 1 Ccube * Cih *
    (qW.sup (schwartzSeminormFamily ℝ ℝ ℂ) (annularTest s i)) ^ 2 * _
  gcongr
  exact le_max_right (1 : ℝ) Ccube

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionNodeStep
