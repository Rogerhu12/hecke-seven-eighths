import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialEstimate
import HeckeSkeleton.Moments.MOM_INV_STEP.UniformSecondPrincipal
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondAdaptiveTail

/-!
# The original inverse orbital source from the actual canonical bound

The original normalized source is identified by genuine Poisson with
the retained source, additive zeros and the actual adaptive tail. The
retained source is bounded using both actual positive production totals.
The existing uniform principal and adaptive-tail theorems discharge the
other terms with constants selected before the source. The only moment
input is the full canonical `UniformBound` supplied by finite induction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

universe u

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialClosure

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckeSkeleton.Moments.MOMInvStep HeckeSkeleton.Moments.MOM_INV_STEP
open CanonicalNormPools CanonicalChildren FixedTripleEnergy
open ProviderNodes ProviderInitialEstimate
open scoped Classical BigOperators nonZeroDivisors

theorem normalized_sqrt_product_le {s a b E : ℝ}
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hea : s * a ≤ E) (heb : s * b ≤ E) :
    s * (Real.sqrt a * Real.sqrt b) ≤ E := by
  have ham : 2 * (Real.sqrt a * Real.sqrt b) ≤ a + b := by
    nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha, Real.sq_sqrt hb]
  have hm := mul_le_mul_of_nonneg_left ham hs
  nlinarith

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
local instance unitClassesFintype :
    Fintype (CanonicalSectors.UnitClasses K (S : Set (HeightOneSpectrum (𝓞 K))) Γ) :=
  Fintype.ofFinite _
local notation "Varch" => mixedEmbedding.euclidean.mixedSpace K

include hΓ hallowed μv ν μ in
/-- The literal original inverse orbital energy is bounded using
actual canonical nodes. The fixed row-length cap and positive adaptive
truncation lower bound precede the profile, source and every source
length. Principal/additive-zero and tail estimates are proved inputs,
not assumptions of this statement. -/
theorem exists_uniform_orbital_bound
    (slotCap : ℕ) (A Mmax pi tauMin : ℝ)
    (hA : 0 ≤ A) (hMmax : 0 ≤ Mmax) (hpi : 0 < pi) (htauMin : 0 < tauMin)
    (qchild : Finset (ℕ × ℕ)) :
    ∃ q : Finset (ℕ × ℕ), ∃ B : ℝ, 1 ≤ B ∧
      ∀ {σ : Type u} [DecidableEq σ] (C : CanonicalBlock.ColumnData K S σ)
        (Θ : Subgroup (HeckeCharacter K)) (ψ : HeckeCharacter K)
        (hν : BackgroundCycle.Admissible K Θ ψ C.background)
        (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
        (Λ G : HeckeCharacter K) (hG : G ∈ Θ)
        (m Q z c h tau lo hi : ℝ) (markLengths : σ → ℝ)
        (hb : SourceConditions K S D C Λ G slotCap A m Q z c h tau lo hi markLengths)
        (eps Cih : ℝ),
      m ≤ Mmax → tauMin ≤ tau → 0 ≤ eps → 1 ≤ Cih →
      UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap C.base m
        (3 * c / 4) z lo hi eps m Cih qchild →
      ‖SourceReductionPoisson.orbitalEnergy K S D Γ C.background
        (ProviderInitialInverse.sourceMark K S C) W (C.base ^ C.length)
        (ProviderInitialProduction.rowCap K S C hb.base_gt_one m)‖ ≤
        B * Cih * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
          C.base ^ (m + 48 * h + 5 * pi + eps) := by
  obtain ⟨e, he, k, qTotal, BTotal, hBTotal, htotal⟩ :=
    ProviderInitialEstimate.exists_uniform_total_bound K S D Γ slotCap A pi hA hpi qchild
  obtain ⟨BRetained, hBRetained, hretained⟩ :=
    ProviderInitialInverse.exists_uniform_initial_retained_bound
      (K := K) (S := S) (D := D) (Γ := Γ) (hΓ := hΓ) (hallowed := hallowed)
      (μv := μv) (ν := ν) e he k
  obtain ⟨qPrincipal, BPrincipal, hBPrincipal, hprincipal⟩ :=
    UniformSecondPrincipal.exists_uniform_principal_bound K S D Γ hΓ μv
      slotCap Mmax A pi hMmax hA hpi
      (rowBallFiniteFamily K S 1) (rowBallFiniteFamily_locallyConstant K S 1)
      (rowBallFiniteFamily_compactSupport K S 1)
  obtain ⟨qTail, BTail, hBTail, htail⟩ :=
    SecondAdaptiveTail.exists_normalized_inverse_tail_bound K S D Γ hΓ μv ν
      slotCap (rowBallFiniteFamily K S 1) (rowBallFiniteFamily_locallyConstant K S 1)
      (rowBallFiniteFamily_compactSupport K S 1)
      (A + Mmax) tauMin 0 (add_nonneg hA hMmax) htauMin le_rfl
  let CP := BPrincipal * qPrincipal.sup (schwartzSeminormFamily ℝ Varch ℂ) (rowBallArchTest K S 1)
  let CT := BTail * qTail.sup (schwartzSeminormFamily ℝ Varch ℂ) (rowBallArchTest K S 1)
  let CR := BRetained * BTotal * (1 + (Fintype.card Sector : ℝ))
  let B := CR + CP + CT
  let q := insert (0, 0) qTotal
  have hCP : 0 ≤ CP := mul_nonneg hBPrincipal (apply_nonneg _ _)
  have hCT : 0 ≤ CT := mul_nonneg hBTail (apply_nonneg _ _)
  have hCR : 0 ≤ CR := by dsimp only [CR]; positivity
  refine ⟨q, max 1 B, le_max_left _ _, ?_⟩
  intro σ _ C Θ ψ hν W hW Λ G hG m Q z c h tau lo hi markLengths hb eps Cih
    hm htau heps hCih hih
  have hz0 := zero_lt_one.trans hb.base_gt_one
  have hz1 := hb.base_gt_one.le
  have hz2 : 2 ≤ C.base := by
    have hp := Real.rpow_le_rpow_of_exponent_le hz1 hb.mesh.2
    rw [Real.rpow_one] at hp
    exact hb.mesh_width.trans hp
  have hCih0 : 0 ≤ Cih := zero_le_one.trans hCih
  let X := C.base ^ C.length
  have hX : 0 < X := Real.rpow_pos_of_pos hz0 _
  have hXi : 0 ≤ X⁻¹ := inv_nonneg.mpr hX.le
  let Hrow := ProviderInitialProduction.rowCap K S C hb.base_gt_one m
  let T := ProviderInitialProduction.parent K S C Θ ψ hν W hb.base_gt_one hW m
  let H := SecondAdaptiveCutoff.fineCutoff K S T.radius X C.base tau
  let a := DivisorInverseColumn.coefficient K S D T.columns T.triple T.label.val.val T.divisor.val
  let P := T.columns.columns T.triple ×ˢ T.columns.columns T.triple
  let retained := SecondAdaptiveCutoff.retainedSourceAt K S D Γ hΓ μv a P
    T.archTest T.localTest T.locallyConstant T.compactSupport T.radius H
  let zeros := SecondPoissonSplit.additiveZeros K S D Γ hΓ μv a (T.columns.columns T.triple)
    T.archTest T.localTest T.locallyConstant T.compactSupport T.radius
  let tail := SecondAdaptiveCutoff.tailSourceAt K S D Γ hΓ μv a P
    T.archTest T.localTest T.locallyConstant T.compactSupport T.radius H
  let Rhs := Cih * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
    C.base ^ (m + 48 * h + 5 * pi + eps)
  have hRhs : 0 ≤ Rhs := by dsimp only [Rhs]; positivity
  have hqTotal : qTotal.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤
      q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_insert (0, 0) qTotal)) W
  have hqZero : SchwartzMap.seminorm ℝ 0 0 W ≤
      q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
    Seminorm.le_def.mp (Finset.le_sup (f := schwartzSeminormFamily ℝ ℝ ℂ)
      (Finset.mem_insert_self (0, 0) qTotal)) W
  have hqZeroSq : (SchwartzMap.seminorm ℝ 0 0 W) ^ 2 ≤
      (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 :=
    pow_le_pow_left₀ (apply_nonneg (SchwartzMap.seminorm ℝ 0 0) W) hqZero 2
  have hsector : Cih + (Fintype.card Sector : ℝ) ≤ (1 + (Fintype.card Sector : ℝ)) * Cih := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (Fintype.card Sector)) (sub_nonneg.mpr hCih)]
  have hprod : X⁻¹ *
      (Real.sqrt (SecondAdaptiveProduction.totalAt K S D Γ T H G hG e k false) *
        Real.sqrt (SecondAdaptiveProduction.totalAt K S D Γ T H G hG e k true)) ≤
      BTotal * (Cih + (Fintype.card Sector : ℝ)) *
        (qTotal.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
          C.base ^ (m + 48 * h + 5 * pi + eps) :=
    normalized_sqrt_product_le hXi
      (SecondAdaptiveProduction.totalAt_nonneg K S D Γ T H G hG e k false)
      (SecondAdaptiveProduction.totalAt_nonneg K S D Γ T H G hG e k true)
      (htotal C Θ ψ hν W hW Λ G hG m Q z c h tau lo hi markLengths hb eps Cih heps hCih0 hih false)
      (htotal C Θ ψ hν W hW Λ G hG m Q z c h tau lo hi markLengths hb eps Cih heps hCih0 hih true)
  have hRet : X⁻¹ * ‖retained‖ ≤ CR * Rhs := by
    have hr := hretained C Θ ψ hν W hb.base_gt_one hW Hrow H G hG
      hb.calibration hb.background_unramified hb.marks.prime
    change ‖retained‖ ≤ BRetained *
      (Real.sqrt (SecondAdaptiveProduction.totalAt K S D Γ T H G hG e k false) *
        Real.sqrt (SecondAdaptiveProduction.totalAt K S D Γ T H G hG e k true)) at hr
    have hs := mul_le_mul_of_nonneg_left hr hXi
    calc
      _ ≤ BRetained * (X⁻¹ *
          (Real.sqrt (SecondAdaptiveProduction.totalAt K S D Γ T H G hG e k false) *
            Real.sqrt (SecondAdaptiveProduction.totalAt K S D Γ T H G hG e k true))) := by
        exact hs.trans_eq (mul_left_comm _ _ _)
      _ ≤ BRetained * (BTotal * (Cih + (Fintype.card Sector : ℝ)) *
          (qTotal.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
            C.base ^ (m + 48 * h + 5 * pi + eps)) :=
        mul_le_mul_of_nonneg_left hprod hBRetained
      _ ≤ BRetained * (BTotal * ((1 + (Fintype.card Sector : ℝ)) * Cih) *
          (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
            C.base ^ (m + 48 * h + 5 * pi + eps)) := by gcongr
      _ = _ := by dsimp only [CR, Rhs]; ring
  have hcols : ∀ n ∈ T.columns.columns T.triple, height K Sset n ≤ 4 * C.base ^ C.length := by
    intro n hn
    have hp := ((mem_squarefreePool K Sset (2 * C.base ^ C.length) n).mp hn).2
    linarith
  have hradius : T.radius = ⟨C.base ^ (-m), Real.rpow_pos_of_pos hz0 _⟩ :=
    Subtype.ext (ProviderInitialProduction.parent_radius K S C Θ ψ hν W hb.base_gt_one hW m)
  have hprincipal' := hprincipal T.columns T.triple T.label.val.val T.divisor.val
    C.base m C.length T.archTest hz1 hb.row_nonneg hm hb.column_nonneg hb.column_le
    hb.marks.card_le hb.marks.weights_le hcols
  rw [← hradius] at hprincipal'
  have hzero : ‖zeros‖ ≤ BPrincipal * (SchwartzMap.seminorm ℝ 0 0 W) ^ 2 *
      qPrincipal.sup (schwartzSeminormFamily ℝ Varch ℂ) (rowBallArchTest K S 1) *
        C.base ^ (m + C.length + pi) := by
    apply le_trans _ hprincipal'
    exact le_add_of_nonneg_left (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg _))
  have hnormal : X⁻¹ * C.base ^ (m + C.length + pi) = C.base ^ (m + pi) := by
    dsimp only [X]
    rw [← Real.rpow_neg hz0.le, ← Real.rpow_add hz0]
    congr 1
    ring
  have hZero : X⁻¹ * ‖zeros‖ ≤ CP * Rhs := by
    calc
      _ ≤ X⁻¹ * (BPrincipal * (SchwartzMap.seminorm ℝ 0 0 W) ^ 2 *
          qPrincipal.sup (schwartzSeminormFamily ℝ Varch ℂ) (rowBallArchTest K S 1) *
            C.base ^ (m + C.length + pi)) := mul_le_mul_of_nonneg_left hzero hXi
      _ = CP * (SchwartzMap.seminorm ℝ 0 0 W) ^ 2 * C.base ^ (m + pi) := by
        dsimp only [CP]
        calc
          _ = (BPrincipal * qPrincipal.sup (schwartzSeminormFamily ℝ Varch ℂ)
              (rowBallArchTest K S 1)) * (SchwartzMap.seminorm ℝ 0 0 W) ^ 2 *
              (X⁻¹ * C.base ^ (m + C.length + pi)) := by ring
          _ = _ := by rw [hnormal]
      _ ≤ CP * Cih * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
          C.base ^ (m + 48 * h + 5 * pi + eps) := by
        have hcoef : CP * (SchwartzMap.seminorm ℝ 0 0 W) ^ 2 ≤
            CP * Cih * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 :=
          mul_le_mul (le_mul_of_one_le_right hCP hCih) hqZeroSq
            (sq_nonneg _) (mul_nonneg hCP hCih0)
        have hpow : C.base ^ (m + pi) ≤ C.base ^ (m + 48 * h + 5 * pi + eps) :=
          Real.rpow_le_rpow_of_exponent_le hz1 (by linarith [hb.mesh.1])
        exact mul_le_mul hcoef hpow (Real.rpow_nonneg hz0.le _)
          (mul_nonneg (mul_nonneg hCP hCih0) (sq_nonneg _))
      _ = _ := by dsimp only [Rhs]; ring
  have ht := htail T.columns T.triple T.label.val.val T.divisor.val P T.archTest
    C.base m C.length tau hz2 (by linarith [hb.row_nonneg]) (by linarith)
    hb.column_nonneg (by linarith [hb.column_le]) htau hb.marks.card_le hb.marks.weights_le
    hcols (Finset.Subset.refl _)
  dsimp only at ht
  rw [← hradius] at ht
  change C.base ^ (-C.length) * ‖tail‖ ≤
    BTail * (SchwartzMap.seminorm ℝ 0 0 W) ^ 2 *
      qTail.sup (schwartzSeminormFamily ℝ Varch ℂ) (rowBallArchTest K S 1) *
        C.base ^ (-(0 : ℝ)) at ht
  rw [Real.rpow_neg hz0.le, neg_zero, Real.rpow_zero, mul_one] at ht
  have htail' : X⁻¹ * ‖tail‖ ≤ CT * (SchwartzMap.seminorm ℝ 0 0 W) ^ 2 := by
    calc
      _ ≤ BTail * (SchwartzMap.seminorm ℝ 0 0 W) ^ 2 *
          qTail.sup (schwartzSeminormFamily ℝ Varch ℂ) (rowBallArchTest K S 1) := ht
      _ = _ := by
        dsimp only [CT]
        exact mul_right_comm _ _ _
  have hTail : X⁻¹ * ‖tail‖ ≤ CT * Rhs := by
    calc
      _ ≤ CT * (SchwartzMap.seminorm ℝ 0 0 W) ^ 2 := htail'
      _ ≤ CT * Cih * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
          C.base ^ (m + 48 * h + 5 * pi + eps) := by
        calc
          _ = CT * (SchwartzMap.seminorm ℝ 0 0 W) ^ 2 * 1 := (mul_one _).symm
          _ ≤ _ := by
            have hcoef : CT * (SchwartzMap.seminorm ℝ 0 0 W) ^ 2 ≤
                CT * Cih * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 :=
              mul_le_mul (le_mul_of_one_le_right hCT hCih) hqZeroSq
                (sq_nonneg _) (mul_nonneg hCT hCih0)
            have hpow : 1 ≤ C.base ^ (m + 48 * h + 5 * pi + eps) :=
              Real.one_le_rpow hz1 (by linarith [hb.row_nonneg, hb.mesh.1])
            exact mul_le_mul hcoef hpow zero_le_one
              (mul_nonneg (mul_nonneg hCT hCih0) (sq_nonneg _))
      _ = _ := by dsimp only [Rhs]; ring
  have hidentity := ProviderInitialInverse.initial_poisson_split
    (K := K) (S := S) (D := D) (C := C) (Θ := Θ) (ψ := ψ) (hν := hν) (W := W)
    (hallowed := hallowed) (Γ := Γ) (hΓ := hΓ) (μv := μv) (ν := ν) (μ := μ)
    hb.base_gt_one hW Hrow H
  change SourceReductionPoisson.orbitalEnergy K S D Γ C.background
    (ProviderInitialInverse.sourceMark K S C) W X Hrow =
      ((X⁻¹ : ℝ) : ℂ) * (retained + zeros + tail) at hidentity
  rw [hidentity, norm_mul, Complex.norm_real, Real.norm_of_nonneg hXi]
  calc
    _ ≤ X⁻¹ * (‖retained‖ + ‖zeros‖ + ‖tail‖) :=
      mul_le_mul_of_nonneg_left
        ((norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)) hXi
    _ = X⁻¹ * ‖retained‖ + X⁻¹ * ‖zeros‖ + X⁻¹ * ‖tail‖ := by ring
    _ ≤ CR * Rhs + CP * Rhs + CT * Rhs := add_le_add (add_le_add hRet hZero) hTail
    _ = B * Rhs := by dsimp only [B]; ring
    _ ≤ max 1 B * Rhs := mul_le_mul_of_nonneg_right (le_max_right _ _) hRhs
    _ = _ := by dsimp only [Rhs]; ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialClosure
