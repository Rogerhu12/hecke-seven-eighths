import HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedCutoff
import HeckeSkeleton.Moments.MOM_INV_STEP.UniformNormalizedFirstTail

/-!
# Uniform tails for the actual localized first cutoff

The cutoff is the literal radius supplied by the first extraction.
Its large-argument condition follows from the original dyadic source.
Original coefficients, masks, cube pairs and labels are all counted
using their proved source-mass bound.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedTail

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton MeasureTheory
open HeckeSkeleton.Moments.MOMInvStep DedekindZetaZeroFree.LargeSieve
open CanonicalBlock CanonicalPoissonSplit TailCoefficientMass FirstMaskGeometry
  JointMaskGeometry PrimitivePoissonSource ConductorMasks ActualPoissonScale CanonicalNormPools
open CanonicalTailBound (coefficientMaskMass)
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [Γ.FiniteIndex]
  [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "Pair" => (Ext × Ext) × (Ext × Ext)
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

def sourceSubsetTail {σ : Type*} (C : ColumnData K S σ) (f : Ext)
    (P : Finset Pair) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r X : {r : ℝ // 0 < r}) (Z tau : ℝ) : ℂ :=
  ∑ p ∈ P, pairWeight K S D C f p *
    CanonicalAdaptiveTail.dualTail K S D Γ μv
      (primitivePairBlock K S D Γ hΓ p.1 p.2 φ h hlc hcs M r)
      (FirstLocalizedCutoff.fineCutoff K S D r X Z tau p.1.2 p.2.2 p.1.1 p.2.1)

theorem sourceSubsetTail_full {σ : Type*} (C : ColumnData K S σ) (f : Ext)
    (B N : Finset Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r X : {r : ℝ // 0 < r}) (Z tau : ℝ) :
    sourceSubsetTail K S D Γ hΓ μv C f ((B ×ˢ N) ×ˢ (B ×ˢ N))
      φ h hlc hcs M r X Z tau =
    FirstAdaptiveTruncation.canonicalTail K S D Γ hΓ μv C f B N φ h hlc hcs M r
      (FirstLocalizedCutoff.fineCutoff K S D r X Z tau) := rfl

include ν in
theorem exists_sourceSubsetTail_bound_uniform
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (Rmax tauMin savingMax : ℝ) (hRmax : 0 ≤ Rmax)
    (htauMin : 0 < tauMin) (hsavingMax : 0 ≤ savingMax) :
    ∃ s : Finset (ℕ × ℕ), ∃ A : ℝ, 0 ≤ A ∧
      ∀ {σ : Type*} (C : ColumnData K S σ) (f : Ext)
        (P : Finset Pair) (φ : SchwartzMap V ℂ)
        (M : Finset (HeightOneSpectrum OS)) (r X : {r : ℝ // 0 < r})
        (Z tau saving : ℝ),
      1 ≤ Z → tauMin ≤ tau → 0 ≤ saving → saving ≤ savingMax →
      (∀ p ∈ P, p.1.2 ∈ dyadicPool K Sset X.val ∧ p.2.2 ∈ dyadicPool K Sset X.val) →
      (∀ p ∈ P, ∀ δ ⊆ (primitivePairBlock K S D Γ hΓ p.1 p.2 φ h hlc hcs M r).mask,
        r.val * (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val *
          ((primitiveIdeal (pairSupport K S D p.1.2 p.2.2 p.1.1 p.2.1).support
            (pairExponent K S p.1.2 p.2.2 p.1.1 p.2.1)).absNorm : ℝ) ≤ Z ^ Rmax) →
      ‖sourceSubsetTail K S D Γ hΓ μv C f P φ h hlc hcs M r X Z tau‖ ≤
        coefficientMaskMass K S D C f P M *
          (A * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
            (fieldConstant K / r.val) * Z ^ (-saving)) := by
  obtain ⟨s, A, hA, hb⟩ := CanonicalAdaptiveTail.exists_primitive_tail_bound_uniform
    K S D Γ hΓ μv ν h hlc hcs Rmax tauMin savingMax hRmax htauMin hsavingMax
  refine ⟨s, A, hA, ?_⟩
  intro σ C f P φ M r X Z tau saving hZ htau hsaving hss hannuli hbudget
  let U := A * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
    (fieldConstant K / r.val) * Z ^ (-saving)
  have hU : 0 ≤ U := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hA (apply_nonneg _ _))
        (div_nonneg (fieldConstant_nonneg K) r.property.le))
      (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  have hp (p : Pair) (hp : p ∈ P) :
      ‖CanonicalAdaptiveTail.dualTail K S D Γ μv
        (primitivePairBlock K S D Γ hΓ p.1 p.2 φ h hlc hcs M r)
        (FirstLocalizedCutoff.fineCutoff K S D r X Z tau p.1.2 p.2.2 p.1.1 p.2.1)‖ ≤
      (2 : ℝ) ^ (M ∪ principalMask K S
        (pairSupport K S D p.1.2 p.2.2 p.1.1 p.2.1)
        (pairExponent K S p.1.2 p.2.2 p.1.1 p.2.1)).card * U := by
    apply CanonicalAdaptiveTail.dualTail_norm_le K S D Γ μv _ _ U hU
    intro δ hδ
    apply hb _ _ φ M r δ Z tau saving
      (FirstLocalizedCutoff.fineCutoff K S D r X Z tau p.1.2 p.2.2 p.1.1 p.2.1 δ)
      hZ htau hsaving hss
    · exact primitive_dual_radius_lower K S D _ _ r (sIntegerMaskGenerator K Sset δ)
        Z Rmax (zero_lt_one.trans_le hZ) (hbudget p hp δ (Finset.mem_powerset.mp hδ))
    · exact FirstLocalizedCutoff.fineCutoff_argument K S D r X Z tau
        (zero_lt_one.trans_le hZ) p.1.2 p.2.2 p.1.2 p.2.2 p.1.1 p.2.1
        (hannuli p hp).1 (hannuli p hp).2 ⟨rfl, rfl, rfl⟩ δ
  unfold sourceSubsetTail
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ P, ‖pairWeight K S D C f p‖ *
        ((2 : ℝ) ^ (M ∪ principalMask K S
          (pairSupport K S D p.1.2 p.2.2 p.1.1 p.2.1)
          (pairExponent K S p.1.2 p.2.2 p.1.1 p.2.1)).card * U) := by
      apply Finset.sum_le_sum
      intro p hp'
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hp p hp') (norm_nonneg _)
    _ = coefficientMaskMass K S D C f P M * U := by
      unfold coefficientMaskMass
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      ring

include ν in
theorem exists_weighted_source_tail_bound_uniform
    (slotCap p : ℕ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (Rmax tauMin savingMax : ℝ) (hRmax : 0 ≤ Rmax)
    (htauMin : 0 < tauMin) (hsavingMax : 0 ≤ savingMax) :
    ∃ s : Finset (ℕ × ℕ), ∃ A : ℝ, 0 ≤ A ∧
      ∀ {σ : Type*} (C : ColumnData K S σ)
      (G : HeckeCharacter K) (hcal : ThetaCalibrationInput K Sset D C.lambda G)
      (B N L : Finset Ext) (P : Ext → Finset Pair) (Q : Ext) (w : Ext → ℝ)
      (X H Y β W Aweight : ℝ) (φ : SchwartzMap V ℂ)
      (ρ Xsrc : {r : ℝ // 0 < r}) (Z tau saving : ℝ),
      1 ≤ Z → tauMin ≤ tau →
      0 ≤ saving → saving ≤ savingMax →
      1 ≤ X → 1 ≤ H → 1 ≤ Y → 0 ≤ β → 0 ≤ W → 0 ≤ Aweight →
      C.slots.card ≤ slotCap →
      (∀ i ∈ C.slots, ∀ J ∈ C.primeLists i, ‖C.primeWeights i J‖ ≤ 1) →
      (∀ n ∈ N, Squarefree n.val.val) →
      (∀ n ∈ N, (n.val.val.absNorm : ℝ) ≤ X) →
      (∀ n ∈ N, n ∈ dyadicPool K Sset Xsrc.val) →
      (∀ b ∈ B, (b.val.val.absNorm : ℝ) ≤ H) →
      (∀ f ∈ L, (f.val.val.absNorm : ℝ) ≤ Y) →
      (∀ f ∈ L, P f ⊆ (B ×ˢ N) ×ˢ (B ×ˢ N)) →
      (∀ b ∈ B, ∀ f ∈ L, ‖C.labelWeight b f‖ ≤ β) →
      (∀ n ∈ N, ‖C.cutoff ((n.val.val.absNorm : ℝ) / C.base ^ C.length)‖ ≤ W) →
      (∀ f ∈ L, 0 ≤ w f) →
      (∀ f ∈ L, w f ≤ Aweight * ((idealDivisors f.val.val).card : ℝ) ^ p) →
      ρ.val * (Q.val.val.absNorm : ℝ) * H ^ 2 * X ^ 2 ≤ Z ^ Rmax →
      (∑ f ∈ L, w f *
        ‖sourceSubsetTail K S D Γ hΓ μv C f (P f) φ h hlc hcs
          (externalMask K S Q) ρ Xsrc Z tau‖) ≤
        A * Aweight * (β * W) ^ 2 * (Q.val.val.absNorm : ℝ) * H ^ 10 * X ^ 6 * Y ^ 2 *
          s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
          (fieldConstant K / ρ.val) * Z ^ (-saving) := by
  obtain ⟨s, At, hAt, ht⟩ := exists_sourceSubsetTail_bound_uniform
    K S D Γ hΓ μv ν h hlc hcs Rmax tauMin savingMax hRmax htauMin hsavingMax
  obtain ⟨Am, hAm, hm⟩ := exists_weighted_source_mass_bound K S D slotCap p
  refine ⟨s, Am * At, mul_nonneg (zero_le_one.trans hAm) hAt, ?_⟩
  intro σ C G hcal B N L P Q w X H Y β W Aweight φ ρ Xsrc Z tau saving
    hZ htau hsaving hss hX hH hY hβ hW hAweight hcap ha hsf hn hannuli hb hf
    hP hlabel hcut hw0 hw hbudget
  let U := At * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
    (fieldConstant K / ρ.val) * Z ^ (-saving)
  have hU : 0 ≤ U := by
    dsimp only [U]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hAt (apply_nonneg _ _))
        (div_nonneg (fieldConstant_nonneg K) ρ.property.le))
      (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  have hp (f : Ext) (hfl : f ∈ L) :
      ‖sourceSubsetTail K S D Γ hΓ μv C f (P f) φ h hlc hcs
        (externalMask K S Q) ρ Xsrc Z tau‖ ≤
          coefficientMaskMass K S D C f (P f) (externalMask K S Q) * U := by
    apply ht C f (P f) φ (externalMask K S Q) ρ Xsrc Z tau saving
      hZ htau hsaving hss
    · intro x hx
      obtain ⟨hleft, hright⟩ := Finset.mem_product.mp (hP f hfl hx)
      exact ⟨hannuli x.1.2 (Finset.mem_product.mp hleft).2,
        hannuli x.2.2 (Finset.mem_product.mp hright).2⟩
    intro x hx δ hδ
    obtain ⟨hleft, hright⟩ := Finset.mem_product.mp (hP f hfl hx)
    obtain ⟨hb₁, hn₁⟩ := Finset.mem_product.mp hleft
    obtain ⟨hb₂, hn₂⟩ := Finset.mem_product.mp hright
    have hd := actual_norm_product_bound K S D Q x.1.2 x.2.2 x.1.1 x.2.1 δ hδ
    have hwindow :
        (Q.val.val.absNorm : ℝ) * (x.1.1.val.val.absNorm : ℝ) *
          (x.2.1.val.val.absNorm : ℝ) * (x.1.2.val.val.absNorm : ℝ) *
          (x.2.2.val.val.absNorm : ℝ) ≤
        (Q.val.val.absNorm : ℝ) * H ^ 2 * X ^ 2 := by
      calc
        _ ≤ (Q.val.val.absNorm : ℝ) * H * H * X * X := by
          gcongr
          · exact hb _ hb₁
          · exact hb _ hb₂
          · exact hn _ hn₁
          · exact hn _ hn₂
        _ = _ := by ring
    calc
      _ = ρ.val *
        ((sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val *
          ((primitiveIdeal (pairSupport K S D x.1.2 x.2.2 x.1.1 x.2.1).support
            (pairExponent K S x.1.2 x.2.2 x.1.1 x.2.1)).absNorm : ℝ)) := by ring
      _ ≤ ρ.val * ((Q.val.val.absNorm : ℝ) * H ^ 2 * X ^ 2) :=
        mul_le_mul_of_nonneg_left (hd.trans hwindow) ρ.property.le
      _ ≤ Z ^ Rmax := by simpa only [mul_assoc] using hbudget
  have hmass := hm C G hcal B N L P Q w X H Y β W Aweight
    hX hH hY hβ hW hAweight hcap ha hsf hn hb hf hP hlabel hcut hw0 hw
  calc
    _ ≤ ∑ f ∈ L, w f *
        (coefficientMaskMass K S D C f (P f) (externalMask K S Q) * U) :=
      Finset.sum_le_sum (fun f hfl => mul_le_mul_of_nonneg_left (hp f hfl) (hw0 f hfl))
    _ = (∑ f ∈ L, w f * coefficientMaskMass K S D C f (P f) (externalMask K S Q)) * U := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro f _
      ring
    _ ≤ (Am * Aweight * (β * W) ^ 2 * (Q.val.val.absNorm : ℝ) *
        H ^ 10 * X ^ 6 * Y ^ 2) * U :=
      mul_le_mul_of_nonneg_right hmass hU
    _ = _ := by dsimp only [U]; ring


include ν in
/-- Every principal or nonprincipal source restriction has arbitrary
normalized power saving. Both dual-radius conditions are proved from
the original dyadic source and bounded physical length windows. -/
theorem exists_normalized_source_tail_bound_uniform
    (slotCap p : ℕ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (lengthCap tauMin desiredSaving : ℝ)
    (hcap0 : 0 ≤ lengthCap)
    (htauMin : 0 < tauMin) (hdesired : 0 ≤ desiredSaving) :
    ∃ s : Finset (ℕ × ℕ), ∃ A : ℝ, 0 ≤ A ∧
      ∀ {σ : Type*} (C : ColumnData K S σ)
      (G : HeckeCharacter K) (hcal : ThetaCalibrationInput K Sset D C.lambda G)
      (B N L : Finset Ext) (P : Ext → Finset Pair) (Q : Ext) (w : Ext → ℝ)
      (φ : SchwartzMap V ℂ) (Z M r ell Vlabel eta E betaLoss tau W Aweight : ℝ),
      ∀ hZ : 1 ≤ Z,
      0 ≤ M → M ≤ lengthCap →
      0 ≤ r → r ≤ lengthCap →
      0 ≤ ell → ell ≤ lengthCap →
      0 ≤ Vlabel → Vlabel ≤ lengthCap →
      0 ≤ eta → eta ≤ lengthCap →
      E ≤ lengthCap → betaLoss ≤ lengthCap →
      2 ≤ Z ^ eta → tauMin ≤ tau →
      0 ≤ W → 0 ≤ Aweight →
      C.slots.card ≤ slotCap →
      (∀ i ∈ C.slots, ∀ J ∈ C.primeLists i, ‖C.primeWeights i J‖ ≤ 1) →
      (∀ n ∈ N, n ∈ dyadicPool K Sset (Z ^ r)) →
      (∀ b ∈ B, (b.val.val.absNorm : ℝ) ≤ Z ^ (ell + eta)) →
      (∀ f ∈ L, (f.val.val.absNorm : ℝ) ≤ Z ^ (Vlabel + eta)) →
      (Q.val.val.absNorm : ℝ) ≤ Z ^ E →
      (∀ f ∈ L, P f ⊆ (B ×ˢ N) ×ˢ (B ×ˢ N)) →
      (∀ b ∈ B, ∀ f ∈ L, ‖C.labelWeight b f‖ ≤ Z ^ betaLoss) →
      (∀ n ∈ N, ‖C.cutoff ((n.val.val.absNorm : ℝ) / C.base ^ C.length)‖ ≤ W) →
      (∀ f ∈ L, 0 ≤ w f) →
      (∀ f ∈ L, w f ≤ Aweight * ((idealDivisors f.val.val).card : ℝ) ^ p) →
      Z ^ (-r - 2 * ell - Vlabel) *
        (∑ f ∈ L, w f *
          ‖sourceSubsetTail K S D Γ hΓ μv C f (P f) φ h hlc hcs
            (externalMask K S Q)
            ⟨Z ^ (-M), Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _⟩
            ⟨Z ^ r, Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _⟩ Z tau‖) ≤
        A * Aweight * W ^ 2 * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
          Z ^ (-desiredSaving) := by
  let Rmax := 9 * lengthCap
  have hRmax : 0 ≤ Rmax := by dsimp only [Rmax]; positivity
  let saving := desiredSaving + 36 * lengthCap
  have hsaving : 0 ≤ saving := by dsimp only [saving]; positivity
  obtain ⟨s, A, hA, hb⟩ := exists_weighted_source_tail_bound_uniform
    K S D Γ hΓ μv ν slotCap p h hlc hcs Rmax tauMin saving hRmax htauMin hsaving
  refine ⟨s, A * fieldConstant K, mul_nonneg hA (fieldConstant_nonneg K), ?_⟩
  intro σ C G hcal B N L P Q w φ Z M r ell Vlabel eta E betaLoss tau W Aweight hZ
    hM hMc hr hrc hell hellc hV hVc heta hetac hEc hβc hwidth htau
    hW hAweight hslots ha hannuli hbn hfn hQ hP hlabel hcut hw0 hw
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  let ρ : {r : ℝ // 0 < r} := ⟨Z ^ (-M), Real.rpow_pos_of_pos hz _⟩
  let Xsrc : {r : ℝ // 0 < r} := ⟨Z ^ r, Real.rpow_pos_of_pos hz _⟩
  have hsf (n : Ext) (hn : n ∈ N) : Squarefree n.val.val :=
    dyadicPool_squarefree K Sset (hannuli n hn)
  have hn (n : Ext) (hn : n ∈ N) : (n.val.val.absNorm : ℝ) ≤ Z ^ (r + eta) := by
    have hnn := ((mem_dyadicPool K Sset (Z ^ r) n).mp (hannuli n hn)).2.2
    apply hnn.trans
    calc
      2 * Z ^ r ≤ Z ^ eta * Z ^ r :=
        mul_le_mul_of_nonneg_right hwidth (Real.rpow_nonneg hz.le _)
      _ = Z ^ (r + eta) := by rw [Real.rpow_add hz]; ring
  have hbudget : ρ.val * (Q.val.val.absNorm : ℝ) *
      (Z ^ (ell + eta)) ^ 2 * (Z ^ (r + eta)) ^ 2 ≤ Z ^ Rmax := by
    calc
      _ ≤ Z ^ (-M) * Z ^ E * (Z ^ (ell + eta)) ^ 2 * (Z ^ (r + eta)) ^ 2 := by
        dsimp only [ρ]
        gcongr
      _ = Z ^ (-M + E + 2 * ell + 2 * r + 4 * eta) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le,
          ← Real.rpow_natCast, ← Real.rpow_mul hz.le]
        repeat rw [← Real.rpow_add hz]
        congr 1
        norm_num
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ (by dsimp only [Rmax]; linarith)
  have hraw := hb C G hcal B N L P Q w (Z ^ (r + eta)) (Z ^ (ell + eta))
    (Z ^ (Vlabel + eta)) (Z ^ betaLoss) W Aweight φ ρ Xsrc Z tau saving
    hZ htau hsaving le_rfl
    (Real.one_le_rpow hZ (add_nonneg hr heta))
    (Real.one_le_rpow hZ (add_nonneg hell heta))
    (Real.one_le_rpow hZ (add_nonneg hV heta))
    (Real.rpow_nonneg hz.le _) hW hAweight hslots ha hsf hn hannuli hbn hfn hP hlabel hcut hw0 hw hbudget
  have hpref : fieldConstant K / ρ.val = fieldConstant K * Z ^ M := by
    dsimp only [ρ]
    rw [div_eq_mul_inv, Real.rpow_neg hz.le, inv_inv]
  rw [hpref] at hraw
  have hpow :
      Z ^ (-r - 2 * ell - Vlabel) * (Z ^ betaLoss) ^ 2 * Z ^ E *
        (Z ^ (ell + eta)) ^ 10 * (Z ^ (r + eta)) ^ 6 *
        (Z ^ (Vlabel + eta)) ^ 2 * Z ^ M * Z ^ (-saving) ≤
          Z ^ (-desiredSaving) := by
    rw [UniformNormalizedFirstTail.normalized_tail_power_identity Z hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    dsimp only [saving]
    linarith
  have hconst : 0 ≤ (A * fieldConstant K) * Aweight * W ^ 2 *
      s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hA (fieldConstant_nonneg K)) hAweight) (sq_nonneg _))
      (apply_nonneg _ _)
  apply (mul_le_mul_of_nonneg_left hraw (Real.rpow_nonneg hz.le _)).trans
  calc
    _ ≤ Z ^ (-r - 2 * ell - Vlabel) *
        (A * Aweight * (Z ^ betaLoss * W) ^ 2 * Z ^ E *
          (Z ^ (ell + eta)) ^ 10 * (Z ^ (r + eta)) ^ 6 *
          (Z ^ (Vlabel + eta)) ^ 2 *
          s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
          (fieldConstant K * Z ^ M) * Z ^ (-saving)) := by
      gcongr
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_left hpow hconst using 1 <;> ring

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedTail

end
