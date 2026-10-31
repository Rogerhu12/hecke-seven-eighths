import HeckeSkeleton.Moments.MOM_INV_STEP.UniformFirstPrincipal
import HeckeSkeleton.Moments.MOM_INV_STEP.UniformNormalizedFirstTail

/-!
# Uniform reduction of the original parent to its actual retained source

This starts from the independently defined canonical orbital energy.
Genuine Poisson proves its identity with the retained source and errors.
The errors are bounded from the original coefficients and norm windows;
no source identity or parent-energy inequality is an input.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentReduction

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton
  HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open HeckeSkeleton.Moments.MOMInvStep DedekindZetaZeroFree.LargeSieve
open FixedTripleFibers CanonicalBlock CanonicalPoissonSplit FirstDualTruncation
  FirstMaskGeometry CanonicalTailBound
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
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "Varch" => mixedEmbedding.euclidean.mixedSpace K

include ν μ in
theorem parent_norm_le_retained_and_errors {σ : Type*}
    (C : ColumnData K S σ) (f : Ext) (B N : Finset Ext)
    (hN : ∀ n ∈ N, Squarefree n.val.val) (φ : SchwartzMap Varch ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (mask : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}) (H : ℝ) :
    ‖canonicalCubeEnergy K S D Γ C f B N φ h mask R‖ ≤
      ‖canonicalRetained K S D Γ hΓ μv C f B N φ h hlc hcs mask R H‖ +
      (2 * ‖canonicalPrincipalSource K S D Γ hΓ C f B N φ h hlc hcs mask R‖ +
        ‖canonicalPrincipal K S D Γ hΓ μv C f B N φ h hlc hcs mask R‖) +
      ‖sourceSubsetTail K S D Γ hΓ μv C f ((B ×ˢ N) ×ˢ (B ×ˢ N))
        φ h hlc hcs mask R H‖ := by
  rw [canonicalCubeEnergy_eq_dual_add_principal K S D Γ hΓ μv ν μ
    C f B N hN φ h hlc hcs mask R,
    canonicalDual_eq_retained_add_tail K S D Γ hΓ μv ν C f B N φ h hlc hcs mask R H]
  have hn := (norm_add_le
    (canonicalRetained K S D Γ hΓ μv C f B N φ h hlc hcs mask R H +
      canonicalTail K S D Γ hΓ μv C f B N φ h hlc hcs mask R H)
    (canonicalPrincipal K S D Γ hΓ μv C f B N φ h hlc hcs mask R)).trans
      (add_le_add_right (norm_add_le _ _) _)
  change ‖_‖ ≤ _ + (_ + _) +
    ‖canonicalTail K S D Γ hΓ μv C f B N φ h hlc hcs mask R H‖
  linarith [norm_nonneg (canonicalPrincipalSource K S D Γ hΓ C f B N φ h hlc hcs mask R)]

include ν μ in
/-- All constants precede the original source data and the physical
lengths. The right side contains the literal retained source, not an
assumed surrogate or a supplied reconstruction packet. -/
theorem exists_uniform_parent_reduction
    (slotCap p : ℕ) (Lmax Rmax tauMin loss saving : ℝ)
    (hL : 1 ≤ Lmax) (hRmax : 0 ≤ Rmax) (htauMin : 0 < tauMin)
    (hloss : 0 < loss) (hsaving : 0 ≤ saving)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    ∃ s : Finset (ℕ × ℕ), ∃ A : ℝ, 0 ≤ A ∧
      ∀ {σ : Type*} (C : ColumnData K S σ)
      (G : HeckeCharacter K) (hcal : ThetaCalibrationInput K Sset D C.lambda G)
      (B N L : Finset Ext) (Q : Ext) (w : Ext → ℝ)
      (φ : SchwartzMap Varch ℂ) (Z M r ell Vlabel eta E betaLoss R tau W Aweight : ℝ),
      ∀ hZ : 1 ≤ Z,
      0 ≤ M → M ≤ Lmax → 0 ≤ r → r ≤ Lmax →
      0 ≤ ell → ell ≤ Lmax → 0 ≤ Vlabel → Vlabel ≤ Lmax →
      0 ≤ eta → eta ≤ 1 → E ≤ Lmax → betaLoss ≤ eta →
      0 ≤ R → R ≤ Rmax → tauMin ≤ tau → 0 ≤ W → 0 ≤ Aweight →
      C.slots.card ≤ slotCap →
      (∀ i ∈ C.slots, ∀ J ∈ C.primeLists i, ‖C.primeWeights i J‖ ≤ 1) →
      (∀ n ∈ N, Squarefree n.val.val) →
      (∀ n ∈ N, (n.val.val.absNorm : ℝ) ≤ Z ^ (r + eta)) →
      (∀ b ∈ B, (b.val.val.absNorm : ℝ) ≤ Z ^ (ell + eta)) →
      (∀ f ∈ L, (f.val.val.absNorm : ℝ) ≤ Z ^ (Vlabel + eta)) →
      (Q.val.val.absNorm : ℝ) ≤ Z ^ E →
      (∀ b ∈ B, ∀ f ∈ L, ‖C.labelWeight b f‖ ≤ Z ^ betaLoss) →
      (∀ n ∈ N, ‖C.cutoff ((n.val.val.absNorm : ℝ) / C.base ^ C.length)‖ ≤ W) →
      (∀ f ∈ L, 0 ≤ w f) →
      (∀ f ∈ L, w f ≤ Aweight * ((idealDivisors f.val.val).card : ℝ) ^ p) →
      -M + E + 2 * ell + 2 * r + 4 * eta ≤ R →
      Z ^ (-r - 2 * ell - Vlabel) *
        (∑ f ∈ L, w f * ‖canonicalCubeEnergy K S D Γ C f B N φ h
          (externalMask K S Q)
          ⟨Z ^ (-M), Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _⟩‖) ≤
      Z ^ (-r - 2 * ell - Vlabel) *
        (∑ f ∈ L, w f * ‖canonicalRetained K S D Γ hΓ μv C f B N φ h hlc hcs
          (externalMask K S Q)
          ⟨Z ^ (-M), Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _⟩ (Z ^ (R + tau))‖) +
      A * Aweight * W ^ 2 * s.sup (schwartzSeminormFamily ℝ Varch ℂ) φ *
        (Z ^ (M + 5 * eta + loss) + Z ^ (-saving)) := by
  obtain ⟨s₁, Ap, hAp, hp⟩ :=
    UniformFirstPrincipal.exists_uniform_first_principal_bound
      K S D Γ hΓ μv slotCap p Lmax loss hL hloss h hlc hcs
  obtain ⟨s₂, At, hAt, ht⟩ :=
    UniformNormalizedFirstTail.exists_normalized_source_tail_bound_uniform
      K S D Γ hΓ μv ν slotCap p h hlc hcs Lmax Rmax tauMin saving
      (zero_le_one.trans hL) hRmax htauMin hsaving
  let s := s₁ ∪ s₂
  refine ⟨s, Ap + At, add_nonneg hAp hAt, ?_⟩
  intro σ C G hcal B N L Q w φ Z M r ell Vlabel eta E betaLoss R tau W Aweight hZ
    hM0 hM hr0 hr hell0 hell hV0 hV heta heta1 hE hbeta hR hRR htau hW hAw
    hcap ha hsf hn hb hf hQ hlabel hcut hw0 hw hradius
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  let rad : {r : ℝ // 0 < r} := ⟨Z ^ (-M), Real.rpow_pos_of_pos hZpos _⟩
  let mask := externalMask K S Q
  let retained : Ext → ℝ := fun f =>
    ‖canonicalRetained K S D Γ hΓ μv C f B N φ h hlc hcs mask rad (Z ^ (R + tau))‖
  let principal : Ext → ℝ := fun f =>
    2 * ‖canonicalPrincipalSource K S D Γ hΓ C f B N φ h hlc hcs mask rad‖ +
      ‖canonicalPrincipal K S D Γ hΓ μv C f B N φ h hlc hcs mask rad‖
  let tail : Ext → ℝ := fun f =>
    ‖sourceSubsetTail K S D Γ hΓ μv C f ((B ×ˢ N) ×ˢ (B ×ˢ N))
      φ h hlc hcs mask rad (Z ^ (R + tau))‖
  let P := primeSupport Q.val
  have hP : ∀ v ∈ P, v ∉ Sset := fun v hv =>
    Q.property v ((mem_primeSupport Q.val v).mp hv)
  have hp' := hp C G hcal B N L w Z M r ell Vlabel eta E betaLoss W Aweight
    P hP Q.val.val φ hZ hM0 hM hr0 hr hell0 hell hV0 hV hE heta heta1 hbeta
    hW hAw (nonZeroDivisors.coe_ne_zero Q.val) hQ
    (fun v hv => (mem_primeSupport Q.val v).mp hv)
    hcap ha hsf hn hb hf hlabel hcut hw0 hw
  have ht' := ht C G hcal B N L (fun _ => (B ×ˢ N) ×ˢ (B ×ˢ N)) Q w
    φ Z M r ell Vlabel eta E betaLoss R tau W Aweight hZ
    hM0 hM hr0 hr hell0 hell hV0 hV heta (heta1.trans hL) hE
    (hbeta.trans (heta1.trans hL)) hR hRR htau hW hAw hcap ha hsf hn hb hf hQ
    (fun _ _ => Finset.Subset.refl _) hlabel hcut hw0 hw hradius
  have hsup₁ : s₁.sup (schwartzSeminormFamily ℝ Varch ℂ) φ ≤
      s.sup (schwartzSeminormFamily ℝ Varch ℂ) φ := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro i hi
    exact Seminorm.le_finset_sup_apply (Finset.mem_union_left _ hi)
  have hsup₂ : s₂.sup (schwartzSeminormFamily ℝ Varch ℂ) φ ≤
      s.sup (schwartzSeminormFamily ℝ Varch ℂ) φ := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro i hi
    exact Seminorm.le_finset_sup_apply (Finset.mem_union_right _ hi)
  have hp'' : Z ^ (-r - 2 * ell - Vlabel) * (∑ f ∈ L, w f * principal f) ≤
      Ap * Aweight * W ^ 2 * s.sup (schwartzSeminormFamily ℝ Varch ℂ) φ *
        Z ^ (M + 5 * eta + loss) :=
    hp'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsup₁ (by positivity)) (Real.rpow_nonneg hZpos.le _))
  have ht'' : Z ^ (-r - 2 * ell - Vlabel) * (∑ f ∈ L, w f * tail f) ≤
      At * Aweight * W ^ 2 * s.sup (schwartzSeminormFamily ℝ Varch ℂ) φ * Z ^ (-saving) :=
    ht'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsup₂ (by positivity)) (Real.rpow_nonneg hZpos.le _))
  have hpoint (f : Ext) :
      ‖canonicalCubeEnergy K S D Γ C f B N φ h mask rad‖ ≤
        retained f + principal f + tail f :=
    parent_norm_le_retained_and_errors K S D Γ hΓ μv ν μ C f B N hsf
      φ h hlc hcs mask rad (Z ^ (R + tau))
  have hsum := Finset.sum_le_sum (fun f hf =>
    mul_le_mul_of_nonneg_left (hpoint f) (hw0 f hf))
  have hscaled := mul_le_mul_of_nonneg_left hsum
    (Real.rpow_nonneg hZpos.le (-r - 2 * ell - Vlabel))
  have hsplit : (∑ f ∈ L, w f * (retained f + principal f + tail f)) =
      (∑ f ∈ L, w f * retained f) + (∑ f ∈ L, w f * principal f) +
        (∑ f ∈ L, w f * tail f) := by
    simp only [mul_add, Finset.sum_add_distrib]
  rw [hsplit, mul_add, mul_add] at hscaled
  apply hscaled.trans
  apply (add_le_add (add_le_add_left hp'' _) ht'').trans
  rw [add_assoc]
  apply add_le_add_left
  let F := Aweight * W ^ 2 * s.sup (schwartzSeminormFamily ℝ Varch ℂ) φ
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have h₁ : 0 ≤ Ap * F * Z ^ (-saving) := by positivity
  have h₂ : 0 ≤ At * F * Z ^ (M + 5 * eta + loss) := by positivity
  dsimp only [F] at h₁ h₂
  nlinarith

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentReduction

end

