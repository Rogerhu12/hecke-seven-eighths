import HeckeSkeleton.Moments.MOM_INV_STEP.ActualPrincipalEstimate
import HeckeSkeleton.Moments.MOM_INV_STEP.PhysicalPrincipalEstimate
import HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalProfileBounds

/-!
# Uniform first principal cost on bounded length ranges

The two physical principal copies and the two additive zeros occurring
in the genuine principal-restoration inequality are bounded together.
All small-power exponents, the finite Schwartz family, and the constant
are selected before Z, the annular lengths, and every original column.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.UniformFirstPrincipal

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton MeasureTheory
open HeckeSkeleton.Moments.MOMInvStep DedekindZetaZeroFree.LargeSieve
open FixedTripleFibers CanonicalBlock CanonicalPoissonSplit PrincipalZero
open scoped Classical BigOperators nonZeroDivisors

/-- One exponent works simultaneously for every length in the fixed box. -/
theorem exists_loss_exponents (L loss : ℝ) (hL : 1 ≤ L) (hloss : 0 < loss) :
    ∃ eps rowEps : ℝ, 0 < eps ∧ 0 < rowEps ∧
      ∀ M r ell V Q eta beta : ℝ,
      M ≤ L → r ≤ L → 0 ≤ ell → ell ≤ L → V ≤ L → Q ≤ L →
      0 ≤ eta → eta ≤ 1 → beta ≤ eta →
      (3 * eta + eps * (Q + 4 * r + 9 * ell + V + 14 * eta) + 2 * beta ≤
        ell + (5 * eta + loss)) ∧
      (3 * eta + eps * (2 * r + 7 * ell + V + 10 * eta) +
        rowEps * M + 2 * beta ≤ ell + (5 * eta + loss)) := by
  let eps := loss / (2 * (15 * L + 14))
  let rowEps := loss / (2 * L)
  have hden : 0 < 2 * (15 * L + 14) := by linarith
  have hdenr : 0 < 2 * L := by linarith
  have heps : 0 < eps := div_pos hloss hden
  have hrow : 0 < rowEps := div_pos hloss hdenr
  have heps_eq : eps * (15 * L + 14) = loss / 2 := by
    have hh := div_mul_cancel₀ loss hden.ne'
    change eps * (2 * (15 * L + 14)) = loss at hh
    nlinarith
  have hrow_eq : rowEps * L = loss / 2 := by
    have hh := div_mul_cancel₀ loss hdenr.ne'
    change rowEps * (2 * L) = loss at hh
    nlinarith
  refine ⟨eps, rowEps, heps, hrow, ?_⟩
  intro M r ell V Q eta beta hM hr hell0 hell hV hQ heta heta1 hbeta
  have ha : Q + 4 * r + 9 * ell + V + 14 * eta ≤ 15 * L + 14 := by linarith
  have hb : 2 * r + 7 * ell + V + 10 * eta ≤ 15 * L + 14 := by linarith
  have ha' := mul_le_mul_of_nonneg_left ha heps.le
  have hb' := mul_le_mul_of_nonneg_left hb heps.le
  have hm' := mul_le_mul_of_nonneg_left hM hrow.le
  rw [heps_eq] at ha' hb'
  rw [hrow_eq] at hm'
  constructor <;> linarith

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

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "Varch" => mixedEmbedding.euclidean.mixedSpace K

/-- The complete principal-restoration cost, with no estimate of a source
or of an energy assumed. The original mark cap is unchanged. -/
theorem exists_uniform_first_principal_bound
    (slotCap p : ℕ) (Lmax loss : ℝ) (hLmax : 1 ≤ Lmax) (hloss : 0 < loss)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    ∃ s : Finset (ℕ × ℕ), ∃ A : ℝ, 0 ≤ A ∧
      ∀ {σ : Type*} (C : ColumnData K S σ)
      (G : HeckeCharacter K) (hcal : ThetaCalibrationInput K Sset D C.lambda G)
      (B N labels : Finset Ext) (w : Ext → ℝ)
      (Z M r ell Vlabel eta Qexp betaLoss W Aweight : ℝ)
      (P : Finset (HeightOneSpectrum (𝓞 K))) (hP : ∀ v ∈ P, v ∉ Sset)
      (Q : Ideal (𝓞 K)) (φ : SchwartzMap Varch ℂ),
      ∀ hZ : 1 ≤ Z,
      0 ≤ M → M ≤ Lmax → 0 ≤ r → r ≤ Lmax →
      0 ≤ ell → ell ≤ Lmax → 0 ≤ Vlabel → Vlabel ≤ Lmax →
      Qexp ≤ Lmax → 0 ≤ eta → eta ≤ 1 → betaLoss ≤ eta →
      0 ≤ W → 0 ≤ Aweight →
      Q ≠ 0 → (Q.absNorm : ℝ) ≤ Z ^ Qexp → (∀ v ∈ P, v.asIdeal ∣ Q) →
      C.slots.card ≤ slotCap →
      (∀ i ∈ C.slots, ∀ J ∈ C.primeLists i, ‖C.primeWeights i J‖ ≤ 1) →
      (∀ n ∈ N, Squarefree n.val.val) →
      (∀ n ∈ N, (n.val.val.absNorm : ℝ) ≤ Z ^ (r + eta)) →
      (∀ b ∈ B, (b.val.val.absNorm : ℝ) ≤ Z ^ (ell + eta)) →
      (∀ f ∈ labels, (f.val.val.absNorm : ℝ) ≤ Z ^ (Vlabel + eta)) →
      (∀ b ∈ B, ∀ f ∈ labels, ‖C.labelWeight b f‖ ≤ Z ^ betaLoss) →
      (∀ n ∈ N, ‖C.cutoff ((n.val.val.absNorm : ℝ) / C.base ^ C.length)‖ ≤ W) →
      (∀ f ∈ labels, 0 ≤ w f) →
      (∀ f ∈ labels, w f ≤ Aweight * ((idealDivisors f.val.val).card : ℝ) ^ p) →
      Z ^ (-r - 2 * ell - Vlabel) *
        (∑ f ∈ labels, w f *
          (2 * ‖canonicalPrincipalSource K S D Γ hΓ C f B N φ h hlc hcs
            (LocalizedMasks.localizeSupportedMask K Sset P hP)
            ⟨Z ^ (-M), Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hZ) _⟩‖ +
          ‖canonicalPrincipal K S D Γ hΓ μv C f B N φ h hlc hcs
            (LocalizedMasks.localizeSupportedMask K Sset P hP)
            ⟨Z ^ (-M), Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hZ) _⟩‖)) ≤
      A * Aweight * W ^ 2 * s.sup (schwartzSeminormFamily ℝ Varch ℂ) φ *
        Z ^ (M + 5 * eta + loss) := by
  obtain ⟨eps, rowEps, heps, hrow, hbudget⟩ :=
    exists_loss_exponents Lmax loss hLmax hloss
  obtain ⟨s₁, A₁, hA₁, hphysical⟩ :=
    PhysicalPrincipalEstimate.exists_actual_physical_principalSource_bound
      K S D Γ hΓ slotCap p eps rowEps heps hrow h hlc hcs
  obtain ⟨A₀, hA₀, hzeros⟩ :=
    ActualPrincipalEstimate.exists_actual_physical_principal_bound
      K S D Γ hΓ μv slotCap p eps heps
  obtain ⟨s₂, Az, hAz, hprofile⟩ :=
    PrincipalProfileBounds.exists_zeroProfileSize_bound K S μv Γ h
  let s := s₁ ∪ s₂
  refine ⟨s, 2 * A₁ + A₀ * Az,
    add_nonneg (mul_nonneg (by norm_num) hA₁)
      (mul_nonneg (le_trans zero_le_one hA₀) hAz), ?_⟩
  intro σ C G hcal B N labels w Z M r ell Vlabel eta Qexp betaLoss W Aweight
    P hP Q φ hZ hM0 hM hr0 hr hell0 hell hV0 hV hQexp heta heta1 hbeta
    hW hAw hQ hQnorm hPQ hcap ha hsf hn hb hf hlabel hcut hw0 hw
  obtain ⟨hbudget₀, hbudget₁⟩ := hbudget M r ell Vlabel Qexp eta betaLoss
    hM hr hell0 hell hV hQexp heta heta1 hbeta
  have hphys := hphysical C G hcal B N labels w Z M r ell Vlabel eta betaLoss
    (5 * eta + loss) W Aweight
    (LocalizedMasks.localizeSupportedMask K Sset P hP) φ hZ hM0
    (add_nonneg hr0 heta) (add_nonneg hell0 heta) (add_nonneg hV0 heta)
    hW hAw hcap ha hsf hn hb hf hlabel hcut hw0 hw hbudget₁
  have hzero := hzeros C G hcal B N labels w Z M r ell Vlabel eta Qexp betaLoss
    (5 * eta + loss) W Aweight P hP Q φ h hlc hcs hZ hM0
    (add_nonneg hr0 heta) (add_nonneg hell0 heta) (add_nonneg hV0 heta)
    hW hAw hQ hQnorm hPQ hcap ha hsf hn hb hf hlabel hcut hw0 hw hbudget₀
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
  have hzprofile := (hprofile φ).trans (mul_le_mul_of_nonneg_left hsup₂ hAz)
  have hphys' := hphys.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsup₁ (by positivity : 0 ≤ A₁ * Aweight * W ^ 2))
    (Real.rpow_nonneg (le_trans zero_le_one hZ) _))
  have hzero' := hzero.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hzprofile
      (by positivity : 0 ≤ A₀ * Aweight * W ^ 2))
    (Real.rpow_nonneg (le_trans zero_le_one hZ) _))
  have hboth := add_le_add (mul_le_mul_of_nonneg_left hphys' (by norm_num : (0 : ℝ) ≤ 2))
    hzero'
  have hsum (a b : Ext → ℝ) :
      (∑ f ∈ labels, w f * (2 * a f + b f)) =
        2 * (∑ f ∈ labels, w f * a f) + ∑ f ∈ labels, w f * b f := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro f hf
    ring
  convert hboth using 1
  · rw [hsum]
    ring
  · rw [show M + 5 * eta + loss = M + (5 * eta + loss) by ring]
    ring

end HeckeSkeleton.Moments.MOM_INV_STEP.UniformFirstPrincipal

end

