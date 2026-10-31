import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalPoissonSplit
import HeckeSkeleton.Moments.MOM_INV_STEP.MaskCounting
import HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalProfileBounds

/-!
# The actual first additive-zero contribution

The bound starts from the literal original marked coefficients and
the actual localized union mask. The principal diagonal is derived from
the real conductor. Every coefficient, mask and mark loss is paid before
the physical normalization is simplified.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ActualPrincipalEstimate

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton MeasureTheory
open HeckeSkeleton.Moments.MOMInvStep DedekindZetaZeroFree.LargeSieve
open CanonicalBlock CanonicalPoissonSplit PrincipalSource PrincipalBudget
  PrincipalZero CoefficientBounds MaskCounting PrimitivePoissonSource ConductorMasks
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

theorem mark_mask_power_identity (X H Q ε : ℝ) (hX : 0 ≤ X) (hH : 0 ≤ H) (hQ : 0 ≤ Q) :
    ((X * H ^ 3) ^ ε) ^ 2 * (Q * H ^ 2 * X ^ 2) ^ ε =
      (Q * X ^ 4 * H ^ 8) ^ ε := by
  rw [pow_two, ← Real.mul_rpow (by positivity) (by positivity),
    ← Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  ring

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

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- No principal energy, diagonal estimate, coefficient estimate, or mask
count is assumed. The only coefficient input is its actual calibration
and the bounds on the original lists and weights. -/
theorem exists_actual_principal_bound (slotCap p : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {σ : Type*} (C : ColumnData K S σ)
      (G : HeckeCharacter K) (hcal : ThetaCalibrationInput K Sset D C.lambda G)
      (B N L : Finset Ext) (w : Ext → ℝ) (X H Y Qmax β W Aweight : ℝ)
      (P : Finset (HeightOneSpectrum (𝓞 K))) (hP : ∀ v ∈ P, v ∉ Sset)
      (Q : Ideal (𝓞 K)) (φ : SchwartzMap V ℂ)
      (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
      (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
      (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (R : {r : ℝ // 0 < r}),
      1 ≤ X → 1 ≤ H → 1 ≤ Y → 0 ≤ Qmax → 0 ≤ β → 0 ≤ W → 0 ≤ Aweight →
      Q ≠ 0 → (Q.absNorm : ℝ) ≤ Qmax → (∀ v ∈ P, v.asIdeal ∣ Q) →
      C.slots.card ≤ slotCap →
      (∀ i ∈ C.slots, ∀ J ∈ C.primeLists i, ‖C.primeWeights i J‖ ≤ 1) →
      (∀ n ∈ N, Squarefree n.val.val) →
      (∀ n ∈ N, (n.val.val.absNorm : ℝ) ≤ X) →
      (∀ b ∈ B, (b.val.val.absNorm : ℝ) ≤ H) →
      (∀ f ∈ L, (f.val.val.absNorm : ℝ) ≤ Y) →
      (∀ b ∈ B, ∀ f ∈ L, ‖C.labelWeight b f‖ ≤ β) →
      (∀ n ∈ N, ‖C.cutoff ((n.val.val.absNorm : ℝ) / C.base ^ C.length)‖ ≤ W) →
      (∀ f ∈ L, 0 ≤ w f) →
      (∀ f ∈ L, w f ≤ Aweight * ((idealDivisors f.val.val).card : ℝ) ^ p) →
      (∑ f ∈ L, w f * ‖canonicalPrincipal K S D Γ hΓ μv C f B N φ h hlc hcs
        (LocalizedMasks.localizeSupportedMask K Sset P hP) R‖) ≤
      A * Aweight * (β * W) ^ 2 * zeroEnvelope K S Γ μv φ h R *
        X * H ^ (1 + ε) * Y ^ (1 + ε) * (Qmax * X ^ 4 * H ^ 8) ^ ε := by
  obtain ⟨Ac, hAc, hcolumn⟩ := exists_uniform_column_bound K S D slotCap ε hε
  obtain ⟨Am, hAm, hmask⟩ := exists_actual_pair_mask_bound K S D ε hε
  obtain ⟨Ap, hAp, hprincipal⟩ := exists_weighted_principal_bound K S D p ε hε
  refine ⟨Ap * Ac ^ 2 * Am, ?_, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hAp (one_le_pow₀ hAc)) hAm
  intro σ C G hcal B N L w X H Y Qmax β W Aweight P hP Q φ h hlc hcs R
    hX hH hY hQmax hβ hW hAweight hQ hQnorm hPQ hcap ha hsf hn hb hf hlabel hcut hw0 hw
  let z := zeroEnvelope K S Γ μv φ h R
  let U := (Ac * β * W * (X * H ^ 3) ^ ε) ^ 2 *
    (Am * (Qmax * H ^ 2 * X ^ 2) ^ ε) * z
  have hz : 0 ≤ z := zeroEnvelope_nonneg K S Γ μv φ h R
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  let summand := fun f x => pairWeight K S D C f x *
    pairPrincipal K S D Γ hΓ μv x.1 x.2 φ h hlc hcs
      (LocalizedMasks.localizeSupportedMask K Sset P hP) R
  have hpoint : ∀ f ∈ L, ∀ x ∈ principalPairs K S D B N, ‖summand f x‖ ≤ U := by
    intro f hfl x hx
    obtain ⟨hxmem, hxzero⟩ := Finset.mem_filter.mp hx
    obtain ⟨hleft, hright⟩ := Finset.mem_product.mp hxmem
    obtain ⟨hb₁, hn₁⟩ := Finset.mem_product.mp hleft
    obtain ⟨hb₂, hn₂⟩ := Finset.mem_product.mp hright
    have hcol₁ := hcolumn C G hcal f x.1.1 x.1.2 X H β W (hsf _ hn₁) hcap
      (le_trans zero_le_one hX) (le_trans zero_le_one hH) hβ hW
      (hn _ hn₁) (hb _ hb₁) (hlabel _ hb₁ f hfl) (hcut _ hn₁) ha
    have hcol₂ := hcolumn C G hcal f x.2.1 x.2.2 X H β W (hsf _ hn₂) hcap
      (le_trans zero_le_one hX) (le_trans zero_le_one hH) hβ hW
      (hn _ hn₂) (hb _ hb₂) (hlabel _ hb₂ f hfl) (hcut _ hn₂) ha
    have hpair : ‖pairWeight K S D C f x‖ ≤
        (Ac * β * W * (X * H ^ 3) ^ ε) ^ 2 := by
      rw [pairWeight, norm_mul, norm_conj, pow_two]
      exact mul_le_mul hcol₁ hcol₂ (norm_nonneg _) (by positivity)
    have hnorm : (Q.absNorm : ℝ) *
        ((x.1.1.val.val * x.2.1.val.val * x.1.2.val.val * x.2.2.val.val).absNorm : ℝ) ≤
        Qmax * H ^ 2 * X ^ 2 := by
      simp only [map_mul, Nat.cast_mul]
      calc
        _ ≤ Qmax * (H * H * X * X) := by gcongr <;> assumption
        _ = _ := by ring
    have hm := (hmask P hP Q hQ hPQ x.1.2 x.2.2 x.1.1 x.2.1).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hnorm hε.le) (le_trans zero_le_one hAm))
    have hp := principalContribution_norm_le K S D Γ hΓ μv
      (pairSupport K S D x.1.2 x.2.2 x.1.1 x.2.1)
      (pairExponent K S x.1.2 x.2.2 x.1.1 x.2.1) φ h hlc hcs
      (LocalizedMasks.localizeSupportedMask K Sset P hP) R
    rw [if_pos hxzero] at hp
    have hp' : ‖pairPrincipal K S D Γ hΓ μv x.1 x.2 φ h hlc hcs
        (LocalizedMasks.localizeSupportedMask K Sset P hP) R‖ ≤
        (Am * (Qmax * H ^ 2 * X ^ 2) ^ ε) * z :=
      hp.trans (mul_le_mul_of_nonneg_right hm hz)
    dsimp only [summand, U]
    rw [norm_mul, mul_assoc]
    exact mul_le_mul hpair hp' (norm_nonneg _) (sq_nonneg _)
  have heq : ∀ f : Ext,
      canonicalPrincipal K S D Γ hΓ μv C f B N φ h hlc hcs
        (LocalizedMasks.localizeSupportedMask K Sset P hP) R =
      ∑ x ∈ principalPairs K S D B N, summand f x :=
    fun f => canonicalPrincipal_eq_principalPairs K S D Γ hΓ μv C f B N φ h hlc hcs
      (LocalizedMasks.localizeSupportedMask K Sset P hP) R
  simp_rw [heq]
  have hp := hprincipal B N L H X Y Aweight U w summand hH hX hY hAweight hU
    hsf hb hn hf hw0 hw hpoint
  have hUeq : U = Ac ^ 2 * Am * (β * W) ^ 2 * z * (Qmax * X ^ 4 * H ^ 8) ^ ε := by
    dsimp only [U]
    calc
      _ = Ac ^ 2 * Am * (β * W) ^ 2 * z *
          (((X * H ^ 3) ^ ε) ^ 2 * (Qmax * H ^ 2 * X ^ 2) ^ ε) := by ring
      _ = _ := by rw [mark_mask_power_identity X H Qmax ε
        (le_trans zero_le_one hX) (le_trans zero_le_one hH) hQmax]
  apply hp.trans_eq
  rw [hUeq]
  dsimp only [z]
  ring


/-- Physical normalization of the literal additive zero contribution.
The fixed constant is independent of Z and all annular lengths. -/
theorem exists_actual_physical_principal_bound
    (slotCap p : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {σ : Type*} (C : ColumnData K S σ)
      (G : HeckeCharacter K) (hcal : ThetaCalibrationInput K Sset D C.lambda G)
      (B N L : Finset Ext) (w : Ext → ℝ)
      (Z M r ell Vlabel eta Qexp betaLoss allowance W Aweight : ℝ)
      (P : Finset (HeightOneSpectrum (𝓞 K))) (hP : ∀ v ∈ P, v ∉ Sset)
      (Q : Ideal (𝓞 K)) (φ : SchwartzMap V ℂ)
      (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
      (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
      (hcs : ∀ v ∈ S, HasCompactSupport (h v)),
      ∀ hZ : 1 ≤ Z,
      0 ≤ M → 0 ≤ r + eta → 0 ≤ ell + eta → 0 ≤ Vlabel + eta →
      0 ≤ W → 0 ≤ Aweight →
      Q ≠ 0 → (Q.absNorm : ℝ) ≤ Z ^ Qexp → (∀ v ∈ P, v.asIdeal ∣ Q) →
      C.slots.card ≤ slotCap →
      (∀ i ∈ C.slots, ∀ J ∈ C.primeLists i, ‖C.primeWeights i J‖ ≤ 1) →
      (∀ n ∈ N, Squarefree n.val.val) →
      (∀ n ∈ N, (n.val.val.absNorm : ℝ) ≤ Z ^ (r + eta)) →
      (∀ b ∈ B, (b.val.val.absNorm : ℝ) ≤ Z ^ (ell + eta)) →
      (∀ f ∈ L, (f.val.val.absNorm : ℝ) ≤ Z ^ (Vlabel + eta)) →
      (∀ b ∈ B, ∀ f ∈ L, ‖C.labelWeight b f‖ ≤ Z ^ betaLoss) →
      (∀ n ∈ N, ‖C.cutoff ((n.val.val.absNorm : ℝ) / C.base ^ C.length)‖ ≤ W) →
      (∀ f ∈ L, 0 ≤ w f) →
      (∀ f ∈ L, w f ≤ Aweight * ((idealDivisors f.val.val).card : ℝ) ^ p) →
      3 * eta + ε * (Qexp + 4 * r + 9 * ell + Vlabel + 14 * eta) + 2 * betaLoss ≤
        ell + allowance →
      Z ^ (-r - 2 * ell - Vlabel) *
        (∑ f ∈ L, w f * ‖canonicalPrincipal K S D Γ hΓ μv C f B N φ h hlc hcs
          (LocalizedMasks.localizeSupportedMask K Sset P hP)
          ⟨Z ^ (-M), Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hZ) _⟩‖) ≤
        A * Aweight * W ^ 2 * zeroProfileSize K S Γ μv φ h * Z ^ (M + allowance) := by
  obtain ⟨A, hA, hbound⟩ := exists_actual_principal_bound K S D Γ hΓ μv slotCap p ε hε
  refine ⟨A, hA, ?_⟩
  intro σ C G hcal B N L w Z M r ell Vlabel eta Qexp betaLoss allowance W Aweight
    P hP Q φ h hlc hcs hZ hM hr hell hV hW hAweight hQ hQnorm hPQ hcap ha
    hsf hn hb hf hlabel hcut hw0 hw hallow
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  let R : {r : ℝ // 0 < r} := ⟨Z ^ (-M), Real.rpow_pos_of_pos hZpos _⟩
  have hbnd := hbound C G hcal B N L w (Z ^ (r + eta)) (Z ^ (ell + eta))
    (Z ^ (Vlabel + eta)) (Z ^ Qexp) (Z ^ betaLoss) W Aweight P hP Q φ h hlc hcs R
    (Real.one_le_rpow hZ hr) (Real.one_le_rpow hZ hell) (Real.one_le_rpow hZ hV)
    (Real.rpow_nonneg hZpos.le _) (Real.rpow_nonneg hZpos.le _) hW hAweight
    hQ hQnorm hPQ hcap ha hsf hn hb hf hlabel hcut hw0 hw
  have hzero := zeroEnvelope_physical_scale K S Γ μv φ h Z M hZ hM
  have hscaled := mul_le_mul_of_nonneg_left hbnd (Real.rpow_nonneg hZpos.le _)
  have hbudget := physical_marked_principal_budget Z hZ M r ell Vlabel eta ε
    Qexp betaLoss allowance hallow
  have hconst : 0 ≤ A * Aweight * W ^ 2 * zeroProfileSize K S Γ μv φ h := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (le_trans zero_le_one hA) hAweight)
      (sq_nonneg _)) (zeroProfileSize_nonneg K S Γ μv φ h)
  apply hscaled.trans
  calc
    _ ≤ Z ^ (-r - 2 * ell - Vlabel) *
        (A * Aweight * (Z ^ betaLoss * W) ^ 2 *
          (zeroProfileSize K S Γ μv φ h * Z ^ M) *
          Z ^ (r + eta) * (Z ^ (ell + eta)) ^ (1 + ε) *
          (Z ^ (Vlabel + eta)) ^ (1 + ε) *
          (Z ^ Qexp * (Z ^ (r + eta)) ^ 4 * (Z ^ (ell + eta)) ^ 8) ^ ε) := by
      gcongr
    _ ≤ A * Aweight * W ^ 2 * zeroProfileSize K S Γ μv φ h *
        Z ^ (M + allowance) := by
      convert mul_le_mul_of_nonneg_left hbudget hconst using 1 <;> ring
end HeckeSkeleton.Moments.MOM_INV_STEP.ActualPrincipalEstimate

end
