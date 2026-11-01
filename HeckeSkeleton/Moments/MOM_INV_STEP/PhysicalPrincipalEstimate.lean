import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalPoissonSplit
import HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalOrbitalMass

/-!
# The whole physical principal source

This counts the actual empty-conductor pairs and bounds their whole
nonzero orbital series. In particular it does not identify principal
restoration with the two additive zero terms.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.PhysicalPrincipalEstimate

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton MeasureTheory
open HeckeSkeleton.Moments.MOMInvStep DedekindZetaZeroFree.LargeSieve
open CanonicalBlock CanonicalPoissonSplit PrincipalSource PrincipalBudget
  CoefficientBounds PrimitivePoissonSource ConductorMasks PrincipalOrbitalMass
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

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

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

theorem exists_physical_principal_bound (slotCap p : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {σ : Type*} (C : ColumnData K S σ)
      (G : HeckeCharacter K) (hcal : ThetaCalibrationInput K Sset D C.lambda G)
      (B N L : Finset Ext) (w : Ext → ℝ) (X H Y β W Aweight : ℝ)
      (φ : SchwartzMap V ℂ)
      (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
      (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
      (hcs : ∀ v ∈ S, HasCompactSupport (h v))
      (M : Finset (HeightOneSpectrum OS)) (R : {r : ℝ // 0 < r}),
      1 ≤ X → 1 ≤ H → 1 ≤ Y → 0 ≤ β → 0 ≤ W → 0 ≤ Aweight →
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
      (∑ f ∈ L, w f * ‖canonicalPrincipalSource K S D Γ hΓ C f B N φ h hlc hcs M R‖) ≤
        A * Aweight * (β * W) ^ 2 *
          absoluteRowMass K Sset Γ φ (sIntegerFiniteTestFunction K S h) R *
          X * H ^ (1 + ε) * Y ^ (1 + ε) * (X * H ^ 3) ^ (2 * ε) := by
  letI : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K) :=
    fun v => borel (v.adicCompletion K)
  letI : ∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K) :=
    fun _ => ⟨rfl⟩
  obtain ⟨Ac, hAc, hcolumn⟩ := exists_uniform_column_bound K S D slotCap ε hε
  obtain ⟨Ap, hAp, hprincipal⟩ := exists_weighted_principal_bound K S D p ε hε
  refine ⟨Ap * Ac ^ 2, one_le_mul_of_one_le_of_one_le hAp (one_le_pow₀ hAc), ?_⟩
  intro σ C G hcal B N L w X H Y β W Aweight φ h hlc hcs M R
    hX hH hY hβ hW hAweight hcap ha hsf hn hb hf hlabel hcut hw0 hw
  let z := absoluteRowMass K Sset Γ φ (sIntegerFiniteTestFunction K S h) R
  have hz : 0 ≤ z := tsum_nonneg (fun _ => norm_nonneg _)
  let U := (Ac * β * W * (X * H ^ 3) ^ ε) ^ 2 * z
  have hU : 0 ≤ U := mul_nonneg (sq_nonneg _) hz
  let summand := fun f x => pairWeight K S D C f x *
    (primitivePairBlock K S D Γ hΓ x.1 x.2 φ h hlc hcs M R).physical
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
      rw [pairWeight, norm_mul, Complex.norm_conj, pow_two]
      exact mul_le_mul hcol₁ hcol₂ (norm_nonneg _) (by positivity)
    have hp : ‖(primitivePairBlock K S D Γ hΓ x.1 x.2 φ h hlc hcs M R).physical‖ ≤ z :=
      principal_physical_norm_le_profile_mass K S D Γ hΓ
        (pairSupport K S D x.1.2 x.2.2 x.1.1 x.2.1)
        (pairExponent K S x.1.2 x.2.2 x.1.1 x.2.1) hxzero φ h hlc hcs M R
    dsimp only [summand, U]
    rw [norm_mul]
    exact mul_le_mul hpair hp (norm_nonneg _) (sq_nonneg _)
  have hp := hprincipal B N L H X Y Aweight U w summand hH hX hY hAweight hU
    hsf hb hn hf hw0 hw hpoint
  have he : ((X * H ^ 3) ^ ε) ^ 2 = (X * H ^ 3) ^ (2 * ε) := by
    rw [pow_two, ← Real.rpow_add (mul_pos (lt_of_lt_of_le zero_lt_one hX)
      (pow_pos (lt_of_lt_of_le zero_lt_one hH) _))]
    congr 1
    ring
  change (∑ f ∈ L, w f * ‖∑ x ∈ principalPairs K S D B N, summand f x‖) ≤ _
  apply hp.trans_eq
  dsimp only [U, z]
  calc
    _ = Ap * Ac ^ 2 * Aweight * (β * W) ^ 2 *
        absoluteRowMass K Sset Γ φ (sIntegerFiniteTestFunction K S h) R *
        X * H ^ (1 + ε) * Y ^ (1 + ε) * ((X * H ^ 3) ^ ε) ^ 2 := by ring
    _ = _ := by rw [he]

/-- The physical principal exponent includes the arbitrarily small
extra loss needed at small radius. -/
theorem physical_source_principal_identity (Z : ℝ) (hZ : 0 < Z)
    (M r ell Vlabel eta eps rowEps betaLoss : ℝ) :
    Z ^ (-r - 2 * ell - Vlabel) * (Z ^ betaLoss) ^ 2 *
      Z ^ ((1 + rowEps) * M) * Z ^ (r + eta) *
      (Z ^ (ell + eta)) ^ (1 + eps) * (Z ^ (Vlabel + eta)) ^ (1 + eps) *
      (Z ^ (r + eta) * (Z ^ (ell + eta)) ^ 3) ^ (2 * eps) =
      Z ^ (M - ell + 3 * eta + eps * (2 * r + 7 * ell + Vlabel + 10 * eta) +
        rowEps * M + 2 * betaLoss) := by
  have hp (a : ℝ) (n : ℕ) : (Z ^ a) ^ n = Z ^ (a * n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hZ.le]
  have hi : Z ^ (r + eta) * (Z ^ (ell + eta)) ^ 3 =
      Z ^ (r + eta + 3 * (ell + eta)) := by
    rw [hp, ← Real.rpow_add hZ]
    congr 1
    norm_num
    ring
  rw [hi, hp, ← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le]
  repeat rw [← Real.rpow_add hZ]
  congr 1
  norm_num
  ring

theorem physical_source_principal_budget (Z : ℝ) (hZ : 1 ≤ Z)
    (M r ell Vlabel eta eps rowEps betaLoss allowance : ℝ)
    (hallow : 3 * eta + eps * (2 * r + 7 * ell + Vlabel + 10 * eta) +
      rowEps * M + 2 * betaLoss ≤ ell + allowance) :
    Z ^ (-r - 2 * ell - Vlabel) * (Z ^ betaLoss) ^ 2 *
      Z ^ ((1 + rowEps) * M) * Z ^ (r + eta) *
      (Z ^ (ell + eta)) ^ (1 + eps) * (Z ^ (Vlabel + eta)) ^ (1 + eps) *
      (Z ^ (r + eta) * (Z ^ (ell + eta)) ^ 3) ^ (2 * eps) ≤ Z ^ (M + allowance) := by
  rw [physical_source_principal_identity Z (lt_of_lt_of_le zero_lt_one hZ)]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)


/-- The whole original physical principal source has its required
normalized budget, with a single finite Schwartz control chosen first. -/
theorem exists_actual_physical_principalSource_bound
    (slotCap p : ℕ) (ε rowEps : ℝ) (hε : 0 < ε) (hrowEps : 0 < rowEps)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    ∃ s : Finset (ℕ × ℕ), ∃ A : ℝ, 0 ≤ A ∧
      ∀ {σ : Type*} (C : ColumnData K S σ)
      (G : HeckeCharacter K) (hcal : ThetaCalibrationInput K Sset D C.lambda G)
      (B N L : Finset Ext) (w : Ext → ℝ)
      (Z M r ell Vlabel eta betaLoss allowance W Aweight : ℝ)
      (mask : Finset (HeightOneSpectrum OS)) (φ : SchwartzMap V ℂ),
      ∀ hZ : 1 ≤ Z,
      0 ≤ M → 0 ≤ r + eta → 0 ≤ ell + eta → 0 ≤ Vlabel + eta →
      0 ≤ W → 0 ≤ Aweight → C.slots.card ≤ slotCap →
      (∀ i ∈ C.slots, ∀ J ∈ C.primeLists i, ‖C.primeWeights i J‖ ≤ 1) →
      (∀ n ∈ N, Squarefree n.val.val) →
      (∀ n ∈ N, (n.val.val.absNorm : ℝ) ≤ Z ^ (r + eta)) →
      (∀ b ∈ B, (b.val.val.absNorm : ℝ) ≤ Z ^ (ell + eta)) →
      (∀ f ∈ L, (f.val.val.absNorm : ℝ) ≤ Z ^ (Vlabel + eta)) →
      (∀ b ∈ B, ∀ f ∈ L, ‖C.labelWeight b f‖ ≤ Z ^ betaLoss) →
      (∀ n ∈ N, ‖C.cutoff ((n.val.val.absNorm : ℝ) / C.base ^ C.length)‖ ≤ W) →
      (∀ f ∈ L, 0 ≤ w f) →
      (∀ f ∈ L, w f ≤ Aweight * ((idealDivisors f.val.val).card : ℝ) ^ p) →
      3 * eta + ε * (2 * r + 7 * ell + Vlabel + 10 * eta) +
        rowEps * M + 2 * betaLoss ≤ ell + allowance →
      Z ^ (-r - 2 * ell - Vlabel) *
        (∑ f ∈ L, w f * ‖canonicalPrincipalSource K S D Γ hΓ C f B N φ h hlc hcs mask
          ⟨Z ^ (-M), Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hZ) _⟩‖) ≤
      A * Aweight * W ^ 2 * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
        Z ^ (M + allowance) := by
  obtain ⟨Ap, hAp, hp⟩ := exists_physical_principal_bound K S D Γ hΓ slotCap p ε hε
  obtain ⟨s, Am, hAm, hm⟩ := exists_absoluteRowMass_rowScale_bound K Sset Γ
    (sIntegerFiniteTestFunction K S h)
    (continuous_sIntegerFiniteTestFunction K S h hlc)
    (hasCompactSupport_sIntegerFiniteTestFunction K S h hcs) rowEps hrowEps
  refine ⟨s, Ap * Am, mul_nonneg (le_trans zero_le_one hAp) hAm, ?_⟩
  intro σ C G hcal B N L w Z M r ell Vlabel eta betaLoss allowance W Aweight
    mask φ hZ hM hr hell hV hW hAweight hcap ha hsf hn hb hf hlabel hcut hw0 hw hallow
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  let R : {r : ℝ // 0 < r} := ⟨Z ^ (-M), Real.rpow_pos_of_pos hZpos _⟩
  have hbnd := hp C G hcal B N L w (Z ^ (r + eta)) (Z ^ (ell + eta))
    (Z ^ (Vlabel + eta)) (Z ^ betaLoss) W Aweight φ h hlc hcs mask R
    (Real.one_le_rpow hZ hr) (Real.one_le_rpow hZ hell) (Real.one_le_rpow hZ hV)
    (Real.rpow_nonneg hZpos.le _) hW hAweight hcap ha hsf hn hb hf hlabel hcut hw0 hw
  have hmass := hm φ Z M hZ hM
  have hscaled := mul_le_mul_of_nonneg_left hbnd
    (Real.rpow_nonneg hZpos.le (-r - 2 * ell - Vlabel))
  have hbudget := physical_source_principal_budget Z hZ M r ell Vlabel eta ε
    rowEps betaLoss allowance hallow
  have hconst : 0 ≤ (Ap * Am) * Aweight * W ^ 2 *
      s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (le_trans zero_le_one hAp) hAm) hAweight) (sq_nonneg _))
      (apply_nonneg _ _)
  apply hscaled.trans
  calc
    _ ≤ Z ^ (-r - 2 * ell - Vlabel) *
        (Ap * Aweight * (Z ^ betaLoss * W) ^ 2 *
          (Am * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * Z ^ ((1 + rowEps) * M)) *
          Z ^ (r + eta) * (Z ^ (ell + eta)) ^ (1 + ε) *
          (Z ^ (Vlabel + eta)) ^ (1 + ε) *
          (Z ^ (r + eta) * (Z ^ (ell + eta)) ^ 3) ^ (2 * ε)) := by
      gcongr
    _ ≤ (Ap * Am) * Aweight * W ^ 2 * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
        Z ^ (M + allowance) := by
      convert mul_le_mul_of_nonneg_left hbudget hconst using 1 <;> ring
end HeckeSkeleton.Moments.MOM_INV_STEP.PhysicalPrincipalEstimate

end
