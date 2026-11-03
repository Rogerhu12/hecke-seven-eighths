import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondDualZeroDiagonal

/-!
# Sharp second dual-zero counting on nonzero original Gram profiles

The complete original source, masks, column carrier and common labels
are retained. Only the powerful-tuple counting set is restricted to
nonzero original profiles. Its actual finite fibres are bounded by the
original tuple fibres, and all removed amplitudes are exactly zero.
The sharp zero window is consequently independent of the coarse window
needed for the physical tail. No columns or chosen children are changed.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory
open HeckePort.IdealMobiusDivisorSum HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

theorem second_dualZero_diagonal_supported_of_fibers
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ Cbound : ℝ, 0 < Cbound ∧
    ∀ (C : A.GeneralArithmeticContext σ η hS) {ι κ : Type*}
      (left : Finset ι) (right : Finset κ)
      (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior),
    ∀ blocks : ∀ DE : FirstZeroLabel left right fullI fullJ,
      FirstCommonCharacterBlock fullI fullJ DE.val,
    ∀ (profiles : ι → κ → SchwartzMap V ℂ)
      (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
      (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R))
      (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
      (factors : ι × κ → Fin k → Ideal (𝓞 K)) (multiplicity : ℕ),
    (∀ v, ((left ×ˢ right).filter (fun ij => factors ij = v)).card ≤ multiplicity) →
    (∀ ij ∈ left ×ˢ right, PowerfulDiagonal.tupleIdeal (factors ij) =
      (fullI ij.1).val * (fullJ ij.2).val) →
    ∀ N Amp : ℝ, 1 ≤ N → 0 ≤ Amp →
    (∀ ij ∈ left ×ˢ right, profiles ij.1 ij.2 ≠ 0 →
      (Ideal.absNorm ((fullI ij.1).val * (fullJ ij.2).val) : ℝ) ≤ N) →
    (∀ DE, ∀ i ∈ (blocks DE).leftColumns left, ∀ D ∈ M.powerset,
      IsCoprime (engineAllowedGenerator C (blocks DE).commonLeftIdeal * (blocks DE).leftGenerator i)
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) →
    (∀ DE, ∀ j ∈ (blocks DE).rightColumns right, ∀ D ∈ M.powerset,
      IsCoprime (engineAllowedGenerator C (blocks DE).commonRightIdeal * (blocks DE).rightGenerator j)
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) →
    (∀ v ∈ firstZeroPairs left right fullI fullJ,
      seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
        A.exteriorNorm (fullI v.2.1) *
        (∑ D ∈ M.powerset, firstZeroDivisorWeight radius D) ≤ Amp / Real.sqrt N) →
    (∑ DE, ‖((blocks DE).secondFiniteSource hΓ hDiff C left right profiles M radius cutoff hcutoff).dualZeroTerm
      μv hDiff finiteTest‖) ≤ Cbound * multiplicity * Amp * N ^ ε := by
  obtain ⟨seminorms, C₀, hC₀, hzero⟩ :=
    second_dualZero_amplitude_uniform (σ := σ) hΓ μv finiteTest
  obtain ⟨Cdiag, hCdiag, hdiag⟩ :=
    PowerfulDiagonal.powerful_whole_index_normalized_sum_of_fibers (K := K) k ε hε
  refine ⟨seminorms, Cdiag * (1 + C₀), mul_pos hCdiag (by linarith), ?_⟩
  intro C ι κ left right fullI fullJ blocks profiles hDiff radius M cutoff hcutoff
    factors multiplicity hfiber hfactor N Amp hN hAmp hnorm hleftmask hrightmask hprofile
  let allPairs := firstZeroPairs left right fullI fullJ
  let pairs := allPairs.filter (fun v => profiles v.2.1 v.2.2 ≠ 0)
  let amp := secondDualZeroPairAmplitude hΓ μv C left right fullI fullJ
    blocks profiles hDiff finiteTest radius M
  have hampnonneg (v : FirstZeroLabel left right fullI fullJ × (ι × κ)) : 0 ≤ amp v := norm_nonneg _
  have hmem (v) (hv : v ∈ allPairs) := (mem_firstZeroPairs left right fullI fullJ v).mp hv
  have hblock (v) (hv : v ∈ allPairs) :
      v.2.1 ∈ (blocks v.1).leftColumns left ∧
      v.2.2 ∈ (blocks v.1).rightColumns right ∧
      IsCoprime ((blocks v.1).leftResidual v.2.1).val ((blocks v.1).rightResidual v.2.2).val :=
    ((blocks v.1).mem_iff_label left right
      (commonSupportPool_support_eq left right (fun i => (fullI i).val)
        (fun j => (fullJ j).val) v.1.val v.1.property) _ _).mpr (hmem v hv)
  have hpoint (v) (hv : v ∈ allPairs) : amp v ≤
      C₀ * (seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
        A.exteriorNorm (fullI v.2.1) *
        ∑ D ∈ M.powerset, firstZeroDivisorWeight radius D) := by
    have hs : 0 ≤ seminorms.sup (schwartzSeminormFamily ℂ V ℂ)
        (profiles v.2.1 v.2.2) := apply_nonneg _ _
    have hb (D) (hD : D ∈ M.powerset) :
        ‖((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).dualZero
          μv hDiff finiteTest radius D‖ ≤
        C₀ * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
          firstZeroDivisorWeight radius D * A.exteriorNorm (fullI v.2.1) := by
      unfold FirstCommonCharacterBlock.secondPair
      rw [ParentPeriodicPair.gated_dualZero, if_pos (hblock v hv).2.2]
      have he := hzero ((blocks v.1).secondLeftIdeal v.2.1) ((blocks v.1).secondRightIdeal v.2.2)
        _ _ ((blocks v.1).secondLeft_generates C _) ((blocks v.1).secondRight_generates C _)
        (profiles v.2.1 v.2.2) hDiff radius D
        (hleftmask v.1 _ (hblock v hv).1 D hD) (hrightmask v.1 _ (hblock v hv).2.1 D hD)
      apply he.trans
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (mul_nonneg hC₀ hs) (firstZeroDivisorWeight_nonneg radius D))
      rw [(blocks v.1).secondLeftIdeal_eq left _ (hblock v hv).1,
        (blocks v.1).secondRightIdeal_eq right _ (hblock v hv).2.1]
      split_ifs
      · exact le_rfl
      · exact (A.exteriorNorm_pos _).le
    change ‖∑ D ∈ M.powerset,
      ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).dualZero
        μv hDiff finiteTest radius D‖ ≤ _
    calc
      _ ≤ ∑ D ∈ M.powerset,
          ‖((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).dualZero
            μv hDiff finiteTest radius D‖ := norm_sum_le _ _
      _ ≤ ∑ D ∈ M.powerset,
          C₀ * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
            firstZeroDivisorWeight radius D * A.exteriorNorm (fullI v.2.1) :=
        Finset.sum_le_sum (fun D hD => hb D hD)
      _ = C₀ * (seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
          A.exteriorNorm (fullI v.2.1) * ∑ D ∈ M.powerset, firstZeroDivisorWeight radius D) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro D hD
        ring
  have hall (v) (hv : v ∈ pairs) : v ∈ allPairs := (Finset.mem_filter.mp hv).1
  have hij (v) (hv : v ∈ allPairs) : v.2 ∈ left ×ˢ right :=
    Finset.mem_product.mpr ⟨(hmem v hv).1, (hmem v hv).2.1⟩
  have hfiber' (w : Fin k → Ideal (𝓞 K)) :
      (pairs.filter (fun v => factors v.2 = w)).card ≤ multiplicity := by
    let T := pairs.filter (fun v => factors v.2 = w)
    have hi : Set.InjOn
        (fun v : FirstZeroLabel left right fullI fullJ × (ι × κ) => v.2)
        (T : Set (FirstZeroLabel left right fullI fullJ × (ι × κ))) := by
      intro v hv u hu he
      exact firstZeroPairs_projection_injective left right fullI fullJ
        (hall v (Finset.mem_filter.mp hv).1)
        (hall u (Finset.mem_filter.mp hu).1) he
    have hs : T.image Prod.snd ⊆ (left ×ˢ right).filter (fun ij => factors ij = w) := by
      intro ij hij'
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hij'
      exact Finset.mem_filter.mpr
        ⟨hij v (hall v (Finset.mem_filter.mp hv).1), (Finset.mem_filter.mp hv).2⟩
    have hc := (Finset.card_le_card hs).trans (hfiber w)
    rw [Finset.card_image_of_injOn hi] at hc
    exact hc
  have hcoef (v) (hv : v ∈ pairs) : amp v ≤ (C₀ * Amp) / Real.sqrt N := by
    calc
      _ ≤ C₀ * (seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
          A.exteriorNorm (fullI v.2.1) *
          ∑ D ∈ M.powerset, firstZeroDivisorWeight radius D) := hpoint v (hall v hv)
      _ ≤ C₀ * (Amp / Real.sqrt N) :=
        mul_le_mul_of_nonneg_left (hprofile v (hall v hv)) hC₀
      _ = _ := by ring
  have hc := hdiag pairs (fun v => factors v.2) multiplicity hfiber' N (C₀ * Amp)
    (fun v => (amp v : ℂ)) hN (mul_nonneg hC₀ hAmp)
    (by
      intro v hv
      rw [hfactor v.2 (hij v (hall v hv))]
      exact mul_ne_zero (fullI v.2.1).property.1 (fullJ v.2.2).property.1)
    (by
      intro v hv
      rw [hfactor v.2 (hij v (hall v hv))]
      exact hnorm v.2 (hij v (hall v hv)) (Finset.mem_filter.mp hv).2)
    (by
      intro v hv hbad
      have hav := hall v hv
      have hbad' : ¬ Powerful ((fullI v.2.1).val * (fullJ v.2.2).val) := by
        simpa only [hfactor v.2 (hij v hav)] using hbad
      have hz : amp v = 0 := by
        change ‖∑ D ∈ M.powerset,
          ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).dualZero
            μv hDiff finiteTest radius D‖ = 0
        have he : (∑ D ∈ M.powerset,
          ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).dualZero
            μv hDiff finiteTest radius D) = 0 :=
          Finset.sum_eq_zero (fun D hD =>
            (blocks v.1).secondDualZero_of_not_powerful hΓ μv C hDiff finiteTest left right profiles
              v.2.1 (hblock v hav).1 v.2.2 (hblock v hav).2.1 hbad'
              radius D
              (hleftmask v.1 _ (hblock v hav).1 D hD)
              (hrightmask v.1 _ (hblock v hav).2.1 D hD))
        rw [he, norm_zero]
      rw [hz, Complex.ofReal_zero])
    (by
      intro v hv
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hampnonneg v)]
        using hcoef v hv)
  have hvanish (v) (hv : v ∈ allPairs) (hφ : profiles v.2.1 v.2.2 = 0) : amp v = 0 := by
    have hp : amp v ≤ 0 := by
      simpa only [hφ, map_zero, zero_mul, mul_zero] using hpoint v hv
    exact le_antisymm hp (hampnonneg v)
  have hrestrict : (∑ v ∈ allPairs, amp v) = ∑ v ∈ pairs, amp v := by
    dsimp only [pairs]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hφ : profiles v.2.1 v.2.2 = 0
    · rw [if_neg (fun hne => hne hφ)]
      exact hvanish v hv hφ
    · rw [if_pos hφ]
  have hreal : ‖∑ v ∈ pairs, (amp v : ℂ)‖ = ∑ v ∈ pairs, amp v := by
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (Finset.sum_nonneg (fun v _ => hampnonneg v))
  rw [hreal] at hc
  calc
    _ ≤ ∑ v ∈ allPairs, amp v :=
      second_dualZero_blocks_le_pair_sum hΓ μv C left right fullI fullJ blocks profiles
        hDiff finiteTest radius M cutoff hcutoff
    _ = ∑ v ∈ pairs, amp v := hrestrict
    _ ≤ Cdiag * multiplicity * (C₀ * Amp) * N ^ ε := hc
    _ = (Cdiag * C₀) * ((multiplicity : ℝ) * Amp * N ^ ε) := by ring
    _ ≤ (Cdiag * (1 + C₀)) * ((multiplicity : ℝ) * Amp * N ^ ε) := by
      apply mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith : C₀ ≤ 1 + C₀) hCdiag.le)
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hAmp)
        (Real.rpow_nonneg (zero_le_one.trans hN) _)
    _ = (Cdiag * (1 + C₀)) * multiplicity * Amp * N ^ ε := by ring

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.second_dualZero_diagonal_supported_of_fibers
