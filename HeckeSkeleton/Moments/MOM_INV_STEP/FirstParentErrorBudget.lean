import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCappedProduction
import HeckeSkeleton.Moments.MOM_INV_STEP.UniformFirstPrincipal
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedTail
import HeckeSkeleton.Moments.MOM_INV_STEP.UniformSecondTail

/-!
# The complete first physical error of the actual canonical parent

The two restored primitive principal terms and the genuine localized
infinite tail are bounded together. All constants and the finite
archimedean seminorm precede the parent, its original prime lists and
its physical lengths. The coefficient puncture is unrestricted here;
only the extra orbital mask is empty, as in the canonical production.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentErrorBudget

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open CanonicalNormPools CanonicalBlock CanonicalPoissonSplit FirstInversePoisson
  FirstMaskGeometry
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
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "Varch" => mixedEmbedding.euclidean.mixedSpace K

include ν in
theorem exists_actualError_bound (slotCap a : ℕ)
    (lengthCap tauMin saving loss : ℝ) (hcap : 1 ≤ lengthCap)
    (htauMin : 0 < tauMin) (hsaving : 0 ≤ saving) (hloss : 0 < loss)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    ∃ s : Finset (ℕ × ℕ), ∃ A : ℝ, 0 ≤ A ∧
      ∀ {σ : Type*} (T : FirstParentEnergy.Data K S (σ := σ)),
      T.localTest = h → T.mask = ∅ →
      ∀ (G : HeckeCharacter K) (hcal : ThetaCalibrationInput K Sset D T.columns.lambda G)
        (labels : Finset Ext) (w : Ext → ℝ)
        (Z M r ell V η tau Aw : ℝ), ∀ hZ : 1 < Z,
      0 ≤ M → M ≤ lengthCap → 0 ≤ r → r ≤ lengthCap →
      0 ≤ ell → ell ≤ lengthCap → 0 ≤ V → V ≤ lengthCap →
      0 ≤ η → η ≤ 1 → 2 ≤ Z ^ η → tauMin ≤ tau → 0 ≤ Aw →
      T.radius.val = Z ^ (-M) → T.scale.val = Z ^ r →
      T.columns.slots.card ≤ slotCap →
      (∀ i ∈ T.columns.slots, ∀ J ∈ T.columns.primeLists i,
        ‖T.columns.primeWeights i J‖ ≤ 1) →
      (∀ b ∈ T.cubes, height K Sset b ≤ Z ^ (ell + η)) →
      (∀ f ∈ labels, height K Sset f ≤ Z ^ (V + η)) →
      (∀ b ∈ T.cubes, ∀ f ∈ labels, ‖T.columns.labelWeight b f‖ ≤ Z ^ η) →
      (∀ f ∈ labels, 0 ≤ w f) →
      (∀ f ∈ labels, w f ≤ Aw * ((idealDivisors f.val.val).card : ℝ) ^ a) →
      ∀ W : SchwartzMap ℝ ℂ, T.columns.cutoff = W →
      Z ^ (-r - 2 * ell - V) *
        (∑ f ∈ labels, w f * FirstCappedProduction.actualError K S D Γ hΓ μv T f Z tau) ≤
      A * Aw * (SchwartzMap.seminorm ℝ 0 0 W) ^ 2 *
        s.sup (schwartzSeminormFamily ℝ Varch ℂ) T.archTest *
        (Z ^ (M + 5 * η + loss) + Z ^ (-saving)) := by
  obtain ⟨sp, Ap, hAp, hp⟩ := UniformFirstPrincipal.exists_uniform_first_principal_bound
    K S D Γ hΓ μv slotCap a lengthCap loss hcap hloss h hlc hcs
  obtain ⟨st, At, hAt, ht⟩ := FirstLocalizedTail.exists_normalized_source_tail_bound_uniform
    K S D Γ hΓ μv ν slotCap a h hlc hcs lengthCap tauMin saving
      (zero_le_one.trans hcap) htauMin hsaving
  refine ⟨sp ∪ st, Ap + At, add_nonneg hAp hAt, ?_⟩
  intro σ T hlocal hmask G hcal labels w Z M r ell V η tau Aw hZ
    hM0 hM hr0 hr hell0 hell hV0 hV hη hη1 hwidth htau hAw hradius hscale
    hslots hweights hcube hlabels hbeta hw0 hw W hcut
  have hz : 0 < Z := zero_lt_one.trans hZ
  let N := FirstParentEnergy.columnPool K S T
  let P := (T.cubes ×ˢ N) ×ˢ (T.cubes ×ˢ N)
  have hρ : T.radius = ⟨Z ^ (-M), Real.rpow_pos_of_pos hz _⟩ := Subtype.ext hradius
  have hX : T.scale = ⟨Z ^ r, Real.rpow_pos_of_pos hz _⟩ := Subtype.ext hscale
  have hannuli (n : Ext) (hn : n ∈ N) : n ∈ dyadicPool K Sset (Z ^ r) := by
    simpa only [N, FirstParentEnergy.columnPool, hscale] using hn
  have hsf (n : Ext) (hn : n ∈ N) : Squarefree n.val.val :=
    dyadicPool_squarefree K Sset (hannuli n hn)
  have hn (n : Ext) (hn : n ∈ N) : (n.val.val.absNorm : ℝ) ≤ Z ^ (r + η) := by
    have hupper := ((mem_dyadicPool K Sset (Z ^ r) n).mp (hannuli n hn)).2.2
    apply hupper.trans
    calc
      2 * Z ^ r ≤ Z ^ η * Z ^ r :=
        mul_le_mul_of_nonneg_right hwidth (Real.rpow_nonneg hz.le _)
      _ = _ := by rw [← Real.rpow_add hz]; congr 1; ring
  have hW : 0 ≤ SchwartzMap.seminorm ℝ 0 0 W := apply_nonneg _ _
  have hcutbound (n : Ext) (hn : n ∈ N) :
      ‖T.columns.cutoff ((n.val.val.absNorm : ℝ) / T.columns.base ^ T.columns.length)‖ ≤
        SchwartzMap.seminorm ℝ 0 0 W := by
    rw [hcut]
    exact SchwartzMap.norm_le_seminorm ℝ W _
  have hemp : (LocalizedMasks.localizeSupportedMask K Sset
      (∅ : Finset (HeightOneSpectrum (𝓞 K))) (by simp)) = ∅ := by
    simp [LocalizedMasks.localizeSupportedMask]
  have hp' := hp T.columns G hcal T.cubes N labels w
    Z M r ell V η 0 η (SchwartzMap.seminorm ℝ 0 0 W) Aw
    ∅ (by simp) 1 T.archTest hZ.le hM0 hM hr0 hr hell0 hell hV0 hV
    (zero_le_one.trans hcap) hη hη1 le_rfl hW hAw one_ne_zero
    (by simp) (by simp) hslots hweights hsf hn hcube hlabels hbeta hcutbound hw0 hw
  have ht' := ht T.columns G hcal T.cubes N labels (fun _ => P)
    (unitIdeal K S) w T.archTest Z M r ell V η 0 η tau
    (SchwartzMap.seminorm ℝ 0 0 W) Aw hZ.le
    hM0 hM hr0 hr hell0 hell hV0 hV hη (hη1.trans hcap)
    (zero_le_one.trans hcap) (hη1.trans hcap) hwidth htau hW hAw
    hslots hweights hannuli hcube hlabels (by simp [unitIdeal_val])
    (fun _ _ => Finset.Subset.refl _) hbeta hcutbound hw0 hw
  have hsp : sp.sup (schwartzSeminormFamily ℝ Varch ℂ) T.archTest ≤
      (sp ∪ st).sup (schwartzSeminormFamily ℝ Varch ℂ) T.archTest :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_left) _
  have hst : st.sup (schwartzSeminormFamily ℝ Varch ℂ) T.archTest ≤
      (sp ∪ st).sup (schwartzSeminormFamily ℝ Varch ℂ) T.archTest :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) _
  have hp'' := hp'.trans (show _ ≤
      (Ap + At) * Aw * (SchwartzMap.seminorm ℝ 0 0 W) ^ 2 *
        (sp ∪ st).sup (schwartzSeminormFamily ℝ Varch ℂ) T.archTest *
        Z ^ (M + 5 * η + loss) by gcongr; linarith)
  have ht'' := ht'.trans (show _ ≤
      (Ap + At) * Aw * (SchwartzMap.seminorm ℝ 0 0 W) ^ 2 *
        (sp ∪ st).sup (schwartzSeminormFamily ℝ Varch ℂ) T.archTest *
        Z ^ (-saving) by gcongr; linarith)
  have hsum := add_le_add hp'' ht''
  have he : Z ^ (-r - 2 * ell - V) *
      (∑ f ∈ labels, w f * FirstCappedProduction.actualError K S D Γ hΓ μv T f Z tau) =
      Z ^ (-r - 2 * ell - V) *
        (∑ f ∈ labels, w f *
          (2 * ‖canonicalPrincipalSource K S D Γ hΓ T.columns f T.cubes N
            T.archTest h hlc hcs ∅ ⟨Z ^ (-M), Real.rpow_pos_of_pos hz _⟩‖ +
           ‖canonicalPrincipal K S D Γ hΓ μv T.columns f T.cubes N
            T.archTest h hlc hcs ∅ ⟨Z ^ (-M), Real.rpow_pos_of_pos hz _⟩‖)) +
      Z ^ (-r - 2 * ell - V) *
        (∑ f ∈ labels, w f *
          ‖FirstLocalizedTail.sourceSubsetTail K S D Γ hΓ μv T.columns f P
            T.archTest h hlc hcs ∅ ⟨Z ^ (-M), Real.rpow_pos_of_pos hz _⟩
            ⟨Z ^ r, Real.rpow_pos_of_pos hz _⟩ Z tau‖) := by
    simp only [FirstCappedProduction.actualError, hlocal, hmask, hρ, hX,
      mul_add, Finset.sum_add_distrib, N, P]
  rw [he]
  simpa only [hemp, UniformSecondTail.externalMask_unit, ← mul_add] using hsum

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentErrorBudget

end
