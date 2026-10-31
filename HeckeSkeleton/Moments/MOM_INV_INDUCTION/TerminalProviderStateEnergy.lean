import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderFrozenBlock

/-!
# Uniform completed-source energy for one actual frozen state

The retained dyadic rectangles cost an arbitrarily small power. Their
canonical saving and the genuinely summable omitted range are combined
before any original tuple or frozen-row count is inserted. Constants
precede the state, scale, finite row support, and original coefficients.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalStateEnergy

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.IdealRows HeckeSkeleton.LowEnergy.ActualReflection
  HeckeSkeleton.LowEnergy.ActualReflectionReindex
  HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open GeneralReflectedEnergy ProviderTerminalConductor TerminalFrozenBlock
open scoped Classical BigOperators nonZeroDivisors

theorem exists_indices_mass_bound (L cstar : ℝ) (hL : 0 ≤ L) (hcstar : 0 < cstar) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ Z R : ℝ, 2 ≤ Z → 0 < R → R ≤ Z ^ L →
      ((TerminalRectangles.indices R).card : ℝ) ^ 2 ≤ B * Z ^ (cstar / 16) := by
  let delta := cstar / (64 * (L + 1))
  have hd : 0 < delta := div_pos hcstar (by positivity)
  obtain ⟨C, hC, hb⟩ := CubeCompletionBlocks.exists_count_small_power delta hd
  refine ⟨C ^ 4, one_le_pow₀ hC, ?_⟩
  intro Z R hZ hR hRL
  have hz : 0 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hZ1 : 1 ≤ Z := by linarith
  have hcap : 2 * max 1 R ≤ Z ^ (L + 1) := by
    rw [Real.rpow_add hz, Real.rpow_one]
    have hm : max 1 R ≤ Z ^ L := max_le (Real.one_le_rpow hZ1 hL) hRL
    nlinarith [Real.rpow_nonneg hz.le L]
  have hc : (CubeCompletionBlocks.count (2 * max 1 R) : ℝ) ≤ C * Z ^ (cstar / 64) := by
    have ht := hb (2 * max 1 R) (by linarith [le_max_left 1 R])
    have hp := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 2 * max 1 R) hcap hd.le
    rw [← Real.rpow_mul hz.le] at hp
    have he : (L + 1) * delta = cstar / 64 := by
      dsimp only [delta]
      field_simp
      <;> ring
    rw [he] at hp
    exact ht.trans (mul_le_mul_of_nonneg_left hp (zero_le_one.trans hC))
  have hi := TerminalRectangles.indices_card_bound R
  calc
    _ ≤ ((CubeCompletionBlocks.count (2 * max 1 R) : ℝ) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hi 2
    _ = (CubeCompletionBlocks.count (2 * max 1 R) : ℝ) ^ 4 := by ring
    _ ≤ (C * Z ^ (cstar / 64)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hc 4
    _ = C ^ 4 * Z ^ (cstar / 16) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hz.le]
      congr 1
      congr 1
      ring

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)
local notation "Ext" => ExteriorIdeal K S

theorem boundedSource_mono (f : FixedData K S) {Z L L' Nstar H za : ℝ}
    (hZ : 1 ≤ Z) (hL : L ≤ L') (h : BoundedSource K S f Z L Nstar H za) :
    BoundedSource K S f Z L' Nstar H za := by
  have hp := Real.rpow_le_rpow_of_exponent_le hZ hL
  exact ⟨h.1.trans hL, h.2.1, h.2.2.1.trans hL, h.2.2.2.1,
    h.2.2.2.2.1.trans hL, h.2.2.2.2.2.1.trans hp,
    h.2.2.2.2.2.2.1.trans hp, h.2.2.2.2.2.2.2.trans hp⟩

/-- Two fixed Euler seminorms suffice for the full original reflected
source. The powerful count is deliberately not yet charged here. -/
theorem exists_uniform_state_energy
    (backgrounds : Finset (HeckeCharacter K))
    (R : ReflectionFamily K S D backgrounds) (hE : Input K S D R.data backgrounds)
    (L lo hi cstar : ℝ) (hL : 1 ≤ L) (hlo : 0 < lo) (hhi : lo ≤ hi) (hcstar : 0 < cstar) :
    ∃ C Z₀ AB AT : ℝ, ∃ JB JT : ℕ,
      0 < C ∧ 2 ≤ Z₀ ∧ 0 ≤ AB ∧ 0 ≤ AT ∧
      ∀ (θ : HeckeCharacter K), θ ∈ backgrounds →
      ∀ (P J f r : Ext) (hr : Squarefree r.val.val) (u : S.unit K)
        (inactive : Finset (ExteriorPrime K S))
        (haway : ∀ p ∈ inactive, ¬p.val.asIdeal ∣ (frozenIdeal K S P J f).val.val ∧
          ¬p.val.asIdeal ∣ r.val.val)
        (s : FrozenState K S (frozenIdeal K S P J f) r)
        (W : SmoothAnnularTest) (Z N V M Q z d c O H za h amp : ℝ),
      Z₀ ≤ Z → Powerful P.val →
      BoundedSource K S (fixedData K S P J f r hr u inactive haway) Z L (N - 3 * h) H za →
      0 ≤ O → O ≤ L → 0 ≤ za → za ≤ z → 0 ≤ h → h ≤ d → 0 ≤ amp →
      exteriorNorm K S f ≤ Z ^ V → exteriorNorm K S r ≤ Z ^ Q →
      0 ≤ M → 0 ≤ Q → 0 ≤ N + V → V ≤ d →
      HeckePort.Moments.CanonicalMargins (N + V) M Q z c →
      cstar / 2 ≤ c → d ≤ cstar / 1000 →
      Function.support W.toFun ⊆ Set.Icc lo hi →
      ∀ (rows ps : Finset Ext) (a : Ext → ℂ),
      (∀ k ∈ rows, exteriorNorm K S (exteriorMul K S (exteriorMul K S P J) k) ≤ Z ^ M) →
      Z ^ O ≤ exteriorNorm K S P →
      (∀ k ∈ rows, InAnnulus K S Z H k) →
      (∀ p ∈ ps, InAnnulus K S Z za p) →
      (∀ p ∈ ps, ‖a p‖ ≤ amp) →
      (∑ k ∈ rows, ‖fullSource K S D (fixedData K S P J f r hr u inactive haway) s
        (R.data θ) θ a W.toFun (Z ^ (N - 3 * h)) ps k‖ ^ 2) ≤
        C * amp ^ 2 * (testSeminorm W.toFun JB AB + testSeminorm W.toFun JT AT) ^ 2 *
          ‖inactiveWeight K S (fixedData K S P J f r hr u inactive haway)‖ ^ 2 *
            Z ^ (N + V - cstar / 8 - O / 2) := by
  let Lbig := 10 * L + cstar + 1
  let tau := cstar / 1000
  let saving := L + cstar
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hbig : 0 < Lbig := by dsimp only [Lbig]; positivity
  have htau : 0 < tau := div_pos hcstar (by norm_num)
  have hsaving : 0 < saving := by dsimp only [saving]; positivity
  obtain ⟨CB, ZB, AB, JB, hCB, hZB, hAB, hb⟩ := canonical_block_energy K S D
    backgrounds R.data hE Lbig lo hi tau hbig hlo hhi htau
  obtain ⟨CT, hCT, ht⟩ := TerminalSelectedTail.uniform_energy K S D
    backgrounds R L tau saving hLp htau hsaving
  obtain ⟨BD, hBD, hd⟩ := exists_indices_mass_bound Lbig cstar hbig.le hcstar
  let AT := TerminalTail.tailShift L tau saving
  let JT := TerminalTail.kernelOrder K AT
  refine ⟨2 * (BD * CB + CT), max 2 ZB, AB, AT, JB, JT, by positivity,
    le_max_left _ _, hAB, le_trans (by norm_num) (TerminalTail.tailShift_ge_two hLp.le htau hsaving.le), ?_⟩
  intro θ hθ P J f r hr u inactive haway s W Z N V M Q z d c O H za h amp
    hZ hP hsource hO hOL hza hz hh hhd hamp hf hpr hM hQ hF hV hinv hc hdsmall hW
    rows ps a hrows hpower hrowsWindow hps ha
  have hZ2 : 2 ≤ Z := (le_max_left _ _).trans hZ
  have hZB' : ZB ≤ Z := (le_max_right _ _).trans hZ
  have hZ' : 1 < Z := lt_of_lt_of_le (by norm_num) hZ2
  have hz0 := zero_lt_one.trans hZ'
  let fdata := fixedData K S P J f r hr u inactive haway
  let T := threshold K S fdata s Z (N - 3 * h) H za
  let cap := Z ^ (T + tau)
  let qB := testSeminorm W.toFun JB AB
  let qT := testSeminorm W.toFun JT AT
  let w := ‖inactiveWeight K S fdata‖
  have hqB : 0 ≤ qB := ThetaGlobal.ReflectedAbsoluteProject.testSeminorm_nonneg _ _ _
  have hqT : 0 ≤ qT := ThetaGlobal.ReflectedAbsoluteProject.testSeminorm_nonneg _ _ _
  have hw : 0 ≤ w := norm_nonneg _
  have hT : T ≤ 9 * L := TerminalTail.threshold_le K S fdata s hZ' hsource
  have hcap : cap ≤ Z ^ Lbig := Real.rpow_le_rpow_of_exponent_le hZ'.le (by
    dsimp only [Lbig, tau]
    linarith)
  have hindices := hd Z cap hZ2 (Real.rpow_pos_of_pos hz0 _) hcap
  have hsource' : BoundedSource K S fdata Z Lbig (N - 3 * h) H za :=
    boundedSource_mono K S fdata hZ'.le (by dsimp only [Lbig]; linarith) hsource
  have hblocks (j : ℕ × ℕ) (hj : j ∈ TerminalRectangles.indices cap) :
      (∑ k ∈ rows, ‖block K S D fdata s (R.data θ) θ a W.toFun (Z ^ (N - 3 * h)) ps
        (TerminalRectangles.annulus K S cap j.1) (TerminalRectangles.annulus K S cap j.2) k‖ ^ 2) ≤
        CB * amp ^ 2 * qB ^ 2 * w ^ 2 * Z ^ (N + V - cstar / 4 - O / 2) := by
    let v := Real.logb Z (CubeCompletionBlocks.scale j.1)
    let ell := Real.logb Z (CubeCompletionBlocks.scale j.2)
    have hv : 0 ≤ v := Real.logb_nonneg hZ' (CubeCompletionBlocks.scale_one_le _)
    have hell : 0 ≤ ell := Real.logb_nonneg hZ' (CubeCompletionBlocks.scale_one_le _)
    have hretain : v + 3 * ell ≤ T + tau := TerminalRectangles.retained_lengths hZ' j hj
    have hvL : v ≤ Lbig := by dsimp only [Lbig, tau] at *; linarith
    have hellL : ell ≤ Lbig := by dsimp only [Lbig, tau] at *; linarith
    exact hb θ hθ (R.reflection θ hθ) P J f r hr u inactive haway s W
      Z N V M Q z d c cstar O H za v ell h tau amp hZB' hP hsource'
      hO hza hz hv hvL hell hellL hh hhd hamp hf hpr hM hQ hV hinv hcstar hc
      (by linarith) (le_refl _) (le_refl _) hretain hW rows ps
      (TerminalRectangles.annulus K S cap j.1) (TerminalRectangles.annulus K S cap j.2)
      a hrows hpower hrowsWindow hps
      (TerminalRectangles.annulus_window K S hZ' cap j.1)
      (TerminalRectangles.annulus_window K S hZ' cap j.2) ha
  have htail := ht θ hθ fdata s W Z (N - 3 * h) H za amp hZ' hsource hamp
    (fun cb => ¬TerminalRectangles.retained K S cap cb)
    (TerminalRectangles.omitted_large K S cap) rows ps a hrowsWindow hps ha
  have hsum (k : Ext) (hk : k ∈ rows) (p : Ext) (hp : p ∈ ps) :=
    TerminalSelectedTail.atom_summable K S D fdata s (R.data θ) θ (R.reflection θ hθ)
      W hZ' hsource k p (hrowsWindow k hk) (hps p hp)
  have hfull := fullSource_energy K S D fdata s (R.data θ) θ a W.toFun
    (Z ^ (N - 3 * h)) cap rows ps hsum
    (CB * amp ^ 2 * qB ^ 2 * w ^ 2 * Z ^ (N + V - cstar / 4 - O / 2))
    (CT * amp ^ 2 * qT ^ 2 * w ^ 2 * Z ^ (-saving)) (by positivity) hblocks htail
  have hqBb : qB ^ 2 ≤ (qB + qT) ^ 2 := by nlinarith
  have hqTb : qT ^ 2 ≤ (qB + qT) ^ 2 := by nlinarith
  have hblockBound : ((TerminalRectangles.indices cap).card : ℝ) ^ 2 *
      (CB * amp ^ 2 * qB ^ 2 * w ^ 2 * Z ^ (N + V - cstar / 4 - O / 2)) ≤
        (BD * CB) * amp ^ 2 * (qB + qT) ^ 2 * w ^ 2 *
          Z ^ (N + V - cstar / 8 - O / 2) := by
    calc
      _ ≤ (BD * Z ^ (cstar / 16)) *
          (CB * amp ^ 2 * (qB + qT) ^ 2 * w ^ 2 * Z ^ (N + V - cstar / 4 - O / 2)) := by
        gcongr
      _ = (BD * CB) * amp ^ 2 * (qB + qT) ^ 2 * w ^ 2 *
          Z ^ (cstar / 16 + (N + V - cstar / 4 - O / 2)) := by
        rw [Real.rpow_add hz0]
        ring
      _ ≤ _ := by gcongr <;> linarith
  have htailBound : CT * amp ^ 2 * qT ^ 2 * w ^ 2 * Z ^ (-saving) ≤
      CT * amp ^ 2 * (qB + qT) ^ 2 * w ^ 2 * Z ^ (N + V - cstar / 8 - O / 2) := by
    gcongr
    dsimp only [saving]
    linarith
  exact hfull.trans ((mul_le_mul_of_nonneg_left (add_le_add hblockBound htailBound)
    (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by dsimp only [qB, qT, w, fdata]; ring))

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalStateEnergy

end
