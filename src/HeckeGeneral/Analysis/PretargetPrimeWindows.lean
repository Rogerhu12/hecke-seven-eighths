import HeckeGeneral.Analysis.PhysicalProbeData
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Actual disjoint smooth prime windows can be chosen for any prescribed
positive even slot count, before selecting the field or target character.
No arithmetic ray filter or prime-density assertion is part of this lemma. -/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open Set Filter HeckeGeneral.ThetaSkeleton.Global
open scoped Topology ContDiff Classical

theorem exists_nonnegative_annular_test {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    ∃ W : SmoothAnnularTest,
      (∀ y, 0 ≤ (W.toFun y).re) ∧ (∀ y, (W.toFun y).im = 0) ∧
      (∃ y, W.toFun y ≠ 0) ∧ Function.support W.toFun ⊆ Ioo a b := by
  have hm : (a + b) / 2 ∈ Ioo a b := by constructor <;> linarith
  obtain ⟨f, hfs, _hfc, hfd, hfr, hf1⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (isOpen_Ioo.mem_nhds hm)
  have hsupport : Function.support (fun y => (f y : ℂ)) ⊆ Ioo a b := by
    intro y hy
    apply hfs
    apply subset_closure
    exact fun he => hy (by simp [he])
  let W : SmoothAnnularTest :=
    { toFun := fun y => (f y : ℂ)
      smooth := Complex.ofRealCLM.contDiff.comp hfd
      lower := a
      upper := b
      lower_pos := ha
      upper_ge := hab.le
      support := fun y hy => ⟨(hsupport hy).1.le, (hsupport hy).2.le⟩ }
  refine ⟨W, ?_, ?_, ?_, hsupport⟩
  · intro y
    exact (hfr ⟨y, rfl⟩).1
  · intro y
    exact Complex.ofReal_im _
  · exact ⟨(a + b) / 2, by change (f ((a + b) / 2) : ℂ) ≠ 0; rw [hf1]; norm_num⟩

theorem exists_primeWindowGeometry_slots (J : ℕ) (hJ : 0 < J) (heven : Even J) :
    ∃ g : PrimeWindowGeometry, g.slots = J := by
  let d : ℝ := 2 * J + 1
  have hd : 0 < d := by dsimp [d]; positivity
  let a : Fin J → ℝ := fun i => 1 + (2 * i.val + 1) / d
  let b : Fin J → ℝ := fun i => 1 + (2 * i.val + 2) / d
  have hai (i : Fin J) : 1 < a i := by
    have hn : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
    dsimp [a]
    exact lt_add_of_pos_right _ (div_pos (by linarith) hd)
  have hab (i : Fin J) : a i < b i := by
    have hnum : 2 * (i.val : ℝ) + 1 < 2 * (i.val : ℝ) + 2 := by linarith
    have hdiv : (2 * (i.val : ℝ) + 1) / d < (2 * (i.val : ℝ) + 2) / d :=
      (div_lt_div_iff_of_pos_right hd).mpr hnum
    dsimp [a, b]
    linarith
  have hbi (i : Fin J) : b i < 2 := by
    have hi : (i.val : ℝ) + 1 ≤ J := by exact_mod_cast Nat.succ_le_of_lt i.isLt
    have hn : 2 * (i.val : ℝ) + 2 < d := by dsimp [d]; linarith
    have hh := (div_lt_one hd).mpr hn
    dsimp [b]
    linarith
  have hw (i : Fin J) := exists_nonnegative_annular_test
    (lt_trans zero_lt_one (hai i)) (hab i)
  choose W hnonneg hreal hnonzero hsupp using hw
  refine ⟨{ slots := J
            slots_pos := hJ
            slots_even := heven
            weight := W
            nonnegative := hnonneg
            real_valued := hreal
            nonzero := hnonzero
            support_annular := ?_
            disjoint := ?_ }, rfl⟩
  · intro i y hy
    exact ⟨(hai i).trans (hsupp i hy).1, (hsupp i hy).2.trans (hbi i)⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro y hyi hyj
    have hi := hsupp i hyi
    have hj := hsupp j hyj
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hne with hij' | hji'
    · have hn : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast Nat.succ_le_of_lt hij'
      have hba : b i ≤ a j := by
        have hnum : 2 * (i.val : ℝ) + 2 ≤ 2 * (j.val : ℝ) + 1 := by linarith
        have hdiv : (2 * (i.val : ℝ) + 2) / d ≤ (2 * (j.val : ℝ) + 1) / d :=
          (div_le_div_iff_of_pos_right hd).mpr hnum
        dsimp [a, b]
        linarith
      exact (not_lt_of_ge hba) (hj.1.trans hi.2)
    · have hn : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast Nat.succ_le_of_lt hji'
      have hba : b j ≤ a i := by
        have hnum : 2 * (j.val : ℝ) + 2 ≤ 2 * (i.val : ℝ) + 1 := by linarith
        have hdiv : (2 * (j.val : ℝ) + 2) / d ≤ (2 * (i.val : ℝ) + 1) / d :=
          (div_le_div_iff_of_pos_right hd).mpr hnum
        dsimp [a, b]
        linarith
      exact (not_lt_of_ge hba) (hi.1.trans hj.2)

/-- The source width 2 ell/J with ell=1/6 is arbitrarily small with an
even number of genuinely disjoint, nonnegative, nonzero smooth windows. -/
theorem exists_primeWindowGeometry_fine {η : ℝ} (hη : 0 < η) :
    ∃ g : PrimeWindowGeometry, 2 * (1 / 6 : ℝ) / g.slots < η := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 ((1 / 3 : ℝ) / η))
  have hn1 : (1 : ℝ) < n := (le_max_left _ _).trans_lt hn
  have hn0 : 0 < n := by exact_mod_cast (lt_trans zero_lt_one hn1)
  have hnη : (1 / 3 : ℝ) / η < n := (le_max_right _ _).trans_lt hn
  have hnη' : (1 / 3 : ℝ) < n * η := (div_lt_iff₀ hη).mp hnη
  obtain ⟨g, hg⟩ := exists_primeWindowGeometry_slots (2 * n) (by omega) (even_two_mul n)
  refine ⟨g, ?_⟩
  rw [hg, Nat.cast_mul, Nat.cast_ofNat]
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
  nlinarith

end HeckeGeneral.ThetaSkeleton.Physical
