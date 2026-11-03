import HeckeGeneral.Analysis.ActualSIntegerSobolevRegularity
import HeckeGeneral.Analysis.RowwiseBoxSobolev
import Mathlib.Analysis.Normed.Group.Bounded

/-! Consumption of the explicit finite-test moment on genuine quotient rows.
The target is fixed here: S and root/embedding data may depend on eta.
The packet wrapper at the end is only a fixed-S specialization. -/

noncomputable section

namespace HeckeGeneral.Analysis.ActualSIntegerMoments

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis.SquarefreeAmplification
open scoped BigOperators Classical Topology

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)

def actualSixTestFamily (η : HeckeCharacter K) (q : ActualSIntegerOrbit K S) : SixTestFamily :=
  fun i m x y z => if i.val = 0 then
    actualLogTestLogPolynomial K S ζ hζ σ η q m.val (x, (y : ℂ) + (z : ℂ) * Complex.I)
  else actualEulerLogTestLogPolynomial K S ζ hζ σ η q m.val
    (x, (y : ℂ) + (z : ℂ) * Complex.I)

theorem actualSixTestFamily_eq (η : HeckeCharacter K) (q : ActualSIntegerOrbit K S)
    (i : Fin 2) (m : Fin 3) (x y z : ℝ) :
    actualSixTestFamily K S ζ hζ σ η q i m x y z =
      sIntegerSexticInverseIdealPolynomial K S ζ hζ σ η
        (dyadicIdealSupport K (Real.exp x)) q.out.val (Real.exp x)
        (scaleSobolevTest i m ((y : ℂ) + (z : ℂ) * Complex.I)) := by
  unfold actualSixTestFamily scaleSobolevTest
  split_ifs <;> rfl

theorem continuous_actualSixTestFamily (η : HeckeCharacter K)
    (q : ActualSIntegerOrbit K S) (i : Fin 2) (m : Fin 3) :
    Continuous (fun p : ℝ × ℝ × ℝ => actualSixTestFamily K S ζ hζ σ η q i m p.1 p.2.1 p.2.2) := by
  have hmap : Continuous (fun p : ℝ × ℝ × ℝ =>
      (p.1, (p.2.1 : ℂ) + (p.2.2 : ℂ) * Complex.I)) :=
    continuous_fst.prodMk ((Complex.continuous_ofReal.comp continuous_snd.fst).add
      ((Complex.continuous_ofReal.comp continuous_snd.snd).mul continuous_const))
  unfold actualSixTestFamily
  split_ifs
  · exact (contDiff_actualLogTestLogPolynomial K S ζ hζ σ η q m.val).continuous.comp hmap
  · exact (continuous_actualEulerLogTestLogPolynomial K S ζ hζ σ η q m.val).comp hmap

theorem hasDerivAt_actualSixTestFamily_scale (η : HeckeCharacter K)
    (q : ActualSIntegerOrbit K S) (m : Fin 3) (x y z : ℝ) :
    HasDerivAt (fun u => actualSixTestFamily K S ζ hζ σ η q 0 m u y z)
      (actualSixTestFamily K S ζ hζ σ η q 1 m x y z) x := by
  simpa [actualSixTestFamily] using
    hasDerivAt_actualLogTestLogPolynomial_scale K S ζ hζ σ η q m.val x
      ((y : ℂ) + (z : ℂ) * Complex.I)

theorem hasDerivAt_actualSixTestFamily_real (η : HeckeCharacter K)
    (q : ActualSIntegerOrbit K S) (m : Fin 2) (x y z : ℝ) :
    HasDerivAt
      (fun v => actualSixTestFamily K S ζ hζ σ η q 0 ⟨m.val, by omega⟩ x v z)
      (actualSixTestFamily K S ζ hζ σ η q 0 ⟨m.val + 1, by omega⟩ x y z) y := by
  have hp : HasDerivAt (fun v : ℝ => (v : ℂ) + (z : ℂ) * Complex.I) 1 y :=
    (hasDerivAt_id y).ofReal_comp.add_const _
  simpa [actualSixTestFamily, Function.comp_def, smul_eq_mul] using
    (hasDerivAt_actualLogTestLogPolynomial_parameter K S ζ hζ σ η q m.val x
      ((y : ℂ) + (z : ℂ) * Complex.I)).scomp y hp

theorem hasDerivAt_actualSixTestFamily_imaginary (η : HeckeCharacter K)
    (q : ActualSIntegerOrbit K S) (x y z : ℝ) :
    HasDerivAt (fun w => actualSixTestFamily K S ζ hζ σ η q 0 0 x y w)
      (Complex.I * actualSixTestFamily K S ζ hζ σ η q 0 1 x y z) z := by
  have hp : HasDerivAt (fun w : ℝ => (y : ℂ) + (w : ℂ) * Complex.I) Complex.I z := by
    simpa using ((hasDerivAt_id z).ofReal_comp.mul_const Complex.I).const_add (y : ℂ)
  simpa [actualSixTestFamily, Function.comp_def, smul_eq_mul] using
    (hasDerivAt_actualLogTestLogPolynomial_parameter K S ζ hζ σ η q 0 x
      ((y : ℂ) + (z : ℂ) * Complex.I)).scomp z hp

theorem actualSIntegerInversePolynomial_zero_of_small_scale
    (η : HeckeCharacter K) (q : ActualSIntegerOrbit K S) (s : ℂ)
    {D : ℝ} (hD : 0 < D) (hsmall : D ≤ 1 / 2) :
    actualSIntegerInversePolynomial K S ζ hζ σ η q D s = 0 := by
  rw [← actualSIntegerInversePolynomial_out]
  have ht (I : NonzeroIdeal K) : sIntegerSexticInverseIdealTerm K S ζ hζ σ η
      q.out.val D (dyadicMellinWeight s) I = 0 := by
    have hy : 2 ≤ idealNorm K I / D := (le_div_iff₀ hD).mpr
      (by linarith [one_le_idealNorm K I])
    simp [sIntegerSexticInverseIdealTerm, dyadicMellinWeight_zero_of_ge s hy]
  simp [sIntegerSexticInverseIdealPolynomial, ht]

omit K S ζ hζ σ in
theorem log_scale_length_le_rpow {δ ε H : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε) (hH : 1 ≤ H) :
    1 + (1 - δ) * Real.log H - Real.log (1 / 2) ≤
      (1 - Real.log (1 / 2) + 2 / ε) * H ^ (ε / 2) := by
  have hu : 0 < ε / 2 := by linarith
  have hp : 1 ≤ H ^ (ε / 2) := Real.one_le_rpow hH hu.le
  have hl := Real.log_le_rpow_div (by linarith : 0 ≤ H) hu
  have hn : 0 ≤ Real.log H := Real.log_nonneg hH
  have ha : Real.log (1 / 2) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have hi : (ε / 2)⁻¹ = 2 / ε := by field_simp
  rw [div_eq_mul_inv, hi] at hl
  nlinarith [mul_nonneg hδ hn,
    mul_nonneg (show 0 ≤ 1 - Real.log (1 / 2) by linarith) (sub_nonneg.mpr hp)]

def ActualTargetZeroSlotScaleSupInput (η : HeckeCharacter K) : Prop :=
  ∀ δ ε : ℝ, 0 < δ → δ < 1 → 0 < ε →
    ∀ T : Set ℂ, IsCompact T →
      ∃ C H₀ : ℝ, 0 < C ∧ 1 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H →
        ∃ B : ActualSIntegerOrbit K S → ℝ, (∀ q, 0 ≤ B q) ∧
          (∀ q, actualSIntegerOrbitNorm K S q ≤ H →
            ∀ D : ℝ, 0 < D → D ≤ H ^ (1 - δ) → ∀ s ∈ T,
              ‖actualSIntegerInversePolynomial K S ζ hζ σ η q D s‖ ^ 2 ≤ B q) ∧
          (∑ q : ActualBoundedSIntegerOrbits K S H, B q.val) ≤ C * H ^ (1 + ε)

theorem ActualTargetZeroSlotSobolevMomentInput.to_scaleSup
    (η : HeckeCharacter K) (h : ActualTargetZeroSlotSobolevMomentInput K S ζ hζ σ η) :
    ActualTargetZeroSlotScaleSupInput K S ζ hζ σ η := by
  intro δ ε hδ hδ1 hε T hT
  obtain ⟨R, hR, hRT⟩ := hT.isBounded.exists_pos_norm_le
  let T' : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
    (Set.Icc (-R) R ×ˢ Set.Icc (-R) R)
  have hT' : IsCompact T' := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  obtain ⟨C, H₀, hC, hH₀, hbound⟩ := h δ (ε / 2) hδ hδ1 (by linarith) T' hT'
  let L : ℝ := 1 - Real.log (1 / 2) + 2 / ε
  let C' : ℝ := (1 + 2 * R) * ((1 + 2 * R) * (8 * C * L))
  have hL : 0 < L := by
    dsimp [L]
    have ha : Real.log (1 / 2) < 0 := Real.log_neg (by norm_num) (by norm_num)
    exact add_pos (by linarith) (div_pos (by norm_num) hε)
  refine ⟨C', H₀, by dsimp [C']; positivity, hH₀, ?_⟩
  intro H hH
  have hH1 : 1 ≤ H := hH₀.trans hH
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH1
  let a : ℝ := Real.log (1 / 2)
  let b : ℝ := (1 - δ) * Real.log H
  have hab : a ≤ b := by
    have ha : a < 0 := Real.log_neg (by norm_num) (by norm_num)
    have hb : 0 ≤ b := mul_nonneg (by linarith) (Real.log_nonneg hH1)
    linarith
  have hRle : -R ≤ R := by linarith
  obtain ⟨B₀, hB₀, hrow, hsum⟩ := exists_sixTest_box_majorants
    (Finset.univ : Finset (ActualBoundedSIntegerOrbits K S H))
    (fun q => actualSixTestFamily K S ζ hζ σ η q.val)
    (fun q i m => continuous_actualSixTestFamily K S ζ hζ σ η q.val i m)
    (fun q m x y z => hasDerivAt_actualSixTestFamily_scale K S ζ hζ σ η q.val m x y z)
    (fun q x y z => hasDerivAt_actualSixTestFamily_real K S ζ hζ σ η q.val 0 x y z)
    (fun q x y z => hasDerivAt_actualSixTestFamily_real K S ζ hζ σ η q.val 1 x y z)
    (fun q x y z => hasDerivAt_actualSixTestFamily_imaginary K S ζ hζ σ η q.val x y z)
    hab hRle hRle (C * H ^ (1 + ε / 2)) (by
      intro i m x hx y hy z hz
      have hscale : Real.exp x ≤ H ^ (1 - δ) := by
        rw [Real.rpow_def_of_pos hHpos]
        apply Real.exp_le_exp.mpr
        dsimp [b] at hx
        nlinarith [hx.2]
      have hs : (y : ℂ) + (z : ℂ) * Complex.I ∈ T' :=
        ⟨(y, z), ⟨hy, hz⟩, rfl⟩
      simpa only [actualSixTestFamily_eq] using
        hbound H hH (Real.exp x) (Real.exp_pos x) hscale
          ((y : ℂ) + (z : ℂ) * Complex.I) hs i m)
  let B : ActualSIntegerOrbit K S → ℝ := fun q =>
    if hq : actualSIntegerOrbitNorm K S q ≤ H then B₀ ⟨q, hq⟩ else 0
  refine ⟨B, ?_, ?_, ?_⟩
  · intro q
    dsimp [B]
    split_ifs
    · exact hB₀ _
    · exact le_rfl
  · intro q hq D hD hscale s hs
    dsimp [B]
    rw [dite_eq_left hq]
    by_cases hsmall : D ≤ 1 / 2
    · rw [actualSIntegerInversePolynomial_zero_of_small_scale K S ζ hζ σ η q s hD hsmall]
      simpa using hB₀ ⟨q, hq⟩
    · have hx : Real.log D ∈ Set.Icc a b := by
        constructor
        · exact Real.log_le_log (by norm_num) (lt_of_not_ge hsmall).le
        · have hl := Real.log_le_log hD hscale
          rw [Real.log_rpow hHpos] at hl
          exact hl
      have hy : s.re ∈ Set.Icc (-R) R := abs_le.mp
        ((Complex.abs_re_le_norm s).trans (hRT s hs))
      have hz : s.im ∈ Set.Icc (-R) R := abs_le.mp
        ((Complex.abs_im_le_norm s).trans (hRT s hs))
      have hh := hrow ⟨q, hq⟩ (Real.log D) hx s.re hy s.im hz
      simpa [actualSixTestFamily,
        actualLogTestLogPolynomial, Real.exp_log hD, mellinLogTest_zero_index,
        Complex.re_add_im, actualSIntegerInversePolynomial_out] using hh
  · have hBsum : (∑ q : ActualBoundedSIntegerOrbits K S H, B q.val) = ∑ q, B₀ q := by
      apply Finset.sum_congr rfl
      intro q _
      exact dite_eq_left q.property
    rw [hBsum]
    apply hsum.trans
    have hlen := log_scale_length_le_rpow hδ.le hε hH1
    change 1 + b - a ≤ L * H ^ (ε / 2) at hlen
    have hp : H ^ (ε / 2) * H ^ (1 + ε / 2) = H ^ (1 + ε) := by
      rw [← Real.rpow_add hHpos]
      congr 1
      ring
    calc
      (1 + R - -R) * ((1 + R - -R) * ((1 + b - a) * (8 * (C * H ^ (1 + ε / 2))))) ≤
          (1 + R - -R) * ((1 + R - -R) * ((L * H ^ (ε / 2)) *
            (8 * (C * H ^ (1 + ε / 2))))) := by gcongr <;> linarith
      _ = C' * (H ^ (ε / 2) * H ^ (1 + ε / 2)) := by dsimp [C']; ring
      _ = C' * H ^ (1 + ε) := by rw [hp]

theorem ActualZeroSlotSobolevMomentInput.to_scaleSup
    (ω : HeckeCharacter K) (h : ActualZeroSlotSobolevMomentInput K S ζ hζ σ ω) :
    ActualZeroSlotScaleSupInput K S ζ hζ σ ω := by
  intro δ ε hδ hδ1 hε T hT η hη
  exact (h.target K S ζ hζ σ ω η hη).to_scaleSup K S ζ hζ σ η
    δ ε hδ hδ1 hε T hT

end HeckeGeneral.Analysis.ActualSIntegerMoments
