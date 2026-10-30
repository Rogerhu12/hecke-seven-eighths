import HeckeSkeleton.HeckeHighRowLRatio
import HeckeSkeleton.HeckeDeletedEulerControl
import HeckeSkeleton.HeckeLRatioConductorBudget
import ActualCanonicalRowConsumers
/-!
An actual high-row L-ratio estimate on the complete horizontal s-strip.
This strengthens the supplied final-line theorem: only the denominator's
real-part premise changes from equality to a closed interval. Its proof
uses the existing buffered reciprocal theorem and the actual functional
equation, not a contour-shift or high-bin conclusion.

Project-dependent module: verification requires the supplied project imports.
-/

set_option autoImplicit false
noncomputable section

namespace HighBinBoundary.ActualLRatioStrip

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Bridge HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.ExplicitHeckeFunctionalEquation HeckeSkeleton.HeckeGammaReciprocal
open HeckeSkeleton.HeckeBufferedReciprocal
open HeckeSkeleton.HeckePhysicalFamilyBufferedControl HeckeSkeleton.HeckeDynamicGammaBound
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

set_option maxHeartbeats 1000000 in
/-- The same constant and cutoff work simultaneously for every
`a + 16e ≤ Re(s) ≤ 2`. In particular they cover all horizontal faces
between the final line and `B + 20e`, once `B ≤ 1` and `e ≤ 1/10000`. -/
theorem exists_uniform_high_row_LRatio_strip_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K)) (hΘ : 1 ∈ Θ)
    (P : ProbeData K S) (E : RowEulerData K S P)
    {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000)
    (hesmall : e ≤ 1 / 10000) (hε : 0 < ε) :
    ∃ C Z₀ : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → ∀ u : FrequencyRow K S,
      Z ^ d ≤ frequencyRowNorm K S u → ∀ a H Hupper : ℝ,
      51 / 100 ≤ a → a ≤ 1 → 0 ≤ H → H + 3 / 2 ≤ Hupper →
      rowZeroBelow K S ψ Θ P E u Hupper (a + 2 * e) →
      ∀ s w : ℂ, a + 16 * e ≤ s.re → s.re ≤ 2 →
        w.re = 1 - a - 6 * e →
      |s.im| ≤ H → |w.im| ≤ H →
        ‖heckeContinuation K (E.rows.character u) w‖ *
          ‖(heckeContinuation K (ψ * conjugate (E.rows.character u)) s)⁻¹‖ ≤
            C * heckeConductorScale K (E.rows.character u) ^ (a - 1 / 2 + 6 * e) *
              heckeConductorScale K ((E.rows.character u)⁻¹) ^ ε *
              heckeConductorScale K (ψ * conjugate (E.rows.character u)) ^ ε *
              (2 + Hupper) ^
                (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) +
                  2 * ((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * ε) := by
  have hFib := HeckeSkeleton.ActualCanonicalRowConsumers.rowCharacter_fiber_finite K S P E
  let v : InfinitePlace K := Classical.choice inferInstance
  obtain ⟨D, Z₁, hD, hZ₁, hbuffer⟩ := exists_uniform_high_physicalFamily_buffered_control
    K S hcomplex ψ Θ P E hFib v he he' hε
  obtain ⟨G, hG, hGamma⟩ := exists_uniform_finiteOrder_reflectedGamma_bound K hcomplex
  obtain ⟨Z₂, hZ₂, hnon⟩ :=
    HeckeSkeleton.HighNormBackgroundExclusion.high_rows_exclude_background_norm_twists
      K S P E.rows hFib v ({1} : Finset (HeckeCharacter K))
  let k : ℕ := 2 * Fintype.card (InfinitePlace K)
  refine ⟨G * D ^ 2, max Z₁ Z₂, by positivity,
    hZ₁.trans (le_max_left _ _), ?_⟩
  intro Z hZ d hd u hu a H Hupper ha ha' hH hpadding hbelow s w hs hsupper hw hsi hwi
  have hZZ₁ : Z₁ ≤ Z := (le_max_left _ _).trans hZ
  have hZZ₂ : Z₂ ≤ Z := (le_max_right _ _).trans hZ
  let χ := E.rows.character u
  let β := ψ * conjugate χ
  have hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t := by
    simpa only [one_mul] using
      (hnon Z hZZ₂ d hd u hu 1 (Finset.mem_singleton_self 1)).1
  have hχbar : conjugate χ ∈ physicalRowFamily K S ψ Θ P E u := by
    apply Finset.mem_biUnion.mpr
    refine ⟨1, hΘ, ?_⟩
    simp only [one_mul, Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr (Or.inl rfl)
  have hβ : β ∈ physicalRowFamily K S ψ Θ P E u :=
    denominator_mem_physicalRowFamily K S ψ Θ P E u hΘ
  have hb := hbuffer Z hZZ₁ d hd u hu a H Hupper (by linarith) ha' hH hpadding hbelow
  have hbdual := hb (conjugate χ) hχbar (1 - w)
    (by simp only [Complex.sub_re, Complex.one_re, hw]; linarith)
    (by simp only [Complex.sub_re, Complex.one_re, hw]; linarith)
    (by simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using hwi)
  have hbden := hb β hβ s (by linarith) hsupper hsi
  have hdual : ‖heckeContinuation K χ⁻¹ (1 - w)‖ ≤
      D * heckeConductorScale K χ⁻¹ ^ ε *
        (2 + Hupper) ^ ((k : ℝ) * ε) := by
    have h := (le_add_of_nonneg_right
      (norm_nonneg ((heckeContinuation K (conjugate χ) (1 - w))⁻¹))).trans hbdual
    simpa only [conjugate] using h
  have hden : ‖(heckeContinuation K β s)⁻¹‖ ≤
      D * heckeConductorScale K β ^ ε * (2 + Hupper) ^ ((k : ℝ) * ε) := by
    exact (le_add_of_nonneg_left (norm_nonneg (heckeContinuation K β s))).trans hbden
  have hHU : 0 ≤ Hupper := by linarith
  have hT : 0 < 2 + Hupper := by linarith
  have hQβ : 0 ≤ heckeConductorScale K β := by unfold heckeConductorScale; positivity
  have hQdual : 0 ≤ heckeConductorScale K χ⁻¹ := by unfold heckeConductorScale; positivity
  have hGammab : ‖(canonicalHeckeGammaProfile K χ w)⁻¹ *
      canonicalHeckeGammaProfile K χ⁻¹ (1 - w)‖ ≤ G * (2 + Hupper) ^ k := by
    have hg := hGamma χ (E.rows.finite_order u) w ⟨by linarith, by linarith⟩
    apply hg.trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith) k) hG.le
  obtain ⟨root, hroot, hQ, hFE⟩ := exists_uncompleted_functionalEquation_left_of_one K χ hχ
  have hre : (w - 1 / 2).re = -(a - 1 / 2 + 6 * e) := by simp [hw]; ring
  have hnorm : ‖heckeContinuation K χ w‖ =
      (‖(canonicalHeckeGammaProfile K χ w)⁻¹ *
          canonicalHeckeGammaProfile K χ⁻¹ (1 - w)‖ *
        ‖heckeContinuation K χ⁻¹ (1 - w)‖) *
          heckeConductorScale K χ ^ (a - 1 / 2 + 6 * e) := by
    rw [hFE w (by linarith), norm_div, norm_mul, norm_mul root, hroot, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hQ, hre, Real.rpow_neg hQ.le, div_inv_eq_mul]
  have hheight : (2 + Hupper) ^ k * (2 + Hupper) ^ ((k : ℝ) * ε) *
      (2 + Hupper) ^ ((k : ℝ) * ε) =
        (2 + Hupper) ^ ((k : ℝ) + 2 * (k : ℝ) * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hT, ← Real.rpow_add hT]
    congr 1
    ring
  change ‖heckeContinuation K χ w‖ * ‖(heckeContinuation K β s)⁻¹‖ ≤ _
  rw [hnorm]
  calc
    _ ≤ (((G * (2 + Hupper) ^ k) *
          (D * heckeConductorScale K χ⁻¹ ^ ε * (2 + Hupper) ^ ((k : ℝ) * ε))) *
            heckeConductorScale K χ ^ (a - 1 / 2 + 6 * e)) *
          (D * heckeConductorScale K β ^ ε * (2 + Hupper) ^ ((k : ℝ) * ε)) := by
      apply mul_le_mul _ hden (norm_nonneg _) (by positivity)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hQ.le _)
      exact mul_le_mul hGammab hdual (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [← hheight]
      ring


/-- Numerical coverage of the actual initial-to-final strip, including B=1. -/
theorem actual_strip_endpoints {a B e : ℝ}
    (haB : a ≤ B) (hB : B ≤ 1) (he : 0 ≤ e) (hesmall : e ≤ 1 / 10000) :
    a + 16 * e ≤ B + 20 * e ∧ B + 20 * e ≤ 2 := by
  constructor <;> linarith


/-- The literal fixed-S deleted ratio on the complete swept strip. The
finite deletion constants are uniform in the actual row and both heights;
the numerator polynomial is allowed to vanish on or left of Re(w)=0. -/
theorem exists_uniform_high_row_deletedLRatio_strip_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K)) (hΘ : 1 ∈ Θ)
    (P : ProbeData K S) (E : RowEulerData K S P)
    {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000)
    (hesmall : e ≤ 1 / 10000) (hε : 0 < ε) :
    ∃ C Z₀ : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → ∀ u : FrequencyRow K S,
      Z ^ d ≤ frequencyRowNorm K S u → ∀ a H Hupper : ℝ,
      51 / 100 ≤ a → a ≤ 1 → 0 ≤ H → H + 3 / 2 ≤ Hupper →
      rowZeroBelow K S ψ Θ P E u Hupper (a + 2 * e) →
      ∀ s w : ℂ, a + 16 * e ≤ s.re → s.re ≤ 2 →
        w.re = 1 - a - 6 * e → |s.im| ≤ H → |w.im| ≤ H →
        ‖heckeDeletedContinuation K (E.rows.character u) (exceptionalPrimes K S) w‖ *
          ‖(heckeDeletedContinuation K (ψ * conjugate (E.rows.character u))
            (exceptionalPrimes K S) s)⁻¹‖ ≤
            C * heckeConductorScale K (E.rows.character u) ^ (a - 1 / 2 + 6 * e) *
              heckeConductorScale K ((E.rows.character u)⁻¹) ^ ε *
              heckeConductorScale K (ψ * conjugate (E.rows.character u)) ^ ε *
              (2 + Hupper) ^
                (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) +
                  2 * ((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * ε) := by
  obtain ⟨C, Z₀, hC, hZ₀, hb⟩ := exists_uniform_high_row_LRatio_strip_bound
    K S hcomplex ψ Θ hΘ P E he he' hesmall hε
  obtain ⟨D, hD, hdel⟩ :=
    HeckeSkeleton.HeckeDeletedEulerControl.exists_uniform_deletedL_ratio_transfer
      K (exceptionalPrimes K S)
  refine ⟨D * C, Z₀, mul_pos hD hC, hZ₀, ?_⟩
  intro Z hZ d hd u hu a H Hupper ha ha1 hH hHU hbelow s w hs hs2 hw hsi hwi
  have hbase := hb Z hZ d hd u hu a H Hupper ha ha1 hH hHU hbelow
    s w hs hs2 hw hsi hwi
  have hdelete := hdel (E.rows.character u) (ψ * conjugate (E.rows.character u))
    w s ⟨by linarith, by linarith⟩ (by linarith)
  exact hdelete.trans (by
    convert mul_le_mul_of_nonneg_left hbase hD.le using 1 <;> ring)


/-- The literal deleted zeta factor occurring in rowEulerContinuation is
uniformly bounded at all heights of the z=17/50 line. The bound comes from
the actual absolutely convergent Euler logarithm and the fixed deletions. -/
theorem exists_uniform_deleted_zeta_six_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, (17 / 50 : ℝ) ≤ z.re →
      ‖heckeDeletedContinuation K 1 (exceptionalPrimes K S) (6 * z)‖ ≤ C := by
  obtain ⟨A, hA, hlog⟩ :=
    HeckeSkeleton.ActualEulerLogarithm.exists_uniform_heckeEulerLog_bound K
  let D := HeckeSkeleton.HeckeDeletedEulerControl.deletionUpperConstant
    K (exceptionalPrimes K S)
  have hD : 0 < D :=
    HeckeSkeleton.HeckeDeletedEulerControl.deletionUpperConstant_pos
      K (exceptionalPrimes K S)
  refine ⟨D * Real.exp A, mul_pos hD (Real.exp_pos A), ?_⟩
  intro z hz
  have hs : (151 / 100 : ℝ) ≤ (6 * z).re := by
    norm_num [Complex.mul_re]
    linarith
  have hL : ‖heckeContinuation K 1 (6 * z)‖ ≤ Real.exp A := by
    rw [← HeckeSkeleton.ActualEulerLogarithm.exp_heckeEulerLog_eq_continuation
      K 1 (6 * z) (by linarith), Complex.norm_exp]
    exact Real.exp_le_exp.mpr
      ((Complex.re_le_norm _).trans (hlog 1 (6 * z) hs))
  unfold heckeDeletedContinuation
  rw [norm_mul]
  exact mul_le_mul
    (HeckeSkeleton.HeckeDeletedEulerControl.norm_heckeEulerDeletionPolynomial_le
      K (exceptionalPrimes K S) 1 (6 * z) (by linarith))
    hL (norm_nonneg _) hD.le

/-- A fixed height degree for coarse horizontal-face estimates. It is
chosen before the external tail order and before every row or scale. -/
def boundaryHeightDegree : ℕ := 6 * Fintype.card (InfinitePlace K)

/-- The actual finite conductor is bounded by the actual row norm. This
uses whole-character uniqueness and the ideal-theoretic radical bound,
including every sixth-unit sector. -/
theorem exists_uniform_actual_row_conductor_norm_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (P : ProbeData K S) (E : RowEulerData K S P)
      (u : FrequencyRow K S),
      heckeConductorScale K (E.rows.character u) ≤ A * frequencyRowNorm K S u := by
  obtain ⟨C, hC, hbound⟩ :=
    HeckeSkeleton.ActualCanonicalRowConsumers.exists_fixed_real_radical_bound_constant K S
  let A : ℝ := max 1 (((NumberField.discr K).natAbs : ℝ) * C)
  refine ⟨A, le_max_left _ _, ?_⟩
  intro P E u
  have hrad : (u.ideal.val.val.radical.absNorm : ℝ) ≤ frequencyRowNorm K S u := by
    have hnat := Nat.le_of_dvd (Ideal.absNorm_pos_of_nonZeroDivisors u.ideal.val)
      (Ideal.absNorm_dvd_absNorm_of_le
        (Ideal.le_radical : u.ideal.val.val ≤ u.ideal.val.val.radical))
    exact_mod_cast hnat
  calc
    heckeConductorScale K (E.rows.character u) ≤
        ((NumberField.discr K).natAbs : ℝ) *
          (C * (u.ideal.val.val.radical.absNorm : ℝ)) :=
      mul_le_mul_of_nonneg_left (hbound P E u) (Nat.cast_nonneg _)
    _ ≤ ((NumberField.discr K).natAbs : ℝ) * (C * frequencyRowNorm K S u) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrad hC.le)
        (Nat.cast_nonneg _)
    _ = (((NumberField.discr K).natAbs : ℝ) * C) * frequencyRowNorm K S u := by ring
    _ ≤ A * frequencyRowNorm K S u :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (idealNorm_pos K u.ideal.val).le

/-- A completely arithmetic polynomial envelope for the actual deleted
L-ratio on all horizontal faces. The conductor and the totally-complex
field property are conclusions of the original ProbeData; neither is an
extra hypothesis. The coarse row exponent 3 and the height degree are
fixed before the external decay order. -/
theorem exists_uniform_high_row_deletedLRatio_norm_bound
    (ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K)) (hΘ : 1 ∈ Θ)
    (P : ProbeData K S) (E : RowEulerData K S P)
    {e : ℝ} (he : 0 < e) (hesmall : e ≤ 1 / 10000) :
    ∃ C Z₀ : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → ∀ u : FrequencyRow K S,
      Z ^ d ≤ frequencyRowNorm K S u → ∀ a H Hupper : ℝ,
      51 / 100 ≤ a → a ≤ 1 → 0 ≤ H → H + 3 / 2 ≤ Hupper →
      rowZeroBelow K S ψ Θ P E u Hupper (a + 2 * e) →
      ∀ s w : ℂ, a + 16 * e ≤ s.re → s.re ≤ 2 →
        w.re = 1 - a - 6 * e → |s.im| ≤ H → |w.im| ≤ H →
        ‖heckeDeletedContinuation K (E.rows.character u) (exceptionalPrimes K S) w‖ *
          ‖(heckeDeletedContinuation K (ψ * conjugate (E.rows.character u))
            (exceptionalPrimes K S) s)⁻¹‖ ≤
          C * frequencyRowNorm K S u ^ 3 * (2 + Hupper) ^ boundaryHeightDegree K := by
  obtain ⟨C, Z₀, hC, hZ₀, hb⟩ := exists_uniform_high_row_deletedLRatio_strip_bound
    K S (HeckeSkeleton.HeckeFiniteBackgroundControl.all_complex_of_primitive12
      K P.arithmetic.primitive12) ψ Θ hΘ P E (ε := 1) he (by linarith) hesmall (by norm_num)
  obtain ⟨A, hA, hAQ⟩ := exists_uniform_actual_row_conductor_norm_bound K S
  let D := HeckeSkeleton.HeckeLRatioConductorBudget.backgroundConductorBudget K ψ A 1
  have hD : 0 < D :=
    HeckeSkeleton.HeckeLRatioConductorBudget.backgroundConductorBudget_pos K ψ A 1 hA
  refine ⟨C * D, Z₀, mul_pos hC hD, hZ₀, ?_⟩
  intro Z hZ d hd u hu a H Hupper ha ha1 hH hHU hbelow s w hs hs2 hw hsi hwi
  have hNu : 1 ≤ frequencyRowNorm K S u := one_le_idealNorm K u.ideal.val
  have hlam : 0 ≤ a - 1 / 2 + 6 * e := by linarith
  have hlam1 : a - 1 / 2 + 6 * e ≤ 1 := by linarith
  have hprod := HeckeSkeleton.HeckeLRatioConductorBudget.conductorPowers_le_radicalPower
    K ψ (E.rows.character u) A (frequencyRowNorm K S u) (a - 1 / 2 + 6 * e) 1
    hA hNu hlam hlam1 (by norm_num) (hAQ P E u)
  have hprod3 :
      heckeConductorScale K (E.rows.character u) ^ (a - 1 / 2 + 6 * e) *
        heckeConductorScale K ((E.rows.character u)⁻¹) ^ (1 : ℝ) *
        heckeConductorScale K (ψ * conjugate (E.rows.character u)) ^ (1 : ℝ) ≤
      D * frequencyRowNorm K S u ^ 3 := by
    apply hprod.trans
    apply mul_le_mul_of_nonneg_left _ hD.le
    calc
      frequencyRowNorm K S u ^ ((a - 1 / 2 + 6 * e) + 2 * 1) ≤
          frequencyRowNorm K S u ^ (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hNu (by linarith)
      _ = _ := Real.rpow_natCast _ _
  have hbase := hb Z hZ d hd u hu a H Hupper ha ha1 hH hHU hbelow
    s w hs hs2 hw hsi hwi
  have hdegree :
      (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) +
        2 * ((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * 1) =
        (boundaryHeightDegree K : ℝ) := by
    simp only [boundaryHeightDegree, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [hdegree, Real.rpow_natCast] at hbase
  apply hbase.trans
  calc
    _ = C *
        (heckeConductorScale K (E.rows.character u) ^ (a - 1 / 2 + 6 * e) *
          heckeConductorScale K ((E.rows.character u)⁻¹) ^ (1 : ℝ) *
          heckeConductorScale K (ψ * conjugate (E.rows.character u)) ^ (1 : ℝ)) *
        (2 + Hupper) ^ boundaryHeightDegree K := by ring
    _ ≤ C * (D * frequencyRowNorm K S u ^ 3) *
        (2 + Hupper) ^ boundaryHeightDegree K :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod3 hC.le)
        (pow_nonneg (by linarith : 0 ≤ 2 + Hupper) _)
    _ = _ := by ring

#print axioms exists_uniform_high_row_LRatio_strip_bound
#print axioms exists_uniform_high_row_deletedLRatio_strip_bound
#print axioms exists_uniform_deleted_zeta_six_bound
#print axioms exists_uniform_actual_row_conductor_norm_bound
#print axioms exists_uniform_high_row_deletedLRatio_norm_bound


end HighBinBoundary.ActualLRatioStrip
