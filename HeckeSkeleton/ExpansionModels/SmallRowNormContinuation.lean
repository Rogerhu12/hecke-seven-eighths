import HeckeGeneral.Analysis.HeckeNormPole
import HeckeSkeleton.HeckeBufferedReciprocal
import HeckeGeneral.Characters.InfinityPacket
import DedekindZetaZeroFree.LFunctions.Hecke.UniformWeakConvexity
import DedekindZetaZeroFree.LFunctions.Hecke.PrincipalUnitCharacter
import DedekindZetaZeroFree.LFunctions.Dedekind.PositiveExteriorZetaResidue

/-!
# The actual pole-cleared norm branch for bounded exceptional rows

The numerator below is the entire function supplied by the actual norm-twist
continuation theorem.  Its polynomial strip bound is obtained from the proved
principal ray-character convexity theorem and uniqueness of entire functions.
No growth assertion about a selected small row is an input.

Dividing this numerator by s-it gives a holomorphic regularization on Re s>0.
The ratio (s-1-it)/(s-it) has norm at most one on Re s>=1/2.  In particular the
literal reciprocal, including its total-division value at the pole, is bounded
by the reciprocal of this regularization.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Expansion.SmallRows

open NumberField IsDedekindDomain Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeSkeleton.HeckeBufferedReciprocal
open scoped Classical Topology

variable (K : Type) [Field K] [NumberField K]

def normPoleNumerator (t : ℝ) : ℂ → ℂ :=
  Classical.choose (exists_nonzero_poleCleared_normTwist K t)

theorem normPoleNumerator_differentiable (t : ℝ) :
    Differentiable ℂ (normPoleNumerator K t) :=
  (Classical.choose_spec (exists_nonzero_poleCleared_normTwist K t)).1

theorem normPoleNumerator_at_pole (t : ℝ) :
    normPoleNumerator K t (heckeNormPole t) ≠ 0 :=
  (Classical.choose_spec (exists_nonzero_poleCleared_normTwist K t)).2.1

theorem normPoleNumerator_right (t : ℝ) (s : ℂ) (hs : 1 < s.re) :
    normPoleNumerator K t s =
      (s - heckeNormPole t) * heckeLSeries K (heckeNormTwist K t) s :=
  (Classical.choose_spec (exists_nonzero_poleCleared_normTwist K t)).2.2 s hs

private theorem entire_eq_of_right (f g : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (heq : ∀ s : ℂ, 1 < s.re → f s = g s) : f = g := by
  apply (show AnalyticOnNhd ℂ f Set.univ from fun z _ => hf.analyticAt z).eq_of_eventuallyEq
    (show AnalyticOnNhd ℂ g Set.univ from fun z _ => hg.analyticAt z)
    (z₀ := (2 : ℂ))
  have hn : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [hn] with z hz
  exact heq z hz

/-- The formula is pointwise, including the total-division value at the pole. -/
theorem heckeContinuation_normTwist_eq (t : ℝ) :
    heckeContinuation K (heckeNormTwist K t) =
      fun s => normPoleNumerator K t s / (s - heckeNormPole t) := by
  obtain ⟨t', Q, ht', hQ, hL⟩ := heckeContinuation_normBranch K
    (heckeNormTwist K t) ⟨t, rfl⟩
  have htt : t' = t := by
    let v : InfinitePlace K := Classical.choice inferInstance
    have hh := congrArg (heckeRadialParameter K v) ht'
    simp only [heckeRadialParameter_normTwist] at hh
    linarith
  subst t'
  have hsame : Q = normPoleNumerator K t := by
    apply entire_eq_of_right Q (normPoleNumerator K t) hQ (normPoleNumerator_differentiable K t)
    intro s hs
    have hmatch := heckeContinuation_eq_series K (heckeNormTwist K t) hs
    rw [hL] at hmatch
    have hden := sub_heckeNormPole_ne_zero hs t
    rw [normPoleNumerator_right K t s hs]
    exact (div_eq_iff hden).mp hmatch |>.trans (mul_comm _ _)
  simpa only [hsame] using hL

/-- The actual principal ray regularization controls the norm numerator.
The constants depend only on the field and the one fixed norm parameter. -/
theorem exists_normPoleNumerator_strip_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) (t : ℝ) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 4 →
      ‖normPoleNumerator K t s‖ ≤ C * (2 + |s.im|) ^ k := by
  let hK : NumberField.IsTotallyComplex K := ⟨hcomplex⟩
  let eta := DedekindZetaZeroFree.LargeSieve.principalUnitRayCharacter K
  have heta : eta.IsPrincipal :=
    DedekindZetaZeroFree.LargeSieve.principalUnitRayCharacter_isPrincipal K
  have hprim : eta.IsPrimitive :=
    DedekindZetaZeroFree.LargeSieve.principalUnitRayCharacter_isPrimitive K
  let D := DedekindZetaZeroFree.principalRayHeckeData K hK ⊤ top_ne_bot eta hprim heta
  let R := DedekindZetaZeroFree.principalHeckeEntireRegularization K ⊤ eta D
  have hR : Differentiable ℂ R :=
    DedekindZetaZeroFree.principalHeckeEntireRegularization_differentiable K hK
      ⊤ top_ne_bot eta D
  have hsame : normPoleNumerator K t = fun s => R (s - (t : ℂ) * Complex.I) := by
    apply entire_eq_of_right _ _ (normPoleNumerator_differentiable K t)
      (hR.comp (differentiable_id.sub_const _))
    intro s hs
    have hs' : 1 < (s - (t : ℂ) * Complex.I).re := by simpa using hs
    have hs1 : s - (t : ℂ) * Complex.I ≠ 1 := by
      intro hh
      rw [hh] at hs'
      norm_num at hs'
    rw [normPoleNumerator_right K t s hs]
    dsimp only [R]
    rw [DedekindZetaZeroFree.principalHeckeEntireRegularization_eq K hK ⊤ top_ne_bot
      eta D _ (zero_lt_one.trans hs') hs1,
      DedekindZetaZeroFree.PositiveZetaResidue.principal_continuation_eq_dedekindZeta
        K eta heta D _ hs', ← heckeLSeries_trivial_eq_dedekindZeta K hs']
    have htwist := heckeLSeries_normTwist K 1 t s
    rw [one_mul] at htwist
    rw [← htwist]
    congr 1
    simp only [heckeNormPole]
    ring
  obtain ⟨k, hk, hconv⟩ := DedekindZetaZeroFree.detector_convexity_bridge K hK
    1 (by norm_num)
  obtain ⟨A, hA, hbound⟩ := hconv (1 / 10) (by norm_num)
  refine ⟨A * (2 : ℝ) ^ (1 / 2 + (1 / 10 : ℝ)) * (2 + |t|) ^ k,
    k, by positivity, hk, ?_⟩
  intro s hs hs4
  have hb := (hbound 2 (by norm_num) ⊤ top_ne_bot eta hprim (by norm_num)
    (s - (t : ℂ) * Complex.I) (by simpa using (show 3 / 1000 ≤ s.re by linarith))
    (by simpa using hs4)).2 heta D
  have hreq := DedekindZetaZeroFree.principalHeckeEntireRegularization_eq_bridge K hK
    ⊤ top_ne_bot eta D (s - (t : ℂ) * Complex.I) (by simpa using (show 0 < s.re by linarith))
  rw [hsame]
  change ‖R (s - (t : ℂ) * Complex.I)‖ ≤ _
  rw [hreq]
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, zero_add, add_zero] at hb
  have habs : |s.im - t| ≤ |s.im| + |t| := abs_sub _ _
  have hheight : (2 + |s.im - t|) ^ k ≤ (2 + |t|) ^ k * (2 + |s.im|) ^ k := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    apply Real.rpow_le_rpow (by positivity) _ hk
    nlinarith [abs_nonneg s.im, abs_nonneg t, mul_nonneg (abs_nonneg s.im) (abs_nonneg t)]
  exact hb.trans ((mul_le_mul_of_nonneg_left hheight (by positivity)).trans_eq (by ring))

def normPoleRegularization (t : ℝ) (s : ℂ) : ℂ :=
  normPoleNumerator K t s / (s - (t : ℂ) * Complex.I)

def normPoleRatio (t : ℝ) (s : ℂ) : ℂ :=
  (s - heckeNormPole t) / (s - (t : ℂ) * Complex.I)

theorem normPoleRatio_norm_le_one (t : ℝ) (s : ℂ) (hs : 1 / 2 ≤ s.re) :
    ‖normPoleRatio t s‖ ≤ 1 := by
  let z := s - (t : ℂ) * Complex.I
  have hzr : 1 / 2 ≤ z.re := by simpa [z] using hs
  have hz : z ≠ 0 := Complex.ne_zero_of_re_pos (by linarith)
  have heq : s - heckeNormPole t = z - 1 := by dsimp [z, heckeNormPole]; ring
  have hn : ‖z - 1‖ ≤ ‖z‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im, sub_zero]
    nlinarith
  dsimp only [normPoleRatio]
  rw [heq, norm_div]
  exact (div_le_one (norm_pos_iff.mpr hz)).mpr hn

theorem normPoleRegularization_right (t : ℝ) (s : ℂ) (hs : 1 < s.re) :
    normPoleRegularization K t s =
      normPoleRatio t s * heckeContinuation K (heckeNormTwist K t) s := by
  rw [normPoleRegularization, normPoleNumerator_right K t s hs,
    heckeContinuation_eq_series K (heckeNormTwist K t) hs]
  dsimp only [normPoleRatio]
  ring

theorem normPoleRegularization_differentiableOn (t : ℝ) :
    DifferentiableOn ℂ (normPoleRegularization K t) {s : ℂ | 0 < s.re} := by
  apply (normPoleNumerator_differentiable K t).differentiableOn.div
    (differentiable_id.sub_const _).differentiableOn
  intro s hs
  exact Complex.ne_zero_of_re_pos (by simpa using hs)

/-- The old zero boundary excludes zeros of the entire numerator, including
the point where the original continuation has its pole. -/
theorem normPoleNumerator_ne_zero_of_upper (t H alpha : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hupper : ZeroUpperBound K (heckeNormTwist K t) H alpha)
    (s : ℂ) (hs : alpha < s.re) (hheight : |s.im| ≤ H) :
    normPoleNumerator K t s ≠ 0 := by
  by_cases hp : s = heckeNormPole t
  · simpa only [hp] using normPoleNumerator_at_pole K t
  intro hzero
  have hLzero : heckeContinuation K (heckeNormTwist K t) s = 0 := by
    rw [heckeContinuation_normTwist_eq K t, hzero, zero_div]
  by_cases hright : 1 < s.re
  · exact heckeContinuation_ne_zero K (heckeNormTwist K t) hright hLzero
  have ha : AnalyticAt ℂ (heckeContinuation K (heckeNormTwist K t)) s := by
    rw [heckeContinuation_normTwist_eq K t]
    exact ((normPoleNumerator_differentiable K t).analyticAt s).div
      (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hp)
  have hlim : Tendsto (heckeContinuation K (heckeNormTwist K t)) (𝓝[≠] s) (𝓝 0) := by
    simpa only [hLzero] using ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hpos : 0 < meromorphicOrderAt (heckeContinuation K (heckeNormTwist K t)) s :=
    (tendsto_zero_iff_meromorphicOrderAt_pos ha.meromorphicAt).mp hlim
  exact (not_le_of_gt hs) (hupper s hpos (halpha.trans hs.le) (le_of_not_gt hright) hheight)

theorem normPoleRegularization_ne_zero_of_upper (t H alpha : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hupper : ZeroUpperBound K (heckeNormTwist K t) H alpha)
    (s : ℂ) (hs : alpha < s.re) (hheight : |s.im| ≤ H) :
    normPoleRegularization K t s ≠ 0 := by
  exact div_ne_zero (normPoleNumerator_ne_zero_of_upper K t H alpha halpha hupper s hs hheight)
    (Complex.ne_zero_of_re_pos (by simpa using (show 0 < s.re by linarith)))

/-- The reciprocal inequality uses the literal chosen continuation even at
the norm pole; no exceptional row or point is removed. -/
theorem normTwist_reciprocal_le_regularized (t : ℝ) (s : ℂ) (hs : 1 / 2 ≤ s.re) :
    ‖(heckeContinuation K (heckeNormTwist K t) s)⁻¹‖ ≤
      ‖(normPoleRegularization K t s)⁻¹‖ := by
  have hden : s - (t : ℂ) * Complex.I ≠ 0 :=
    Complex.ne_zero_of_re_pos (by simpa using (show 0 < s.re by linarith))
  have heq : (heckeContinuation K (heckeNormTwist K t) s)⁻¹ =
      normPoleRatio t s * (normPoleRegularization K t s)⁻¹ := by
    rw [heckeContinuation_normTwist_eq K t]
    dsimp only [normPoleRatio, normPoleRegularization]
    simp only [inv_div]
    simp only [div_eq_mul_inv]
    calc
      _ = (s - heckeNormPole t) *
          ((s - (t : ℂ) * Complex.I)⁻¹ * (s - (t : ℂ) * Complex.I)) *
          (normPoleNumerator K t s)⁻¹ := by rw [inv_mul_cancel₀ hden, mul_one]
      _ = _ := by ring
  rw [heq, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (normPoleRatio_norm_le_one t s hs)

end HeckeSkeleton.Expansion.SmallRows

#print axioms HeckeSkeleton.Expansion.SmallRows.heckeContinuation_normTwist_eq
#print axioms HeckeSkeleton.Expansion.SmallRows.exists_normPoleNumerator_strip_bound
#print axioms HeckeSkeleton.Expansion.SmallRows.normTwist_reciprocal_le_regularized
