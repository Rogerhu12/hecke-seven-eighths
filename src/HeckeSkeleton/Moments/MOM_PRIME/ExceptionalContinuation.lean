import HeckeSkeleton.ExpansionModels.SmallRowNormContinuation
import HeckeSkeleton.HeckeUniformStripGrowth
import DedekindZetaZeroFree.LFunctions.Hecke.RegularizationStripGrowth
import DedekindZetaZeroFree.LFunctions.Hecke.UniformRegularizationBoundaryBounds
import DedekindZetaZeroFree.Analysis.PhragmenLindelof.PolynomialBoundaryBounds

/-!
# Actual exceptional continuations and their uniform contour control

The norm-reduced exceptional background is either principal or a genuine
non-norm Hecke character.  The principal numerator is the actual entire
numerator already used by the source expansion.  Its bound here includes
the line Re(s)=0, where the terminal Mellin remainder is independent of
the physical length.  Both branches are proved from existing Hecke and
principal ray-character theorems; no ideal-sum asymptotic is an input.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME

open NumberField IsDedekindDomain Set Filter
open HeckeGeneral.Analysis HeckeGeneral.Characters HeckeGeneral.Bridge
open HeckeSkeleton.Expansion.SmallRows HeckeSkeleton.HeckeUniformStripGrowth
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open scoped Classical Topology

variable (K : Type) [Field K] [NumberField K]

/-- The only possible norm character after removal of the global norm
phase is the principal character.  This is the manuscript's structural
norm-reduction condition. -/
def ExceptionalNormReduced (χ : HeckeCharacter K) : Prop :=
  χ = 1 ∨ ∀ t : ℝ, χ ≠ heckeNormTwist K t

/-- The genuine residue of the actual norm-reduced continuation. -/
def actualExceptionalResidue (χ : HeckeCharacter K) : ℂ :=
  if χ = 1 then normPoleNumerator K 0 1 else 0

@[simp] theorem actualExceptionalResidue_principal :
    actualExceptionalResidue K (1 : HeckeCharacter K) = normPoleNumerator K 0 1 := by
  simp [actualExceptionalResidue]

theorem actualExceptionalResidue_eq_zero (χ : HeckeCharacter K) (hχ : χ ≠ 1) :
    actualExceptionalResidue K χ = 0 := by
  simp [actualExceptionalResidue, hχ]

theorem actualExceptionalResidue_principal_ne_zero :
    actualExceptionalResidue K (1 : HeckeCharacter K) ≠ 0 := by
  simpa [actualExceptionalResidue, heckeNormPole] using normPoleNumerator_at_pole K 0

/-- A polynomial bound on the entire principal numerator throughout
[-1/10,11/10], including the pole and the zero line. -/
theorem exists_principalNumerator_zeroStrip_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -(1 / 10 : ℝ) ≤ s.re → s.re ≤ 11 / 10 →
      ‖normPoleNumerator K 0 s‖ ≤
        C * (2 + |s.im|) ^ (2 * InfinitePlace.nrComplexPlaces K + 1) := by
  let hK : IsTotallyComplex K := ⟨hcomplex⟩
  let η := DedekindZetaZeroFree.LargeSieve.principalUnitRayCharacter K
  have hη : η.IsPrincipal :=
    DedekindZetaZeroFree.LargeSieve.principalUnitRayCharacter_isPrincipal K
  have hprim : η.IsPrimitive :=
    DedekindZetaZeroFree.LargeSieve.principalUnitRayCharacter_isPrimitive K
  let D := DedekindZetaZeroFree.principalRayHeckeData K hK ⊤ top_ne_bot η hprim hη
  let R := DedekindZetaZeroFree.principalHeckeEntireRegularization K ⊤ η D
  have hR : Differentiable ℂ R :=
    DedekindZetaZeroFree.principalHeckeEntireRegularization_differentiable K hK
      ⊤ top_ne_bot η D
  have hsame : normPoleNumerator K 0 = R := by
    apply entire_eq_of_eq_rightHalfPlane _ _ (normPoleNumerator_differentiable K 0) hR
    intro s hs
    have hs1 : s ≠ 1 := by intro h; simpa [h] using hs
    rw [normPoleNumerator_right K 0 s hs]
    dsimp only [R]
    rw [DedekindZetaZeroFree.principalHeckeEntireRegularization_eq K hK ⊤ top_ne_bot
      η D s (zero_lt_one.trans hs) hs1,
      DedekindZetaZeroFree.PositiveZetaResidue.principal_continuation_eq_dedekindZeta
        K η hη D s hs, ← heckeLSeries_trivial_eq_dedekindZeta K hs]
    simp [heckeNormPole, heckeNormTwist]
  obtain ⟨C, hC, _, hp⟩ :=
    DedekindZetaZeroFree.heckeEntireRegularizations_uniform_boundaries K hK
      (1 / 10) (by norm_num) (by norm_num)
  obtain ⟨M, B, hM, hB, hg⟩ :=
    DedekindZetaZeroFree.principalHeckeEntireRegularization_quadratic_strip_growth
      K hK ⊤ top_ne_bot η D (-(1 / 10)) (1 + 1 / 10) (by norm_num)
  let n := 2 * InfinitePlace.nrComplexPlaces K + 1
  refine ⟨6 ^ n * C, mul_pos (by positivity) hC, ?_⟩
  intro s hs hs'
  rw [hsame]
  exact DedekindZetaZeroFree.norm_le_on_closed_strip_of_polynomial_boundary
    (1 / 10) (by norm_num) (by norm_num) n C hC.le R hR.diffContOnCl
    ⟨M, B, hM, hB, fun z hz => hg z hz.1.le hz.2.le⟩
    (hp η hprim hη D).1 s ⟨hs, by linarith⟩

theorem actualPrincipalContinuation_eq (s : ℂ) :
    heckeContinuation K (1 : HeckeCharacter K) s = normPoleNumerator K 0 s / (s - 1) := by
  simpa [heckeNormTwist, heckeNormPole] using congrFun (heckeContinuation_normTwist_eq K 0) s

theorem actualExceptionalContinuation_differentiableAt
    (χ : HeckeCharacter K) (hχ : ExceptionalNormReduced K χ)
    (s : ℂ) (hs : s ≠ 1) : DifferentiableAt ℂ (heckeContinuation K χ) s := by
  rcases hχ with rfl | hχ
  · have heq : heckeContinuation K (1 : HeckeCharacter K) =
        fun z => normPoleNumerator K 0 z / (z - 1) := funext (actualPrincipalContinuation_eq K)
    rw [heq]
    exact (normPoleNumerator_differentiable K 0 s).div
      (differentiableAt_id.sub_const _) (sub_ne_zero.mpr hs)
  · exact differentiable_heckeContinuation_of_nonNorm K χ hχ s

/-- The genuine residue limit, including residue zero in the non-norm
branch.  It refers to the literal chosen Hecke continuation. -/
theorem actualExceptionalContinuation_residue
    (χ : HeckeCharacter K) (hχ : ExceptionalNormReduced K χ) :
    Tendsto (fun s : ℂ => (s - 1) * heckeContinuation K χ s)
      (𝓝[≠] (1 : ℂ)) (𝓝 (actualExceptionalResidue K χ)) := by
  rcases hχ with rfl | hχ
  · rw [actualExceptionalResidue_principal]
    refine (((normPoleNumerator_differentiable K 0).continuous.tendsto 1).mono_left
      nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [actualPrincipalContinuation_eq]
    field_simp [sub_ne_zero.mpr hs]
  · have hne : χ ≠ 1 := by
      intro h
      apply hχ 0
      simpa [heckeNormTwist] using h
    rw [actualExceptionalResidue_eq_zero K χ hne]
    have hc : Continuous (fun s : ℂ => (s - 1) * heckeContinuation K χ s) :=
      (continuous_id.sub continuous_const).mul
        (differentiable_heckeContinuation_of_nonNorm K χ hχ).continuous
    have ht := hc.tendsto (1 : ℂ)
    simpa only [sub_self, zero_mul] using ht.mono_left nhdsWithin_le_nhds

/-- One polynomial degree controls both the entire zero line and the
bounded real strip away from pole height.  The constants precede all
physical scales, all annular tests, and every norm phase. -/
theorem exists_actualExceptionalContinuation_control
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (hχ : ExceptionalNormReduced K χ) :
    ∃ (n : ℕ) (C : ℝ), 0 < C ∧
      (∀ s : ℂ, s.re = 0 → ‖heckeContinuation K χ s‖ ≤ C * (1 + |s.im|) ^ n) ∧
      (∀ s : ℂ, 0 ≤ s.re → s.re ≤ 11 / 10 → 1 ≤ |s.im| →
        ‖heckeContinuation K χ s‖ ≤ C * (1 + |s.im|) ^ n) := by
  have htwo (n : ℕ) (s : ℂ) :
      (2 + |s.im|) ^ n ≤ 2 ^ n * (1 + |s.im|) ^ n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [abs_nonneg s.im]) n
  rcases hχ with rfl | hχ
  · obtain ⟨C, hC, hb⟩ := exists_principalNumerator_zeroStrip_bound K hcomplex
    let n := 2 * InfinitePlace.nrComplexPlaces K + 1
    refine ⟨n, C * 2 ^ n, mul_pos hC (by positivity), ?_, ?_⟩
    · intro s hs
      have hden : 1 ≤ ‖s - 1‖ := by
        have hh := Complex.abs_re_le_norm (s - 1)
        simpa [Complex.sub_re, hs] using hh
      rw [actualPrincipalContinuation_eq, norm_div]
      calc
        _ ≤ ‖normPoleNumerator K 0 s‖ := div_le_self (norm_nonneg _) hden
        _ ≤ C * (2 + |s.im|) ^ n := hb s (by linarith) (by linarith)
        _ ≤ _ := (mul_le_mul_of_nonneg_left (htwo n s) hC.le).trans_eq (by ring)
    · intro s hs hs' ht
      have hden : 1 ≤ ‖s - 1‖ := ht.trans (by
        simpa using Complex.abs_im_le_norm (s - 1))
      rw [actualPrincipalContinuation_eq, norm_div]
      calc
        _ ≤ ‖normPoleNumerator K 0 s‖ := div_le_self (norm_nonneg _) hden
        _ ≤ C * (2 + |s.im|) ^ n := hb s (by linarith) hs'
        _ ≤ _ := (mul_le_mul_of_nonneg_left (htwo n s) hC.le).trans_eq (by ring)
  · obtain ⟨E, hE, hb⟩ := exists_uniform_fixedType_strip_bound K hcomplex
      (fun v => heckeRadialParameter K v χ) (heckeArchWeight K χ)
      (1 / 10) (by norm_num) (by norm_num)
    let n := 2 * Fintype.card (InfinitePlace K)
    let C := E * heckeConductorScale K χ ^ (1 / 2 + (1 / 10 : ℝ))
    have hC : 0 ≤ C := by dsimp [C, heckeConductorScale]; positivity
    have hb' (s : ℂ) (hs : 0 ≤ s.re) (hs' : s.re ≤ 11 / 10) :
        ‖heckeContinuation K χ s‖ ≤ (1 + C) * 2 ^ n * (1 + |s.im|) ^ n := by
      have h := hb χ hχ rfl rfl s ⟨by linarith, by linarith⟩
      change ‖heckeContinuation K χ s‖ ≤ C * (2 + |s.im|) ^ n at h
      calc
        _ ≤ C * (2 + |s.im|) ^ n := h
        _ ≤ C * (2 ^ n * (1 + |s.im|) ^ n) :=
          mul_le_mul_of_nonneg_left (htwo n s) hC
        _ ≤ _ := by nlinarith [show 0 ≤ 2 ^ n * (1 + |s.im|) ^ n by positivity]
    refine ⟨n, (1 + C) * 2 ^ n, by positivity, ?_, ?_⟩
    · intro s hs
      exact hb' s (by linarith) (by linarith)
    · intro s hs hs' _
      exact hb' s hs hs'

end HeckeSkeleton.Moments.MOM_PRIME
