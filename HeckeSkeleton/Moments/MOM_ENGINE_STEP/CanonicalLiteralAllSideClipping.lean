import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralRawWindows

/-!
# Clipping every literal side, including an identically zero side

A zero source need not have a central scale bounded below. Its actual
clipping factor is therefore retained in the normalization radius.
The fixed broad window starts at zero; each actual dilated profile is
still a constructed Schwartz function. On every active side a genuine
nonzero member bounds these same clipping factors by the original
annulus. This proves the uniform active cost and the narrower positive
window without changing any profile, chosen child or Fourier measure.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

namespace CanonicalLiteralAllSideClipping

theorem clippingCoefficient_mono (s : Finset (ℕ × ℕ))
    {c B : ℝ} (hc : 1 ≤ c) (h : c ≤ B) :
    CanonicalLogProfiles.clippingCoefficient c s ≤
      CanonicalLogProfiles.clippingCoefficient B s := by
  unfold CanonicalLogProfiles.clippingCoefficient
  exact mul_le_mul (Real.sqrt_le_sqrt h)
    (pow_le_pow_left₀ (zero_le_one.trans hc) h _)
    (pow_nonneg (zero_le_one.trans hc) _) (Real.sqrt_nonneg _)

def cost (Z : ℝ) (parameters : RealParameters) (s : Finset (ℕ × ℕ)) : ℝ :=
  1 + CanonicalLogProfiles.clippingCoefficient (plainClippingFactor Z parameters.n₁) s +
    CanonicalLogProfiles.clippingCoefficient (plainClippingFactor Z parameters.n₂) s

theorem cost_bounds (Z : ℝ) (parameters : RealParameters) (hZ : 1 ≤ Z)
    (s : Finset (ℕ × ℕ)) :
    1 ≤ cost Z parameters s ∧
      CanonicalLogProfiles.clippingCoefficient (plainClippingFactor Z parameters.n₁) s ≤
        cost Z parameters s ∧
      CanonicalLogProfiles.clippingCoefficient (plainClippingFactor Z parameters.n₂) s ≤
        cost Z parameters s := by
  have h₁ := CanonicalLogProfiles.clippingCoefficient_one_le _
    (plainClippingFactor_one_le Z parameters.n₁ hZ) s
  have h₂ := CanonicalLogProfiles.clippingCoefficient_one_le _
    (plainClippingFactor_one_le Z parameters.n₂ hZ) s
  unfold cost
  constructor
  · linarith
  constructor <;> linarith

theorem dilation_support (lo hi c : ℝ) (hlo : 0 < lo) (hc : 1 ≤ c)
    (φ : 𝓢(ℝ, ℂ)) (hφ : Function.support φ ⊆ Set.Icc lo hi) :
    Function.support (CanonicalLogProfiles.dilationSchwartz c hc φ) ⊆ Set.Icc 0 hi := by
  intro y hy
  rw [Function.mem_support, CanonicalLogProfiles.dilationSchwartz_apply] at hy
  have harg := hφ (right_ne_zero_of_mul hy)
  have hy0 : 0 ≤ y := by
    by_contra h
    have hcy : c * y < 0 := mul_neg_of_pos_of_neg (zero_lt_one.trans_le hc) (lt_of_not_ge h)
    linarith [harg.1]
  exact ⟨hy0, (le_mul_of_one_le_left hy0 hc).trans harg.2⟩

theorem original_support (lo hi : ℝ) (hlo : 0 < lo) :
    Set.Icc lo hi ⊆ Set.Icc 0 hi := fun _ hy => ⟨hlo.le.trans hy.1, hy.2⟩

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain : Set ℝ}

/-- The only cost is the explicitly computed dilation at the same
two original exponents. No nonzero-source premise is needed here. -/
def clipWindow (d : MomentData K ω ψ) (parameters : RealParameters)
    (Z : ℝ) (hZ : 1 ≤ Z) (lo hi : ℝ) (hlo : 0 < lo)
    (s : Finset (ℕ × ℕ)) {B : ℝ} (hB : 0 ≤ B)
    (w : RawProfileWindow rowDomain heightDomain (Set.Icc lo hi) s d B) :
    RawProfileWindow rowDomain heightDomain (Set.Icc 0 hi) s
      (clipPlainData d parameters Z (zero_lt_one.trans_le hZ)) (cost Z parameters s * B) := by
  let c₁ := plainClippingFactor Z parameters.n₁
  let c₂ := plainClippingFactor Z parameters.n₂
  have hc₁ : 1 ≤ c₁ := plainClippingFactor_one_le Z parameters.n₁ hZ
  have hc₂ : 1 ≤ c₂ := plainClippingFactor_one_le Z parameters.n₂ hZ
  have hcost := cost_bounds Z parameters hZ s
  have hBC : B ≤ cost Z parameters s * B := le_mul_of_one_le_left hB hcost.1
  have hleft (φ : 𝓢(ℝ, ℂ)) (hφ : s.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ ≤ B) :
      s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
          (CanonicalLogProfiles.dilationSchwartz c₁ hc₁ φ) ≤ cost Z parameters s * B :=
    (CanonicalLogProfiles.dilationSchwartz_finset_bound c₁ hc₁ s c₁ hc₁ le_rfl φ).trans
      (mul_le_mul hcost.2.1 hφ (apply_nonneg _ _) (zero_le_one.trans hcost.1))
  have hright (φ : 𝓢(ℝ, ℂ)) (hφ : s.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ ≤ B) :
      s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
          (CanonicalLogProfiles.dilationSchwartz c₂ hc₂ φ) ≤ cost Z parameters s * B :=
    (CanonicalLogProfiles.dilationSchwartz_finset_bound c₂ hc₂ s c₂ hc₂ le_rfl φ).trans
      (mul_le_mul hcost.2.2 hφ (apply_nonneg _ _) (zero_le_one.trans hcost.1))
  refine
    { inverseRep := w.inverseRep
      leftRep := fun u t => CanonicalLogProfiles.dilationSchwartz c₁ hc₁ (w.leftRep u t)
      rightRep := fun u t => CanonicalLogProfiles.dilationSchwartz c₂ hc₂ (w.rightRep u t)
      primeRep := w.primeRep
      inverse_eq := w.inverse_eq
      left_eq := ?_
      right_eq := ?_
      prime_eq := w.prime_eq
      inverse_support := fun u hu t ht =>
        (w.inverse_support u hu t ht).trans (original_support lo hi hlo)
      left_support := fun u hu t ht =>
        dilation_support lo hi c₁ hlo hc₁ _ (w.left_support u hu t ht)
      right_support := fun u hu t ht =>
        dilation_support lo hi c₂ hlo hc₂ _ (w.right_support u hu t ht)
      prime_support := fun j t ht => (w.prime_support j t ht).trans (original_support lo hi hlo)
      inverse_bound := fun u hu t ht => (w.inverse_bound u hu t ht).trans hBC
      left_bound := fun u hu t ht => hleft _ (w.left_bound u hu t ht)
      right_bound := fun u hu t ht => hright _ (w.right_bound u hu t ht)
      prime_bound := fun j t ht => (w.prime_bound j t ht).trans hBC }
  · intro u t y
    change (Real.sqrt c₁ : ℂ) * d.plainTest₁.profile u t (c₁ * y) = _
    rw [CanonicalLogProfiles.dilationSchwartz_apply, w.left_eq]
  · intro u t y
    change (Real.sqrt c₂ : ℂ) * d.plainTest₂.profile u t (c₂ * y) = _
    rw [CanonicalLogProfiles.dilationSchwartz_apply, w.right_eq]

/-- Only the support proofs are sharpened on an active family. The
representatives and the previously computed radius are identical. -/
def clipWindowNarrow (d : MomentData K ω ψ) (parameters : RealParameters)
    (Z : ℝ) (hZ : 1 ≤ Z) (lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi)
    (s : Finset (ℕ × ℕ)) {B : ℝ} (hB : 0 ≤ B)
    (w : RawProfileWindow rowDomain heightDomain (Set.Icc lo hi) s d B)
    (hleft : plainClippingFactor Z parameters.n₁ ≤ hi)
    (hright : plainClippingFactor Z parameters.n₂ ≤ hi) :
    RawProfileWindow rowDomain heightDomain (Set.Icc (lo / hi) hi) s
      (clipPlainData d parameters Z (zero_lt_one.trans_le hZ)) (cost Z parameters s * B) :=
  { clipWindow d parameters Z hZ lo hi hlo s hB w with
    inverse_support := fun u hu t ht => (w.inverse_support u hu t ht).trans
      (CanonicalLogProfiles.originalAnnulus_subset_clipped lo hi hlo hhi)
    left_support := fun u hu t ht => CanonicalLogProfiles.dilationSchwartz_support
      lo hi hlo hhi _ (plainClippingFactor_one_le Z parameters.n₁ hZ) hleft _
      (w.left_support u hu t ht)
    right_support := fun u hu t ht => CanonicalLogProfiles.dilationSchwartz_support
      lo hi hlo hhi _ (plainClippingFactor_one_le Z parameters.n₂ hZ) hright _
      (w.right_support u hu t ht)
    prime_support := fun j t ht => (w.prime_support j t ht).trans
      (CanonicalLogProfiles.originalAnnulus_subset_clipped lo hi hlo hhi) }

theorem cost_le_of_factors (Z : ℝ) (parameters : RealParameters) (hZ : 1 ≤ Z)
    (hi : ℝ) (s : Finset (ℕ × ℕ))
    (hleft : plainClippingFactor Z parameters.n₁ ≤ hi)
    (hright : plainClippingFactor Z parameters.n₂ ≤ hi) :
    cost Z parameters s ≤ 1 + 2 * CanonicalLogProfiles.clippingCoefficient hi s := by
  have hl := clippingCoefficient_mono s (plainClippingFactor_one_le Z parameters.n₁ hZ) hleft
  have hr := clippingCoefficient_mono s (plainClippingFactor_one_le Z parameters.n₂ hZ) hright
  unfold cost
  linarith

/-- The active clipping cost is bounded from the actual nonzero
energy and the original annulus, without a final profile bound. -/
theorem cost_le_of_nonzero (d : MomentData K ω ψ) (parameters : RealParameters)
    (Z time lo hi : ℝ) (hZ : 1 < Z) (hhi : 1 ≤ hi)
    (s : Finset (ℕ × ℕ)) (B : ℝ)
    (w : RawProfileWindow rowDomain heightDomain (Set.Icc lo hi) s d B)
    (hrows : ∀ u ∈ pairedRows d parameters Z, u ∈ rowDomain)
    (ht : time ∈ heightDomain) (hne : pairedEnergy d parameters Z time ≠ 0) :
    cost Z parameters s ≤ 1 + 2 * CanonicalLogProfiles.clippingCoefficient hi s := by
  have hc := CanonicalLogProfiles.clipping_factors_le_of_window_nonzero
    d parameters Z time lo hi hZ hhi s B w hrows ht hne
  exact cost_le_of_factors Z parameters hZ.le hi s hc.1 hc.2

/-- A polynomial radius for every side. Active sides later use
`cost_le_of_nonzero`; inactive sides never enter the kernel carrier. -/
def familyWindows
    (family : WithLp 2 (ℝ × ℝ) → MomentData K ω ψ) (parameters : RealParameters)
    (Z : ℝ) (hZ : 1 ≤ Z) (lo hi : ℝ) (hlo : 0 < lo)
    (s : Finset (ℕ × ℕ)) (B : ℝ) (hB : 0 ≤ B) (J : ℕ)
    (raw : ∀ ξ, RawProfileWindow rowDomain heightDomain (Set.Icc lo hi) s (family ξ)
      (polynomialProfileRadius B J J (WithLp.ofLp ξ)))
    (ξ : WithLp 2 (ℝ × ℝ)) :
    RawProfileWindow rowDomain heightDomain (Set.Icc 0 hi) s (family ξ)
      (polynomialProfileRadius (cost Z parameters s * (1 + B)) J J (WithLp.ofLp ξ)) ×
    RawProfileWindow rowDomain heightDomain (Set.Icc 0 hi) s
      (clipPlainData (family ξ) parameters Z (zero_lt_one.trans_le hZ))
      (polynomialProfileRadius (cost Z parameters s * (1 + B)) J J (WithLp.ofLp ξ)) := by
  have hC := (cost_bounds Z parameters hZ s).1
  have hrawpos := (polynomialProfileRadius_pos B hB J J (WithLp.ofLp ξ)).le
  have henvelope : cost Z parameters s * polynomialProfileRadius B J J (WithLp.ofLp ξ) ≤
      polynomialProfileRadius (cost Z parameters s * (1 + B)) J J (WithLp.ofLp ξ) := by
    have h := mul_le_mul_of_nonneg_left
      (polynomialProfileRadius_le B J J (WithLp.ofLp ξ)) (zero_le_one.trans hC)
    unfold polynomialProfileRadius at h ⊢
    nlinarith
  refine ⟨?_, (clipWindow (family ξ) parameters Z hZ lo hi hlo s hrawpos (raw ξ)).mono henvelope⟩
  exact (CanonicalLiteralFourierWindows.enlargeWindow (raw ξ) (original_support lo hi hlo)).mono
    ((le_mul_of_one_le_left hrawpos hC).trans henvelope)

end CanonicalLiteralAllSideClipping
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllSideClipping.clipWindow
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllSideClipping.clipWindowNarrow
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllSideClipping.cost_le_of_nonzero
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAllSideClipping.familyWindows
