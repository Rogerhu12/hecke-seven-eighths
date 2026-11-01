import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralBalancedSchwartz
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSelectedRawWindow
import HeckeGeneral.Analysis.IdealDirichlet

/-!
# Original norm lower bounds for active balanced profiles

The lower bound on a plain central scale is derived from a genuinely
nonzero ideal summand and the original annulus. Dividing that scale by
the norms of the actual extracted ideals only decreases it. Thus the
pre-extraction scale product required by the balanced-profile estimate
is a consequence of the literal quotient-scale identities, rather than
a final profile or capacity assumption.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support

namespace CanonicalLiteralActiveProfileBounds

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

theorem plainScale_lower (W : IdealTest K)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (N time hi : ℝ)
    (hN : 0 < N) (hhi : 0 < hi)
    (hannulus : ∀ y, W.profile u time y ≠ 0 → y ≤ hi)
    (hne : (W.support u time N).Nonempty) : 1 / hi ≤ N := by
  obtain ⟨I, hI⟩ := hne
  have hratio := hannulus (idealNorm K I / N) ((W.support_spec _ _ _ _).mp hI)
  have hnorm : idealNorm K I ≤ hi * N := (div_le_iff₀ hN).mp hratio
  apply (div_le_iff₀ hhi).mpr
  have h := (one_le_idealNorm K I).trans hnorm
  simpa only [mul_comm] using h

theorem pairedScale_lower (d : MomentData K ω ψ) (parameters : RealParameters)
    (Z time lo hi : ℝ) (hZ : 0 < Z) (hhi : 0 < hi)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain : Set ℝ}
    {s : Finset (ℕ × ℕ)} {B : ℝ}
    (w : RawProfileWindow rowDomain heightDomain (Set.Icc lo hi) s d B)
    (hrows : ∀ u ∈ pairedRows d parameters Z, u ∈ rowDomain)
    (ht : time ∈ heightDomain) (hne : pairedEnergy d parameters Z time ≠ 0) :
    1 / hi ≤ Z ^ parameters.n₁ ∧ 1 / hi ≤ Z ^ parameters.n₂ := by
  obtain ⟨u, hu, hleft, hright⟩ := nonzero_pairedEnergy_plain_witness d parameters Z time hne
  have hleftAnnulus : ∀ y, d.plainTest₁.profile u time y ≠ 0 → y ≤ hi := by
    intro y hy
    rw [w.left_eq] at hy
    exact (w.left_support u (hrows u hu) time ht hy).2
  have hrightAnnulus : ∀ y, d.plainTest₂.profile u time y ≠ 0 → y ≤ hi := by
    intro y hy
    rw [w.right_eq] at hy
    exact (w.right_support u (hrows u hu) time ht hy).2
  exact ⟨plainScale_lower d.plainTest₁ u _ time hi (Real.rpow_pos_of_pos hZ _)
      hhi hleftAnnulus (plainPolynomial_support_nonempty d d.plainTest₁ u _ time hleft),
    plainScale_lower d.plainTest₂ u _ time hi (Real.rpow_pos_of_pos hZ _)
      hhi hrightAnnulus (plainPolynomial_support_nonempty d d.plainTest₂ u _ time hright)⟩

/-- The ideals may be the products of the actual second-common and
allocation divisors. Their norm lower bound is proved internally. -/
theorem quotient_product_lower_of_nonzero
    (d : MomentData K ω ψ) (parameters : RealParameters)
    (Z time lo hi N₁ N₂ : ℝ) (hZ : 0 < Z) (hhi : 0 < hi)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (I₁ I₂ : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hscale₁ : Z ^ parameters.n₁ = N₁ / idealNorm K I₁)
    (hscale₂ : Z ^ parameters.n₂ = N₂ / idealNorm K I₂)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain : Set ℝ}
    {s : Finset (ℕ × ℕ)} {B : ℝ}
    (w : RawProfileWindow rowDomain heightDomain (Set.Icc lo hi) s d B)
    (hrows : ∀ u ∈ pairedRows d parameters Z, u ∈ rowDomain)
    (ht : time ∈ heightDomain) (hne : pairedEnergy d parameters Z time ≠ 0) :
    hi ^ (-2 : ℝ) ≤ N₁ * N₂ := by
  have hscales := pairedScale_lower d parameters Z time lo hi hZ hhi w hrows ht hne
  have h₁ : 1 / hi ≤ N₁ := hscales.1.trans
    (hscale₁.le.trans (div_le_self hN₁.le (one_le_idealNorm K I₁)))
  have h₂ : 1 / hi ≤ N₂ := hscales.2.trans
    (hscale₂.le.trans (div_le_self hN₂.le (one_le_idealNorm K I₂)))
  have heq : hi ^ (-2 : ℝ) = (1 / hi) * (1 / hi) := by
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hhi.le,
      Real.rpow_two]
    simp only [pow_two, one_div, mul_inv_rev]
  rw [heq]
  exact mul_le_mul h₁ h₂ (div_nonneg zero_le_one hhi.le) hN₁.le

end CanonicalLiteralActiveProfileBounds

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel

variable {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k} {W : d.ProfileData}
variable {window : Set ℝ} (E : W.SchwartzModel window)
variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (power firstFixed poolFixed unitFixed : A.Exterior)
variable (firstElement poolElement unitElement : A.R)
variable (hfirst : A.Generates firstFixed firstElement)
variable (hpool : A.Generates poolFixed poolElement)
variable (hunit : A.Generates unitFixed unitElement)
variable (δ₁ δ₂ : ℝ)

/-- The common numerical coefficient is computed from the original
profile bound, fixed annulus and tilt/order constants. Its only scale
premise is the literal product lower bound proved above from a real
nonzero member. -/
theorem scalarFreeBalanced_original_bounds
    (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (r : Bool) (s : Finset (ℕ × ℕ)) (B hi : ℝ) (hB : 0 ≤ B) (hhi : 1 ≤ hi)
    (hδlo : 0 ≤ δ₁ + δ₂) (hδhi : δ₁ + δ₂ ≤ 1 / 2)
    (hproduct : d.scale₁ r * d.scale₂ r = d.scale₁ false * d.scale₂ false)
    (hlower : hi ^ (-2 : ℝ) ≤ (d.extract b).scale₁ false * (d.extract b).scale₂ false)
    (hleft : (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.left r) ≤ B)
    (hright : (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.right r) ≤ B)
    (hslot : ∀ j, (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.slot j) ≤ B) :
    let T := E.scalarFreeBalancedSecondInput (σ := σ) b P R
      power firstFixed poolFixed unitFixed firstElement poolElement unitElement
      hfirst hpool hunit δ₁ δ₂ hcompact hpositive
    let bound := B * CanonicalLogProfiles.shapeCoefficient window hcompact hpositive
      (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) s * (1 + Real.sqrt hi)
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (T.left r) ≤ bound ∧
      s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (T.right r) ≤ bound ∧
      ∀ j, s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (T.slot j) ≤ bound := by
  let Cshape := CanonicalLogProfiles.shapeCoefficient window hcompact hpositive
    (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) s
  have hC : 0 ≤ Cshape := CanonicalLogProfiles.shapeCoefficient_nonneg
    window hcompact hpositive _ s
  have hf := CanonicalLiteralBalancedSchwartz.factor_le d b δ₁ δ₂ hi r hhi
    hδlo hδhi hproduct hlower
  have hcompare (M : ℝ) (hM : 0 ≤ M) (hMB : M ≤ B) :
      CanonicalLiteralBalancedSchwartz.factor d b δ₁ δ₂ r * Cshape * M ≤
        B * Cshape * (1 + Real.sqrt hi) := by
    calc
      _ ≤ Real.sqrt hi * Cshape * B :=
        mul_le_mul (mul_le_mul_of_nonneg_right hf hC) hMB hM
          (mul_nonneg (Real.sqrt_nonneg _) hC)
      _ ≤ _ := by nlinarith [mul_nonneg hB hC]
  refine ⟨?_, ?_, ?_⟩
  · exact (E.scalarFreeBalanced_left_bound (σ := σ) b P R
      power firstFixed poolFixed unitFixed firstElement poolElement unitElement
      hfirst hpool hunit δ₁ δ₂ hcompact hpositive r s).trans
        (hcompare _ (apply_nonneg _ _) hleft)
  · exact (E.scalarFreeBalanced_right_bound (σ := σ) b P R
      power firstFixed poolFixed unitFixed firstElement poolElement unitElement
      hfirst hpool hunit δ₁ δ₂ hcompact hpositive r s).trans
        (hcompare _ (apply_nonneg _ _) hright)
  · intro j
    apply (E.scalarFreeBalanced_slot_bound (σ := σ) b P R
      power firstFixed poolFixed unitFixed firstElement poolElement unitElement
      hfirst hpool hunit δ₁ δ₂ hcompact hpositive j s hδhi).trans
    calc
      _ ≤ Cshape * B := mul_le_mul_of_nonneg_left (hslot (SlotRestriction.index b.keep j)) hC
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hB hC) (Real.sqrt_nonneg hi)]

/-- Every rectangle, including a zero rectangle, gets a radius from
its actual scale product. No nonzero-source premise or maximum over
other rectangles occurs in this construction. The preceding theorem
bounds this same coefficient uniformly when the rectangle is active. -/
theorem scalarFreeBalanced_computed_bounds
    (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (r : Bool) (s : Finset (ℕ × ℕ)) (B : ℝ) (hB : 0 ≤ B)
    (hδhi : δ₁ + δ₂ ≤ 1 / 2)
    (hleft : (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.left r) ≤ B)
    (hright : (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.right r) ≤ B)
    (hslot : ∀ j, (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.slot j) ≤ B) :
    let T := E.scalarFreeBalancedSecondInput (σ := σ) b P R
      power firstFixed poolFixed unitFixed firstElement poolElement unitElement
      hfirst hpool hunit δ₁ δ₂ hcompact hpositive
    let bound := B + B * CanonicalLogProfiles.shapeCoefficient window hcompact hpositive
      (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) s *
        (1 + CanonicalLiteralBalancedSchwartz.factor d b δ₁ δ₂ r)
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (T.left r) ≤ bound ∧
      s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (T.right r) ≤ bound ∧
      ∀ j, s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (T.slot j) ≤ bound := by
  let Cshape := CanonicalLogProfiles.shapeCoefficient window hcompact hpositive
    (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) s
  let f := CanonicalLiteralBalancedSchwartz.factor d b δ₁ δ₂ r
  have hC : 0 ≤ Cshape := CanonicalLogProfiles.shapeCoefficient_nonneg
    window hcompact hpositive _ s
  have hf : 0 ≤ f := Real.sqrt_nonneg _
  have hcompare (M : ℝ) (hMB : M ≤ B) : f * Cshape * M ≤ B + B * Cshape * (1 + f) := by
    calc
      _ ≤ f * Cshape * B := mul_le_mul_of_nonneg_left hMB (mul_nonneg hf hC)
      _ ≤ _ := by nlinarith [mul_nonneg hB hC]
  refine ⟨?_, ?_, ?_⟩
  · exact (E.scalarFreeBalanced_left_bound (σ := σ) b P R
      power firstFixed poolFixed unitFixed firstElement poolElement unitElement
      hfirst hpool hunit δ₁ δ₂ hcompact hpositive r s).trans (hcompare _ hleft)
  · exact (E.scalarFreeBalanced_right_bound (σ := σ) b P R
      power firstFixed poolFixed unitFixed firstElement poolElement unitElement
      hfirst hpool hunit δ₁ δ₂ hcompact hpositive r s).trans (hcompare _ hright)
  · intro j
    apply (E.scalarFreeBalanced_slot_bound (σ := σ) b P R
      power firstFixed poolFixed unitFixed firstElement poolElement unitElement
      hfirst hpool hunit δ₁ δ₂ hcompact hpositive j s hδhi).trans
    calc
      _ ≤ Cshape * B := mul_le_mul_of_nonneg_left (hslot (SlotRestriction.index b.keep j)) hC
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hB hC) hf]

end CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralActiveProfileBounds.quotient_product_lower_of_nonzero
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel.scalarFreeBalanced_original_bounds
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel.scalarFreeBalanced_computed_bounds
