import HeckeGeneral.Analysis.MeromorphicFamily
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Convex.Topology

/-!
# The analytic last step of the physical detector

The exponent is the manuscript's `C(s) = s - 11/16`.  A bound on the
physical probe gives holomorphy of its actual Mellin integral.  The separate
germ identity with the L-function and a nonzero numerator then excludes
positive meromorphic order, including at points where the L-function has
a pole.  Neither the physical bound nor that identity is asserted here.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open Filter MeasureTheory Set
open scoped Topology

def rightHalfPlane (b : ℝ) : Set ℂ := {s | b < s.re}

theorem isOpen_rightHalfPlane (b : ℝ) : IsOpen (rightHalfPlane b) :=
  isOpen_lt continuous_const Complex.continuous_re

theorem isPreconnected_rightHalfPlane (b : ℝ) : IsPreconnected (rightHalfPlane b) :=
  ((convex_Ioi b).linear_preimage Complex.reLm).isPreconnected

/-- Meromorphic identity propagation keeps punctured germs, so arbitrary
total-function values assigned at poles are irrelevant. -/
theorem meromorphic_germ_identity_of_preconnected {U : Set ℂ} {f g : ℂ → ℂ}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) (hU : IsPreconnected U)
    {s₀ : ℂ} (hs₀ : s₀ ∈ U) (heq : f =ᶠ[𝓝[≠] s₀] g) :
    ∀ s ∈ U, f =ᶠ[𝓝[≠] s] g := by
  have hd : MeromorphicOn (fun w => f w - g w) U :=
    fun w hw => (hf w hw).sub (hg w hw)
  have hzero : meromorphicOrderAt (fun w => f w - g w) s₀ = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [heq] with w hw
    exact sub_eq_zero.mpr hw
  intro s hs
  have hz := meromorphicOrderAt_eq_top_iff.mp
    (hd.meromorphicOrderAt_eq_top_of_isPreconnected hU hs₀ hs hzero)
  filter_upwards [hz] with w hw
  exact sub_eq_zero.mp hw

/-- This is the integral of `f(Z) Z^(-C(s)) dZ/Z`, not an abstract
holomorphic function supplied as a placeholder. -/
def physicalMellin (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  mellin f ((11 / 16 : ℂ) - s)

/-- Growth at infinity and rapid decay at the origin, with the exact
physical normalization.  Deriving this bound is an outstanding moment
consumer; this definition is not one of the manuscript's T/I/P inputs. -/
def PhysicalProbeBound (f : ℝ → ℂ) (b : ℝ) : Prop :=
  LocallyIntegrableOn f (Ioi 0) ∧
  f =O[atTop] (fun Z : ℝ => Z ^ (b - 11 / 16)) ∧
  ∀ N : ℝ, f =O[𝓝[>] 0] (fun Z : ℝ => Z ^ N)

theorem physicalMellin_differentiableAt {f : ℝ → ℂ} {b : ℝ}
    (hf : PhysicalProbeBound f b) {s : ℂ} (hs : s ∈ rightHalfPlane b) :
    DifferentiableAt ℂ (physicalMellin f) s := by
  have ht : f =O[atTop] (fun Z : ℝ => Z ^ (-((11 / 16 : ℝ) - b))) := by
    have he : -((11 / 16 : ℝ) - b) = b - 11 / 16 := by ring
    simpa only [he] using hf.2.1
  have hd := mellin_differentiableAt_of_isBigO_rpow
    (a := (11 / 16 : ℝ) - b) (b := ((11 / 16 : ℂ) - s).re - 1)
    (s := (11 / 16 : ℂ) - s) hf.1 ht
    (by change b < s.re at hs; norm_num; linarith)
    (hf.2.2 (-(((11 / 16 : ℂ) - s).re - 1))) (by linarith)
  exact hd.comp s (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => 11 / 16 - z) s)

theorem physicalMellin_analyticOnNhd {f : ℝ → ℂ} {b : ℝ}
    (hf : PhysicalProbeBound f b) :
    AnalyticOnNhd ℂ (physicalMellin f) (rightHalfPlane b) := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_rightHalfPlane b)
  exact fun s hs => (physicalMellin_differentiableAt hf hs).differentiableWithinAt

/-- The numerator identity is an equality of punctured germs.  Pointwise
division at a pole would not suffice for this argument. -/
def MellinDetectorIdentity (L : ℂ → ℂ) (f : ℝ → ℂ) (H : ℂ → ℂ)
    (b : ℝ) : Prop :=
  AnalyticOnNhd ℂ H (rightHalfPlane b) ∧
  (∀ s ∈ rightHalfPlane b, H s ≠ 0) ∧
  ∀ s ∈ rightHalfPlane b,
    (fun w => L w * physicalMellin f w) =ᶠ[𝓝[≠] s] H

/-- The transferred identification is needed at just one initial germ.
The full identity on the continued half-plane is proved below. -/
def InitialMellinDetectorIdentity (L : ℂ → ℂ) (f : ℝ → ℂ) (H : ℂ → ℂ)
    (b : ℝ) : Prop :=
  AnalyticOnNhd ℂ H (rightHalfPlane b) ∧
  (∀ s ∈ rightHalfPlane b, H s ≠ 0) ∧
  ∃ s₀ ∈ rightHalfPlane b,
    (fun w => L w * physicalMellin f w) =ᶠ[𝓝[≠] s₀] H

theorem InitialMellinDetectorIdentity.continue {L H : ℂ → ℂ} {f : ℝ → ℂ}
    {b : ℝ} (hid : InitialMellinDetectorIdentity L f H b)
    (hL : MeromorphicOn L (rightHalfPlane b)) (hf : PhysicalProbeBound f b) :
    MellinDetectorIdentity L f H b := by
  obtain ⟨s₀, hs₀, heq⟩ := hid.2.2
  refine ⟨hid.1, hid.2.1, ?_⟩
  exact meromorphic_germ_identity_of_preconnected
    (fun w hw => (hL w hw).mul ((physicalMellin_analyticOnNhd hf w hw).meromorphicAt))
    (fun w hw => (hid.1 w hw).meromorphicAt)
    (isPreconnected_rightHalfPlane b) hs₀ heq

theorem order_nonpos_of_analytic_multiplier {L G H : ℂ → ℂ} {s : ℂ}
    (hL : MeromorphicAt L s) (hG : AnalyticAt ℂ G s)
    (hH : AnalyticAt ℂ H s) (hne : H s ≠ 0)
    (heq : (fun w => L w * G w) =ᶠ[𝓝[≠] s] H) :
    meromorphicOrderAt L s ≤ 0 := by
  have hoH : meromorphicOrderAt H s = 0 := by
    rw [hH.meromorphicOrderAt_eq, hH.analyticOrderAt_eq_zero.mpr hne]
    rfl
  have hsum : meromorphicOrderAt L s + meromorphicOrderAt G s = 0 := by
    rw [← meromorphicOrderAt_mul hL hG.meromorphicAt]
    exact (meromorphicOrderAt_congr heq).trans hoH
  calc
    meromorphicOrderAt L s ≤ meromorphicOrderAt L s + meromorphicOrderAt G s :=
      le_add_of_nonneg_right hG.meromorphicOrderAt_nonneg
    _ = 0 := hsum

theorem meromorphicZeroFreeOn_of_physicalMellin {L H : ℂ → ℂ} {f : ℝ → ℂ}
    {b : ℝ} (hL : MeromorphicOn L (rightHalfPlane b))
    (hf : PhysicalProbeBound f b) (hid : MellinDetectorIdentity L f H b) :
    MeromorphicZeroFreeOn L (rightHalfPlane b) := by
  refine ⟨hL, ?_⟩
  intro s hs
  exact order_nonpos_of_analytic_multiplier (hL s hs)
    (physicalMellin_analyticOnNhd hf s hs) (hid.1 s hs)
    (hid.2.1 s hs) (hid.2.2 s hs)

theorem meromorphicZeroFreeOn_of_initial_physicalMellin {L H : ℂ → ℂ} {f : ℝ → ℂ}
    {b : ℝ} (hL : MeromorphicOn L (rightHalfPlane b))
    (hf : PhysicalProbeBound f b) (hid : InitialMellinDetectorIdentity L f H b) :
    MeromorphicZeroFreeOn L (rightHalfPlane b) :=
  meromorphicZeroFreeOn_of_physicalMellin hL hf (hid.continue hL hf)

end HeckeGeneral.Analysis
