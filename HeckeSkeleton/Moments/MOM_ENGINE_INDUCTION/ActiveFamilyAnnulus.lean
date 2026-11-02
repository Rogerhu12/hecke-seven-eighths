import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ActiveChildAnnulus
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.MovingEngineOutput

/-!
# Tight supports on the same finite normalized family

The family itself decides which original source pairs are active and
chooses their fixed capacity removals. Its active-label proof supplies
the nonzero witnesses used below. The resulting windows concern exactly
its public left and right data; there is no second family selection.

The arithmetic part of the existing moving-child admissibility is
retained when the actual profile-window proof is strengthened.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain
open DedekindZetaZeroFree (SArithmeticData)
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.Moments.EngineStep
open ActiveChildAnnulus

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {V Λ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : ℝ}

/-- The two true active sources supply their own clipping bounds. All
Schwartz radii and the public frozen children remain unchanged. -/
theorem actualNormalizedFamily_active_windows
    (family : ActualNormalizedPairFamily A σ V Λ ω ψ Z) (labels : Finset Λ)
    {lo hi : ℝ} (hlo : 0 ≤ lo) (hhi : 1 ≤ hi)
    {sourceOrders childOrders : Finset (ℕ × ℕ)} {broad : Set ℝ}
    {leftBudget rightBudget : Λ → V → ℝ}
    (originalLeft : ∀ b ∈ labels, ∀ ξ,
      RawProfileWindow Set.univ Set.univ (Set.Icc lo hi) sourceOrders
        ((family.leftCalibration b).data ξ) (leftBudget b ξ))
    (originalRight : ∀ b ∈ labels, ∀ ξ,
      RawProfileWindow Set.univ Set.univ (Set.Icc lo hi) sourceOrders
        ((family.rightCalibration b).data ξ) (rightBudget b ξ))
    (clippedLeft : ∀ b ∈ labels, ∀ ξ,
      RawProfileWindow Set.univ Set.univ broad childOrders
        ((family.leftCalibration b).clippedData ξ) ((family.leftCapacity b).radius ξ))
    (clippedRight : ∀ b ∈ labels, ∀ ξ,
      RawProfileWindow Set.univ Set.univ broad childOrders
        ((family.rightCalibration b).clippedData ξ) ((family.rightCapacity b).radius ξ)) :
    ∀ (b : family.active labels) (ξ : V),
      InFixedProfileWindow Set.univ Set.univ (Set.Icc (lo / hi) hi) childOrders
        (family.leftData labels b ξ) ∧
      InFixedProfileWindow Set.univ Set.univ (Set.Icc (lo / hi) hi) childOrders
        (family.rightData labels b ξ) := by
  intro b ξ
  have hb := Finset.mem_filter.mp b.property
  exact ⟨(active_child_windows (family.leftChild labels b) hlo hhi
      (originalLeft b.val hb.1) (clippedLeft b.val hb.1)
      (fun _ _ _ => Set.mem_univ _) (fun _ => Set.mem_univ _) hb.2.1 ξ).2,
    (active_child_windows (family.rightChild labels b) hlo hhi
      (originalRight b.val hb.1) (clippedRight b.val hb.1)
      (fun _ _ _ => Set.mem_univ _) (fun _ => Set.mem_univ _) hb.2.2 ξ).2⟩

/-- The narrower original prime support survives on both public
children of every retained original source label. -/
theorem actualNormalizedFamily_prime_support
    (family : ActualNormalizedPairFamily A σ V Λ ω ψ Z) (labels : Finset Λ)
    {primeWindow : Set ℝ}
    (left : ∀ b ∈ labels, ∀ ξ i t,
      Function.support ((((family.leftCalibration b).data ξ).geometry.slots i).profile t) ⊆
        primeWindow)
    (right : ∀ b ∈ labels, ∀ ξ i t,
      Function.support ((((family.rightCalibration b).data ξ).geometry.slots i).profile t) ⊆
        primeWindow) :
    ∀ (b : family.active labels) (ξ : V),
      (∀ i t, Function.support (((family.leftData labels b ξ).geometry.slots i).profile t) ⊆
        primeWindow) ∧
      (∀ i t, Function.support (((family.rightData labels b ξ).geometry.slots i).profile t) ⊆
        primeWindow) := by
  intro b ξ
  have hb : b.val ∈ labels := (Finset.mem_filter.mp b.property).1
  exact ⟨frozen_child_prime_support (family.leftChild labels b) (left b.val hb) ξ,
    frozen_child_prime_support (family.rightChild labels b) (right b.val hb) ξ⟩

/-- The actual prime supports at the calibration heights already
suffice for the public frozen family. -/
theorem actualNormalizedFamily_prime_support_at
    (family : ActualNormalizedPairFamily A σ V Λ ω ψ Z) (labels : Finset Λ)
    {primeWindow : Set ℝ}
    (left : ∀ b ∈ labels, ∀ ξ i,
      Function.support ((((family.leftCalibration b).data ξ).geometry.slots i).profile
        ((family.leftCalibration b).height ξ)) ⊆ primeWindow)
    (right : ∀ b ∈ labels, ∀ ξ i,
      Function.support ((((family.rightCalibration b).data ξ).geometry.slots i).profile
        ((family.rightCalibration b).height ξ)) ⊆ primeWindow) :
    ∀ (b : family.active labels) (ξ : V),
      (∀ i t, Function.support (((family.leftData labels b ξ).geometry.slots i).profile t) ⊆
        primeWindow) ∧
      (∀ i t, Function.support (((family.rightData labels b ξ).geometry.slots i).profile t) ⊆
        primeWindow) := by
  intro b ξ
  have hb : b.val ∈ labels := (Finset.mem_filter.mp b.property).1
  exact ⟨frozen_child_prime_support_at (family.leftChild labels b) (left b.val hb) ξ,
    frozen_child_prime_support_at (family.rightChild labels b) (right b.val hb) ξ⟩

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {Q : Type*} {parent child : MomentData K ω ψ} {parameters : RealParameters}
variable {rowDomain : Set (NonzeroIdeal K)} {broad narrow : Set ℝ}
variable {orders : Finset (ℕ × ℕ)}

/-- Strengthening the support proof leaves the complete moving recipe,
the combined row budget, arithmetic atoms and slot injection intact. -/
def movingChild_withWindow
    (h : MovingEngineChildAdmissible A P R Q parent rowDomain broad orders Z child parameters)
    (window : InFixedProfileWindow rowDomain Set.univ narrow orders child) :
    MovingEngineChildAdmissible A P R Q parent rowDomain narrow orders Z child parameters where
  engine := ⟨window, h.engine.2⟩
  rows := h.rows
  plain_background := h.plain_background
  profiles := h.profiles
  arithmetic := h.arithmetic
  slots := h.slots

end HeckeSkeleton.Moments.EngineInduction

#print axioms HeckeSkeleton.Moments.EngineInduction.actualNormalizedFamily_active_windows
#print axioms HeckeSkeleton.Moments.EngineInduction.actualNormalizedFamily_prime_support
#print axioms HeckeSkeleton.Moments.EngineInduction.movingChild_withWindow
