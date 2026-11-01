import HeckeSkeleton.Moments.MOM_INV_INDUCTION.EnergyClosure

/-!
# Initial marked inverse reduction

This file consumes the initial masked Poisson reduction of the proof of
Theorem 4.1.  The overlap length `G`, frozen puncture length `P`, and
clipping correction stay explicit.  The initial child margins are proved
from the original two marked margins, rather than assumed to follow from
the old capped inverse region.

`InitialEnergy` is a finite reduction to canonical child energies, not an
inverse moment estimate.  Constructing it for a given source still
requires the source's actual first Poisson identity, common masks and
fibre count.  The independent construction is not supplied by the
numerical margin hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open scoped BigOperators
open HeckePort.Moments

/-- The overlap tuples and distinct frozen triples after their positive
norm counts have been extracted. -/
structure InitialData (α : Type*) where
  nodes : Finset α
  weight : α → ℝ
  weight_nonneg : ∀ y ∈ nodes, 0 ≤ weight y
  weight_mass : ∑ y ∈ nodes, weight y ≤ 1
  overlap : α → ℝ
  puncture : α → ℝ
  clipping : α → ℝ

/-- Actual initial child lengths, with all support errors displayed. -/
structure InitialGeometry {α : Type*} (F M Q cap : α → ℝ)
    (m r z eta tau : ℝ) (s : InitialData α) : Prop where
  total_length : ∀ y ∈ s.nodes,
    F y = initialF r z (s.overlap y) (s.puncture y) (s.clipping y)
  row_length : ∀ y ∈ s.nodes,
    M y = initialM m r z (s.overlap y) (s.puncture y) eta tau
  mark_cap : ∀ y ∈ s.nodes, cap y = z - s.overlap y
  overlap_nonneg : ∀ y ∈ s.nodes, 0 ≤ s.overlap y
  overlap_le : ∀ y ∈ s.nodes, s.overlap y ≤ z
  puncture_lower : ∀ y ∈ s.nodes, -2 * eta ≤ s.puncture y
  puncture_upper : ∀ y ∈ s.nodes, Q y ≤ s.puncture y + s.overlap y + 3 * eta
  clipping_nonneg : ∀ y ∈ s.nodes, 0 ≤ s.clipping y
  clipping_le : ∀ y ∈ s.nodes, s.clipping y ≤ 3 * eta

def initialPrefactor (m r z G P : ℝ) : ℝ := m - 2 * (r + z - 2 * G) + P

/-- Principal and frequency-tail terms have already been bounded by
the two displayed `Z^m` terms.  The common finite profile factor is `S`.
The residual child energy retains its own label measure. -/
def InitialEnergy {α : Type*} (E F : α → ℝ)
    (source Z m r z eta pi S : ℝ) (s : InitialData α) : Prop :=
  source ≤ S * (Z ^ m + Z ^ m + Z ^ (5 * eta + pi) *
    ∑ y ∈ s.nodes, s.weight y *
      (Z ^ (initialPrefactor m r z (s.overlap y) (s.puncture y) +
        s.puncture y + F y) * E y))

/-- Initial strict margins, including the overlap and puncture gains. -/
theorem initial_children_margins {α : Type*} {F M Q cap : α → ℝ}
    {m r z eta tau c₁ c₂ : ℝ} {s : InitialData α}
    (g : InitialGeometry F M Q cap m r z eta tau s)
    (h₁ : r + 2 * z ≤ m - c₁) (h₂ : 2 * r + 8 * z ≤ 3 * m - c₂)
    (hc : 0 ≤ min c₁ c₂) (heta : eta ≤ min c₁ c₂ / 100)
    (htau : tau ≤ min c₁ c₂ / 100) :
    ∀ y ∈ s.nodes, CanonicalMargins (F y) (M y) (Q y) (cap y) (3 * min c₁ c₂ / 4) := by
  intro y hy
  rw [g.total_length y hy, g.row_length y hy, g.mark_cap y hy]
  exact initial_margins h₁ h₂ (g.overlap_nonneg y hy) (g.puncture_lower y hy)
    (g.puncture_upper y hy) hc (g.clipping_nonneg y hy) heta htau

/-- The first marked margin also gives the initial row range.  Thus the
finite descent can use the source's fixed upper range, chosen before any
Poisson child or clipping parameter. -/
theorem initial_children_row_upper {α : Type*} {F M Q cap : α → ℝ}
    {m r z eta tau margin upper : ℝ} {s : InitialData α}
    (g : InitialGeometry F M Q cap m r z eta tau s)
    (hz : 0 ≤ z) (hm : m ≤ upper) (hmargin : r + 2 * z ≤ m - margin)
    (hloss : 10 * eta + tau ≤ 2 * margin) :
    ∀ y ∈ s.nodes, M y ≤ upper := by
  intro y hy
  have hG := g.overlap_nonneg y hy
  have hP := g.puncture_lower y hy
  rw [g.row_length y hy]
  unfold initialM
  linarith

/-- The same source range bounds the initial column-and-label length.
Together with `budget_total_length_bound`, this gives one bounded length
range for all descendants. -/
theorem initial_children_total_upper {α : Type*} {F M Q cap : α → ℝ}
    {m r z eta tau margin upper : ℝ} {s : InitialData α}
    (g : InitialGeometry F M Q cap m r z eta tau s)
    (hz : 0 ≤ z) (hm : m ≤ upper) (hmargin : r + 2 * z ≤ m - margin)
    (hloss : 5 * eta ≤ margin) :
    ∀ y ∈ s.nodes, F y ≤ upper := by
  intro y hy
  have hG := g.overlap_nonneg y hy
  have hP := g.puncture_lower y hy
  have hclip := g.clipping_le y hy
  rw [g.total_length y hy]
  unfold initialF
  linarith

/-- The two restored child normalizations use the clipping error twice. -/
theorem initial_normalized_prefactor_le {α : Type*} {F M Q cap : α → ℝ}
    {m r z eta tau : ℝ} {s : InitialData α}
    (g : InitialGeometry F M Q cap m r z eta tau s)
    (y : α) (hy : y ∈ s.nodes) (pi e : ℝ) :
    5 * eta + pi +
      (initialPrefactor m r z (s.overlap y) (s.puncture y) + s.puncture y + F y) +
      (F y + e) ≤ m + 11 * eta + pi + e := by
  have hid := initial_prefactor_identity m r z (s.overlap y) (s.puncture y)
  have hc := g.clipping_le y hy
  rw [g.total_length y hy]
  unfold initialPrefactor initialF at *
  linarith

/-- A finite positive measure transports uniform normalized child
estimates without charging its mass a second time. -/
theorem weighted_energy_transport {α : Type*}
    (nodes : Finset α) (weight E F prefactor : α → ℝ)
    {Z a B e target : ℝ}
    (hZ : 1 ≤ Z) (hB : 0 ≤ B)
    (hw : ∀ y ∈ nodes, 0 ≤ weight y) (hmass : ∑ y ∈ nodes, weight y ≤ 1)
    (hchild : ∀ y ∈ nodes, E y ≤ B * Z ^ (F y + e))
    (hexponent : ∀ y ∈ nodes, a + prefactor y + (F y + e) ≤ target) :
    Z ^ a * (∑ y ∈ nodes, weight y * (Z ^ prefactor y * E y)) ≤ B * Z ^ target := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hterm (y : α) (hy : y ∈ nodes) :
      Z ^ a * (Z ^ prefactor y * E y) ≤ B * Z ^ target := by
    calc
      _ ≤ Z ^ a * (Z ^ prefactor y * (B * Z ^ (F y + e))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hchild y hy) (Real.rpow_nonneg hz.le _))
          (Real.rpow_nonneg hz.le _)
      _ = B * Z ^ (a + prefactor y + (F y + e)) := by
        simp only [Real.rpow_add hz]
        ring
      _ ≤ B * Z ^ target := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ (hexponent y hy)) hB
  calc
    _ = ∑ y ∈ nodes, weight y * (Z ^ a * (Z ^ prefactor y * E y)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ ≤ ∑ y ∈ nodes, weight y * (B * Z ^ target) :=
      Finset.sum_le_sum (fun y hy => mul_le_mul_of_nonneg_left (hterm y hy) (hw y hy))
    _ = (∑ y ∈ nodes, weight y) * (B * Z ^ target) := (Finset.sum_mul ..).symm
    _ ≤ 1 * (B * Z ^ target) :=
      mul_le_mul_of_nonneg_right hmass (mul_nonneg hB (Real.rpow_nonneg hz.le _))
    _ = _ := one_mul _

/-- The marked inverse moment follows from the initial reduction and
the already closed canonical recursion, with the paper's `11η + π`
initial loss. -/
theorem initial_energy_bound {α : Type*} {E F M Q cap : α → ℝ}
    {source Z m r z eta tau pi S B e : ℝ} {s : InitialData α}
    (hZ : 1 ≤ Z) (heta : 0 ≤ eta) (hpi : 0 ≤ pi)
    (hS : 0 ≤ S) (hB : 1 ≤ B) (he : 0 ≤ e)
    (g : InitialGeometry F M Q cap m r z eta tau s)
    (hsource : InitialEnergy E F source Z m r z eta pi S s)
    (hchild : ∀ y ∈ s.nodes, E y ≤ B * Z ^ (F y + e)) :
    source ≤ 3 * S * B * Z ^ (m + 11 * eta + pi + e) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hBn : 0 ≤ B := zero_le_one.trans hB
  let T := B * Z ^ (m + 11 * eta + pi + e)
  have hprincipal : Z ^ m ≤ T := by
    calc
      _ ≤ Z ^ (m + 11 * eta + pi + e) :=
        Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
      _ ≤ _ := by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg hz.le _)
  have hsum := weighted_energy_transport s.nodes s.weight E F
    (fun y => initialPrefactor m r z (s.overlap y) (s.puncture y) + s.puncture y + F y)
    hZ hBn s.weight_nonneg s.weight_mass hchild
    (fun y hy => initial_normalized_prefactor_le g y hy pi e)
  apply hsource.trans
  calc
    _ ≤ S * (3 * T) := mul_le_mul_of_nonneg_left (by dsimp [T] at *; linarith) hS
    _ = _ := by dsimp [T]; ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION
