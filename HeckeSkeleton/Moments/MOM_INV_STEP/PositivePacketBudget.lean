import HeckeSkeleton.Moments.MOM_INV_STEP.FixedTripleEnergy
import HeckeSkeleton.Moments.MOM_INV_STEP.CenteredChildGeometry

/-!
# Uniform positive child budgets at the actual centered scale

The positive energy used under the second common Mellin measure keeps the
frozen-triple weight inside its sum. Its total mass is estimated from the
actual three ideal norms, once. The energy premise is solely the smaller
canonical child's normalized bound. The physical powers include the true
center error before clipping and the finer internal mesh.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOMInvStep.PositivePacketBudget

open NumberField IsDedekindDomain FixedTripleFibers FixedTripleEnergy
open scoped Classical BigOperators NumberField

variable {K : Type*} [Field K] [NumberField K] {Sector : Type*}
variable {transport : Ideal (𝓞 K) → Ideal (𝓞 K) → (Sector ≃ Sector)}
variable {slotCap Jo Jn : ℕ}

def positiveEnergy
    (P : ReconstructionPacket (K := K) (Sector := Sector) transport slotCap Jo Jn)
    (F : SecondChild K Sector → ℂ) : ℝ :=
  ∑ γ ∈ P.triples, tripleDivisorWeight slotCap γ * P.energy F γ

theorem positiveEnergy_nonneg
    (P : ReconstructionPacket (K := K) (Sector := Sector) transport slotCap Jo Jn)
    (F : SecondChild K Sector → ℂ) : 0 ≤ positiveEnergy P F := by
  apply Finset.sum_nonneg
  intro γ hγ
  exact mul_nonneg (tripleDivisorWeight_nonneg slotCap γ)
    (childEnergy_nonneg slotCap P.labels P.rows F γ)

theorem positiveEnergy_le
    (P : ReconstructionPacket (K := K) (Sector := Sector) transport slotCap Jo Jn)
    (F : SecondChild K Sector → ℂ) (H : ℝ)
    (hF : ∀ γ ∈ P.triples, P.energy F γ ≤ H) :
    positiveEnergy P F ≤ H * P.tripleMass := by
  rw [positiveEnergy, ReconstructionPacket.tripleMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro γ hγ
  simpa only [mul_comm H] using
    mul_le_mul_of_nonneg_left (hF γ hγ) (tripleDivisorWeight_nonneg slotCap γ)

/-- A positive source block, in the form needed inside the common
Mellin integrals. The constant precedes the complete packet, its tests,
all physical lengths and all original prime lists. -/
theorem exists_centered_positive_budget
    (transport : Ideal (𝓞 K) → Ideal (𝓞 K) → (Sector ≃ Sector))
    (slotCap : ℕ) (massEps : ℝ) (hmassEps : 0 < massEps) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Jo Jn : ℕ}
      (P : ReconstructionPacket (K := K) (Sector := Sector) transport slotCap Jo Jn)
      (Z M r ell V delta A B R j t g theta v h eta tau pi eps Nactual Cchild : ℝ),
      1 ≤ Z → 0 ≤ h → h ≤ eta / 16 → 0 ≤ Cchild →
      secondFormalColumn r A B t g v - 5 * h ≤ Nactual →
      Nactual ≤ secondFormalColumn r A B t g v + 8 * h →
      -2 * h ≤ Nactual →
      massEps * (secondCount ell R j t g theta + 11 * h / 2) ≤ pi →
      (∀ x ∈ originalSource P.source P.oldLists P.newLists P.keep,
        (Ideal.absNorm x.outer.q0 : ℝ) ≤ Z ^ (ell + R / 2 - j + 5 * h / 2) ∧
        (Ideal.absNorm x.outer.quotient : ℝ) ≤ Z ^ (t + h) ∧
        (Ideal.absNorm x.outer.residual : ℝ) ≤ Z ^ (g - theta + 2 * h)) →
      ∀ F : SecondChild K Sector → ℂ,
      (∀ γ ∈ P.triples,
        normalizedChildEnergy Z (max 0 Nactual)
          (secondFormalLabel B theta v j + 4 * h)
          slotCap P.labels P.rows F γ ≤
        Cchild * Z ^ (max 0 Nactual + secondFormalLabel B theta v j + 4 * h + eps)) →
      Z ^ (firstKappa M r ell V delta A B R + (9 / 2 : ℝ) * h) *
        Z ^ (secondLambda M r ell V delta A B j t g theta + 18 * h + tau) *
        positiveEnergy P F ≤
      C * Cchild * Z ^ (r + 3 * ell + V + 40 * eta + tau + pi + eps) := by
  obtain ⟨C, hC, hmass⟩ := ReconstructionPacket.exists_tripleMass_bound_of_norm_box
    (K := K) (Sector := Sector) (sectorTransport := transport)
    (slotCap := slotCap) massEps hmassEps
  refine ⟨C, hC, ?_⟩
  intro Jo Jn P Z M r ell V delta A B R j t g theta v h eta tau pi eps Nactual Cchild
    hZ hh hmesh hCchild hlo hhi hlive hloss hsource F hF
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hmass' : P.tripleMass ≤
      C * Z ^ (secondCount ell R j t g theta + 11 * h / 2 + pi) := by
    have hm := hmass P (Z ^ (ell + R / 2 - j + 5 * h / 2)) (Z ^ (t + h))
      (Z ^ (g - theta + 2 * h)) (Real.rpow_pos_of_pos hz _)
      (Real.rpow_pos_of_pos hz _) (Real.rpow_pos_of_pos hz _) hsource
    have hprod : Z ^ (ell + R / 2 - j + 5 * h / 2) * Z ^ (t + h) *
        Z ^ (g - theta + 2 * h) =
        Z ^ (secondCount ell R j t g theta + 11 * h / 2) := by
      rw [← Real.rpow_add hz, ← Real.rpow_add hz]
      congr 1
      unfold secondCount
      ring
    rw [hprod, ← Real.rpow_mul hz.le] at hm
    apply hm.trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.rpow_le_rpow_of_exponent_le hZ
    nlinarith
  let E := 2 * (max 0 Nactual + secondFormalLabel B theta v j + 4 * h) + eps
  have hraw : ∀ γ ∈ P.triples, P.energy F γ ≤ Cchild * Z ^ E := by
    intro γ hγ
    have hb := childEnergy_bound_of_normalized Z (max 0 Nactual)
      (secondFormalLabel B theta v j + 4 * h) eps Cchild hz
      slotCap P.labels P.rows F γ
      (by simpa only [add_assoc] using hF γ hγ)
    simpa only [E, add_assoc] using hb
  have hp := (positiveEnergy_le P F (Cchild * Z ^ E) hraw).trans
    (mul_le_mul_of_nonneg_left hmass' (by positivity))
  have hscaled := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ Z ^ (firstKappa M r ell V delta A B R + (9 / 2 : ℝ) * h) *
        Z ^ (secondLambda M r ell V delta A B j t g theta + 18 * h + tau) by
      positivity)
  have hbudget := CenteredChildGeometry.physical_power_budget
    Z M r ell V delta A B R j t g theta v h eta tau pi eps Nactual
    hZ hh hmesh hlo hhi hlive
  apply hscaled.trans
  convert mul_le_mul_of_nonneg_left hbudget (mul_nonneg hC.le hCchild) using 1 <;>
    dsimp only [E] <;> ring

end HeckeSkeleton.Moments.MOMInvStep.PositivePacketBudget

end

