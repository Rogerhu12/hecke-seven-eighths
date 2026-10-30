import HeckeSkeleton.LowHybrid.NormalFormBound
import HeckeSkeleton.LowHybrid.NaturalLosses

/-!
# Uniform epsilon bound for the original hybrid energy

This is the final analytic conclusion. Arithmetic adapters supply the finite
support conditions, divisor-envelope bounds, and harmonic-envelope bounds.
All analytic constants are selected before the four scales and all original
coefficient/support data. The actual hybrid energy is on the left throughout.
-/

namespace HeckeSkeleton.LowHybrid.NormalForm

open scoped BigOperators Classical
noncomputable section

variable {I : Type*} [CommMonoid I]

namespace Arithmetic

variable (S : Arithmetic I)

def originalColumnMass (a : I → ℂ) (marks : Finset I) : ℝ :=
  ∑ p ∈ marks, ‖a p‖ ^ 2 / S.normI p

theorem originalColumnMass_nonneg (a : I → ℂ) (marks : Finset I) :
    0 ≤ S.originalColumnMass a marks :=
  Finset.sum_nonneg fun p hp => div_nonneg (sq_nonneg _) (S.norm_nonneg p)

/-- Uniform LOW-HYBRID estimate, with every remaining arithmetic obligation
expressed as finite support or scalar counting data. There is no assumed
normal-form equality, block operator estimate, or hybrid-energy bound. -/
theorem hybrid_energy_of_finite_inputs (sf : I → Prop)
    (hnorm : ∀ x, 1 ≤ S.normI x) (hmu : ∀ x, ‖S.mu x‖ ≤ 1)
    (hq : QuadraticSieveInput S.normI sf S.symbol)
    (hc : CubicSieveInput S.normI sf S.symbol)
    (divisor harmonic : ℝ → ℝ)
    (hd0 : ∀ X : ℝ, 1 ≤ X → 0 ≤ divisor X)
    (hh0 : ∀ X : ℝ, 1 ≤ X → 0 ≤ harmonic X)
    (hd : SubpowerBound divisor) (hh : SubpowerBound harmonic)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C0 : ℝ, 0 < C0 ∧
    ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ L →
    ∀ (rows marks columns cubes ds rs : Finset I) (C : Completion columns cubes)
      (ts cs ms hs : I → I → Finset I)
      (goodPairs goodMC : I → I → Finset (I × I)) (qset jset : Finset I)
      (a : I → ℂ) (beta : I → I → ℂ),
      (∀ n ∈ columns, ∀ b ∈ cubes, ‖beta n b‖ ≤ 1) →
      (∀ b ∈ cubes, S.normI b ≤ B) →
      S.FiniteInputs sf rows marks columns cubes ds rs C ts cs ms hs goodPairs goodMC
        qset jset K (N * B) N L (divisor K ^ 2) (divisor (N * B)) (divisor N)
        (harmonic B) (harmonic N) (harmonic B) →
      (∑ d ∈ ds, S.columnMass a marks d / S.normI d) ≤
        divisor L * S.originalColumnMass a marks →
      (∑ r ∈ rs, 1 / S.normI r) ≤ harmonic K →
      hybridEnergy S.symbol S.cop S.normI a beta rows marks columns cubes ≤
        C0 * (K * N * B * L) ^ eps * (K + N * B) * B *
          (N + L + (N * L) ^ (2 / 3 : ℝ)) * S.originalColumnMass a marks := by
  obtain ⟨eta, CLoss, heta, hCLoss, hLoss⟩ :=
    natural_hybrid_arithmetic_loss_subpower divisor harmonic hd0 hh0 hd hh eps heps
  obtain ⟨CSieve, hCSieve, hFinite⟩ := S.hybridEnergy_finite_bound sf hnorm hmu hq hc eta heta
  refine ⟨CSieve * CLoss, mul_pos hCSieve hCLoss, ?_⟩
  intro K N B L hK hN hB hL rows marks columns cubes ds rs C ts cs ms hs
    goodPairs goodMC qset jset a beta hbeta hcubes H hmass hrecip
  have hNB : 1 ≤ N * B := one_le_mul_of_one_le_of_one_le hN hB
  have hK0 := le_trans zero_le_one hK
  have hN0 := le_trans zero_le_one hN
  have hB0 := le_trans zero_le_one hB
  have hL0 := le_trans zero_le_one hL
  have hNB0 := le_trans zero_le_one hNB
  have hDK := hd0 K hK
  have hDNB := hd0 (N * B) hNB
  have hDN := hd0 N hN
  have hDL := hd0 L hL
  have hHB := hh0 B hB
  have hHN := hh0 N hN
  have hA := S.originalColumnMass_nonneg a marks
  have hR : 0 ≤ ∑ r ∈ rs, 1 / S.normI r :=
    Finset.sum_nonneg fun r hr => div_nonneg zero_le_one (S.norm_nonneg r)
  have hf := hFinite K (N * B) N L hK hNB hN hL rows marks columns cubes ds rs C
    ts cs ms hs goodPairs goodMC qset jset a beta B (divisor K ^ 2)
    (divisor (N * B)) (divisor N) (harmonic B) (harmonic N) (harmonic B)
    hB0 (sq_nonneg _) hDNB hDN hHB hHN hHB hbeta hcubes H
  let front := CSieve * divisor K ^ 2 * divisor (N * B) * divisor N *
    (K * (N * B) * N * L) ^ eta * (K + N * B) * B *
      (N + L + (N * L) ^ (2 / 3 : ℝ)) * harmonic B ^ 2 * harmonic N * harmonic B
  let growth := (K + N * B) * B * (N + L + (N * L) ^ (2 / 3 : ℝ))
  have hfront : 0 ≤ front := by dsimp only [front]; positivity
  have hgrowth : 0 ≤ growth := by dsimp only [growth]; positivity
  have hmassprod :
      (∑ d ∈ ds, S.columnMass a marks d / S.normI d) * (∑ r ∈ rs, 1 / S.normI r) ≤
        (divisor L * S.originalColumnMass a marks) * harmonic K :=
    mul_le_mul hmass hrecip hR (mul_nonneg hDL hA)
  have hpower : (K * (N * B) * N * L) ^ eta =
      (K * N * B) ^ eta * (N * L) ^ eta := by
    rw [show K * (N * B) * N * L = (K * N * B) * (N * L) by ring]
    exact Real.mul_rpow (by positivity) (by positivity)
  have hfull : hybridEnergy S.symbol S.cop S.normI a beta rows marks columns cubes ≤
      CSieve * naturalHybridArithmeticLoss divisor harmonic eta K N B L * growth *
        S.originalColumnMass a marks := by
    calc
      _ ≤ front * ((∑ d ∈ ds, S.columnMass a marks d / S.normI d) *
          (∑ r ∈ rs, 1 / S.normI r)) := by simpa only [front, mul_assoc] using hf
      _ ≤ front * ((divisor L * S.originalColumnMass a marks) * harmonic K) :=
        mul_le_mul_of_nonneg_left hmassprod hfront
      _ = _ := by dsimp only [front, growth]; rw [hpower]; unfold naturalHybridArithmeticLoss; ring
  have hloss := hLoss K N B L hK hN hB hL
  calc
    _ ≤ CSieve * naturalHybridArithmeticLoss divisor harmonic eta K N B L * growth *
        S.originalColumnMass a marks := hfull
    _ ≤ CSieve * (CLoss * (K * N * B * L) ^ eps) * growth *
        S.originalColumnMass a marks := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hloss (le_of_lt hCSieve)) hgrowth) hA
    _ = _ := by dsimp only [growth]; ring

end Arithmetic

#print axioms Arithmetic.hybrid_energy_of_finite_inputs

end
end HeckeSkeleton.LowHybrid.NormalForm
