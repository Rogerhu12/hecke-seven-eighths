import HeckeSkeleton.LowHybrid.SieveBounds
import HeckeSkeleton.LowHybrid.Weighted
import HeckeSkeleton.LowHybrid.Transpose

/-!
# Zero-extended product operators from the two squarefree sieves

The weighted proof uses rectangular index sets, while the arithmetic sieves
apply only to squarefree products. The kernels in this file are exactly zero
outside explicitly specified good product pairs. Both rectangular operator
bounds are proved from the squarefree sieves and their product-fiber counts.

No sieve over nonsquarefree products is assumed. The quadratic input is
transposed using finite complex duality; its denominator is therefore the row,
exactly as in hybridRow. The cubic input keeps its original orientation.
-/

namespace HeckeSkeleton.LowHybrid

open scoped BigOperators
noncomputable section

private theorem sum_zero_extension {X A : Type*} [DecidableEq X] [AddCommMonoid A]
    (ambient good : Finset X) (f : X → A) (hgood : good ⊆ ambient) :
    (∑ x ∈ ambient, if x ∈ good then f x else 0) = ∑ x ∈ good, f x := by
  have hf : ambient.filter (fun x => x ∈ good) = good := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun hx => hx.2, fun hx => ⟨hgood hx, hx⟩⟩
  rw [← Finset.sum_filter, hf]

/-- The quadratic product kernel is zero outside its actual good pairs. -/
def zeroExtendedQuadratic {K M H J : Type*} [DecidableEq M] [DecidableEq H]
    (good : Finset (M × H)) (phi : M × H → J) (q : K → J → ℂ) :
    K → M → H → ℂ :=
  fun k m h => if (m, h) ∈ good then q k (phi (m, h)) else 0

/-- The cubic row kernel is zero outside its actual good product rows. -/
def zeroExtendedCubic {M C J P : Type*} [DecidableEq M] [DecidableEq C]
    (good : Finset (M × C)) (phi : M × C → J) (chi : P → J → ℂ) :
    M → C → P → ℂ :=
  fun m c p => if (m, c) ∈ good then chi p (phi (m, c)) else 0

/-- Extend a squarefree product-column sieve to a rectangle by literal zeros.
The only loss is the good product map's explicit fiber multiplicity. -/
theorem zero_extended_column_fiber_sieve
    {K M H J : Type*} [DecidableEq M] [DecidableEq H] [DecidableEq J]
    (rows : Finset K) (ms : Finset M) (hs : Finset H)
    (good : Finset (M × H)) (target : Finset J)
    (phi : M × H → J) (q : K → J → ℂ) (Q D : ℝ)
    (hQ : 0 ≤ Q) (hD : 0 ≤ D) (hgood : good ⊆ ms ×ˢ hs)
    (hmap : ∀ x ∈ good, phi x ∈ target)
    (hfiber : ∀ j ∈ target, ((good.filter fun x => phi x = j).card : ℝ) ≤ D)
    (hsieve : ∀ z : J → ℂ,
      (∑ k ∈ rows, ‖∑ j ∈ target, q k j * z j‖ ^ 2) ≤
        Q * ∑ j ∈ target, ‖z j‖ ^ 2)
    (f : M → H → ℂ) :
    (∑ k ∈ rows, ‖∑ m ∈ ms, ∑ h ∈ hs,
      zeroExtendedQuadratic good phi q k m h * f m h‖ ^ 2) ≤
      Q * D * (∑ m ∈ ms, ∑ h ∈ hs, ‖f m h‖ ^ 2) := by
  classical
  have heq (k : K) :
      (∑ m ∈ ms, ∑ h ∈ hs,
        zeroExtendedQuadratic good phi q k m h * f m h) =
        ∑ x ∈ good, q k (phi x) * f x.1 x.2 := by
    calc
      _ = ∑ x ∈ ms ×ˢ hs,
          (if x ∈ good then q k (phi x) else 0) * f x.1 x.2 := by
        simp only [zeroExtendedQuadratic, Finset.sum_product]
      _ = ∑ x ∈ ms ×ˢ hs,
          if x ∈ good then q k (phi x) * f x.1 x.2 else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        split_ifs <;> simp
      _ = _ := sum_zero_extension (ms ×ˢ hs) good
        (fun x => q k (phi x) * f x.1 x.2) hgood
  have hmass :
      (∑ x ∈ good, ‖f x.1 x.2‖ ^ 2) ≤
      ∑ x ∈ ms ×ˢ hs, ‖f x.1 x.2‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hgood (fun _ _ _ => sq_nonneg _)
  calc
    _ = ∑ k ∈ rows, ‖∑ x ∈ good, q k (phi x) * f x.1 x.2‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [heq]
    _ ≤ Q * D * ∑ x ∈ good, ‖f x.1 x.2‖ ^ 2 :=
      column_fiber_sieve rows good target phi q (fun x => f x.1 x.2)
        Q D hQ hmap hfiber hsieve
    _ ≤ Q * D * ∑ x ∈ ms ×ˢ hs, ‖f x.1 x.2‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hmass (mul_nonneg hQ hD)
    _ = _ := by rw [Finset.sum_product]

/-- Extend the cubic sieve to a rectangle by zero rows. Bad product rows
contribute exactly zero, so no sieve hypothesis is imposed on them. -/
theorem zero_extended_row_fiber_sieve
    {M C J P : Type*} [DecidableEq M] [DecidableEq C] [DecidableEq J]
    (ms : Finset M) (cs : Finset C) (good : Finset (M × C))
    (target : Finset J) (columns : Finset P)
    (phi : M × C → J) (chi : P → J → ℂ) (S D : ℝ) (hD : 0 ≤ D)
    (hgood : good ⊆ ms ×ˢ cs)
    (hmap : ∀ x ∈ good, phi x ∈ target)
    (hfiber : ∀ j ∈ target, ((good.filter fun x => phi x = j).card : ℝ) ≤ D)
    (hsieve : ∀ z : P → ℂ,
      (∑ j ∈ target, ‖∑ p ∈ columns, z p * chi p j‖ ^ 2) ≤
        S * ∑ p ∈ columns, ‖z p‖ ^ 2)
    (a : P → ℂ) :
    (∑ m ∈ ms, ∑ c ∈ cs,
      ‖∑ p ∈ columns, a p * zeroExtendedCubic good phi chi m c p‖ ^ 2) ≤
      S * D * ∑ p ∈ columns, ‖a p‖ ^ 2 := by
  classical
  have heq :
      (∑ m ∈ ms, ∑ c ∈ cs,
        ‖∑ p ∈ columns, a p * zeroExtendedCubic good phi chi m c p‖ ^ 2) =
        ∑ x ∈ good, ‖∑ p ∈ columns, a p * chi p (phi x)‖ ^ 2 := by
    calc
      _ = ∑ x ∈ ms ×ˢ cs,
          if x ∈ good then ‖∑ p ∈ columns, a p * chi p (phi x)‖ ^ 2 else 0 := by
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro c hc
        by_cases hmc : (m, c) ∈ good
        · simp only [zeroExtendedCubic, if_pos hmc]
        · simp only [zeroExtendedCubic, if_neg hmc, mul_zero, Finset.sum_const_zero,
            norm_zero, zero_pow (by decide : 2 ≠ 0)]
      _ = _ := sum_zero_extension (ms ×ˢ cs) good
        (fun x => ‖∑ p ∈ columns, a p * chi p (phi x)‖ ^ 2) hgood
  rw [heq]
  exact (row_fiber_sieve good target columns phi chi a D S hD hmap hfiber hsieve).trans_eq
    (by ring)

/-- The dyad-free weighted estimate from precisely the two arithmetic-form
sieve inputs. Both product kernels are zero outside their good squarefree
product supports. The constant is chosen before all scales and finite data.

Dq and Dc are the two different product-fiber costs. The surviving mass and
all three harmonic sums are explicit, along with the original beta budget.
-/
theorem weighted_energy_from_sieve_inputs {I : Type*} [DecidableEq I]
    (normI : I → ℝ) (sf : I → Prop) (symbol : I → I → ℂ)
    (hq : QuadraticSieveInput normI sf symbol)
    (hc : CubicSieveInput normI sf symbol) (eps : ℝ) (heps : 0 < eps) :
    ∃ C0 : ℝ, 0 < C0 ∧
    ∀ K0 Y0 N0 L0 : ℝ, 1 ≤ K0 → 1 ≤ Y0 → 1 ≤ N0 → 1 ≤ L0 →
    ∀ (rows ts cs ms hs ps qset jset : Finset I)
      (goodPairs goodMC : Finset (I × I))
      (qprod cprod : I × I → I)
      (a : I → I → I → ℂ) (beta : I → I → I → I → ℂ)
      (rowMask : I → I → ℂ) (wt wc wh : I → ℝ)
      (Dq Dc Rbudget A : ℝ),
      0 ≤ Dq → 0 ≤ Dc → 0 ≤ Rbudget → 0 ≤ A →
      (∀ k ∈ rows, sf k ∧ normI k ≤ K0) →
      (∀ j ∈ qset, sf j ∧ normI j ≤ Y0) →
      (∀ j ∈ jset, sf j ∧ normI j ≤ N0) →
      (∀ p ∈ ps, sf p ∧ normI p ≤ L0) →
      goodPairs ⊆ ms ×ˢ hs → goodMC ⊆ ms ×ˢ cs →
      (∀ x ∈ goodPairs, qprod x ∈ qset) →
      (∀ j ∈ qset, ((goodPairs.filter fun x => qprod x = j).card : ℝ) ≤ Dq) →
      (∀ x ∈ goodMC, cprod x ∈ jset) →
      (∀ j ∈ jset, ((goodMC.filter fun x => cprod x = j).card : ℝ) ≤ Dc) →
      (∀ t ∈ ts, 0 < wt t) → (∀ c ∈ cs, 0 < wc c) → (∀ h ∈ hs, 0 < wh h) →
      (∀ k ∈ rows, ∀ t ∈ ts, ‖rowMask k t‖ ≤ 1) →
      (∀ t ∈ ts, ∀ c ∈ cs, ∀ m ∈ ms, ∀ h ∈ hs,
        wt t * wc c * ‖beta t c m h‖ ^ 2 ≤ Rbudget / (wt t * wh h)) →
      (∀ t ∈ ts, ∀ h ∈ hs, (∑ p ∈ ps, ‖a t h p‖ ^ 2) ≤ A) →
      (∑ k ∈ rows, ‖∑ t ∈ ts, ∑ c ∈ cs, rowMask k t *
        (∑ m ∈ ms, ∑ h ∈ hs,
          zeroExtendedQuadratic goodPairs qprod (fun k j => symbol k j ^ 3) k m h *
            (beta t c m h * (∑ p ∈ ps, a t h p *
              zeroExtendedCubic goodMC cprod
                (fun p j => symbol p j ^ (-2 : ℤ)) m c p)))‖ ^ 2) ≤
        C0 * (K0 * Y0 * N0 * L0) ^ eps * (K0 + Y0) * Dq * Dc *
          (N0 + L0 + (N0 * L0) ^ (2 / 3 : ℝ)) * Rbudget * A *
          (∑ t ∈ ts, 1 / wt t) ^ 2 *
            (∑ c ∈ cs, 1 / wc c) * (∑ h ∈ hs, 1 / wh h) := by
  classical
  obtain ⟨Cq, hCq, hquadratic⟩ :=
    quadratic_sieve_input_transpose normI sf symbol hq eps heps
  obtain ⟨Cc, hCc, hcubic⟩ := hc eps heps
  refine ⟨Cq * Cc, mul_pos hCq hCc, ?_⟩
  intro K0 Y0 N0 L0 hK hY hN hL rows ts cs ms hs ps qset jset
    goodPairs goodMC qprod cprod a beta rowMask wt wc wh Dq Dc Rbudget A
    hDq hDc hR hA hrows hqset hjset hps hgoodPairs hgoodMC
    hqmap hqfiber hcmap hcfiber hwt hwc hwh hmask hbudget ha
  let Q := Cq * (K0 * Y0) ^ eps * (K0 + Y0)
  let S := Cc * (N0 * L0) ^ eps * (N0 + L0 + (N0 * L0) ^ (2 / 3 : ℝ))
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hqp : ∀ f : I → I → ℂ,
      (∑ k ∈ rows, ‖∑ m ∈ ms, ∑ h ∈ hs,
        zeroExtendedQuadratic goodPairs qprod (fun k j => symbol k j ^ 3) k m h *
          f m h‖ ^ 2) ≤
        (Q * Dq) * (∑ m ∈ ms, ∑ h ∈ hs, ‖f m h‖ ^ 2) := by
    intro f
    apply zero_extended_column_fiber_sieve rows ms hs goodPairs qset qprod
      (fun k j => symbol k j ^ 3) Q Dq hQ hDq hgoodPairs hqmap hqfiber
      (f := f)
    intro z
    simpa only [Q, mul_comm] using hquadratic K0 Y0 hK hY rows qset hrows hqset z
  have hcp : ∀ z : I → ℂ,
      (∑ m ∈ ms, ∑ c ∈ cs,
        ‖∑ p ∈ ps, z p * zeroExtendedCubic goodMC cprod
          (fun p j => symbol p j ^ (-2 : ℤ)) m c p‖ ^ 2) ≤
        (S * Dc) * ∑ p ∈ ps, ‖z p‖ ^ 2 := by
    intro z
    apply zero_extended_row_fiber_sieve ms cs goodMC jset ps cprod
      (fun p j => symbol p j ^ (-2 : ℤ)) S Dc hDc hgoodMC hcmap hcfiber
      (a := z)
    intro u
    exact hcubic N0 L0 hN hL jset ps hjset hps u (-2) (Or.inr rfl)
  have hb := weighted_energy_of_two_sieves
    rows ts cs ms hs ps
    (zeroExtendedQuadratic goodPairs qprod (fun k j => symbol k j ^ 3))
    (zeroExtendedCubic goodMC cprod (fun p j => symbol p j ^ (-2 : ℤ)))
    a beta rowMask wt wc wh
    (Q * Dq) (S * Dc) Rbudget A
    (mul_nonneg hQ hDq) (mul_nonneg hS hDc) hR hA
    hwt hwc hwh hmask hbudget ha hqp hcp
  apply hb.trans_eq
  have hpow : (K0 * Y0 * N0 * L0) ^ eps =
      (K0 * Y0) ^ eps * (N0 * L0) ^ eps := by
    rw [show K0 * Y0 * N0 * L0 = (K0 * Y0) * (N0 * L0) by ring]
    exact Real.mul_rpow (by positivity) (by positivity)
  rw [hpow]
  dsimp only [Q, S]
  ring

#print axioms zero_extended_column_fiber_sieve
#print axioms zero_extended_row_fiber_sieve
#print axioms weighted_energy_from_sieve_inputs

end
end HeckeSkeleton.LowHybrid

