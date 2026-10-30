import HeckeSkeleton.LowHybrid.SieveComposition
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The two arithmetic sieve inputs and their fixed-block consequence

For the project interface instantiate `I := ExteriorIdeal K S`,
`normI := exteriorNorm K S`, `sf I := Squarefree I.val.val`, and
`symbol J I := idealSymbol K S D J (D.generator I)`.
The definitions below then have the quantifiers and orientations of the
supplied `QuadraticSieveBound` and `CubicSieveBound`; they do not mention
`TargetContext`. No assertion about an actual project symbol is postulated.

`hybrid_fixed_block_from_sieve_bounds` chooses its constant before the
supports and scales. It derives both product-family bounds from the two
sieves and the two explicit fiber bounds.
-/

namespace HeckeSkeleton.LowHybrid

open scoped BigOperators

noncomputable section

variable {I : Type*}

def QuadraticSieveInput (normI : I → ℝ) (sf : I → Prop)
    (symbol : I → I → ℂ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ C : ℝ, 0 < C ∧
    ∀ X Y : ℝ, 1 ≤ X → 1 ≤ Y →
      ∀ rows columns : Finset I,
        (∀ i ∈ rows, sf i ∧ normI i ≤ X) →
        (∀ j ∈ columns, sf j ∧ normI j ≤ Y) →
        ∀ a : I → ℂ,
          (∑ i ∈ rows, ‖∑ j ∈ columns, a j * symbol j i ^ 3‖ ^ 2) ≤
            C * (X * Y) ^ eps * (X + Y) * ∑ j ∈ columns, ‖a j‖ ^ 2

def CubicSieveInput (normI : I → ℝ) (sf : I → Prop)
    (symbol : I → I → ℂ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ C : ℝ, 0 < C ∧
    ∀ X Y : ℝ, 1 ≤ X → 1 ≤ Y →
      ∀ rows columns : Finset I,
        (∀ i ∈ rows, sf i ∧ normI i ≤ X) →
        (∀ j ∈ columns, sf j ∧ normI j ≤ Y) →
        ∀ a : I → ℂ, ∀ e : ℤ, (e = 2 ∨ e = -2) →
          (∑ i ∈ rows, ‖∑ j ∈ columns, a j * symbol j i ^ e‖ ^ 2) ≤
            C * (X * Y) ^ eps * (X + Y + (X * Y) ^ (2 / 3 : ℝ)) *
              ∑ j ∈ columns, ‖a j‖ ^ 2

/-- Fixed-block consequence of the actual-form quadratic and cubic inputs.

`qprod(m,h)=mh` is the squarefree product used by the quadratic sieve;
`cprod(m,c)=cm` is the different product used by the cubic sieve. The only
extra quantities on the right are explicit finite combinatorial counts and
the actual squared column mass. They are not assumed hybrid bounds.
-/
theorem hybrid_fixed_block_from_sieve_bounds [DecidableEq I]
    (normI : I → ℝ) (sf : I → Prop) (symbol : I → I → ℂ)
    (hq : QuadraticSieveInput normI sf symbol)
    (hc : CubicSieveInput normI sf symbol) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧
    ∀ K0 Y0 N0 L0 : ℝ, 1 ≤ K0 → 1 ≤ Y0 → 1 ≤ N0 → 1 ≤ L0 →
    ∀ (rows : Finset I) (pairs : Finset (I × I)) (qset : Finset I)
      (cset : I → Finset I) (hset : Finset I) (mc : Finset (I × I))
      (jset pset : Finset I)
      (qprod cprod : I × I → I) (a : I → I → ℂ) (beta : I → I → I → ℂ)
      (Dq Dc Cbound Ebound : ℝ),
      0 ≤ Dq → 0 ≤ Dc → 0 ≤ Cbound →
      (∀ k ∈ rows, sf k ∧ normI k ≤ K0) →
      (∀ j ∈ qset, sf j ∧ normI j ≤ Y0) →
      (∀ j ∈ jset, sf j ∧ normI j ≤ N0) →
      (∀ p ∈ pset, sf p ∧ normI p ≤ L0) →
      (∀ u ∈ pairs, qprod u ∈ qset) →
      (∀ j ∈ qset, ((pairs.filter fun u => qprod u = j).card : ℝ) ≤ Dq) →
      (∀ u ∈ pairs, ((cset u.1).card : ℝ) ≤ Cbound) →
      (∀ u ∈ pairs, ∀ c ∈ cset u.1, ‖beta c u.1 u.2‖ ≤ 1) →
      (∀ u ∈ pairs, u.2 ∈ hset) →
      (∀ u ∈ pairs, ∀ c ∈ cset u.1, (u.1, c) ∈ mc) →
      (∀ u ∈ mc, cprod u ∈ jset) →
      (∀ j ∈ jset, ((mc.filter fun u => cprod u = j).card : ℝ) ≤ Dc) →
      (∀ h ∈ hset, (∑ p ∈ pset, ‖a h p‖ ^ 2) ≤ Ebound) →
      (∑ k ∈ rows, ‖∑ u ∈ pairs, symbol (qprod u) k ^ 3 *
        (∑ c ∈ cset u.1, beta c u.1 u.2 *
          (∑ p ∈ pset, a u.2 p * symbol p (cprod (u.1, c)) ^ (-2 : ℤ)))‖ ^ 2) ≤
        C * (K0 * Y0 * N0 * L0) ^ eps * (K0 + Y0) *
          Cbound * (hset.card : ℝ) * Dq * Dc *
          (N0 + L0 + (N0 * L0) ^ (2 / 3 : ℝ)) * Ebound := by
  classical
  obtain ⟨Cq, hCq, hquadratic⟩ := hq eps heps
  obtain ⟨Cc, hCc, hcubic⟩ := hc eps heps
  refine ⟨Cq * Cc, mul_pos hCq hCc, ?_⟩
  intro K0 Y0 N0 L0 hK hY hN hL rows pairs qset cset hset mc jset pset
    qprod cprod a beta Dq Dc Cbound Ebound hDq hDc hCbound
    hrows hqset hjset hpset hqmap hqfiber hcount hbeta hh hmc hcmap hcfiber hcoef
  let Q := Cq * (K0 * Y0) ^ eps * (K0 + Y0)
  let S := Cc * (N0 * L0) ^ eps * (N0 + L0 + (N0 * L0) ^ (2 / 3 : ℝ))
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hqp : ∀ f : I × I → ℂ,
      (∑ k ∈ rows, ‖∑ u ∈ pairs, symbol (qprod u) k ^ 3 * f u‖ ^ 2) ≤
        (Q * Dq) * ∑ u ∈ pairs, ‖f u‖ ^ 2 := by
    intro f
    apply column_fiber_sieve rows pairs qset qprod
      (fun k j => symbol j k ^ 3) f Q Dq hQ hqmap hqfiber
    intro g
    simpa only [Q, mul_comm] using hquadratic K0 Y0 hK hY rows qset hrows hqset g
  have hcp : ∀ u : I → ℂ,
      (∑ j ∈ jset, ‖∑ p ∈ pset, u p * symbol p j ^ (-2 : ℤ)‖ ^ 2) ≤
        S * ∑ p ∈ pset, ‖u p‖ ^ 2 := by
    intro u
    exact hcubic N0 L0 hN hL jset pset hjset hpset u (-2) (Or.inr rfl)
  have hb := fixed_block_energy_of_two_sieves rows pairs cset hset mc jset pset
    (fun k u => symbol (qprod u) k ^ 3) cprod (fun p j => symbol p j ^ (-2 : ℤ))
    a beta (Q * Dq) S Cbound Dc Ebound
    (mul_nonneg hQ hDq) hS hCbound hDc hcount hbeta hh hmc hcmap hcfiber hcoef hqp hcp
  apply hb.trans_eq
  have hpow : (K0 * Y0 * N0 * L0) ^ eps =
      (K0 * Y0) ^ eps * (N0 * L0) ^ eps := by
    rw [show K0 * Y0 * N0 * L0 = (K0 * Y0) * (N0 * L0) by ring]
    exact Real.mul_rpow (by positivity) (by positivity)
  rw [hpow]
  dsimp only [Q, S]
  ring

#print axioms hybrid_fixed_block_from_sieve_bounds

end
end HeckeSkeleton.LowHybrid
