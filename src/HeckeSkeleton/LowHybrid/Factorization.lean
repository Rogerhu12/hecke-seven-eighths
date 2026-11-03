import Mathlib.Analysis.Complex.Basic
import HeckeSkeleton.LowHybrid.CommonTactics

/-!
# The exact square extraction used in completed quadratic reduction

The first section works at one prime. The next section transports the
identities to valuation vectors. The final section retains the zero masks
when applying a multiplicative complex-valued symbol. For an ideal
application, the prime index type can be a finite set containing the supports
of the ideals concerned; the given ideal symbol must supply multiplicativity
and its sixth-power/zero laws.
-/

namespace HeckeSkeleton.LowHybrid.Factorization

open scoped Classical

def squarefreeExp (b : ℕ) : ℕ := b % 2
def squareExp (b : ℕ) : ℕ := b / 2
def commonExp (n b : ℕ) : ℕ := min n (squarefreeExp b)
def leftExp (n b : ℕ) : ℕ := n - commonExp n b
def rightExp (n b : ℕ) : ℕ := squarefreeExp b - commonExp n b

theorem square_extraction (b : ℕ) : b = squarefreeExp b + 2 * squareExp b := by
  unfold squarefreeExp squareExp
  omega

theorem squarefreeExp_le_one (b : ℕ) : squarefreeExp b ≤ 1 := by
  unfold squarefreeExp
  omega

theorem split_left (n b : ℕ) : n = commonExp n b + leftExp n b := by
  have hc : commonExp n b ≤ n := min_le_left _ _
  unfold leftExp
  omega

theorem split_right (n b : ℕ) : squarefreeExp b = commonExp n b + rightExp n b := by
  have hc : commonExp n b ≤ squarefreeExp b := min_le_right _ _
  unfold rightExp
  omega

theorem commonExp_le_one (n b : ℕ) (hn : n ≤ 1) : commonExp n b ≤ 1 :=
  le_trans (min_le_left _ _) hn

theorem leftExp_le_one (n b : ℕ) (hn : n ≤ 1) : leftExp n b ≤ 1 := by
  unfold leftExp
  omega

theorem rightExp_le_one (n b : ℕ) : rightExp n b ≤ 1 := by
  have hg := squarefreeExp_le_one b
  unfold rightExp
  omega

theorem common_left_disjoint (n b : ℕ) (hn : n ≤ 1) :
    commonExp n b = 0 ∨ leftExp n b = 0 := by
  have h := split_left n b
  omega

theorem common_right_disjoint (n b : ℕ) :
    commonExp n b = 0 ∨ rightExp n b = 0 := by
  have h := split_right n b
  have hg := squarefreeExp_le_one b
  omega

theorem left_right_disjoint (n b : ℕ) : leftExp n b = 0 ∨ rightExp n b = 0 := by
  unfold leftExp rightExp commonExp
  simp only [min_def]
  split_ifs <;> omega

/-- Exact completed-square exponent identity, with no coprimality assumption
between `b` and `n`. -/
theorem completed_square_exponent (n b : ℕ) :
    n + b = leftExp n b + rightExp n b + 2 * (commonExp n b + squareExp b) := by
  have hb := square_extraction b
  have hn := split_left n b
  have hg := split_right n b
  omega

theorem residual_exponent_le_one (n b : ℕ) (hn : n ≤ 1) :
    leftExp n b + rightExp n b ≤ 1 := by
  have hm := leftExp_le_one n b hn
  have hh := rightExp_le_one n b
  have hd := left_right_disjoint n b
  omega

/-- The factorization is unique. The condition `m = 0 ∨ h = 0` is the local
form of extracting the full gcd, and prevents common factors remaining in
the two residual variables. -/
theorem local_factorization_unique (n b g t c m h : ℕ)
    (hg : g ≤ 1) (hb : b = g + 2 * t)
    (hn : n = c + m) (hgc : g = c + h) (hmh : m = 0 ∨ h = 0) :
    g = squarefreeExp b ∧ t = squareExp b ∧ c = commonExp n b ∧
      m = leftExp n b ∧ h = rightExp n b := by
  unfold squarefreeExp squareExp commonExp leftExp rightExp
  simp only [squarefreeExp, commonExp, min_def]
  split_ifs <;> omega

/-! ## Valuation vectors -/

variable {ι : Type*}

def SquarefreeVector (a : ι → ℕ) : Prop := ∀ p, a p ≤ 1
def CoprimeVector (a b : ι → ℕ) : Prop := ∀ p, a p = 0 ∨ b p = 0

def squarefreePart (b : ι → ℕ) : ι → ℕ := fun p => squarefreeExp (b p)
def squarePart (b : ι → ℕ) : ι → ℕ := fun p => squareExp (b p)
def commonPart (n b : ι → ℕ) : ι → ℕ := fun p => commonExp (n p) (b p)
def leftPart (n b : ι → ℕ) : ι → ℕ := fun p => leftExp (n p) (b p)
def rightPart (n b : ι → ℕ) : ι → ℕ := fun p => rightExp (n p) (b p)
def residualProduct (n b : ι → ℕ) : ι → ℕ :=
  fun p => leftPart n b p + rightPart n b p
def maskPart (n b : ι → ℕ) : ι → ℕ :=
  fun p => commonPart n b p + squarePart b p

theorem squarePart_decomposition (b : ι → ℕ) :
    b = fun p => squarefreePart b p + 2 * squarePart b p := by
  funext p
  exact square_extraction (b p)

theorem leftPart_decomposition (n b : ι → ℕ) :
    n = fun p => commonPart n b p + leftPart n b p := by
  funext p
  exact split_left (n p) (b p)

theorem rightPart_decomposition (n b : ι → ℕ) :
    squarefreePart b = fun p => commonPart n b p + rightPart n b p := by
  funext p
  exact split_right (n p) (b p)

theorem squarefreePart_squarefree (b : ι → ℕ) : SquarefreeVector (squarefreePart b) := by
  intro p
  exact squarefreeExp_le_one (b p)

theorem commonPart_squarefree (n b : ι → ℕ) (hn : SquarefreeVector n) :
    SquarefreeVector (commonPart n b) := by
  intro p
  exact commonExp_le_one (n p) (b p) (hn p)

theorem leftPart_squarefree (n b : ι → ℕ) (hn : SquarefreeVector n) :
    SquarefreeVector (leftPart n b) := by
  intro p
  exact leftExp_le_one (n p) (b p) (hn p)

theorem rightPart_squarefree (n b : ι → ℕ) : SquarefreeVector (rightPart n b) := by
  intro p
  exact rightExp_le_one (n p) (b p)

theorem commonPart_leftPart_coprime (n b : ι → ℕ) (hn : SquarefreeVector n) :
    CoprimeVector (commonPart n b) (leftPart n b) := by
  intro p
  exact common_left_disjoint (n p) (b p) (hn p)

theorem commonPart_rightPart_coprime (n b : ι → ℕ) :
    CoprimeVector (commonPart n b) (rightPart n b) := by
  intro p
  exact common_right_disjoint (n p) (b p)

theorem leftPart_rightPart_coprime (n b : ι → ℕ) :
    CoprimeVector (leftPart n b) (rightPart n b) := by
  intro p
  exact left_right_disjoint (n p) (b p)

/-- The product `m h` to which the quadratic sieve is applied is squarefree. -/
theorem residualProduct_squarefree (n b : ι → ℕ) (hn : SquarefreeVector n) :
    SquarefreeVector (residualProduct n b) := by
  intro p
  exact residual_exponent_le_one (n p) (b p) (hn p)

theorem completed_square_decomposition (n b : ι → ℕ) :
    (fun p => n p + b p) = fun p => residualProduct n b p + 2 * maskPart n b p := by
  funext p
  exact completed_square_exponent (n p) (b p)

theorem vector_factorization_unique (n b g t c m h : ι → ℕ)
    (hg : SquarefreeVector g) (hb : ∀ p, b p = g p + 2 * t p)
    (hn : ∀ p, n p = c p + m p) (hgc : ∀ p, g p = c p + h p)
    (hmh : CoprimeVector m h) :
    g = squarefreePart b ∧ t = squarePart b ∧ c = commonPart n b ∧
      m = leftPart n b ∧ h = rightPart n b := by
  have hp (p : ι) := local_factorization_unique
    (n p) (b p) (g p) (t p) (c p) (m p) (h p)
    (hg p) (hb p) (hn p) (hgc p) (hmh p)
  exact ⟨funext (fun p => (hp p).1), funext (fun p => (hp p).2.1),
    funext (fun p => (hp p).2.2.1), funext (fun p => (hp p).2.2.2.1),
    funext (fun p => (hp p).2.2.2.2)⟩

/-- Once `c = r c'` has been extracted, the cubic column is `j = c' m`
and the original squarefree variable is exactly `n = r j`. -/
theorem cubicColumn_decomposition (n b r c' : ι → ℕ)
    (hc : ∀ p, commonPart n b p = r p + c' p) :
    n = fun p => r p + (c' p + leftPart n b p) := by
  funext p
  have h := split_left (n p) (b p)
  have hcp := hc p
  change commonExp (n p) (b p) = r p + c' p at hcp
  change n p = r p + (c' p + leftExp (n p) (b p))
  omega

/-- The recombined column `c' m` is squarefree; no separate Cauchy step
over `c'` is needed to establish the cubic-sieve support condition. -/
theorem cubicColumn_squarefree (n b r c' : ι → ℕ)
    (hn : SquarefreeVector n)
    (hc : ∀ p, commonPart n b p = r p + c' p) :
    SquarefreeVector (fun p => c' p + leftPart n b p) := by
  have he := cubicColumn_decomposition n b r c' hc
  intro p
  have hp := congrFun he p
  have hnp := hn p
  change n p = r p + (c' p + leftPart n b p) at hp
  change n p ≤ 1 at hnp
  change c' p + leftPart n b p ≤ 1
  omega

theorem cubicColumn_factors_coprime (n b r c' : ι → ℕ)
    (hn : SquarefreeVector n)
    (hc : ∀ p, commonPart n b p = r p + c' p) :
    CoprimeVector c' (leftPart n b) := by
  have hj := cubicColumn_squarefree n b r c' hn hc
  intro p
  have h := hj p
  change c' p + leftPart n b p ≤ 1 at h
  change c' p = 0 ∨ leftPart n b p = 0
  omega

/-! ## Exact zero-preserving symbol masks -/

theorem coprimeVector_add_right (P a b : ι → ℕ) :
    CoprimeVector P (fun p => a p + b p) ↔
      CoprimeVector P a ∧ CoprimeVector P b := by
  constructor
  · intro h
    constructor
    · intro p
      have hp := h p
      change P p = 0 ∨ a p + b p = 0 at hp
      change P p = 0 ∨ a p = 0
      omega
    · intro p
      have hp := h p
      change P p = 0 ∨ a p + b p = 0 at hp
      change P p = 0 ∨ b p = 0
      omega
  · rintro ⟨ha, hb⟩ p
    have hap := ha p
    have hbp := hb p
    change P p = 0 ∨ a p = 0 at hap
    change P p = 0 ∨ b p = 0 at hbp
    change P p = 0 ∨ a p + b p = 0
    omega

/-- `chi(n b)^3 = chi(m h)^3 1_(row,c t)=1`, including the original
zeros. Only multiplicativity and the sixth-power law are used. -/
theorem completed_quadratic_symbol (row n b : ι → ℕ)
    (chi : (ι → ℕ) → ℂ)
    (hadd : ∀ a b, chi (fun p => a p + b p) = chi a * chi b)
    (hsix : ∀ a, chi a ^ 6 = if CoprimeVector row a then 1 else 0) :
    chi (fun p => n p + b p) ^ 3 =
      if CoprimeVector row (maskPart n b) then chi (residualProduct n b) ^ 3 else 0 := by
  classical
  have hd : (fun p => n p + b p) =
      fun p => (residualProduct n b p + maskPart n b p) + maskPart n b p := by
    funext p
    have hp := congrFun (completed_square_decomposition n b) p
    omega
  calc
    chi (fun p => n p + b p) ^ 3 =
        (chi (residualProduct n b) * chi (maskPart n b) * chi (maskPart n b)) ^ 3 := by
      rw [hd, hadd (fun p => residualProduct n b p + maskPart n b p) (maskPart n b),
        hadd (residualProduct n b) (maskPart n b)]
    _ = chi (residualProduct n b) ^ 3 * chi (maskPart n b) ^ 6 := by ring
    _ = if CoprimeVector row (maskPart n b) then chi (residualProduct n b) ^ 3 else 0 := by
      rw [hsix]
      split_ifs <;> simp

/-- The full row mask separates into the retained `t` mask and the `c` mask
that is resolved by Möbius inversion. -/
theorem completed_row_mask (row n b : ι → ℕ) :
    CoprimeVector row (maskPart n b) ↔
      CoprimeVector row (commonPart n b) ∧ CoprimeVector row (squarePart b) :=
  coprimeVector_add_right _ _ _

/-- If the symbol's argument is prime to `P`, the redundant `r,c'` part of
the explicit mask can be removed. The `t` exponent two has the same support
as `t` itself. -/
theorem cubic_mask_equivalence (P r c m h t : ι → ℕ)
    (hn : CoprimeVector P (fun p => r p + c p + m p)) :
    CoprimeVector P (fun p => r p + c p + h p + 2 * t p) ↔
      CoprimeVector P (fun p => h p + t p) := by
  constructor
  · intro hfull p
    have hp := hfull p
    change P p = 0 ∨ r p + c p + h p + 2 * t p = 0 at hp
    change P p = 0 ∨ h p + t p = 0
    omega
  · intro hshort p
    have hp := hshort p
    have hnp := hn p
    change P p = 0 ∨ h p + t p = 0 at hp
    change P p = 0 ∨ r p + c p + m p = 0 at hnp
    change P p = 0 ∨ r p + c p + h p + 2 * t p = 0
    omega

/-- The precise cubic-column mask identity used after `n = r c' m` and
`b = r c' h t^2`. The function `psi` represents `chi_P^(-2)`; its common-prime
zeros are retained, so this equality also covers overlap with `r` or `c'`. -/
theorem completed_cubic_mask (P r c m h t : ι → ℕ)
    (psi : (ι → ℕ) → ℂ)
    (hadd : ∀ a b, psi (fun p => a p + b p) = psi a * psi b)
    (hzero : ∀ a, ¬ CoprimeVector P a → psi a = 0) :
    (if CoprimeVector P (fun p => r p + c p + h p + 2 * t p)
      then psi (fun p => r p + c p + m p) else 0) =
    if CoprimeVector P (fun p => h p + t p)
      then psi r * psi (fun p => c p + m p) else 0 := by
  classical
  have hprod : psi (fun p => r p + c p + m p) = psi r * psi (fun p => c p + m p) := by
    have he : (fun p => r p + c p + m p) = (fun p => r p + (c p + m p)) := by
      funext p
      omega
    rw [he, hadd]
  by_cases hn : CoprimeVector P (fun p => r p + c p + m p)
  · rw [cubic_mask_equivalence P r c m h t hn, hprod]
  · rw [← hprod]
    simp [hzero _ hn]

#print axioms local_factorization_unique
#print axioms residualProduct_squarefree
#print axioms vector_factorization_unique
#print axioms cubicColumn_squarefree
#print axioms completed_quadratic_symbol
#print axioms completed_row_mask
#print axioms completed_cubic_mask

end HeckeSkeleton.LowHybrid.Factorization
