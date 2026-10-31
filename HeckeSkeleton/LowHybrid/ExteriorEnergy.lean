import HeckeSkeleton.LowHybrid.ExteriorSieve
import HeckeSkeleton.LowHybrid.Corollaries
import HeckeSkeleton.LowHybrid.CompletedQuadraticBound

/-!
# The hybrid and completed-quadratic estimates on the actual exterior ideals

These are the actual-object forms of Lemmas 4.6 and 4.7.  The left sides use
`idealSymbol`, the chosen `ThetaArithmeticData.generator`, ordinary ideal
coprimality, and `exteriorNorm`.  The only fixed arithmetic datum in the
estimates is the repository's `ArithmeticChoice`; all coordinates, norm
counting, allowed-generator compatibility and both sieve inputs are proved
by the preceding adapters.  Constants precede all scales and coefficients.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowHybrid.Exterior

open NumberField IsDedekindDomain
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowFrozenCube.PrimeCoordinates
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- The original row, with literal ideal coprimality and its two collisions. -/
def row (a : ExteriorIdeal K S → ℂ) (beta : ExteriorIdeal K S → ExteriorIdeal K S → ℂ)
    (marks columns cubes : Finset (ExteriorIdeal K S)) (k : ExteriorIdeal K S) : ℂ :=
  ∑ P ∈ marks, (a P / (Real.sqrt (exteriorNorm K S P) : ℂ)) *
    (if IsCoprime P.val.val k.val.val then (1 : ℂ) else 0) *
    ∑ n ∈ columns, ∑ b ∈ cubes, beta n b *
      (idealSymbol K S D k (D.generator (exteriorMul K S n b)) ^ 3 *
        idealSymbol K S D P (D.generator n) ^ (-2 : ℤ) *
        (if IsCoprime P.val.val b.val.val then (1 : ℂ) else 0))

/-- The genuine normalized hybrid energy over the original ideal rows. -/
def energy (a : ExteriorIdeal K S → ℂ)
    (beta : ExteriorIdeal K S → ExteriorIdeal K S → ℂ)
    (rows marks columns cubes : Finset (ExteriorIdeal K S)) : ℝ :=
  ∑ k ∈ rows, ‖row K S D a beta marks columns cubes k‖ ^ 2

/-- The model energy and the original actual-ideal energy are equal. -/
theorem coordinateEnergy_eq (a : ExteriorIdeal K S → ℂ)
    (beta : ExteriorIdeal K S → ExteriorIdeal K S → ℂ)
    (rows marks columns cubes : Finset (ExteriorIdeal K S)) :
    hybridEnergy (ExteriorSymbol.symbol K S D) (Coprime (ExteriorArithmetic.coords K S))
      (ExteriorArithmetic.normHom K S) a beta rows marks columns cubes =
        energy K S D a beta rows marks columns cubes := by
  simp only [hybridEnergy, hybridRow, energy, row, ExteriorArithmetic.coords_coprime_iff,
    ExteriorArithmetic.normHom_apply, ExteriorSymbol.symbol_apply, ExteriorArithmetic.mul_eq]

variable {K S D}
variable {S₀ : Finset (HeightOneSpectrum (𝓞 K))} {root12 : K} {σ : K →+* ℂ}
variable (X : HeckeAxiom.ArithmeticChoice K S₀ root12 σ)
local notation "S" => (X.places : Set (HeightOneSpectrum (𝓞 K)))
local notation "D" => X.thetaData

/-- The actual mixed energy, with arbitrary normalized mark mass and
unit-bounded two-variable coefficients. -/
theorem hybrid_energy (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧
      ∀ R N B L : ℝ, 1 ≤ R → 1 ≤ N → 1 ≤ B → 1 ≤ L →
      ∀ (rows marks columns cubes : Finset (ExteriorIdeal K S))
        (a : ExteriorIdeal K S → ℂ) (beta : ExteriorIdeal K S → ExteriorIdeal K S → ℂ),
        (∀ k ∈ rows, Squarefree k.val.val ∧ exteriorNorm K S k ≤ R) →
        (∀ p ∈ marks, Squarefree p.val.val ∧ exteriorNorm K S p ≤ L) →
        (∀ n ∈ columns, Squarefree n.val.val ∧ exteriorNorm K S n ≤ N) →
        (∀ b ∈ cubes, exteriorNorm K S b ≤ B) →
        (∀ n ∈ columns, ∀ b ∈ cubes, ‖beta n b‖ ≤ 1) →
        energy K S D a beta rows marks columns cubes ≤
          C * (R * N * B * L) ^ eps * (R + N * B) * B *
            (N + L + (N * L) ^ (2 / 3 : ℝ)) *
            (∑ p ∈ marks, ‖a p‖ ^ 2 / exteriorNorm K S p) := by
  simpa only [ExteriorArithmetic.coords_squarefree_iff, ExteriorArithmetic.normHom_apply,
    coordinateEnergy_eq] using HeckeSkeleton.LowHybrid.hybrid_energy
      (ExteriorArithmetic.coords K S) (ExteriorArithmetic.normHom K S)
      (ExteriorArithmetic.natNorm K S) (ExteriorArithmetic.normHom_natNorm K S)
      (ExteriorArithmetic.one_le_natNorm K S) (ExteriorArithmetic.countConstant K)
      (ExteriorArithmetic.countConstant_pos K) (ExteriorArithmetic.linearNormCounting K S)
      (ExteriorSymbol.symbol K S D)
      (ExteriorSymbol.symbol_mul_left K S D (ExteriorSieve.allowedInput X))
      (ExteriorSymbol.symbol_mul_right K S D (ExteriorSieve.allowedInput X))
      (ExteriorSymbol.symbol_sixth K S D)
      (ExteriorSieve.quadraticSieveInput X)
      (ExteriorSieve.cubicSieveInput X.A D (ExteriorSieve.allowedInput X)) eps heps

/-- Arbitrary complex beta coefficients, with their actual finite maximum
squared norm appearing exactly once. -/
theorem hybrid_energy_with_beta_mass (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧
      ∀ R N B L : ℝ, 1 ≤ R → 1 ≤ N → 1 ≤ B → 1 ≤ L →
      ∀ (rows marks columns cubes : Finset (ExteriorIdeal K S))
        (a : ExteriorIdeal K S → ℂ) (beta : ExteriorIdeal K S → ExteriorIdeal K S → ℂ),
        (∀ k ∈ rows, Squarefree k.val.val ∧ exteriorNorm K S k ≤ R) →
        (∀ p ∈ marks, Squarefree p.val.val ∧ exteriorNorm K S p ≤ L) →
        (∀ n ∈ columns, Squarefree n.val.val ∧ exteriorNorm K S n ≤ N) →
        (∀ b ∈ cubes, exteriorNorm K S b ≤ B) →
        energy K S D a beta rows marks columns cubes ≤
          C * (R * N * B * L) ^ eps * (R + N * B) * B *
            (N + L + (N * L) ^ (2 / 3 : ℝ)) *
            (∑ p ∈ marks, ‖a p‖ ^ 2 / exteriorNorm K S p) *
              betaSquaredMass beta columns cubes := by
  simpa only [ExteriorArithmetic.coords_squarefree_iff, ExteriorArithmetic.normHom_apply,
    coordinateEnergy_eq] using HeckeSkeleton.LowHybrid.hybrid_energy_with_beta_mass
      (ExteriorArithmetic.coords K S) (ExteriorArithmetic.normHom K S)
      (ExteriorArithmetic.natNorm K S) (ExteriorArithmetic.normHom_natNorm K S)
      (ExteriorArithmetic.one_le_natNorm K S) (ExteriorArithmetic.countConstant K)
      (ExteriorArithmetic.countConstant_pos K) (ExteriorArithmetic.linearNormCounting K S)
      (ExteriorSymbol.symbol K S D)
      (ExteriorSymbol.symbol_mul_left K S D (ExteriorSieve.allowedInput X))
      (ExteriorSymbol.symbol_mul_right K S D (ExteriorSieve.allowedInput X))
      (ExteriorSymbol.symbol_sixth K S D)
      (ExteriorSieve.quadraticSieveInput X)
      (ExteriorSieve.cubicSieveInput X.A D (ExteriorSieve.allowedInput X)) eps heps

/-- The displayed mixed bound for unit-bounded original coefficients. -/
theorem hybrid_energy_bounded (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧
      ∀ R N B L : ℝ, 1 ≤ R → 1 ≤ N → 1 ≤ B → 1 ≤ L →
      ∀ (rows marks columns cubes : Finset (ExteriorIdeal K S))
        (a : ExteriorIdeal K S → ℂ) (beta : ExteriorIdeal K S → ExteriorIdeal K S → ℂ),
        (∀ k ∈ rows, Squarefree k.val.val ∧ exteriorNorm K S k ≤ R) →
        (∀ p ∈ marks, Squarefree p.val.val ∧ exteriorNorm K S p ≤ L) →
        (∀ n ∈ columns, Squarefree n.val.val ∧ exteriorNorm K S n ≤ N) →
        (∀ b ∈ cubes, exteriorNorm K S b ≤ B) →
        (∀ p ∈ marks, ‖a p‖ ≤ 1) →
        (∀ n ∈ columns, ∀ b ∈ cubes, ‖beta n b‖ ≤ 1) →
        energy K S D a beta rows marks columns cubes ≤
          C * (R * N * B * L) ^ eps * (R + N * B) * B *
            (N + L + (N * L) ^ (2 / 3 : ℝ)) := by
  simpa only [ExteriorArithmetic.coords_squarefree_iff, ExteriorArithmetic.normHom_apply,
    coordinateEnergy_eq] using HeckeSkeleton.LowHybrid.hybrid_energy_bounded
      (ExteriorArithmetic.coords K S) (ExteriorArithmetic.normHom K S)
      (ExteriorArithmetic.natNorm K S) (ExteriorArithmetic.normHom_natNorm K S)
      (ExteriorArithmetic.one_le_natNorm K S) (ExteriorArithmetic.countConstant K)
      (ExteriorArithmetic.countConstant_pos K) (ExteriorArithmetic.linearNormCounting K S)
      (ExteriorSymbol.symbol K S D)
      (ExteriorSymbol.symbol_mul_left K S D (ExteriorSieve.allowedInput X))
      (ExteriorSymbol.symbol_mul_right K S D (ExteriorSieve.allowedInput X))
      (ExteriorSymbol.symbol_sixth K S D)
      (ExteriorSieve.quadraticSieveInput X)
      (ExteriorSieve.cubicSieveInput X.A D (ExteriorSieve.allowedInput X)) eps heps

/-- Lemma 4.6 for the actual raw completed quadratic double sum.  Only the
quadratic sieve enters this proof; the cube variable is unrestricted. -/
theorem completed_quadratic_energy_bounded (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ R N B : ℝ, 1 ≤ R → 1 ≤ N → 1 ≤ B →
      ∀ (rows columns cubes : Finset (ExteriorIdeal K S))
        (beta : ExteriorIdeal K S → ExteriorIdeal K S → ℂ),
        (∀ k ∈ rows, Squarefree k.val.val ∧ exteriorNorm K S k ≤ R) →
        (∀ n ∈ columns, Squarefree n.val.val ∧ exteriorNorm K S n ≤ N) →
        (∀ b ∈ cubes, exteriorNorm K S b ≤ B) →
        (∀ n ∈ columns, ∀ b ∈ cubes, ‖beta n b‖ ≤ 1) →
        (∑ k ∈ rows, ‖∑ n ∈ columns, ∑ b ∈ cubes,
          beta n b * idealSymbol K S D k (X.thetaData.generator (exteriorMul K S n b)) ^ 3‖ ^ 2) ≤
            C * (R * N * B) ^ eps * (R + N * B) * (N * B) := by
  simpa only [ExteriorArithmetic.coords_squarefree_iff, ExteriorArithmetic.normHom_apply,
    ExteriorSymbol.symbol_apply, ExteriorArithmetic.mul_eq] using
    HeckeSkeleton.LowHybrid.completed_quadratic_energy_bounded
      (ExteriorArithmetic.coords K S) (ExteriorArithmetic.normHom K S)
      (ExteriorArithmetic.natNorm K S) (ExteriorArithmetic.normHom_natNorm K S)
      (ExteriorArithmetic.one_le_natNorm K S) (ExteriorArithmetic.countConstant K)
      (ExteriorArithmetic.countConstant_pos K) (ExteriorArithmetic.linearNormCounting K S)
      (ExteriorSymbol.symbol K S D)
      (ExteriorSymbol.symbol_mul_right K S D (ExteriorSieve.allowedInput X))
      (ExteriorSymbol.symbol_sixth K S D) (ExteriorSieve.quadraticSieveInput X) eps heps

#print axioms coordinateEnergy_eq
#print axioms hybrid_energy
#print axioms hybrid_energy_with_beta_mass
#print axioms hybrid_energy_bounded
#print axioms completed_quadratic_energy_bounded

end HeckeSkeleton.LowHybrid.Exterior
