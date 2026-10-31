import Expansion.ActualHeckeSaturation
import Expansion.CanonicalDetectorBounds
import Expansion.PhysicalRowPoleExclusion

/-!
# Saturated witnesses on the original canonical physical row family

All arithmetic inputs of the analytic detector are supplied here by the
actual row: finite-order infinity types, the original-ideal conductor
bound, and the finite exceptional-character fibers. One cutoff works for
both permitted backgrounds before the row, bin, zero and source exponent
are selected. The lower and upper zero information is exactly that of the
original four-character physical family with the identity companion.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Bridge
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.ExpansionDetectorBridge HeckeSkeleton.HeckeBufferedReciprocal
open Expansion.ActualTerminalSaturation
open scoped Classical BigOperators ContDiff

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (E : RowEulerData K S P) (ψ : HeckeCharacter K)

/-- The output retains the positive-order ordinary zero and all three
actual upper/lower estimates, at the same selected dyadic scales and
frequency. No rowwise conductor, non-norm or polynomial-bound premise is
left to the caller. -/
theorem exists_canonical_row_saturation
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000) (hε : 0 < ε)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (hVnorm : ∀ x : ℝ, ‖V x‖ ≤ 1)
    (hVcomp : ∀ x : ℝ, 0 ≤ x → ‖1 - V x‖ ≤ 1)
    (Cheight θzero θ τ η : ℝ)
    (hθzero : 0 ≤ θzero) (hθ : 0 ≤ θ) (hτ : 0 < τ) (hη : 0 < η)
    (hzeroBudget : heightDegree K * θzero ≤ 1)
    (hforward : 132 * e + 2 * ε + heightDegree K * ε * θ ≤ η / 4)
    (hreflected : 12 * e + 2 * ε + heightDegree K * θ * (1 + ε) ≤ η / 4) :
    ∃ U₀ : ℝ, 6 ≤ U₀ ∧ ∀ (u : FrequencyRow K S)
      (U a height H Hupper D : ℝ),
      U₀ ≤ U → U < frequencyRowNorm K S u → frequencyRowNorm K S u ≤ 2 * U →
      2 ≤ D → D ≤ U ^ (3 / 2 : ℝ) → 51 / 100 ≤ a →
      rowZeroAbove K S ψ {1} P E u height a → height ≤ U ^ θzero →
      2 + Hupper ≤ Cheight * U ^ θ → U ^ τ ≤ H →
      height + 2 * Real.pi * (U ^ τ / (8 * Real.pi + 8)) + H + 3 / 2 ≤ Hupper →
      rowZeroBelow K S ψ {1} P E u Hupper (a + 2 * e) →
      ∃ i : Fin 2, ∃ ρ : ℂ,
        0 < meromorphicOrderAt
          (heckeContinuation K (canonicalDetectorCharacter K ψ S P E i u)) ρ ∧
        a ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ height ∧
        let n := Expansion.Dyadic.dyadicCap (3 * U ^ (21 : ℕ))
        ∃ j ≤ n, ∃ k ≤ n, ∃ ξ : ℝ,
          ‖ξ‖ ≤ U ^ τ / (8 * Real.pi + 8) ∧
          ((2 : ℝ) ^ j < 4 * D ∧ D / 8 < (2 : ℝ) ^ j * (2 : ℝ) ^ k ∧
            (2 : ℝ) ^ j * (2 : ℝ) ^ k < 8 * U ^ (21 : ℕ)) ∧
          let r := Expansion.Dyadic.dyadicLength U j
          let m := Expansion.Dyadic.dyadicLength U k
          let ν := 2 * Real.pi * ξ - ρ.im
          let χ := canonicalDetectorCharacter K ψ S P E i u
          let M := inverseDetectorValue K χ (originalDeletedPrimes K S u.ideal.val)
            V D U j ρ.re ν
          let Q := plainDetectorValue K χ (originalDeletedPrimes K S u.ideal.val) U k ρ.re ν
          U ^ ((2 * a - 1) * (r + m) - η) ≤ ‖M * Q‖ ^ 2 ∧
          ‖M‖ ^ 2 ≤ U ^ ((2 * a - 1) * r + η) ∧
          ‖Q‖ ^ 2 ≤ U ^ ((2 * a - 1) * min m (1 - m) + η) ∧
          U ^ ((2 * a - 1) * r - 2 * η) ≤ ‖M‖ ^ 2 ∧
          U ^ ((2 * a - 1) * m - 2 * η) ≤ ‖Q‖ ^ 2 ∧
          m ≤ 1 / 2 + 75 * η ∧
          Real.log D / Real.log U - 1 / 2 - 75 * η - Real.log 8 / Real.log U ≤ r := by
  let R : ℝ := max (canonicalDetectorConductorConstant K S ψ) Cheight
  have hR : 1 ≤ R := (canonicalDetectorConductorConstant_ge_one K S ψ).trans
    (le_max_left _ _)
  have hfamily (i : Fin 2) := exists_original_masked_saturation K S hcomplex
    (fun v => heckeRadialParameter K v (canonicalDetectorBackground K ψ i))
    (heckeArchWeight K (canonicalDetectorBackground K ψ i))
    he he' hε V hV hone hzero hVnorm hVcomp R θzero θ τ η hR
    hθzero hθ hτ hη hzeroBudget hforward hreflected
  choose C hC hsaturation using hfamily
  obtain ⟨Cp, hCp, hpole⟩ := exists_physicalRowFamily_normTwist_cutoff K S P ψ {1} E
  let Csum : ℝ := ∑ i : Fin 2, C i
  have hCi (i : Fin 2) : C i ≤ Csum :=
    Finset.single_le_sum (fun j _ => (by linarith [hC j])) (Finset.mem_univ i)
  refine ⟨max Cp Csum, (hC 0).trans ((hCi 0).trans (le_max_right _ _)), ?_⟩
  intro u U a height H Hupper D hU huLower huUpper hD hDU ha habove hzeroheight
    hheight hH hpadding hbelow
  have hUpos : 0 < U := by
    have h6 : 6 ≤ U := (hC 0).trans ((hCi 0).trans ((le_max_right _ _).trans hU))
    linarith
  obtain ⟨i, ρ, hz, hβ, hβ', hγ⟩ :=
    exists_canonicalDetector_zero K ψ S P E u height a habove
  have hnonnorm : ∀ t : ℝ, canonicalDetectorCharacter K ψ S P E i u ≠
      heckeNormTwist K t :=
    hpole u (lt_of_le_of_lt ((le_max_left _ _).trans hU) huLower) _
      (canonicalDetectorCharacter_mem_family K ψ S P E i u)
  have hQ : heckeConductorScale K (canonicalDetectorCharacter K ψ S P E i u) ≤ R * U :=
    (canonicalDetector_conductor K S P E ψ i u U hUpos.le huUpper).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hUpos.le)
  have hh : 2 + Hupper ≤ R * U ^ θ := hheight.trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hUpos.le θ))
  have hpad : |ρ.im| + 2 * Real.pi * (U ^ τ / (8 * Real.pi + 8)) + H + 3 / 2 ≤
      Hupper := by linarith
  refine ⟨i, ρ, hz, hβ, hβ', hγ, ?_⟩
  exact hsaturation i (canonicalDetectorCharacter K ψ S P E i u) u.ideal.val
    U a H Hupper D ρ hnonnorm (canonicalDetector_radial K S P E ψ i u)
    (canonicalDetector_weight K S P E ψ hcomplex i u)
    ((hCi i).trans ((le_max_right _ _).trans hU)) huUpper hQ hD hDU ha hβ hβ'
    hz (hγ.trans hzeroheight) hh hH hpad
    (canonicalDetector_zero_upper K ψ S P E u Hupper (a + 2 * e) hbelow i)

end Expansion.Project

#print axioms Expansion.Project.exists_canonical_row_saturation
