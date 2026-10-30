import HeckeSkeleton.LowHybrid.CanonicalInputs
import HeckeSkeleton.LowHybrid.NormalFormUniform
import HeckeSkeleton.LowHybrid.ColumnMass
import HeckeSkeleton.LowHybrid.ArithmeticLosses

/-!
# LOW-HYBRID: the original energy from prime arithmetic and two sieves

All normal-form data and all arithmetic losses are discharged in this
module. The hypotheses describe a free prime-coordinate ideal monoid, its
positive natural multiplicative norm and linear norm count, and the two
arithmetic large-sieve conclusions. No normal-form equality, divisor bound,
harmonic bound, block operator estimate, or hybrid-energy bound is assumed.

The coefficient `a` is an arbitrary function of the mark alone. The
coefficient `beta` is an arbitrary bounded function of the two dual indices
alone. The cube index is unrestricted. The original square-root column
normalization and both original coprimality masks are retained literally.
-/

namespace HeckeSkeleton.LowHybrid

open scoped BigOperators Classical
open NormalForm PrimeArithmetic
open HeckeSkeleton.LowFrozenCube.PrimeCoordinates

noncomputable section

variable {ι A : Type*} [CommMonoid A]

/-- The complete arbitrary-epsilon hybrid inequality. Its constant is
selected before all four scales, every finite support, and both coefficients.
The only analytic sieve assumptions are the original quadratic and cubic
large-sieve conclusions. Linear norm counting is used for elementary
arithmetic loss absorption. -/
theorem hybrid_energy
    (coords : A ≃* Multiplicative (ι →₀ ℕ))
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount) (hcount : LinearNormCounting q Ccount)
    (symbol : A → A → ℂ)
    (hleft : ∀ a b c, symbol (a * b) c = symbol a c * symbol b c)
    (hright : ∀ a b c, symbol a (b * c) = symbol a b * symbol a c)
    (h6 : ∀ a b, symbol a b ^ 6 = if Coprime coords a b then 1 else 0)
    (hq : QuadraticSieveInput normI (PrimeArithmetic.Squarefree coords) symbol)
    (hc : CubicSieveInput normI (PrimeArithmetic.Squarefree coords) symbol)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ L →
      ∀ (rows marks columns cubes : Finset A) (a : A → ℂ) (beta : A → A → ℂ),
        (∀ k ∈ rows, PrimeArithmetic.Squarefree coords k ∧ normI k ≤ K) →
        (∀ p ∈ marks, PrimeArithmetic.Squarefree coords p ∧ normI p ≤ L) →
        (∀ n ∈ columns, PrimeArithmetic.Squarefree coords n ∧ normI n ≤ N) →
        (∀ b ∈ cubes, normI b ≤ B) →
        (∀ n ∈ columns, ∀ b ∈ cubes, ‖beta n b‖ ≤ 1) →
        hybridEnergy symbol (Coprime coords) normI a beta rows marks columns cubes ≤
          C0 * (K * N * B * L) ^ eps * (K + N * B) * B *
            (N + L + (N * L) ^ (2 / 3 : ℝ)) *
            (∑ p ∈ marks, ‖a p‖ ^ 2 / normI p) := by
  have hn : ∀ a, 1 ≤ normI a := one_le_real_norm_of_natural q normI hnatural hqpos
  let S : Arithmetic A := arithmetic coords normI
    (fun a => le_trans zero_le_one (hn a)) normI.map_mul symbol hleft hright h6
  let finiteNorms := finite_real_norms_of_linear_counting q normI hnatural Ccount hcount
  let cutoff := normCutoff normI finiteNorms
  let delta := divisorEnvelopeOfCounting coords normI q hnatural Ccount hcount
  let harmonic := harmonicEnvelope Ccount
  have hmem (X : ℝ) (a : A) : a ∈ cutoff X ↔ S.normI a ≤ X :=
    mem_normCutoff normI finiteNorms X a
  have hdelta : SubpowerBound delta :=
    divisorEnvelopeOfCounting_subpower coords normI q hnatural Ccount hcount hqpos
  have hdelta0 (X : ℝ) : 0 ≤ delta X :=
    divisorEnvelopeOfCounting_nonneg coords normI q hnatural Ccount hcount X
  have hharmonic : SubpowerBound harmonic := harmonicEnvelope_subpower Ccount hCcount
  have hharmonic0 (X : ℝ) (hX : 1 ≤ X) : 0 ≤ harmonic X :=
    harmonicEnvelope_nonneg Ccount (le_of_lt hCcount) X hX
  have hH (X : ℝ) (hX : 1 ≤ X) : cutoffHarmonic S cutoff X ≤ harmonic X := by
    exact reciprocal_sum_le_harmonicEnvelope q normI hnatural Ccount (le_of_lt hCcount)
      hqpos hcount X hX (cutoff X) (fun a ha => (hmem X a).mp ha)
  have hmu (a : A) : ‖S.mu a‖ ≤ 1 := le_of_eq (mobius_norm coords a)
  obtain ⟨C0, hC0, hbound⟩ := S.hybrid_energy_of_finite_inputs
    (PrimeArithmetic.Squarefree coords) hn hmu hq hc delta harmonic
    (fun X _ => hdelta0 X) hharmonic0 hdelta hharmonic eps heps
  refine ⟨C0, hC0, ?_⟩
  intro K N B L hK hN hB hL rows marks columns cubes a beta hrows hmarks hcolumns hcubes hbeta
  have H0 := canonical_finite_inputs coords S hn rfl cutoff hmem K N B L
    rows marks columns cubes hrows hmarks hcolumns hcubes
  have H : S.FiniteInputs (PrimeArithmetic.Squarefree coords) rows marks columns cubes
      (cutoff K) (cutoff K) (completion coords columns cubes)
      (fun _ _ => cutoff B) (fun _ _ => cutoff N)
      (fun _ _ => cutoff N) (fun _ _ => cutoff B)
      (fun _ _ => quadraticPairs coords S cutoff N B)
      (fun _ _ => cubicPairs coords S cutoff N)
      (squarefreeCutoff coords cutoff (N * B)) (squarefreeCutoff coords cutoff N)
      K (N * B) N L (delta K ^ 2) (delta (N * B)) (delta N)
      (harmonic B) (harmonic N) (harmonic B) := {
    local_pairs := H0.local_pairs
    pair_count := H0.pair_count
    quotient_rows := H0.quotient_rows
    quadratic_support := H0.quadratic_support
    cubic_support := H0.cubic_support
    mark_columns := H0.mark_columns
    quadratic_rectangle := H0.quadratic_rectangle
    cubic_rectangle := H0.cubic_rectangle
    quadratic_products := H0.quadratic_products
    quadratic_fibers := H0.quadratic_fibers
    cubic_products := H0.cubic_products
    cubic_fibers := H0.cubic_fibers
    box := H0.box
    quadratic_completion := H0.quadratic_completion
    cubic_completion := H0.cubic_completion
    t_harmonic := fun _ _ _ _ => hH B hB
    c_harmonic := fun _ _ _ _ => hH N hN
    h_harmonic := fun _ _ _ _ => hH B hB
  }
  have hmass : (∑ d ∈ cutoff K, S.columnMass a marks d / S.normI d) ≤
      delta L * S.originalColumnMass a marks := by
    apply S.columnMass_sum_le_divisors a marks (cutoff K) (delta L)
    · intro p hp d hdp
      exact mem_divisors_of_squarefree_dvd coords
        (squarefree_of_dvd coords hdp (hmarks p hp).1) hdp
    · intro p hp
      exact divisor_count_le_envelopeOfCounting coords normI q hnatural Ccount hcount
        L p (hmarks p hp).2
  have hb := hbound K N B L hK hN hB hL rows marks columns cubes
    (cutoff K) (cutoff K) (completion coords columns cubes)
    (fun _ _ => cutoff B) (fun _ _ => cutoff N)
    (fun _ _ => cutoff N) (fun _ _ => cutoff B)
    (fun _ _ => quadraticPairs coords S cutoff N B)
    (fun _ _ => cubicPairs coords S cutoff N)
    (squarefreeCutoff coords cutoff (N * B)) (squarefreeCutoff coords cutoff N)
    a beta hbeta hcubes H hmass (hH K hK)
  exact hb

#print axioms hybrid_energy

end
end HeckeSkeleton.LowHybrid
