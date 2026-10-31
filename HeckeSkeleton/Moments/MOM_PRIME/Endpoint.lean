import HeckeSkeleton.Moments.MOM_PRIME.Interface
import HeckeSkeleton.Moments.MOM_PRIME.AbsoluteGeometry

/-!
# The whole-family prime endpoint

The fixed physical prime geometry supplies a single constant before every
source index, height, scale, character, and model.  The resulting estimate
is stronger than the endpoint with a positive loss: its power is exactly
`1 + selectedLength`, with no height cost.  The last theorem gives the
threshold/height quantifier order of `UniformMomentBound` without importing
the unfinished source construction.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- The absolute endpoint for the entire selected-slot and sector family.
The constant precedes even the family of models; it depends only on `K`,
the fixed physical windows, and the finite number of sectors. -/
theorem paired_primes_endpoint (g : PrimeWindowGeometry) (Sector : Type*)
    [Fintype Sector] :
    ∃ C : ℝ, 0 < C ∧ ∀ {ω ψ : HeckeCharacter K} {Index : ℝ → ℝ → Type*}
      (F : PrimeEndpointFamily K g ω ψ Index Sector) (Z T : ℝ) (i : Index Z T),
      1 ≤ Z → F.energy i ≤ C * F.base i ^ (1 + F.selectedLength i) := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_actualSelectedPrimeGeometry_absolute_bound K g
  refine ⟨((Fintype.card Sector : ℝ) + 1) * C₀, by positivity, ?_⟩
  intro ω ψ Index F Z T i hZ
  have hbase := F.one_le_base i hZ
  have hs (s : Sector) :
      (∑ u ∈ pairedRows (F.data Z T i s) (F.parameters Z T i) (F.base i),
        ‖slotProduct (F.data Z T i s) u (F.base i) 0‖ ^ 2) ≤
          C₀ * F.base i ^ (1 + F.selectedLength i) := by
    have h := hbound (F.data Z T i s) (F.shell Z T i) (F.shell_pos Z T i)
      (F.selected Z T i) (F.parameters Z T i) (F.base i) 0 (F.geometry Z T i s)
      hbase (by rw [F.row_width]; norm_num)
    simpa only [F.row_width, PrimeEndpointFamily.selectedLength] using h
  calc
    _ ≤ ∑ _s : Sector, C₀ * F.base i ^ (1 + F.selectedLength i) :=
      Finset.sum_le_sum (fun s _ => hs s)
    _ = (Fintype.card Sector : ℝ) * C₀ * F.base i ^ (1 + F.selectedLength i) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ ((Fintype.card Sector : ℝ) + 1) * C₀ *
        F.base i ^ (1 + F.selectedLength i) := by
      gcongr
      linarith

/-- The source's exact uniform quantifier order, with zero height loss and
threshold one.  Any nonnegative loss `δ` and any eligibility predicate may
be used downstream, because the preceding endpoint holds for every index.
-/
theorem paired_primes_endpoint_uniform (g : PrimeWindowGeometry) (Sector : Type*)
    [Fintype Sector] {ω ψ : HeckeCharacter K} {Index : ℝ → ℝ → Type*}
    (F : PrimeEndpointFamily K g ω ψ Index Sector) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∃ A ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ ceiling →
        ∃ Z₀ k : ℝ, 1 ≤ Z₀ ∧ 0 ≤ k ∧
          ∀ Z : ℝ, Z₀ ≤ Z → ∀ i : Index Z (Z ^ τ),
            F.energy i ≤
              k * F.base i ^ (1 + F.selectedLength i + δ) * (1 + Z ^ τ) ^ A := by
  obtain ⟨C, hC, hbound⟩ := paired_primes_endpoint K g Sector
  refine ⟨0, 1, le_rfl, zero_lt_one, ?_⟩
  intro τ _ _
  refine ⟨1, C, le_rfl, hC.le, ?_⟩
  intro Z hZ i
  simp only [Real.rpow_zero, mul_one]
  exact (hbound F Z (Z ^ τ) i hZ).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (F.one_le_base i hZ) (by linarith)) hC.le)

end HeckeSkeleton.Moments.MOM_PRIME
