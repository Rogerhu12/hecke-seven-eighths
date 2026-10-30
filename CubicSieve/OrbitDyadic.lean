import CubicSieve.OrbitRows
import CubicSieve.AnalyticDyadic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Dyadic summation over every actual sixth-unit orbit. A finite block
estimate proves absolute summability before any exchange with an infinite
orbit sum. No choice of a single unit sector enters the partition. -/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.OrbitDyadic

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open CubicSieve.ExteriorKernel CubicSieve.OrbitRows
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

include D in
theorem orbitNorm_eq_idealNorm (q : Orbits K S) :
    (sIntegerOrbitNorm K S (Γ K S) q).val = exteriorNorm K S (orbitIdeal K S q) := by
  obtain ⟨⟨I, l⟩, rfl⟩ := classOrbit_surjective K S D q
  change (sIntegerOrbitNorm K S (Γ K S) (scalarOrbit K S D I l.out)).val =
    exteriorNorm K S (orbitIdeal K S (scalarOrbit K S D I l.out))
  rw [orbitIdeal_scalarOrbit]
  exact scalarOrbit_norm K S D I l.out

def bin (q : Orbits K S) : ℕ := AnalyticDyadic.normBin K S (orbitIdeal K S q)

include D in
theorem bin_bounds (q : Orbits K S) :
    (2 : ℝ) ^ bin K S q ≤ (sIntegerOrbitNorm K S (Γ K S) q).val ∧
      (sIntegerOrbitNorm K S (Γ K S) q).val ≤ (2 : ℝ) ^ (bin K S q + 1) := by
  rw [orbitNorm_eq_idealNorm K S D]
  have hb := AnalyticDyadic.normBin_bounds K S (orbitIdeal K S q)
  simpa only [bin, pow_succ, mul_comm] using hb

include D in
/-- Uniform finite block estimates imply the full nonnegative orbit estimate.
The zero-th dyadic budget may be unused; all actual orbits occur once. -/
theorem tsum_le_of_blocks (f : Orbits K S → ℝ) (hf : ∀ q, 0 ≤ f q)
    (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (hs : Summable b)
    (hblock : ∀ j : ℕ, ∀ R : Finset (Orbits K S),
      (∀ q ∈ R, (2 : ℝ) ^ j ≤ (sIntegerOrbitNorm K S (Γ K S) q).val ∧
        (sIntegerOrbitNorm K S (Γ K S) q).val ≤ (2 : ℝ) ^ (j + 1)) →
      (∑ q ∈ R, f q) ≤ b (j + 1)) :
    Summable f ∧ (∑' q, f q) ≤ ∑' j, b j := by
  have hfinite (R : Finset (Orbits K S)) : (∑ q ∈ R, f q) ≤ ∑' j, b j := by
    let J := R.image (bin K S)
    have hp : (∑ j ∈ J, ∑ q ∈ R.filter (fun q => bin K S q = j), f q) =
        ∑ q ∈ R, f q :=
      Finset.sum_fiberwise_of_maps_to (fun q hq => Finset.mem_image_of_mem _ hq) _
    calc
      _ = ∑ j ∈ J, ∑ q ∈ R.filter (fun q => bin K S q = j), f q := hp.symm
      _ ≤ ∑ j ∈ J, b (j + 1) := by
        apply Finset.sum_le_sum
        intro j hj
        apply hblock
        intro q hq
        obtain ⟨_, he⟩ := Finset.mem_filter.mp hq
        simpa only [he] using bin_bounds K S D q
      _ = ∑ i ∈ J.image Nat.succ, b i := by
        rw [Finset.sum_image Nat.succ_injective.injOn]
      _ ≤ ∑' i, b i := hs.sum_le_tsum _ (fun i hi => hb i)
  exact ⟨summable_of_sum_le hf hfinite, Real.tsum_le_of_sum_le hf hfinite⟩

end CubicSieve.OrbitDyadic
