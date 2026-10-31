import HeckePort.Moments.Poisson
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Ring

/-!
# Whole finite Gauss polynomials: exact expansion and the optional radial transform

The coefficient `c` is arbitrary.  It may therefore contain a centered
rectangle difference, all frozen extraction factors, the common mask and
every live prime slot.  The theorem expands the whole product only into
its exact sesquilinear coefficient array; it never estimates the two
centered rectangles separately.

Every pair uses `fullModulusCorrelation`, including nonprimitive and
noncoprime pairs.  The two analytic inputs are explicit: summability of
the actual weighted pair rows and the repository's `RadialPoissonData`.
The radial specialization is an optional formal lemma.  The repository
already provides general-number-field orbital summation in
`HeckeGeneral.Analysis.SIntegerPeriodicOrbitalPoisson`,
`SIntegerMaskedOrbitalPoisson`, and `SIntegerMaskedTruncation`.  Their native
sector and common-kernel interfaces are the route for the general-field
engine; they are not replaced by an assertion of radial data for every field.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStep

open scoped NumberField BigOperators Classical SchwartzMap
open HeckePort.Moments HeckePort.Moments.CommonSupport
open HeckePort.Moments.Fourier HeckePort.Moments.Poisson

/-- Exact finite sesquilinear expansion under the true pairwise convergence hypotheses. -/
theorem whole_bilinear_tsum {ι κ ρ : Type*} (S : Finset ι) (U : Finset κ)
    (c : ι → ℂ) (d : κ → ℂ) (F : ι → ρ → ℂ) (G : κ → ρ → ℂ) (W : ρ → ℂ)
    (hsum : ∀ a ∈ S, ∀ b ∈ U,
      Summable (fun z => F a z * star (G b z) * W z)) :
    (∑' z : ρ, (∑ a ∈ S, c a * F a z) * star (∑ b ∈ U, d b * G b z) * W z) =
      ∑ a ∈ S, ∑ b ∈ U, (c a * star (d b)) *
        ∑' z : ρ, F a z * star (G b z) * W z := by
  have hterm (z : ρ) :
      (∑ a ∈ S, c a * F a z) * star (∑ b ∈ U, d b * G b z) * W z =
        ∑ a ∈ S, ∑ b ∈ U, (c a * star (d b)) *
          (F a z * star (G b z) * W z) := by
    simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring
  have hweighted (a : ι) (ha : a ∈ S) (b : κ) (hb : b ∈ U) :
      Summable (fun z => (c a * star (d b)) * (F a z * star (G b z) * W z)) :=
    (hsum a ha b hb).mul_left (c a * star (d b))
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum (fun a ha => summable_sum (fun b hb => hweighted a ha b hb))]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Summable.tsum_finsetSum (fun b hb => hweighted a ha b hb)]
  apply Finset.sum_congr rfl
  intro b hb
  rw [tsum_mul_left]

variable {K : Type*} [Field K] [NumberField K]
variable {T : TraceFamily K} (R : RadialPoissonData T)

/-- The complete once-transformed bilinear form, for arbitrary two finite coefficient arrays. -/
theorem whole_bilinear_gauss_poisson {ι κ : Type*}
    (S : Finset ι) (U : Finset κ) (u : ι → 𝓞 K) (v : κ → 𝓞 K)
    [∀ a, Fintype (Residue (u a))] [∀ b, Fintype (Residue (v b))]
    [∀ a b, Fintype (Residue (u a * v b))]
    (χu : ∀ a, MulChar (Residue (u a)) ℂ) (χv : ∀ b, MulChar (Residue (v b)) ℂ)
    (c : ι → ℂ) (d : κ → ℂ) (hu : ∀ a ∈ S, u a ≠ 0) (hv : ∀ b ∈ U, v b ≠ 0)
    (W : 𝓢(ℝ, ℂ)) (H : ℝ) (hH : 0 < H)
    (hsum : ∀ a ∈ S, ∀ b ∈ U, Summable (fun z : 𝓞 K =>
      normalizedResidueGauss T (u a) (χu a) (Ideal.Quotient.mk _ z) *
        star (normalizedResidueGauss T (v b) (χv b) (Ideal.Quotient.mk _ z)) *
          W (R.norm2 z / H))) :
    (∑' z : 𝓞 K,
      (∑ a ∈ S, c a * normalizedResidueGauss T (u a) (χu a) (Ideal.Quotient.mk _ z)) *
        star (∑ b ∈ U, d b * normalizedResidueGauss T (v b) (χv b) (Ideal.Quotient.mk _ z)) *
          W (R.norm2 z / H)) =
      ∑ a ∈ S, ∑ b ∈ U,
        (c a * star (d b)) *
          ((H : ℂ) / ((Real.sqrt (Ideal.absNorm (Ideal.span {u a}) : ℝ) : ℂ) *
            (Real.sqrt (Ideal.absNorm (Ideal.span {v b}) : ℝ) : ℂ))) *
          ∑' j : 𝓞 K, fullModulusCorrelation (u a) (v b) (χu a) (χv b) (-j) *
            R.transform W (H * R.norm2 j / R.norm2 (u a * v b)) := by
  rw [whole_bilinear_tsum S U c d
    (fun a z => normalizedResidueGauss T (u a) (χu a) (Ideal.Quotient.mk _ z))
    (fun b z => normalizedResidueGauss T (v b) (χv b) (Ideal.Quotient.mk _ z))
    (fun z => W (R.norm2 z / H)) hsum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [normalized_gauss_pair_poisson R (u a) (v b) (hu a ha) (hv b hb) (χu a) (χv b) W H hH]
  ring

/-- The exact first or second transform of a whole finite row energy. -/
theorem whole_gauss_energy_poisson {ι : Type*}
    (S : Finset ι) (u : ι → 𝓞 K)
    [∀ a, Fintype (Residue (u a))] [∀ a b, Fintype (Residue (u a * u b))]
    (χ : ∀ a, MulChar (Residue (u a)) ℂ) (c : ι → ℂ)
    (hu : ∀ a ∈ S, u a ≠ 0) (W : 𝓢(ℝ, ℂ)) (H : ℝ) (hH : 0 < H)
    (hsum : ∀ a ∈ S, ∀ b ∈ S, Summable (fun z : 𝓞 K =>
      normalizedResidueGauss T (u a) (χ a) (Ideal.Quotient.mk _ z) *
        star (normalizedResidueGauss T (u b) (χ b) (Ideal.Quotient.mk _ z)) *
          W (R.norm2 z / H))) :
    (∑' z : 𝓞 K,
      (∑ a ∈ S, c a * normalizedResidueGauss T (u a) (χ a) (Ideal.Quotient.mk _ z)) *
        star (∑ b ∈ S, c b * normalizedResidueGauss T (u b) (χ b) (Ideal.Quotient.mk _ z)) *
          W (R.norm2 z / H)) =
      ∑ a ∈ S, ∑ b ∈ S,
        (c a * star (c b)) *
          ((H : ℂ) / ((Real.sqrt (Ideal.absNorm (Ideal.span {u a}) : ℝ) : ℂ) *
            (Real.sqrt (Ideal.absNorm (Ideal.span {u b}) : ℝ) : ℂ))) *
          ∑' j : 𝓞 K, fullModulusCorrelation (u a) (u b) (χ a) (χ b) (-j) *
            R.transform W (H * R.norm2 j / R.norm2 (u a * u b)) :=
  whole_bilinear_gauss_poisson R S S u u χ χ c c hu hu W H hH hsum

end HeckeSkeleton.Moments.EngineStep

end

#print axioms HeckeSkeleton.Moments.EngineStep.whole_bilinear_tsum
#print axioms HeckeSkeleton.Moments.EngineStep.whole_gauss_energy_poisson
