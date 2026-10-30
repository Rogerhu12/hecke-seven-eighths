import HeckeGeneral.Analysis.ConductorLatticeGauss
import HeckeGeneral.Analysis.LatticeSchwartzTail

/-!
The actual conductor Gauss coefficients in trace-lattice Poisson satisfy a
square-root conductor bound. Applying Schwartz decay gives absolute convergence
and a quantitative nonzero polar tail, with the fixed polar-lattice mass kept
explicit. Build and declaration-audit evidence is tracked in docs/NEXT_POISSON.md.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField HeckeGeneral.Arithmetic HeckeGeneral.Characters
open scoped Classical FourierTransform nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

local instance conductorResidueTailFintype (χ : HeckeCharacter K) :
    Fintype (𝓞 K ⧸ (finiteConductor K χ).val) := Fintype.ofFinite _

/-- The coefficients are those of the actual conductor-weighted Poisson sum.
Their bound is proved from the character, including all nonunit frequencies. -/
theorem summable_norm_scaled_conductor_fourier (χ : HeckeCharacter K)
    (f : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (v : mixedEmbedding.euclidean.mixedSpace K) (M : ℕ)
    (hM : Module.finrank ℤ
      (dualLattice (traceIdealLattice K (integralIdealUnit K (finiteConductor K χ)))) < M)
    {α : ℝ} (hα : 0 < α) :
    Summable fun m : NonzeroLattice
      (dualLattice (traceIdealLattice K (integralIdealUnit K (finiteConductor K χ)))) =>
      ‖latticePhase v m.val *
        gaussSum (conductorMulCharacter K χ)
          (integralLatticeAddCharacter K (finiteConductor K χ) m.val) *
        (𝓕 ⇑f) (α • (m.val : mixedEmbedding.euclidean.mixedSpace K))‖ := by
  apply summable_norm_scaled_weighted_schwartz _ (𝓕 f) M hM hα
    (C := Real.sqrt (Ideal.absNorm (finiteConductor K χ).val : ℝ))
  intro m
  simpa only [norm_mul, norm_latticePhase, one_mul] using
    conductorLatticeGauss_norm_le K χ m.val

/-- Square-root conductor dependence for the actual nonzero dual sum.
The lattice mass remains dependent on the actual conductor lattice. -/
theorem norm_tsum_scaled_conductor_fourier_le (χ : HeckeCharacter K)
    (f : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (v : mixedEmbedding.euclidean.mixedSpace K) (M : ℕ)
    (hM : Module.finrank ℤ
      (dualLattice (traceIdealLattice K (integralIdealUnit K (finiteConductor K χ)))) < M)
    {α : ℝ} (hα : 0 < α) :
    ‖∑' m : NonzeroLattice
      (dualLattice (traceIdealLattice K (integralIdealUnit K (finiteConductor K χ)))),
      latticePhase v m.val *
        gaussSum (conductorMulCharacter K χ)
          (integralLatticeAddCharacter K (finiteConductor K χ) m.val) *
        (𝓕 ⇑f) (α • (m.val : mixedEmbedding.euclidean.mixedSpace K))‖ ≤
      Real.sqrt (Ideal.absNorm (finiteConductor K χ).val : ℝ) *
        (SchwartzMap.seminorm ℂ M 0 (𝓕 f) * α⁻¹ ^ M *
          latticeInversePowerMass
            (dualLattice (traceIdealLattice K (integralIdealUnit K (finiteConductor K χ)))) M) := by
  apply norm_tsum_scaled_weighted_schwartz_le _ (𝓕 f) M hM hα (Real.sqrt_nonneg _)
  intro m
  simpa only [norm_mul, norm_latticePhase, one_mul] using
    conductorLatticeGauss_norm_le K χ m.val

end HeckeGeneral.Analysis
