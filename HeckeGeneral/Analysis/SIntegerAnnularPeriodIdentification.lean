import HeckeGeneral.Analysis.SIntegerAnnularCosetReindex
import HeckeGeneral.Arithmetic.SIntegerMovingPeriodNormScale
/-! Join of the actual additive period and the bundled moving
ideal used by compact-shape transport. The auxiliary ideal is the same on
both sides; this does not assert periodicity of any additional ray factor. -/

noncomputable section
namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (M : (Ideal (𝓞 K))⁰)

/-- The coset reindexing and the compact-shape theorem use the identical
ordinary ideal, including every prime in S and the fixed refinement M. -/
@[simp] theorem sIntegerMovingPeriod_val_eq_annularPeriod
    (c : NonzeroRingElements (S.integer K)) :
    (sIntegerMovingPeriod K S M c).val =
      sIntegerAnnularSexticPeriod K S M.val c := by
  simp [sIntegerMovingPeriod, sIntegerAnnularSexticPeriod]

/-- Exact arithmetic size of the period. All growth in c is the actual
principal S-integer residue cardinality; the other factors are fixed. -/
theorem sIntegerAnnularPeriod_absNorm
    (c : NonzeroRingElements (S.integer K)) :
    (sIntegerAnnularSexticPeriod K S M.val c).absNorm =
      Nat.card (S.integer K ⧸ Ideal.span ({c.val} : Set (S.integer K))) *
        (∏ v : S, v.val.asIdeal.absNorm) * M.val.absNorm := by
  rw [natCard_sIntegerPrincipalResidue K S c.val c.property]
  simp only [sIntegerAnnularSexticPeriod, map_mul, map_prod]

end HeckeGeneral.Analysis
