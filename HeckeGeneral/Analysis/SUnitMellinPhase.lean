import HeckeGeneral.Analysis.TraceMovingPhaseBounds
import HeckeGeneral.Analysis.SUnitPartitionCovariance

/-!
# The actual total S-local Mellin phase

On a fixed finite fibre, the total phase is the archimedean moving phase
times a genuine finite-coordinate unit-modulus constant. Under independent
S-unit translations both the finite and archimedean coordinates change.
Their actual product norms are preserved, giving strict invariance of the
total phase. Unit modulus alone is not used to infer invariance.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField NumberField.InfinitePlace IsDedekindDomain HeckeGeneral.Arithmetic
open scoped Classical

private theorem traceRealMovingPhase_add (ν s t : ℝ) :
    traceRealMovingPhase ν (s + t) =
      traceRealMovingPhase ν s * traceRealMovingPhase ν t := by
  simp only [traceRealMovingPhase, Complex.ofReal_add, mul_add, Complex.exp_add]

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- The fixed-fibre compensation, formed from the actual finite local norms. -/
def sUnitMellinFiniteFactor (ν : ℝ) (ζ ξ : SFiniteLocalGroup K S) : ℂ :=
  traceRealMovingPhase ν
    (Real.log (sFiniteProductNorm K S ζ) - Real.log (sFiniteProductNorm K S ξ))

/-- The genuine Mellin phase of the two total S-local product norms.
The formula is totalized outside regular columns; factorization below is
stated on the actual regular locus, where both archimedean norms are positive. -/
def sUnitMellinPhase (ν : ℝ) (ζ ξ : SFiniteLocalGroup K S) (p : V × V) : ℂ :=
  traceRealMovingPhase ν
    (Real.log (traceArchProductNorm K p.1 * sFiniteProductNorm K S ζ) -
      Real.log (traceArchProductNorm K p.2 * sFiniteProductNorm K S ξ))

theorem norm_sUnitMellinFiniteFactor (ν : ℝ) (ζ ξ : SFiniteLocalGroup K S) :
    ‖sUnitMellinFiniteFactor K S ν ζ ξ‖ = 1 :=
  norm_traceRealMovingPhase _ _

theorem norm_sUnitMellinPhase (ν : ℝ) (ζ ξ : SFiniteLocalGroup K S) (p : V × V) :
    ‖sUnitMellinPhase K S ν ζ ξ p‖ = 1 :=
  norm_traceRealMovingPhase _ _

/-- Exact finite compensation of the existing archimedean moving phase. -/
theorem sUnitMellinPhase_eq_finiteFactor_mul_traceMovingPhase
    (ν : ℝ) (ζ ξ : SFiniteLocalGroup K S) (p : V × V)
    (hx : p.1 ∈ traceArchRegular K) (hy : p.2 ∈ traceArchRegular K) :
    sUnitMellinPhase K S ν ζ ξ p =
      sUnitMellinFiniteFactor K S ν ζ ξ * traceMovingPhase K ν p := by
  have hx0 := (traceArchProductNorm_pos K hx).ne'
  have hy0 := (traceArchProductNorm_pos K hy).ne'
  have hζ0 := (sFiniteProductNorm_pos K S ζ).ne'
  have hξ0 := (sFiniteProductNorm_pos K S ξ).ne'
  have hlog :
      Real.log (traceArchProductNorm K p.1 * sFiniteProductNorm K S ζ) -
        Real.log (traceArchProductNorm K p.2 * sFiniteProductNorm K S ξ) =
      (Real.log (sFiniteProductNorm K S ζ) - Real.log (sFiniteProductNorm K S ξ)) +
        (traceArchLogNorm K p.1 - traceArchLogNorm K p.2) := by
    rw [Real.log_mul hx0 hζ0, Real.log_mul hy0 hξ0]
    unfold traceArchLogNorm
    ring
  change traceRealMovingPhase ν _ =
    traceRealMovingPhase ν _ * traceRealMovingPhase ν _
  rw [hlog, traceRealMovingPhase_add, traceLogNormDifference_apply]

variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

/-- Independent translations by the original Γ preserve the actual total
phase, with the finite coordinates translated along with each arch column. -/
theorem sUnitMellinPhase_translate
    (ν : ℝ) (u v : Γ) (ζ ξ : SFiniteLocalGroup K S)
    (x y : traceArchRegular K) :
    sUnitMellinPhase K S ν
      ((sLocalDiagonal K S u.val).2 * ζ)
      ((sLocalDiagonal K S v.val).2 * ξ)
      ((sUnitPartitionArchTranslate K S Γ u x).val,
        (sUnitPartitionArchTranslate K S Γ v y).val) =
      sUnitMellinPhase K S ν ζ ξ (x.val, y.val) := by
  unfold sUnitMellinPhase
  rw [sUnitPartitionFibre_totalNorm_translate K S Γ u ζ x,
    sUnitPartitionFibre_totalNorm_translate K S Γ v ξ y]

/-- The exact compensated arch-phase covariance. The individual arch phase
need not be invariant; the translated finite factor is retained literally. -/
theorem sUnitMellinFiniteFactor_mul_traceMovingPhase_translate
    (ν : ℝ) (u v : Γ) (ζ ξ : SFiniteLocalGroup K S)
    (x y : traceArchRegular K) :
    sUnitMellinFiniteFactor K S ν
      ((sLocalDiagonal K S u.val).2 * ζ)
      ((sLocalDiagonal K S v.val).2 * ξ) *
        traceMovingPhase K ν
          ((sUnitPartitionArchTranslate K S Γ u x).val,
            (sUnitPartitionArchTranslate K S Γ v y).val) =
      sUnitMellinFiniteFactor K S ν ζ ξ * traceMovingPhase K ν (x.val, y.val) := by
  have htranslated := sUnitMellinPhase_eq_finiteFactor_mul_traceMovingPhase K S ν
    ((sLocalDiagonal K S u.val).2 * ζ) ((sLocalDiagonal K S v.val).2 * ξ)
    ((sUnitPartitionArchTranslate K S Γ u x).val,
      (sUnitPartitionArchTranslate K S Γ v y).val)
    (sUnitPartitionArchTranslate K S Γ u x).property
    (sUnitPartitionArchTranslate K S Γ v y).property
  have hbase := sUnitMellinPhase_eq_finiteFactor_mul_traceMovingPhase K S ν ζ ξ
    (x.val, y.val) x.property y.property
  exact htranslated.symm.trans
    ((sUnitMellinPhase_translate K S Γ ν u v ζ ξ x y).trans hbase)

end HeckeGeneral.Analysis
