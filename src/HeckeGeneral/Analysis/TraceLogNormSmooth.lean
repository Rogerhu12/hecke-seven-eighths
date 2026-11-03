import HeckeGeneral.Arithmetic.IdealTraceLattice
import HeckeGeneral.Arithmetic.SUnitArchimedeanBalancing
import HeckeGeneral.Analysis.SUnitJointRadialProfile
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.Group.Pi.Units

/-! The genuine archimedean product norm on weighted trace Euclidean space.
Its regular locus is precisely the inverse image of the units of the mixed
archimedean algebra. Logarithmic smoothness is proved on this open locus by
the real and complex coordinate norm calculus. Complex places retain their
actual multiplicity two in the product and logarithmic sum. -/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField NumberField.InfinitePlace IsDedekindDomain HeckeGeneral.Arithmetic
open scoped Classical ContDiff BigOperators

variable (K : Type) [Field K] [NumberField K]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "W" => mixedEmbedding.mixedSpace K

/-- The arithmetic product norm transported from mixed space, rather than
the Banach-space norm of the weighted Euclidean vector. -/
def traceArchProductNorm (z : V) : ℝ := mixedEmbedding.norm (traceToMixed K z)

def traceArchRegular : Set V := {z | traceArchProductNorm K z ≠ 0}

def traceArchLogNorm (z : V) : ℝ := Real.log (traceArchProductNorm K z)

theorem traceArchRegular_iff_places (z : V) :
    z ∈ traceArchRegular K ↔ ∀ w : InfinitePlace K,
      mixedEmbedding.normAtPlace w (traceToMixed K z) ≠ 0 :=
  mixedEmbedding.norm_ne_zero_iff

/-- The locus excludes each individual real or complex zero coordinate;
excluding just the zero vector would be insufficient. -/
theorem traceArchRegular_iff_coordinates (z : V) :
    z ∈ traceArchRegular K ↔
      (∀ w : {w : InfinitePlace K // IsReal w}, (traceToMixed K z).1 w ≠ 0) ∧
      (∀ w : {w : InfinitePlace K // IsComplex w}, (traceToMixed K z).2 w ≠ 0) := by
  rw [traceArchRegular_iff_places]
  constructor
  · intro hz
    constructor
    · intro w
      exact norm_ne_zero_iff.mp (by
        simpa only [mixedEmbedding.normAtPlace_apply_of_isReal w.property] using hz w.val)
    · intro w
      exact norm_ne_zero_iff.mp (by
        simpa only [mixedEmbedding.normAtPlace_apply_of_isComplex w.property] using hz w.val)
  · rintro ⟨hr, hc⟩ w
    by_cases hw : IsReal w
    · rw [mixedEmbedding.normAtPlace_apply_of_isReal hw]
      exact norm_ne_zero_iff.mpr (hr ⟨w, hw⟩)
    · rw [mixedEmbedding.normAtPlace_apply_of_isComplex
        (not_isReal_iff_isComplex.mp hw)]
      exact norm_ne_zero_iff.mpr (hc ⟨w, not_isReal_iff_isComplex.mp hw⟩)

theorem traceArchRegular_iff_isUnit (z : V) :
    z ∈ traceArchRegular K ↔ IsUnit (traceToMixed K z) := by
  rw [traceArchRegular_iff_coordinates, Prod.isUnit_iff]
  simp only [Pi.isUnit_iff, isUnit_iff_ne_zero]

theorem continuous_traceArchProductNorm : Continuous (traceArchProductNorm K) :=
  (mixedEmbedding.continuous_norm K).comp (traceToMixed K).continuous

theorem isOpen_traceArchRegular : IsOpen (traceArchRegular K) :=
  isOpen_ne_fun (continuous_traceArchProductNorm K) continuous_const

theorem traceArchProductNorm_pos {z : V} (hz : z ∈ traceArchRegular K) :
    0 < traceArchProductNorm K z :=
  lt_of_le_of_ne (mixedEmbedding.norm_nonneg _) hz.symm

theorem traceArchRegular_unit (u : Wˣ) :
    (traceToMixed K).symm (u : W) ∈ traceArchRegular K := by
  rw [traceArchRegular_iff_isUnit, ContinuousLinearEquiv.apply_symm_apply]
  exact u.isUnit

/-- Each local factor is smooth at a point of the actual regular locus. The
real absolute value and complex norm use their genuine nonzero hypotheses. -/
theorem contDiffAt_traceNormAtPlace (w : InfinitePlace K) {z : V}
    (hz : z ∈ traceArchRegular K) :
    ContDiffAt ℝ ∞ (fun x : V => mixedEmbedding.normAtPlace w (traceToMixed K x)) z := by
  have ht : ContDiff ℝ ∞ (traceToMixed K) := (traceToMixed K).contDiff
  have hcoords := (traceArchRegular_iff_coordinates K z).mp hz
  by_cases hw : IsReal w
  · simp_rw [mixedEmbedding.normAtPlace_apply_of_isReal hw]
    have hproj : ContDiff ℝ ∞ (fun x : V => (traceToMixed K x).1) :=
      contDiff_fst.comp ht
    have hf : ContDiff ℝ ∞ (fun x : V => (traceToMixed K x).1 ⟨w, hw⟩) :=
      contDiff_pi.mp hproj ⟨w, hw⟩
    exact hf.contDiffAt.norm ℝ (hcoords.1 ⟨w, hw⟩)
  · have hc := not_isReal_iff_isComplex.mp hw
    simp_rw [mixedEmbedding.normAtPlace_apply_of_isComplex hc]
    have hproj : ContDiff ℝ ∞ (fun x : V => (traceToMixed K x).2) :=
      contDiff_snd.comp ht
    have hf : ContDiff ℝ ∞ (fun x : V => (traceToMixed K x).2 ⟨w, hc⟩) :=
      contDiff_pi.mp hproj ⟨w, hc⟩
    exact hf.contDiffAt.norm ℂ (hcoords.2 ⟨w, hc⟩)

theorem contDiffAt_traceArchProductNorm {z : V} (hz : z ∈ traceArchRegular K) :
    ContDiffAt ℝ ∞ (traceArchProductNorm K) z := by
  change ContDiffAt ℝ ∞
    (fun x : V => ∏ w : InfinitePlace K,
      mixedEmbedding.normAtPlace w (traceToMixed K x) ^ mult w) z
  exact contDiffAt_prod (fun w _ => (contDiffAt_traceNormAtPlace K w hz).pow _)

theorem contDiffOn_traceArchProductNorm :
    ContDiffOn ℝ ∞ (traceArchProductNorm K) (traceArchRegular K) :=
  fun _ hz => (contDiffAt_traceArchProductNorm K hz).contDiffWithinAt

theorem contDiffAt_traceArchLogNorm {z : V} (hz : z ∈ traceArchRegular K) :
    ContDiffAt ℝ ∞ (traceArchLogNorm K) z :=
  (contDiffAt_traceArchProductNorm K hz).log hz

theorem contDiffOn_traceArchLogNorm :
    ContDiffOn ℝ ∞ (traceArchLogNorm K) (traceArchRegular K) :=
  fun _ hz => (contDiffAt_traceArchLogNorm K hz).contDiffWithinAt

/-- The logarithm is the sum with the actual infinite-place multiplicities. -/
theorem traceArchLogNorm_eq_sum {z : V} (hz : z ∈ traceArchRegular K) :
    traceArchLogNorm K z = ∑ w : InfinitePlace K,
      (mult w : ℝ) * Real.log (mixedEmbedding.normAtPlace w (traceToMixed K z)) := by
  have hn := (traceArchRegular_iff_places K z).mp hz
  unfold traceArchLogNorm traceArchProductNorm
  rw [mixedEmbedding.norm_apply, Real.log_prod (fun w _ => pow_ne_zero _ (hn w))]
  simp only [Real.log_pow]

theorem traceArchLogNorm_real_summand (w : {w : InfinitePlace K // IsReal w}) (z : V) :
    (mult w.val : ℝ) * Real.log (mixedEmbedding.normAtPlace w.val (traceToMixed K z)) =
      Real.log |(traceToMixed K z).1 w| := by
  simp only [w.property.mult_eq_one, Nat.cast_one, one_mul,
    mixedEmbedding.normAtPlace_apply_of_isReal w.property, Real.norm_eq_abs]

theorem traceArchLogNorm_complex_summand
    (w : {w : InfinitePlace K // IsComplex w}) (z : V) :
    (mult w.val : ℝ) * Real.log (mixedEmbedding.normAtPlace w.val (traceToMixed K z)) =
      2 * Real.log ‖(traceToMixed K z).2 w‖ := by
  simp only [w.property.mult_eq_two, Nat.cast_ofNat,
    mixedEmbedding.normAtPlace_apply_of_isComplex w.property]

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Evaluation on an actual S-local group element recovers its archimedean
factor, so the arithmetic normalization agrees exactly with the existing one. -/
theorem sLocalProductNorm_eq_traceArchProductNorm (x : sLocalMultiplicativeGroup K S) :
    sLocalProductNorm K S x =
      traceArchProductNorm K ((traceToMixed K).symm (x.1 : W)) *
        ∏ v : S, ‖(x.2 v).val‖ := by
  simp only [traceArchProductNorm, ContinuousLinearEquiv.apply_symm_apply, sLocalProductNorm]

theorem log_sLocalProductNorm_eq_traceArchLogNorm (x : sLocalMultiplicativeGroup K S) :
    Real.log (sLocalProductNorm K S x) =
      traceArchLogNorm K ((traceToMixed K).symm (x.1 : W)) +
        ∑ v : S, Real.log ‖(x.2 v).val‖ := by
  have hn (v : S) : ‖(x.2 v).val‖ ≠ 0 := norm_ne_zero_iff.mpr (Units.ne_zero _)
  have hp : (∏ v : S, ‖(x.2 v).val‖) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun v _ => hn v)
  rw [sLocalProductNorm, Real.log_mul (sLocal_archNorm_ne_zero K S x) hp,
    Real.log_prod (fun v _ => hn v)]
  simp only [traceArchLogNorm, traceArchProductNorm, ContinuousLinearEquiv.apply_symm_apply]

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

include Γ in
/-- The smooth log-radius orbital kernel now acts on the real weighted trace
vector space in both columns. Its domain excludes all coordinate hyperplanes. -/
theorem contDiffOn_sUnitJointRadialProfile_traceLogNorm
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (R : {r : ℝ // 0 < r}) (j : ℕ) :
    ContDiffOn ℝ ∞ (fun p : V × V => sUnitJointRadialProfile K S φ ψ R j
      (traceArchLogNorm K p.1, traceArchLogNorm K p.2))
      (traceArchRegular K ×ˢ traceArchRegular K) := by
  intro p hp
  have hfst : ContDiffAt ℝ ∞ (fun q : V × V => traceArchLogNorm K q.1) p :=
    (contDiffAt_traceArchLogNorm K hp.1).comp p contDiff_fst.contDiffAt
  have hsnd : ContDiffAt ℝ ∞ (fun q : V × V => traceArchLogNorm K q.2) p :=
    (contDiffAt_traceArchLogNorm K hp.2).comp p contDiff_snd.contDiffAt
  exact ((contDiff_sUnitJointRadialProfile K S Γ φ ψ hψ hψsupport R j).contDiffAt.comp p
    (hfst.prodMk hsnd)).contDiffWithinAt

/-- On the regular vector locus the composed kernel is literally the orbital
profile at R divided by the two arithmetic product norms. -/
theorem sUnitJointRadialProfile_traceLogNorm_eq
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (R : {r : ℝ // 0 < r}) (j : ℕ) (z w : V)
    (hz : z ∈ traceArchRegular K) (hw : w ∈ traceArchRegular K) :
    sUnitJointRadialProfile K S φ ψ R j (traceArchLogNorm K z, traceArchLogNorm K w) =
      sUnitOrbitalProfile K S
        (sLocalTensorTestFunction K S
          (traceSchwartzEulerIterCLM K j (HeckeGeneral.Bridge.traceSchwartzFourier K φ)) ψ)
        ⟨R.val / (traceArchProductNorm K z * traceArchProductNorm K w),
          div_pos R.property
            (mul_pos (traceArchProductNorm_pos K hz) (traceArchProductNorm_pos K hw))⟩ :=
  sUnitJointRadialProfile_at_logs K S φ ψ R
    ⟨traceArchProductNorm K z, traceArchProductNorm_pos K hz⟩
    ⟨traceArchProductNorm K w, traceArchProductNorm_pos K hw⟩ j

end HeckeGeneral.Analysis
