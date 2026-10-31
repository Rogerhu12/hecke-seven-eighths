import HeckeGeneral.Analysis.SUnitTotalNormFourierBounds

/-!
UNCOMPILED / native 0. The original two independent Γ sums, including
finite fibres, reconstruct the total-norm compensated kernel and phase.
The compensated radius MOVES with the finite fibres; only the resulting
orbital profile parameter is invariant. Actual compact partition support
proves finite support of the double family, without a convergence input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.Analysis.ActualTotalNormUnitPartitionDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped Classical BigOperators ContDiff

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K)) [Subgroup.FiniteIndex Γ]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Z" => SFiniteLocalGroup K S
local notation "Regular" => traceArchRegular K

/-- Genuine finite support of one actual translated annular cutoff. -/
theorem finite_cutoff_translates (a : ℝ → ℝ) (ζ : Z) (x : Regular) :
    Set.Finite (Function.support (fun u : Γ =>
      sUnitAnnularPartitionCutoff K S Γ a ((sLocalDiagonal K S u.val).2 * ζ)
        (sUnitPartitionArchTranslate K S Γ u x).val)) := by
  have h := finite_sUnitPartition_nonzero_terms K S Γ
    (sUnitNormalizedPartition K S Γ) (hasCompactSupport_sUnitNormalizedPartition K S Γ)
    (sUnitPartitionFibreNormalize K S ζ x)
  apply h.subset
  intro u hu
  change sUnitNormalizedPartition K S Γ
    (sUnitPartitionDiagonal K S Γ u * sUnitPartitionFibreNormalize K S ζ x) ≠ 0
  intro hz
  apply hu
  dsimp only
  rw [sUnitAnnularPartitionCutoff_translate, hz, mul_zero]

variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]

/-- Kernel covariance uses both preserved total column norms, not a false
invariance of the archimedean radius alone. -/
theorem compensatedKernel_translate
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (ζ ξ : Z) (R : {r : ℝ // 0 < r}) (x y : Regular) (u v : Γ) :
    traceJointOrbitalKernel K S φ ψ
      (sUnitTotalNormRadius K S ((sLocalDiagonal K S u.val).2 * ζ)
        ((sLocalDiagonal K S v.val).2 * ξ) R)
      ((sUnitPartitionArchTranslate K S Γ u x).val,
        (sUnitPartitionArchTranslate K S Γ v y).val) =
    traceJointOrbitalKernel K S φ ψ (sUnitTotalNormRadius K S ζ ξ R)
      (x.val, y.val) := by
  rw [traceJointOrbitalKernel_totalNormRadius, traceJointOrbitalKernel_totalNormRadius]
  congr 1
  apply Subtype.ext
  exact congrArg (fun t : ℝ => R.val / t)
    (congrArg₂ (fun b c : ℝ => b * c)
      (sUnitPartitionFibre_totalNorm_translate K S Γ u ζ x)
      (sUnitPartitionFibre_totalNorm_translate K S Γ v ξ y))

/-- The literal translated kernel, total phase and joint partition term. -/
def translatedJointTerm
    (a : ℝ → ℝ) (ν : ℝ) (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (ζ ξ : Z) (R : {r : ℝ // 0 < r}) (x y : Regular) (u v : Γ) : ℂ :=
  sUnitMellinPhase K S ν ((sLocalDiagonal K S u.val).2 * ζ)
    ((sLocalDiagonal K S v.val).2 * ξ)
    ((sUnitPartitionArchTranslate K S Γ u x).val,
      (sUnitPartitionArchTranslate K S Γ v y).val) *
  (sUnitAnnularPartitionJointCutoff K S Γ a
      ((sLocalDiagonal K S u.val).2 * ζ) ((sLocalDiagonal K S v.val).2 * ξ)
      ((sUnitPartitionArchTranslate K S Γ u x).val,
        (sUnitPartitionArchTranslate K S Γ v y).val) *
    traceJointOrbitalKernel K S φ ψ
      (sUnitTotalNormRadius K S ((sLocalDiagonal K S u.val).2 * ζ)
        ((sLocalDiagonal K S v.val).2 * ξ) R)
      ((sUnitPartitionArchTranslate K S Γ u x).val,
        (sUnitPartitionArchTranslate K S Γ v y).val))

/-- Every nonzero pair lies in the product of two actual finite partition supports. -/
theorem translatedJointTerm_finiteSupport
    (a : ℝ → ℝ) (ν : ℝ) (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (ζ ξ : Z) (R : {r : ℝ // 0 < r}) (x y : Regular) :
    Set.Finite (Function.support (fun p : Γ × Γ =>
      translatedJointTerm K S Γ a ν φ ψ ζ ξ R x y p.1 p.2)) := by
  apply ((finite_cutoff_translates K S Γ a ζ x).prod
    (finite_cutoff_translates K S Γ a ξ y)).subset
  rintro ⟨u, v⟩ hp
  constructor
  · change sUnitAnnularPartitionCutoff K S Γ a
      ((sLocalDiagonal K S u.val).2 * ζ)
      (sUnitPartitionArchTranslate K S Γ u x).val ≠ 0
    intro hz
    exact hp (by simp only [translatedJointTerm, sUnitAnnularPartitionJointCutoff,
      hz, zero_mul, Complex.ofReal_zero, mul_zero])
  · change sUnitAnnularPartitionCutoff K S Γ a
      ((sLocalDiagonal K S v.val).2 * ξ)
      (sUnitPartitionArchTranslate K S Γ v y).val ≠ 0
    intro hz
    exact hp (by simp only [translatedJointTerm, sUnitAnnularPartitionJointCutoff,
      hz, mul_zero, Complex.ofReal_zero, zero_mul])

/-- In particular the actual double family is genuinely summable. -/
theorem translatedJointTerm_summable
    (a : ℝ → ℝ) (ν : ℝ) (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (ζ ξ : Z) (R : {r : ℝ // 0 < r}) (x y : Regular) :
    Summable (fun p : Γ × Γ =>
      translatedJointTerm K S Γ a ν φ ψ ζ ξ R x y p.1 p.2) :=
  summable_of_hasFiniteSupport
    (translatedJointTerm_finiteSupport K S Γ a ν φ ψ ζ ξ R x y)

/-- Reconstruction with the SAME original Γ, both moving finite coordinates,
and two independent unit sums. No arithmetic coefficient is moved here. -/
theorem translatedJointTerm_two_column
    (a : ℝ → ℝ) (ν : ℝ) (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (ζ ξ : Z) (R : {r : ℝ // 0 < r}) (x y : Regular) :
    (∑' u : Γ, ∑' v : Γ, translatedJointTerm K S Γ a ν φ ψ ζ ξ R x y u v) =
    sUnitMellinPhase K S ν ζ ξ (x.val, y.val) *
      traceJointOrbitalKernel K S φ ψ (sUnitTotalNormRadius K S ζ ξ R) (x.val, y.val) *
      ((a (traceArchProductNorm K x.val * sFiniteProductNorm K S ζ) *
        a (traceArchProductNorm K y.val * sFiniteProductNorm K S ξ) : ℝ) : ℂ) := by
  have hterm (u v : Γ) :
      translatedJointTerm K S Γ a ν φ ψ ζ ξ R x y u v =
      (sUnitMellinPhase K S ν ζ ξ (x.val, y.val) *
        traceJointOrbitalKernel K S φ ψ (sUnitTotalNormRadius K S ζ ξ R) (x.val, y.val)) *
      ((sUnitAnnularPartitionCutoff K S Γ a ((sLocalDiagonal K S u.val).2 * ζ)
          (sUnitPartitionArchTranslate K S Γ u x).val *
        sUnitAnnularPartitionCutoff K S Γ a ((sLocalDiagonal K S v.val).2 * ξ)
          (sUnitPartitionArchTranslate K S Γ v y).val : ℝ) : ℂ) := by
    unfold translatedJointTerm
    rw [sUnitMellinPhase_translate, compensatedKernel_translate]
    unfold sUnitAnnularPartitionJointCutoff
    ring
  simp_rw [hterm, tsum_mul_left, ← Complex.ofReal_tsum,
    sUnitAnnularPartitionCutoff_two_column]

/-- Direct specialization to the already constructed actual joint Schwartz
profile: the finite fibres AND the compensated radius move in each term. -/
theorem actualJointSchwartz_two_column
    (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a) (a0 b0 : ℝ) (ha0 : 0 < a0)
    (haSupport : tsupport a ⊆ Set.Icc a0 b0)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (ν : ℝ) (φ : SchwartzMap V ℂ) (ζ ξ : Z)
    (R : {r : ℝ // 0 < r}) (x y : Regular) :
    (∑' u : Γ, ∑' v : Γ,
      sUnitTotalNormAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
        ψ hψ hψsupport ν ((sLocalDiagonal K S u.val).2 * ζ)
        ((sLocalDiagonal K S v.val).2 * ξ) φ R
        ((sUnitPartitionArchTranslate K S Γ u x).val,
          (sUnitPartitionArchTranslate K S Γ v y).val)) =
    sUnitMellinPhase K S ν ζ ξ (x.val, y.val) *
      traceJointOrbitalKernel K S φ ψ (sUnitTotalNormRadius K S ζ ξ R) (x.val, y.val) *
      ((a (traceArchProductNorm K x.val * sFiniteProductNorm K S ζ) *
        a (traceArchProductNorm K y.val * sFiniteProductNorm K S ξ) : ℝ) : ℂ) := by
  simp_rw [sUnitTotalNormAnnularPartitionJointSchwartz_apply]
  exact translatedJointTerm_two_column K S Γ a ν φ ψ ζ ξ R x y

end HeckeGeneral.Analysis.ActualTotalNormUnitPartitionDraft
