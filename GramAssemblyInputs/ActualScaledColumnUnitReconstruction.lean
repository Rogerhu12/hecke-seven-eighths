import ActualTotalNormUnitPartitionReconstruction
import ActualOriginalJointFactor
import ActualTraceProductFourierDilation
import HeckeGeneral.Analysis.SIntegerAnnularColumnFinite
import HeckeGeneral.Arithmetic.SIntegerOrbitEnumeration
import HeckeGeneral.Arithmetic.SIntegerModulusNorm

/-!
UNCOMPILED / native 0. The actual S-integer columns, with degree-root
archimedean scaling and their original finite diagonal coordinates,
instantiate the original two independent unit-partition sums. The divisor
is fixed. Each term uses its own finite-norm compensated radius.
No coefficient, ideal-sum rearrangement or analytic bound is asserted here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.Analysis.ActualScaledColumnUnitDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open ActualGramJointChartDraft
open ActualClearedJointPeriodicDraft ActualTraceProductFourierDilationDraft
open ActualTotalNormUnitPartitionDraft
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "NZ" => NonzeroRingElements (S.integer K)
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "M" => mixedEmbedding.mixedSpace K
local notation "Z" => SFiniteLocalGroup K S

/-- Only the archimedean coordinates are scaled; the finite coordinates
are exactly the diagonal of the supplied nonzero S-integer. -/
def scaledColumnLocal (n : NZ) (N : ℝ) (hN : 0 < N) :
    sLocalMultiplicativeGroup K S :=
  sLocalNormSection K S ⟨N⁻¹, inv_pos.mpr hN⟩ *
    sLocalNonzeroIntegerDiagonal K S n

theorem scaledColumnLocal_finite (n : NZ) (N : ℝ) (hN : 0 < N) :
    (scaledColumnLocal K S n N hN).2 = (sLocalNonzeroIntegerDiagonal K S n).2 := by
  change 1 * (sLocalNonzeroIntegerDiagonal K S n).2 = _
  exact one_mul _

def scaledColumnArch (n : NZ) (N : ℝ) (hN : 0 < N) : traceArchRegular K :=
  ⟨(traceToMixed K).symm ((scaledColumnLocal K S n N hN).1 : M),
    traceArchRegular_unit K (scaledColumnLocal K S n N hN).1⟩

/-- The local-group construction has exactly the trace coordinate used
by originalJointFactor and sIntegerAnnularColumn. -/
theorem scaledColumnArch_val (n : NZ) (N : ℝ) (hN : 0 < N) :
    (scaledColumnArch K S n N hN).val =
      (traceNormScale K N)⁻¹ • traceEmbedding K (n.val : K) := by
  apply (traceToMixed K).injective
  change traceToMixed K ((traceToMixed K).symm
    ((scaledColumnLocal K S n N hN).1 : M)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply, map_smul]
  simp only [traceEmbedding, ContinuousLinearEquiv.apply_symm_apply]
  change algebraMap ℝ M (N⁻¹ ^ ((Module.finrank ℚ K : ℝ)⁻¹)) *
    mixedEmbedding K (n.val : K) = _
  rw [Real.inv_rpow hN.le]
  simp only [traceNormScale, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul]

theorem scaledColumn_totalNorm (n : NZ) (N : ℝ) (hN : 0 < N) :
    traceArchProductNorm K (scaledColumnArch K S n N hN).val *
      sFiniteProductNorm K S (sLocalNonzeroIntegerDiagonal K S n).2 =
      (sIntegerElementNorm K S n).val / N := by
  have hn : sLocalProductNorm K S (scaledColumnLocal K S n N hN) =
      (sIntegerElementNorm K S n).val / N := by
    rw [scaledColumnLocal, sLocalProductNorm_mul, sLocalProductNorm_section]
    change N⁻¹ * (sIntegerElementNorm K S n).val = _
    rw [div_eq_mul_inv, mul_comm]
  rw [sLocalProductNorm_eq_traceArchProductNorm] at hn
  change traceArchProductNorm K (scaledColumnArch K S n N hN).val *
    sFiniteProductNorm K S (scaledColumnLocal K S n N hN).2 = _ at hn
  simpa only [scaledColumnLocal_finite] using hn

/-- The numerator is the norm of the actual contracted principal ideal,
including denominator removal at S, rather than the full field norm. -/
theorem scaledColumn_totalNorm_eq_idealNorm (n : NZ) (N : ℝ) (hN : 0 < N) :
    traceArchProductNorm K (scaledColumnArch K S n N hN).val *
      sFiniteProductNorm K S (sLocalNonzeroIntegerDiagonal K S n).2 =
      (Ideal.absNorm (sIntegerModulusContraction K S n.val) : ℝ) / N := by
  rw [scaledColumn_totalNorm]
  have hn := natCard_sIntegerPrincipalResidue_eq_productNorm K S n.val n.property
  rw [natCard_sIntegerPrincipalResidue K S n.val n.property] at hn
  exact congrArg (fun t : ℝ => t / N) hn.symm

variable (Γ : Subgroup (S.unit K)) [Subgroup.FiniteIndex Γ]

theorem scaledColumnLocal_translate (u : Γ) (n : NZ) (N : ℝ) (hN : 0 < N) :
    scaledColumnLocal K S (sIntegerOrbitTranslate K S Γ u n) N hN =
      sLocalDiagonal K S u.val * scaledColumnLocal K S n N hN := by
  rw [scaledColumnLocal, sLocalNonzeroIntegerDiagonal_translate, scaledColumnLocal]
  exact mul_left_comm _ _ _

theorem scaledColumnFinite_translate (u : Γ) (n : NZ) :
    (sLocalNonzeroIntegerDiagonal K S (sIntegerOrbitTranslate K S Γ u n)).2 =
      (sLocalDiagonal K S u.val).2 * (sLocalNonzeroIntegerDiagonal K S n).2 := by
  rw [sLocalNonzeroIntegerDiagonal_translate]
  rfl

theorem scaledColumnArch_translate (u : Γ) (n : NZ) (N : ℝ) (hN : 0 < N) :
    scaledColumnArch K S (sIntegerOrbitTranslate K S Γ u n) N hN =
      sUnitPartitionArchTranslate K S Γ u (scaledColumnArch K S n N hN) := by
  apply Subtype.ext
  apply (traceToMixed K).injective
  simp only [scaledColumnArch, scaledColumnLocal_translate,
    sUnitPartitionArchTranslate_val, traceToMixed_traceUnitMulEquiv,
    ContinuousLinearEquiv.apply_symm_apply, Prod.fst_mul, Units.val_mul]

theorem scaledColumn_annular (a : ℝ → ℝ) (n : NZ) (N : ℝ) (hN : 0 < N) :
    sIntegerAnnularColumn K S Γ a (traceNormScale K N) n =
      sUnitAnnularPartitionCutoff K S Γ a
        (sLocalNonzeroIntegerDiagonal K S n).2 (scaledColumnArch K S n N hN).val := by
  rw [scaledColumnArch_val]
  rfl

private theorem divisorColumn_translate_right (u : Γ) (d m : NZ) :
    divisorColumn K S d (sIntegerOrbitTranslate K S Γ u m) =
      sIntegerOrbitTranslate K S Γ u (divisorColumn K S d m) := by
  apply Subtype.ext
  change d.val * ((S.unitEquivUnitsInteger K u.val).val * m.val) =
    (S.unitEquivUnitsInteger K u.val).val * (d.val * m.val)
  ring

variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]

/-- The actual original non-cutoff factor at both columns' own finite
coordinates and the corrected total-norm radius. -/
def scaledColumnCompensatedJointFactor
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (d : NZ) (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r})
    (N : ℝ) (m : NZ × NZ) : ℂ :=
  let z₁ := (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m.1)).2
  let z₂ := (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m.2)).2
  originalJointFactor K S ψ d ν z₁ z₂ φ (sUnitTotalNormRadius K S z₁ z₂ R)
    (traceNormScale K N) m

/-- The two actual annular columns times that literal original factor. -/
def scaledColumnAnnularJointTerm (a : ℝ → ℝ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (d : NZ) (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r})
    (N : ℝ) (m : NZ × NZ) : ℂ :=
  (sIntegerAnnularColumn K S Γ a (traceNormScale K N) (divisorColumn K S d m.1) : ℂ) *
    (sIntegerAnnularColumn K S Γ a (traceNormScale K N) (divisorColumn K S d m.2) : ℂ) *
    scaledColumnCompensatedJointFactor K S ψ d ν φ R N m

/-- Pointwise bridge from the original summand coordinates to the pure
analysis partition term; Γ acts independently with the divisor fixed. -/
theorem scaledColumnAnnularJointTerm_eq_translated
    (a : ℝ → ℝ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (d m₁ m₂ : NZ) (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r})
    (N : ℝ) (hN : 0 < N) (u v : Γ) :
    scaledColumnAnnularJointTerm K S Γ a ψ d ν φ R N
      (sIntegerOrbitTranslate K S Γ u m₁, sIntegerOrbitTranslate K S Γ v m₂) =
    translatedJointTerm K S Γ a ν φ ψ
      (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₁)).2
      (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₂)).2 R
      (scaledColumnArch K S (divisorColumn K S d m₁) N hN)
      (scaledColumnArch K S (divisorColumn K S d m₂) N hN) u v := by
  have hx (t : Γ) (n : NZ) :
      (traceNormScale K N)⁻¹ • traceEmbedding K
          ((sIntegerOrbitTranslate K S Γ t n).val : K) =
        (sUnitPartitionArchTranslate K S Γ t (scaledColumnArch K S n N hN)).val :=
    (scaledColumnArch_val K S _ N hN).symm.trans
      (congrArg Subtype.val (scaledColumnArch_translate K S Γ t n N hN))
  simp only [scaledColumnAnnularJointTerm, scaledColumnCompensatedJointFactor,
    originalJointFactor, sIntegerAnnularColumn, divisorColumn_translate_right,
    scaledColumnFinite_translate, hx, translatedJointTerm,
    sUnitAnnularPartitionJointCutoff, Complex.ofReal_mul]
  ring

theorem scaledColumnAnnularJointTerm_summable
    (a : ℝ → ℝ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (d m₁ m₂ : NZ) (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r})
    (N : ℝ) (hN : 0 < N) :
    Summable (fun p : Γ × Γ => scaledColumnAnnularJointTerm K S Γ a ψ d ν φ R N
      (sIntegerOrbitTranslate K S Γ p.1 m₁, sIntegerOrbitTranslate K S Γ p.2 m₂)) := by
  have h := translatedJointTerm_summable K S Γ a ν φ ψ
    (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₁)).2
    (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₂)).2 R
    (scaledColumnArch K S (divisorColumn K S d m₁) N hN)
    (scaledColumnArch K S (divisorColumn K S d m₂) N hN)
  exact h.congr (fun p => (scaledColumnAnnularJointTerm_eq_translated
    K S Γ a ψ d m₁ m₂ ν φ R N hN p.1 p.2).symm)

/-- Exact two-unit reconstruction at the original S-integer columns.
No smoothness, coprimality or independently supplied convergence is needed. -/
theorem scaledColumnAnnularJointTerm_two_column
    (a : ℝ → ℝ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (d m₁ m₂ : NZ) (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r})
    (N : ℝ) (hN : 0 < N) :
    (∑' u : Γ, ∑' v : Γ,
      scaledColumnAnnularJointTerm K S Γ a ψ d ν φ R N
        (sIntegerOrbitTranslate K S Γ u m₁, sIntegerOrbitTranslate K S Γ v m₂)) =
    scaledColumnCompensatedJointFactor K S ψ d ν φ R N (m₁, m₂) *
      ((a ((Ideal.absNorm (sIntegerModulusContraction K S (divisorColumn K S d m₁).val) : ℝ) / N) *
        a ((Ideal.absNorm (sIntegerModulusContraction K S (divisorColumn K S d m₂).val) : ℝ) / N) : ℝ) : ℂ) := by
  simp_rw [scaledColumnAnnularJointTerm_eq_translated K S Γ a ψ d m₁ m₂ ν φ R N hN]
  have h := translatedJointTerm_two_column K S Γ a ν φ ψ
    (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₁)).2
    (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₂)).2 R
    (scaledColumnArch K S (divisorColumn K S d m₁) N hN)
    (scaledColumnArch K S (divisorColumn K S d m₂) N hN)
  rw [scaledColumn_totalNorm_eq_idealNorm, scaledColumn_totalNorm_eq_idealNorm] at h
  simpa only [scaledColumnCompensatedJointFactor, originalJointFactor,
    scaledColumnArch_val] using h

end HeckeGeneral.Analysis.ActualScaledColumnUnitDraft
