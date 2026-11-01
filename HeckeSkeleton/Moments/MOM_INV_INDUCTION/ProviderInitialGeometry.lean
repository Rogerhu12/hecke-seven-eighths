import HeckeSkeleton.Moments.MOM_INV_STEP.ActualCenterGeometry
import HeckeSkeleton.Moments.MOM_INV_STEP.PartitionedChildGeometry
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondAdaptiveRows
import HeckeSkeleton.Moments.MOM_INV_STEP.SourceLengths

/-!
# Geometry and normalization of the actual initial inverse transform

The one-pass source has a fresh common ideal g, its actual divisor d,
and the independent full-Moebius overlap v. Its frozen puncture is g/d,
its averaged label is d*v, and its row is d*k. These are the actual
second-production objects, with the old label and old divisor equal to
one. The original column length is L=r+z for the marked inverse source.

The strict source margins L+Q+z<m and 2L+6z<3m yield the canonical
margins after the real dyadic center, clipping and 24-piece smooth
partition. The exact physical scalar contributes m-2L+P and the
frozen-ideal count contributes P; both raw child normalizations then
cancel to m. No energy assertion occurs in these geometric hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialGeometry

open NumberField IsDedekindDomain HeckePort.Moments
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open HeckeSkeleton.Moments.MOM_INV_STEP
open CanonicalNormPools ActualDivisorSectors SecondSourceColumns
open scoped Classical nonZeroDivisors

def rowLength (m L g theta h tau : ℝ) : ℝ :=
  2 * L - m - 2 * g + 2 * theta + 8 * h + tau

def labelLength (theta v h : ℝ) : ℝ := theta + v + 2 * h

def formalColumn (L g v : ℝ) : ℝ := L - g - v

/-- The actual single center has its full width-four error. -/
theorem center_log_bounds (Z L g v h Ng Nv c : ℝ)
    (hZ : 1 < Z) (hc : 0 < c) (hwidth : 2 ≤ Z ^ h)
    (hg : Z ^ (g - h) ≤ Ng ∧ Ng ≤ Z ^ (g + h))
    (hv : Z ^ (v - h) ≤ Nv ∧ Nv ≤ Z ^ (v + h))
    (hbin : c ≤ Ng * Nv ∧ Ng * Nv ≤ 4 * c) :
    formalColumn L g v - 2 * h ≤ Real.logb Z (Z ^ L / c) ∧
      Real.logb Z (Z ^ L / c) ≤ formalColumn L g v + 4 * h := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hb := ActualCenterGeometry.second_center_bounds Z g v h Ng Nv c
    hz hc hwidth hg hv hbin
  have hs := ActualCenterGeometry.scale_bounds Z (Z ^ L) c L L
    (g + v - 4 * h) (g + v + 2 * h) hz hc le_rfl le_rfl hb.1 hb.2
  have hh := ActualCenterGeometry.log_length_bounds Z (Z ^ L / c)
    (formalColumn L g v) (2 * h) (4 * h) hZ
    (div_pos (Real.rpow_pos_of_pos hz L) hc)
    (by convert hs.1 using 1 <;> unfold formalColumn <;> congr 1 <;> ring)
    (by convert hs.2 using 1 <;> unfold formalColumn <;> congr 1 <;> ring)
  exact hh

/-- The actual bin lower bound U>=1/4 controls numerical clipping. -/
theorem clipped_length_bounds (L g v h N : ℝ) (hh : 0 ≤ h)
    (hlo : formalColumn L g v - 2 * h ≤ N)
    (hhi : N ≤ formalColumn L g v + 4 * h) (hlive : -2 * h ≤ N) :
    formalColumn L g v - 2 * h ≤ max 0 N ∧
      max 0 N ≤ formalColumn L g v + 6 * h := by
  constructor
  · exact hlo.trans (le_max_right _ _)
  · apply max_le <;> linarith

/-- Every scale factor of the fixed smooth partition remains explicit. -/
theorem piece_length_bounds (Z L g v h N : ℝ) (hZ : 1 < Z)
    (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
    (hlo : formalColumn L g v - 2 * h ≤ N)
    (hhi : N ≤ formalColumn L g v + 4 * h) (hlive : -2 * h ≤ N)
    (a : SchwartzTestPartition.Index) :
    formalColumn L g v - 20 * h ≤
        PartitionedChildGeometry.pieceLength Z N a ∧
      PartitionedChildGeometry.pieceLength Z N a ≤ formalColumn L g v + 11 * h := by
  have hc := clipped_length_bounds L g v h N hh hlo hhi hlive
  have hs := PartitionedChildGeometry.piece_shift_bounds Z h hZ hwidth a
  unfold PartitionedChildGeometry.pieceLength
  constructor <;> linarith [hc.1, hc.2, hs.1, hs.2]

/-- The original source margins imply the actual child margins. The
same original mark budget z is safe for all surviving slot subsets. -/
theorem piece_margins (Z m L Q z c g theta v h tau N Qnew : ℝ)
    (hZ : 1 < Z) (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
    (hsource₁ : L + Q + z ≤ m - c)
    (hsource₂ : 2 * L + 6 * z ≤ 3 * m - c)
    (hgap : -2 * h ≤ g - theta)
    (hpuncture : Qnew ≤ Q + g - theta + 2 * h)
    (hlo : formalColumn L g v - 2 * h ≤ N)
    (hhi : N ≤ formalColumn L g v + 4 * h) (hlive : -2 * h ≤ N)
    (hloss : 100 * h + 3 * tau ≤ c / 4) (htau : 0 ≤ tau)
    (a : SchwartzTestPartition.Index) :
    CanonicalMargins
      (PartitionedChildGeometry.pieceLength Z N a + labelLength theta v h)
      (rowLength m L g theta h tau) Qnew z (3 * c / 4) := by
  have hp := piece_length_bounds Z L g v h N hZ hh hwidth hlo hhi hlive a
  unfold CanonicalMargins rowLength labelLength formalColumn at *
  constructor <;> linarith [hp.1]

/-- A negative actual partition scale uses the proved unit-column
estimate; its row mass is bounded by the label mass with the exact
allowance required by `CanonicalChildClosure`. -/
theorem small_piece_row (Z m L Q z c g theta v h tau N Qnew : ℝ)
    (hZ : 1 < Z) (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
    (hsource : L + Q + z ≤ m - c) (hQ : 0 ≤ Qnew) (hz : 0 ≤ z)
    (hpuncture : Qnew ≤ Q + g - theta + 2 * h)
    (hlo : formalColumn L g v - 2 * h ≤ N)
    (hhi : N ≤ formalColumn L g v + 4 * h) (hlive : -2 * h ≤ N)
    (htau : tau ≤ c) (a : SchwartzTestPartition.Index)
    (hsmall : PartitionedChildGeometry.pieceLength Z N a < 0) :
    rowLength m L g theta h tau ≤ labelLength theta v h + 28 * h := by
  have hp := (piece_length_bounds Z L g v h N hZ hh hwidth hlo hhi hlive a).1
  unfold rowLength labelLength formalColumn at *
  linarith

/-- Uniform capacities use only the original source length and margin. -/
theorem initial_capacities (Z m L Q z c g theta v h tau N : ℝ)
    (hZ : 1 < Z) (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
    (hsource : L + Q + z ≤ m - c) (hQ : 0 ≤ Q) (hz : 0 ≤ z)
    (hgap : -2 * h ≤ g - theta)
    (hlo : formalColumn L g v - 2 * h ≤ N)
    (hhi : N ≤ formalColumn L g v + 4 * h) (hlive : -2 * h ≤ N)
    (hloss : 15 * h + tau ≤ c) (htau : 0 ≤ tau)
    (a : SchwartzTestPartition.Index) :
    PartitionedChildGeometry.pieceLength Z N a + labelLength theta v h ≤ m ∧
      rowLength m L g theta h tau ≤ m := by
  have hp := (piece_length_bounds Z L g v h N hZ hh hwidth hlo hhi hlive a).2
  unfold rowLength labelLength formalColumn at *
  constructor <;> linarith

/-- The scalar from actual Poisson, the distinct frozen residual count,
and both raw child normalizations cancel exactly. -/
theorem initial_exponent_identity (m L P : ℝ) :
    (m - 2 * L + P) + P + 2 * (L - P) = m := by ring

theorem physical_power_identity (Z m L R A : ℝ) (hZ : 0 < Z) :
    A * Z ^ m * Z ^ R / (Z ^ L) ^ 2 = A * Z ^ (m - 2 * L + R) := by
  have htwo : Z ^ (2 * L) = (Z ^ L) ^ 2 := by
    rw [mul_comm, Real.rpow_mul hZ.le, Real.rpow_two]
  rw [Real.rpow_add hZ, Real.rpow_sub hZ, htwo]
  ring

/-- Closure uses the original clipped family, so its 28h unit-column
allowance is paid together with both actual norm-window errors. -/
theorem closed_exponent_budget (m L g theta v h N pi eps : ℝ)
    (hh : 0 ≤ h) (hhi : N ≤ formalColumn L g v + 4 * h)
    (hlive : -2 * h ≤ N) :
    (m - 2 * L + (g - theta) + 2 * h) + (g - theta + 2 * h) +
      2 * (max 0 N + labelLength theta v h) + 28 * h + pi + eps ≤
        m + 48 * h + pi + eps := by
  have hb : max 0 N ≤ formalColumn L g v + 6 * h := by
    apply max_le <;> linarith
  unfold formalColumn labelLength at *
  linarith

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "OS" => Set.integer Sset K

/-- The actual returned row d*k has the displayed initial row length;
its frequency bound is the existing common/divisor-local cutoff. -/
theorem actual_row_bound (rho : {r : ℝ // 0 < r})
    (Z m L g theta h tau : ℝ) (hZ : 1 < Z) (hwidth : 2 ≤ Z ^ h)
    (G k : Ext) (d : NonzeroRingElements OS) (delta : Finset (HeightOneSpectrum OS))
    (hrho : rho.val ≤ Z ^ (-m))
    (hunit : (sIntegerElementNorm K Sset d).val = 1)
    (hg : Z ^ (g - h) ≤ height K Sset G)
    (hd : (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset delta)).val ≤
      Z ^ (theta + h))
    (hk : height K Sset k ≤
      SecondAdaptiveCutoff.fineCutoff K S rho (Z ^ L) Z tau G delta) :
    height K Sset (newRowIdeal K S k d (sIntegerMaskGenerator K Sset delta)) ≤
      Z ^ rowLength m L g theta h tau := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have h16 : (16 : ℝ) ≤ Z ^ (4 * h) := by
    have h4 := ActualCenterGeometry.four_le_rpow_two Z h hz hwidth
    calc
      (16 : ℝ) = 4 * 4 := by norm_num
      _ ≤ Z ^ (2 * h) * Z ^ (2 * h) :=
        mul_le_mul h4 h4 (by norm_num) (Real.rpow_nonneg hz.le _)
      _ = Z ^ (4 * h) := by rw [← Real.rpow_add hz]; congr 1; ring
  have hb := SecondAdaptiveRows.newRow_fine_rpow_bound K S rho (Z ^ L) Z tau
    (4 * h) (-m) L (g - h) 0 (theta + h)
    (Real.rpow_pos_of_pos hz L) hz G k d delta h16 hrho le_rfl hg
    (by rw [hunit, Real.rpow_zero]) hd hk
  convert hb using 1 <;> unfold rowLength <;> congr 1 <;> ring

/-- Exact normalized physical scalar, before any norm window or count. -/
theorem normalized_scalar (H X d g : ℝ) (hH : 0 < H) (hX : 0 < X)
    (hd : 0 < d) (hg : 0 < g) (A : ℝ) :
    X⁻¹ * ((A / (H⁻¹ * d)) / (X / g)) = A * H * (g / d) / X ^ 2 := by
  field_simp [hH.ne', hX.ne', hd.ne', hg.ne']
  <;> ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialGeometry

end
