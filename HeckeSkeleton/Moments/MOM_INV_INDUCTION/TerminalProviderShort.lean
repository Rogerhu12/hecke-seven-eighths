import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProvider
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderTheta
import HeckeSkeleton.LowEnergy.IdealMass

/-!
# The genuine short cube sum in the row Hilbert space

The selected cubes form the complete original norm range. Their signed
coefficient still contains the row and label phases and every puncture
zero.  Its row-independent majorant is 1/N(H), whose finite mass has an
arbitrary small-power bound proved from ideal counting.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOM_BASE
open HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalNormPools
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

def shortCubes (T : ℝ) : Finset (ExteriorIdeal K S) :=
  (boundedPool K S T).filter (fun H => exteriorNorm K S H < T)

theorem mem_shortCubes (T : ℝ) (H : ExteriorIdeal K S) :
    H ∈ shortCubes K S T ↔ exteriorNorm K S H < T := by
  simp only [shortCubes, boundedPool, Finset.mem_filter, Finset.mem_preimage,
    DedekindZetaZeroFree.LargeSieve.mem_boundedNormIdeals]
  constructor
  · exact And.right
  · intro h
    have hN : 0 < exteriorNorm K S H := idealNorm_pos K H.val
    exact ⟨by change exteriorNorm K S H ≤ 2 * T; linarith, h⟩

def shortCompletedColumn (θ : HeckeCharacter K) (k : S.integer K)
    (f r : ExteriorIdeal K S) (mark : Ideal (𝓞 K) → ℂ)
    (W : ℝ → ℂ) (X T : ℝ) : ℂ :=
  ∑ H ∈ shortCubes K S T,
    ((moebius H.val.val : ℂ) *
      canonicalTau K S D θ (k * D.generator f ^ 4) r.val.val H.val.val ^ 3 /
      (exteriorNorm K S H : ℂ)) *
    weightedCompletedTheta K S D θ (k * D.generator f ^ 4) r ∅
      (fun A => mark (H.val.val ^ 3 * A)) (canonicalVstar W)
      (X / exteriorNorm K S H ^ 3)

/-- The finite original short range equals its restricted exterior
series without a summability convention or a support hypothesis. -/
theorem shortCompletedColumn_eq_tsum (θ : HeckeCharacter K) (k : S.integer K)
    (f r : ExteriorIdeal K S) (mark : Ideal (𝓞 K) → ℂ)
    (W : ℝ → ℂ) (X T : ℝ) :
    shortCompletedColumn K S D θ k f r mark W X T =
      ∑' H : ExteriorIdeal K S, if exteriorNorm K S H < T then
        ((moebius H.val.val : ℂ) *
          canonicalTau K S D θ (k * D.generator f ^ 4) r.val.val H.val.val ^ 3 /
          (exteriorNorm K S H : ℂ)) *
        weightedCompletedTheta K S D θ (k * D.generator f ^ 4) r ∅
          (fun A => mark (H.val.val ^ 3 * A)) (canonicalVstar W)
          (X / exteriorNorm K S H ^ 3)
      else 0 := by
  symm
  rw [tsum_eq_sum (shortCubes K S T)]
  · apply Finset.sum_congr rfl
    intro H hH
    rw [if_pos ((mem_shortCubes K S T H).mp hH)]
  · intro H hH
    exact if_neg (fun h => hH ((mem_shortCubes K S T H).mpr h))

/-- A single constant works for every short-cube cutoff and its entire
exterior ideal range. -/
theorem shortCubes_mass_small_power (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      (∑ H ∈ shortCubes K S T, 1 / exteriorNorm K S H) ≤ C * T ^ eps := by
  obtain ⟨C, hC, hb⟩ := HeckeSkeleton.LowEnergy.ideal_harmonic_small_power_pullback K eps heps
  refine ⟨C, hC, ?_⟩
  intro T hT
  exact hb (fun H : ExteriorIdeal K S => H.val.val)
    (fun _ _ h => Subtype.ext (Subtype.ext h)) T hT (shortCubes K S T)
    (fun H _ => nonZeroDivisors.coe_ne_zero H.val)
    (fun H hH => ((mem_shortCubes K S T H).mp hH).le)

/-- The positive block energy bound is used only after the literal
row-dependent cube phases are bounded by their independent majorants. -/
theorem shortCompletedColumn_energy {κ : Type*}
    (θ : HeckeCharacter K) (rows : Finset κ) (row : κ → S.integer K)
    (f r : ExteriorIdeal K S) (mark : Ideal (𝓞 K) → ℂ)
    (W : ℝ → ℂ) (X T B mass : ℝ)
    (hB : 0 ≤ B)
    (hmass : (∑ H ∈ shortCubes K S T, 1 / exteriorNorm K S H) ≤ mass)
    (hcompleted : ∀ H ∈ shortCubes K S T,
      (∑ k ∈ rows, ‖weightedCompletedTheta K S D θ
        (row k * D.generator f ^ 4) r ∅
        (fun A => mark (H.val.val ^ 3 * A)) (canonicalVstar W)
        (X / exteriorNorm K S H ^ 3)‖ ^ 2) ≤ B) :
    (∑ k ∈ rows, ‖shortCompletedColumn K S D θ (row k) f r mark W X T‖ ^ 2) ≤
      mass ^ 2 * B := by
  apply finite_reconstruction_energy_bounded (shortCubes K S T) rows
    (fun H k => (moebius H.val.val : ℂ) *
      canonicalTau K S D θ (row k * D.generator f ^ 4) r.val.val H.val.val ^ 3 /
      (exteriorNorm K S H : ℂ))
    (fun H => 1 / exteriorNorm K S H)
    (fun H k => weightedCompletedTheta K S D θ
      (row k * D.generator f ^ 4) r ∅
      (fun A => mark (H.val.val ^ 3 * A)) (canonicalVstar W)
      (X / exteriorNorm K S H ^ 3))
    (fun k => shortCompletedColumn K S D θ (row k) f r mark W X T) hB
  · intro H _
    exact (one_div_pos.mpr (idealNorm_pos K H.val)).le
  · intro H hH k hk
    exact completeCanonicalColumn_cube_coefficient_norm_le K S D θ (row k) f r H
  · intro k hk
    rfl
  · exact hmass
  · exact hcompleted

end HeckeSkeleton.Moments.MOM_INV_INDUCTION

end
