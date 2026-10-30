import HeckeSkeleton.LowEnergy.ActualResidualDyadicEnergy
import HeckeSkeleton.LowEnergy.PowerfulRowAssembly
import HeckeSkeleton.LowEnergy.LogGeometry

/-!
# Uniform energy for the actual complete ideal rows

The powerful part and the residual norm shell partition the original row
energy.  Their outer sum uses the proved powerful-ideal half-norm mass.
The residual shell count contributes one logarithmic factor, absorbed
together with the arbitrarily small local-state power.  Finally the actual
selected-prime norm restores the literal inverse-square denominator.

All constants and the lower threshold are chosen before the window scale,
the selected tuple, its subset, the unit sector, and the finite row set.
The only analytic inputs are coefficient reflection and the two original
exterior sieve estimates.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowEnergy.ActualCompleteIdealEnergy

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.CenteredMomentGenerator
open HeckeSkeleton.LowEnergy.ActualRows HeckeSkeleton.LowEnergy.ActualReflection
open HeckeSkeleton.LowEnergy.ActualSymbols HeckeSkeleton.LowEnergy.ActualSieveDictionary
open HeckeSkeleton.LowEnergy.ActualResidualDyadicEnergy
open HeckeSkeleton.LowEnergy.ActualAnnularBlockEnergy
open HeckeSkeleton.LowEnergy.WindowTuples
open HeckeSkeleton.LowEnergy.IdealRows HeckeSkeleton.LowEnergy.IdealRankin
open scoped Classical BigOperators NumberField nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The dyad is attached to the residual part of the complete ideal. -/
theorem exteriorNorm_residualPart_le (I : ExteriorIdeal K S) :
    exteriorNorm K S (exteriorResidualPart K S I) ≤ exteriorNorm K S I := by
  have hd : (residualPart I.val).val.absNorm ∣ I.val.val.absNorm :=
    map_dvd Ideal.absNorm (residualPart_dvd I.val)
  change ((residualPart I.val).val.absNorm : ℝ) ≤ (I.val.val.absNorm : ℝ)
  exact_mod_cast Nat.le_of_dvd (Ideal.absNorm_pos_of_nonZeroDivisors I.val) hd

/-- A uniform coarse ambient length suffices for the powerful-ideal budget.
The selected norm is retained in the local block estimate. -/
theorem physical_cutoff_le_square {Z B q : ℝ}
    (hZ : 1 ≤ Z) (hB : 0 ≤ B) (hBZ : B ≤ Z) (hq : 1 ≤ q) :
    B * Z ^ (5 / 6 : ℝ) / q ^ 2 ≤ Z ^ (2 : ℝ) := by
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
  have hp : Z ^ (5 / 6 : ℝ) ≤ Z := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hZ (show (5 / 6 : ℝ) ≤ 1 by norm_num)
  calc
    _ ≤ B * Z ^ (5 / 6 : ℝ) :=
      div_le_self (mul_nonneg hB (Real.rpow_nonneg hZ0 _)) (one_le_pow₀ hq)
    _ ≤ Z * Z := mul_le_mul hBZ hp (Real.rpow_nonneg hZ0 _) hZ0
    _ = Z ^ (2 : ℝ) := by rw [Real.rpow_two]; ring

/-- The residual shell cost is logarithmic, with a fixed universal constant. -/
theorem shellCount_square_le (Z : ℝ) (hZ : 1 ≤ Z) :
    (DyadicReindex.shellCount (Z ^ (2 : ℝ)) : ℝ) ≤
      (1 + 2 / Real.log 2) * (1 + Real.log Z) ^ 2 := by
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hlog : 0 ≤ Real.log Z := Real.log_nonneg hZ
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht : 0 ≤ 2 / Real.log 2 := (div_pos (by norm_num) htwo).le
  have h1 : 1 + Real.log Z ≤ (1 + Real.log Z) ^ 2 := by nlinarith
  calc
    _ ≤ Real.log (Z ^ (2 : ℝ)) / Real.log 2 + 1 :=
      DyadicReindex.shellCount_le_log (Real.one_le_rpow hZ (by norm_num))
    _ = (2 / Real.log 2) * Real.log Z + 1 := by rw [Real.log_rpow hZpos]; ring
    _ ≤ (1 + 2 / Real.log 2) * (1 + Real.log Z) := by nlinarith
    _ ≤ (1 + 2 / Real.log 2) * (1 + Real.log Z) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by linarith)

section Target

variable (c : HeckeSkeleton.TargetContext K)
local notation "Sc" => HeckeSkeleton.places K c
local notation "Pc" => HeckeSkeleton.probeData K c
local notation "ψc" => HeckeSkeleton.targetCharacter K c
local notation "θc" => thetaPeriod K Sc Pc ψc
local notation "gc" => c.geometry
local notation "Tc" => HeckeSkeleton.rayFilter K c

/-- The complete-ideal estimate for the literal marked row in the repository.
It has no reflected-block energy premise and no auxiliary counting premise. -/
theorem actual_finite_complete_ideal_energy [Finite (SixthLocalClasses K Sc)]
    (F : FiniteMellinData K Sc)
    (hreflection : MarkedCoefficientReflectionInput K Sc Pc.arithmetic F θc)
    (hquadratic : ExteriorQuadraticBound K Sc Pc.arithmetic)
    (hcubic : ExteriorCubicBound K Sc Pc.arithmetic)
    (B eps : ℝ) (hB : 0 < B) (heps : 0 < eps) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧
      ∀ Z : ℝ, Z0 ≤ Z →
      ∀ p ∈ Fintype.piFinset (fun i => primeWindow K Sc gc Tc Z i),
      ∀ (J : Finset (Fin gc.slots)) (ξ : SixthUnitClasses K Sc)
        (R : Finset (ExteriorIdeal K Sc)),
      (∀ I ∈ R, exteriorNorm K Sc I ≤
        B * Z ^ (5 / 6 : ℝ) / exteriorNorm K Sc (subsetPrimeIdeal K Sc p J) ^ 2) →
      (∑ I ∈ R, ‖HeckeSkeleton.LowCauchy.completedMarkedRow K c Z p J
        (idealSectorElement K Sc Pc.arithmetic (I, ξ))‖ ^ 2) ≤
        C * Z ^ ((5 / 6 : ℝ) + eps) /
          exteriorNorm K Sc (subsetPrimeIdeal K Sc p J) ^ 2 := by
  let delta : ℝ := min 1 (eps / 100)
  let epsInner : ℝ := eps / 100
  let epsOuter : ℝ := eps / 2
  let rho : ℝ := epsOuter / (4 * ((2 : ℝ) + 1))
  let Clog : ℝ := 1 + 2 / Real.log 2
  let C0 : ℝ := max 0 (max (Real.log B) (Real.log ((2 : ℝ) ^ gc.slots)))
  let D : ℝ := (2 : ℝ) ^ gc.slots
  have hdelta : 0 < delta := lt_min (by norm_num) (by positivity)
  have hdelta' : delta ≤ 1 := min_le_left _ _
  have hdeltaEps : delta ≤ eps / 100 := min_le_right _ _
  have hepsInner : 0 < epsInner := by dsimp [epsInner]; positivity
  have hepsOuter : 0 < epsOuter := by dsimp [epsOuter]; positivity
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hClog : 0 < Clog := by
    have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [Clog]
    positivity
  have hC0 : 0 ≤ C0 := le_max_left _ _
  have hlogB : Real.log B ≤ C0 :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hlogWin : Real.log ((2 : ℝ) ^ gc.slots) ≤ C0 :=
    (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨Cb, hCb, hblock⟩ :=
    completedMarkedRow_residual_shell_energy K c F hreflection hquadratic hcubic
      delta epsInner C0 rho hdelta hdelta' hepsInner hC0 hrho
  obtain ⟨Cp, hCp, hpowerful⟩ :=
    PowerfulRowAssembly.powerful_shell_aggregation_at_scale K 2 epsOuter Clog
      (by norm_num) hepsOuter hClog
  refine ⟨(Cp * Cb) * D ^ 2, max 2 B, by dsimp [D]; positivity, ?_, ?_⟩
  · exact (show (1 : ℝ) ≤ 2 by norm_num).trans (le_max_left _ _)
  intro Z hthreshold p hp J ξ R hcut
  have hZ2 : 2 ≤ Z := (le_max_left _ _).trans hthreshold
  have hZ : 1 < Z := lt_of_lt_of_le (by norm_num) hZ2
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hBZ : B ≤ Z := (le_max_right _ _).trans hthreshold
  let q : ℝ := exteriorNorm K Sc (subsetPrimeIdeal K Sc p J)
  let d : ℝ := (J.card : ℝ) / (6 * gc.slots)
  let a : ℝ := (5 / 6 : ℝ) - 2 * d + 23 * delta + 2 * epsInner
  let N : ℕ := DyadicReindex.shellCount (Z ^ (2 : ℝ))
  let E : ExteriorIdeal K Sc → ℝ := fun I =>
    ‖HeckeSkeleton.LowCauchy.completedMarkedRow K c Z p J
      (idealSectorElement K Sc Pc.arithmetic (I, ξ))‖ ^ 2
  have hq : 0 < q := exteriorNorm_pos K Sc _
  have hq1 : 1 ≤ q := exteriorNorm_one_le K Sc _
  have hambient : ∀ I ∈ R, idealNorm K I.val ≤ Z ^ (2 : ℝ) := by
    intro I hI
    exact (hcut I hI).trans (physical_cutoff_le_square hZ.le hB.le hBZ hq1)
  have hshell : ∀ I ∈ R, residualIndex K Sc I < N := by
    intro I hI
    exact DyadicReindex.index_lt_shellCount
      (fun k : ExteriorIdeal K Sc => k.val.val.absNorm) (Z ^ (2 : ℝ))
      ((exteriorNorm_residualPart_le K Sc I).trans (hambient I hI))
  have hN : (N : ℝ) ≤ Clog * (1 + Real.log Z) ^ 2 := shellCount_square_le Z hZ.le
  have hlocal : ∀ A ∈ R.image (fun I => powerfulPart I.val),
      ∀ j ∈ Finset.range N,
      (∑ I ∈ R.filter (fun I => powerfulPart I.val = A ∧ residualIndex K Sc I = j),
        E I) ≤ (Cb * Z ^ a) * idealNorm K A ^ (-(1 / 2 : ℝ) + rho) := by
    intro A hA j hj
    obtain ⟨I0, hI0, rfl⟩ := Finset.mem_image.mp hA
    have hfilter :
        R.filter (fun I => powerfulPart I.val = powerfulPart I0.val ∧
          residualIndex K Sc I = j) =
          fibreShell K Sc R (exteriorPowerfulPart K Sc I0) j := by
      unfold fibreShell
      apply Finset.filter_congr
      intro I hI
      constructor
      · rintro ⟨h, hr⟩
        exact ⟨Subtype.ext h, hr⟩
      · rintro ⟨h, hr⟩
        exact ⟨congrArg Subtype.val h, hr⟩
    rw [hfilter]
    have hb := hblock Z B hZ hB hlogB hlogWin p hp J ξ R
      (exteriorPowerfulPart K Sc I0) j hcut
    simpa only [E, a, d, exteriorPowerfulPart, exteriorNorm, idealNorm,
      mul_assoc, mul_left_comm, mul_comm] using hb
  have hag := hpowerful R (fun I => I.val) (residualIndex K Sc) E N Z
    (Cb * Z ^ a) hZ.le (by positivity) hambient hshell hN hlocal
  have hexp : a + epsOuter ≤ (5 / 6 : ℝ) - 2 * d + eps := by
    dsimp [a, epsOuter, epsInner]
    linarith
  have henergy : (∑ I ∈ R, E I) ≤
      (Cp * Cb) * Z ^ ((5 / 6 : ℝ) - 2 * d + eps) := by
    calc
      _ ≤ Cp * (Cb * Z ^ a) * Z ^ epsOuter := hag
      _ = (Cp * Cb) * Z ^ (a + epsOuter) := by
        rw [Real.rpow_add hZpos]
        ring
      _ ≤ (Cp * Cb) * Z ^ ((5 / 6 : ℝ) - 2 * d + eps) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hZ.le hexp) (mul_nonneg hCp.le hCb.le)
  have hselected : q ≤ D * Z ^ d :=
    (selected_norm_bounds K Sc gc Tc hZpos p hp J).2
  exact LogGeometry.restore_selected_norm hZpos hq (by dsimp [D]; positivity)
    (mul_nonneg hCp.le hCb.le) hselected henergy

end Target

#print axioms exteriorNorm_residualPart_le
#print axioms physical_cutoff_le_square
#print axioms shellCount_square_le
#print axioms actual_finite_complete_ideal_energy

end HeckeSkeleton.LowEnergy.ActualCompleteIdealEnergy
