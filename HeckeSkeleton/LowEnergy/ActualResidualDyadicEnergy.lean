import HeckeSkeleton.LowEnergy.ActualTupleReconstruction
import HeckeSkeleton.LowEnergy.ActualRowFibres

/-!
# Literal target energy on one powerful fibre and one residual dyad

The moving row is the residual part of the original complete ideal.  On a
fixed powerful fibre this map is injective, so passing to ordinary ideal
rows preserves the energy exactly.  Empty shells cost zero, and every
nonempty shell inherits its lower-endpoint cutoff from an actual row.
The estimate invokes the derived marked-tuple bound and the literal
coefficient-reflection identity, without an additional energy hypothesis.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.ActualResidualDyadicEnergy

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.CenteredMomentGenerator
open HeckeSkeleton.LowEnergy.ActualRows HeckeSkeleton.LowEnergy.ActualReflection
open HeckeSkeleton.LowEnergy.ActualSymbols HeckeSkeleton.LowEnergy.ActualSieveDictionary
open HeckeSkeleton.LowEnergy.ActualSeparatedBlock HeckeSkeleton.LowEnergy.ActualBlockReindex
open HeckeSkeleton.LowEnergy.ActualMarkedTupleEnergy
open HeckeSkeleton.LowEnergy.ActualTupleReconstruction
open HeckeSkeleton.LowEnergy.ActualRowFibres
open HeckeSkeleton.LowEnergy.WindowTuples
open scoped Classical BigOperators NumberField nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def residualIndex (I : ExteriorIdeal K S) : ℕ :=
  DyadicReindex.index (fun k : ExteriorIdeal K S => k.val.val.absNorm)
    (exteriorResidualPart K S I)

def fibreShell (R : Finset (ExteriorIdeal K S)) (frozen : ExteriorIdeal K S)
    (j : ℕ) : Finset (ExteriorIdeal K S) :=
  R.filter (fun I => exteriorPowerfulPart K S I = frozen ∧ residualIndex K S I = j)

def ordinaryResiduals (R : Finset (ExteriorIdeal K S)) : Finset (Ideal (𝓞 K)) :=
  R.image (fun I => (exteriorResidualPart K S I).val.val)

theorem residualIndex_bounds (I : ExteriorIdeal K S) :
    (2 : ℝ) ^ residualIndex K S I ≤ exteriorNorm K S (exteriorResidualPart K S I) ∧
      exteriorNorm K S (exteriorResidualPart K S I) <
        2 * (2 : ℝ) ^ residualIndex K S I := by
  have hn : 0 < (exteriorResidualPart K S I).val.val.absNorm :=
    Ideal.absNorm_pos_of_nonZeroDivisors (exteriorResidualPart K S I).val
  simpa only [residualIndex, exteriorNorm, pow_succ, mul_comm] using
    DyadicReindex.index_bounds_real
      (fun k : ExteriorIdeal K S => k.val.val.absNorm) hn

/-- This identity is an injective reindexing of the original row energy. -/
theorem ordinaryResiduals_sum {M : Type*} [AddCommMonoid M]
    (R : Finset (ExteriorIdeal K S)) (frozen : ExteriorIdeal K S)
    (hf : ∀ I ∈ R, exteriorPowerfulPart K S I = frozen)
    (E : Ideal (𝓞 K) → M) :
    (∑ I ∈ R, E (exteriorResidualPart K S I).val.val) =
      ∑ k ∈ ordinaryResiduals K S R, E k := by
  rw [ordinaryResiduals, Finset.sum_image]
  intro I hI I' hI' heq
  apply residual_injective_on_fibre K S frozen (hf I hI) (hf I' hI')
  apply Subtype.ext
  exact Subtype.ext heq

variable (D : ThetaArithmeticData K S)

/-- The constant is independent of the original row set, its powerful
part, its residual dyad, and every physical prime tuple. -/
theorem actual_residual_shell_energy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (g : PrimeWindowGeometry) (delta eps C0 rho : ℝ)
    (hdelta : 0 < delta) (hdelta' : delta ≤ 1) (heps : 0 < eps)
    (hC0 : 0 ≤ C0) (hrho : 0 < rho) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ψ : HeckeCharacter K) (T : Finset (HeckeCharacter K))
      (frozen : ExteriorIdeal K S) (u : S.unit K) (Z q Ccut : ℝ),
      1 < Z → 0 < q → 0 < Ccut → Real.log Ccut ≤ C0 →
      Real.log ((2 : ℝ) ^ g.slots) ≤ C0 →
      ∀ J : Finset (Fin g.slots),
      Z ^ ((J.card : ℝ) / (6 * g.slots)) ≤ q →
      ∀ (R : Finset (ExteriorIdeal K S)) (j : ℕ),
      (∀ I ∈ R, exteriorPowerfulPart K S I = frozen) →
      (∀ I ∈ R, residualIndex K S I = j) →
      (∀ I ∈ R, exteriorNorm K S I ≤ Ccut * Z ^ (5 / 6 : ℝ) / q ^ 2) →
      (∑ I ∈ R, ‖markedFrozenRow K S D frozen u F θ ψ g T Z J
        (exteriorResidualPart K S I).val.val‖ ^ 2) ≤
        C * exteriorNorm K S frozen ^ (-(1 / 2 : ℝ) + rho) *
          Z ^ ((5 / 6 : ℝ) - 2 * ((J.card : ℝ) / (6 * g.slots)) +
            23 * delta + 2 * eps) := by
  obtain ⟨C, hC, hbound⟩ := actual_marked_tuple_energy K S D F hF θ hKernel hθ hD
    hquadratic hcubic g delta eps C0 rho hdelta hdelta' heps hC0 hrho
  refine ⟨C, hC, ?_⟩
  intro ψ T frozen u Z q Ccut hZ hq hCut hlogCut hlogWin J hselected R j hf hj hcut
  by_cases hR : R.Nonempty
  · obtain ⟨I0, hI0⟩ := hR
    have hpowerful : IdealRows.Powerful frozen.val := by
      have h := IdealRows.powerfulPart_powerful I0.val
      change IdealRows.Powerful (exteriorPowerfulPart K S I0).val at h
      simpa only [hf I0 hI0] using h
    have hrow : exteriorNorm K S frozen * (2 : ℝ) ^ j ≤
        Ccut * Z ^ (5 / 6 : ℝ) / q ^ 2 := by
      have h := (residualIndex_bounds K S I0).1
      rw [hj I0 hI0] at h
      have hn : exteriorNorm K S I0 = exteriorNorm K S frozen *
          exteriorNorm K S (exteriorResidualPart K S I0) := by
        have hnorm := IdealRows.norm_powerful_residual_decomposition I0.val
        change exteriorNorm K S I0 = exteriorNorm K S (exteriorPowerfulPart K S I0) *
          exteriorNorm K S (exteriorResidualPart K S I0) at hnorm
        simpa only [hf I0 hI0] using hnorm
      exact (mul_le_mul_of_nonneg_left h (exteriorNorm_pos K S frozen).le).trans
        (hn ▸ hcut I0 hI0)
    have hs : ∀ k ∈ ordinaryResiduals K S R,
        IsExterior K S k ∧ Squarefree k ∧ (k.absNorm : ℝ) ≤ 2 * (2 : ℝ) ^ j := by
      intro k hk
      obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hk
      have hi := (residualIndex_bounds K S I).2.le
      rw [hj I hI] at hi
      exact ⟨exterior_isExterior K S _, IdealRows.residualPart_squarefree I.val, hi⟩
    have hr : ∀ k ∈ ordinaryResiduals K S R,
        1 ≤ safeNorm k / (2 : ℝ) ^ j ∧ safeNorm k / (2 : ℝ) ^ j ≤ 2 := by
      intro k hk
      obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hk
      rw [safeNorm_exterior K S (exteriorResidualPart K S I)]
      have hi := residualIndex_bounds K S I
      rw [hj I hI] at hi
      exact ⟨(le_div_iff₀ (by positivity)).mpr (by simpa only [one_mul] using hi.1),
        (div_le_iff₀ (by positivity)).mpr hi.2.le⟩
    rw [ordinaryResiduals_sum K S R frozen hf]
    exact hbound ψ T frozen u Z ((2 : ℝ) ^ j) q Ccut hZ
      (one_le_pow₀ (by norm_num)) hq hCut hpowerful hlogCut hlogWin J hselected
      hrow (ordinaryResiduals K S R) hs hr
  · have hR0 : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
    simp only [hR0, Finset.sum_empty]
    exact mul_nonneg
      (mul_nonneg hC.le (Real.rpow_nonneg (exteriorNorm_pos K S frozen).le _))
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)

section Target

variable (c : HeckeSkeleton.TargetContext K)
local notation "Sc" => HeckeSkeleton.places K c
local notation "Pc" => HeckeSkeleton.probeData K c
local notation "ψc" => HeckeSkeleton.targetCharacter K c
local notation "θc" => thetaPeriod K Sc Pc ψc
local notation "gc" => c.geometry
local notation "Tc" => HeckeSkeleton.rayFilter K c

/-- The local premise used by the actual powerful-ideal aggregation.  It
is the literal repository target row, with its original complete-ideal
cutoff and its original residual ideal in both hybrid masks. -/
theorem completedMarkedRow_residual_shell_energy [Finite (SixthLocalClasses K Sc)]
    (F : FiniteMellinData K Sc)
    (hreflection : MarkedCoefficientReflectionInput K Sc Pc.arithmetic F θc)
    (hquadratic : ExteriorQuadraticBound K Sc Pc.arithmetic)
    (hcubic : ExteriorCubicBound K Sc Pc.arithmetic)
    (delta eps C0 rho : ℝ)
    (hdelta : 0 < delta) (hdelta' : delta ≤ 1) (heps : 0 < eps)
    (hC0 : 0 ≤ C0) (hrho : 0 < rho) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z Ccut : ℝ),
      1 < Z → 0 < Ccut → Real.log Ccut ≤ C0 →
      Real.log ((2 : ℝ) ^ gc.slots) ≤ C0 →
      ∀ p ∈ Fintype.piFinset (fun i => primeWindow K Sc gc Tc Z i),
      ∀ (J : Finset (Fin gc.slots)) (ξ : SixthUnitClasses K Sc)
        (R : Finset (ExteriorIdeal K Sc)) (frozen : ExteriorIdeal K Sc) (j : ℕ),
      (∀ I ∈ R, exteriorNorm K Sc I ≤
        Ccut * Z ^ (5 / 6 : ℝ) / exteriorNorm K Sc (subsetPrimeIdeal K Sc p J) ^ 2) →
      (∑ I ∈ fibreShell K Sc R frozen j,
        ‖HeckeSkeleton.LowCauchy.completedMarkedRow K c Z p J
          (idealSectorElement K Sc Pc.arithmetic (I, ξ))‖ ^ 2) ≤
        C * exteriorNorm K Sc frozen ^ (-(1 / 2 : ℝ) + rho) *
          Z ^ ((5 / 6 : ℝ) - 2 * ((J.card : ℝ) / (6 * gc.slots)) +
            23 * delta + 2 * eps) := by
  obtain ⟨C, hC, hbound⟩ := actual_residual_shell_energy K Sc Pc.arithmetic F
    hreflection.kernel.finite_admissible θc hreflection.kernel hreflection.exterior_unramified
    hreflection.allowed_generators hquadratic hcubic gc delta eps C0 rho
    hdelta hdelta' heps hC0 hrho
  refine ⟨C, hC, ?_⟩
  intro Z Ccut hZ hCut hlogCut hlogWin p hp J ξ R frozen j hcut
  have hf : ∀ I ∈ fibreShell K Sc R frozen j, exteriorPowerfulPart K Sc I = frozen :=
    fun I hI => (Finset.mem_filter.mp hI).2.1
  have hj : ∀ I ∈ fibreShell K Sc R frozen j, residualIndex K Sc I = j :=
    fun I hI => (Finset.mem_filter.mp hI).2.2
  have hsub : ∀ I ∈ fibreShell K Sc R frozen j, I ∈ R :=
    fun I hI => (Finset.mem_filter.mp hI).1
  have heq : (∑ I ∈ fibreShell K Sc R frozen j,
      ‖HeckeSkeleton.LowCauchy.completedMarkedRow K c Z p J
        (idealSectorElement K Sc Pc.arithmetic (I, ξ))‖ ^ 2) =
      ∑ I ∈ fibreShell K Sc R frozen j,
        ‖markedFrozenRow K Sc Pc.arithmetic frozen (Quotient.out ξ) F θc ψc gc Tc Z J
          (exteriorResidualPart K Sc I).val.val‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro I hI
    rw [completedMarkedRow_reflection_identity K c F hreflection hquadratic hcubic
      Z Ccut hZ hCut p hp J (I, ξ) (hcut I (hsub I hI)), hf I hI]
  rw [heq]
  exact hbound ψc Tc frozen (Quotient.out ξ) Z
    (exteriorNorm K Sc (subsetPrimeIdeal K Sc p J)) Ccut hZ (exteriorNorm_pos K Sc _)
    hCut hlogCut hlogWin J
    (selected_norm_bounds K Sc gc Tc (zero_lt_one.trans hZ) p hp J).1
    (fibreShell K Sc R frozen j) j hf hj (fun I hI => hcut I (hsub I hI))

end Target

#print axioms ordinaryResiduals_sum
#print axioms actual_residual_shell_energy
#print axioms completedMarkedRow_residual_shell_energy

end HeckeSkeleton.LowEnergy.ActualResidualDyadicEnergy
