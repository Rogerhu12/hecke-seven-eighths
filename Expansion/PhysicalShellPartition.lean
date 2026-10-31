import Expansion.PhysicalRowSupport
import Expansion.ProjectSelectedPhysicalRows
import ExpansionInterfaces.DyadicShells

/-!
# Exact retained physical-row partition

Every nonprincipal row between the global cutoffs belongs to exactly one
upper-closed dyadic shell. The last shell is clipped at the original global
cutoff. The buffered row choice is made before integration, so the resulting
double sum is an identity for the original row values.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical
open ExpansionInterfaces
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The retained rows use the original global upper cutoff, with no extra
rows from the natural envelope of the last dyadic shell. -/
def retainedGlobalRows (Z lower upper : ℝ) : Finset (FrequencyRow K S) :=
  (frequencyRows K S (Z ^ upper)).filter fun u =>
    Z ^ lower < frequencyRowNorm K S u ∧ ¬principalFrequencyRow K S u

/-- An actual shell in the finite schedule, clipped at the global endpoint. -/
def physicalShellRows (Z lower upper : ℝ) (j : Fin (shellCount Z lower upper)) :
    Finset (FrequencyRow K S) :=
  (retainedShellRows K S (Z ^ shellExponent Z lower j.val)).filter fun u =>
    frequencyRowNorm K S u ≤ Z ^ upper

theorem mem_physicalShellRows_iff {Z lower upper : ℝ} (hZ : 1 < Z)
    (j : Fin (shellCount Z lower upper)) (u : FrequencyRow K S) :
    u ∈ physicalShellRows K S Z lower upper j ↔
      Z ^ shellExponent Z lower j.val < frequencyRowNorm K S u ∧
      frequencyRowNorm K S u ≤ 2 * Z ^ shellExponent Z lower j.val ∧
      frequencyRowNorm K S u ≤ Z ^ upper ∧ ¬principalFrequencyRow K S u := by
  have hU : 0 ≤ 2 * Z ^ shellExponent Z lower j.val := by positivity
  simp only [physicalShellRows, retainedShellRows, Finset.mem_filter,
    mem_frequencyRows_iff K S _ hU]
  tauto

/-- The finite shell schedule covers exactly the retained nonprincipal rows. -/
theorem biUnion_physicalShellRows {Z lower upper : ℝ} (hZ : 1 < Z) :
    Finset.univ.biUnion (physicalShellRows K S Z lower upper) =
      retainedGlobalRows K S Z lower upper := by
  have hZ0 : 0 < Z := lt_trans zero_lt_one hZ
  ext u
  constructor
  · intro hu
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨hlo, _, hupper, hnpr⟩ := (mem_physicalShellRows_iff K S hZ j u).mp hj
    have hbase : Z ^ lower ≤ Z ^ shellExponent Z lower j.val :=
      Real.rpow_le_rpow_of_exponent_le hZ.le (actualShell_range hZ j).1
    apply Finset.mem_filter.mpr
    exact ⟨(mem_frequencyRows_iff K S _ (Real.rpow_pos_of_pos hZ0 _).le u).mpr hupper,
      hbase.trans_lt hlo, hnpr⟩
  · intro hu
    obtain ⟨hrows, hlo, hnpr⟩ := Finset.mem_filter.mp hu
    have hupper := (mem_frequencyRows_iff K S _
      (Real.rpow_pos_of_pos hZ0 upper).le u).mp hrows
    let j := actualShellIndex Z lower upper (frequencyRowNorm K S u) hZ hlo hupper
    have hj := actualShellIndex_spec Z lower upper (frequencyRowNorm K S u) hZ hlo hupper
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_univ _, ?_⟩
    exact (mem_physicalShellRows_iff K S hZ j u).mpr
      ⟨hj.2.2.1, hj.2.2.2, hupper, hnpr⟩

/-- Strict lower endpoints and weak upper endpoints prevent duplicate rows,
including rows whose norms are exact dyadic endpoints. -/
theorem physicalShellRows_disjoint {Z lower upper : ℝ} (hZ : 1 < Z)
    {i j : Fin (shellCount Z lower upper)} (hij : i ≠ j) :
    Disjoint (physicalShellRows K S Z lower upper i)
      (physicalShellRows K S Z lower upper j) := by
  apply Finset.disjoint_left.mpr
  intro u hui huj
  have hi := (mem_physicalShellRows_iff K S hZ i u).mp hui
  have hj := (mem_physicalShellRows_iff K S hZ j u).mp huj
  have hbase : 0 < Z ^ lower := Real.rpow_pos_of_pos (lt_trans zero_lt_one hZ) _
  have hi' : Z ^ lower * (2 : ℝ) ^ i.val < frequencyRowNorm K S u ∧
      frequencyRowNorm K S u ≤ Z ^ lower * (2 : ℝ) ^ (i.val + 1) := by
    simpa only [shellExponent_identity hZ, pow_succ, mul_assoc,
      mul_left_comm, mul_comm] using And.intro hi.1 hi.2.1
  have hj' : Z ^ lower * (2 : ℝ) ^ j.val < frequencyRowNorm K S u ∧
      frequencyRowNorm K S u ≤ Z ^ lower * (2 : ℝ) ^ (j.val + 1) := by
    simpa only [shellExponent_identity hZ, pow_succ, mul_assoc,
      mul_left_comm, mul_comm] using And.intro hj.1 hj.2.1
  exact hij (Fin.ext (dyadicShell_unique hbase hi' hj'))

/-- Exact shell summation for arbitrary original row values. -/
theorem sum_physicalShellRows {Z lower upper : ℝ} (hZ : 1 < Z)
    (value : FrequencyRow K S → ℂ) :
    (∑ j : Fin (shellCount Z lower upper),
      ∑ u ∈ physicalShellRows K S Z lower upper j, value u) =
      ∑ u ∈ retainedGlobalRows K S Z lower upper, value u := by
  rw [← biUnion_physicalShellRows K S hZ]
  symm
  apply Finset.sum_biUnion
  intro i _ j _ hij
  exact physicalShellRows_disjoint K S hZ hij

variable (ω ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K))
variable (P : ProbeData K S) (E : RowEulerData K S P)
variable (hψ : ψ ∈ HeckePacket K ω)
variable (hΘ : ∀ θ ∈ Θ, FiniteOrder θ)
variable {B e : ℝ} (hB0 : (51 / 100 : ℝ) ≤ B) (hB : B ≤ 1) (he : 0 < e)
variable (hbound : ∀ χ r, r ∈ heckePacketZeros K ω χ →
  1 / 2 ≤ r → r ≤ 1 → r ≤ B)

/-- The actual finite shell and buffered-bin schedule counts every retained
row exactly once, before any contour integration or label decomposition. -/
theorem sum_clippedSelectedPhysicalShellRows {Z lower upper : ℝ} (hZ : 1 < Z)
    (T : ℝ) (value : FrequencyRow K S → ℂ) :
    (∑ j : Fin (shellCount Z lower upper), ∑ b : RowBufferIndex B e,
      ∑ u ∈ clippedSelectedPhysicalRows K S ω ψ Θ P E hψ hΘ hB0 hB he hbound
        (Z ^ shellExponent Z lower j.val) (Z ^ upper) T b, value u) =
      ∑ u ∈ retainedGlobalRows K S Z lower upper, value u := by
  calc
    _ = ∑ j : Fin (shellCount Z lower upper),
        ∑ u ∈ physicalShellRows K S Z lower upper j, value u := by
      apply Finset.sum_congr rfl
      intro j _
      exact sum_clippedSelectedPhysicalRows K S ω ψ Θ P E hψ hΘ hB0 hB he hbound
        _ _ T value
    _ = _ := sum_physicalShellRows K S hZ value

end Expansion.Project

#print axioms Expansion.Project.biUnion_physicalShellRows
#print axioms Expansion.Project.physicalShellRows_disjoint
#print axioms Expansion.Project.sum_physicalShellRows
#print axioms Expansion.Project.sum_clippedSelectedPhysicalShellRows
