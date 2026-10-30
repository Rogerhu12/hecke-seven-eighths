import HeckeGeneral.Analysis.SUnitSchwartzDecay

/-! Uniform decay on the span of a fixed finite family of actual finite-local
test functions. The coefficient dependence is its explicit l1 norm. -/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic MeasureTheory
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "T" => sLocalNormOneGroup K S
local notation "L" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

variable {ι : Type*} [Fintype ι]

/-- An actual finite linear combination on the additive finite-local space. -/
def finiteLocalProfileCombination
    (ψ : ι → (Π v : S, v.val.adicCompletion K) → ℂ) (c : ι → ℂ)
    (z : Π v : S, v.val.adicCompletion K) : ℂ :=
  ∑ i, c i * ψ i z

theorem sLocalSchwartzSlice_finiteLocalProfileCombination
    (φ : SchwartzMap V ℂ) (ψ : ι → (Π v : S, v.val.adicCompletion K) → ℂ) (c : ι → ℂ)
    (r : {r : ℝ // 0 < r}) (x : T) :
    sLocalSchwartzSlice K S φ (finiteLocalProfileCombination K S ψ c) r x =
      ∑ i, c i * sLocalSchwartzSlice K S φ (ψ i) r x := by
  unfold sLocalSchwartzSlice sLocalTensorTestFunction finiteLocalProfileCombination
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

include Γ in
/-- Profile linearity is obtained from actual integrability of each slice. -/
theorem sUnitOrbitalProfile_finiteLocalProfileCombination
    (φ : SchwartzMap V ℂ) (ψ : ι → (Π v : S, v.val.adicCompletion K) → ℂ)
    (hψ : ∀ i, Continuous (ψ i)) (hcs : ∀ i, HasCompactSupport (ψ i))
    (c : ι → ℂ) (r : {r : ℝ // 0 < r}) :
    sUnitOrbitalProfile K S
      (sLocalTensorTestFunction K S φ (finiteLocalProfileCombination K S ψ c)) r =
      ∑ i, c i * sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ (ψ i)) r := by
  change (∫ x : T,
    sLocalSchwartzSlice K S φ (finiteLocalProfileCombination K S ψ c) r x
      ∂sUnitHaarMeasure K S) =
    ∑ i, c i * ∫ x : T, sLocalSchwartzSlice K S φ (ψ i) r x ∂sUnitHaarMeasure K S
  simp_rw [sLocalSchwartzSlice_finiteLocalProfileCombination]
  rw [integral_finset_sum _ (fun i _ =>
    (integrable_sLocalSchwartzSlice K S Γ φ (ψ i) (hψ i) (hcs i) r).const_mul (c i))]
  simp only [integral_const_mul]

include Γ in
/-- A fixed family has one decay constant for every coefficient vector and
every archimedean Schwartz function. No profile-linearity or decay hypothesis
is introduced. -/
theorem exists_sLocalSchwartzProfile_finiteFamily_power_decay
    (ψ : ι → (Π v : S, v.val.adicCompletion K) → ℂ) (hψ : ∀ i, Continuous (ψ i))
    (hcs : ∀ i, HasCompactSupport (ψ i))
    (A : ℝ) (M : ℕ) (hM : Module.finrank ℤ L < M)
    (hOrder : (Module.finrank ℚ K : ℝ) * A ≤ M) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ c : ι → ℂ, ∀ φ : SchwartzMap V ℂ,
      ∀ r : {r : ℝ // 0 < r}, 1 ≤ r.val →
      ‖sUnitOrbitalProfile K S
        (sLocalTensorTestFunction K S φ (finiteLocalProfileCombination K S ψ c)) r‖ ≤
        D * (∑ i, ‖c i‖) * SchwartzMap.seminorm ℂ M 0 φ * r.val ^ (-A) := by
  choose d hd hbound using (fun i : ι =>
    exists_sLocalSchwartzProfile_power_decay K S Γ (ψ i) (hψ i) (hcs i) A M hM hOrder)
  let D : ℝ := ∑ i, d i
  have hD : 0 ≤ D := Finset.sum_nonneg (fun i _ => hd i)
  have hdD (i : ι) : d i ≤ D :=
    Finset.single_le_sum (fun j _ => hd j) (Finset.mem_univ i)
  refine ⟨D, hD, fun c φ r hr => ?_⟩
  have hseminorm : 0 ≤ SchwartzMap.seminorm ℂ M 0 φ :=
    apply_nonneg (SchwartzMap.seminorm ℂ M 0) φ
  have hrpow : 0 ≤ r.val ^ (-A) := Real.rpow_nonneg r.property.le _
  rw [sUnitOrbitalProfile_finiteLocalProfileCombination K S Γ φ ψ hψ hcs c r]
  calc
    _ ≤ ∑ i, ‖c i * sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ (ψ i)) r‖ :=
      norm_sum_le _ _
    _ = ∑ i, ‖c i‖ * ‖sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ (ψ i)) r‖ := by
      simp only [norm_mul]
    _ ≤ ∑ i, ‖c i‖ * (d i * SchwartzMap.seminorm ℂ M 0 φ * r.val ^ (-A)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hbound i φ r hr) (norm_nonneg _)
    _ ≤ ∑ i, ‖c i‖ * (D * SchwartzMap.seminorm ℂ M 0 φ * r.val ^ (-A)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hdD i) hseminorm) hrpow) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

end HeckeGeneral.Analysis
