import HeckeSkeleton.HighBinSupport.HighNormFormAmplitude
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
A measurable finite amplitude partition. The bucket index is the first
geometric threshold attained, with the final index as a total fallback.
Thus it is defined before any cap theorem, and its fibers are measurable
for measurable actual slot profiles. The cap is used only to prove the
upper estimate in the clipped final bucket.

The finite fibers partition the integration domain exactly. Their integral
identity requires genuine integrability and permits overlapping row sets:
the partition is in the height variable separately for each row.
-/

set_option autoImplicit false
noncomputable section

namespace HighBinVerified.NormForm

open MeasureTheory Set
open scoped BigOperators Classical

private theorem pointwiseBucket_exists (P theta : ℝ) (N : ℕ) (M : ℝ) :
    ∃ n : ℕ, n ≤ N ∧ (n = N ∨ M ≤ P ^ (((n : ℝ) + 1) * theta)) :=
  ⟨N, le_rfl, Or.inl rfl⟩

/-- The first threshold, with the final bucket retained even beyond the cap. -/
def pointwiseBucket (P theta : ℝ) (N : ℕ) (M : ℝ) : Fin (N + 1) :=
  ⟨Nat.find (pointwiseBucket_exists P theta N M),
    Nat.lt_succ_of_le (Nat.find_spec (pointwiseBucket_exists P theta N M)).1⟩

/-- Measurability uses the threshold predicates, not an arbitrary choice
of a bucket satisfying a list of analytic inequalities. -/
theorem pointwiseBucket_val_measurable (P theta : ℝ) (N : ℕ) :
    Measurable (fun M : ℝ => (pointwiseBucket P theta N M).val) := by
  apply measurable_find (pointwiseBucket_exists P theta N)
  intro n
  exact (MeasurableSet.const (n ≤ N)).inter
    ((MeasurableSet.const (n = N)).union (measurableSet_le measurable_id measurable_const))

/-- Both bounds are consequences of this explicit bucket recipe. Positive
amplitudes have a strict lower witness at the very same profile value. -/
theorem pointwiseBucket_spec (P theta cap M : ℝ) (N : ℕ)
    (hP : 1 ≤ P) (htheta : 0 < theta) (hcap : 0 ≤ cap)
    (hN : cap ≤ (N : ℝ) * theta) (hupper : M ≤ P ^ (cap + theta)) :
    let amplitude := min (((pointwiseBucket P theta N M).val : ℝ) * theta) cap
    0 ≤ amplitude ∧ amplitude ≤ cap ∧ M ≤ P ^ (amplitude + theta) ∧
      (0 < amplitude → P ^ amplitude < M) := by
  let k := Nat.find (pointwiseBucket_exists P theta N M)
  have hk : k ≤ N ∧ (k = N ∨ M ≤ P ^ (((k : ℝ) + 1) * theta)) :=
    Nat.find_spec (pointwiseBucket_exists P theta N M)
  change 0 ≤ min ((k : ℝ) * theta) cap ∧
    min ((k : ℝ) * theta) cap ≤ cap ∧
    M ≤ P ^ (min ((k : ℝ) * theta) cap + theta) ∧
    (0 < min ((k : ℝ) * theta) cap → P ^ min ((k : ℝ) * theta) cap < M)
  have hkt : 0 ≤ (k : ℝ) * theta := mul_nonneg (Nat.cast_nonneg _) htheta.le
  refine ⟨le_min hkt hcap, min_le_right _ _, ?_, ?_⟩
  · by_cases hkN : k = N
    · have hc : cap ≤ (k : ℝ) * theta := by simpa only [hkN] using hN
      simpa only [min_eq_right hc] using hupper
    · have hthreshold := hk.2.resolve_left hkN
      by_cases hkc : (k : ℝ) * theta ≤ cap
      · rw [min_eq_left hkc]
        convert hthreshold using 1 <;> congr 1 <;> ring
      · simpa only [min_eq_right (le_of_not_ge hkc)] using hupper
  · intro hg
    have hkpos : 0 < k := by
      by_contra hn
      have hk0 : k = 0 := by omega
      simp only [hk0, Nat.cast_zero, zero_mul, min_eq_left hcap] at hg
      linarith
    have hprev := Nat.find_min (pointwiseBucket_exists P theta N M)
      (show k - 1 < k by omega)
    have hkcast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
      have heq : k - 1 + 1 = k := by omega
      exact_mod_cast heq
    have hstrict : P ^ ((k : ℝ) * theta) < M := by
      apply lt_of_not_ge
      intro hh
      exact hprev ⟨by omega, Or.inr (by simpa only [hkcast] using hh)⟩
    exact (Real.rpow_le_rpow_of_exponent_le hP (min_le_left _ _)).trans_lt hstrict

/-- The simultaneous label at one height. -/
def pointwiseAmplitudeLabel {X : Type*} (J N : ℕ) (P theta : ℝ)
    (M : Fin J → X → ℝ) (x : X) : Fin J → Fin (N + 1) :=
  fun i => pointwiseBucket P theta N (M i x)

/-- A literal height fiber of the simultaneous finite label. -/
def amplitudeRegion {X : Type*} (J N : ℕ) (P theta : ℝ)
    (M : Fin J → X → ℝ) (domain : Set X) (label : Fin J → Fin (N + 1)) : Set X :=
  {x | x ∈ domain ∧ ∀ i, (pointwiseBucket P theta N (M i x)).val = (label i).val}

theorem mem_amplitudeRegion_iff {X : Type*} (J N : ℕ) (P theta : ℝ)
    (M : Fin J → X → ℝ) (domain : Set X) (label : Fin J → Fin (N + 1)) (x : X) :
    x ∈ amplitudeRegion J N P theta M domain label ↔
      x ∈ domain ∧ pointwiseAmplitudeLabel J N P theta M x = label := by
  constructor
  · rintro ⟨hx, hlabel⟩
    exact ⟨hx, funext (fun i => Fin.ext (hlabel i))⟩
  · rintro ⟨hx, hlabel⟩
    exact ⟨hx, fun i => congrArg Fin.val (congrFun hlabel i)⟩

theorem amplitudeRegion_subset {X : Type*} (J N : ℕ) (P theta : ℝ)
    (M : Fin J → X → ℝ) (domain : Set X) (label : Fin J → Fin (N + 1)) :
    amplitudeRegion J N P theta M domain label ⊆ domain := fun _ h => h.1

theorem amplitudeRegion_measurable {X : Type*} [MeasurableSpace X]
    (J N : ℕ) (P theta : ℝ) (M : Fin J → X → ℝ)
    (hM : ∀ i, Measurable (M i)) (domain : Set X) (hdom : MeasurableSet domain)
    (label : Fin J → Fin (N + 1)) :
    MeasurableSet (amplitudeRegion J N P theta M domain label) := by
  have hrepr : amplitudeRegion J N P theta M domain label =
      domain ∩ ⋂ i, {x | (pointwiseBucket P theta N (M i x)).val = (label i).val} := by
    ext x
    simp only [amplitudeRegion, mem_setOf_eq, mem_inter_iff, mem_iInter]
  rw [hrepr]
  exact hdom.inter (MeasurableSet.iInter fun i =>
    measurableSet_eq_fun ((pointwiseBucket_val_measurable P theta N).comp (hM i))
      measurable_const)

theorem amplitudeRegion_disjoint {X : Type*} (J N : ℕ) (P theta : ℝ)
    (M : Fin J → X → ℝ) (domain : Set X) :
    Pairwise (fun a b => Disjoint
      (amplitudeRegion J N P theta M domain a)
      (amplitudeRegion J N P theta M domain b)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro x hxa hxb
  have ha := (mem_amplitudeRegion_iff J N P theta M domain a x).mp hxa
  have hb := (mem_amplitudeRegion_iff J N P theta M domain b x).mp hxb
  exact hab (ha.2.symm.trans hb.2)

theorem iUnion_amplitudeRegion {X : Type*} (J N : ℕ) (P theta : ℝ)
    (M : Fin J → X → ℝ) (domain : Set X) :
    (⋃ label, amplitudeRegion J N P theta M domain label) = domain := by
  ext x
  constructor
  · intro hx
    obtain ⟨label, hlabel⟩ := mem_iUnion.mp hx
    exact hlabel.1
  · intro hx
    exact mem_iUnion.mpr ⟨pointwiseAmplitudeLabel J N P theta M x,
      (mem_amplitudeRegion_iff J N P theta M domain _ x).mpr ⟨hx, rfl⟩⟩

/-- The restricted integrals preserve the exact original integral. -/
theorem sum_integral_amplitudeRegion {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (J N : ℕ) (P theta : ℝ) (M : Fin J → X → ℝ)
    (hM : ∀ i, Measurable (M i)) (domain : Set X) (hdom : MeasurableSet domain)
    (f : X → ℂ) (hf : IntegrableOn f domain μ) :
    (∑ label : Fin J → Fin (N + 1),
      ∫ x in amplitudeRegion J N P theta M domain label, f x ∂μ) =
      ∫ x in domain, f x ∂μ := by
  rw [← integral_iUnion_fintype
    (fun label => amplitudeRegion_measurable J N P theta M hM domain hdom label)
    (amplitudeRegion_disjoint J N P theta M domain)
    (fun label => hf.mono_set (amplitudeRegion_subset J N P theta M domain label))]
  rw [iUnion_amplitudeRegion]

end HighBinVerified.NormForm

#print axioms HighBinVerified.NormForm.pointwiseBucket_val_measurable
#print axioms HighBinVerified.NormForm.pointwiseBucket_spec
#print axioms HighBinVerified.NormForm.amplitudeRegion_measurable
#print axioms HighBinVerified.NormForm.sum_integral_amplitudeRegion
