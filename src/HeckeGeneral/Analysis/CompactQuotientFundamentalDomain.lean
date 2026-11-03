import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Data.Finset.Max

/-!
Measurable fundamental domains from a compact quotient by a discrete subgroup.

The quotient covering supplies open charts on which the quotient map is
injective. A finite subcover is ordered by `Fin n`; each chart is trimmed by
the preimages of all earlier chart images. The resulting set meets every coset
exactly once, hence is a fundamental domain for every measure simultaneously.
In a locally compact Hausdorff group the charts can first be shrunk into
compact neighborhoods, so the same construction has compact closure.

The subgroup need not be normal. The action is the actual right multiplication
action of `H.op` on the group. No countability, Polish-space, or pre-existing
fundamental-domain hypothesis is required.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open Set Topology MeasureTheory
open scoped Classical Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Subgroup G)

/-- Retain a point only in the first chart whose image contains its coset. -/
private def finiteQuotientChartSection {n : ℕ} (U : Fin n → Set G) : Set G :=
  ⋃ i : Fin n, U i \ (QuotientGroup.mk (s := H)) ⁻¹'
    (⋃ j : Fin n, ⋃ (_ : j < i), (QuotientGroup.mk (s := H)) '' U j)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem mem_finiteQuotientChartSection {n : ℕ} (U : Fin n → Set G) (x : G) :
    x ∈ finiteQuotientChartSection H U ↔
      ∃ i, x ∈ U i ∧ ∀ j, j < i →
        QuotientGroup.mk (s := H) x ∉ (QuotientGroup.mk (s := H)) '' U j := by
  simp [finiteQuotientChartSection]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem finiteQuotientChartSection_injOn {n : ℕ} (U : Fin n → Set G)
    (hU : ∀ i, Set.InjOn (QuotientGroup.mk (s := H)) (U i)) :
    Set.InjOn (QuotientGroup.mk (s := H)) (finiteQuotientChartSection H U) := by
  intro x hx y hy hxy
  obtain ⟨i, hxi, hfirstx⟩ := (mem_finiteQuotientChartSection H U x).mp hx
  obtain ⟨j, hyj, hfirsty⟩ := (mem_finiteQuotientChartSection H U y).mp hy
  rcases lt_trichotomy i j with hij | hij | hji
  · exact False.elim (hfirsty i hij ⟨x, hxi, hxy⟩)
  · subst j
    exact hU i hxi hyj hxy
  · exact False.elim (hfirstx j hji ⟨y, hyj, hxy.symm⟩)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem finiteQuotientChartSection_surjOn {n : ℕ} (U : Fin n → Set G)
    (hcover : ∀ x : G, ∃ i, QuotientGroup.mk (s := H) x ∈
      (QuotientGroup.mk (s := H)) '' U i) (x : G) :
    ∃ y ∈ finiteQuotientChartSection H U,
      QuotientGroup.mk (s := H) y = QuotientGroup.mk (s := H) x := by
  let I : Finset (Fin n) := Finset.univ.filter fun i =>
    QuotientGroup.mk (s := H) x ∈ (QuotientGroup.mk (s := H)) '' U i
  have hI : I.Nonempty := by
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let i := I.min' hI
  have hi : QuotientGroup.mk (s := H) x ∈ (QuotientGroup.mk (s := H)) '' U i :=
    (Finset.mem_filter.mp (Finset.min'_mem I hI)).2
  obtain ⟨y, hy, hyx⟩ := hi
  refine ⟨y, (mem_finiteQuotientChartSection H U y).mpr ⟨i, hy, ?_⟩, hyx⟩
  intro j hji hj
  have hjI : j ∈ I := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← hyx]
    exact hj
  have hij : i ≤ j := Finset.min'_le I j hjI
  exact (not_le_of_gt hji) hij

variable [MeasurableSpace G] [BorelSpace G]

private theorem measurableSet_finiteQuotientChartSection {n : ℕ} (U : Fin n → Set G)
    (hU : ∀ i, IsOpen (U i)) : MeasurableSet (finiteQuotientChartSection H U) := by
  apply MeasurableSet.iUnion
  intro i
  refine (hU i).measurableSet.diff ?_
  apply IsOpen.measurableSet
  apply IsOpen.preimage QuotientGroup.continuous_mk
  apply isOpen_iUnion
  intro j
  apply isOpen_iUnion
  intro _
  exact QuotientGroup.isOpenQuotientMap_mk.isOpenMap _ (hU j)

private theorem isFundamentalDomain_finiteQuotientChartSection {n : ℕ}
    (hH : IsDiscrete (H : Set G)) (U : Fin n → Set G)
    (hUopen : ∀ i, IsOpen (U i))
    (hUinj : ∀ i, Set.InjOn (QuotientGroup.mk (s := H)) (U i))
    (hcover : ∀ x : G, ∃ i, QuotientGroup.mk (s := H) x ∈
      (QuotientGroup.mk (s := H)) '' U i) (ν : Measure G) :
    IsFundamentalDomain H.op (finiteQuotientChartSection H U) ν := by
  have hc := H.isQuotientCoveringMap hH
  have := hc.isCancelSMul
  apply IsFundamentalDomain.mk'
    (measurableSet_finiteQuotientChartSection H U hUopen).nullMeasurableSet
  intro x
  obtain ⟨y, hy, hyx⟩ := finiteQuotientChartSection_surjOn H U hcover x
  obtain ⟨g, hg⟩ := hc.apply_eq_iff_mem_orbit.mp hyx
  change g • x = y at hg
  refine ⟨g, ?_, ?_⟩
  · change g • x ∈ finiteQuotientChartSection H U
    rw [hg]
    exact hy
  · intro g' hg'
    have hgy : g' • x = y := finiteQuotientChartSection_injOn H U hUinj hg' hy
      ((hc.map_smul g').trans hyx.symm)
    exact IsCancelSMul.right_cancel g' g x (hgy.trans hg.symm)

variable [CompactSpace (G ⧸ H)]

omit [MeasurableSpace G] [BorelSpace G] in
/-- Relabel the finite chart subcover by an actual finite ordinal. -/
private theorem finite_quotientChart_cover (U : G → Set G)
    (hUopen : ∀ x, IsOpen (U x)) (hUx : ∀ x, x ∈ U x) :
    ∃ n : ℕ, ∃ f : Fin n → G, ∀ x : G, ∃ i,
      QuotientGroup.mk (s := H) x ∈ (QuotientGroup.mk (s := H)) '' U (f i) := by
  have hcover : (Set.univ : Set (G ⧸ H)) ⊆
      ⋃ x : G, (QuotientGroup.mk (s := H)) '' U x := by
    intro q _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact Set.mem_iUnion.mpr ⟨x, x, hUx x, rfl⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : G => (QuotientGroup.mk (s := H)) '' U x)
    (fun x => QuotientGroup.isOpenQuotientMap_mk.isOpenMap _ (hUopen x)) hcover
  let e : ↥t ≃ Fin (Fintype.card ↥t) := Fintype.equivFin ↥t
  refine ⟨Fintype.card ↥t, fun i => (e.symm i).val, ?_⟩
  intro x
  obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ (QuotientGroup.mk (s := H) x)))
  obtain ⟨hyt, hxy⟩ := Set.mem_iUnion.mp hy
  refine ⟨e ⟨y, hyt⟩, ?_⟩
  simpa only [Equiv.symm_apply_apply] using hxy

/-- A compact quotient by a discrete subgroup has a Borel representative domain.
The same domain is fundamental for every measure, with no null exceptional set. -/
theorem exists_measurable_fundamentalDomain_of_compact_quotient
    (hH : IsDiscrete (H : Set G)) :
    ∃ F : Set G, MeasurableSet F ∧ ∀ ν : Measure G, IsFundamentalDomain H.op F ν := by
  have hc := H.isQuotientCoveringMap hH
  have hcharts := hc.isCoveringMap.isLocalHomeomorph.isLocallyInjective
  choose U hUopen hUx hUinj using hcharts
  obtain ⟨n, f, hcover⟩ := finite_quotientChart_cover H U hUopen hUx
  refine ⟨finiteQuotientChartSection H (fun i : Fin n => U (f i)),
    measurableSet_finiteQuotientChartSection H _ (fun i => hUopen (f i)), ?_⟩
  intro ν
  exact isFundamentalDomain_finiteQuotientChartSection H hH _
    (fun i => hUopen (f i)) (fun i => hUinj (f i)) hcover ν

variable [LocallyCompactSpace G] [T2Space G]

/-- Shrinking the charts before taking the finite subcover gives a Borel domain
with compact closure. Its construction is independent of the chosen measure. -/
theorem exists_precompact_fundamentalDomain_of_compact_quotient
    (hH : IsDiscrete (H : Set G)) :
    ∃ F : Set G, MeasurableSet F ∧ IsCompact (closure F) ∧
      ∀ ν : Measure G, IsFundamentalDomain H.op F ν := by
  have hc := H.isQuotientCoveringMap hH
  have hcharts := hc.isCoveringMap.isLocalHomeomorph.isLocallyInjective
  choose U hUopen hUx hUinj using hcharts
  choose C hCcompact hxC hCU using fun x => exists_compact_subset (hUopen x) (hUx x)
  obtain ⟨n, f, hcover⟩ := finite_quotientChart_cover H
    (fun x => interior (C x)) (fun _ => isOpen_interior) hxC
  let V : Fin n → Set G := fun i => interior (C (f i))
  let F := finiteQuotientChartSection H V
  have hFmeas : MeasurableSet F := measurableSet_finiteQuotientChartSection H V
    (fun _ => isOpen_interior)
  have hbound : F ⊆ ⋃ i : Fin n, C (f i) := by
    intro x hx
    obtain ⟨i, hi, _⟩ := (mem_finiteQuotientChartSection H V x).mp hx
    exact Set.mem_iUnion.mpr ⟨i, interior_subset hi⟩
  have hcompact : IsCompact (⋃ i : Fin n, C (f i)) :=
    isCompact_iUnion fun i => hCcompact (f i)
  refine ⟨F, hFmeas,
    hcompact.of_isClosed_subset isClosed_closure (closure_minimal hbound hcompact.isClosed), ?_⟩
  intro ν
  exact isFundamentalDomain_finiteQuotientChartSection H hH V
    (fun _ => isOpen_interior)
    (fun i => (hUinj (f i)).mono (interior_subset.trans (hCU (f i)))) hcover ν

end HeckeGeneral.Analysis
