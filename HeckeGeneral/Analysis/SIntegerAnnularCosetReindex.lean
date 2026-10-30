import HeckeGeneral.Analysis.SIntegerAnnularSexticCosets
import HeckeGeneral.Arithmetic.ClearedUnitLattice
import HeckeGeneral.Arithmetic.IdealLatticeQuotient

/-!
Exact coset indexing. Ordinary ideal translates retain every
actual element. The nonzero condition is explicit in the equivalence;
the final product-indexed sum restores the omitted origin only through
the proved zero value of its summand. No infinite sums are interchanged.
The ordinary period includes an arbitrary nonzero auxiliary ideal M.
This permits later conductor refinement but asserts no invariance of the
missing reciprocity correction or deeper fixed-ray coefficient.
-/

noncomputable section
namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
local notation "N" => NonzeroRingElements (S.integer K)

def sIntegerAnnularActive :=
  {m : N // (sLocalNonzeroIntegerDiagonal K S m).2 ∈
    finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)}

/-- The translated element, in the actual S-integer ring, rather than
a field norm or chosen associate. -/
def sIntegerAnnularCosetValue (M : Ideal (𝓞 K)) (c : N) (T : Finset N)
    (p : {n : N // n ∈ T} × sIntegerAnnularSexticPeriod K S M c) : S.integer K :=
  p.1.val.val + algebraMap (𝓞 K) (S.integer K) p.2.val

def sIntegerAnnularCosetIndex (M : Ideal (𝓞 K)) (c : N) (T : Finset N) :=
  {p : {n : N // n ∈ T} × sIntegerAnnularSexticPeriod K S M c //
    sIntegerAnnularCosetValue K S M c T p ≠ 0}

/-- Exact arithmetic reindexing by disjoint ordinary ideal translates.
The finite representative set is chosen before any analytic function or
archimedean scale. In the last identity both sides have one index; it is
not a claim that a nonabsolutely convergent double sum can be split. -/
theorem exists_sIntegerAnnularCosetEquiv_and_tsum (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (c : N) :
    ∃ T : Finset N,
    ∃ e : sIntegerAnnularCosetIndex K S M c T ≃ sIntegerAnnularActive K S Γ,
      (∀ p, (e p).val.val = sIntegerAnnularCosetValue K S M c T p.val) ∧
      ∀ F : S.integer K → ℂ, F 0 = 0 →
        (∑' m : sIntegerAnnularActive K S Γ, F m.val.val) =
          ∑' p : {n : N // n ∈ T} × sIntegerAnnularSexticPeriod K S M c,
            F (sIntegerAnnularCosetValue K S M c T p) := by
  obtain ⟨T, hdisjoint, hcover⟩ :=
    exists_finite_sIntegerAnnular_period_representatives K S Γ M hM c
  let f : sIntegerAnnularCosetIndex K S M c T → sIntegerAnnularActive K S Γ := fun p =>
    let m : N := ⟨sIntegerAnnularCosetValue K S M c T p.val, p.property⟩
    ⟨m, (hcover m).mpr ⟨p.val.1.val, p.val.1.property,
      p.val.2.val, p.val.2.property, by
        change (p.val.1.val.val + algebraMap (𝓞 K) (S.integer K) p.val.2.val) -
          p.val.1.val.val = algebraMap (𝓞 K) (S.integer K) p.val.2.val
        ring⟩⟩
  have hinj : Function.Injective f := by
    intro p q hpq
    have he : p.val.1.val.val + algebraMap (𝓞 K) (S.integer K) p.val.2.val =
        q.val.1.val.val + algebraMap (𝓞 K) (S.integer K) q.val.2.val :=
      congrArg (fun x : sIntegerAnnularActive K S Γ => x.val.val) hpq
    have hn : p.val.1.val = q.val.1.val := by
      by_contra hne
      apply hdisjoint p.val.1.val p.val.1.property q.val.1.val q.val.1.property hne
      refine ⟨q.val.2.val - p.val.2.val,
        (sIntegerAnnularSexticPeriod K S M c).sub_mem q.val.2.property p.val.2.property, ?_⟩
      rw [map_sub]
      linear_combination he
    have htS : algebraMap (𝓞 K) (S.integer K) p.val.2.val =
        algebraMap (𝓞 K) (S.integer K) q.val.2.val := by
      rw [hn] at he
      exact add_left_cancel he
    have ht : p.val.2.val = q.val.2.val :=
      RingOfIntegers.coe_injective (congrArg (fun x : S.integer K => (x : K)) htS)
    apply Subtype.ext
    exact Prod.ext (Subtype.ext hn) (Subtype.ext ht)
  have hsurj : Function.Surjective f := by
    intro m
    obtain ⟨n, hn, t, ht, hdiff⟩ := (hcover m.val).mp m.property
    have he : n.val + algebraMap (𝓞 K) (S.integer K) t = m.val.val := by
      rw [← hdiff]
      ring
    let p0 : {n : N // n ∈ T} × sIntegerAnnularSexticPeriod K S M c :=
      (⟨n, hn⟩, ⟨t, ht⟩)
    have hp0 : sIntegerAnnularCosetValue K S M c T p0 ≠ 0 := by
      change n.val + algebraMap (𝓞 K) (S.integer K) t ≠ 0
      rw [he]
      exact m.val.property
    refine ⟨⟨p0, hp0⟩, ?_⟩
    apply Subtype.ext
    exact Subtype.ext he
  let e := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have he (p : sIntegerAnnularCosetIndex K S M c T) :
      (e p).val.val = sIntegerAnnularCosetValue K S M c T p.val := rfl
  refine ⟨T, e, he, fun F hF0 => ?_⟩
  have hs : Function.support (fun p : {n : N // n ∈ T} × sIntegerAnnularSexticPeriod K S M c =>
      F (sIntegerAnnularCosetValue K S M c T p)) ⊆
      {p | sIntegerAnnularCosetValue K S M c T p ≠ 0} := by
    intro p hp hz
    exact hp (by
      change F (sIntegerAnnularCosetValue K S M c T p) = 0
      rw [hz, hF0])
  calc
    _ = ∑' p : sIntegerAnnularCosetIndex K S M c T, F (e p).val.val :=
      (e.tsum_eq (fun m => F m.val.val)).symm
    _ = ∑' p : sIntegerAnnularCosetIndex K S M c T,
        F (sIntegerAnnularCosetValue K S M c T p.val) := by
      apply tsum_congr
      intro p
      rw [he]
    _ = _ := tsum_subtype_eq_of_support_subset hs

/-- A literal annular factor provides the zero value required by the
full additive-coset sum, even when S is empty. Other multiplicative
coefficient factors may be retained without any nonvanishing assumption. -/
theorem sIntegerAnnular_arch_kernel_zero
    (a : ℝ → ℝ) (ξ : SFiniteLocalGroup K S) (r : ℝ)
    (b : S.integer K → ℂ) :
    b 0 * (sUnitAnnularPartitionCutoff K S Γ a ξ
      (r⁻¹ • traceEmbedding K ((0 : S.integer K) : K)) : ℂ) = 0 := by
  change b 0 * (sUnitAnnularPartitionCutoff K S Γ a ξ
    (r⁻¹ • traceEmbedding K (0 : K)) : ℂ) = 0
  simp only [traceEmbedding_zero, smul_zero,
    sUnitAnnularPartitionCutoff_origin, Complex.ofReal_zero, mul_zero]

/-- The actual ordinary period, with the proved nonzero ideal condition
needed by the arithmetic trace-lattice construction. -/
def sIntegerAnnularPeriodIdealNZ (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (c : N) : (Ideal (𝓞 K))⁰ :=
  ⟨sIntegerAnnularSexticPeriod K S M c,
    mem_nonZeroDivisors_of_ne_zero (sIntegerAnnularSexticPeriod_ne_bot K S M hM c)⟩

/-- Actual integral-ideal elements enumerate their trace ideal lattice
bijectively. This retains both the zero and every nonzero lattice point. -/
def integralIdealTraceElementEquiv (I : (Ideal (𝓞 K))⁰) :
    I.val ≃ traceIdealLattice K (integralIdealUnit K I) := by
  let f : I.val → traceIdealLattice K (integralIdealUnit K I) := fun t =>
    ⟨traceEmbedding K (t.val : K), (traceEmbedding_integral_mem K I t.val).mpr t.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro t u htu
    apply Subtype.ext
    apply RingOfIntegers.coe_injective
    exact traceEmbedding_injective K (congrArg Subtype.val htu)
  · intro l
    obtain ⟨x, hx, hxl⟩ := exists_traceEmbedding_eq_of_mem_traceIdealLattice
      K (integralIdealUnit K I) l.property
    obtain ⟨t, ht, htx⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hx
    refine ⟨⟨t, ht⟩, Subtype.ext ?_⟩
    change traceEmbedding K (t : K) = (l : mixedEmbedding.euclidean.mixedSpace K)
    change (t : K) = x at htx
    rw [htx]
    exact hxl

@[simp] theorem integralIdealTraceElementEquiv_apply (I : (Ideal (𝓞 K))⁰) (t : I.val) :
    (integralIdealTraceElementEquiv K I t : mixedEmbedding.euclidean.mixedSpace K) =
      traceEmbedding K (t.val : K) := rfl

/-- Each actual annular coset is exactly an ordinary trace-ideal lattice
translate. The archimedean scale acts on the entire translated argument.
The origin remains included; this is the literal input to translated PSF. -/
theorem tsum_sIntegerAnnular_coset_eq_trace_lattice
    (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (c n : N) (r : ℝ) (H : mixedEmbedding.euclidean.mixedSpace K → ℂ) :
    (∑' t : sIntegerAnnularSexticPeriod K S M c,
      H (r⁻¹ • traceEmbedding K
        ((n.val + algebraMap (𝓞 K) (S.integer K) t.val : S.integer K) : K))) =
      ∑' l : traceIdealLattice K (integralIdealUnit K (sIntegerAnnularPeriodIdealNZ K S M hM c)),
        H (r⁻¹ • (traceEmbedding K (n.val : K) +
          (l : mixedEmbedding.euclidean.mixedSpace K))) := by
  let I := sIntegerAnnularPeriodIdealNZ K S M hM c
  have h := (integralIdealTraceElementEquiv K I).tsum_eq
    (fun l => H (r⁻¹ • (traceEmbedding K (n.val : K) +
      (l : mixedEmbedding.euclidean.mixedSpace K))))
  change (∑' t : I.val,
    H (r⁻¹ • traceEmbedding K ((n.val : K) + (t.val : K)))) = _
  simpa only [integralIdealTraceElementEquiv_apply, traceEmbedding,
    map_add] using h

end HeckeGeneral.Analysis
