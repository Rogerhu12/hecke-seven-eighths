import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocationMass

/-!
# Injecting each actual occurrence allocation into the fixed cap

Different genuine support-cover branches retain different numbers of
slots. The arithmetic carrier can nevertheless use the one earlier
occurrence cap: each nonempty occurrence subset is mapped through the
literal inclusion of Fin m into Fin n. The resulting map of complete
allocation functions is injective, including empty prime supports.
No allocation label is removed or counted a second time.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep.AllocationMass

open NumberField HeckePort.IdealMobiusDivisorSum

def finInclusion {m n : ℕ} (h : m ≤ n) : Fin m ↪ Fin n where
  toFun i := ⟨i.val, lt_of_lt_of_le i.isLt h⟩
  inj' := by
    intro i j hij
    exact Fin.ext (congrArg (fun z : Fin n => z.val) hij)

/-- The literal occurrence map, also available before a nonempty
allocation is packaged as a subtype. -/
def padSelection {ι : Type*} {m n : ℕ} (h : m ≤ n)
    (a : ι → Finset (Fin m)) : ι → Finset (Fin n) :=
  fun p => (a p).map (finInclusion h)

def pad {ι : Type*} (P : Finset ι) {m n : ℕ} (h : m ≤ n)
    (a : allocations P m) : allocations P n :=
  ⟨fun p => (a.val p).map (finInclusion h), by
    apply (mem_allocations P n _).mpr
    intro p
    obtain ⟨i, hi⟩ := (mem_allocations P m a.val).mp a.property p
    exact ⟨finInclusion h i, Finset.mem_map.mpr ⟨i, hi, rfl⟩⟩⟩

theorem pad_injective {ι : Type*} (P : Finset ι) {m n : ℕ} (h : m ≤ n) :
    Function.Injective (pad P h) := by
  intro a b hab
  apply Subtype.ext
  funext p
  have hp := congrArg (fun x : allocations P n => x.val p) hab
  change (a.val p).map (finInclusion h) = (b.val p).map (finInclusion h) at hp
  apply Finset.ext
  intro i
  constructor
  · intro hi
    have hm : finInclusion h i ∈ (b.val p).map (finInclusion h) :=
      hp ▸ Finset.mem_map.mpr ⟨i, hi, rfl⟩
    obtain ⟨j, hj, he⟩ := Finset.mem_map.mp hm
    exact (finInclusion h).injective he ▸ hj
  · intro hi
    have hm : finInclusion h i ∈ (a.val p).map (finInclusion h) :=
      hp.symm ▸ Finset.mem_map.mpr ⟨i, hi, rfl⟩
    obtain ⟨j, hj, he⟩ := Finset.mem_map.mp hm
    exact (finInclusion h).injective he ▸ hj

variable {K : Type} [Field K] [NumberField K]

/-- The actual ideal is unchanged; only the occurrence-index codomain
is embedded into the earlier fixed cap. -/
def idealPad (D : Ideal (𝓞 K)) {m n : ℕ} (h : m ≤ n) :
    idealAllocations D m → idealAllocations D n := pad (primeSupport D) h

@[simp] theorem idealPad_selection (D : Ideal (𝓞 K)) {m n : ℕ} (h : m ≤ n)
    (a : idealAllocations D m) :
    (idealPad D h a).val = padSelection h a.val := rfl

theorem idealPad_injective (D : Ideal (𝓞 K)) {m n : ℕ} (h : m ≤ n) :
    Function.Injective (idealPad D h) := pad_injective (primeSupport D) h

theorem idealPad_pair_injective (D : Ideal (𝓞 K)) {m l n : ℕ}
    (hm : m ≤ n) (hl : l ≤ n) :
    Function.Injective (fun a : idealAllocations D m × idealAllocations D l =>
      (idealPad D hm a.1, idealPad D hl a.2)) := by
  intro a b hab
  apply Prod.ext
  · exact idealPad_injective D hm (congrArg Prod.fst hab)
  · exact idealPad_injective D hl (congrArg Prod.snd hab)

end HeckeSkeleton.Moments.EngineStep.AllocationMass

#print axioms HeckeSkeleton.Moments.EngineStep.AllocationMass.idealPad_pair_injective
