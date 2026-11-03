import HeckeGeneral.Arithmetic.IdealTraceLattice

/-!
# Denominator-cleared global units in the actual trace integer lattice

For a fixed nonzero integer a, every global field unit u for which a*u is
integral determines a nonzero point of the same trace integer lattice.
The map is injective: the denominator and the trace embedding cannot merge
distinct units. This retains the actual unit multiplicity in later bounds
for finite orbital sums.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField
open scoped Classical nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

theorem traceEmbedding_injective : Function.Injective (traceEmbedding K) :=
  (traceToMixed K).symm.injective.comp (mixedEmbedding_injective K)

@[simp] theorem traceEmbedding_zero : traceEmbedding K 0 = 0 := by
  simp [traceEmbedding]

/-- The integrality condition is membership in the actual ring-of-integers image. -/
def IntegralMultipleUnits (a : 𝓞 K) :=
  {u : Kˣ // algebraMap (𝓞 K) K a * (u : K) ∈ (algebraMap (𝓞 K) K).range}

/-- All cleared points lie in the same lattice, not a lattice depending on u. -/
def clearedUnitTraceLatticeEmbedding (a : 𝓞 K) (ha : a ≠ 0) :
    IntegralMultipleUnits K a ↪
      {l : traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) // l ≠ 0} where
  toFun u := by
    have hm : traceEmbedding K (algebraMap (𝓞 K) K a * (u.val : K)) ∈
        traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) := by
      apply (traceEmbedding_mem_traceIdealLattice K 1).mpr
      exact (FractionalIdeal.mem_one_iff (𝓞 K)⁰).mpr u.property
    refine ⟨⟨traceEmbedding K (algebraMap (𝓞 K) K a * (u.val : K)), hm⟩, ?_⟩
    intro hz
    have he : traceEmbedding K (algebraMap (𝓞 K) K a * (u.val : K)) = 0 :=
      congrArg (fun l : traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =>
        (l : mixedEmbedding.euclidean.mixedSpace K)) hz
    have halg : algebraMap (𝓞 K) K a ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr ha
    apply mul_ne_zero halg u.val.ne_zero
    apply traceEmbedding_injective K
    simpa only [traceEmbedding_zero] using he
  inj' := by
    intro u v huv
    apply Subtype.ext
    apply Units.ext
    have halg : algebraMap (𝓞 K) K a ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr ha
    apply mul_left_cancel₀ halg
    apply traceEmbedding_injective K
    exact congrArg (fun l :
      {l : traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) // l ≠ 0} =>
        ((l.val : traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) :
          mixedEmbedding.euclidean.mixedSpace K)) huv

@[simp] theorem clearedUnitTraceLatticeEmbedding_val
    (a : 𝓞 K) (ha : a ≠ 0) (u : IntegralMultipleUnits K a) :
    (((clearedUnitTraceLatticeEmbedding K a ha u).val :
      traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) :
        mixedEmbedding.euclidean.mixedSpace K) =
      traceEmbedding K (algebraMap (𝓞 K) K a * (u.val : K)) := rfl

end HeckeGeneral.Arithmetic
