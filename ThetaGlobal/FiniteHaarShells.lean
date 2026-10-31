import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Decomposing actual multiplicative Haar into valuation shells

This is a purely geometric measure theorem.  A uniformizer and the embedded
integral-unit group give all valuation shells.  Pulling the *given* Haar
measure back to the integral units, and then translating it by all integer
powers of the uniformizer, reconstructs that same Haar measure.  No unit
volume is set to one and no Mellin convergence statement is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.FiniteHaarShells

open MeasureTheory MeasureTheory.Measure Set
open scoped BigOperators

variable {G U : Type*} [CommGroup G] [MeasurableSpace G]
  [MeasurableMul G] [MeasurableInv G] [MeasurableSpace U]

/-- A valuation fiber, with additive indexing convention `ord(π) = 1`. -/
def valuationFiber (e : G →* Multiplicative ℤ) (k : ℤ) : Set G :=
  {x | e x = Multiplicative.ofAdd k}

/-- The unit-shell measure is induced by the fixed multiplicative Haar,
including its original normalization. -/
def unitMeasure (ν : Measure G) (ι : U → G) : Measure U := ν.comap ι

theorem unitMeasure_finite (ν : Measure G) (ι : U → G)
    (hι : MeasurableEmbedding ι) (hfinite : ν (Set.range ι) < ⊤) :
    IsFiniteMeasure (unitMeasure ν ι) := by
  constructor
  change ν.comap ι Set.univ < ⊤
  rw [hι.comap_apply, Set.image_univ]
  exact hfinite

private theorem order_uniformizer_zpow (e : G →* Multiplicative ℤ)
    (π : G) (hπ : e π = Multiplicative.ofAdd (1 : ℤ)) (k : ℤ) :
    e (π ^ k) = Multiplicative.ofAdd k := by
  rw [map_zpow, hπ, ← ofAdd_zsmul]
  simp

/-- A translated unit Haar measure is exactly Haar restricted to the
corresponding valuation fiber. -/
theorem map_unitMeasure_shell (ν : Measure G) [IsMulLeftInvariant ν]
    (e : G →* Multiplicative ℤ) (π : G)
    (hπ : e π = Multiplicative.ofAdd (1 : ℤ))
    (ι : U → G) (hι : MeasurableEmbedding ι)
    (hrange : Set.range ι = valuationFiber e 0) (k : ℤ) :
    Measure.map (fun u => π ^ k * ι u) (unitMeasure ν ι) =
      ν.restrict (valuationFiber e k) := by
  have hpre : (fun x : G => π ^ k * x) ⁻¹' valuationFiber e k =
      valuationFiber e 0 := by
    ext x
    change e (π ^ k * x) = Multiplicative.ofAdd k ↔ e x = 1
    simp only [map_mul, order_uniformizer_zpow e π hπ k, mul_eq_left]
  calc
    Measure.map (fun u => π ^ k * ι u) (unitMeasure ν ι) =
        (Measure.map ι (unitMeasure ν ι)).map (fun x => π ^ k * x) := by
      rw [Measure.map_map (measurable_const_mul _) hι.measurable]
      rfl
    _ = (ν.restrict (valuationFiber e 0)).map (fun x => π ^ k * x) := by
      rw [unitMeasure, hι.map_comap, hrange]
    _ = (ν.map (fun x => π ^ k * x)).restrict (valuationFiber e k) := by
      have he := (MeasurableEquiv.mulLeft (π ^ k)).restrict_map ν (valuationFiber e k)
      change (ν.map (fun x => π ^ k * x)).restrict (valuationFiber e k) =
        (ν.restrict ((fun x => π ^ k * x) ⁻¹' valuationFiber e k)).map
          (fun x => π ^ k * x) at he
      rw [hpre] at he
      exact he.symm
    _ = ν.restrict (valuationFiber e k) := by rw [map_mul_left_eq_self]

/-- Every point has exactly one integer valuation.  Summing Haar restricted
to those measurable fibers recovers the original measure. -/
theorem sum_restrict_valuationFiber (ν : Measure G)
    (e : G →* Multiplicative ℤ)
    (hmeas : ∀ k : ℤ, MeasurableSet (valuationFiber e k)) :
    Measure.sum (fun k : ℤ => ν.restrict (valuationFiber e k)) = ν := by
  have hdisjoint : Pairwise (fun k l => Disjoint (valuationFiber e k) (valuationFiber e l)) := by
    intro k l hkl
    rw [Set.disjoint_left]
    intro x hx hy
    apply hkl
    have h := hx.symm.trans hy
    exact Multiplicative.ofAdd.injective h
  have hcover : (⋃ k : ℤ, valuationFiber e k) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨Multiplicative.toAdd (e x), rfl⟩
  rw [← Measure.restrict_iUnion hdisjoint hmeas, hcover, Measure.restrict_univ]

/-- The Haar shell identity used by the Mellin integration theorem.  Its
inputs are valuation, uniformizer, unit embedding, and left invariance. -/
theorem haar_eq_sum_shells (ν : Measure G) [IsMulLeftInvariant ν]
    (e : G →* Multiplicative ℤ) (π : G)
    (hπ : e π = Multiplicative.ofAdd (1 : ℤ))
    (ι : U → G) (hι : MeasurableEmbedding ι)
    (hrange : Set.range ι = valuationFiber e 0)
    (hmeas : ∀ k : ℤ, MeasurableSet (valuationFiber e k)) :
    ν = Measure.sum (fun k : ℤ =>
      Measure.map (fun u => π ^ k * ι u) (unitMeasure ν ι)) := by
  simp_rw [map_unitMeasure_shell ν e π hπ ι hι hrange]
  exact (sum_restrict_valuationFiber ν e hmeas).symm

end ThetaGlobal.FiniteHaarShells

#print axioms ThetaGlobal.FiniteHaarShells.map_unitMeasure_shell
#print axioms ThetaGlobal.FiniteHaarShells.haar_eq_sum_shells
