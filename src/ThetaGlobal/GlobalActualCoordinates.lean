import ThetaGlobal.GlobalActualReindex
import ThetaGlobal.GlobalIdealCoordinates
import HeckeAxiom.ArithmeticAdapter

/-!
# Reconstruction in the repository's full ReflectionIndex

Numerical supported coordinates are converted to actual exterior ideals
and split into the two independent active sets.  All support, squarefree,
digit and coprimality fields of `ReflectionIndex` are proved here.
The coefficient dictionary supplies the local valuation restrictions;
there is no global bijection hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GlobalActualCoordinates

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped Classical

variable {K : Type} [Field K] [NumberField K] (A : SArithmeticData K)
local notation "S" => (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
variable (d : MarkedDatum K ((A.Sf : Set (HeightOneSpectrum (𝓞 K)))))

def allowed : Set (ExteriorPrime K S) := ↑(frozenPrimes K S d ∪ d.marks)

def frozenPart (b : GlobalIdealCoordinates.Coordinates A) : Finset (ExteriorPrime K S) :=
  b.active.filter (fun p => p ∈ frozenPrimes K S d)

def markedPart (b : GlobalIdealCoordinates.Coordinates A) : Finset (ExteriorPrime K S) :=
  b.active.filter (fun p => p ∈ d.marks)

theorem union_parts (b : GlobalIdealCoordinates.Coordinates A)
    (ha : (b.active : Set (ExteriorPrime K S)) ⊆ allowed A d) :
    frozenPart A d b ∪ markedPart A d b = b.active := by
  ext p
  simp only [frozenPart, markedPart, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro h
    rcases Finset.mem_union.mp (ha h) with hf | hm
    · exact Or.inl ⟨h, hf⟩
    · exact Or.inr ⟨h, hm⟩

theorem exponent_exteriorEquiv (I : A.Exterior) (p : ExteriorPrime K S) :
    primeExponents (HeckeAxiom.exteriorEquiv A I).val p.val =
      GlobalIdealCoordinates.exponent A I p := rfl

def indexOfCoordinates (b : GlobalIdealCoordinates.Coordinates A)
    (hb : GlobalFrequency.Supported (GlobalIndexSupport.mandatory K S d) (b.toBranch A))
    (ha : (b.active : Set (ExteriorPrime K S)) ⊆ allowed A d)
    (ε : SixthUnitClasses K S) : ReflectionIndex K S d where
  activeMarks := markedPart A d b
  marks_subset := by intro p hp; exact (Finset.mem_filter.mp hp).2
  activeFrozen := frozenPart A d b
  frozen_subset := by intro p hp; exact (Finset.mem_filter.mp hp).2
  nonzero_active := by
    intro p hp hj
    exact Finset.mem_filter.mpr ⟨hb.mandatory_active ⟨hp, hj⟩, hp⟩
  numeratorFrozen := HeckeAxiom.exteriorEquiv A b.a
  frozen_support := by
    intro p hp
    have he : GlobalIdealCoordinates.exponent A b.a p ≠ 0 :=
      (GlobalIndexSupport.mem_exteriorSupport K S _ p).mp hp
    have hpactive : p ∈ b.active := by
      by_contra hn
      exact he (hb.a_outside p hn)
    have hpmandatory : p ∈ GlobalIndexSupport.mandatory K S d := by
      by_contra hn
      exact he (hb.optional_zero p hpactive hn)
    exact Finset.mem_filter.mpr ⟨hpactive, hpmandatory.1⟩
  frozen_digits := hb.a_digits
  n := HeckeAxiom.exteriorEquiv A b.n
  n_coprime := by
    apply GlobalIndexSupport.coprime_of_exponent_zeros K S
    intro p hp
    apply hb.n_active p
    have hpu : p ∈ frozenPart A d b ∪ markedPart A d b := by
      by_contra hn
      have hf : p ∉ frozenPart A d b := fun h => hn (Finset.mem_union_left _ h)
      have hm : p ∉ markedPart A d b := fun h => hn (Finset.mem_union_right _ h)
      apply hp
      change primeExponents ((primeSetIdeal K S (frozenPart A d b)).val *
        (primeSetIdeal K S (markedPart A d b)).val) p.val = 0
      simp only [primeExponents_mul, Finsupp.add_apply,
        GlobalIndexSupport.exponent_primeSetIdeal,
        GlobalIndexSupport.exponent_primeSetIdeal, if_neg hf, if_neg hm]
    rwa [union_parts A d b ha] at hpu
  c := HeckeAxiom.exteriorEquiv A b.c
  c_squarefree := GlobalIdealCoordinates.coordinates_squarefree A _ b hb
  c_coprime := by
    apply GlobalIndexSupport.coprime_of_exponent_zeros K S
    intro p hp
    apply hb.c_active p
    have hf : p ∈ frozenPart A d b := by
      by_contra hn
      exact hp (by rw [GlobalIndexSupport.exponent_primeSetIdeal, if_neg hn])
    exact (Finset.mem_filter.mp hf).1
  unitSector := ε

theorem branch_indexOfCoordinates (b : GlobalIdealCoordinates.Coordinates A)
    (hb : GlobalFrequency.Supported (GlobalIndexSupport.mandatory K S d) (b.toBranch A))
    (ha : (b.active : Set (ExteriorPrime K S)) ⊆ allowed A d)
    (ε : SixthUnitClasses K S) :
    GlobalIndexSupport.branch K S d (indexOfCoordinates A d b hb ha ε) = b.toBranch A := by
  apply GlobalFrequency.Branch.ext
  · exact congrArg (fun t : Finset (ExteriorPrime K S) => (↑t : Set (ExteriorPrime K S)))
      (union_parts A d b ha)
  · rfl
  · rfl
  · rfl

/-- All proof fields of the actual enlarged index have been discharged
from the local support conditions and the numerical reconstruction. -/
theorem exists_index_with_valuations (v : ExteriorPrime K S → ℤ)
    (hv : GlobalFrequencyReconstruction.LocalSupport
      (GlobalIndexSupport.mandatory K S d) (allowed A d) v)
    (hfinite : (Function.support v).Finite) (ε : SixthUnitClasses K S) :
    ∃ i : ReflectionIndex K S d,
      GlobalFrequency.Supported (GlobalIndexSupport.mandatory K S d)
        (GlobalIndexSupport.branch K S d i) ∧
      GlobalFrequency.valuation (GlobalIndexSupport.branch K S d i) = v ∧
      i.unitSector = ε := by
  have hallowed : (allowed A d).Finite := (frozenPrimes K S d ∪ d.marks).finite_toSet
  obtain ⟨b, hb, _⟩ := GlobalIdealCoordinates.existsUnique_coordinates A
    (GlobalIndexSupport.mandatory K S d) (allowed A d) v hv hallowed hfinite
  have ha : (b.active : Set (ExteriorPrime K S)) ⊆ allowed A d := by
    intro p hp
    rcases (GlobalFrequency.active_iff_mandatory_or_negative
      (GlobalIndexSupport.mandatory K S d) (b.toBranch A) hb.1 p).mp hp with hm | hn
    · exact hv.mandatory_allowed hm
    · exact hv.negative_allowed p (by rwa [hb.2] at hn)
  refine ⟨indexOfCoordinates A d b hb.1 ha ε, ?_, ?_, rfl⟩
  · rw [branch_indexOfCoordinates]
    exact hb.1
  · rw [branch_indexOfCoordinates]
    exact hb.2

/-- Coverage of the actual rational frequency quotient. Only the local
valuation support conditions are used; all ideal and unit coordinates
are constructed. -/
theorem exists_index_with_frequency (D : ThetaArithmeticData K S) (x : Kˣ)
    (hv : GlobalFrequencyReconstruction.LocalSupport
      (GlobalIndexSupport.mandatory K S d) (allowed A d)
      (fun p => ThetaBranch.order p.val x + 2 * (primeExponents d.moving.val p.val : ℤ))) :
    ∃ i : ReflectionIndex K S d,
      GlobalFrequency.Supported (GlobalIndexSupport.mandatory K S d)
        (GlobalIndexSupport.branch K S d i) ∧
      GlobalActualReindex.frequency A D d i = QuotientGroup.mk x := by
  have hfinite : (Function.support (fun p : ExteriorPrime K S =>
      ThetaBranch.order p.val x + 2 * (primeExponents d.moving.val p.val : ℤ))).Finite :=
    GlobalIdealCoordinates.finite_normalized_orders A
      ((HeckeAxiom.exteriorEquiv A).symm d.moving) x
  obtain ⟨i₀, hi₀, hv₀, _⟩ := exists_index_with_valuations A d _ hv hfinite 1
  let y := GlobalActualReindex.bodyRepresentative A D d i₀
  have horders (p : ThetaBranch.ExteriorPrime A) :
      ThetaBranch.order p.val x = ThetaBranch.order p.val y := by
    rw [GlobalActualReindex.order_bodyRepresentative, congrFun hv₀ p]
    ring
  obtain ⟨ε, hε⟩ := GlobalUnitCoordinates.exists_unit_sector A
    (GlobalActualReindex.unitRepresentatives A) x y horders
  let i : ReflectionIndex K S d := {i₀ with unitSector := ε}
  refine ⟨i, hi₀, ?_⟩
  simp only [GlobalActualReindex.frequency, GlobalActualReindex.representative_eq,
    GlobalUnitCoordinates.frequency, GlobalActualReindex.unitRepresentatives,
    frequencyUnit, GlobalActualReindex.bodyRepresentative, activeFrozenIdeal,
    activeMarkedIdeal, i, y] at hε ⊢
  exact hε

end ThetaGlobal.GlobalActualCoordinates
