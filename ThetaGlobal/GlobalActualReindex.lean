import ThetaGlobal.GlobalActualFrequency
import ThetaGlobal.GlobalIndexSupport
import ThetaGlobal.GlobalUnitCoordinates
import DedekindZetaZeroFree.Arithmetic.Ideals.SIntegerLocalization.GeneratorValuation

/-!
# Injectivity of the actual reflected index on nonzero support

The field representative is the literal numerator and denominator used
by `ReflectionIndex`.  Its exterior orders recover all ideal coordinates
and both active sets; the remaining rational sixth-power class recovers
the stored unit sector.  No frequency bijection is an input.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GlobalActualReindex

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] (A : SArithmeticData K)

local notation "S" => (A.Sf : Set (HeightOneSpectrum (𝓞 K)))

variable (D : ThetaArithmeticData K ((A.Sf : Set (HeightOneSpectrum (𝓞 K))))) (d : MarkedDatum K ((A.Sf : Set (HeightOneSpectrum (𝓞 K)))))

def unitRepresentatives : ThetaBranch.UnitRepresentatives A where
  representative := Quotient.out
  represents := Quotient.out_eq

def frequency (i : ReflectionIndex K S d) : ThetaReflectionData.Frequency A :=
  QuotientGroup.mk (GlobalActualFrequency.representative K S D d i)

def bodyRepresentative (i : ReflectionIndex K S d) : Kˣ :=
  GlobalActualFrequency.generatorUnit K S D i.numeratorFrozen *
    GlobalActualFrequency.generatorUnit K S D i.c *
    GlobalActualFrequency.generatorUnit K S D i.n ^ 3 *
    GlobalActualFrequency.generatorUnit K S D d.moving ^ (-2 : ℤ) *
    GlobalActualFrequency.generatorUnit K S D (activeFrozenIdeal K S d i) ^ (-2 : ℤ) *
    GlobalActualFrequency.generatorUnit K S D (activeMarkedIdeal K S d i) ^ (-2 : ℤ)

theorem representative_eq (i : ReflectionIndex K S d) :
    GlobalActualFrequency.representative K S D d i =
      (frequencyUnit K S d i).val * bodyRepresentative A D d i := by
  simp only [GlobalActualFrequency.representative, bodyRepresentative, mul_assoc]

private theorem order_mul (p : HeightOneSpectrum (𝓞 K)) (x y : Kˣ) :
    ThetaBranch.order p (x * y) = ThetaBranch.order p x + ThetaBranch.order p y := by
  simp only [ThetaBranch.order, Units.val_mul, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).mpr x.ne_zero)
    ((Valuation.ne_zero_iff _).mpr y.ne_zero), neg_add]

private theorem order_zpow (p : HeightOneSpectrum (𝓞 K)) (x : Kˣ) (n : ℤ) :
    ThetaBranch.order p (x ^ n) = n * ThetaBranch.order p x := by
  simp only [ThetaBranch.order, Units.val_zpow_eq_zpow_val, map_zpow₀,
    WithZero.log_zpow, smul_eq_mul]
  ring

private theorem order_pow (p : HeightOneSpectrum (𝓞 K)) (x : Kˣ) (n : ℕ) :
    ThetaBranch.order p (x ^ n) = (n : ℤ) * ThetaBranch.order p x := by
  rw [← zpow_natCast, order_zpow]

theorem order_generator (I : ExteriorIdeal K S) (p : ExteriorPrime K S) :
    ThetaBranch.order p.val (GlobalActualFrequency.generatorUnit K S D I) =
      (primeExponents I.val p.val : ℤ) := by
  have hv := SIntegerLocalization.generator_valuation A.Sf I.val.val
    (nonZeroDivisors.coe_ne_zero I.val) (D.generator I) (D.generator_ne_zero I)
    (D.generator_span I) p.val p.property
  change -WithZero.log (p.val.valuation K (D.generator I : K)) = _
  simp only [hv, WithZero.log_exp, neg_neg] <;> rfl

theorem order_representative (i : ReflectionIndex K S d) (p : ExteriorPrime K S) :
    ThetaBranch.order p.val (GlobalActualFrequency.representative K S D d i) =
      GlobalFrequency.valuation (GlobalIndexSupport.branch K S d i) p -
        2 * (primeExponents d.moving.val p.val : ℤ) := by
  have hu : ThetaBranch.order p.val (frequencyUnit K S d i).val = 0 := by
    simp [ThetaBranch.order, (frequencyUnit K S d i).property p.val p.property]
  simp only [GlobalActualFrequency.representative, order_mul, order_zpow,
    order_pow, hu, order_generator, zero_add, activeFrozenIdeal, activeMarkedIdeal,
    GlobalIndexSupport.exponent_primeSetIdeal]
  have hd := Finset.disjoint_left.mp (GlobalIndexSupport.marks_disjoint_frozen K S d)
  unfold GlobalFrequency.valuation GlobalIndexSupport.branch
  by_cases hf : p ∈ i.activeFrozen
  · have hm : p ∉ i.activeMarks := fun h => hd (i.marks_subset h) (i.frozen_subset hf)
    simp [hf, hm]
    ring
  · by_cases hm : p ∈ i.activeMarks <;> simp [hf, hm] <;> ring

theorem order_bodyRepresentative (i : ReflectionIndex K S d) (p : ExteriorPrime K S) :
    ThetaBranch.order p.val (bodyRepresentative A D d i) =
      GlobalFrequency.valuation (GlobalIndexSupport.branch K S d i) p -
        2 * (primeExponents d.moving.val p.val : ℤ) := by
  have h := order_representative A D d i p
  rw [representative_eq, order_mul] at h
  have hu : ThetaBranch.order p.val (frequencyUnit K S d i).val = 0 := by
    simp [ThetaBranch.order, (frequencyUnit K S d i).property p.val p.property]
  simpa only [hu, zero_add] using h

/-- Branch equality leaves only the unit sector.  Replacing that field
does not change any ideal, phase exponent, or finite active set. -/
theorem index_eq_of_frequency_eq (θ : HeckeCharacter K)
    (i j : ReflectionIndex K S d)
    (hi : ReflectedArithmetic.reflectedCoefficient K S D d i θ ≠ 0)
    (hj : ReflectedArithmetic.reflectedCoefficient K S D d j θ ≠ 0)
    (h : frequency A D d i = frequency A D d j) : i = j := by
  have hv : GlobalFrequency.valuation (GlobalIndexSupport.branch K S d i) =
      GlobalFrequency.valuation (GlobalIndexSupport.branch K S d j) := by
    funext p
    have ho := ThetaBranch.CanonicalCoordinateProof.order_eq_of_frequency_eq A
      (GlobalActualFrequency.representative K S D d i)
      (GlobalActualFrequency.representative K S D d j) h p
    rw [order_representative, order_representative] at ho
    omega
  have hb := GlobalFrequency.supported_valuation_injective
    (GlobalIndexSupport.mandatory K S d) _ _
    (GlobalIndexSupport.supported K S D d i θ hi)
    (GlobalIndexSupport.supported K S D d j θ hj) hv
  let i' : ReflectionIndex K S d := {i with unitSector := j.unitSector}
  have he : i' = j := GlobalIndexSupport.index_eq_of_branch_unit K S d i' j hb rfl
  have hf : frequency A D d i = frequency A D d i' :=
    h.trans (congrArg (frequency A D d) he).symm
  let y : Kˣ :=
    GlobalActualFrequency.generatorUnit K S D i.numeratorFrozen *
    GlobalActualFrequency.generatorUnit K S D i.c *
    GlobalActualFrequency.generatorUnit K S D i.n ^ 3 *
    GlobalActualFrequency.generatorUnit K S D d.moving ^ (-2 : ℤ) *
    GlobalActualFrequency.generatorUnit K S D (activeFrozenIdeal K S d i) ^ (-2 : ℤ) *
    GlobalActualFrequency.generatorUnit K S D (activeMarkedIdeal K S d i) ^ (-2 : ℤ)
  have hu : i.unitSector = j.unitSector := by
    apply GlobalUnitCoordinates.frequency_injective A (unitRepresentatives A) y
    simp only [frequency, GlobalActualFrequency.representative,
      GlobalUnitCoordinates.frequency, unitRepresentatives, frequencyUnit,
      activeFrozenIdeal, activeMarkedIdeal, i', y, mul_assoc] at hf ⊢
    exact hf
  exact GlobalIndexSupport.index_eq_of_branch_unit K S d i j hb hu

/-- The exact map needed for support-level `tsum` reindexing.  The
overlarge raw index is retained in the statement of marked reflection. -/
theorem frequency_injective_on_support (θ : HeckeCharacter K) :
    Set.InjOn (frequency A D d)
      (Function.support (fun i => ReflectedArithmetic.reflectedCoefficient K S D d i θ)) := by
  intro i hi j hj h
  exact index_eq_of_frequency_eq A D d θ i j hi hj h

end ThetaGlobal.GlobalActualReindex
