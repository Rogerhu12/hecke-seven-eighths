import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocatedSubsupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PrimePowerQuotientSupport

/-!
# Genuine quotient supports on the moment's nonzero ideal type

The ideal quotient supports are lifted by their actual nonzero predicate.
The lift is a bijection on every support used here.  No multiplicity or
fiber loss is introduced when the allocated whole polynomial is passed
to MomentData's NonzeroIdeal indices.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments
open WholeAllocation AllocatedSubsupport HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

def nonzeroMomentSupport (S : Finset (Ideal (𝓞 K))) : Finset (NonzeroIdeal K) :=
  S.subtype (fun I => I ∈ nonZeroDivisors (Ideal (𝓞 K)))

@[simp] theorem mem_nonzeroMomentSupport (S : Finset (Ideal (𝓞 K)))
    (I : NonzeroIdeal K) : I ∈ nonzeroMomentSupport S ↔ I.val ∈ S :=
  Finset.mem_subtype

theorem sum_nonzeroMomentSupport {B : Type*} [AddCommMonoid B]
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ I ∈ S, I ≠ 0) (f : Ideal (𝓞 K) → B) :
    (∑ I ∈ S, f I) = ∑ I ∈ nonzeroMomentSupport S, f I.val := by
  refine Finset.sum_bij
    (fun I hI => (⟨I, mem_nonZeroDivisors_of_ne_zero (hS I hI)⟩ : NonzeroIdeal K))
    ?_ ?_ ?_ ?_
  · intro I hI
    exact Finset.mem_subtype.mpr hI
  · intro I hI J hJ he
    exact congrArg Subtype.val he
  · intro J hJ
    exact ⟨J.val, Finset.mem_subtype.mp hJ, Subtype.ext rfl⟩
  · intro I hI
    rfl

theorem sum_cartesian_nonzeroMomentSupport {P : Type*} {k : ℕ}
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset P)
    (hS₁ : ∀ I ∈ S₁, I ≠ 0) (hS₂ : ∀ I ∈ S₂, I ≠ 0)
    (C : (Ideal (𝓞 K) × Ideal (𝓞 K)) × (Fin k → P) → ℂ) :
    (∑ x ∈ childCartesianColumns S₁ S₂ S, C x) =
      ∑ y ∈ childCartesianColumns (nonzeroMomentSupport S₁) (nonzeroMomentSupport S₂) S,
        C ((y.1.1.val, y.1.2.val), y.2) := by
  simp only [childCartesianColumns, Finset.product_eq_sprod, Finset.sum_product]
  rw [sum_nonzeroMomentSupport S₁ hS₁]
  apply Finset.sum_congr rfl
  intro I _
  rw [sum_nonzeroMomentSupport S₂ hS₂]

def nonzeroQuotientMomentSupport (D : Ideal (𝓞 K)) (S : Finset (Ideal (𝓞 K))) :
    Finset (NonzeroIdeal K) := nonzeroMomentSupport (quotientSupport D S)

@[simp] theorem mem_nonzeroQuotientMomentSupport (D : Ideal (𝓞 K))
    (hD : D ≠ 0) (S : Finset (Ideal (𝓞 K))) (I : NonzeroIdeal K) :
    I ∈ nonzeroQuotientMomentSupport D S ↔ D * I.val ∈ S := by
  simp only [nonzeroQuotientMomentSupport, mem_nonzeroMomentSupport,
    mem_quotientSupport D I.val hD]

theorem occurrenceDivisor_ne_zero {k : ℕ} (D : Ideal (𝓞 K))
    (v : primeSupport D → Finset (Fin (k + 2))) (i : Fin (k + 2)) :
    occurrenceDivisor D v i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p _
  exact (support_prime p.property).ne_zero

/-- The actual allocated column is now indexed by the exact moment
ideal type; its reconstructed original coefficient remains intact. -/
theorem actual_allocated_polynomial_nonzero_subsupport {k : ℕ}
    (D : Ideal (𝓞 K)) (v : primeSupport D → Finset (Fin (k + 2)))
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (hS₁ : ∀ I ∈ S₁, I ≠ 0) (hS₂ : ∀ I ∈ S₂, I ≠ 0)
    (frozen : (Ideal (𝓞 K) × Ideal (𝓞 K)) × (Fin k → HeightOneSpectrum (𝓞 K)))
    (hfrozen : frozen ∈ pairedAllocatedColumns D v S₁ S₂ S id id HeightOneSpectrum.asIdeal)
    (C : (Ideal (𝓞 K) × Ideal (𝓞 K)) × (Fin k → HeightOneSpectrum (𝓞 K)) → ℂ) :
    (∑ x ∈ pairedAllocatedColumns D v S₁ S₂ S id id HeightOneSpectrum.asIdeal, C x) =
      ∑ y ∈ childCartesianColumns
        (nonzeroQuotientMomentSupport (occurrenceDivisor D v 0) S₁)
        (nonzeroQuotientMomentSupport (occurrenceDivisor D v (Fin.succ 0)) S₂)
        (fun j => S (selectedSlotIndex (AllocatedSubsupport.liveSlots D v) j)),
        C ((occurrenceDivisor D v 0 * y.1.1.val,
          occurrenceDivisor D v (Fin.succ 0) * y.1.2.val),
          SlotRestriction.extend (AllocatedSubsupport.liveSlots D v) frozen.2 y.2) := by
  rw [actual_allocated_polynomial_subsupport D v S₁ S₂ S frozen hfrozen C]
  exact sum_cartesian_nonzeroMomentSupport
    (quotientSupport (occurrenceDivisor D v 0) S₁)
    (quotientSupport (occurrenceDivisor D v (Fin.succ 0)) S₂)
    (fun j => S (selectedSlotIndex (AllocatedSubsupport.liveSlots D v) j))
    (quotientSupport_nonzero _ (occurrenceDivisor_ne_zero D v 0) S₁ hS₁)
    (quotientSupport_nonzero _ (occurrenceDivisor_ne_zero D v (Fin.succ 0)) S₂ hS₂)
    (fun y => C ((occurrenceDivisor D v 0 * y.1.1,
      occurrenceDivisor D v (Fin.succ 0) * y.1.2),
      SlotRestriction.extend (AllocatedSubsupport.liveSlots D v) frozen.2 y.2))

/-- The same lossless bridge for each valuation-one/six/seven branch. -/
theorem actual_error_polynomial_nonzero_subsupport {k : ℕ}
    (p : HeightOneSpectrum (𝓞 K)) (n : Fin (k + 2) → ℕ)
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (hS₁ : ∀ I ∈ S₁, I ≠ 0) (hS₂ : ∀ I ∈ S₂, I ≠ 0)
    (frozen : (Ideal (𝓞 K) × Ideal (𝓞 K)) × (Fin k → HeightOneSpectrum (𝓞 K)))
    (hfrozen : frozen ∈ AmplifierValuationSupport.pairedColumns p n S₁ S₂ S id id)
    (C : (Ideal (𝓞 K) × Ideal (𝓞 K)) × (Fin k → HeightOneSpectrum (𝓞 K)) → ℂ) :
    (∑ x ∈ AmplifierValuationSupport.pairedColumns p n S₁ S₂ S id id, C x) =
      ∑ y ∈ childCartesianColumns
        (nonzeroMomentSupport (PrimePowerQuotientSupport.primitiveQuotient p (n 0) S₁))
        (nonzeroMomentSupport (PrimePowerQuotientSupport.primitiveQuotient p (n (Fin.succ 0)) S₂))
        (fun j => (S (selectedSlotIndex (AmplifierValuationSupport.liveSlots n) j)).erase p),
        C ((p.asIdeal ^ n 0 * y.1.1.val, p.asIdeal ^ n (Fin.succ 0) * y.1.2.val),
          SlotRestriction.extend (AmplifierValuationSupport.liveSlots n) (fun _ => p) y.2) := by
  rw [PrimePowerQuotientSupport.actual_error_polynomial_quotient_subsupport
    p n S₁ S₂ S hS₁ hS₂ frozen hfrozen C]
  apply sum_cartesian_nonzeroMomentSupport
  · intro I hI
    exact quotientSupport_nonzero _ (pow_ne_zero _ p.ne_bot) S₁ hS₁ I
      (Finset.mem_filter.mp hI).1
  · intro I hI
    exact quotientSupport_nonzero _ (pow_ne_zero _ p.ne_bot) S₂ hS₂ I
      (Finset.mem_filter.mp hI).1

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_allocated_polynomial_nonzero_subsupport
#print axioms HeckeSkeleton.Moments.EngineStep.actual_error_polynomial_nonzero_subsupport

