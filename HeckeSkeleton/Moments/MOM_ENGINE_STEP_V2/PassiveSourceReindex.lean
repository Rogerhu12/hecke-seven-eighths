import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveSource

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Exact ideal reindexing of the extracted source

The original child columns use nonzero ideals, whereas residual
allocations use ideals in the image carrier. The forgetful map is
injective, preserves every prime occurrence, and is onto precisely that
carrier. The source coefficient and both Fourier locations therefore
transport without a multiplicity or a norm factor.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

namespace PassiveAllocation

abbrev TypedColumn (K : Type) [Field K] [NumberField K] (k : ℕ) :=
  (NonzeroIdeal K × NonzeroIdeal K) × (Fin k → HeightOneSpectrum (𝓞 K))

def typedColumns (B : Carrier K k) : Finset (TypedColumn K k) :=
  childCartesianColumns (B.plain false) (B.plain true) B.slots

def toIdealColumn (i : TypedColumn K k) : AllocationColumn K k :=
  ((i.1.1.val, i.1.2.val), i.2)

theorem toIdealColumn_injective : Function.Injective (toIdealColumn (K := K) (k := k)) := by
  intro a b hab
  apply Prod.ext
  · apply Prod.ext
    · exact Subtype.ext (congrArg (fun i : AllocationColumn K k => i.1.1) hab)
    · exact Subtype.ext (congrArg (fun i : AllocationColumn K k => i.1.2) hab)
  · exact congrArg (fun i : AllocationColumn K k => i.2) hab

theorem carrierColumns_eq_image (B : Carrier K k) :
    carrierColumns B = (typedColumns B).image toIdealColumn := by
  ext i
  constructor
  · intro hi
    obtain ⟨hp, hs⟩ := Finset.mem_product.mp hi
    obtain ⟨hl, hr⟩ := Finset.mem_product.mp hp
    obtain ⟨I, hI, hIe⟩ := Finset.mem_image.mp hl
    obtain ⟨J, hJ, hJe⟩ := Finset.mem_image.mp hr
    refine Finset.mem_image.mpr ⟨((I, J), i.2), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hI, hJ⟩, hs⟩
    · exact Prod.ext (Prod.ext hIe hJe) rfl
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨hp, hs⟩ := Finset.mem_product.mp hj
    obtain ⟨hl, hr⟩ := Finset.mem_product.mp hp
    exact Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨j.1.1, hl, rfl⟩,
          Finset.mem_image.mpr ⟨j.1.2, hr, rfl⟩⟩, hs⟩

theorem joint_carrierColumns (B : Carrier K k)
    (coefficient : AllocationColumn K k → ℂ)
    (location : AllocationColumn K k → EngineParameter) (ξ : EngineParameter) :
    jointFourierColumn (carrierColumns B) coefficient location ξ =
      jointFourierColumn (typedColumns B)
        (fun i => coefficient (toIdealColumn i))
        (fun i => location (toIdealColumn i)) ξ := by
  unfold jointFourierColumn
  rw [carrierColumns_eq_image, Finset.sum_image]
  intro a _ b _ hab
  exact toIdealColumn_injective hab

end PassiveAllocation

namespace PassiveSource

variable {A : SArithmeticData K} {σ : K →+* ℂ} {H : Type*}
variable (s : ActualAllocatedSource A EngineParameter H k)

/-- The exact child carrier of the old second allocation, prior to
restoring any smooth support or removing any residual mask. -/
def oldCarrier : PassiveAllocation.Carrier K s.allocation.keep.card where
  plain side := if side then s.allocation.childPlain₂ else s.allocation.childPlain₁
  slots := s.allocation.childSlots

@[simp] theorem oldCarrier_typedColumns :
    PassiveAllocation.typedColumns (oldCarrier s) = s.allocation.childColumns := rfl

/-- This equality fixes the starting point for support restoration.
It contains the old restricted characters and the old exact carrier,
so no paid-mask identity is assumed by this change of index type. -/
theorem energy_eq_oldCarrier (ξ : EngineParameter) :
    s.energy (σ := σ) ξ =
      jointColumnEnergy s.rows (PassiveAllocation.carrierColumns (oldCarrier s))
        (s.childWeight (σ := σ))
        (paidCoefficient (σ := σ) s
          (fun h => (s.characters h).restrictSlots s.allocation.keep))
        (paidLocation s) ξ := by
  rw [energy_eq_extracted]
  unfold jointColumnEnergy
  apply Finset.sum_congr rfl
  intro h _
  have hp :
      jointFourierColumn (PassiveAllocation.carrierColumns (oldCarrier s))
        (paidCoefficient (σ := σ) s
          (fun h => (s.characters h).restrictSlots s.allocation.keep) h)
        (paidLocation s h) ξ =
      jointFourierColumn s.allocation.childColumns
        (extractedCoefficient (σ := σ) s h) (extractedLocation s h) ξ := by
    simpa only [oldCarrier_typedColumns, paidCoefficient, paidLocation,
      extractedCoefficient, extractedLocation, rawSourceCoefficient, rawSourceLocation,
      PassiveAllocation.toIdealColumn, sourceMomentIdeal_coe] using
      (PassiveAllocation.joint_carrierColumns (oldCarrier s)
        (paidCoefficient (σ := σ) s
          (fun h => (s.characters h).restrictSlots s.allocation.keep) h)
        (paidLocation s h) ξ)
  rw [hp]

end PassiveSource
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveSource.energy_eq_oldCarrier
