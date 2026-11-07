module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bProfiles

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual finite plain support survives both occurrence extractions

The mask only removes terms already zero. An extracted plain ideal is
the original witness's exact supported part; multiplication by an ideal
outside the deleted primes reconstructs the same fibre. These are
single-ideal support statements, before any exceptional sum or bound.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

def Avoids (I : Ideal (𝓞 K)) (excluded : Finset (Ideal (𝓞 K))) : Prop :=
  ∀ Q ∈ excluded, IsCoprime I Q

structure PlainSupportData (weight : Bool → HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (carrier excluded : Finset (Ideal (𝓞 K))) : Prop where
  nonzero : ∀ I ∈ carrier, I ≠ 0
  avoids : ∀ I ∈ carrier, Avoids I excluded
  mem_of_weight : ∀ r (I : HeckeGeneral.Analysis.NonzeroIdeal K), weight r I ≠ 0 →
    Avoids I.val excluded → I.val ∈ carrier

namespace PlainSupportData

variable {weight : Bool → HeckeGeneral.Analysis.NonzeroIdeal K → ℂ}
variable {carrier excluded : Finset (Ideal (𝓞 K))}
variable (d : PlainSupportData weight carrier excluded)

def congrWeight (other : Bool → HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (h : ∀ r I, other r I = weight r I) : PlainSupportData other carrier excluded where
  nonzero := d.nonzero
  avoids := d.avoids
  mem_of_weight r I hI := d.mem_of_weight r I ((h r I) ▸ hI)

/-- The extracted divisor is supplied by its original finite witness,
not by a new support choice. -/
def extract (deleted : Finset (Ideal (𝓞 K)))
    (hdeleted : ∀ Q ∈ deleted, Prime Q)
    (D : HeckeGeneral.Analysis.NonzeroIdeal K) (witness : Ideal (𝓞 K))
    (hwitness : witness ∈ carrier) (hextract : supportExtract witness deleted = D.val) :
    PlainSupportData (fun r I => weight r (D * I))
      (SupportCartesian.plainResidual carrier deleted D.val) (excluded ∪ deleted) where
  nonzero I hI := by
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    exact supportResidual_ne_zero J deleted
  avoids I hI := by
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    have hJmem : J ∈ carrier := (Finset.mem_filter.mp hJ).1
    have hdiv : supportResidual J deleted ∣ J := by
      refine ⟨supportExtract J deleted, ?_⟩
      exact (support_reconstruct J (d.nonzero J hJmem) deleted).symm.trans (mul_comm _ _)
    intro Q hQ
    rcases Finset.mem_union.mp hQ with hQ | hQ
    · exact (d.avoids J hJmem Q hQ).of_isCoprime_of_dvd_left hdiv
    · exact (outside_iff_coprime deleted hdeleted
        ⟨supportResidual J deleted, supportResidual_ne_zero J deleted⟩).mp
        (residual_outside deleted hdeleted J) Q hQ
  mem_of_weight r I hweight hI := by
    have hDdiv : D.val ∣ witness := by
      refine ⟨supportResidual witness deleted, ?_⟩
      rw [← hextract]
      exact (support_reconstruct witness (d.nonzero witness hwitness) deleted).symm
    have hDold : Avoids D.val excluded := fun Q hQ =>
      (d.avoids witness hwitness Q hQ).of_isCoprime_of_dvd_left hDdiv
    have hIold : Avoids I.val excluded := fun Q hQ => hI Q (Finset.mem_union_left _ hQ)
    have hInew : Avoids I.val deleted := fun Q hQ => hI Q (Finset.mem_union_right _ hQ)
    have hm : (D * I).val ∈ carrier :=
      d.mem_of_weight r (D * I) hweight
        (fun Q hQ => (hDold Q hQ).mul_left (hIold Q hQ))
    have hDsmooth : HeckePort.IdealMobiusDivisorSum.primeSupport D.val ⊆ deleted := by
      rw [← hextract]
      exact extract_smooth deleted witness
    have hIoutside : outside deleted I.val :=
      (outside_iff_coprime deleted hdeleted
        ⟨I.val, nonZeroDivisors.coe_ne_zero I⟩).mpr hInew
    have hsplit := split_product deleted hdeleted
      (⟨⟨D.val, nonZeroDivisors.coe_ne_zero D⟩, hDsmooth⟩ : SmoothIdeal deleted)
      (⟨⟨I.val, nonZeroDivisors.coe_ne_zero I⟩, hIoutside⟩ : OutsideIdeal deleted)
    exact Finset.mem_image.mpr
      ⟨(D * I).val, Finset.mem_filter.mpr ⟨hm, hsplit.1⟩, hsplit.2⟩

include d

/-- The final independent allocation's plain divisor belongs to the
same support and hence avoids every previously deleted prime. -/
theorem divisor_avoids (D J : Ideal (𝓞 K)) (hJ : J ∈ carrier) (hD : D ∣ J) :
    Avoids D excluded :=
  fun Q hQ => (d.avoids J hJ Q hQ).of_isCoprime_of_dvd_left hD

end PlainSupportData
end HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.PlainSupportData.extract
