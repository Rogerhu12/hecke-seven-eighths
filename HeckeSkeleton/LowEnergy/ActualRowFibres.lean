import HeckeSkeleton.LowEnergy.ActualReflection
import HeckeSkeleton.LowEnergy.PowerfulRowAssembly

/-!
# Exact residual-row fibres of actual exterior ideals

Fixing the powerful part makes the residual row map injective.  Thus the
finite row energy on each fibre is an exact energy over actual squarefree
ideals, with the physical cutoff divided by the powerful norm.  No row
multiplicity or quotient-row character is introduced.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.ActualRowFibres

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.IdealRows HeckeSkeleton.LowEnergy.ActualReflection
open scoped Classical BigOperators NumberField nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem residual_injective_on_fibre (F : ExteriorIdeal K S) :
    Set.InjOn (exteriorResidualPart K S)
      {I : ExteriorIdeal K S | exteriorPowerfulPart K S I = F} := by
  intro I hI J hJ hres
  calc
    I = exteriorMul K S (exteriorResidualPart K S I) (exteriorPowerfulPart K S I) :=
      (exterior_residual_powerful_decomposition K S I).symm
    _ = exteriorMul K S (exteriorResidualPart K S J) (exteriorPowerfulPart K S J) := by
      rw [hI, hJ, hres]
    _ = J := exterior_residual_powerful_decomposition K S J

def powerfulFibre (R : Finset (ExteriorIdeal K S)) (F : ExteriorIdeal K S) :
    Finset (ExteriorIdeal K S) := R.filter (fun I => exteriorPowerfulPart K S I = F)

def residualFibre (R : Finset (ExteriorIdeal K S)) (F : ExteriorIdeal K S) :
    Finset (ExteriorIdeal K S) := (powerfulFibre K S R F).image (exteriorResidualPart K S)

/-- The inverse on a fixed powerful fibre is the literal product `kF`. -/
theorem residual_fibre_reconstruction (R : Finset (ExteriorIdeal K S))
    (F I : ExteriorIdeal K S) (hI : I ∈ powerfulFibre K S R F) :
    exteriorMul K S (exteriorResidualPart K S I) F = I := by
  have hf := (Finset.mem_filter.mp hI).2
  simpa only [hf] using exterior_residual_powerful_decomposition K S I

theorem residual_fibre_sum {M : Type*} [AddCommMonoid M]
    (R : Finset (ExteriorIdeal K S)) (F : ExteriorIdeal K S)
    (E : ExteriorIdeal K S → M) :
    (∑ I ∈ powerfulFibre K S R F, E I) =
      ∑ k ∈ residualFibre K S R F, E (exteriorMul K S k F) := by
  rw [residualFibre, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro I hI
    rw [residual_fibre_reconstruction K S R F I hI]
  · intro I hI J hJ h
    exact residual_injective_on_fibre K S F
      (Finset.mem_filter.mp hI).2 (Finset.mem_filter.mp hJ).2 h

theorem residual_fibre_squarefree (R : Finset (ExteriorIdeal K S))
    (F k : ExteriorIdeal K S) (hk : k ∈ residualFibre K S R F) :
    Squarefree k.val.val := by
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hk
  exact residualPart_squarefree I.val

theorem residual_fibre_coprime (R : Finset (ExteriorIdeal K S))
    (F k : ExteriorIdeal K S) (hk : k ∈ residualFibre K S R F) :
    IsCoprime k.val.val F.val.val := by
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hk
  have hf := (Finset.mem_filter.mp hI).2
  have he := (powerful_residual_coprime I.val).symm
  change IsCoprime (exteriorResidualPart K S I).val.val
    (exteriorPowerfulPart K S I).val.val at he
  simpa only [hf] using he

theorem residual_fibre_norm_le (R : Finset (ExteriorIdeal K S))
    (F k : ExteriorIdeal K S) (X : ℝ)
    (hR : ∀ I ∈ R, exteriorNorm K S I ≤ X)
    (hk : k ∈ residualFibre K S R F) :
    exteriorNorm K S k ≤ X / exteriorNorm K S F := by
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hk
  have hf := (Finset.mem_filter.mp hI).2
  have hnorm : exteriorNorm K S I =
      exteriorNorm K S F * exteriorNorm K S (exteriorResidualPart K S I) := by
    have h := norm_powerful_residual_decomposition I.val
    change exteriorNorm K S I = exteriorNorm K S (exteriorPowerfulPart K S I) *
      exteriorNorm K S (exteriorResidualPart K S I) at h
    simpa only [hf] using h
  apply (le_div_iff₀ (exteriorNorm_pos K S F)).mpr
  rw [mul_comm, ← hnorm]
  exact hR I (Finset.mem_filter.mp hI).1

/-- In each fixed sector the original energy is exactly the squarefree-row
energy on the fibre, so the sieve applies to the original residual ideal. -/
theorem residual_fibre_energy (R : Finset (ExteriorIdeal K S))
    (F : ExteriorIdeal K S) (row : ExteriorIdeal K S → ℂ) :
    (∑ I ∈ powerfulFibre K S R F, ‖row I‖ ^ 2) =
      ∑ k ∈ residualFibre K S R F, ‖row (exteriorMul K S k F)‖ ^ 2 :=
  residual_fibre_sum K S R F (fun I => ‖row I‖ ^ 2)

#print axioms residual_injective_on_fibre
#print axioms residual_fibre_sum
#print axioms residual_fibre_norm_le
#print axioms residual_fibre_energy

end HeckeSkeleton.LowEnergy.ActualRowFibres
