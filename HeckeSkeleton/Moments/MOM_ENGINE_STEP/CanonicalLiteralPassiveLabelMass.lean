import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPaidSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PassiveDeletionMass

set_option linter.unusedSectionVars false

/-!
# Uniform mass of the genuine passive labels

The first deletion is the radical of the original common support. The
pool deletion keeps the union with the original amplifier prime and,
at valuation six, a second copy of that prime. This literal mask divides
the first radical times two copies of the original pool prime.

Original common-column reconstruction pays the first radical. Original
column and prime norm windows then pay the complete deletion ideal.
The divisor-allocation count supplies the actual signed label mass;
its constant is selected before every scale, source and label.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum CommonSupportMass

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralPassiveLabelMass

def firstMask (D : Ideal (𝓞 K)) : HeckeGeneral.Analysis.NonzeroIdeal K :=
  literalDeletionIdeal (primeSupport D) (fun _ hp => support_prime hp)

theorem firstMask_val (D : Ideal (𝓞 K)) :
    (firstMask D).val = commonRadical D D := by
  sorry

theorem firstMask_primes (D : Ideal (𝓞 K)) :
    primeSupport (firstMask D).val = primeSupport D := by
  sorry

theorem firstMask_dvd (D : Ideal (𝓞 K)) (hD : D ≠ 0) : (firstMask D).val ∣ D := by
  sorry

variable {A : SArithmeticData K}

theorem pool_support_prime (D : Ideal (𝓞 K)) (p : ExteriorPrime A)
    (v : Ideal (𝓞 K)) (hv : v ∈ primeSupport D ∪ {p.val.asIdeal}) : Prime v := by
  sorry

def poolExtra (D : Ideal (𝓞 K)) (p : ExteriorPrime A) :
    HeckeGeneral.Analysis.NonzeroIdeal K :=
  literalDeletionIdeal (primeSupport D ∪ {p.val.asIdeal}) (pool_support_prime D p)

def poolMask (D : Ideal (𝓞 K)) (p : ExteriorPrime A) (e : AmplifierValuation) :
    HeckeGeneral.Analysis.NonzeroIdeal K :=
  CanonicalLiteralPaidCharacters.passiveMask (poolExtra D p) p e

/-- The pool prime is included before the radical is formed; overlap
with the first support never requires a disjointness assumption. -/
theorem poolExtra_dvd (D : Ideal (𝓞 K)) (p : ExteriorPrime A) :
    (poolExtra D p).val ∣ (firstMask D).val * p.val.asIdeal := by
  sorry

/-- At valuation six the passive prime is kept a second time. This
bound pays that genuine multiplicity, rather than silently taking a radical. -/
theorem poolMask_dvd (D : Ideal (𝓞 K)) (p : ExteriorPrime A) (e : AmplifierValuation) :
    (poolMask D p e).val ∣ ((firstMask D).val * p.val.asIdeal) * p.val.asIdeal := by
  sorry

theorem firstMask_norm_le_column (D I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (hdiv : (firstMask D).val ∣ I) :
    idealNorm K (firstMask D) ≤ (Ideal.absNorm I : ℝ) := by
  sorry

theorem poolMask_norm_le_column (D I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (hdiv : (firstMask D).val ∣ I) (p : ExteriorPrime A) (e : AmplifierValuation) :
    idealNorm K (poolMask D p e) ≤
      ((Ideal.absNorm I : ℝ) * (Ideal.absNorm p.val.asIdeal : ℝ)) *
        (Ideal.absNorm p.val.asIdeal : ℝ) := by
  sorry

theorem poolMask_norm_window (D I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (hdiv : (firstMask D).val ∣ I) (p : ExteriorPrime A) (e : AmplifierValuation)
    (Z columnBound primeBound : ℝ) (hZ : 1 < Z)
    (hcolumn : (Ideal.absNorm I : ℝ) ≤ Z ^ columnBound)
    (hprime : (Ideal.absNorm p.val.asIdeal : ℝ) ≤ Z ^ primeBound) :
    idealNorm K (poolMask D p e) ≤ Z ^ (columnBound + 2 * primeBound) := by
  sorry

end CanonicalLiteralPassiveLabelMass

namespace FirstCommonCharacterBlock

variable {A : SArithmeticData K}
variable {α β : Type*} {fullI : α → A.Exterior} {fullJ : β → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable (b : FirstCommonCharacterBlock fullI fullJ DE)

/-- Membership in the genuine common fibre supplies the first-mask
divisibility used in the label bound. -/
theorem passiveFirstMask_dvd_left (left : Finset α) (i : α)
    (hi : i ∈ b.leftColumns left) :
    (CanonicalLiteralPassiveLabelMass.firstMask DE.1).val ∣ (fullI i).val := by
  sorry

/-- The right fibre has the same original prime support. No left
column or nonempty left carrier is required for this alternative. -/
theorem passiveFirstMask_dvd_right (right : Finset β) (j : β)
    (hj : j ∈ b.rightColumns right) :
    (CanonicalLiteralPassiveLabelMass.firstMask DE.1).val ∣ (fullJ j).val := by
  sorry

end FirstCommonCharacterBlock

namespace CanonicalLiteralPassiveLabelMass

open CanonicalLiteralPassiveDeletion

private theorem mass_of_original_norm_window (cap : ℕ) (box ε : ℝ)
    (hbox : 0 ≤ box) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 < Z →
      ∀ M : HeckeGeneral.Analysis.NonzeroIdeal K,
      idealNorm K M ≤ Z ^ box → ∀ k : ℕ, k ≤ cap →
      ∀ T : Finset (Label K k), T ⊆ labels M.val k →
        (∑ a ∈ T, ‖sign a‖) ≤ C * Z ^ ε := by
  sorry

/-- The literal surviving direct/main labels have a uniform small
power cost. The only numerical input is an original column norm window. -/
theorem direct_source_labels_mass (cap : ℕ) (columnBound ε : ℝ)
    (hcolumnBound : 0 ≤ columnBound) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 < Z → ∀ (A : SArithmeticData K)
      (D I : Ideal (𝓞 K)), I ≠ 0 → (firstMask D).val ∣ I →
      (Ideal.absNorm I : ℝ) ≤ Z ^ columnBound →
      ∀ k : ℕ, ∀ (d : CanonicalLiteralRectangles.Atoms (K := K) k)
        (W : d.ProfileData) (allocation : ActualColumnAllocation K k), k ≤ cap →
        (∑ a ∈ CanonicalLiteralPassiveSource.labels W allocation A (firstMask D),
          ‖sign a‖) ≤ C * Z ^ ε := by
  sorry

/-- The actual pool mask retains its duplicate prime when necessary.
Both prime copies are paid before applying the uniform label theorem. -/
theorem pool_source_labels_mass (cap : ℕ) (columnBound primeBound ε : ℝ)
    (hcolumnBound : 0 ≤ columnBound) (hprimeBound : 0 ≤ primeBound) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 < Z → ∀ (A : SArithmeticData K)
      (D I : Ideal (𝓞 K)), I ≠ 0 → (firstMask D).val ∣ I →
      (Ideal.absNorm I : ℝ) ≤ Z ^ columnBound →
      ∀ (p : ExteriorPrime A), (Ideal.absNorm p.val.asIdeal : ℝ) ≤ Z ^ primeBound →
      ∀ e : AmplifierValuation, ∀ k : ℕ,
      ∀ (d : CanonicalLiteralRectangles.Atoms (K := K) k)
        (W : d.ProfileData) (allocation : ActualColumnAllocation K k), k ≤ cap →
        (∑ a ∈ CanonicalLiteralPassiveSource.labels W allocation A (poolMask D p e),
          ‖sign a‖) ≤ C * Z ^ ε := by
  sorry

end CanonicalLiteralPassiveLabelMass
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveLabelMass.poolMask_dvd
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveLabelMass.poolMask_norm_window
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.passiveFirstMask_dvd_left
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.passiveFirstMask_dvd_right
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveLabelMass.direct_source_labels_mass
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveLabelMass.pool_source_labels_mass
