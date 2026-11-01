import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPaidSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PassiveDeletionMass

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
  simp only [firstMask, literalDeletionIdeal, commonRadical, Finset.inter_self]

theorem firstMask_primes (D : Ideal (𝓞 K)) :
    primeSupport (firstMask D).val = primeSupport D := by
  rw [firstMask_val, commonRadical_support, Finset.inter_self]

theorem firstMask_dvd (D : Ideal (𝓞 K)) (hD : D ≠ 0) : (firstMask D).val ∣ D := by
  rw [firstMask_val]
  exact (commonRadical_dvd D D hD hD).1

variable {A : SArithmeticData K}

theorem pool_support_prime (D : Ideal (𝓞 K)) (p : ExteriorPrime A)
    (v : Ideal (𝓞 K)) (hv : v ∈ primeSupport D ∪ {p.val.asIdeal}) : Prime v := by
  rcases Finset.mem_union.mp hv with hv | hv
  · exact support_prime hv
  · simpa only [Finset.mem_singleton.mp hv] using p.val.prime

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
  apply literalDeletionIdeal_dvd _ _ _
    (mul_ne_zero (nonZeroDivisors.coe_ne_zero (firstMask D)) p.val.ne_bot)
  intro v hv
  have hvprime := pool_support_prime D p v hv
  apply (prime_mem_support_iff_dvd v _ hvprime
    (mul_ne_zero (nonZeroDivisors.coe_ne_zero (firstMask D)) p.val.ne_bot)).mpr
  rcases Finset.mem_union.mp hv with hv | hv
  · have hfirst : v ∈ primeSupport (firstMask D).val := by
      rw [firstMask_primes]
      exact hv
    exact dvd_mul_of_dvd_left
      ((prime_mem_support_iff_dvd v _ hvprime
        (nonZeroDivisors.coe_ne_zero (firstMask D))).mp hfirst) _
  · rcases Finset.mem_singleton.mp hv with rfl
    exact dvd_mul_of_dvd_right (dvd_refl _) _

/-- At valuation six the passive prime is kept a second time. This
bound pays that genuine multiplicity, rather than silently taking a radical. -/
theorem poolMask_dvd (D : Ideal (𝓞 K)) (p : ExteriorPrime A) (e : AmplifierValuation) :
    (poolMask D p e).val ∣ ((firstMask D).val * p.val.asIdeal) * p.val.asIdeal := by
  have hp : (CanonicalLiteralPassivePhases.passiveIdeal p e).val ∣ p.val.asIdeal := by
    cases e <;> simp [CanonicalLiteralPassivePhases.passiveIdeal,
      CanonicalLiteralPassivePhases.passiveExponent, powerIdeal,
      ExteriorIdealEuler.pow, LocalFiniteSums.primeIdeal]
  exact mul_dvd_mul (poolExtra_dvd D p) hp

theorem firstMask_norm_le_column (D I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (hdiv : (firstMask D).val ∣ I) :
    idealNorm K (firstMask D) ≤ (Ideal.absNorm I : ℝ) :=
  HeckePort.Moments.norm_le_of_dvd hI hdiv

theorem poolMask_norm_le_column (D I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (hdiv : (firstMask D).val ∣ I) (p : ExteriorPrime A) (e : AmplifierValuation) :
    idealNorm K (poolMask D p e) ≤
      ((Ideal.absNorm I : ℝ) * (Ideal.absNorm p.val.asIdeal : ℝ)) *
        (Ideal.absNorm p.val.asIdeal : ℝ) := by
  have h := HeckePort.Moments.norm_le_of_dvd
    (mul_ne_zero (mul_ne_zero hI p.val.ne_bot) p.val.ne_bot)
    ((poolMask_dvd D p e).trans
      (mul_dvd_mul (mul_dvd_mul hdiv (dvd_refl _)) (dvd_refl _)))
  simpa only [map_mul, Nat.cast_mul] using h

theorem poolMask_norm_window (D I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (hdiv : (firstMask D).val ∣ I) (p : ExteriorPrime A) (e : AmplifierValuation)
    (Z columnBound primeBound : ℝ) (hZ : 1 < Z)
    (hcolumn : (Ideal.absNorm I : ℝ) ≤ Z ^ columnBound)
    (hprime : (Ideal.absNorm p.val.asIdeal : ℝ) ≤ Z ^ primeBound) :
    idealNorm K (poolMask D p e) ≤ Z ^ (columnBound + 2 * primeBound) := by
  calc
    _ ≤ _ := poolMask_norm_le_column D I hI hdiv p e
    _ ≤ (Z ^ columnBound * Z ^ primeBound) * Z ^ primeBound :=
      mul_le_mul (mul_le_mul hcolumn hprime (by positivity) (by positivity))
        hprime (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (zero_lt_one.trans hZ),
        ← Real.rpow_add (zero_lt_one.trans hZ)]
      congr 1
      ring

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
  have hD : DE.1 ≠ 0 := by
    rw [← b.common_left]
    exact (primePowerProduct b.primes b.leftMultiplicity).property.1
  apply (CanonicalLiteralPassiveLabelMass.firstMask_dvd DE.1 hD).trans
  refine ⟨(b.leftResidual i).val, ?_⟩
  simpa only [b.common_left] using b.left_reconstruct left i hi

/-- The right fibre has the same original prime support. No left
column or nonempty left carrier is required for this alternative. -/
theorem passiveFirstMask_dvd_right (right : Finset β) (j : β)
    (hj : j ∈ b.rightColumns right) :
    (CanonicalLiteralPassiveLabelMass.firstMask DE.1).val ∣ (fullJ j).val := by
  have hD : DE.2 ≠ 0 := by
    rw [← b.common_right]
    exact (primePowerProduct b.primes b.rightMultiplicity).property.1
  have hrad : (CanonicalLiteralPassiveLabelMass.firstMask DE.1).val ∣ DE.2 := by
    apply literalDeletionIdeal_dvd _ _ DE.2 hD
    rw [b.common_support_eq] <;> exact Finset.Subset.refl _
  apply hrad.trans
  refine ⟨(b.rightResidual j).val, ?_⟩
  simpa only [b.common_right] using b.right_reconstruct right j hj

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
  let δ := ε / (box + 1)
  have hden : 0 < box + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨C, hC, hmass⟩ := labels_mass_bound K cap δ hδ
  refine ⟨C, hC, ?_⟩
  intro Z hZ M hM k hk T hT
  have hexp : box * δ ≤ ε := by
    have he : (box + 1) * δ = ε := by
      dsimp only [δ]
      field_simp [hden.ne']
    nlinarith
  refine (hmass M.val (nonZeroDivisors.coe_ne_zero M) k hk T hT).trans ?_
  apply mul_le_mul_of_nonneg_left _ hC.le
  calc
    (Ideal.absNorm M.val : ℝ) ^ δ ≤ (Z ^ box) ^ δ :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hM hδ.le
    _ = Z ^ (box * δ) := (Real.rpow_mul (zero_lt_one.trans hZ).le box δ).symm
    _ ≤ Z ^ ε := Real.rpow_le_rpow_of_exponent_le hZ.le hexp

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
  obtain ⟨C, hC, hmass⟩ := mass_of_original_norm_window (K := K)
    cap columnBound ε hcolumnBound hε
  refine ⟨C, hC, ?_⟩
  intro Z hZ A D I hI hdiv hnorm k d W allocation hk
  have hkeep : allocation.keep.card ≤ cap :=
    (Finset.card_le_univ allocation.keep).trans (by simpa only [Fintype.card_fin] using hk)
  exact hmass Z hZ (firstMask D)
    ((firstMask_norm_le_column D I hI hdiv).trans hnorm) allocation.keep.card hkeep
    (CanonicalLiteralPassiveSource.labels W allocation A (firstMask D))
    (liveLabels_subset _ _ _ _ _ _ _)

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
  obtain ⟨C, hC, hmass⟩ := mass_of_original_norm_window (K := K)
    cap (columnBound + 2 * primeBound) ε (by positivity) hε
  refine ⟨C, hC, ?_⟩
  intro Z hZ A D I hI hdiv hnorm p hprime e k d W allocation hk
  have hkeep : allocation.keep.card ≤ cap :=
    (Finset.card_le_univ allocation.keep).trans (by simpa only [Fintype.card_fin] using hk)
  exact hmass Z hZ (poolMask D p e)
    (poolMask_norm_window D I hI hdiv p e Z columnBound primeBound hZ hnorm hprime)
    allocation.keep.card hkeep
    (CanonicalLiteralPassiveSource.labels W allocation A (poolMask D p e))
    (liveLabels_subset _ _ _ _ _ _ _)

end CanonicalLiteralPassiveLabelMass
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveLabelMass.poolMask_dvd
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveLabelMass.poolMask_norm_window
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.passiveFirstMask_dvd_left
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.passiveFirstMask_dvd_right
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveLabelMass.direct_source_labels_mass
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveLabelMass.pool_source_labels_mass
