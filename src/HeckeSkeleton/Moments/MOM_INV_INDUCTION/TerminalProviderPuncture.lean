import HeckeSkeleton.Moments.MOM_BASE.ThetaBridge
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstSourceDecomposition
import HeckeSkeleton.Moments.MOM_INV_STEP.ConductorMasks
import HeckePort.Moments.Descent.MarkedTwists

/-!
# The actual exterior radical of a canonical puncture

The canonical family permits an arbitrary nonzero integral puncture.
On exterior columns its mask is exactly the mask of the exterior part
of its radical. This is a proved prime-support projection, with no
change to the source and with norm bounded by the original radical.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Arithmetic.IdealMobiusMask
open HeckeSkeleton.Moments.MOM_BASE
open HeckeSkeleton.Moments.MOM_INV_STEP.FirstSourceDecomposition
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def exteriorPunctureSupport (r : NonzeroIdeal K) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (primeSupport r).filter (fun p => p ∉ S)

/-- The squarefree exterior ideal is constructed from the actual
puncture support, including when the original puncture has S factors. -/
def exteriorRadicalPuncture (r : NonzeroIdeal K) : ExteriorIdeal K S :=
  ⟨squarefreeIdeal K (exteriorPunctureSupport K S r), by
    intro p hp
    have hm : p ∈ exteriorPunctureSupport K S r := by
      simpa only [idealPrimeSupport_squarefreeIdeal] using
        (mem_idealPrimeSupport_iff K _ p).mpr hp
    exact (Finset.mem_filter.mp hm).2⟩

theorem exteriorRadicalPuncture_squarefree (r : NonzeroIdeal K) :
    Squarefree (exteriorRadicalPuncture K S r).val.val :=
  squarefree_primeProduct _

theorem exteriorRadicalPuncture_dvd_radical (r : NonzeroIdeal K) :
    (exteriorRadicalPuncture K S r).val.val ∣ r.val.radical := by
  rw [radical_eq_primeProduct r]
  change (∏ p ∈ exteriorPunctureSupport K S r, p.asIdeal) ∣
    ∏ p ∈ primeSupport r, p.asIdeal
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)

/-- Projection cannot enlarge the logarithmic puncture charge. -/
theorem exteriorRadicalPuncture_norm_le (r : NonzeroIdeal K) :
    exteriorNorm K S (exteriorRadicalPuncture K S r) ≤ (r.val.radical.absNorm : ℝ) := by
  have hr : r.val.radical ≠ ⊥ := by
    intro hz
    exact nonZeroDivisors.coe_ne_zero r
      (le_bot_iff.mp (hz ▸ (Ideal.le_radical : r.val ≤ r.val.radical)))
  have hn : 0 < r.val.radical.absNorm :=
    Nat.pos_of_ne_zero (fun h => hr (Ideal.absNorm_eq_zero_iff.mp h))
  change ((exteriorRadicalPuncture K S r).val.val.absNorm : ℝ) ≤
    (r.val.radical.absNorm : ℝ)
  exact_mod_cast Nat.le_of_dvd hn
    (Ideal.absNorm_dvd_absNorm_of_le
      (Ideal.dvd_iff_le.mp (exteriorRadicalPuncture_dvd_radical K S r)))

/-- Every original puncture zero is retained, and S-supported factors
are inert because the moving column is exterior. -/
theorem exteriorRadicalPuncture_coprime (r : NonzeroIdeal K) (n : ExteriorIdeal K S) :
    IsCoprime n.val.val (exteriorRadicalPuncture K S r).val.val ↔
      IsCoprime n.val.val r.val := by
  rw [← HeckeSkeleton.Moments.MOM_INV_STEP.ConductorMasks.coprime_radical_right_iff
      n.val.val r.val,
    radical_eq_primeProduct r]
  change IsCoprime n.val.val (primeProduct (exteriorPunctureSupport K S r)) ↔
    IsCoprime n.val.val (primeProduct (primeSupport r))
  simp only [primeProduct, IsCoprime.prod_right_iff]
  constructor
  · intro h p hp
    by_cases hpS : p ∈ S
    · apply IsCoprime.symm
      apply (HeckePort.Moments.prime_isCoprime_iff_not_dvd _ _ p.prime).mpr
      intro hdiv
      exact n.property p hdiv hpS
    · exact h p (Finset.mem_filter.mpr ⟨hp, hpS⟩)
  · intro h p hp
    exact h p (Finset.mem_filter.mp hp).1

variable (D : ThetaArithmeticData K S)

/-- The complete multiplicative coefficient is unchanged on every
ideal, using its original exterior zero off the admissible support. -/
theorem canonicalTau_exteriorRadicalPuncture
    (θ : HeckeCharacter K) (m : S.integer K) (r : NonzeroIdeal K) :
    canonicalTau K S D θ m (exteriorRadicalPuncture K S r).val.val =
      canonicalTau K S D θ m r.val := by
  ext I
  by_cases hI : HeckePort.CenteredMomentGenerator.IsExterior K S I
  · let n := HeckePort.CenteredMomentGenerator.toExterior K S I hI
    change canonicalTau K S D θ m (exteriorRadicalPuncture K S r).val.val n.val.val =
      canonicalTau K S D θ m r.val n.val.val
    rw [canonicalTau_apply, canonicalTau_apply, exteriorRadicalPuncture_coprime]
  · rw [canonicalTau_eq_zero_of_not_exterior K S D θ m _ I hI,
      canonicalTau_eq_zero_of_not_exterior K S D θ m _ I hI]

end HeckeSkeleton.Moments.MOM_INV_INDUCTION

end
