import HeckeGeneral.Analysis.MarkedThetaReflection
import HeckeGeneral.Analysis.SIntegerSexticDyadicAmplification

/-!
Absolute convergence of the actual completed ideal sum for an annular test.
The support is contained in a product of two finite ideal norm cutoffs.
No KP realization, arithmetic calibration, or reflection premise is used.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.MarkedAnnularSupport

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- An annular test makes the literal completed ideal sum finitely supported,
uniformly in the choice of row element and the finite puncture/mark masks. -/
theorem completedTerm_summable_of_annular (D : ThetaArithmeticData K S)
    (θ : HeckeCharacter K) (m : S.integer K) (r : ExteriorIdeal K S)
    (Q : Finset (ExteriorPrime K S)) (V : SmoothAnnularTest) (X : ℝ)
    (hX : 0 < X) :
    Summable (completedTerm K S D θ m r Q V.toFun X) := by
  classical
  let bound : ℝ := V.upper * X
  have hbound : 0 < bound := mul_pos (V.lower_pos.trans_le V.upper_ge) hX
  let cutoff : Finset (ExteriorIdeal K S) :=
    (SquarefreeAmplification.dyadicIdealSupport K (bound / 2)).subtype
      (fun I => ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → p ∉ S)
  have hmem (I : ExteriorIdeal K S) (hI : exteriorNorm K S I ≤ bound) :
      I ∈ cutoff := by
    change I ∈ (SquarefreeAmplification.dyadicIdealSupport K (bound / 2)).subtype _
    rw [Finset.mem_subtype]
    apply (SquarefreeAmplification.mem_dyadicIdealSupport_iff K
      (div_nonneg hbound.le (by norm_num)) I.val).mpr
    simpa only [exteriorNorm, idealNorm,
      show 2 * (bound / 2) = bound by ring] using hI
  apply summable_of_hasFiniteSupport
  apply (cutoff.product cutoff).finite_toSet.subset
  intro cn hcn
  change completedTerm K S D θ m r Q V.toFun X cn ≠ 0 at hcn
  have hV : V.toFun (exteriorNorm K S (completedIdeal K S cn.1 cn.2) / X) ≠ 0 := by
    intro hz
    apply hcn
    simp only [completedTerm, hz, mul_zero, ite_self]
  have hupper := (V.support hV).2
  have hnorm : exteriorNorm K S (completedIdeal K S cn.1 cn.2) =
      exteriorNorm K S cn.1 * exteriorNorm K S cn.2 ^ 3 := by
    simp only [exteriorNorm, completedIdeal, exteriorMul, Submonoid.coe_mul,
      map_mul, Nat.cast_mul]
    ring
  have hprod : exteriorNorm K S cn.1 * exteriorNorm K S cn.2 ^ 3 ≤ bound := by
    rw [hnorm] at hupper
    exact (div_le_iff₀ hX).mp hupper
  have hc : 1 ≤ exteriorNorm K S cn.1 := one_le_idealNorm K cn.1.val
  have hn : 1 ≤ exteriorNorm K S cn.2 := one_le_idealNorm K cn.2.val
  have hc0 : 0 ≤ exteriorNorm K S cn.1 := le_trans zero_le_one hc
  have hn0 : 0 ≤ exteriorNorm K S cn.2 := le_trans zero_le_one hn
  have hn3 : 1 ≤ exteriorNorm K S cn.2 ^ 3 := one_le_pow₀ hn
  have hcBound : exteriorNorm K S cn.1 ≤ bound := by
    calc
      _ = exteriorNorm K S cn.1 * 1 := (mul_one _).symm
      _ ≤ exteriorNorm K S cn.1 * exteriorNorm K S cn.2 ^ 3 :=
        mul_le_mul_of_nonneg_left hn3 hc0
      _ ≤ bound := hprod
  have hn2 : 1 ≤ exteriorNorm K S cn.2 ^ 2 := one_le_pow₀ hn
  have hnBound : exteriorNorm K S cn.2 ≤ bound := by
    calc
      _ = exteriorNorm K S cn.2 * 1 := (mul_one _).symm
      _ ≤ exteriorNorm K S cn.2 * exteriorNorm K S cn.2 ^ 2 :=
        mul_le_mul_of_nonneg_left hn2 hn0
      _ = exteriorNorm K S cn.2 ^ 3 := by ring
      _ = 1 * exteriorNorm K S cn.2 ^ 3 := (one_mul _).symm
      _ ≤ exteriorNorm K S cn.1 * exteriorNorm K S cn.2 ^ 3 :=
        mul_le_mul_of_nonneg_right hc (pow_nonneg hn0 _)
      _ ≤ bound := hprod
  exact Finset.mem_product.mpr ⟨hmem cn.1 hcBound, hmem cn.2 hnBound⟩

end HeckeSkeleton.MarkedAnnularSupport
