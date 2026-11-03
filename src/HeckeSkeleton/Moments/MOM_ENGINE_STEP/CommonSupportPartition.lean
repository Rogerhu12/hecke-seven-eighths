import HeckePort.Moments.Support

/-!
# A complete finite partition by the genuine common supports

Every original pair belongs to exactly one pair of complete extracted
ideals.  A fixed block is a rectangle of independently filtered columns,
with precisely the residual coprimality condition retained.  This is the
condition used by the complete-correlation and Möbius identities.

The label pool is the actual image of all original column pairs.  The
identity neither assumes a support partition nor bounds its cardinality
by an unrelated formal family.
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField HeckePort.IdealMobiusDivisorSum
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type*} [Field K] [NumberField K]

/-- Both complete extracted ideals, retaining every original multiplicity. -/
def commonSupportLabel (I J : Ideal (𝓞 K)) : Ideal (𝓞 K) × Ideal (𝓞 K) :=
  let S := primeSupport I ∩ primeSupport J
  (supportExtract I S, supportExtract J S)

theorem commonSupportLabel_left_support (I J : Ideal (𝓞 K)) :
    primeSupport (commonSupportLabel I J).1 = primeSupport I ∩ primeSupport J := by
  rw [commonSupportLabel, supportExtract_support]
  ext p
  simp only [Finset.mem_inter]
  tauto

theorem commonSupportLabel_right_support (I J : Ideal (𝓞 K)) :
    primeSupport (commonSupportLabel I J).2 = primeSupport I ∩ primeSupport J := by
  rw [commonSupportLabel, supportExtract_support]
  ext p
  simp only [Finset.mem_inter]
  tauto

theorem commonSupportLabel_support_eq (I J : Ideal (𝓞 K)) :
    primeSupport (commonSupportLabel I J).1 = primeSupport (commonSupportLabel I J).2 := by
  rw [commonSupportLabel_left_support, commonSupportLabel_right_support]

/-- Membership in a fixed genuine block has independent left/right
conditions and the full residual coprimality condition, with no deletion. -/
theorem commonSupportLabel_eq_iff (I J D E : Ideal (𝓞 K))
    (hDE : primeSupport D = primeSupport E) :
    commonSupportLabel I J = (D, E) ↔
      supportExtract I (primeSupport D) = D ∧
      supportExtract J (primeSupport D) = E ∧
      IsCoprime (supportResidual I (primeSupport D))
        (supportResidual J (primeSupport D)) := by
  constructor
  · intro hlabel
    have hD : (commonSupportLabel I J).1 = D := congrArg Prod.fst hlabel
    have hE : (commonSupportLabel I J).2 = E := congrArg Prod.snd hlabel
    have hS : primeSupport D = primeSupport I ∩ primeSupport J := by
      rw [← hD, commonSupportLabel_left_support]
    rw [hS]
    exact ⟨hD, hE, common_support_residual_coprime I J⟩
  · rintro ⟨hD, hE, hcop⟩
    have hI : primeSupport I ∩ primeSupport D = primeSupport D := by
      rw [← supportExtract_support, hD]
    have hJ : primeSupport J ∩ primeSupport D = primeSupport D := by
      rw [← supportExtract_support, hE, ← hDE]
    have hdis := (primeSupport_disjoint_iff
      (supportResidual_ne_zero I (primeSupport D))
      (supportResidual_ne_zero J (primeSupport D))).mpr hcop
    rw [supportResidual_support, supportResidual_support] at hdis
    have hS : primeSupport I ∩ primeSupport J = primeSupport D := by
      apply Finset.Subset.antisymm
      · intro p hp
        by_contra hn
        exact Finset.disjoint_left.mp hdis
          (Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hp).1, hn⟩)
          (Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hp).2, hn⟩)
      · intro p hp
        apply Finset.mem_inter.mpr
        constructor
        · exact (Finset.mem_inter.mp (hI.symm ▸ hp)).1
        · exact (Finset.mem_inter.mp (hJ.symm ▸ hp)).1
    simp only [commonSupportLabel, hS, hD, hE]

/-- The actual finite common-support labels occurring in the original sum. -/
def commonSupportPool {ι κ : Type*} (left : Finset ι) (right : Finset κ)
    (I : ι → Ideal (𝓞 K)) (J : κ → Ideal (𝓞 K)) :
    Finset (Ideal (𝓞 K) × Ideal (𝓞 K)) :=
  (left ×ˢ right).image fun ij => commonSupportLabel (I ij.1) (J ij.2)

theorem commonSupportPool_support_eq {ι κ : Type*}
    (left : Finset ι) (right : Finset κ)
    (I : ι → Ideal (𝓞 K)) (J : κ → Ideal (𝓞 K))
    (DE : Ideal (𝓞 K) × Ideal (𝓞 K))
    (hDE : DE ∈ commonSupportPool left right I J) :
    primeSupport DE.1 = primeSupport DE.2 := by
  obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp hDE
  exact commonSupportLabel_support_eq _ _

/-- Exact rectangular partition of every original pair.  The same identity
applies before either orbital transform, without an absolute estimate. -/
theorem sum_common_support_blocks {ι κ T : Type*} [AddCommMonoid T]
    (left : Finset ι) (right : Finset κ)
    (I : ι → Ideal (𝓞 K)) (J : κ → Ideal (𝓞 K)) (f : ι → κ → T) :
    (∑ i ∈ left, ∑ j ∈ right, f i j) =
      ∑ DE ∈ commonSupportPool left right I J,
        ∑ i ∈ left.filter (fun i => supportExtract (I i) (primeSupport DE.1) = DE.1),
        ∑ j ∈ right.filter (fun j => supportExtract (J j) (primeSupport DE.1) = DE.2),
          if IsCoprime (supportResidual (I i) (primeSupport DE.1))
              (supportResidual (J j) (primeSupport DE.1)) then f i j else 0 := by
  have hmap : ∀ ij ∈ left ×ˢ right,
      commonSupportLabel (I ij.1) (J ij.2) ∈ commonSupportPool left right I J :=
    fun ij hij => Finset.mem_image_of_mem _ hij
  have hsum := Finset.sum_fiberwise_of_maps_to hmap (fun ij => f ij.1 ij.2)
  rw [Finset.sum_product] at hsum
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro DE hDE
  have hsupport := commonSupportPool_support_eq left right I J DE hDE
  simp only [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [commonSupportLabel_eq_iff (I i) _ DE.1 DE.2 hsupport]
  by_cases hD : supportExtract (I i) (primeSupport DE.1) = DE.1
  · simp only [hD, true_and, ite_true]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hE : supportExtract (J j) (primeSupport DE.1) = DE.2 <;>
      simp only [hE, true_and, false_and, ite_true, ite_false]
  · simp only [hD, false_and, ite_false, Finset.sum_const_zero]

/-- The label pool contains only nonzero complete supports. -/
theorem commonSupportPool_nonzero {ι κ : Type*}
    (left : Finset ι) (right : Finset κ)
    (I : ι → Ideal (𝓞 K)) (J : κ → Ideal (𝓞 K))
    (DE : Ideal (𝓞 K) × Ideal (𝓞 K))
    (hDE : DE ∈ commonSupportPool left right I J) : DE.1 ≠ ⊥ ∧ DE.2 ≠ ⊥ := by
  obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp hDE
  exact ⟨supportExtract_ne_zero _ _, supportExtract_ne_zero _ _⟩

end HeckeSkeleton.Moments.EngineStep

end

#print axioms HeckeSkeleton.Moments.EngineStep.commonSupportLabel_eq_iff
#print axioms HeckeSkeleton.Moments.EngineStep.sum_common_support_blocks
