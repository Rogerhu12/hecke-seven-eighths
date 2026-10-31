import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CommonSupportPartition
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CommonHarmonicMass

/-!
# Arithmetic conditions of actual common-support labels

The old squarefree divisor is inherited from each original column and
therefore divides both complete extracted common parts. Original
individual norm windows also bound those parts. This supplies the raw
conditions of the harmonic estimate for the actual finite support pool;
neither a label count nor a total label mass is assumed.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField UniqueFactorizationMonoid
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open CommonSupportMass

variable {K : Type} [Field K] [NumberField K]

theorem actual_supportExtract_dvd (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (T : Finset (Ideal (𝓞 K))) : supportExtract I T ∣ I :=
  ⟨supportResidual I T, (support_reconstruct I (by simpa only [Ideal.zero_eq_bot] using hI) T).symm⟩

theorem actual_common_label_nonzero (I J : Ideal (𝓞 K)) :
    (commonSupportLabel I J).1 ≠ 0 ∧ (commonSupportLabel I J).2 ≠ 0 := by
  constructor <;>
    simpa only [commonSupportLabel, Ideal.zero_eq_bot] using supportExtract_ne_zero _ _

theorem actual_common_label_norm_le (I J : Ideal (𝓞 K)) (hI : I ≠ 0) (hJ : J ≠ 0) :
    (Ideal.absNorm (commonSupportLabel I J).1 : ℝ) ≤ Ideal.absNorm I ∧
      (Ideal.absNorm (commonSupportLabel I J).2 : ℝ) ≤ Ideal.absNorm J :=
  ⟨norm_le_of_dvd hI (actual_supportExtract_dvd I hI _),
    norm_le_of_dvd hJ (actual_supportExtract_dvd J hJ _)⟩

/-- A genuine common divisor survives extraction on the whole common
support. Only its squarefreeness and original divisibilities are used. -/
theorem actual_common_label_old_mask (s I J : Ideal (𝓞 K))
    (hs : Squarefree s) (hI : I ≠ 0) (hJ : J ≠ 0)
    (hsI : s ∣ I) (hsJ : s ∣ J) :
    s ∣ (commonSupportLabel I J).1 ∧ s ∣ (commonSupportLabel I J).2 := by
  have hrad := old_mask_dvd_commonRadical s I J hs hI hJ hsI hsJ
  have hzero := actual_common_label_nonzero I J
  constructor
  · apply hrad.trans
    apply support_product_dvd hzero.1
    simpa only [commonSupportLabel_left_support] using
      (Finset.Subset.refl (primeSupport I ∩ primeSupport J))
  · apply hrad.trans
    apply support_product_dvd hzero.2
    simpa only [commonSupportLabel_right_support] using
      (Finset.Subset.refl (primeSupport I ∩ primeSupport J))

/-- All complete original common pairs and all subsets of their real
common radical. Additional source labels are counted by their fibres. -/
def actualCommonLabels {ι κ : Type*}
    (left : Finset ι) (right : Finset κ)
    (I : ι → Ideal (𝓞 K)) (J : κ → Ideal (𝓞 K)) : Finset (Label K) :=
  (commonSupportPool left right I J).biUnion fun DE =>
    (primeSupport (commonRadical DE.1 DE.2)).powerset.image (fun T => (DE, T))

theorem mem_actualCommonLabels {ι κ : Type*}
    (left : Finset ι) (right : Finset κ)
    (I : ι → Ideal (𝓞 K)) (J : κ → Ideal (𝓞 K)) (v : Label K) :
    v ∈ actualCommonLabels left right I J ↔
      v.1 ∈ commonSupportPool left right I J ∧
        v.2 ⊆ primeSupport (commonRadical v.1.1 v.1.2) := by
  constructor
  · intro hv
    obtain ⟨DE, hDE, hv⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨T, hT, he⟩ := Finset.mem_image.mp hv
    cases he
    exact ⟨hDE, Finset.mem_powerset.mp hT⟩
  · rintro ⟨hv, hT⟩
    exact Finset.mem_biUnion.mpr ⟨v.1, hv,
      Finset.mem_image.mpr ⟨v.2, Finset.mem_powerset.mpr hT, by cases v; rfl⟩⟩

theorem actualCommonLabels_valid {ι κ : Type*}
    (left : Finset ι) (right : Finset κ)
    (I : ι → Ideal (𝓞 K)) (J : κ → Ideal (𝓞 K))
    (s : Ideal (𝓞 K)) (hs : Squarefree s)
    (hI : ∀ i ∈ left, I i ≠ 0) (hJ : ∀ j ∈ right, J j ≠ 0)
    (hsI : ∀ i ∈ left, s ∣ I i) (hsJ : ∀ j ∈ right, s ∣ J j)
    (v : Label K) (hv : v ∈ actualCommonLabels left right I J) : Valid s v := by
  obtain ⟨hv, hT⟩ := (mem_actualCommonLabels left right I J v).mp hv
  obtain ⟨ij, hij, he⟩ := Finset.mem_image.mp hv
  have hi := (Finset.mem_product.mp hij).1
  have hj := (Finset.mem_product.mp hij).2
  have hn := actual_common_label_nonzero (I ij.1) (J ij.2)
  have hd := actual_common_label_old_mask s (I ij.1) (J ij.2) hs
    (hI ij.1 hi) (hJ ij.2 hj) (hsI ij.1 hi) (hsJ ij.2 hj)
  rw [he] at hn hd
  refine ⟨hn.1, hn.2, ?_, hd.1, hd.2, hT⟩
  rw [← he]
  exact commonSupportLabel_support_eq _ _

theorem actualCommonLabels_norm {ι κ : Type*}
    (left : Finset ι) (right : Finset κ)
    (I : ι → Ideal (𝓞 K)) (J : κ → Ideal (𝓞 K))
    (hI : ∀ i ∈ left, I i ≠ 0) (hJ : ∀ j ∈ right, J j ≠ 0)
    (Y : ℝ) (hNI : ∀ i ∈ left, (Ideal.absNorm (I i) : ℝ) ≤ Y)
    (hNJ : ∀ j ∈ right, (Ideal.absNorm (J j) : ℝ) ≤ Y)
    (v : Label K) (hv : v ∈ actualCommonLabels left right I J) :
    (Ideal.absNorm v.1.1 : ℝ) ≤ Y ∧ (Ideal.absNorm v.1.2 : ℝ) ≤ Y := by
  have hv := ((mem_actualCommonLabels left right I J v).mp hv).1
  obtain ⟨ij, hij, he⟩ := Finset.mem_image.mp hv
  have hi := (Finset.mem_product.mp hij).1
  have hj := (Finset.mem_product.mp hij).2
  have hn := actual_common_label_norm_le (I ij.1) (J ij.2) (hI ij.1 hi) (hJ ij.2 hj)
  rw [he] at hn
  exact ⟨hn.1.trans (hNI ij.1 hi), hn.2.trans (hNJ ij.2 hj)⟩

/-- The same harmonic estimate is now derived for the actual image of
original columns, rather than supplied as an aggregate calibration. -/
theorem actual_common_support_harmonic_mass (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ s : Ideal (𝓞 K), Squarefree s → s ≠ 0 →
      ∀ {ι κ : Type*} (left : Finset ι) (right : Finset κ)
        (I : ι → Ideal (𝓞 K)) (J : κ → Ideal (𝓞 K)),
      (∀ i ∈ left, I i ≠ 0) → (∀ j ∈ right, J j ≠ 0) →
      (∀ i ∈ left, s ∣ I i) → (∀ j ∈ right, s ∣ J j) →
      (∀ i ∈ left, (Ideal.absNorm (I i) : ℝ) ≤ Z ^ B) →
      (∀ j ∈ right, (Ideal.absNorm (J j) : ℝ) ≤ Z ^ B) →
      (∑ v ∈ actualCommonLabels left right I J,
        1 / (Ideal.absNorm (commonRadical v.1.1 v.1.2) : ℝ)) ≤
          C * Z ^ ε / (Ideal.absNorm s : ℝ) := by
  obtain ⟨C, hC, hm⟩ := common_radical_harmonic_mass (K := K) B ε hB hε
  refine ⟨C, hC, ?_⟩
  intro Z hZ s hs hs0 ι κ left right I J hI hJ hsI hsJ hNI hNJ
  exact hm Z hZ s hs hs0 (actualCommonLabels left right I J)
    (actualCommonLabels_valid left right I J s hs hI hJ hsI hsJ)
    (actualCommonLabels_norm left right I J hI hJ (Z ^ B) hNI hNJ)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_common_label_old_mask
#print axioms HeckeSkeleton.Moments.EngineStep.actual_common_support_harmonic_mass
