import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalLogNormLocations
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SupportCartesianReindex

/-!
# The two literal logarithmic coordinates of every original occurrence

The first Fourier sign is fixed by the actual left or right source.
Both logarithmic coordinates are then the sum of the same two plain
occurrences and every retained prime occurrence.  A genuine support
reconstruction adds only the logarithm of its fixed extracted ideal.
The second transform's row radius likewise adds one common row
translation.  The ordinary binding removes these translations inside
the squared column norms, without changing either Fourier variable.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralLocations

/-- This sign is fixed by the actual first source; the second
coordinate retains its original negative logarithm. -/
def direction (firstSign : ℝ) : WithLp 2 (ℝ × ℝ) :=
  WithLp.toLp 2 (firstSign, 1)

def plain (firstSign : ℝ) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    WithLp 2 (ℝ × ℝ) :=
  -Real.log (idealNorm K I) • direction firstSign

def prime {k : ℕ} (firstSign : ℝ) (_ : Fin k)
    (p : HeightOneSpectrum (𝓞 K)) : WithLp 2 (ℝ × ℝ) :=
  -Real.log (Ideal.absNorm p.asIdeal : ℝ) • direction firstSign

theorem scalar_direction (firstSign a : ℝ) :
    (-a) • direction firstSign = WithLp.toLp 2 (-firstSign * a, -a) := by
  change WithLp.toLp 2 ((-a) * firstSign, (-a) * 1) = _
  congr 1
  apply Prod.ext <;> dsimp <;> ring

/-- The location is proved from the individual ideal factors.  This
includes zero slots and repeated occurrences of the same prime. -/
theorem rawLocation (firstSign : ℝ) {k : ℕ} (i : AllocationColumn K k)
    (hleft : i.1.1 ≠ 0) (hright : i.1.2 ≠ 0) :
    rawSourceLocation (plain firstSign) (plain firstSign) (prime firstSign) i =
      WithLp.toLp 2
        (-firstSign * Real.log (Ideal.absNorm (allocationColumnIdeal i) : ℝ),
          -Real.log (Ideal.absNorm (allocationColumnIdeal i) : ℝ)) := by
  have hs := rawSourceLocation_neg_log_norm i hleft hright
  change -Real.log (idealNorm K (sourceMomentIdeal i.1.1)) +
      -Real.log (idealNorm K (sourceMomentIdeal i.1.2)) +
      ∑ j, -Real.log (Ideal.absNorm (i.2 j).asIdeal : ℝ) = _ at hs
  simp only [rawSourceLocation, childCartesianLocation, plain, prime]
  rw [← Finset.sum_smul, ← add_smul, ← add_smul, hs]
  exact scalar_direction firstSign _

theorem rawLocation_exterior (firstSign : ℝ) {A : SArithmeticData K} {k : ℕ}
    (i : AllocationColumn K k) (hleft : i.1.1 ≠ 0) (hright : i.1.2 ≠ 0)
    (I : A.Exterior) (hI : I.val = allocationColumnIdeal i) :
    rawSourceLocation (plain firstSign) (plain firstSign) (prime firstSign) i =
      WithLp.toLp 2 (-firstSign * Real.log (A.exteriorNorm I),
        -Real.log (A.exteriorNorm I)) := by
  rw [rawLocation firstSign i hleft hright]
  change WithLp.toLp 2
      (-firstSign * Real.log (Ideal.absNorm (allocationColumnIdeal i) : ℝ),
        -Real.log (Ideal.absNorm (allocationColumnIdeal i) : ℝ)) =
    WithLp.toLp 2 (-firstSign * Real.log (Ideal.absNorm I.val : ℝ),
      -Real.log (Ideal.absNorm I.val : ℝ))
  rw [hI]

private theorem real_norm_ne_zero (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    (Ideal.absNorm I : ℝ) ≠ 0 := by
  exact_mod_cast Ideal.absNorm_ne_zero_of_nonZeroDivisors
    (⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ : (Ideal (𝓞 K))⁰)

/-- Each of the two transforms may have extracted a different fixed
ideal.  Their exact contributions are common to all residual columns. -/
theorem two_product_locations
    (firstSign rowLog : ℝ) (F₁ F₂ I : Ideal (𝓞 K))
    (hF₁ : F₁ ≠ 0) (hF₂ : F₂ ≠ 0) (hI : I ≠ 0) :
    WithLp.toLp 2
      (-firstSign * Real.log (Ideal.absNorm (F₁ * I) : ℝ),
        rowLog - Real.log (Ideal.absNorm (F₂ * I) : ℝ)) =
      WithLp.toLp 2
          (-firstSign * Real.log (Ideal.absNorm F₁ : ℝ),
            rowLog - Real.log (Ideal.absNorm F₂ : ℝ)) +
        WithLp.toLp 2
          (-firstSign * Real.log (Ideal.absNorm I : ℝ),
            -Real.log (Ideal.absNorm I : ℝ)) := by
  simp only [map_mul, Nat.cast_mul,
    Real.log_mul (real_norm_ne_zero F₁ hF₁) (real_norm_ne_zero I hI),
    Real.log_mul (real_norm_ne_zero F₂ hF₂) (real_norm_ne_zero I hI)]
  change WithLp.toLp 2 _ = WithLp.toLp 2 _
  congr 1
  apply Prod.ext <;> dsimp <;> ring

/-- This form is used by the exact leaf binding after the two actual
whole-ideal recipes have been proved from their original occurrence
maps.  No Fourier or polynomial identity is an input. -/
theorem actual_product_locations
    (firstSign rowLog : ℝ) {k : ℕ} (i : AllocationColumn K k)
    (hleft : i.1.1 ≠ 0) (hright : i.1.2 ≠ 0)
    (I₁ I₂ F₁ F₂ : Ideal (𝓞 K)) (hF₁ : F₁ ≠ 0) (hF₂ : F₂ ≠ 0)
    (h₁ : I₁ = F₁ * allocationColumnIdeal i)
    (h₂ : I₂ = F₂ * allocationColumnIdeal i) :
    WithLp.toLp 2
      (-firstSign * Real.log (Ideal.absNorm I₁ : ℝ),
        rowLog - Real.log (Ideal.absNorm I₂ : ℝ)) =
      WithLp.toLp 2
          (-firstSign * Real.log (Ideal.absNorm F₁ : ℝ),
            rowLog - Real.log (Ideal.absNorm F₂ : ℝ)) +
        rawSourceLocation (plain firstSign) (plain firstSign) (prime firstSign) i := by
  have hi : allocationColumnIdeal i ≠ 0 :=
    mul_ne_zero (mul_ne_zero hleft hright)
      (Finset.prod_ne_zero_iff.mpr (fun j _ => (i.2 j).ne_bot))
  rw [rawLocation firstSign i hleft hright, h₁, h₂]
  exact two_product_locations firstSign rowLog F₁ F₂ _ hF₁ hF₂ hi

end CanonicalLiteralLocations

namespace SupportCartesianBranch

variable {k : ℕ} {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable {P : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch S₁ S₂ S P)

/-- The fixed ideal is computed from every original extracted
occurrence.  No restriction to a prime set or support surrogate is
made, and an empty prime product remains one. -/
def literalExtractedIdeal : Ideal (𝓞 K) :=
  b.plainExtract₁ * b.plainExtract₂ * ∏ j, b.slotExtract j

theorem reconstruct_literalIdeal (i : AllocationColumn K b.keep.card)
    (hi : i ∈ b.residualColumns) :
    allocationColumnIdeal (b.reconstruct i) =
      b.literalExtractedIdeal * allocationColumnIdeal i := by
  have hm := b.reconstruct_mem i hi
  have hp := Finset.mem_product.mp (Finset.mem_product.mp (b.original_subset hm)).1
  have hn : allocationColumnIdeal (b.reconstruct i) ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (b.plain₁_nonzero _ hp.1) (b.plain₂_nonzero _ hp.2))
      (Finset.prod_ne_zero_iff.mpr (fun j _ => ((b.reconstruct i).2 j).ne_bot))
  have hr := support_reconstruct (allocationColumnIdeal (b.reconstruct i)) hn P
  rw [b.extract_ideal (b.reconstruct i) hm,
    b.residual_ideal (b.reconstruct i) hm, b.residual_reconstruct i hi] at hr
  exact hr.symm

theorem literalExtractedIdeal_ne_zero : b.literalExtractedIdeal ≠ 0 := by
  have he := b.extract_ideal b.witness b.witness_mem
  exact he ▸ supportExtract_ne_zero (allocationColumnIdeal b.witness) P

/-- The common support extraction introduces exactly the common row
translation used by the real source.  Its ideal product is proved by
the occurrence reconstruction, rather than supplied by a caller. -/
theorem reconstructed_log_location (firstSign : ℝ)
    (i : AllocationColumn K b.keep.card) (hi : i ∈ b.residualColumns) :
    WithLp.toLp 2
      (-firstSign * Real.log (Ideal.absNorm (allocationColumnIdeal (b.reconstruct i)) : ℝ),
        -Real.log (Ideal.absNorm (allocationColumnIdeal (b.reconstruct i)) : ℝ)) =
      WithLp.toLp 2
          (-firstSign * Real.log (Ideal.absNorm b.literalExtractedIdeal : ℝ),
            -Real.log (Ideal.absNorm b.literalExtractedIdeal : ℝ)) +
        rawSourceLocation (CanonicalLiteralLocations.plain firstSign)
          (CanonicalLiteralLocations.plain firstSign)
          (CanonicalLiteralLocations.prime firstSign) i := by
  have hp := Finset.mem_product.mp (Finset.mem_product.mp hi).1
  have hleft : i.1.1 ≠ 0 := by
    obtain ⟨I, _, rfl⟩ := Finset.mem_image.mp hp.1
    exact supportResidual_ne_zero I P
  have hright : i.1.2 ≠ 0 := by
    obtain ⟨I, _, rfl⟩ := Finset.mem_image.mp hp.2
    exact supportResidual_ne_zero I P
  simpa only [zero_sub] using CanonicalLiteralLocations.actual_product_locations
    firstSign 0 i hleft hright _ _ b.literalExtractedIdeal b.literalExtractedIdeal
    b.literalExtractedIdeal_ne_zero b.literalExtractedIdeal_ne_zero
    (b.reconstruct_literalIdeal i hi) (b.reconstruct_literalIdeal i hi)

end SupportCartesianBranch
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralLocations.rawLocation
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralLocations.actual_product_locations
#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesianBranch.reconstruct_literalIdeal
#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesianBranch.reconstructed_log_location
