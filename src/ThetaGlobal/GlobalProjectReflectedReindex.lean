import ThetaGlobal.GlobalProjectReflectedDictionary
import ThetaGlobal.GlobalProjectDirectReindex
import ThetaGlobal.GlobalSupportReindex
import ThetaGlobal.ActualAnnularTransfer
import ThetaGlobal.GlobalDiagonalNorm

/-!
# Reindexing the actual reflected quotient series by the full literal index

Only nonzero support is required to be injective. Coverage is constructed
from the local digit table and actual exterior valuations; the complete
arithmetic dictionary then restores the enlarged index's zero terms.
The local class and positive norm are those of the same field frequency.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section

namespace ThetaGlobal.GlobalProjectReflectedReindex

open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources DedekindZetaZeroFree.OrbitExpansion
open DedekindZetaZeroFree.ThetaProfileHaarSheets
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.GlobalProjectReflectedLocalModel
open scoped NumberField Classical BigOperators

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)

local notation "Sf" => (R.A.Sf : Set (HeightOneSpectrum (𝓞 F)))
local notation "P" => ThetaBranch.ExteriorPrime R.A
local notation "k" => QuotientGroup.mk' R.A.sixthPowers

/-- Both actual norms have identical finite factors.  At every infinite
place the completion norm is its absolute value and the multiplicity is
two.  This direct comparison does not import the unrelated principal
Euler continuation through `ProbeUnits`. -/
theorem norm_diagonal (a : Fˣ) :
    R.A.norm (R.A.diagonal a) = sLocalProductNorm F Sf (sLocalFieldUnitDiagonal F Sf a) := by
  unfold SArithmeticData.norm sLocalProductNorm
  congr 1
  change (∏ w : InfinitePlace F, ‖algebraMap F w.Completion (a : F)‖ ^ 2) =
    mixedEmbedding.norm (mixedEmbedding F (a : F))
  exact GlobalDiagonalNorm.archimedean_product F R.A.complex_place a.val

theorem class_representative (Adata : ThetaArithmeticData F Sf)
    (d : MarkedDatum F Sf) (i : ReflectionIndex F Sf d) :
    GlobalProjectSheetProfiles.skeletonClass R
      (k (R.A.diagonal (GlobalActualFrequency.representative F Sf Adata d i))) =
      frequencyClass F Sf Adata d i := by
  apply (ProjectFiniteClass.skeletonAxiomClassEquiv R.A).injective
  rw [GlobalProjectSheetProfiles.skeletonClass, MulEquiv.apply_symm_apply,
    ← GlobalActualFrequency.localClass_representative F Sf Adata d i,
    ProjectFiniteClass.skeletonAxiomClassEquiv_diagonal]
  rfl

theorem norm_representative (Adata : ThetaArithmeticData F Sf)
    (hA : AllowedGeneratorInput F Sf Adata)
    (d : MarkedDatum F Sf) (i : ReflectionIndex F Sf d) (l : PositiveAxis) :
    ((ThetaSheetExactUnfolding.q R.A (GlobalActualFrequency.representative F Sf Adata d i) / l : PositiveAxis) : ℝ) =
      ReflectedLimitProject.argument F Sf d l.val⁻¹ i := by
  change R.A.norm (R.A.diagonal (GlobalActualFrequency.representative F Sf Adata d i)) / l.val = _
  rw [norm_diagonal, GlobalActualFrequency.norm_representative F Sf Adata hA]
  unfold ReflectedLimitProject.argument
  ring

variable (θ : HeckeCharacter F) (C : FiniteFixedSource.Source R θ)
  (L : FiniteLocalHighK.Input R θ C)

local notation "D" => C.projected.base.factorization

theorem reflectedTerm_eq_of_frequency_eq
    (hS : conductorPlaces F θ ⊆ R.A.Sf) (u : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (c : GlobalProjectWeightedDigits.Digits R m → ℂ)
    (hc : GlobalProjectWeightedDigits.ReindexInvariant R m c)
    (w : InfinitePlace F) (l : PositiveAxis) (a b : Fˣ)
    (h : (QuotientGroup.mk a : ThetaReflectionData.Frequency R.A) = QuotientGroup.mk b) :
    GlobalProjectOrbitEvaluation.reflectedTerm R θ C L u m c w l a =
      GlobalProjectOrbitEvaluation.reflectedTerm R θ C L u m c w l b := by
  let γ : ThetaReflectionData.rationalGamma R.A :=
    ⟨a / b, QuotientGroup.eq_iff_div_mem.mp h⟩
  have ha : a = γ.val * b := by simp [γ]
  have hs : GlobalProjectSignedExtraction.reverseCoefficient R D m c a =
      GlobalProjectSignedExtraction.reverseCoefficient R D m c b := by
    rw [ha]
    exact GlobalProjectOrbitCoefficients.reverseCoefficient_gamma R D m c hc b γ
  have hk : k (R.A.diagonal a) = k (R.A.diagonal b) :=
    congrArg (ThetaReflectionData.frequencyClass R.A) h
  have hq : ThetaSheetExactUnfolding.q R.A a = ThetaSheetExactUnfolding.q R.A b := by
    apply Subtype.ext
    exact congrArg (ThetaReflectionData.frequencyNorm R.A) h
  rw [GlobalProjectOrbitEvaluation.reflectedTerm, GlobalProjectOrbitEvaluation.reflectedTerm,
    hs, GlobalProjectDirectReindex.period_eq_of_frequency_eq R θ hS u a b h, hk, hq]

theorem admissible_of_actual_frequency (Adata : ThetaArithmeticData F Sf)
    (H : GlobalProjectLocalDigitTables.Input R D Adata)
    (d : MarkedDatum F Sf) (a : Fˣ)
    (ha : GlobalProjectSignedExtraction.reverseCoefficient R D (GlobalProjectMarkedSupport.row R d)
      (GlobalProjectMarkedSupport.weight R Adata d) a ≠ 0)
    (i : ReflectionIndex F Sf d)
    (hi : GlobalFrequency.Supported (GlobalIndexSupport.mandatory F Sf d)
      (GlobalIndexSupport.branch F Sf d i))
    (hfreq : GlobalActualReindex.frequency R.A Adata d i = QuotientGroup.mk a) :
    Admissible R d i := by
  have hz (p : P) (hp : p ∈ exteriorSupport F Sf d.moving) :
      primeExponents i.c.val p.val = 0 ∧ primeExponents i.n.val p.val = 0 := by
    have hac : p ∉ i.activeFrozen ∪ i.activeMarks := fun h =>
      (Finset.disjoint_left.mp (moving_active_disjoint R d i)) hp h
    have hfa : p ∉ i.activeFrozen := fun h => hac (Finset.mem_union_left _ h)
    have hv := ThetaBranch.CanonicalCoordinateProof.order_eq_of_frequency_eq R.A
      (GlobalActualFrequency.representative F Sf Adata d i) a hfreq p
    rw [GlobalActualReindex.order_representative R.A Adata d i p,
      GlobalProjectMarkedSupport.moving_order R Adata d D H a ha p hp,
      GlobalProjectMarkedSupport.moving_exponent R d p, if_pos hp] at hv
    simp only [GlobalFrequency.valuation, GlobalIndexSupport.branch, Finset.mem_coe,
      outside_a R d i p hfa, if_neg hac, Nat.cast_zero, Nat.cast_one] at hv
    omega
  exact ⟨hi, fun p hp => (hz p hp).1, fun p hp => (hz p hp).2⟩

end ThetaGlobal.GlobalProjectReflectedReindex

namespace ThetaGlobal.GlobalSkeletonReflected

open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources DedekindZetaZeroFree.ThetaProfileHaarSheets
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton
open ThetaGlobal.GlobalProjectReflectedLocalModel ThetaGlobal.GlobalProjectReflectedReindex
open scoped NumberField Classical BigOperators

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)
local notation "R" => thetaRecipe K c
local notation "Sf" => places K c
local notation "Adata" => arithmeticData K c

variable (θ : HeckeCharacter K) (C : FiniteFixedSource.Source (thetaRecipe K c) θ)
  (L : FiniteLocalHighK.Input (thetaRecipe K c) θ C)
  (H : GlobalProjectLocalDigitTables.Input (thetaRecipe K c) C.projected.base.factorization (arithmeticData K c))
  (hA : AllowedGeneratorInput K (places K c) (arithmeticData K c))
  (hS : conductorPlaces K θ ⊆ ((thetaRecipe K c)).A.Sf)

def literalTerm (d : MarkedDatum K Sf) (w : InfinitePlace K) (l : PositiveAxis)
    (i : ReflectionIndex K Sf d) : ℂ :=
  ReflectedArithmetic.reflectedCoefficient K Sf Adata d i θ *
    ActualAnnularTransfer.reflectedProfile R θ C L (QuotientGroup.mk d.rowUnit)
      (frequencyClass K Sf Adata d i) w (ReflectedLimitProject.argument K Sf d l.val⁻¹ i)

include H hA hS in
theorem representative_term (d : MarkedDatum K Sf) (w : InfinitePlace K)
    (l : PositiveAxis) (i : ReflectionIndex K Sf d) (hi : Admissible R d i) :
    GlobalProjectOrbitEvaluation.reflectedTerm R θ C L (QuotientGroup.mk d.rowUnit)
      (GlobalProjectMarkedSupport.row R d) (GlobalProjectMarkedSupport.weight R Adata d)
      w l (GlobalActualFrequency.representative K Sf Adata d i) =
      literalTerm K c θ C L d w l i := by
  have hcl : GlobalProjectSheetProfiles.skeletonClass R
      (QuotientGroup.mk' (R).A.sixthPowers
        ((R).A.diagonal (GlobalActualFrequency.representative K Sf Adata d i))) =
      frequencyClass K Sf Adata d i := class_representative R Adata d i
  rw [GlobalProjectOrbitEvaluation.reflectedTerm,
    thetaRecipe_reflected_coefficient K c θ hS C.projected.base.factorization H hA d i hi]
  simp only [hcl]
  unfold literalTerm ActualAnnularTransfer.reflectedProfile
  rw [dif_pos (ReflectedLimitProject.argument_pos K Sf d (inv_pos.mpr l.property) i)]
  congr 2
  apply Subtype.ext
  exact norm_representative R Adata hA d i l

include H hA hS in
theorem quotient_term (d : MarkedDatum K Sf) (w : InfinitePlace K)
    (l : PositiveAxis) (i : ReflectionIndex K Sf d) (hi : Admissible R d i) :
    GlobalProjectOrbitEvaluation.reflectedTerm R θ C L (QuotientGroup.mk d.rowUnit)
      (GlobalProjectMarkedSupport.row R d) (GlobalProjectMarkedSupport.weight R Adata d)
      w l (Quotient.out (GlobalActualReindex.frequency (R).A Adata d i)) =
      literalTerm K c θ C L d w l i := by
  rw [reflectedTerm_eq_of_frequency_eq R θ C L hS (QuotientGroup.mk d.rowUnit)
    (GlobalProjectMarkedSupport.row R d) (GlobalProjectMarkedSupport.weight R Adata d)
    (GlobalProjectMarkedSupport.weight_reindexInvariant R Adata d) w l _
    (GlobalActualFrequency.representative K Sf Adata d i)
    (Quotient.out_eq (GlobalActualReindex.frequency (R).A Adata d i))]
  exact representative_term K c θ C L H hA hS d w l i hi

theorem literalTerm_coefficient_nonzero (d : MarkedDatum K Sf) (w : InfinitePlace K)
    (l : PositiveAxis) (i : ReflectionIndex K Sf d)
    (hi : literalTerm K c θ C L d w l i ≠ 0) :
    ReflectedArithmetic.reflectedCoefficient K Sf Adata d i θ ≠ 0 := by
  exact (mul_ne_zero_iff.mp hi).1

theorem support_injective (d : MarkedDatum K Sf) (w : InfinitePlace K) (l : PositiveAxis) :
    Set.InjOn (GlobalActualReindex.frequency (R).A Adata d)
      (Function.support (literalTerm K c θ C L d w l)) := by
  intro i hi j hj he
  exact GlobalActualReindex.index_eq_of_frequency_eq (R).A Adata d θ i j
    (literalTerm_coefficient_nonzero K c θ C L d w l i hi)
    (literalTerm_coefficient_nonzero K c θ C L d w l j hj) he

include H hA hS in
theorem support_coverage (d : MarkedDatum K Sf) (w : InfinitePlace K) (l : PositiveAxis)
    (ξ : ThetaReflectionData.Frequency (R).A)
    (hξ : GlobalProjectOrbitEvaluation.reflectedTerm R θ C L (QuotientGroup.mk d.rowUnit)
      (GlobalProjectMarkedSupport.row R d) (GlobalProjectMarkedSupport.weight R Adata d)
      w l (Quotient.out ξ) ≠ 0) :
    ∃ i : ReflectionIndex K Sf d, literalTerm K c θ C L d w l i ≠ 0 ∧
      GlobalActualReindex.frequency (R).A Adata d i = ξ := by
  have ha : GlobalProjectSignedExtraction.reverseCoefficient R C.projected.base.factorization
      (GlobalProjectMarkedSupport.row R d) (GlobalProjectMarkedSupport.weight R Adata d)
      (Quotient.out ξ) ≠ 0 := by
    intro hz
    exact hξ (by simp [GlobalProjectOrbitEvaluation.reflectedTerm, hz])
  obtain ⟨i, hi, hf⟩ := GlobalProjectMarkedSupport.exists_index R Adata d
    C.projected.base.factorization H C.projected.base.exterior (Quotient.out ξ) ha
  have hai := admissible_of_actual_frequency R θ C Adata H d (Quotient.out ξ) ha i hi hf
  have hfi : GlobalActualReindex.frequency (R).A Adata d i = ξ := hf.trans (Quotient.out_eq ξ)
  refine ⟨i, ?_, hfi⟩
  rw [← quotient_term K c θ C L H hA hS d w l i hai, hfi]
  exact hξ

include H hA hS in
/-- Exact reflection-series reindexing on support, followed by restoration
of every zero term in the repository's full `ReflectionIndex`. -/
theorem reflected_sum_eq_literal (d : MarkedDatum K Sf) (w : InfinitePlace K) (l : PositiveAxis) :
    (∑' ξ : ThetaReflectionData.Frequency (R).A,
      GlobalProjectOrbitEvaluation.reflectedTerm R θ C L (QuotientGroup.mk d.rowUnit)
        (GlobalProjectMarkedSupport.row R d) (GlobalProjectMarkedSupport.weight R Adata d)
        w l (Quotient.out ξ)) =
      ∑' i : ReflectionIndex K Sf d, literalTerm K c θ C L d w l i := by
  apply GlobalSupportReindex.tsum_eq_of_supported_coordinates _ _
    (GlobalActualReindex.frequency (R).A Adata d)
    (support_injective K c θ C L d w l)
    (support_coverage K c θ C L H hA hS d w l)
  intro i hi
  exact quotient_term K c θ C L H hA hS d w l i
    (admissible_of_nonzero R Adata d i θ
      (literalTerm_coefficient_nonzero K c θ C L d w l i hi))

include H hA hS in
theorem reflected_norm_summable (d : MarkedDatum K Sf) (w : InfinitePlace K) (l : PositiveAxis)
    (hs : Summable (fun ξ : ThetaReflectionData.Frequency (R).A =>
      ‖GlobalProjectOrbitEvaluation.reflectedTerm R θ C L (QuotientGroup.mk d.rowUnit)
        (GlobalProjectMarkedSupport.row R d) (GlobalProjectMarkedSupport.weight R Adata d)
        w l (Quotient.out ξ)‖)) :
    Summable (fun i : ReflectionIndex K Sf d => ‖literalTerm K c θ C L d w l i‖) := by
  let f : ThetaReflectionData.Frequency (R).A → ℝ := fun ξ =>
    ‖GlobalProjectOrbitEvaluation.reflectedTerm R θ C L (QuotientGroup.mk d.rowUnit)
      (GlobalProjectMarkedSupport.row R d) (GlobalProjectMarkedSupport.weight R Adata d)
      w l (Quotient.out ξ)‖
  let g : ReflectionIndex K Sf d → ℝ := fun i => ‖literalTerm K c θ C L d w l i‖
  have he : HasSum f (∑' ξ, f ξ) ↔ HasSum g (∑' ξ, f ξ) := by
    apply hasSum_iff_hasSum_of_ne_zero_bij
      (fun i : Function.support g => GlobalActualReindex.frequency (R).A Adata d i.val)
    · intro i j h
      apply Subtype.ext
      exact support_injective K c θ C L d w l
        (norm_ne_zero_iff.mp i.property) (norm_ne_zero_iff.mp j.property) h
    · intro ξ hξ
      obtain ⟨i, hi, hf⟩ := support_coverage K c θ C L H hA hS d w l ξ
        (norm_ne_zero_iff.mp hξ)
      exact ⟨⟨i, norm_ne_zero_iff.mpr hi⟩, hf⟩
    · intro i
      exact congrArg norm (quotient_term K c θ C L H hA hS d w l i.val
        (admissible_of_nonzero R Adata d i.val θ
          (literalTerm_coefficient_nonzero K c θ C L d w l i.val
            (norm_ne_zero_iff.mp i.property))))
  exact (he.mp hs.hasSum).summable

end ThetaGlobal.GlobalSkeletonReflected
