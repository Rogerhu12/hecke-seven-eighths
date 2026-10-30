import HeckeGeneral.Analysis.MarkedThetaReflection
import Mathlib.RingTheory.Ideal.Operations

/-!
Actual arithmetic dictionary for GR-12 section comparison. The functions
below use the existing zero-extended sextic symbol, the actual generators,
and actual S-unit ratios. Reciprocity is cancelled only after proving the
common symbol nonzero on coprime ideals. Finite-avoidance separation and
the fixed-depth local mask are not assumed to have been constructed.
-/
set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.GramSectionReciprocity

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem idealSymbol_mul (D : ThetaArithmeticData K S) (I : ExteriorIdeal K S)
    (a b : S.integer K) :
    idealSymbol K S D I (a * b) = idealSymbol K S D I a * idealSymbol K S D I b :=
  sIntegerSexticIdealEvaluation_mul K S D.root6 D.primitive6 D.embedding _ _ _ _ a b

@[simp] theorem idealSymbol_one (D : ThetaArithmeticData K S) (I : ExteriorIdeal K S) :
    idealSymbol K S D I 1 = 1 :=
  sIntegerSexticIdealEvaluation_one K S D.root6 D.primitive6 D.embedding _ _ _ _

theorem residue_eq_zero_iff (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S)
    (a : S.integer K) :
    sIntegerSexticResidueMap K S p hp a = 0 ↔
      a ∈ p.asIdeal.map (algebraMap (𝓞 K) (S.integer K)) := by
  change (sIntegerResidueEquiv K S p.asIdeal
    (sIntegerSexticResidue_coprime K S p hp)).symm
      (Ideal.Quotient.mk _ a) = 0 ↔ _
  rw [← map_zero (sIntegerResidueEquiv K S p.asIdeal
    (sIntegerSexticResidue_coprime K S p hp)).symm,
    (sIntegerResidueEquiv K S p.asIdeal
      (sIntegerSexticResidue_coprime K S p hp)).symm.injective.eq_iff]
  exact Ideal.Quotient.eq_zero_iff_mem

theorem generators_isCoprime (D : ThetaArithmeticData K S)
    (I J : ExteriorIdeal K S) (hIJ : IsCoprime I.val.val J.val.val) :
    IsCoprime (D.generator I) (D.generator J) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [D.generator_span, D.generator_span, Ideal.isCoprime_iff_sup_eq,
    ← Ideal.map_sup, hIJ.sup_eq, Ideal.map_top]

theorem generator_residue_ne_zero (D : ThetaArithmeticData K S)
    (I J : ExteriorIdeal K S) (hIJ : IsCoprime I.val.val J.val.val)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p.asIdeal ∣ I.val.val) :
    sIntegerSexticResidueMap K S p (I.property p hp) (D.generator J) ≠ 0 := by
  letI : Field (𝓞 K ⧸ p.asIdeal) := Ideal.Quotient.field _
  have hI : D.generator I ∈ p.asIdeal.map (algebraMap (𝓞 K) (S.integer K)) := by
    apply Ideal.map_mono (f := algebraMap (𝓞 K) (S.integer K)) (Ideal.dvd_iff_le.mp hp)
    rw [← D.generator_span I]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hzero : sIntegerSexticResidueMap K S p (I.property p hp) (D.generator I) = 0 :=
    (residue_eq_zero_iff K S p (I.property p hp) _).mpr hI
  have hcop := (generators_isCoprime K S D I J hIJ).map
    (sIntegerSexticResidueMap K S p (I.property p hp))
  rw [hzero] at hcop
  exact (isCoprime_zero_left.mp hcop).ne_zero

theorem generator_symbol_norm (D : ThetaArithmeticData K S)
    (I J : ExteriorIdeal K S) (hIJ : IsCoprime I.val.val J.val.val) :
    ‖idealSymbol K S D I (D.generator J)‖ = 1 :=
  norm_sIntegerSexticIdealEvaluation_eq_one K S D.root6 D.primitive6 D.embedding
    _ _ _ _ _ (generator_residue_ne_zero K S D I J hIJ)

theorem generator_symbol_ne_zero (D : ThetaArithmeticData K S)
    (I J : ExteriorIdeal K S) (hIJ : IsCoprime I.val.val J.val.val) :
    idealSymbol K S D I (D.generator J) ≠ 0 := by
  intro h
  have hn := generator_symbol_norm K S D I J hIJ
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

/-- A ratio in the actual S-unit group, obtained solely from equal spans. -/
theorem exists_sectionRatio (D D₀ : ThetaArithmeticData K S) (I : ExteriorIdeal K S) :
    ∃ u : S.unit K,
      D.generator I = (S.unitEquivUnitsInteger K u).val * D₀.generator I := by
  have hspan : Ideal.span ({D₀.generator I} : Set (S.integer K)) =
      Ideal.span ({D.generator I} : Set (S.integer K)) := by
    rw [D₀.generator_span, D.generator_span]
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  refine ⟨(S.unitEquivUnitsInteger K).symm v, ?_⟩
  rw [MulEquiv.apply_symm_apply]
  exact hv.symm.trans (mul_comm _ _)

def sectionRatio (D D₀ : ThetaArithmeticData K S) (I : ExteriorIdeal K S) : S.unit K :=
  Classical.choose (exists_sectionRatio K S D D₀ I)

theorem sectionRatio_spec (D D₀ : ThetaArithmeticData K S) (I : ExteriorIdeal K S) :
    D.generator I = (S.unitEquivUnitsInteger K (sectionRatio K S D D₀ I)).val *
      D₀.generator I := Classical.choose_spec (exists_sectionRatio K S D D₀ I)

theorem idealSymbol_eq_of_root_embedding (D D₀ : ThetaArithmeticData K S)
    (hroot : D.root6 = D₀.root6) (hembedding : D.embedding = D₀.embedding)
    (I : ExteriorIdeal K S) (a : S.integer K) :
    idealSymbol K S D I a = idealSymbol K S D₀ I a := by
  unfold idealSymbol
  congr 1

/-- Dividing the TWO genuine reciprocity identities gives the actual
dictionary on coprime ideals. The common factor is proved nonzero; no
division is performed at a collision zero. -/
theorem sectionRatio_reciprocity (D D₀ : ThetaArithmeticData K S)
    (hroot : D.root6 = D₀.root6) (hembedding : D.embedding = D₀.embedding)
    (hallowed : AllowedGeneratorInput K S D)
    (hallowed₀ : AllowedGeneratorInput K S D₀)
    (I J : ExteriorIdeal K S) (hIJ : IsCoprime I.val.val J.val.val) :
    idealSymbol K S D₀ I
        (S.unitEquivUnitsInteger K (sectionRatio K S D D₀ J)).val =
      idealSymbol K S D₀ J
        (S.unitEquivUnitsInteger K (sectionRatio K S D D₀ I)).val := by
  have hrec := hallowed.reciprocity I J
  rw [idealSymbol_eq_of_root_embedding K S D D₀ hroot hembedding,
    idealSymbol_eq_of_root_embedding K S D D₀ hroot hembedding,
    sectionRatio_spec K S D D₀ J, sectionRatio_spec K S D D₀ I,
    idealSymbol_mul, idealSymbol_mul, ← hallowed₀.reciprocity I J] at hrec
  exact mul_right_cancel₀ (generator_symbol_ne_zero K S D₀ I J hIJ) hrec

end HeckeSkeleton.GramSectionReciprocity
