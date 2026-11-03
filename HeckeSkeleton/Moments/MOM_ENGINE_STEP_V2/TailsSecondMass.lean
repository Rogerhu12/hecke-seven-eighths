import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsOriginalMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsAnalytic

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual second tail mass from active physical columns

The second residue is the complete nonprimitive Gauss pair. Its norm is
bounded by the original product modulus, and its common-support gate
counts each active original pair exactly once. No column coefficient is
split into its centered rectangles.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton.Global HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

def emptyMaskNorm (c : TargetContext K) : ℝ :=
  (sIntegerElementNorm K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
    (sIntegerMaskGenerator K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
      ∅)).val

theorem emptyMaskNorm_pos (c : TargetContext K) : 0 < emptyMaskNorm c :=
  (sIntegerElementNorm K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
    (sIntegerMaskGenerator K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
      ∅)).property

def physicalActiveColumns (source : PhysicalSource call p) : Finset source.Column :=
  source.source.columns.filter (fun i => source.source.coefficient i ≠ 0)

def secondActivePairs (source : SecondSource call p) :
    Finset (source.CommonLabel × (source.physical.Column × source.physical.Column)) :=
  (firstZeroPairs source.physical.source.columns source.physical.source.columns
    source.physical.source.ideal source.physical.source.ideal).filter
      (fun v => source.physical.source.coefficient v.2.1 ≠ 0 ∧
        source.physical.source.coefficient v.2.2 ≠ 0)

theorem secondActivePairs_card (source : SecondSource call p) :
    ((secondActivePairs source).card : ℝ) ≤
      ((physicalActiveColumns source.physical).card : ℝ) ^ 2 := by
  let G := source.physical.source
  have hsub : (secondActivePairs source).image Prod.snd ⊆
      physicalActiveColumns source.physical ×ˢ physicalActiveColumns source.physical := by
    intro ij hij
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hij
    have hvm := Finset.mem_filter.mp hv
    have hm := (mem_firstZeroPairs G.columns G.columns G.ideal G.ideal v).mp hvm.1
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨hm.1, hvm.2.1⟩,
        Finset.mem_filter.mpr ⟨hm.2.1, hvm.2.2⟩⟩
  have hinj : Set.InjOn Prod.snd (secondActivePairs source : Set
      (source.CommonLabel × (source.physical.Column × source.physical.Column))) := by
    intro v hv w hw h
    exact firstZeroPairs_projection_injective G.columns G.columns G.ideal G.ideal
      (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hw).1 h
  have hn := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_product] at hn
  simpa only [pow_two, Nat.cast_mul] using (Nat.cast_le (α := ℝ)).mpr hn

theorem second_gram_seminorm_le (source : SecondSource call p) (hs : source.Realizes)
    (orders : Finset (ℕ × ℕ)) (amplitude : ℝ) (hamp : 0 ≤ amplitude)
    (hcoefficient : ∀ i ∈ source.physical.source.columns,
      ‖source.physical.source.coefficient i‖ ≤ amplitude)
    (i : source.physical.Column) (hi : i ∈ source.physical.source.columns)
    (j : source.physical.Column) (hj : j ∈ source.physical.source.columns) :
    orders.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
        ((source.physical.source.coefficient i *
          star (source.physical.source.coefficient j)) • source.stage.profile) ≤
      amplitude ^ 2 * originalKernelSeminorm c orders := by
  rw [map_smul_eq_mul, norm_mul, norm_star, hs.profile]
  apply mul_le_mul_of_nonneg_right _ (originalKernelSeminorm_nonneg c orders)
  simpa only [pow_two] using
    mul_le_mul (hcoefficient i hi) (hcoefficient j hj) (norm_nonneg _) hamp

theorem second_pair_modulus_le (source : SecondSource call p)
    (X : ℝ) (hX : 0 ≤ X)
    (hideal : ∀ i ∈ physicalActiveColumns source.physical,
      (Arithmetic.data c).exteriorNorm (source.physical.source.ideal i) ≤ X)
    (v : source.CommonLabel) (i : source.physical.Column)
    (hi : i ∈ (source.stage.sources v).leftColumns)
    (j : source.physical.Column) (hj : j ∈ (source.stage.sources v).rightColumns)
    (hci : source.physical.source.coefficient i ≠ 0)
    (hcj : source.physical.source.coefficient j ≠ 0) :
    (sIntegerElementNorm K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨((source.stage.sources v).pairs i j).modulus,
        ((source.stage.sources v).pairs i j).modulus_ne_zero⟩).val ≤ X ^ 2 := by
  have hi' : i ∈ source.physical.source.columns :=
    (Finset.mem_filter.mp hi).1
  have hj' : j ∈ source.physical.source.columns :=
    (Finset.mem_filter.mp hj).1
  calc
    _ = (Ideal.absNorm ((source.physical.source.ideal i).val *
        (source.physical.source.ideal j).val) : ℝ) :=
      (source.block v).second_modulus_norm (Arithmetic.units_are_sixth c)
        (Arithmetic.different c) (Arithmetic.context c)
        source.physical.source.columns source.physical.source.columns
        (fun a b => (source.physical.source.coefficient a *
          star (source.physical.source.coefficient b)) • source.stage.profile) i hi j hj
    _ ≤ _ := by
      rw [map_mul, Nat.cast_mul]
      change (Arithmetic.data c).exteriorNorm (source.physical.source.ideal i) *
        (Arithmetic.data c).exteriorNorm (source.physical.source.ideal j) ≤ X ^ 2
      simpa only [pow_two] using
        mul_le_mul (hideal i (Finset.mem_filter.mpr ⟨hi', hci⟩))
          (hideal j (Finset.mem_filter.mpr ⟨hj', hcj⟩))
          ((Arithmetic.data c).exteriorNorm_pos _).le hX

theorem second_pair_truncationMass_le (source : SecondSource call p)
    (hs : source.Realizes) (X R : ℝ) (hX : 0 ≤ X)
    (hradius : source.stage.radius.val⁻¹ ≤ R)
    (hideal : ∀ i ∈ physicalActiveColumns source.physical,
      (Arithmetic.data c).exteriorNorm (source.physical.source.ideal i) ≤ X)
    (v : source.CommonLabel) (i : source.physical.Column)
    (hi : i ∈ (source.stage.sources v).leftColumns)
    (j : source.physical.Column) (hj : j ∈ (source.stage.sources v).rightColumns)
    (hci : source.physical.source.coefficient i ≠ 0)
    (hcj : source.physical.source.coefficient j ≠ 0) :
    ((source.stage.sources v).pairs i j).truncationMass
        source.stage.mask source.stage.radius ≤
      X ^ 2 * (firstTailFieldConstant K * emptyMaskNorm c * (R + X ^ 2)) := by
  have hm := second_pair_modulus_le source X hX hideal v i hi j hj hci hcj
  have hb := ((source.stage.sources v).pairs i j).truncationMass_le_residue_bound
    (X ^ 2) (sq_nonneg _) (fun x =>
      ((source.block v).second_residue_norm_le_modulus (Arithmetic.units_are_sixth c)
        (Arithmetic.different c) (Arithmetic.context c)
        (fun a b => (source.physical.source.coefficient a *
          star (source.physical.source.coefficient b)) • source.stage.profile) i j x).trans hm)
    source.stage.mask source.stage.radius
  apply hb.trans
  rw [hs.mask]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg X)
  apply mul_le_mul_of_nonneg_left (add_le_add hradius hm)
    (mul_nonneg firstTailFieldConstant_nonneg (emptyMaskNorm_pos c).le)

/-- A source with bounded active column count, original coefficient,
ideal norm and inverse radius has this literal complete-residue mass. -/
theorem second_rawTailMass_le (source : SecondSource call p) (hs : source.Realizes)
    (orders : Finset (ℕ × ℕ)) (N amplitude X R : ℝ)
    (hN : 0 ≤ N) (hamp : 0 ≤ amplitude) (hX : 0 ≤ X) (hR : 0 ≤ R)
    (hcount : ((physicalActiveColumns source.physical).card : ℝ) ≤ N)
    (hcoefficient : ∀ i ∈ source.physical.source.columns,
      ‖source.physical.source.coefficient i‖ ≤ amplitude)
    (hideal : ∀ i ∈ physicalActiveColumns source.physical,
      (Arithmetic.data c).exteriorNorm (source.physical.source.ideal i) ≤ X)
    (hradius : source.stage.radius.val⁻¹ ≤ R) :
    source.stage.rawTailMass orders ≤
      N ^ 2 * (amplitude ^ 2 * originalKernelSeminorm c orders) *
        (X ^ 2 * (firstTailFieldConstant K * emptyMaskNorm c * (R + X ^ 2))) := by
  let G := source.physical.source
  let profiles := fun i j => (G.coefficient i * star (G.coefficient j)) • source.stage.profile
  let P := firstZeroPairs G.columns G.columns G.ideal G.ideal
  let term := fun v : source.CommonLabel × (source.physical.Column × source.physical.Column) =>
    orders.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
        (profiles v.2.1 v.2.2) *
      ((source.block v.1).secondPair (Arithmetic.units_are_sixth c)
        (Arithmetic.different c) (Arithmetic.context c) profiles v.2.1 v.2.2).truncationMass
          source.stage.mask source.stage.radius
  have hsum : (∑ v ∈ P, term v) = ∑ v ∈ secondActivePairs source, term v := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro v hv hvnot
    have hz : G.coefficient v.2.1 = 0 ∨ G.coefficient v.2.2 = 0 := by
      by_cases hi : G.coefficient v.2.1 = 0
      · exact Or.inl hi
      · right
        by_contra hj
        exact hvnot (Finset.mem_filter.mpr ⟨hv, hi, hj⟩)
    have hprofile : profiles v.2.1 v.2.2 = 0 := by
      rcases hz with hi | hj
      · simp only [profiles, hi, zero_mul, zero_smul]
      · simp only [profiles, hj, star_zero, mul_zero, zero_smul]
    dsimp only [term]
    rw [hprofile, map_zero, zero_mul]
  let Amp := amplitude ^ 2 * originalKernelSeminorm c orders
  let Mass := X ^ 2 * (firstTailFieldConstant K * emptyMaskNorm c * (R + X ^ 2))
  have hAmp : 0 ≤ Amp := mul_nonneg (sq_nonneg _) (originalKernelSeminorm_nonneg c orders)
  have hMass : 0 ≤ Mass := mul_nonneg (sq_nonneg _)
    (mul_nonneg (mul_nonneg firstTailFieldConstant_nonneg (emptyMaskNorm_pos c).le)
      (add_nonneg hR (sq_nonneg _)))
  have hpoint (v) (hv : v ∈ secondActivePairs source) : term v ≤ Amp * Mass := by
    have hvm := Finset.mem_filter.mp hv
    have hm := (mem_firstZeroPairs G.columns G.columns G.ideal G.ideal v).mp hvm.1
    have hb := ((source.block v.1).mem_iff_label G.columns G.columns
      (commonSupportPool_support_eq G.columns G.columns
        (fun i => (G.ideal i).val) (fun j => (G.ideal j).val) v.1.val v.1.property) _ _).mpr hm
    have hmass := second_pair_truncationMass_le source hs X R hX hradius hideal
      v.1 v.2.1 hb.1 v.2.2 hb.2.1 hvm.2.1 hvm.2.2
    have hprofile := second_gram_seminorm_le source hs orders amplitude hamp
      hcoefficient v.2.1 hm.1 v.2.2 hm.2.1
    exact (mul_le_mul_of_nonneg_left hmass (apply_nonneg _ _)).trans
      (mul_le_mul_of_nonneg_right hprofile hMass)
  have hpairCount : ((secondActivePairs source).card : ℝ) ≤ N ^ 2 :=
    (secondActivePairs_card source).trans
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hcount 2)
  change secondBlockTailMass (Arithmetic.units_are_sixth c) (Arithmetic.different c)
    (Arithmetic.context c) G.columns G.columns G.ideal G.ideal source.block
    orders profiles source.stage.radius source.stage.mask ≤ _
  rw [secondBlockTailMass_eq_original_pairs]
  change (∑ v ∈ P, term v) ≤ _
  rw [hsum]
  calc
    _ ≤ ∑ _v ∈ secondActivePairs source, Amp * Mass := Finset.sum_le_sum hpoint
    _ = ((secondActivePairs source).card : ℝ) * (Amp * Mass) := by simp
    _ ≤ N ^ 2 * (Amp * Mass) :=
      mul_le_mul_of_nonneg_right hpairCount (mul_nonneg hAmp hMass)
    _ = _ := by ring

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.second_rawTailMass_le
