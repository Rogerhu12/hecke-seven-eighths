import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8SourceFirstNorms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8SourceSecondCommonMass

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original first common pair, mask and residual-divisor sum

The first family is reindexed by its actual `FirstCauchyKey` equivalence.
Its finite phase and Cauchy orientation contribute only their fixed
cardinalities.  The literal right residual divisor pool is summed with
the density supplied by the proved second common sum.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.LargeSieve
open CommonSupportMass HeckePort.IdealMobiusDivisorSum
open HeckePort.Moments HeckePort.Moments.MobiusRegroup
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

local instance n8FirstMassCircleFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p}

namespace N8Source

theorem moebius_norm_le_one (I : Ideal (𝓞 K)) : ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖ ≤ 1 := by
  unfold UniqueFactorizationMonoid.moebius
  split_ifs <;> simp

theorem commonRadical_comm (I J : Ideal (𝓞 K)) :
    commonRadical I J = commonRadical J I := by
  simp only [commonRadical, Finset.inter_comm]

end N8Source

namespace PhysicalSource

def firstIndexWeight (source : PhysicalSource call p) : ℝ :=
  (1 / (Ideal.absNorm (commonRadical source.first.selected.val source.first.opposite.val) : ℝ)) *
    ‖(UniqueFactorizationMonoid.moebius source.first.residualDivisor.val : ℂ)‖ /
      (Ideal.absNorm source.first.residualDivisor.val : ℝ)

theorem firstIndexWeight_nonneg (source : PhysicalSource call p) :
    0 ≤ source.firstIndexWeight := by
  unfold firstIndexWeight
  positivity

end PhysicalSource

namespace FirstCauchyKey

def arithmeticWeight (key : FirstCauchyKey F) : ℝ :=
  (1 / (Ideal.absNorm (commonRadical key.1.val.1 key.1.val.2) : ℝ)) *
    ‖(UniqueFactorizationMonoid.moebius (FirstCauchyKey.residual key).val : ℂ)‖ /
      (Ideal.absNorm (FirstCauchyKey.residual key).val : ℝ)

end FirstCauchyKey

namespace FirstPresentation

variable (F : FirstPresentation call p)

def arithmeticMass : ℝ :=
  ∑ v : F.source.CommonLabel,
    (1 / (Ideal.absNorm (commonRadical v.val.1 v.val.2) : ℝ)) *
      ∑ D : ((F.source.block v).mask F.source.mask).powerset,
        ∑ S : divisorPool (F.source.pieces v D).rightData.columns
          (fun j => ((F.source.pieces v D).rightData.ideal j).val),
          ‖(UniqueFactorizationMonoid.moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)

theorem arithmeticMass_nonneg : 0 ≤ F.arithmeticMass := by
  apply Finset.sum_nonneg
  intro v _
  apply mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_nonneg
  intro D _
  exact Finset.sum_nonneg (fun _ _ => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))

private theorem sum_phase_side_arithmetic_weight (a b d : ℝ) :
    (∑ _chi : (PUnit.{1} × PUnit.{1}) →* Circle, ∑ _side : Bool, a * b / d) =
      ((Fintype.card ((PUnit.{1} × PUnit.{1}) →* Circle) : ℝ) * 2) * (a * (b / d)) := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul,
    Nat.cast_ofNat]
  ring

theorem cauchyKey_sum :
    (∑ key : FirstCauchyKey F, FirstCauchyKey.arithmeticWeight key) =
      ((Fintype.card ((PUnit.{1} × PUnit.{1}) →* Circle) : ℝ) * 2) *
        F.arithmeticMass := by
  simp only [FirstCauchyKey, Fintype.sum_sigma, Fintype.sum_prod_type,
    FirstCauchyKey.arithmeticWeight, FirstCauchyKey.residual,
    arithmeticMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro D _
  apply Finset.sum_congr rfl
  intro S _
  exact sum_phase_side_arithmetic_weight
    (1 / (Ideal.absNorm (commonRadical v.val.1 v.val.2) : ℝ))
    ‖(UniqueFactorizationMonoid.moebius S.val : ℂ)‖ (Ideal.absNorm S.val : ℝ)

theorem mask_card_le_divisorCount (hF : F.Realizes) (v : F.source.CommonLabel) :
    ((F.source.block v).mask F.source.mask).powerset.card ≤ idealDivisorCount v.val.1 := by
  have hD : v.val.1 ≠ 0 := by
    rw [← (F.source.block v).common_left]
    exact (primePowerProduct (F.source.block v).primes
      (F.source.block v).leftMultiplicity).property.1
  have hprimes : 2 ^ (F.source.block v).primeCount ≤ idealDivisorCount v.val.1 := by
    simpa only [Finset.card_powerset, Finset.card_univ, Fintype.card_fin] using
      (F.source.block v).originalCommonPrimeData.powerset_card_le_divisorCount hD
  have hmask := (F.source.block v).mask_card_le F.source.mask
  rw [hF.mask, Finset.card_empty, zero_add] at hmask
  rw [Finset.card_powerset, hF.mask]
  exact (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hmask).trans hprimes

end FirstPresentation

namespace FirstCauchyFamily

variable (family : FirstCauchyFamily F)

def firstIndexMass : ℝ := ∑ i, (family.source i).firstIndexWeight

theorem firstIndexWeight_eq_key (hf : family.Realizes) (i : Fin family.count) :
    (family.source i).firstIndexWeight = FirstCauchyKey.arithmeticWeight (family.index i) := by
  have hswap (side : Bool) (I J : Ideal (𝓞 K)) :
      commonRadical (if side then J else I) (if side then I else J) =
        commonRadical I J := by
    cases side with
    | false => rfl
    | true => exact N8Source.commonRadical_comm J I
  have hrad :
      commonRadical (family.source i).first.selected.val (family.source i).first.opposite.val =
        commonRadical (family.index i).1.val.1 (family.index i).1.val.2 :=
    (congrArg₂ commonRadical (hf.selected i) (hf.opposite i)).trans
      (hswap (FirstCauchyKey.side (family.index i))
        (family.index i).1.val.1 (family.index i).1.val.2)
  exact congrArg₂ (fun radical divisor : Ideal (𝓞 K) =>
    (1 / (Ideal.absNorm radical : ℝ)) *
      ‖(UniqueFactorizationMonoid.moebius divisor : ℂ)‖ / (Ideal.absNorm divisor : ℝ))
    hrad (hf.residual i)

theorem firstIndexMass_eq (hf : family.Realizes) :
    family.firstIndexMass =
      ((Fintype.card ((PUnit.{1} × PUnit.{1}) →* Circle) : ℝ) * 2) * F.arithmeticMass := by
  apply (Fintype.sum_equiv family.index _ _
    (fun i => family.firstIndexWeight_eq_key hf i)).trans
  exact F.cauchyKey_sum

end FirstCauchyFamily

namespace N8Source

theorem original_first_arithmetic_mass (c : TargetContext K) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (call : Call c) (input : ProfileInput call),
      normThreshold c call.frame ≤ call.base →
      ∀ (p : SourceParameters c) (F : FirstPresentation call p), F.Realizes →
        F.arithmeticMass ≤ C * call.base ^ ε := by
  let δ : ℝ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨A, hA, hdiv⟩ := ideal_inverse_norm_subpower (K := K)
    (columnExponent c) δ (columnExponent_pos c).le hδ
  obtain ⟨D, hD, hmask⟩ := support_tuple_multiplicity_subpower (K := K)
    1 (columnExponent c) δ (columnExponent_pos c).le hδ
  obtain ⟨H, hH, hcommon⟩ := pair_harmonic_mass (K := K)
    (columnExponent c) δ (columnExponent_pos c).le hδ
  refine ⟨D * A * H, by positivity, ?_⟩
  intro call input large p F hF
  have hbase_pos : 0 < call.base := call.base_pos
  have hnorm (v : F.source.CommonLabel) :
      (Ideal.absNorm v.val.1 : ℝ) ≤ call.base ^ columnExponent c ∧
        (Ideal.absNorm v.val.2 : ℝ) ≤ call.base ^ columnExponent c :=
    commonSupportPool_norm _ _ _ _ (fun j _ => (F.source.ideal j).property.1)
      (fun j _ => (F.source.ideal j).property.1) _
      (first_source_norm input large F hF) (first_source_norm input large F hF) _ v.property
  have hdivSum (v : F.source.CommonLabel)
      (D : ((F.source.block v).mask F.source.mask).powerset) :
      (∑ S : divisorPool (F.source.pieces v D).rightData.columns
        (fun j => ((F.source.pieces v D).rightData.ideal j).val),
        ‖(UniqueFactorizationMonoid.moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) ≤ A * call.base ^ δ := by
    refine (Finset.sum_coe_sort
      (divisorPool (F.source.pieces v D).rightData.columns
        (fun j => ((F.source.pieces v D).rightData.ideal j).val))
      (fun S : Ideal (𝓞 K) =>
        ‖(UniqueFactorizationMonoid.moebius S : ℂ)‖ / (Ideal.absNorm S : ℝ))).trans_le ?_
    apply (Finset.sum_le_sum (fun S hS =>
      div_le_div_of_nonneg_right (moebius_norm_le_one S) (Nat.cast_nonneg _))).trans
    apply hdiv call.base call.domain.scale.le
    · intro S hS
      obtain ⟨j, _, hSj⟩ := Finset.mem_biUnion.mp hS
      have hj := ((F.source.pieces v D).rightData.ideal j).property.1
      exact ne_zero_of_dvd_ne_zero hj ((mem_idealDivisors hj).mp hSj)
    · intro S hS
      exact (FirstCauchyKey.residual_norm
        (F := F) ⟨v, D, ⟨S, hS⟩, 1, false⟩ input large hF)
  let M : ℝ := D * A * call.base ^ (2 * δ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hinner (v : F.source.CommonLabel) :
      (∑ mask : ((F.source.block v).mask F.source.mask).powerset,
        ∑ S : divisorPool (F.source.pieces v mask).rightData.columns
          (fun j => ((F.source.pieces v mask).rightData.ideal j).val),
          ‖(UniqueFactorizationMonoid.moebius S.val : ℂ)‖ / (Ideal.absNorm S.val : ℝ)) ≤ M := by
    have hc : (((F.source.block v).mask F.source.mask).powerset.card : ℝ) ≤
        D * call.base ^ δ := by
      have h : (((F.source.block v).mask F.source.mask).powerset.card : ℝ) ≤
          (idealDivisorCount v.val.1 : ℝ) :=
        Nat.cast_le.mpr (F.mask_card_le_divisorCount hF v)
      have h' : (idealDivisorCount v.val.1 : ℝ) ≤ D * call.base ^ δ := by
        simpa only [pow_one] using hmask call.base call.domain.scale.le _ (hnorm v).1
      exact h.trans h'
    calc
      _ ≤ ∑ _mask : ((F.source.block v).mask F.source.mask).powerset,
          A * call.base ^ δ := Finset.sum_le_sum (fun mask _ => hdivSum v mask)
      _ = (((F.source.block v).mask F.source.mask).powerset.card : ℝ) *
          (A * call.base ^ δ) := by simp
      _ ≤ (D * call.base ^ δ) * (A * call.base ^ δ) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = M := by
        dsimp only [M]
        rw [show 2 * δ = δ + δ by ring, Real.rpow_add call.base_pos]
        ring
  have hfirst : (∑ v : F.source.CommonLabel,
      1 / (Ideal.absNorm (commonRadical v.val.1 v.val.2) : ℝ)) ≤ H * call.base ^ δ := by
    let pairs := commonSupportPool F.source.columns F.source.columns
      (fun j => (F.source.ideal j).val) (fun j => (F.source.ideal j).val)
    refine (Finset.sum_coe_sort pairs
      (fun DE : Ideal (𝓞 K) × Ideal (𝓞 K) =>
        1 / (Ideal.absNorm (commonRadical DE.1 DE.2) : ℝ))).trans_le ?_
    have h := hcommon call.base call.domain.scale.le (1 : Ideal (𝓞 K))
      squarefree_one one_ne_zero pairs
      (by
        intro DE hDE
        have hz := commonSupportPool_nonzero _ _ _ _ DE hDE
        exact ⟨hz.1, hz.2, commonSupportPool_support_eq _ _ _ _ DE hDE,
          one_dvd _, one_dvd _, Finset.empty_subset _⟩)
      (fun DE hDE => hnorm ⟨DE, hDE⟩)
    simpa only [map_one, Nat.cast_one, div_one] using h
  calc
    F.arithmeticMass ≤ ∑ v : F.source.CommonLabel,
        (1 / (Ideal.absNorm (commonRadical v.val.1 v.val.2) : ℝ)) * M :=
      Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hinner v)
        (one_div_nonneg.mpr (Nat.cast_nonneg _)))
    _ = M * (∑ v : F.source.CommonLabel,
        1 / (Ideal.absNorm (commonRadical v.val.1 v.val.2) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ ≤ M * (H * call.base ^ δ) := mul_le_mul_of_nonneg_left hfirst hM
    _ = (D * A * H) * call.base ^ ε := by
      dsimp only [M]
      have he : ε = 2 * δ + δ := by dsimp [δ]; ring
      rw [he, Real.rpow_add call.base_pos]
      ring

theorem original_first_index_mass (c : TargetContext K) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (call : Call c) (input : ProfileInput call),
      normThreshold c call.frame ≤ call.base →
      ∀ (p : SourceParameters c) (F : FirstPresentation call p), F.Realizes →
      ∀ family : FirstCauchyFamily F, family.Realizes →
        family.firstIndexMass ≤ C * call.base ^ ε := by
  obtain ⟨C, hC, hmass⟩ := original_first_arithmetic_mass c ε hε
  have hphase : 0 < (Fintype.card ((PUnit.{1} × PUnit.{1}) →* Circle) : ℝ) := by
    exact_mod_cast (Fintype.card_pos :
      0 < Fintype.card ((PUnit.{1} × PUnit.{1}) →* Circle))
  refine ⟨((Fintype.card ((PUnit.{1} × PUnit.{1}) →* Circle) : ℝ) * 2) * C,
    by positivity, ?_⟩
  intro call input large p F hF family hf
  have hbase_pos : 0 < call.base := call.base_pos
  rw [family.firstIndexMass_eq hf]
  exact (mul_le_mul_of_nonneg_left (hmass call input large p F hF)
    (by positivity)).trans_eq (by ring)

end N8Source
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstCauchyFamily.firstIndexMass_eq
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8Source.original_first_index_mass
