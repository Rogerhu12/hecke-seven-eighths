import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstZeroDiagonal
import HeckePort.CenteredMoment.Counting
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Actual common-block truncation budgets

The residue L1 mass is bounded on the complete finite quotient. Its
cardinality cancels the literal Poisson modulus denominator. The inverse
dual radius then cancels the mask-divisor norm; each divisor costs at most
the field constant times the sum of the inverse original radius and the
original modulus norm.

The number of mask divisors is bounded by the norm of the actual
squarefree mask through the Chinese remainder theorem. Original pairs
are counted once, using their unique common-support label and an
injective encoding by their whole ideal-factor tuple.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis UniqueFactorizationMonoid MeasureTheory
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open HeckePort.CenteredMomentCounting DedekindZetaZeroFree.LargeSieve

variable {K : Type} [Field K] [NumberField K]

section SinglePair

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- The only field normalization in the raw truncation mass. -/
def firstTailFieldConstant (K : Type) [Field K] [NumberField K] : ℝ :=
  ‖(((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K /
    Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ)‖

theorem firstTailFieldConstant_nonneg : 0 ≤ firstTailFieldConstant K := norm_nonneg _

variable [IsPrincipalIdealRing
  (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

/-- Every Boolean choice of actual mask primes gives a different residue
class by CRT, so the number of squarefree divisors is at most the genuine
mask-generator norm. This includes the empty mask. -/
theorem mask_powerset_card_le_generator_norm
    (M : Finset (HeightOneSpectrum OS)) :
    (M.powerset.card : ℝ) ≤
      (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) M)).val := by
  letI : IsDedekindDomain OS :=
    sIntegerOrbitMask_isDedekindDomain K (S : Set (HeightOneSpectrum (𝓞 K)))
  let δ := sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) M
  letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K)))
    δ.val δ.property
  letI := Fintype.ofFinite (OS ⧸ Ideal.span ({δ.val} : Set OS))
  have hspan : Ideal.span ({δ.val} : Set OS) = IdealMobiusMask.primeProduct M := by
    ext x
    rw [Ideal.mem_span_singleton]
    exact IdealMobiusMask.maskGenerator_dvd_iff M x
  have hprod : IdealMobiusMask.primeProduct M = ⨅ p : M, p.val.asIdeal := by
    simp only [IdealMobiusMask.primeProduct_eq_iInf, iInf_subtype]
  have hcop : Pairwise (fun p q : M => IsCoprime p.val.asIdeal q.val.asIdeal) := by
    intro p q hpq
    exact IdealMobiusMask.pairwise_coprime_primeIdeals M p.property q.property
      (fun he => hpq (Subtype.ext he))
  let e := (Ideal.quotEquivOfEq (hspan.trans hprod)).trans
    (Ideal.quotientInfRingEquivPiQuotient (fun p : M => p.val.asIdeal) hcop)
  let encode : (M → Bool) → OS ⧸ Ideal.span ({δ.val} : Set OS) :=
    fun f => e.symm (fun p => if f p then 1 else 0)
  have hinj : Function.Injective encode := by
    intro f g he
    have hfg : (fun p : M => if f p then (1 : OS ⧸ p.val.asIdeal) else 0) =
        (fun p : M => if g p then (1 : OS ⧸ p.val.asIdeal) else 0) := by
      simpa only [encode, RingEquiv.apply_symm_apply] using congrArg e he
    funext p
    have hp := congrFun hfg p
    cases hf : f p <;> cases hg : g p <;> simp_all
  have hc := Nat.card_le_card_of_injective encode hinj
  have hc' : (M.powerset.card : ℝ) ≤
      (Nat.card (OS ⧸ Ideal.span ({δ.val} : Set OS)) : ℝ) := by
    exact_mod_cast (by simpa [Finset.card_powerset, Nat.card_eq_fintype_card] using hc)
  exact hc'.trans_eq
    (natCard_sIntegerPrincipalResidue_eq_productNorm
      K (S : Set (HeightOneSpectrum (𝓞 K))) δ.val δ.property)

theorem ParentPeriodicPair.residueL1_norm_le_card
    (p : ParentPeriodicPair K S Γ) (hres : ∀ x, ‖p.residue x‖ ≤ 1) (δ : OS) :
    sIntegerPeriodicResidueL1 K (S : Set (HeightOneSpectrum (𝓞 K)))
      p.modulus p.modulus_ne_zero
      (fun a => p.residue (Ideal.Quotient.mk _ δ * a)) ≤
        (Nat.card (OS ⧸ Ideal.span {p.modulus}) : ℝ) := by
  letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K)))
    p.modulus p.modulus_ne_zero
  letI := Fintype.ofFinite (OS ⧸ Ideal.span {p.modulus})
  change (∑ x : OS ⧸ Ideal.span {p.modulus}, ‖p.residue (Ideal.Quotient.mk _ δ * x)‖) ≤ _
  calc
    _ ≤ ∑ _x : OS ⧸ Ideal.span {p.modulus}, (1 : ℝ) :=
      Finset.sum_le_sum (fun x _ => hres _)
    _ = _ := by simp [Nat.card_eq_fintype_card]

/-- The actual Poisson denominator and inverse dual radius are charged
once. No norm of an individual divisor remains in this upper bound. -/
theorem ParentPeriodicPair.truncationMass_le_mask_norm
    (p : ParentPeriodicPair K S Γ) (hres : ∀ x, ‖p.residue x‖ ≤ 1)
    (M : Finset (HeightOneSpectrum OS)) (radius : {r : ℝ // 0 < r}) :
    p.truncationMass M radius ≤ firstTailFieldConstant K *
      (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) M)).val *
      (radius.val⁻¹ +
        (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
          ⟨p.modulus, p.modulus_ne_zero⟩).val) := by
  let N := sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
    ⟨p.modulus, p.modulus_ne_zero⟩
  have hterm (D : Finset (HeightOneSpectrum OS)) :
      ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ *
        ‖sIntegerMaskPoissonFactor K S p.modulus p.modulus_ne_zero radius
          (sIntegerMaskGenerator K _ D)‖ *
        sIntegerPeriodicResidueL1 K (S : Set (HeightOneSpectrum (𝓞 K)))
          p.modulus p.modulus_ne_zero
          (fun a => p.residue (Ideal.Quotient.mk _ (sIntegerMaskGenerator K _ D).val * a)) *
        (1 + (sIntegerMaskDualRadius K S p.modulus p.modulus_ne_zero radius
          (sIntegerMaskGenerator K _ D)).val⁻¹) ≤
        firstTailFieldConstant K * (radius.val⁻¹ + N.val) := by
    let δ := sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D
    let ρ := sIntegerMaskDilationRadius K S radius δ
    have hmu : ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ ≤ 1 := by
      unfold moebius
      split_ifs <;> simp
    have hL1 := p.residueL1_norm_le_card hres δ.val
    have hlast : 0 ≤ 1 +
        (sIntegerMaskDualRadius K S p.modulus p.modulus_ne_zero radius δ).val⁻¹ :=
      add_nonneg zero_le_one (inv_nonneg.mpr
        (sIntegerMaskDualRadius K S p.modulus p.modulus_ne_zero radius δ).property.le)
    have hrho : radius.val ≤ ρ.val := by
      exact (mul_one radius.val).symm.trans_le
        (mul_le_mul_of_nonneg_left
          (one_le_sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) δ)
          radius.property.le)
    have hinv : ρ.val⁻¹ ≤ radius.val⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le radius.property hrho
    calc
      _ ≤ ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ *
          ‖sIntegerMaskPoissonFactor K S p.modulus p.modulus_ne_zero radius δ‖ *
          (Nat.card (OS ⧸ Ideal.span {p.modulus}) : ℝ) *
          (1 + (sIntegerMaskDualRadius K S p.modulus p.modulus_ne_zero radius δ).val⁻¹) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hL1 (mul_nonneg (norm_nonneg _) (norm_nonneg _))) hlast
      _ ≤ ‖sIntegerMaskPoissonFactor K S p.modulus p.modulus_ne_zero radius δ‖ *
          (Nat.card (OS ⧸ Ideal.span {p.modulus}) : ℝ) *
          (1 + (sIntegerMaskDualRadius K S p.modulus p.modulus_ne_zero radius δ).val⁻¹) := by
        have hn := mul_le_mul_of_nonneg_right hmu
          (mul_nonneg (mul_nonneg
            (norm_nonneg (sIntegerMaskPoissonFactor K S p.modulus p.modulus_ne_zero radius δ))
            (Nat.cast_nonneg (Nat.card (OS ⧸ Ideal.span {p.modulus})))) hlast)
        simpa only [one_mul, mul_assoc] using hn
      _ = (ρ.val⁻¹ * firstTailFieldConstant K) * (1 + ρ.val * N.val) := by
        have hfactor : ‖sIntegerMaskPoissonFactor K S p.modulus p.modulus_ne_zero radius δ‖ *
            (Nat.card (OS ⧸ Ideal.span {p.modulus}) : ℝ) =
              ρ.val⁻¹ * firstTailFieldConstant K := by
          rw [natCard_sIntegerPrincipalResidue_eq_productNorm]
          change ‖(ρ.val : ℂ)⁻¹ *
              (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K /
                Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) * (N.val : ℂ)⁻¹‖ * N.val = _
          simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos ρ.property, abs_of_pos N.property]
          rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt N.property), mul_one] <;> rfl
        rw [hfactor]
        simp only [sIntegerMaskDualRadius, inv_inv, N, ρ]
      _ = firstTailFieldConstant K * (ρ.val⁻¹ + N.val) := by
        field_simp [ne_of_gt ρ.property]
        <;> ring
      _ ≤ firstTailFieldConstant K * (radius.val⁻¹ + N.val) :=
        mul_le_mul_of_nonneg_left (add_le_add hinv le_rfl)
          firstTailFieldConstant_nonneg
  calc
    _ ≤ ∑ _D ∈ M.powerset, firstTailFieldConstant K * (radius.val⁻¹ + N.val) :=
      Finset.sum_le_sum (fun D _ => hterm D)
    _ = firstTailFieldConstant K * (M.powerset.card : ℝ) * (radius.val⁻¹ + N.val) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mask_powerset_card_le_generator_norm M)
          firstTailFieldConstant_nonneg)
        (add_nonneg (inv_nonneg.mpr radius.property.le) N.property.le)

theorem ParentPeriodicPair.gated_truncationMass_zero
    (p : ParentPeriodicPair K S Γ) (P : Prop) [Decidable P] (hP : ¬P)
    (M : Finset (HeightOneSpectrum OS)) (radius : {r : ℝ // 0 < r}) :
    (p.gated P).truncationMass M radius = 0 := by
  simp [ParentPeriodicPair.truncationMass, sIntegerMaskedTruncationMass,
    ParentPeriodicPair.gated, hP, sIntegerPeriodicResidueL1]


end SinglePair

section WholeCounting

/-- A whole tuple is counted by its actual ideal coordinates. Every
coordinate divides its nonzero product, so its norm lies in the same
ordinary ideal ball. No count of original indices is an input. -/
theorem whole_ideal_tuple_card {α : Type*} {k : ℕ}
    (indices : Finset α) (factors : α → Fin k → Ideal (𝓞 K))
    (hinj : Set.InjOn factors (indices : Set α))
    (X : ℝ) (hX : 1 ≤ X)
    (hzero : ∀ a ∈ indices, PowerfulDiagonal.tupleIdeal (factors a) ≠ 0)
    (hnorm : ∀ a ∈ indices,
      (Ideal.absNorm (PowerfulDiagonal.tupleIdeal (factors a)) : ℝ) ≤ X) :
    (indices.card : ℝ) ≤ (idealCountConstant K * X) ^ k := by
  let ball := boundedNormIdeals K X
  have hball : (ball.card : ℝ) ≤ idealCountConstant K * X :=
    card_le_idealCountConstant K ball X hX (fun I hI => mem_boundedNormIdeals.mp hI)
  have hsub : indices.image factors ⊆ Fintype.piFinset (fun _ : Fin k => ball) := by
    intro f hf
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hf
    apply Fintype.mem_piFinset.mpr
    intro i
    apply mem_boundedNormIdeals.mpr
    have hd : factors a i ∣ PowerfulDiagonal.tupleIdeal (factors a) :=
      Finset.dvd_prod_of_mem (factors a) (Finset.mem_univ i)
    have hN0 : 0 < Ideal.absNorm (PowerfulDiagonal.tupleIdeal (factors a)) :=
      Nat.pos_of_ne_zero (fun he => hzero a ha (Ideal.absNorm_eq_zero_iff.mp he))
    have hn : Ideal.absNorm (factors a i) ≤
        Ideal.absNorm (PowerfulDiagonal.tupleIdeal (factors a)) :=
      Nat.le_of_dvd hN0 (map_dvd Ideal.absNorm hd)
    exact (Nat.cast_le.mpr hn).trans (hnorm a ha)
  have hc : ((indices.image factors).card : ℝ) ≤ (ball.card : ℝ) ^ k := by
    exact_mod_cast (by
      simpa only [Fintype.card_piFinset_const, Fintype.card_fin] using Finset.card_le_card hsub)
  rw [Finset.card_image_of_injOn hinj] at hc
  exact hc.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hball k)

variable {A : SArithmeticData K} {ι κ : Type*}

/-- Unique actual common-support labels preserve a whole tuple count. -/
theorem first_common_label_tuple_card
    (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    {k : ℕ} (factors : ι × κ → Fin k → Ideal (𝓞 K))
    (hinj : Set.InjOn factors (left ×ˢ right : Set (ι × κ)))
    (hproduct : ∀ ij ∈ left ×ˢ right, PowerfulDiagonal.tupleIdeal (factors ij) =
      (fullI ij.1).val * (fullJ ij.2).val)
    (X : ℝ) (hX : 1 ≤ X)
    (hnorm : ∀ ij ∈ left ×ˢ right,
      (Ideal.absNorm ((fullI ij.1).val * (fullJ ij.2).val) : ℝ) ≤ X) :
    ((firstZeroPairs left right fullI fullJ).card : ℝ) ≤
      (idealCountConstant K * X) ^ k := by
  have hij (v) (hv : v ∈ firstZeroPairs left right fullI fullJ) :
      v.2 ∈ left ×ˢ right := by
    have hm := (mem_firstZeroPairs left right fullI fullJ v).mp hv
    exact Finset.mem_product.mpr ⟨hm.1, hm.2.1⟩
  apply whole_ideal_tuple_card (firstZeroPairs left right fullI fullJ) (fun v => factors v.2)
    (fun v hv w hw he => firstZeroPairs_projection_injective left right fullI fullJ hv hw
      (hinj (Finset.mem_product.mp (hij v hv))
        (Finset.mem_product.mp (hij w hw)) he)) X hX
  · intro v hv
    rw [hproduct v.2 (hij v hv)]
    exact mul_ne_zero (fullI v.2.1).property.1 (fullJ v.2.2).property.1
  · intro v hv
    rw [hproduct v.2 (hij v hv)]
    exact hnorm v.2 (hij v hv)

/-- Exact regrouping on the genuine label calculated from each original
pair. The only required vanishing is the literal residual coprimality gate. -/
theorem first_common_label_sum
    (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (blocks : ∀ DE : FirstZeroLabel left right fullI fullJ,
      FirstCommonCharacterBlock fullI fullJ DE.val)
    (f : FirstZeroLabel left right fullI fullJ → ι → κ → ℝ)
    (hzero : ∀ DE i j,
      ¬IsCoprime ((blocks DE).leftResidual i).val ((blocks DE).rightResidual j).val →
        f DE i j = 0) :
    (∑ DE, ∑ i ∈ (blocks DE).leftColumns left, ∑ j ∈ (blocks DE).rightColumns right,
      f DE i j) = ∑ v ∈ firstZeroPairs left right fullI fullJ, f v.1 v.2.1 v.2.2 := by
  unfold firstZeroPairs
  rw [Finset.sum_filter, Finset.sum_product]
  simp only [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro DE _
  have hDE := commonSupportPool_support_eq left right
    (fun i => (fullI i).val) (fun j => (fullJ j).val) DE.val DE.property
  simp_rw [commonSupportLabel_eq_iff _ _ DE.val.1 DE.val.2 hDE]
  simp only [FirstCommonCharacterBlock.leftColumns,
    FirstCommonCharacterBlock.rightColumns, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hleft : supportExtract (fullI i).val (primeSupport DE.val.1) = DE.val.1
  · simp only [hleft, if_true, true_and]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hright : supportExtract (fullJ j).val (primeSupport DE.val.1) = DE.val.2
    · simp only [hright, if_true, true_and]
      by_cases hc : IsCoprime (supportResidual (fullI i).val (primeSupport DE.val.1))
          (supportResidual (fullJ j).val (primeSupport DE.val.1))
      · simp only [if_pos hc]
      · simp only [if_neg hc]
        exact hzero DE i j (by
          simpa only [(blocks DE).left_residual, (blocks DE).right_residual] using hc)
    · simp only [hright, if_false, false_and, Finset.sum_const_zero]
  · simp only [hleft, if_false, false_and, Finset.sum_const_zero]

end WholeCounting

section ActualTailMass

local notation "V" => mixedEmbedding.euclidean.mixedSpace K

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ₀ : Subgroup A.U}
variable (hΓ₀ : ∀ u : Γ₀, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable {ι κ : Type*}

/-- Exactly the coefficient of the uniform physical-cutoff error in the
first source theorem, summed over all genuine common-support blocks. -/
def firstBlockTailMass (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (blocks : ∀ DE : FirstZeroLabel left right fullI fullJ,
      FirstCommonCharacterBlock fullI fullJ DE.val)
    (seminorms : Finset (ℕ × ℕ)) (profiles : ι → κ → SchwartzMap V ℂ)
    (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R)) : ℝ :=
  ∑ DE, ∑ i ∈ (blocks DE).leftColumns left, ∑ j ∈ (blocks DE).rightColumns right,
    seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles i j) *
      ((blocks DE).pair hΓ₀ C profiles i j).truncationMass ((blocks DE).mask M) radius

/-- The actual rectangular source sum has one contribution per original
pair. The gate removes all rectangular cross-pairs with the wrong label. -/
theorem firstBlockTailMass_eq_original_pairs
    (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (blocks : ∀ DE : FirstZeroLabel left right fullI fullJ,
      FirstCommonCharacterBlock fullI fullJ DE.val)
    (seminorms : Finset (ℕ × ℕ)) (profiles : ι → κ → SchwartzMap V ℂ)
    (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R)) :
    firstBlockTailMass hΓ₀ C left right fullI fullJ blocks seminorms profiles radius M =
      ∑ v ∈ firstZeroPairs left right fullI fullJ,
        seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
          ((blocks v.1).pair hΓ₀ C profiles v.2.1 v.2.2).truncationMass
            ((blocks v.1).mask M) radius := by
  apply first_common_label_sum
  intro DE i j hc
  have hz : ((blocks DE).pair hΓ₀ C profiles i j).truncationMass
      ((blocks DE).mask M) radius = 0 := by
    unfold FirstCommonCharacterBlock.pair
    exact ParentPeriodicPair.gated_truncationMass_zero _ _ hc _ _
  rw [hz, mul_zero]

/-- A total actual tail-mass bound from original pointwise seminorm and
generator windows, with the number of original indices proved from their
whole factor encoding. No summed tail estimate is assumed. -/
theorem firstBlockTailMass_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (blocks : ∀ DE : FirstZeroLabel left right fullI fullJ,
      FirstCommonCharacterBlock fullI fullJ DE.val)
    (seminorms : Finset (ℕ × ℕ)) (profiles : ι → κ → SchwartzMap V ℂ)
    (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R))
    {k : ℕ} (factors : ι × κ → Fin k → Ideal (𝓞 K))
    (hinj : Set.InjOn factors (left ×ˢ right : Set (ι × κ)))
    (hproduct : ∀ ij ∈ left ×ˢ right, PowerfulDiagonal.tupleIdeal (factors ij) =
      (fullI ij.1).val * (fullJ ij.2).val)
    (X Amp maskBound modulusBound : ℝ) (hX : 1 ≤ X)
    (hAmp : 0 ≤ Amp) (hmaskBound : 0 ≤ maskBound) (hmodulusBound : 0 ≤ modulusBound)
    (hnorm : ∀ ij ∈ left ×ˢ right,
      (Ideal.absNorm ((fullI ij.1).val * (fullJ ij.2).val) : ℝ) ≤ X)
    (hprofile : ∀ v ∈ firstZeroPairs left right fullI fullJ,
      seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) ≤ Amp)
    (hmask : ∀ v ∈ firstZeroPairs left right fullI fullJ,
      (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ((blocks v.1).mask M))).val ≤
        maskBound)
    (hmodulus : ∀ v ∈ firstZeroPairs left right fullI fullJ,
      (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        ⟨((blocks v.1).pair hΓ₀ C profiles v.2.1 v.2.2).modulus,
          ((blocks v.1).pair hΓ₀ C profiles v.2.1 v.2.2).modulus_ne_zero⟩).val ≤ modulusBound) :
    firstBlockTailMass hΓ₀ C left right fullI fullJ blocks seminorms profiles radius M ≤
      (firstTailFieldConstant K * idealCountConstant K ^ k) *
        Amp * X ^ k * maskBound * (radius.val⁻¹ + modulusBound) := by
  have hcard := first_common_label_tuple_card left right fullI fullJ
    factors hinj hproduct X hX hnorm
  let bound := firstTailFieldConstant K * maskBound * (radius.val⁻¹ + modulusBound)
  have hbound : 0 ≤ bound := mul_nonneg
    (mul_nonneg firstTailFieldConstant_nonneg hmaskBound)
    (add_nonneg (inv_nonneg.mpr radius.property.le) hmodulusBound)
  have hpoint (v) (hv : v ∈ firstZeroPairs left right fullI fullJ) :
      seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
        ((blocks v.1).pair hΓ₀ C profiles v.2.1 v.2.2).truncationMass
          ((blocks v.1).mask M) radius ≤ Amp * bound := by
    have hm := ((blocks v.1).pair hΓ₀ C profiles v.2.1 v.2.2).truncationMass_le_mask_norm
      ((blocks v.1).residue_norm_le_one hΓ₀ C profiles v.2.1 v.2.2)
      ((blocks v.1).mask M) radius
    have hm' : ((blocks v.1).pair hΓ₀ C profiles v.2.1 v.2.2).truncationMass
        ((blocks v.1).mask M) radius ≤ bound := by
      apply hm.trans
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hmask v hv) firstTailFieldConstant_nonneg)
        (add_le_add le_rfl (hmodulus v hv))
        (add_nonneg (inv_nonneg.mpr radius.property.le)
          (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
            ⟨((blocks v.1).pair hΓ₀ C profiles v.2.1 v.2.2).modulus,
              ((blocks v.1).pair hΓ₀ C profiles v.2.1 v.2.2).modulus_ne_zero⟩).property.le)
        (mul_nonneg firstTailFieldConstant_nonneg hmaskBound)
    exact (mul_le_mul_of_nonneg_left hm' (apply_nonneg _ _)).trans
      (mul_le_mul_of_nonneg_right (hprofile v hv) hbound)
  rw [firstBlockTailMass_eq_original_pairs]
  calc
    _ ≤ ∑ _v ∈ firstZeroPairs left right fullI fullJ, Amp * bound :=
      Finset.sum_le_sum hpoint
    _ = ((firstZeroPairs left right fullI fullJ).card : ℝ) * (Amp * bound) := by simp
    _ ≤ (idealCountConstant K * X) ^ k * (Amp * bound) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg hAmp hbound)
    _ = _ := by
      rw [mul_pow]
      dsimp only [bound]
      ring


/-- The total exponent charged by the actual whole-index count and the
three pointwise windows. It is independent of the original columns. -/
def firstTailExponent (k : ℕ) (productExponent profileExponent maskExponent
    modulusExponent : ℝ) : ℝ :=
  productExponent * (k : ℝ) + profileExponent + maskExponent + modulusExponent

/-- A single physical cutoff exponent, chosen before all source data. -/
def firstTailCutoffExponent (L N decay : ℝ) : ℝ := max 0 (L + N) / (decay - 1)

theorem firstTailCutoffExponent_nonneg (L N decay : ℝ) (hdecay : 1 < decay) :
    0 ≤ firstTailCutoffExponent L N decay :=
  div_nonneg (le_max_left _ _) (sub_pos.mpr hdecay).le

theorem first_tail_cutoff_power (Z L N decay : ℝ) (hZ : 1 ≤ Z) (hdecay : 1 < decay) :
    (Z ^ firstTailCutoffExponent L N decay) ^ (1 - decay) * Z ^ L ≤ Z ^ (-N) := by
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have he : firstTailCutoffExponent L N decay * (1 - decay) = -max 0 (L + N) := by
    unfold firstTailCutoffExponent
    field_simp [ne_of_gt (sub_pos.mpr hdecay)]
    <;> ring
  rw [← Real.rpow_mul hZpos.le, ← Real.rpow_add hZpos, he]
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have hm := le_max_right (0 : ℝ) (L + N)
  linarith

/-- All fields are original pointwise data: a whole factor encoding, the
actual product norm, original Schwartz seminorms, and actual generator
norms. There is no total-tail or parent-energy premise. -/
structure FirstTailWindows (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (blocks : ∀ DE : FirstZeroLabel left right fullI fullJ,
      FirstCommonCharacterBlock fullI fullJ DE.val)
    (seminorms : Finset (ℕ × ℕ)) (profiles : ι → κ → SchwartzMap V ℂ)
    (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R))
    (k : ℕ) (Z productExponent profileExponent maskExponent modulusExponent Amp : ℝ) where
  base_ge_one : 1 ≤ Z
  productExponent_nonneg : 0 ≤ productExponent
  amplitude_nonneg : 0 ≤ Amp
  factors : ι × κ → Fin k → Ideal (𝓞 K)
  factors_injective : Set.InjOn factors (left ×ˢ right : Set (ι × κ))
  factor_product : ∀ ij ∈ left ×ˢ right, PowerfulDiagonal.tupleIdeal (factors ij) =
    (fullI ij.1).val * (fullJ ij.2).val
  product_norm : ∀ ij ∈ left ×ˢ right,
    (Ideal.absNorm ((fullI ij.1).val * (fullJ ij.2).val) : ℝ) ≤ Z ^ productExponent
  profile_seminorm : ∀ v ∈ firstZeroPairs left right fullI fullJ,
    seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) ≤
      Amp * Z ^ profileExponent
  mask_norm : ∀ v ∈ firstZeroPairs left right fullI fullJ,
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ((blocks v.1).mask M))).val ≤
      Z ^ maskExponent
  modulus_norm : ∀ v ∈ firstZeroPairs left right fullI fullJ,
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨((blocks v.1).pair hΓ₀ C profiles v.2.1 v.2.2).modulus,
        ((blocks v.1).pair hΓ₀ C profiles v.2.1 v.2.2).modulus_ne_zero⟩).val ≤
      Z ^ modulusExponent
  inverse_radius : radius.val⁻¹ ≤ Z ^ modulusExponent

namespace FirstTailWindows

variable {hΓ₀}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {left : Finset ι} {right : Finset κ}
variable {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {blocks : ∀ DE : FirstZeroLabel left right fullI fullJ,
  FirstCommonCharacterBlock fullI fullJ DE.val}
variable {seminorms : Finset (ℕ × ℕ)}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {M : Finset (HeightOneSpectrum A.R)}
variable {k : ℕ} {Z productExponent profileExponent maskExponent modulusExponent Amp : ℝ}

theorem power_bound
    (W : FirstTailWindows hΓ₀ C left right fullI fullJ blocks seminorms profiles radius M
      k Z productExponent profileExponent maskExponent modulusExponent Amp) :
    firstBlockTailMass hΓ₀ C left right fullI fullJ blocks seminorms profiles radius M ≤
      (2 * firstTailFieldConstant K * idealCountConstant K ^ k) * Amp *
        Z ^ firstTailExponent k productExponent profileExponent maskExponent modulusExponent := by
  have hZpos : 0 < Z := zero_lt_one.trans_le W.base_ge_one
  have hAmp : 0 ≤ Amp := W.amplitude_nonneg
  have hcount : 0 ≤ idealCountConstant K := zero_le_one.trans (one_le_idealCountConstant K)
  have hfield : 0 ≤ firstTailFieldConstant K := firstTailFieldConstant_nonneg
  have hraw := firstBlockTailMass_bound hΓ₀ C left right fullI fullJ blocks
    seminorms profiles radius M W.factors W.factors_injective W.factor_product
    (Z ^ productExponent) (Amp * Z ^ profileExponent)
    (Z ^ maskExponent) (Z ^ modulusExponent)
    (Real.one_le_rpow W.base_ge_one W.productExponent_nonneg)
    (mul_nonneg W.amplitude_nonneg (Real.rpow_nonneg hZpos.le _))
    (Real.rpow_nonneg hZpos.le _) (Real.rpow_nonneg hZpos.le _)
    W.product_norm W.profile_seminorm W.mask_norm W.modulus_norm
  have hadd : radius.val⁻¹ + Z ^ modulusExponent ≤ 2 * Z ^ modulusExponent := by
    linarith [W.inverse_radius]
  calc
    _ ≤ (firstTailFieldConstant K * idealCountConstant K ^ k) *
        (Amp * Z ^ profileExponent) * (Z ^ productExponent) ^ k *
        Z ^ maskExponent * (radius.val⁻¹ + Z ^ modulusExponent) := hraw
    _ ≤ (firstTailFieldConstant K * idealCountConstant K ^ k) *
        (Amp * Z ^ profileExponent) * (Z ^ productExponent) ^ k *
        Z ^ maskExponent * (2 * Z ^ modulusExponent) :=
      mul_le_mul_of_nonneg_left hadd (by positivity)
    _ = _ := by
      unfold firstTailExponent
      rw [Real.rpow_add hZpos, Real.rpow_add hZpos, Real.rpow_add hZpos,
        Real.rpow_mul_natCast hZpos.le]
      ring

/-- Uniform arbitrary-power tail saving with a single physical cutoff.
The explicit cutoff exponent depends only on the fixed window exponents,
the requested saving, and the previously chosen decay order. -/
theorem cutoff_budget
    (W : FirstTailWindows hΓ₀ C left right fullI fullJ blocks seminorms profiles radius M
      k Z productExponent profileExponent maskExponent modulusExponent Amp)
    (decay N Ctail : ℝ) (hdecay : 1 < decay) (hCtail : 0 ≤ Ctail) :
    let L := firstTailExponent k productExponent profileExponent maskExponent modulusExponent
    let X := Z ^ firstTailCutoffExponent L N decay
    1 ≤ X ∧
      Ctail * X ^ (1 - decay) *
        firstBlockTailMass hΓ₀ C left right fullI fullJ blocks seminorms profiles radius M ≤
          (Ctail * (2 * firstTailFieldConstant K * idealCountConstant K ^ k)) *
            Amp * Z ^ (-N) := by
  dsimp only
  refine ⟨Real.one_le_rpow W.base_ge_one (firstTailCutoffExponent_nonneg _ _ _ hdecay), ?_⟩
  have hZpos : 0 < Z := zero_lt_one.trans_le W.base_ge_one
  have hAmp : 0 ≤ Amp := W.amplitude_nonneg
  have hcount : 0 ≤ idealCountConstant K := zero_le_one.trans (one_le_idealCountConstant K)
  have hfield : 0 ≤ firstTailFieldConstant K := firstTailFieldConstant_nonneg
  let L := firstTailExponent k productExponent profileExponent maskExponent modulusExponent
  let X := Z ^ firstTailCutoffExponent L N decay
  change Ctail * X ^ (1 - decay) *
    firstBlockTailMass hΓ₀ C left right fullI fullJ blocks seminorms profiles radius M ≤ _
  calc
    _ ≤ Ctail * X ^ (1 - decay) *
        ((2 * firstTailFieldConstant K * idealCountConstant K ^ k) * Amp * Z ^ L) :=
      mul_le_mul_of_nonneg_left W.power_bound (mul_nonneg hCtail
        (Real.rpow_nonneg (Real.rpow_nonneg hZpos.le _) _))
    _ = (Ctail * (2 * firstTailFieldConstant K * idealCountConstant K ^ k)) * Amp *
        (X ^ (1 - decay) * Z ^ L) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (first_tail_cutoff_power Z L N decay W.base_ge_one hdecay) (by positivity)

end FirstTailWindows

/-- The budget is exactly the mass appearing in every actual finite first
source, regardless of the chosen common physical cutoff. -/
theorem first_source_tail_mass_eq
    (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (blocks : ∀ DE : FirstZeroLabel left right fullI fullJ,
      FirstCommonCharacterBlock fullI fullJ DE.val)
    (seminorms : Finset (ℕ × ℕ)) (profiles : ι → κ → SchwartzMap V ℂ)
    (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R))
    (X : ℝ) (hX : 1 ≤ X) :
    let sources := fun DE => (blocks DE).finiteSource hΓ₀ C left right profiles M radius X hX
    (∑ DE, ∑ i ∈ (sources DE).leftColumns, ∑ j ∈ (sources DE).rightColumns,
      seminorms.sup (schwartzSeminormFamily ℂ V ℂ) ((sources DE).pairs i j).profile *
        ((sources DE).pairs i j).truncationMass (sources DE).mask radius) =
      firstBlockTailMass hΓ₀ C left right fullI fullJ blocks seminorms profiles radius M := rfl

end ActualTailMass

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.mask_powerset_card_le_generator_norm
#print axioms HeckeSkeleton.Moments.EngineStep.ParentPeriodicPair.truncationMass_le_mask_norm
#print axioms HeckeSkeleton.Moments.EngineStep.whole_ideal_tuple_card
#print axioms HeckeSkeleton.Moments.EngineStep.firstBlockTailMass_bound
#print axioms HeckeSkeleton.Moments.EngineStep.FirstTailWindows.cutoff_budget

