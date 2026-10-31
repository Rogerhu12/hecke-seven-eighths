import HeckeSkeleton.Moments.MOM_ENGINE_STEP.TailBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondZeroDiagonal
import Mathlib.Analysis.Normed.Ring.Finite

/-!
# Genuine whole-Gauss source tail budgets

The actual second source contains two complete Gauss sums. Their trivial
finite bounds are proved on every residue, including zero and nonunits:
the product is bounded by the norm of the actual product modulus.

For the canonical common-support blocks, that modulus norm is exactly
the norm of the two original full ideals. Thus the extra Gauss factor is
charged to the original whole-product window. The total tail then uses
the unique original common label and the proved whole tuple count.
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

/-- A comparison coefficient on precisely the same actual quotient. -/
def ParentPeriodicPair.unitResidue (p : ParentPeriodicPair K S Γ) :
    ParentPeriodicPair K S Γ :=
  { p with residue := fun _ => 1
           invariant := by intro u a; rfl }

theorem ParentPeriodicPair.residueL1_le_bound_card
    (p : ParentPeriodicPair K S Γ) (B : ℝ) (hres : ∀ x, ‖p.residue x‖ ≤ B) (δ : OS) :
    sIntegerPeriodicResidueL1 K (S : Set (HeightOneSpectrum (𝓞 K)))
      p.modulus p.modulus_ne_zero
      (fun a => p.residue (Ideal.Quotient.mk _ δ * a)) ≤
        B * (Nat.card (OS ⧸ Ideal.span {p.modulus}) : ℝ) := by
  letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K)))
    p.modulus p.modulus_ne_zero
  letI := Fintype.ofFinite (OS ⧸ Ideal.span {p.modulus})
  change (∑ x : OS ⧸ Ideal.span {p.modulus}, ‖p.residue (Ideal.Quotient.mk _ δ * x)‖) ≤ _
  calc
    _ ≤ ∑ _x : OS ⧸ Ideal.span {p.modulus}, B :=
      Finset.sum_le_sum (fun x _ => hres _)
    _ = _ := by simp [Nat.card_eq_fintype_card, mul_comm]

variable [IsPrincipalIdealRing OS]

/-- The raw actual truncation mass is linear in a pointwise residue bound.
Its quotient cardinality and Poisson denominator still cancel exactly. -/
theorem ParentPeriodicPair.truncationMass_le_residue_bound
    (p : ParentPeriodicPair K S Γ) (B : ℝ) (hB : 0 ≤ B)
    (hres : ∀ x, ‖p.residue x‖ ≤ B)
    (M : Finset (HeightOneSpectrum OS)) (radius : {r : ℝ // 0 < r}) :
    p.truncationMass M radius ≤ B * (firstTailFieldConstant K *
      (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) M)).val *
      (radius.val⁻¹ +
        (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
          ⟨p.modulus, p.modulus_ne_zero⟩).val)) := by
  have hcmp : p.truncationMass M radius ≤ B * p.unitResidue.truncationMass M radius := by
    unfold ParentPeriodicPair.truncationMass sIntegerMaskedTruncationMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro D hD
    let δ := sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D
    have hL1 := p.residueL1_le_bound_card B hres δ.val
    have hunit :
        sIntegerPeriodicResidueL1 K (S : Set (HeightOneSpectrum (𝓞 K)))
          p.modulus p.modulus_ne_zero (fun _ => (1 : ℂ)) =
          (Nat.card (OS ⧸ Ideal.span {p.modulus}) : ℝ) := by
      letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K)))
        p.modulus p.modulus_ne_zero
      letI := Fintype.ofFinite (OS ⧸ Ideal.span {p.modulus})
      change (∑ _x : OS ⧸ Ideal.span {p.modulus}, ‖(1 : ℂ)‖) = _
      simp [Nat.card_eq_fintype_card]
    dsimp only [ParentPeriodicPair.unitResidue]
    rw [hunit]
    have hlast : 0 ≤ 1 +
        (sIntegerMaskDualRadius K S p.modulus p.modulus_ne_zero radius δ).val⁻¹ :=
      add_nonneg zero_le_one (inv_nonneg.mpr
        (sIntegerMaskDualRadius K S p.modulus p.modulus_ne_zero radius δ).property.le)
    calc
      _ ≤ ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ *
          ‖sIntegerMaskPoissonFactor K S p.modulus p.modulus_ne_zero radius δ‖ *
          (B * (Nat.card (OS ⧸ Ideal.span {p.modulus}) : ℝ)) *
          (1 + (sIntegerMaskDualRadius K S p.modulus p.modulus_ne_zero radius δ).val⁻¹) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hL1 (mul_nonneg (norm_nonneg _) (norm_nonneg _))) hlast
      _ = _ := by ring
  exact hcmp.trans (mul_le_mul_of_nonneg_left
    (p.unitResidue.truncationMass_le_mask_norm
      (by intro x; simp [ParentPeriodicPair.unitResidue]) M radius) hB)

/-- Every complete Gauss column has the trivial full-quotient bound,
without primitive-character or unit-frequency restrictions. -/
theorem OrbitalGaussColumn.residue_norm_le_modulus
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (c : OrbitalGaussColumn K S Γ) (h : OS ⧸ Ideal.span {c.modulus}) :
    ‖c.residue hDiff h‖ ≤
      (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c.modulus, c.nonzero⟩).val := by
  letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K)))
    c.modulus c.nonzero
  letI := Fintype.ofFinite (OS ⧸ Ideal.span {c.modulus})
  unfold OrbitalGaussColumn.residue completeResidueGauss
  calc
    _ ≤ ∑ x : OS ⧸ Ideal.span {c.modulus},
        ‖c.character x *
          (actualSIntegerTrace K (S : Set (HeightOneSpectrum (𝓞 K))) hDiff).ψ c.modulus (h * x)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _x : OS ⧸ Ideal.span {c.modulus}, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [norm_mul, AddChar.norm_apply, mul_one]
      exact finiteCharacter_norm_le_one c.character x
    _ = (Nat.card (OS ⧸ Ideal.span {c.modulus}) : ℝ) := by
      simp [Nat.card_eq_fintype_card]
    _ = _ := natCard_sIntegerPrincipalResidue_eq_productNorm
      K (S : Set (HeightOneSpectrum (𝓞 K))) c.modulus c.nonzero

/-- The two complete Gauss bounds multiply to the actual product-modulus
norm, including every nonprimitive term of the genuine second source. -/
theorem OrbitalGaussColumn.pair_residue_norm_le_modulus
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (c d : OrbitalGaussColumn K S Γ) (φ : SchwartzMap V ℂ)
    (x : OS ⧸ Ideal.span {(c.pair hDiff d φ).modulus}) :
    ‖(c.pair hDiff d φ).residue x‖ ≤
      (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        ⟨(c.pair hDiff d φ).modulus, (c.pair hDiff d φ).modulus_ne_zero⟩).val := by
  change ‖c.residue hDiff _ * star (d.residue hDiff _)‖ ≤ _
  rw [norm_mul, norm_star]
  apply (mul_le_mul (c.residue_norm_le_modulus hDiff _) (d.residue_norm_le_modulus hDiff _)
    (norm_nonneg _)
    (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) ⟨c.modulus, c.nonzero⟩).property.le).trans_eq
  exact (sIntegerElementNorm_nonzeroMul K (S : Set (HeightOneSpectrum (𝓞 K)))
    ⟨c.modulus, c.nonzero⟩ ⟨d.modulus, d.nonzero⟩).symm

end SinglePair

section ActualSecond

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- The norm of any actual generator is its original ideal norm. No
chosen-generator equality or unit-normalization hypothesis is needed. -/
theorem generates_sIntegerElementNorm (I : A.Exterior) (a : A.R) (ha : A.Generates I a) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ⟨a, ha.1⟩).val =
      (Ideal.absNorm I.val : ℝ) := by
  rw [← natCard_sIntegerPrincipalResidue_eq_productNorm K
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) a ha.1, ha.2, A.exteriorResidue_card]

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

/-- Gating can only lower the actual pair-residue norm. -/
theorem FirstCommonCharacterBlock.second_residue_norm_le_modulus
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (profiles : ι → κ → SchwartzMap V ℂ) (i : ι) (j : κ)
    (x : A.R ⧸ Ideal.span {(b.secondPair hΓ hDiff C profiles i j).modulus}) :
    ‖(b.secondPair hΓ hDiff C profiles i j).residue x‖ ≤
      (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        ⟨(b.secondPair hΓ hDiff C profiles i j).modulus,
          (b.secondPair hΓ hDiff C profiles i j).modulus_ne_zero⟩).val := by
  unfold FirstCommonCharacterBlock.secondPair
  by_cases hc : IsCoprime (b.leftResidual i).val (b.rightResidual j).val
  · simp only [ParentPeriodicPair.gated, if_pos hc]
    exact OrbitalGaussColumn.pair_residue_norm_le_modulus hDiff _ _ _ x
  · simp only [ParentPeriodicPair.gated, if_neg hc, norm_zero]
    exact (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) _).property.le

/-- On retained original columns the second modulus has exactly the
original product norm, uniformly in its blockwise generator choices. -/
theorem FirstCommonCharacterBlock.second_modulus_norm
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (right : Finset κ) (profiles : ι → κ → SchwartzMap V ℂ)
    (i : ι) (hi : i ∈ b.leftColumns left) (j : κ) (hj : j ∈ b.rightColumns right) :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨(b.secondPair hΓ hDiff C profiles i j).modulus,
        (b.secondPair hΓ hDiff C profiles i j).modulus_ne_zero⟩).val =
      (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) := by
  change (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
    (sIntegerNonzeroMul K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨_, (b.secondLeft_generates C i).1⟩ ⟨_, (b.secondRight_generates C j).1⟩)).val = _
  rw [sIntegerElementNorm_nonzeroMul,
    generates_sIntegerElementNorm (b.secondLeftIdeal i) _ (b.secondLeft_generates C i),
    generates_sIntegerElementNorm (b.secondRightIdeal j) _ (b.secondRight_generates C j),
    b.secondLeftIdeal_eq left i hi, b.secondRightIdeal_eq right j hj,
    map_mul, Nat.cast_mul]

/-- The literal coefficient of the physical-cutoff error of the second
source, summed over the genuine common-support pool. -/
def secondBlockTailMass (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (blocks : ∀ DE : FirstZeroLabel left right fullI fullJ,
      FirstCommonCharacterBlock fullI fullJ DE.val)
    (seminorms : Finset (ℕ × ℕ)) (profiles : ι → κ → SchwartzMap V ℂ)
    (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R)) : ℝ :=
  ∑ DE, ∑ i ∈ (blocks DE).leftColumns left, ∑ j ∈ (blocks DE).rightColumns right,
    seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles i j) *
      ((blocks DE).secondPair hΓ hDiff C profiles i j).truncationMass M radius

/-- The second source has exactly one retained label for each original
whole pair; its coprimality gate removes the rectangular cross-pairs. -/
theorem secondBlockTailMass_eq_original_pairs
    (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (blocks : ∀ DE : FirstZeroLabel left right fullI fullJ,
      FirstCommonCharacterBlock fullI fullJ DE.val)
    (seminorms : Finset (ℕ × ℕ)) (profiles : ι → κ → SchwartzMap V ℂ)
    (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R)) :
    secondBlockTailMass hΓ hDiff C left right fullI fullJ blocks seminorms profiles radius M =
      ∑ v ∈ firstZeroPairs left right fullI fullJ,
        seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
          ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).truncationMass M radius := by
  apply first_common_label_sum
  intro DE i j hc
  have hz : ((blocks DE).secondPair hΓ hDiff C profiles i j).truncationMass M radius = 0 := by
    unfold FirstCommonCharacterBlock.secondPair
    exact ParentPeriodicPair.gated_truncationMass_zero _ _ hc _ _
  rw [hz, mul_zero]

/-- The extra cost of the two complete Gauss residues is one original
product norm. Both this factor and the modulus-radius factor are derived
from the original ideals, and the whole-index count is proved internally. -/
theorem secondBlockTailMass_bound
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
    (X Amp maskBound : ℝ) (hX : 1 ≤ X)
    (hAmp : 0 ≤ Amp) (hmaskBound : 0 ≤ maskBound)
    (hnorm : ∀ ij ∈ left ×ˢ right,
      (Ideal.absNorm ((fullI ij.1).val * (fullJ ij.2).val) : ℝ) ≤ X)
    (hprofile : ∀ v ∈ firstZeroPairs left right fullI fullJ,
      seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) ≤ Amp)
    (hmask :
      (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) M)).val ≤ maskBound) :
    secondBlockTailMass hΓ hDiff C left right fullI fullJ blocks seminorms profiles radius M ≤
      (firstTailFieldConstant K * idealCountConstant K ^ k) *
        Amp * X ^ (k + 1) * maskBound * (radius.val⁻¹ + X) := by
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hcard := first_common_label_tuple_card left right fullI fullJ
    factors hinj hproduct X hX hnorm
  let bound := X * (firstTailFieldConstant K * maskBound * (radius.val⁻¹ + X))
  have hbound : 0 ≤ bound := mul_nonneg hX0 (mul_nonneg
    (mul_nonneg firstTailFieldConstant_nonneg hmaskBound)
    (add_nonneg (inv_nonneg.mpr radius.property.le) hX0))
  have hpoint (v) (hv : v ∈ firstZeroPairs left right fullI fullJ) :
      seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
        ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).truncationMass M radius ≤
          Amp * bound := by
    have hmem := (mem_firstZeroPairs left right fullI fullJ v).mp hv
    have hblock := ((blocks v.1).mem_iff_label left right
      (commonSupportPool_support_eq left right (fun i => (fullI i).val)
        (fun j => (fullJ j).val) v.1.val v.1.property) _ _).mpr hmem
    let p := (blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2
    let N := sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨p.modulus, p.modulus_ne_zero⟩
    have hN : N.val ≤ X := by
      change (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        ⟨((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).modulus,
          ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).modulus_ne_zero⟩).val ≤ X
      rw [(blocks v.1).second_modulus_norm hΓ hDiff C left right profiles
        _ hblock.1 _ hblock.2.1]
      exact hnorm v.2 (Finset.mem_product.mpr ⟨hmem.1, hmem.2.1⟩)
    have hm := p.truncationMass_le_residue_bound N.val N.property.le
      ((blocks v.1).second_residue_norm_le_modulus hΓ hDiff C profiles v.2.1 v.2.2)
      M radius
    have hm' : p.truncationMass M radius ≤ bound := by
      apply hm.trans
      apply mul_le_mul hN
      · exact mul_le_mul
          (mul_le_mul_of_nonneg_left hmask firstTailFieldConstant_nonneg)
          (add_le_add_left hN _)
          (add_nonneg (inv_nonneg.mpr radius.property.le) N.property.le)
          (mul_nonneg firstTailFieldConstant_nonneg hmaskBound)
      · exact mul_nonneg
          (mul_nonneg firstTailFieldConstant_nonneg
            (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
              (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) M)).property.le)
          (add_nonneg (inv_nonneg.mpr radius.property.le) N.property.le)
      · exact hX0
    exact (mul_le_mul_of_nonneg_left hm' (apply_nonneg _ _)).trans
      (mul_le_mul_of_nonneg_right (hprofile v hv) hbound)
  rw [secondBlockTailMass_eq_original_pairs]
  calc
    _ ≤ ∑ _v ∈ firstZeroPairs left right fullI fullJ, Amp * bound :=
      Finset.sum_le_sum hpoint
    _ = ((firstZeroPairs left right fullI fullJ).card : ℝ) * (Amp * bound) := by simp
    _ ≤ (idealCountConstant K * X) ^ k * (Amp * bound) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg hAmp hbound)
    _ = _ := by
      rw [mul_pow, pow_succ]
      dsimp only [bound]
      ring

/-- All costs are fixed box exponents. The additional product exponent
is the proven full-quotient Gauss bound; it is not a tail hypothesis. -/
def secondTailExponent (k : ℕ) (productExponent profileExponent maskExponent
    inverseRadiusExponent : ℝ) : ℝ :=
  productExponent * ((k + 1 : ℕ) : ℝ) + profileExponent + maskExponent +
    max productExponent inverseRadiusExponent

/-- Only original pointwise data are supplied. In particular, the
actual second modulus window and the total tail mass are conclusions. -/
structure SecondTailWindows (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (blocks : ∀ DE : FirstZeroLabel left right fullI fullJ,
      FirstCommonCharacterBlock fullI fullJ DE.val)
    (seminorms : Finset (ℕ × ℕ)) (profiles : ι → κ → SchwartzMap V ℂ)
    (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R))
    (k : ℕ) (Z productExponent profileExponent maskExponent inverseRadiusExponent Amp : ℝ) where
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
  mask_norm :
    (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) M)).val ≤
        Z ^ maskExponent
  inverse_radius : radius.val⁻¹ ≤ Z ^ inverseRadiusExponent

namespace SecondTailWindows

variable {hΓ hDiff}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {left : Finset ι} {right : Finset κ}
variable {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {blocks : ∀ DE : FirstZeroLabel left right fullI fullJ,
  FirstCommonCharacterBlock fullI fullJ DE.val}
variable {seminorms : Finset (ℕ × ℕ)} {profiles : ι → κ → SchwartzMap V ℂ}
variable {radius : {r : ℝ // 0 < r}} {M : Finset (HeightOneSpectrum A.R)}
variable {k : ℕ} {Z productExponent profileExponent maskExponent inverseRadiusExponent Amp : ℝ}

theorem power_bound
    (W : SecondTailWindows C left right fullI fullJ blocks seminorms profiles radius M
      k Z productExponent profileExponent maskExponent inverseRadiusExponent Amp) :
    secondBlockTailMass hΓ hDiff C left right fullI fullJ blocks seminorms profiles radius M ≤
      (2 * firstTailFieldConstant K * idealCountConstant K ^ k) * Amp *
        Z ^ secondTailExponent k productExponent profileExponent maskExponent inverseRadiusExponent := by
  have hZpos : 0 < Z := zero_lt_one.trans_le W.base_ge_one
  have hAmp : 0 ≤ Amp := W.amplitude_nonneg
  have hcount : 0 ≤ idealCountConstant K := zero_le_one.trans (one_le_idealCountConstant K)
  have hfield : 0 ≤ firstTailFieldConstant K := firstTailFieldConstant_nonneg
  have hraw := secondBlockTailMass_bound hΓ hDiff C left right fullI fullJ blocks
    seminorms profiles radius M W.factors W.factors_injective W.factor_product
    (Z ^ productExponent) (Amp * Z ^ profileExponent) (Z ^ maskExponent)
    (Real.one_le_rpow W.base_ge_one W.productExponent_nonneg)
    (mul_nonneg W.amplitude_nonneg (Real.rpow_nonneg hZpos.le _))
    (Real.rpow_nonneg hZpos.le _) W.product_norm W.profile_seminorm W.mask_norm
  have hproduct : Z ^ productExponent ≤ Z ^ max productExponent inverseRadiusExponent :=
    Real.rpow_le_rpow_of_exponent_le W.base_ge_one (le_max_left _ _)
  have hradius : radius.val⁻¹ ≤ Z ^ max productExponent inverseRadiusExponent :=
    W.inverse_radius.trans
      (Real.rpow_le_rpow_of_exponent_le W.base_ge_one (le_max_right _ _))
  have hadd : radius.val⁻¹ + Z ^ productExponent ≤
      2 * Z ^ max productExponent inverseRadiusExponent := by linarith
  calc
    _ ≤ (firstTailFieldConstant K * idealCountConstant K ^ k) *
        (Amp * Z ^ profileExponent) * (Z ^ productExponent) ^ (k + 1) *
        Z ^ maskExponent * (radius.val⁻¹ + Z ^ productExponent) := hraw
    _ ≤ (firstTailFieldConstant K * idealCountConstant K ^ k) *
        (Amp * Z ^ profileExponent) * (Z ^ productExponent) ^ (k + 1) *
        Z ^ maskExponent * (2 * Z ^ max productExponent inverseRadiusExponent) :=
      mul_le_mul_of_nonneg_left hadd (by positivity)
    _ = _ := by
      unfold secondTailExponent
      rw [Real.rpow_add hZpos, Real.rpow_add hZpos, Real.rpow_add hZpos,
        Real.rpow_mul_natCast hZpos.le]
      ring

/-- A single physical cutoff gives arbitrary power decay for the actual
second tail. All constants and box exponents precede the moving source. -/
theorem cutoff_budget
    (W : SecondTailWindows C left right fullI fullJ blocks seminorms profiles radius M
      k Z productExponent profileExponent maskExponent inverseRadiusExponent Amp)
    (decay N Ctail : ℝ) (hdecay : 1 < decay) (hCtail : 0 ≤ Ctail) :
    let L := secondTailExponent k productExponent profileExponent maskExponent inverseRadiusExponent
    let X := Z ^ firstTailCutoffExponent L N decay
    1 ≤ X ∧
      Ctail * X ^ (1 - decay) *
        secondBlockTailMass hΓ hDiff C left right fullI fullJ blocks seminorms profiles radius M ≤
          (Ctail * (2 * firstTailFieldConstant K * idealCountConstant K ^ k)) *
            Amp * Z ^ (-N) := by
  dsimp only
  refine ⟨Real.one_le_rpow W.base_ge_one (firstTailCutoffExponent_nonneg _ _ _ hdecay), ?_⟩
  have hZpos : 0 < Z := zero_lt_one.trans_le W.base_ge_one
  have hAmp : 0 ≤ Amp := W.amplitude_nonneg
  have hcount : 0 ≤ idealCountConstant K := zero_le_one.trans (one_le_idealCountConstant K)
  have hfield : 0 ≤ firstTailFieldConstant K := firstTailFieldConstant_nonneg
  let L := secondTailExponent k productExponent profileExponent maskExponent inverseRadiusExponent
  let X := Z ^ firstTailCutoffExponent L N decay
  change Ctail * X ^ (1 - decay) *
    secondBlockTailMass hΓ hDiff C left right fullI fullJ blocks seminorms profiles radius M ≤ _
  calc
    _ ≤ Ctail * X ^ (1 - decay) *
        ((2 * firstTailFieldConstant K * idealCountConstant K ^ k) * Amp * Z ^ L) :=
      mul_le_mul_of_nonneg_left W.power_bound (mul_nonneg hCtail
        (Real.rpow_nonneg (Real.rpow_nonneg hZpos.le _) _))
    _ = (Ctail * (2 * firstTailFieldConstant K * idealCountConstant K ^ k)) * Amp *
        (X ^ (1 - decay) * Z ^ L) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (first_tail_cutoff_power Z L N decay W.base_ge_one hdecay) (by positivity)

end SecondTailWindows

/-- Exact binding to the error mass in the actual second finite source.
This is independent of which common physical cutoff was chosen. -/
theorem second_source_tail_mass_eq
    (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (blocks : ∀ DE : FirstZeroLabel left right fullI fullJ,
      FirstCommonCharacterBlock fullI fullJ DE.val)
    (seminorms : Finset (ℕ × ℕ)) (profiles : ι → κ → SchwartzMap V ℂ)
    (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R))
    (X : ℝ) (hX : 1 ≤ X) :
    let sources := fun DE => (blocks DE).secondFiniteSource hΓ hDiff C left right profiles M radius X hX
    (∑ DE, ∑ i ∈ (sources DE).leftColumns, ∑ j ∈ (sources DE).rightColumns,
      seminorms.sup (schwartzSeminormFamily ℂ V ℂ) ((sources DE).pairs i j).profile *
        ((sources DE).pairs i j).truncationMass (sources DE).mask radius) =
      secondBlockTailMass hΓ hDiff C left right fullI fullJ blocks seminorms profiles radius M := rfl

end ActualSecond

/-- A decay order chosen from fixed width and exponent boxes, before
the scale, original columns, profiles, or any Poisson frequency. -/
def tailDecayForWidth (Lmax N ξ : ℝ) : ℝ :=
  1 + (1 + max 0 (Lmax + N)) / ξ

theorem tailDecayForWidth_gt_one (Lmax N ξ : ℝ) (hξ : 0 < ξ) :
    1 < tailDecayForWidth Lmax N ξ := by
  have hnum : 0 < 1 + max 0 (Lmax + N) := by
    linarith [le_max_left (0 : ℝ) (Lmax + N)]
  exact lt_add_of_pos_right 1 (div_pos hnum hξ)

/-- Arbitrary saving can be obtained while paying at most the prescribed
small cutoff exponent. Only the fixed upper box for the raw cost enters
the choice of order. -/
theorem firstTailCutoffExponent_le_width
    (Lmax N ξ L : ℝ) (hξ : 0 < ξ) (hL : L ≤ Lmax) :
    firstTailCutoffExponent L N (tailDecayForWidth Lmax N ξ) ≤ ξ := by
  have hden : 0 < tailDecayForWidth Lmax N ξ - 1 :=
    sub_pos.mpr (tailDecayForWidth_gt_one Lmax N ξ hξ)
  unfold firstTailCutoffExponent
  apply (div_le_iff₀ hden).mpr
  calc
    max 0 (L + N) ≤ max 0 (Lmax + N) :=
      max_le_max le_rfl (add_le_add_right hL N)
    _ ≤ 1 + max 0 (Lmax + N) := by linarith
    _ = ξ * (tailDecayForWidth Lmax N ξ - 1) := by
      unfold tailDecayForWidth
      field_simp [ne_of_gt hξ]
      <;> ring

/-- The same order works for every scale and every raw exponent in the
fixed box. In particular the actual physical cutoff lies in [1,Z^ξ]. -/
theorem exists_uniform_small_tail_cutoff (Lmax N ξ : ℝ) (hξ : 0 < ξ) :
    ∃ decay : ℝ, 1 < decay ∧ ∀ L : ℝ, L ≤ Lmax →
      firstTailCutoffExponent L N decay ≤ ξ ∧
      ∀ Z : ℝ, 1 ≤ Z →
        1 ≤ Z ^ firstTailCutoffExponent L N decay ∧
        Z ^ firstTailCutoffExponent L N decay ≤ Z ^ ξ := by
  refine ⟨tailDecayForWidth Lmax N ξ, tailDecayForWidth_gt_one Lmax N ξ hξ, ?_⟩
  intro L hL
  have he := firstTailCutoffExponent_le_width Lmax N ξ L hξ hL
  refine ⟨he, ?_⟩
  intro Z hZ
  exact ⟨Real.one_le_rpow hZ
    (firstTailCutoffExponent_nonneg L N _ (tailDecayForWidth_gt_one Lmax N ξ hξ)),
    Real.rpow_le_rpow_of_exponent_le hZ he⟩

/-- The largest fixed box chooses one common cutoff. Every smaller raw
cost exponent then has the same saving at that very cutoff. -/
theorem first_tail_cutoff_power_of_le
    (Z L Lmax N decay : ℝ) (hZ : 1 ≤ Z) (hdecay : 1 < decay) (hL : L ≤ Lmax) :
    (Z ^ firstTailCutoffExponent Lmax N decay) ^ (1 - decay) * Z ^ L ≤ Z ^ (-N) := by
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
  exact (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ hL)
    (Real.rpow_nonneg (Real.rpow_nonneg hZ0 _) _)).trans
      (first_tail_cutoff_power Z Lmax N decay hZ hdecay)

/-- Both the real decay and the integer differentiability order are
chosen before the scale or source. The single cutoff based on `Lmax`
simultaneously preserves the prescribed width and controls all branches. -/
theorem exists_uniform_small_tail_order
    (rank : ℕ) (degree Lmax N ξ : ℝ) (hξ : 0 < ξ) :
    ∃ decay : ℝ, 1 < decay ∧ ∃ order : ℕ,
      rank < order ∧ degree * decay ≤ (order : ℝ) ∧
      ∀ Z : ℝ, 1 ≤ Z →
        let X := Z ^ firstTailCutoffExponent Lmax N decay
        1 ≤ X ∧ X ≤ Z ^ ξ ∧
          ∀ L : ℝ, L ≤ Lmax → X ^ (1 - decay) * Z ^ L ≤ Z ^ (-N) := by
  let decay := tailDecayForWidth Lmax N ξ
  have hdecay : 1 < decay := tailDecayForWidth_gt_one Lmax N ξ hξ
  obtain ⟨order, horder⟩ := exists_nat_gt (max (rank : ℝ) (degree * decay))
  have hr : (rank : ℝ) < (order : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) horder
  have hd : degree * decay ≤ (order : ℝ) :=
    (lt_of_le_of_lt (le_max_right _ _) horder).le
  refine ⟨decay, hdecay, order, ?_, hd, ?_⟩
  · exact_mod_cast hr
  · intro Z hZ
    refine ⟨Real.one_le_rpow hZ (firstTailCutoffExponent_nonneg _ _ _ hdecay), ?_, ?_⟩
    · exact Real.rpow_le_rpow_of_exponent_le hZ
        (firstTailCutoffExponent_le_width Lmax N ξ Lmax hξ le_rfl)
    · intro L hL
      exact first_tail_cutoff_power_of_le Z L Lmax N decay hZ hdecay hL

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OrbitalGaussColumn.residue_norm_le_modulus
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.second_modulus_norm
#print axioms HeckeSkeleton.Moments.EngineStep.secondBlockTailMass_bound
#print axioms HeckeSkeleton.Moments.EngineStep.SecondTailWindows.cutoff_budget
#print axioms HeckeSkeleton.Moments.EngineStep.exists_uniform_small_tail_cutoff
#print axioms HeckeSkeleton.Moments.EngineStep.exists_uniform_small_tail_order

