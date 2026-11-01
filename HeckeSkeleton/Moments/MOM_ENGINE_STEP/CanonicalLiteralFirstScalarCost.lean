import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAtomCosts

/-!
# The original first scalar is paid once with its full frozen ideal

The literal first scalar consists of the actual common frozen atoms,
the original pool norm tilt and its genuine residue value. The frozen
scalar estimate retains the complete square-root ideal denominator.
For a pool label the extracted ideal contains the same pool power;
the original bound `δ₁ ≤ 1/2` therefore pays its norm tilt internally.

The final original-profile theorem constructs the needed atom cost
from one fixed parent seminorm window. Neither a scalar bound nor a
row-profile or child-mass bound is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical (ProbeData RowCharacterInput)
open HeckePort.Moments HeckePort.Moments.Support

namespace CanonicalLiteralFirstScalarCost

/-- Chosen only from the original annulus and original profile control. -/
def atomBudget (annulus B : ℝ) : ℝ := max 1 (annulus * B ^ 2)

theorem atomBudget_one (annulus B : ℝ) : 1 ≤ atomBudget annulus B := le_max_left _ _

theorem atomBudget_atom (annulus B : ℝ) :
    annulus * B ^ 2 ≤ atomBudget annulus B := le_max_right _ _

end CanonicalLiteralFirstScalarCost

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}

namespace CanonicalLiteralRectangles.Atoms

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable (C : A.GeneralArithmeticContext σ η htrace)

include C

/-- The complete first frozen ideal, including repeated occurrences,
stays in the denominator. The atom fields are computed by the literal
table; the only estimates concern its individual original primes. -/
theorem commonScalar_norm_le_original_atoms
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
    (I : A.Exterior)
    (hI : frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂ b.keep b.witness.2 = I.val)
    (hmask : d.characters.MaskIndicator) (cap : ℕ) (B : ℝ)
    (hcap : k ≤ cap) (hB : 1 ≤ B)
    (hcost : ∀ i ∈ Finset.univ \ b.keep, d.primeAtomCost i (b.witness.2 i) ≤ B) :
    ‖d.commonScalar b‖ ≤ Real.sqrt (B ^ cap) / Real.sqrt (Ideal.absNorm I.val : ℝ) := by
  let bounds := d.commonAtomBounds b hmask
  let atoms := bounds.atoms (A := A) (σ := σ) ({()} : Finset Unit)
  have hideal : atoms.ideal = I.val := hI
  have hvalue : atoms.value () = d.commonScalar b :=
    bounds.atoms_value ({()} : Finset Unit) I
      (b.frozenSourceIdeal_eq.symm.trans hI) ()
  have henvelope : atoms.envelope ≤ B ^ cap := by
    change (∏ i ∈ Finset.univ \ b.keep, d.primeAtomCost i (b.witness.2 i)) ≤ _
    calc
      _ ≤ ∏ _i ∈ Finset.univ \ b.keep, B :=
        Finset.prod_le_prod₀ (fun i _ => d.primeAtomCost_nonneg i _) hcost
      _ = B ^ (Finset.univ \ b.keep).card := Finset.prod_const B
      _ ≤ B ^ cap := pow_le_pow_right₀ hB
        ((Finset.card_le_univ _).trans (by simpa only [Fintype.card_fin] using hcap))
  have h := atoms.norm_le C () (Finset.mem_singleton_self ())
  rw [hvalue, hideal] at h
  exact h.trans (div_le_div_of_nonneg_right
    (Real.sqrt_le_sqrt henvelope) (Real.sqrt_nonneg _))

/-- The pool reciprocity value keeps all of its ramification zeros.
Its norm is bounded by one using the actual arithmetic context. -/
theorem secondInputScalar_norm_le_common
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
    (power : A.Exterior) (firstElement : A.R) (δ₁ : ℝ) :
    ‖d.secondInputScalar (σ := σ) b power firstElement δ₁‖ ≤
      ‖d.commonScalar b‖ * A.exteriorNorm power ^ δ₁ := by
  have h := mul_le_mul_of_nonneg_left
    (actualIdealResidue_norm_le_one C power.val firstElement)
    (mul_nonneg (norm_nonneg (d.commonScalar b))
      (Real.rpow_nonneg (A.exteriorNorm_pos power).le δ₁))
  simpa only [secondInputScalar, norm_mul,
    Complex.norm_of_nonneg (Real.rpow_nonneg (A.exteriorNorm_pos power).le δ₁),
    mul_one, mul_assoc] using h

/-- Exact original norm costs before the pool power is paid. -/
theorem secondInputScalar_norm_le_original_atoms
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
    (I power : A.Exterior) (firstElement : A.R) (δ₁ : ℝ)
    (hI : frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂ b.keep b.witness.2 = I.val)
    (hmask : d.characters.MaskIndicator) (cap : ℕ) (B : ℝ)
    (hcap : k ≤ cap) (hB : 1 ≤ B)
    (hcost : ∀ i ∈ Finset.univ \ b.keep, d.primeAtomCost i (b.witness.2 i) ≤ B) :
    ‖d.secondInputScalar (σ := σ) b power firstElement δ₁‖ ≤
      Real.sqrt (B ^ cap) * A.exteriorNorm power ^ δ₁ /
        Real.sqrt (Ideal.absNorm I.val : ℝ) := by
  apply (d.secondInputScalar_norm_le_common C b power firstElement δ₁).trans
  exact (mul_le_mul_of_nonneg_right
    (d.commonScalar_norm_le_original_atoms C b I hI hmask cap B hcap hB hcost)
    (Real.rpow_nonneg (A.exteriorNorm_pos power).le δ₁)).trans_eq (by ring)

/-- The actual removed pool power is part of the first frozen ideal.
It pays its own norm tilt, with no moving factor inserted into the
fixed atom budget. Direct and main branches use the same lemma with
the unit power. -/
theorem secondInputScalar_norm_le_of_power_dvd
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
    (I power : A.Exterior) (firstElement : A.R) (δ₁ : ℝ) (hδ₁ : δ₁ ≤ 1 / 2)
    (hI : frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂ b.keep b.witness.2 = I.val)
    (hpower : power.val ∣ I.val)
    (hmask : d.characters.MaskIndicator) (cap : ℕ) (B : ℝ)
    (hcap : k ≤ cap) (hB : 1 ≤ B)
    (hcost : ∀ i ∈ Finset.univ \ b.keep, d.primeAtomCost i (b.witness.2 i) ≤ B) :
    ‖d.secondInputScalar (σ := σ) b power firstElement δ₁‖ ≤ Real.sqrt (B ^ cap) := by
  have hnp : 1 ≤ A.exteriorNorm power := by
    change (1 : ℝ) ≤ Ideal.absNorm power.val
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr power.property.1)
  have hnorm : A.exteriorNorm power ≤ (Ideal.absNorm I.val : ℝ) :=
    ideal_norm_le_of_dvd I.property.1 hpower
  have htilt : A.exteriorNorm power ^ δ₁ ≤ Real.sqrt (Ideal.absNorm I.val : ℝ) := by
    calc
      _ ≤ A.exteriorNorm power ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnp hδ₁
      _ = Real.sqrt (A.exteriorNorm power) := (Real.sqrt_eq_rpow _).symm
      _ ≤ _ := Real.sqrt_le_sqrt hnorm
  have hden : 0 < Real.sqrt (Ideal.absNorm I.val : ℝ) :=
    Real.sqrt_pos.mpr (A.exteriorNorm_pos I)
  apply (d.secondInputScalar_norm_le_original_atoms C b I power firstElement δ₁
    hI hmask cap B hcap hB hcost).trans
  apply (div_le_iff₀ hden).mpr
  exact mul_le_mul_of_nonneg_left htilt (Real.sqrt_nonneg _)

/-- A literal product identity is enough to supply the preceding
divisibility. It is the identity of the actual combined support
branch, not an additional scalar or mass hypothesis. -/
theorem secondInputScalar_norm_le_of_frozen_product
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
    (first power : A.Exterior) (firstElement : A.R) (δ₁ : ℝ) (hδ₁ : δ₁ ≤ 1 / 2)
    (hI : frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂ b.keep b.witness.2 =
      first.val * power.val)
    (hmask : d.characters.MaskIndicator) (cap : ℕ) (B : ℝ)
    (hcap : k ≤ cap) (hB : 1 ≤ B)
    (hcost : ∀ i ∈ Finset.univ \ b.keep, d.primeAtomCost i (b.witness.2 i) ≤ B) :
    ‖d.secondInputScalar (σ := σ) b power firstElement δ₁‖ ≤ Real.sqrt (B ^ cap) := by
  apply d.secondInputScalar_norm_le_of_power_dvd C b (ExteriorIdealEuler.mul first power)
    power firstElement δ₁ hδ₁ hI _ hmask cap B hcap hB hcost
  exact ⟨first.val, mul_comm _ _⟩

end CanonicalLiteralRectangles.Atoms

namespace CompleteMovingRowRecipe

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (ξ : X)

theorem literalSourceCharacters_maskIndicator :
    (Q.literalSourceCharacters ξ).MaskIndicator := by
  intro I
  change (if IsCoprime I Q.arithmeticMask.val then (1 : ℂ) else 0) = 0 ∨
    (if IsCoprime I Q.arithmeticMask.val then (1 : ℂ) else 0) = 1
  split_ifs <;> simp

variable (W : NormProfileRecipe (fun _ : PUnit => data ξ))
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
variable (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
variable (C : A.GeneralArithmeticContext σ η htrace)

include C

/-- The complete bound is obtained from the original parent window,
original slot cap and the actual pool-power inclusion. -/
theorem literalOriginalAtoms_firstScalar_norm_le
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {B : ℝ}
    (original : RawProfileWindow rowDomain heightDomain window orders (data ξ) B)
    (hzero : (0, 0) ∈ orders) (ht : t ∈ heightDomain)
    (annulus : ℝ) (hannulus : 0 ≤ annulus) (hwindow : window ⊆ Set.Iic annulus)
    (cap : ℕ) (hcap : (data ξ).geometry.slotCount ≤ cap)
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch
      (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₁
      (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₂
      (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).slots support)
    (I power : A.Exterior) (firstElement : A.R) (δ₁ : ℝ) (hδ₁ : δ₁ ≤ 1 / 2)
    (hI : frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂ b.keep b.witness.2 = I.val)
    (hpower : power.val ∣ I.val) :
    ‖(Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂)
        .secondInputScalar (σ := σ) b power firstElement δ₁‖ ≤
      Real.sqrt ((CanonicalLiteralFirstScalarCost.atomBudget annulus B) ^ cap) := by
  apply (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂)
    .secondInputScalar_norm_le_of_power_dvd C b I power firstElement δ₁ hδ₁ hI hpower
      (Q.literalSourceCharacters_maskIndicator ξ) cap
      (CanonicalLiteralFirstScalarCost.atomBudget annulus B) hcap
      (CanonicalLiteralFirstScalarCost.atomBudget_one annulus B)
  intro i _
  exact (Q.literalOriginalAtoms_primeAtomCost_le ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    original hzero ht annulus hannulus hwindow i (b.witness.2 i)).trans
      (CanonicalLiteralFirstScalarCost.atomBudget_atom annulus B)

/-- Both first constants are charged once. This is the multiplier in
the actual `withColumnConstants` row profile; it is not raised to the
number of second-stage occurrences. -/
theorem literalOriginalAtoms_firstScalar_pair_norm_le
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {B : ℝ}
    (original : RawProfileWindow rowDomain heightDomain window orders (data ξ) B)
    (hzero : (0, 0) ∈ orders) (ht : t ∈ heightDomain)
    (annulus : ℝ) (hannulus : 0 ≤ annulus) (hwindow : window ⊆ Set.Iic annulus)
    (cap : ℕ) (hcap : (data ξ).geometry.slotCount ≤ cap)
    {supportL supportR : Finset (Ideal (𝓞 K))}
    (bL : SupportCartesianBranch
      (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₁
      (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₂
      (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).slots supportL)
    (bR : SupportCartesianBranch
      (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₁
      (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₂
      (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).slots supportR)
    (IL IR powerL powerR : A.Exterior) (elementL elementR : A.R)
    (δ₁ : ℝ) (hδ₁ : δ₁ ≤ 1 / 2)
    (hIL : frozenSourceIdeal bL.plainDivisor₁ bL.plainDivisor₂ bL.keep bL.witness.2 = IL.val)
    (hIR : frozenSourceIdeal bR.plainDivisor₁ bR.plainDivisor₂ bR.keep bR.witness.2 = IR.val)
    (hpowerL : powerL.val ∣ IL.val) (hpowerR : powerR.val ∣ IR.val) :
    ‖(Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂)
        .secondInputScalar (σ := σ) bL powerL elementL δ₁‖ *
      ‖(Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂)
        .secondInputScalar (σ := σ) bR powerR elementR δ₁‖ ≤
      (CanonicalLiteralFirstScalarCost.atomBudget annulus B) ^ cap := by
  have hL := Q.literalOriginalAtoms_firstScalar_norm_le ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ C original hzero ht annulus hannulus hwindow cap hcap
    bL IL powerL elementL δ₁ hδ₁ hIL hpowerL
  have hR := Q.literalOriginalAtoms_firstScalar_norm_le ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ C original hzero ht annulus hannulus hwindow cap hcap
    bR IR powerR elementR δ₁ hδ₁ hIR hpowerR
  have h := mul_le_mul hL hR (norm_nonneg _) (Real.sqrt_nonneg _)
  exact h.trans_eq (Real.mul_self_sqrt (pow_nonneg
    (zero_le_one.trans (CanonicalLiteralFirstScalarCost.atomBudget_one annulus B)) cap))

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.commonScalar_norm_le_original_atoms
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.secondInputScalar_norm_le_of_power_dvd
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalOriginalAtoms_firstScalar_pair_norm_le
