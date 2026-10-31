import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ChildMomentDataAdapter
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.LocalCRT

/-!
# Actual child polynomials from single-ideal character dictionaries

The arithmetic input is a pointwise MOM_BASE dictionary for one ideal or
one slot prime.  It displays the original background, the original slot
character, the specified finite-ray twist, the common mask and the frozen
frequency factor.  No polynomial identity or energy inequality is an input.

The frozen factor is split by multiplicativity of the actual residue
character, including all its zeros.  Two finite plain sums and the whole
finite product of prime sums are then expanded internally.  The same
Cartesian expansion covers an empty set of slots.  Membership of the
specified ray twists in the actual `theta` is retained as explicit data;
finite order alone is never used to infer that membership.
-/

noncomputable section
open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain

namespace HeckeSkeleton.Moments.EngineStep

open DedekindZetaZeroFree HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}

/-- The actual exterior residue symbol, with zero extension outside the
fixed arithmetic support. -/
def actualIdealResidue (I : Ideal (𝓞 F)) (h : A.R) : ℂ :=
  if hI : I ≠ 0 ∧ IsCoprime I A.cS then
    σ (A.sexticResidue ⟨I, hI.1, Ideal.isCoprime_iff_sup_eq.mp hI.2⟩ h)
  else 0

theorem actualIdealResidue_exterior (I : A.Exterior) (h : A.R) :
    actualIdealResidue (A := A) (σ := σ) I.val h = σ (A.sexticResidue I h) := by
  rw [actualIdealResidue, dif_pos
    ⟨I.property.1, Ideal.isCoprime_iff_sup_eq.mpr I.property.2⟩]
  apply congrArg (fun J : A.Exterior => σ (A.sexticResidue J h))
  exact Subtype.ext rfl

/-- Extraction of `h = g * h'` preserves the actual ramification zeros. -/
theorem actualIdealResidue_frequency_mul (I : Ideal (𝓞 F)) (g h : A.R) :
    actualIdealResidue (A := A) (σ := σ) I (g * h) =
      actualIdealResidue (A := A) (σ := σ) I g *
        actualIdealResidue (A := A) (σ := σ) I h := by
  by_cases hI : I ≠ 0 ∧ IsCoprime I A.cS
  · simp only [actualIdealResidue, dif_pos hI]
    change σ ((MulChar.ofUnitHom _) (Ideal.Quotient.mk _ (g * h))) =
      σ ((MulChar.ofUnitHom _) (Ideal.Quotient.mk _ g)) *
        σ ((MulChar.ofUnitHom _) (Ideal.Quotient.mk _ h))
    rw [map_mul, map_mul, map_mul]
  · simp only [actualIdealResidue, dif_neg hI, zero_mul]

theorem generatedIdealCharacter_frequency_extract
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (g h h' : A.R) (hh : h = g * h') :
    generatedIdealCharacter (σ := σ) I a ha (Ideal.Quotient.mk _ h) =
      σ (A.sexticResidue I g) * σ (A.sexticResidue I h') := by
  rw [hh, map_mul, map_mul, generatedIdealCharacter_mk, generatedIdealCharacter_mk]

private theorem exterior_product_iff (I J : Ideal (𝓞 F)) :
    (I * J ≠ 0 ∧ IsCoprime (I * J) A.cS) ↔
      (I ≠ 0 ∧ IsCoprime I A.cS) ∧ (J ≠ 0 ∧ IsCoprime J A.cS) := by
  simp only [mul_ne_zero_iff, IsCoprime.mul_left_iff]
  tauto

/-- The same zero-extended value is multiplicative in the complete ideal,
so the finite tuple expansion retains one whole residue coefficient. -/
theorem actualIdealResidue_ideal_mul (I J : Ideal (𝓞 F)) (h : A.R) :
    actualIdealResidue (A := A) (σ := σ) (I * J) h =
      actualIdealResidue (A := A) (σ := σ) I h *
        actualIdealResidue (A := A) (σ := σ) J h := by
  by_cases hI : I ≠ 0 ∧ IsCoprime I A.cS
  · by_cases hJ : J ≠ 0 ∧ IsCoprime J A.cS
    · have hIJ := (exterior_product_iff (A := A) I J).mpr ⟨hI, hJ⟩
      simp only [actualIdealResidue, dif_pos hI, dif_pos hJ, dif_pos hIJ]
      let II : A.Exterior := ⟨I, hI.1, Ideal.isCoprime_iff_sup_eq.mp hI.2⟩
      let JJ : A.Exterior := ⟨J, hJ.1, Ideal.isCoprime_iff_sup_eq.mp hJ.2⟩
      let IJ : A.Exterior := ⟨I * J, hIJ.1, Ideal.isCoprime_iff_sup_eq.mp hIJ.2⟩
      change σ (A.residueValue A.sexticResidueFamily IJ h) =
        σ (A.residueValue A.sexticResidueFamily II h) *
          σ (A.residueValue A.sexticResidueFamily JJ h)
      simpa only [map_mul] using congrArg σ
        (A.sexticResidueFamily_normalized.2.2 II JJ IJ rfl h)
    · have hIJ : ¬(I * J ≠ 0 ∧ IsCoprime (I * J) A.cS) :=
        fun h => hJ ((exterior_product_iff (A := A) I J).mp h).2
      simp only [actualIdealResidue, dif_neg hIJ, dif_neg hJ, mul_zero]
  · have hIJ : ¬(I * J ≠ 0 ∧ IsCoprime (I * J) A.cS) :=
      fun h => hI ((exterior_product_iff (A := A) I J).mp h).1
    simp only [actualIdealResidue, dif_neg hIJ, dif_neg hI, zero_mul]

theorem actualIdealResidue_one (h : A.R) :
    actualIdealResidue (A := A) (σ := σ) 1 h = 1 := by
  have hI : (1 : Ideal (𝓞 F)) ≠ 0 ∧ IsCoprime (1 : Ideal (𝓞 F)) A.cS :=
    ⟨one_ne_zero, isCoprime_one_left⟩
  rw [actualIdealResidue, dif_pos hI]
  let II : A.Exterior := ⟨1, hI.1, Ideal.isCoprime_iff_sup_eq.mp hI.2⟩
  change σ (A.residueValue A.sexticResidueFamily II h) = 1
  rw [A.residueValue_top A.sexticResidueFamily II (by rfl), map_one]

theorem actualIdealResidue_prod {ι : Type*} (S : Finset ι)
    (I : ι → Ideal (𝓞 F)) (h : A.R) :
    actualIdealResidue (A := A) (σ := σ) (∏ i ∈ S, I i) h =
      ∏ i ∈ S, actualIdealResidue (A := A) (σ := σ) (I i) h := by
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using actualIdealResidue_one (σ := σ) h
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, actualIdealResidue_ideal_mul, ih, Finset.prod_insert hi]

section Cartesian

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem jointPhase_sum {ι : Type*} (ξ : V) (S : Finset ι) (x : ι → V) :
    jointPhase ξ (∑ i ∈ S, x i) = ∏ i ∈ S, jointPhase ξ (x i) := by
  induction S using Finset.induction_on with
  | empty => simp [jointPhase]
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, jointPhase_add, ih, Finset.prod_insert hi]

def childCartesianColumns {X Y : Type*} {P : Type*} {k : ℕ}
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P) :
    Finset ((X × Y) × (Fin k → P)) :=
  (S₁.product S₂).product (Fintype.piFinset S)

def childCartesianCoefficient {X Y P : Type*} {k : ℕ}
    (a₁ : X → ℂ) (a₂ : Y → ℂ) (a : Fin k → P → ℂ)
    (v : (X × Y) × (Fin k → P)) : ℂ :=
  a₁ v.1.1 * a₂ v.1.2 * ∏ i, a i (v.2 i)

def childCartesianLocation {X Y P : Type*} {k : ℕ}
    (x₁ : X → V) (x₂ : Y → V) (x : Fin k → P → V)
    (v : (X × Y) × (Fin k → P)) : V :=
  x₁ v.1.1 + x₂ v.1.2 + ∑ i, x i (v.2 i)

/-- One proof for both empty and nonempty slot sets. -/
theorem joint_cartesian_column_factorization {X Y P : Type*} {k : ℕ}
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (a₁ : X → ℂ) (a₂ : Y → ℂ) (a : Fin k → P → ℂ)
    (x₁ : X → V) (x₂ : Y → V) (x : Fin k → P → V) (ξ : V) :
    jointFourierColumn (childCartesianColumns S₁ S₂ S)
      (childCartesianCoefficient a₁ a₂ a) (childCartesianLocation x₁ x₂ x) ξ =
      (∑ I ∈ S₁, a₁ I * jointPhase ξ (x₁ I)) *
        (∑ J ∈ S₂, a₂ J * jointPhase ξ (x₂ J)) *
          ∏ i, ∑ p ∈ S i, a i p * jointPhase ξ (x i p) := by
  rw [Finset.prod_univ_sum]
  simp only [jointFourierColumn, childCartesianColumns, childCartesianCoefficient,
    childCartesianLocation, Finset.product_eq_sprod, Finset.sum_product,
    jointPhase_add, jointPhase_sum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.prod_mul_distrib]
  ring

end Cartesian

section HeckeTerms

variable {ω ψ : HeckeCharacter F}

def sourcePlainCoefficient (χ θ : HeckeCharacter F) (M : Ideal (𝓞 F) →* ℂ)
    (I : HeckeGeneral.Analysis.NonzeroIdeal F) : ℂ :=
  heckeIdealCoefficient F χ I * heckeIdealCoefficient F θ I * M I.val

def sourcePrimeCoefficient (χ θ : HeckeCharacter F) (M : Ideal (𝓞 F) →* ℂ)
    (p : HeightOneSpectrum (𝓞 F)) : ℂ :=
  primeCoefficient F χ p * primeCoefficient F θ p * M p.asIdeal

/-- Primitive single-ideal and single-prime MOM_BASE input.  This data
cannot be obtained from arbitrary bare `MomentData`; it records precisely
the source reciprocity and fixed-ray identification that must be supplied.
The stated `theta` membership is not inferred from finite order. -/
structure ChildHeckeTermDictionary (d : MomentData F ω ψ)
    (u : HeckeGeneral.Analysis.NonzeroIdeal F) (g h' : A.R) where
  sourcePlain : HeckeCharacter F
  sourceSlot : Fin d.geometry.slotCount → HeckeCharacter F
  sourceMask : Ideal (𝓞 F) →* ℂ
  fixedRay : Finset (HeckeCharacter F)
  fixedRay_mem_theta : ∀ θ ∈ fixedRay, θ ∈ d.theta
  plainTwist : HeckeCharacter F
  plainTwist_mem : plainTwist ∈ fixedRay
  slotTwist : Fin d.geometry.slotCount → HeckeCharacter F
  slotTwist_mem : ∀ i, slotTwist i ∈ fixedRay
  plain : ∀ I : HeckeGeneral.Analysis.NonzeroIdeal F,
    heckeIdealCoefficient F (d.plainBackground * d.rowCharacter u) I * maskValue d u I.val =
      sourcePlainCoefficient sourcePlain plainTwist sourceMask I *
        actualIdealResidue (A := A) (σ := σ) I.val g *
          actualIdealResidue (A := A) (σ := σ) I.val h'
  slot : ∀ (i : Fin d.geometry.slotCount) (p : HeightOneSpectrum (𝓞 F)),
    primeCoefficient F (d.rowCharacter u * d.slotCoefficient i) p * maskValue d u p.asIdeal =
      sourcePrimeCoefficient (sourceSlot i) (slotTwist i) sourceMask p *
        actualIdealResidue (A := A) (σ := σ) p.asIdeal g *
          actualIdealResidue (A := A) (σ := σ) p.asIdeal h'

def sourcePlainTerm (χ θ : HeckeCharacter F) (M : Ideal (𝓞 F) →* ℂ)
    (g h' : A.R) (W : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ) (N : ℝ)
    (I : HeckeGeneral.Analysis.NonzeroIdeal F) : ℂ :=
  (Real.sqrt N : ℂ)⁻¹ * (sourcePlainCoefficient χ θ M I *
    actualIdealResidue (A := A) (σ := σ) I.val (g * h') * W I)

def sourcePrimeTerm (χ θ : HeckeCharacter F) (M : Ideal (𝓞 F) →* ℂ)
    (g h' : A.R) (W : HeightOneSpectrum (𝓞 F) → ℂ) (P : ℝ)
    (p : HeightOneSpectrum (𝓞 F)) : ℂ :=
  (Real.sqrt P : ℂ)⁻¹ * (sourcePrimeCoefficient χ θ M p *
    actualIdealResidue (A := A) (σ := σ) p.asIdeal (g * h') * W p)

def childIndexIdeal {k : ℕ}
    (v : (HeckeGeneral.Analysis.NonzeroIdeal F × HeckeGeneral.Analysis.NonzeroIdeal F) ×
      (Fin k → HeightOneSpectrum (𝓞 F))) : Ideal (𝓞 F) :=
  (v.1.1.val * v.1.2.val) * ∏ i, (v.2 i).asIdeal

/-- The factorized terms are exactly one complete ideal coefficient:
one original background, every original slot coefficient, one specified
finite-ray factor, one common mask and one complete residue symbol. -/
theorem child_source_coefficient_whole {k : ℕ}
    (χ θ : HeckeCharacter F) (χp θp : Fin k → HeckeCharacter F)
    (M : Ideal (𝓞 F) →* ℂ) (g h' : A.R)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (N₁ N₂ : ℝ) (P : Fin k → ℝ)
    (v : (HeckeGeneral.Analysis.NonzeroIdeal F × HeckeGeneral.Analysis.NonzeroIdeal F) ×
      (Fin k → HeightOneSpectrum (𝓞 F))) :
    childCartesianCoefficient
      (sourcePlainTerm (σ := σ) χ θ M g h' w₁ N₁)
      (sourcePlainTerm (σ := σ) χ θ M g h' w₂ N₂)
      (fun i => sourcePrimeTerm (σ := σ) (χp i) (θp i) M g h' (w i) (P i)) v =
      ((Real.sqrt N₁ : ℂ)⁻¹ * (Real.sqrt N₂ : ℂ)⁻¹ *
        ∏ i, (Real.sqrt (P i) : ℂ)⁻¹) *
      (heckeIdealCoefficient F χ (v.1.1 * v.1.2) *
        ∏ i, primeCoefficient F (χp i) (v.2 i)) *
      (heckeIdealCoefficient F θ (v.1.1 * v.1.2) *
        ∏ i, primeCoefficient F (θp i) (v.2 i)) *
      M (childIndexIdeal v) *
      actualIdealResidue (A := A) (σ := σ) (childIndexIdeal v) (g * h') *
      (w₁ v.1.1 * w₂ v.1.2 * ∏ i, w i (v.2 i)) := by
  simp only [childCartesianCoefficient, sourcePlainTerm, sourcePrimeTerm,
    sourcePlainCoefficient, sourcePrimeCoefficient, childIndexIdeal,
    heckeIdealCoefficient_mul, map_mul, map_prod, actualIdealResidue_ideal_mul,
    actualIdealResidue_prod, Finset.prod_mul_distrib]
  ring

theorem plainPolynomial_enlarge_support (d : MomentData F ω ψ) (W : IdealTest F)
    (u : HeckeGeneral.Analysis.NonzeroIdeal F) (N t : ℝ)
    (S : Finset (HeckeGeneral.Analysis.NonzeroIdeal F))
    (hS : W.support u t N ⊆ S) :
    plainPolynomial d W u N t =
      ∑ I ∈ S, (Real.sqrt N : ℂ)⁻¹ *
        (heckeIdealCoefficient F (d.plainBackground * d.rowCharacter u) I *
          W.profile u t (idealNorm F I / N) * maskValue d u I.val) := by
  rw [plainPolynomial, ← Finset.mul_sum]
  congr 1
  apply Finset.sum_subset hS
  intro I _ hnot
  have hz : W.profile u t (idealNorm F I / N) = 0 := by
    by_contra h
    exact hnot ((W.support_spec u t N I).mpr h)
  rw [hz, mul_zero, zero_mul]

theorem primePolynomial_enlarge_support (d : MomentData F ω ψ)
    (i : Fin d.geometry.slotCount) (u : HeckeGeneral.Analysis.NonzeroIdeal F) (Z t : ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length) ⊆ S) :
    primePolynomial d i u Z t =
      ∑ p ∈ S, (Real.sqrt (Z ^ (d.geometry.slots i).length) : ℂ)⁻¹ *
        (primeCoefficient F (d.rowCharacter u * d.slotCoefficient i) p *
          (d.geometry.slots i).profile t
            ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length) *
              maskValue d u p.asIdeal) := by
  rw [primePolynomial, ← Finset.mul_sum]
  congr 1
  apply Finset.sum_subset hS
  intro p _ hnot
  have hz : (d.geometry.slots i).profile t
      ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length) = 0 := by
    by_contra h
    exact hnot (((d.geometry.slots i).support_spec t _ p).mpr h)
  rw [hz, mul_zero, zero_mul]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem sourcePlainTerm_calibrated (d : MomentData F ω ψ)
    (u : HeckeGeneral.Analysis.NonzeroIdeal F) (g h' : A.R)
    (D : ChildHeckeTermDictionary (σ := σ) d u g h')
    (W : IdealTest F) (w : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (x : HeckeGeneral.Analysis.NonzeroIdeal F → V) (ξ : V) (N t : ℝ)
    (I : HeckeGeneral.Analysis.NonzeroIdeal F)
    (hW : w I * jointPhase ξ (x I) = W.profile u t (idealNorm F I / N)) :
    sourcePlainTerm (σ := σ) D.sourcePlain D.plainTwist D.sourceMask g h' w N I *
      jointPhase ξ (x I) = (Real.sqrt N : ℂ)⁻¹ *
        (heckeIdealCoefficient F (d.plainBackground * d.rowCharacter u) I *
          W.profile u t (idealNorm F I / N) * maskValue d u I.val) := by
  rw [sourcePlainTerm, actualIdealResidue_frequency_mul]
  calc
    _ = (Real.sqrt N : ℂ)⁻¹ *
      ((sourcePlainCoefficient D.sourcePlain D.plainTwist D.sourceMask I *
        actualIdealResidue (A := A) (σ := σ) I.val g *
          actualIdealResidue (A := A) (σ := σ) I.val h') *
            (w I * jointPhase ξ (x I))) := by ring
    _ = _ := by rw [← D.plain I, hW]; ring

theorem sourcePrimeTerm_calibrated (d : MomentData F ω ψ)
    (u : HeckeGeneral.Analysis.NonzeroIdeal F) (g h' : A.R)
    (D : ChildHeckeTermDictionary (σ := σ) d u g h')
    (i : Fin d.geometry.slotCount) (w : HeightOneSpectrum (𝓞 F) → ℂ)
    (x : HeightOneSpectrum (𝓞 F) → V) (ξ : V) (Z t : ℝ)
    (p : HeightOneSpectrum (𝓞 F))
    (hW : w p * jointPhase ξ (x p) = (d.geometry.slots i).profile t
      ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length)) :
    sourcePrimeTerm (σ := σ) (D.sourceSlot i) (D.slotTwist i) D.sourceMask g h' w
      (Z ^ (d.geometry.slots i).length) p * jointPhase ξ (x p) =
      (Real.sqrt (Z ^ (d.geometry.slots i).length) : ℂ)⁻¹ *
        (primeCoefficient F (d.rowCharacter u * d.slotCoefficient i) p *
          (d.geometry.slots i).profile t
            ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length) *
              maskValue d u p.asIdeal) := by
  rw [sourcePrimeTerm, actualIdealResidue_frequency_mul]
  calc
    _ = (Real.sqrt (Z ^ (d.geometry.slots i).length) : ℂ)⁻¹ *
      ((sourcePrimeCoefficient (D.sourceSlot i) (D.slotTwist i) D.sourceMask p *
        actualIdealResidue (A := A) (σ := σ) p.asIdeal g *
          actualIdealResidue (A := A) (σ := σ) p.asIdeal h') *
            (w p * jointPhase ξ (x p))) := by ring
    _ = _ := by rw [← D.slot i p, hW]; ring

/-- The aggregate child polynomial is a conclusion.  Its inputs are
only individual ideal/prime arithmetic dictionaries, individual profile
identities and literal finite support inclusions.  Every original slot
coefficient and common mask remains in the actual moment polynomial. -/
theorem actual_child_polynomial_from_terms (d : MomentData F ω ψ)
    (u : HeckeGeneral.Analysis.NonzeroIdeal F) (g h' : A.R)
    (D : ChildHeckeTermDictionary (σ := σ) d u g h')
    (N₁ N₂ Z t : ℝ)
    (S₁ S₂ : Finset (HeckeGeneral.Analysis.NonzeroIdeal F))
    (S : Fin d.geometry.slotCount → Finset (HeightOneSpectrum (𝓞 F)))
    (hS₁ : d.plainTest₁.support u t N₁ ⊆ S₁)
    (hS₂ : d.plainTest₂.support u t N₂ ⊆ S₂)
    (hS : ∀ i, (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length) ⊆ S i)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (w : Fin d.geometry.slotCount → HeightOneSpectrum (𝓞 F) → ℂ)
    (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal F → V)
    (x : Fin d.geometry.slotCount → HeightOneSpectrum (𝓞 F) → V) (ξ : V)
    (hW₁ : ∀ I ∈ S₁, w₁ I * jointPhase ξ (x₁ I) =
      d.plainTest₁.profile u t (idealNorm F I / N₁))
    (hW₂ : ∀ I ∈ S₂, w₂ I * jointPhase ξ (x₂ I) =
      d.plainTest₂.profile u t (idealNorm F I / N₂))
    (hW : ∀ i, ∀ p ∈ S i, w i p * jointPhase ξ (x i p) =
      (d.geometry.slots i).profile t
        ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length)) :
    jointFourierColumn (childCartesianColumns S₁ S₂ S)
      (childCartesianCoefficient
        (sourcePlainTerm (σ := σ) D.sourcePlain D.plainTwist D.sourceMask g h' w₁ N₁)
        (sourcePlainTerm (σ := σ) D.sourcePlain D.plainTwist D.sourceMask g h' w₂ N₂)
        (fun i => sourcePrimeTerm (σ := σ) (D.sourceSlot i) (D.slotTwist i) D.sourceMask
          g h' (w i) (Z ^ (d.geometry.slots i).length)))
      (childCartesianLocation x₁ x₂ x) ξ =
      plainPolynomial d d.plainTest₁ u N₁ t *
        plainPolynomial d d.plainTest₂ u N₂ t * slotProduct d u Z t := by
  rw [joint_cartesian_column_factorization,
    plainPolynomial_enlarge_support d d.plainTest₁ u N₁ t S₁ hS₁,
    plainPolynomial_enlarge_support d d.plainTest₂ u N₂ t S₂ hS₂, slotProduct]
  have h₁ : (∑ I ∈ S₁,
      sourcePlainTerm (σ := σ) D.sourcePlain D.plainTwist D.sourceMask g h' w₁ N₁ I *
        jointPhase ξ (x₁ I)) =
      ∑ I ∈ S₁, (Real.sqrt N₁ : ℂ)⁻¹ *
        (heckeIdealCoefficient F (d.plainBackground * d.rowCharacter u) I *
          d.plainTest₁.profile u t (idealNorm F I / N₁) * maskValue d u I.val) := by
    apply Finset.sum_congr rfl
    intro I hI
    exact sourcePlainTerm_calibrated d u g h' D d.plainTest₁ w₁ x₁ ξ N₁ t I (hW₁ I hI)
  have h₂ : (∑ I ∈ S₂,
      sourcePlainTerm (σ := σ) D.sourcePlain D.plainTwist D.sourceMask g h' w₂ N₂ I *
        jointPhase ξ (x₂ I)) =
      ∑ I ∈ S₂, (Real.sqrt N₂ : ℂ)⁻¹ *
        (heckeIdealCoefficient F (d.plainBackground * d.rowCharacter u) I *
          d.plainTest₂.profile u t (idealNorm F I / N₂) * maskValue d u I.val) := by
    apply Finset.sum_congr rfl
    intro I hI
    exact sourcePlainTerm_calibrated d u g h' D d.plainTest₂ w₂ x₂ ξ N₂ t I (hW₂ I hI)
  rw [h₁, h₂]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [primePolynomial_enlarge_support d i u Z t (S i) (hS i)]
  apply Finset.sum_congr rfl
  intro p hp
  exact sourcePrimeTerm_calibrated d u g h' D i (w i) (x i) ξ Z t p (hW i p hp)

end HeckeTerms

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.generatedIdealCharacter_frequency_extract
#print axioms HeckeSkeleton.Moments.EngineStep.child_source_coefficient_whole
#print axioms HeckeSkeleton.Moments.EngineStep.actual_child_polynomial_from_terms
