import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonSupportSource
import HeckePort.Moments.Descent.IdealMasks

/-!
# Canonical actual first blocks

Each label in the genuine finite common-support pool determines exact
prime multiplicities and independent residual ideals. The arithmetic
context chooses allowed generators for those residuals. Reciprocity then
proves that the original reciprocal phase is one; it is not a new input.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open UniqueFactorizationMonoid HeckePort.IdealMobiusDivisorSum
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}

def exteriorPrimeOfSupport (I : A.Exterior) (P : primeSupport I.val) : ExteriorPrime A :=
  ⟨⟨P.val, Ideal.isPrime_of_prime (support_prime P.property),
      (support_prime P.property).ne_zero⟩, by
    apply top_unique
    rw [← I.property.2]
    apply sup_le_sup_right
    exact Ideal.dvd_iff_le.mp
      ((HeckePort.Moments.prime_mem_support_iff_dvd P.val I.val
        (support_prime P.property) I.property.1).mp P.property)⟩

private theorem ideal_support_count_product (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    (∏ P ∈ primeSupport I, P ^ (normalizedFactors I).count P) = I := by
  change (∏ P ∈ (normalizedFactors I).toFinset, P ^ (normalizedFactors I).count P) = I
  rw [← Finset.prod_multiset_count]
  exact Ideal.prod_normalizedFactors_eq_self hI

theorem exists_actual_first_common_block
    (C : A.GeneralArithmeticContext σ η hS)
    {ι κ : Type*} (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (DE : Ideal (𝓞 K) × Ideal (𝓞 K))
    (hDE : DE ∈ commonSupportPool left right (fun i => (fullI i).val) (fun j => (fullJ j).val)) :
    ∃ b : FirstCommonCharacterBlock fullI fullJ DE,
      (∀ i, ∃ u : Kˣ, (u : K) = (b.leftGenerator i : K) ∧ A.IsAllowed C.correction.B u) ∧
      (∀ j, ∃ u : Kˣ, (u : K) = (b.rightGenerator j : K) ∧ A.IsAllowed C.correction.B u) := by
  obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp hDE
  let commonSupport := primeSupport (fullI ij.1).val ∩ primeSupport (fullJ ij.2).val
  let CI := extractedExterior (fullI ij.1) commonSupport
  let CJ := extractedExterior (fullJ ij.2) commonSupport
  have hsupport : primeSupport CI.val = primeSupport CJ.val :=
    commonSupportLabel_support_eq (fullI ij.1).val (fullJ ij.2).val
  let e : Fin (Fintype.card (primeSupport CI.val)) ≃ primeSupport CI.val :=
    (Fintype.equivFin _).symm
  let p := fun i : Fin (Fintype.card (primeSupport CI.val)) => exteriorPrimeOfSupport CI (e i)
  let m := fun i : Fin (Fintype.card (primeSupport CI.val)) =>
    (normalizedFactors CI.val).count (e i).val
  let n := fun i : Fin (Fintype.card (primeSupport CI.val)) =>
    (normalizedFactors CJ.val).count (e i).val
  have hp : Function.Injective p := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact congrArg (fun q : ExteriorPrime A => q.val.asIdeal) hij
  have hm : ∀ i, 0 < m i := by
    intro i
    exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp (e i).property)
  have hn : ∀ i, 0 < n i := by
    intro i
    apply Multiset.count_pos.mpr
    apply Multiset.mem_toFinset.mp
    rw [← hsupport]
    exact (e i).property
  have hCI : (primePowerProduct p m).val = CI.val := by
    change (∏ i : Fin (Fintype.card (primeSupport CI.val)),
      (e i).val ^ (normalizedFactors CI.val).count (e i).val) = CI.val
    calc
      _ = ∏ P : primeSupport CI.val, P.val ^ (normalizedFactors CI.val).count P.val :=
        Fintype.prod_equiv e _ _ (fun i => rfl)
      _ = ∏ P ∈ primeSupport CI.val, P ^ (normalizedFactors CI.val).count P :=
        Finset.prod_coe_sort _ _
      _ = CI.val := ideal_support_count_product CI.val CI.property.1
  have hCJ : (primePowerProduct p n).val = CJ.val := by
    change (∏ i : Fin (Fintype.card (primeSupport CI.val)),
      (e i).val ^ (normalizedFactors CJ.val).count (e i).val) = CJ.val
    calc
      _ = ∏ P : primeSupport CI.val, P.val ^ (normalizedFactors CJ.val).count P.val :=
        Fintype.prod_equiv e _ _ (fun i => rfl)
      _ = ∏ P ∈ primeSupport CI.val, P ^ (normalizedFactors CJ.val).count P :=
        Finset.prod_coe_sort _ _
      _ = CJ.val := by
        rw [hsupport]
        exact ideal_support_count_product CJ.val CJ.property.1
  let g : A.Exterior → A.R := fun I => Classical.choose (C.allowed_integral I)
  have hg (I : A.Exterior) : A.Generates I (g I) :=
    (Classical.choose_spec (Classical.choose_spec (C.allowed_integral I))).1
  have hallowed (I : A.Exterior) :
      ∃ u : Kˣ, (u : K) = (g I : K) ∧ A.IsAllowed C.correction.B u := by
    obtain ⟨u, hu⟩ := Classical.choose_spec (C.allowed_integral I)
    exact ⟨u, hu.2⟩
  let b : FirstCommonCharacterBlock fullI fullJ
      (commonSupportLabel (fullI ij.1).val (fullJ ij.2).val) :=
    { primeCount := Fintype.card (primeSupport CI.val)
      primes := p
      primes_injective := hp
      leftMultiplicity := m
      rightMultiplicity := n
      left_positive := hm
      right_positive := hn
      common_left := hCI
      common_right := hCJ
      leftResidual := fun i => residualExterior (fullI i) (primeSupport CI.val)
      rightResidual := fun j => residualExterior (fullJ j) (primeSupport CI.val)
      left_residual := fun i => rfl
      right_residual := fun j => rfl
      leftGenerator := fun i => g (residualExterior (fullI i) (primeSupport CI.val))
      rightGenerator := fun j => g (residualExterior (fullJ j) (primeSupport CI.val))
      left_generates := fun i => hg _
      right_generates := fun j => hg _ }
  exact ⟨b, fun i => hallowed _, fun j => hallowed _⟩

def canonicalFirstCommonBlock
    (C : A.GeneralArithmeticContext σ η hS)
    {ι κ : Type*} (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (DE : Ideal (𝓞 K) × Ideal (𝓞 K))
    (hDE : DE ∈ commonSupportPool left right (fun i => (fullI i).val) (fun j => (fullJ j).val)) :
    FirstCommonCharacterBlock fullI fullJ DE :=
  Classical.choose (exists_actual_first_common_block C left right fullI fullJ DE hDE)

theorem canonicalFirstCommonBlock_allowed
    (C : A.GeneralArithmeticContext σ η hS)
    {ι κ : Type*} (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (DE : Ideal (𝓞 K) × Ideal (𝓞 K))
    (hDE : DE ∈ commonSupportPool left right (fun i => (fullI i).val) (fun j => (fullJ j).val)) :
    let b := canonicalFirstCommonBlock C left right fullI fullJ DE hDE
    (∀ i, ∃ u : Kˣ, (u : K) = (b.leftGenerator i : K) ∧ A.IsAllowed C.correction.B u) ∧
      (∀ j, ∃ u : Kˣ, (u : K) = (b.rightGenerator j : K) ∧ A.IsAllowed C.correction.B u) :=
  Classical.choose_spec (exists_actual_first_common_block C left right fullI fullJ DE hDE)

variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)

theorem canonicalFirstCommonBlock_phase_one
    (C : A.GeneralArithmeticContext σ η hS)
    {ι κ : Type*} (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (DE : Ideal (𝓞 K) × Ideal (𝓞 K))
    (hDE : DE ∈ commonSupportPool left right (fun i => (fullI i).val) (fun j => (fullJ j).val))
    (i : ι) (j : κ)
    (hcop : IsCoprime
      ((canonicalFirstCommonBlock C left right fullI fullJ DE hDE).leftResidual i).val
      ((canonicalFirstCommonBlock C left right fullI fullJ DE hDE).rightResidual j).val) :
    let b := canonicalFirstCommonBlock C left right fullI fullJ DE hDE
    firstReciprocalPhase
      (generatedOriginalColumn (σ := σ) hΓ (b.leftResidual i) (b.leftGenerator i) (b.left_generates i))
      (generatedOriginalColumn (σ := σ) hΓ (b.rightResidual j) (b.rightGenerator j)
        (b.right_generates j)) = 1 := by
  let b := canonicalFirstCommonBlock C left right fullI fullJ DE hDE
  obtain ⟨ua, hua, ha⟩ := (canonicalFirstCommonBlock_allowed C left right fullI fullJ DE hDE).1 i
  obtain ⟨ub, hub, hb⟩ := (canonicalFirstCommonBlock_allowed C left right fullI fullJ DE hDE).2 j
  exact firstReciprocalPhase_allowed hΓ C (b.leftResidual i) (b.rightResidual j)
    (b.leftGenerator i) (b.rightGenerator j) (b.left_generates i) (b.right_generates j)
    ua ub hua hub ha hb hcop

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.exists_actual_first_common_block
#print axioms HeckeSkeleton.Moments.EngineStep.canonicalFirstCommonBlock_phase_one

