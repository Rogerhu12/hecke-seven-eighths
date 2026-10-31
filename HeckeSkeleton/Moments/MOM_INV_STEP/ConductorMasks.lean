import HeckeSkeleton.Moments.MOM_INV_STEP.LocalSource
import HeckeGeneral.Arithmetic.IdealMobiusMask

/-!
# Active conductor support and its actual complementary mask

The two ideal products are squarefree and coprime. The principal local
zero factors are exactly coprimality with the complementary ideal, using
the actual S-integer modulus contraction, including at zero numerators.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ConductorMasks

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open scoped BigOperators Classical

section IdealProducts

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- The puncture can be written using the ideal itself or its radical;
zero and unit ideals are included. -/
theorem coprime_radical_right_iff (I J : Ideal R) :
    IsCoprime I J.radical ↔ IsCoprime I J := by
  constructor
  · intro hcop
    apply Ideal.coprime_of_no_prime_ge
    intro P hIP hJP hP
    have hrad : J.radical ≤ P := hP.radical_le_iff.mpr hJP
    have htop : (⊤ : Ideal R) ≤ P := by
      rw [← hcop.sup_eq]
      exact sup_le hIP hrad
    exact hP.ne_top (top_le_iff.mp htop)
  · intro hcop
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply top_le_iff.mp
    rw [← hcop.sup_eq]
    exact sup_le_sup_left Ideal.le_radical I

def activeSupport (B : Finset (HeightOneSpectrum R)) (t : HeightOneSpectrum R → ZMod 6) :=
  B.filter (fun p => t p ≠ 0)

def principalSupport (B : Finset (HeightOneSpectrum R)) (t : HeightOneSpectrum R → ZMod 6) :=
  B.filter (fun p => t p = 0)

def primitiveIdeal (B : Finset (HeightOneSpectrum R)) (t : HeightOneSpectrum R → ZMod 6) :
    Ideal R := IdealMobiusMask.primeProduct (activeSupport B t)

def principalIdeal (B : Finset (HeightOneSpectrum R)) (t : HeightOneSpectrum R → ZMod 6) :
    Ideal R := IdealMobiusMask.primeProduct (principalSupport B t)

theorem support_disjoint (B : Finset (HeightOneSpectrum R))
    (t : HeightOneSpectrum R → ZMod 6) :
    Disjoint (activeSupport B t) (principalSupport B t) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2

theorem support_union (B : Finset (HeightOneSpectrum R))
    (t : HeightOneSpectrum R → ZMod 6) :
    activeSupport B t ∪ principalSupport B t = B := by
  ext p
  by_cases h : t p = 0 <;> simp [activeSupport, principalSupport, h]

theorem period_eq_primitive_mul_principal (B : Finset (HeightOneSpectrum R))
    (t : HeightOneSpectrum R → ZMod 6) :
    IdealMobiusMask.primeProduct B = primitiveIdeal B t * principalIdeal B t := by
  unfold primitiveIdeal principalIdeal IdealMobiusMask.primeProduct
  rw [← Finset.prod_union (support_disjoint B t), support_union]

theorem primitiveIdeal_squarefree (B : Finset (HeightOneSpectrum R))
    (t : HeightOneSpectrum R → ZMod 6) : Squarefree (primitiveIdeal B t) :=
  IdealMobiusMask.squarefree_primeProduct _

theorem principalIdeal_squarefree (B : Finset (HeightOneSpectrum R))
    (t : HeightOneSpectrum R → ZMod 6) : Squarefree (principalIdeal B t) :=
  IdealMobiusMask.squarefree_primeProduct _

theorem primitive_coprime_principal (B : Finset (HeightOneSpectrum R))
    (t : HeightOneSpectrum R → ZMod 6) :
    IsCoprime (primitiveIdeal B t) (principalIdeal B t) := by
  unfold primitiveIdeal principalIdeal IdealMobiusMask.primeProduct
  apply IsCoprime.prod_left
  intro p hp
  apply IsCoprime.prod_right
  intro q hq
  apply Ideal.isCoprime_of_isMaximal
  intro he
  have hpq : p = q := HeightOneSpectrum.asIdeal_injective he
  subst q
  exact Finset.disjoint_left.mp (support_disjoint B t) hp hq

end IdealProducts

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]

theorem prime_coprime_contraction_iff
    (p : HeightOneSpectrum (𝓞 K)) (hpS : p ∉ S) (a : S.integer K) :
    IsCoprime p.asIdeal (sIntegerModulusContraction K S a) ↔
      sIntegerSexticResidueMap K S p hpS a ≠ 0 := by
  constructor
  · intro hcop hzero
    have hd := (sIntegerSexticResidueMap_eq_zero_iff_dvd_contraction K S p hpS a).mp hzero
    have he : p.asIdeal ⊔ sIntegerModulusContraction K S a = p.asIdeal :=
      sup_eq_left.mpr (Ideal.dvd_iff_le.mp hd)
    exact p.isPrime.ne_top (he.symm.trans hcop.sup_eq)
  · intro hnonzero
    apply Ideal.isCoprime_iff_sup_eq.mpr
    by_contra hsup
    have he : p.asIdeal = p.asIdeal ⊔ sIntegerModulusContraction K S a :=
      p.isMaximal.eq_of_le hsup le_sup_left
    have hle : sIntegerModulusContraction K S a ≤ p.asIdeal := by
      rw [he]
      exact le_sup_right
    exact hnonzero ((sIntegerSexticResidueMap_eq_zero_iff_dvd_contraction K S p hpS a).mpr
      (Ideal.dvd_iff_le.mpr hle))

theorem finite_residue_mask_eq_coprime
    (P : Finset (HeightOneSpectrum (𝓞 K))) (hPS : ∀ p ∈ P, p ∉ S)
    (a : S.integer K) :
    (if ∃ p : P, sIntegerSexticResidueMap K S p.val (hPS p.val p.property) a = 0
      then (0 : ℂ) else 1) =
    if IsCoprime (IdealMobiusMask.primeProduct P) (sIntegerModulusContraction K S a)
      then 1 else 0 := by
  have hcop : IsCoprime (IdealMobiusMask.primeProduct P) (sIntegerModulusContraction K S a) ↔
      ∀ p : P, sIntegerSexticResidueMap K S p.val (hPS p.val p.property) a ≠ 0 := by
    rw [IdealMobiusMask.primeProduct, IsCoprime.prod_left_iff]
    constructor
    · intro h p
      exact (prime_coprime_contraction_iff K S p.val (hPS p.val p.property) a).mp
        (h p.val p.property)
    · intro h p hp
      exact (prime_coprime_contraction_iff K S p (hPS p hp) a).mpr (h ⟨p, hp⟩)
  by_cases hbad : ∃ p : P, sIntegerSexticResidueMap K S p.val (hPS p.val p.property) a = 0
  · rw [if_pos hbad, if_neg]
    intro h
    obtain ⟨p, hp⟩ := hbad
    exact hcop.mp h p hp
  · rw [if_neg hbad, if_pos]
    apply hcop.mpr
    intro p hp
    exact hbad ⟨p, hp⟩

/-- The principal factor in `ActualFiniteSource.actual_pair_source_split`
is a literal ideal coprimality mask. -/
theorem principal_source_mask_eq_coprime
    (B : Finset (HeightOneSpectrum (𝓞 K))) (hBS : ∀ p ∈ B, p ∉ S)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (a : S.integer K) :
    (if ∃ p : B, t p.val = 0 ∧
      sIntegerSexticResidueMap K S p.val (hBS p.val p.property) a = 0
      then (0 : ℂ) else 1) =
    if IsCoprime (principalIdeal B t) (sIntegerModulusContraction K S a) then 1 else 0 := by
  let hpS := fun p (hp : p ∈ principalSupport B t) => hBS p (Finset.mem_filter.mp hp).1
  have hbad : (∃ p : B, t p.val = 0 ∧
      sIntegerSexticResidueMap K S p.val (hBS p.val p.property) a = 0) ↔
      ∃ p : principalSupport B t, sIntegerSexticResidueMap K S p.val (hpS p.val p.property) a = 0 := by
    constructor
    · rintro ⟨p, ht, hz⟩
      exact ⟨⟨p.val, Finset.mem_filter.mpr ⟨p.property, ht⟩⟩, hz⟩
    · rintro ⟨p, hz⟩
      obtain ⟨hp, ht⟩ := Finset.mem_filter.mp p.property
      exact ⟨⟨p.val, hp⟩, ht, hz⟩
  rw [hbad]
  exact finite_residue_mask_eq_coprime K S (principalSupport B t) hpS a

end HeckeSkeleton.Moments.MOM_INV_STEP.ConductorMasks

end
