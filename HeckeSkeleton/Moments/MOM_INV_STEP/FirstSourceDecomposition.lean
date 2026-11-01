import HeckeGeneral.Arithmetic.IdealMobiusMask
import HeckeSkeleton.Moments.MOM_INV_STEP.SupportPartition
import Mathlib.Tactic.Tauto

/-!
# The actual squarefree source decompositions

All factors here are defined from the prime exponents of the original
nonzero integral ideals. The first extraction is exactly the gcd with the
cube radical; the next extraction is exactly the gcd of the two remaining
columns. No factorization or coprimality relation is an input.

The support identities use the same local divisibility bits and exponent
vector as `ActualFiniteSource` and `CanonicalConductor`. The final pair
decomposition is the second-transform identity `xᵢ = g' zᵢ`.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstSourceDecomposition

open IsDedekindDomain UniqueFactorizationMonoid HeckeGeneral.Arithmetic
open IdealMobiusMask
open scoped BigOperators Classical nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

def primeSupport (I : (Ideal R)⁰) : Finset (HeightOneSpectrum R) :=
  (primeExponents I).support

@[simp] theorem mem_primeSupport (I : (Ideal R)⁰) (p : HeightOneSpectrum R) :
    p ∈ primeSupport I ↔ p.asIdeal ∣ I.val := by
  rw [primeSupport, Finsupp.mem_support_iff, primeExponents_apply,
    Multiset.count_ne_zero, mem_normalizedFactors_iff (nonZeroDivisors.coe_ne_zero I)]
  exact and_iff_right p.prime

/-- Reconstruction of a squarefree ideal from its actual prime support. -/
theorem primeProduct_support (I : (Ideal R)⁰) (hI : Squarefree I.val) :
    primeProduct (primeSupport I) = I.val := by
  have hn := (squarefree_iff_nodup_normalizedFactors
    (nonZeroDivisors.coe_ne_zero I)).mp hI
  have hm : (primeSupport I).val.map HeightOneSpectrum.asIdeal = normalizedFactors I.val := by
    apply (Multiset.Nodup.ext
      ((primeSupport I).nodup.map HeightOneSpectrum.asIdeal_injective) hn).mpr
    intro P
    constructor
    · intro hP
      obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hP
      exact (mem_normalizedFactors_iff (nonZeroDivisors.coe_ne_zero I)).mpr
        ⟨p.prime, (mem_primeSupport I p).mp hp⟩
    · intro hP
      let p := HeightOneSpectrum.ofPrime (prime_of_normalized_factor P hP)
      exact Multiset.mem_map.mpr
        ⟨p, (mem_primeSupport I p).mpr (dvd_of_mem_normalizedFactors hP), rfl⟩
  calc
    _ = (normalizedFactors (primeProduct (primeSupport I))).prod :=
      (Ideal.prod_normalizedFactors_eq_self (primeProduct_ne_bot _)).symm
    _ = (normalizedFactors I.val).prod := by rw [normalizedFactors_primeProduct, hm]
    _ = I.val := Ideal.prod_normalizedFactors_eq_self (nonZeroDivisors.coe_ne_zero I)

/-- The support product is the ordinary ideal radical, including for
cube ideals with repeated prime factors. -/
theorem radical_eq_primeProduct (I : (Ideal R)⁰) :
    I.val.radical = primeProduct (primeSupport I) := by
  rw [primeProduct_eq_iInf]
  apply le_antisymm
  · apply le_iInf
    intro p
    apply le_iInf
    intro hp
    exact p.isPrime.radical_le_iff.mpr
      (Ideal.dvd_iff_le.mp ((mem_primeSupport I p).mp hp))
  · rw [Ideal.radical_eq_sInf]
    apply le_sInf
    intro P hP
    have hP0 : P ≠ ⊥ := ne_bot_of_le_ne_bot (nonZeroDivisors.coe_ne_zero I) hP.1
    let p : HeightOneSpectrum R := ⟨P, hP.2, hP0⟩
    apply iInf_le_of_le p
    apply iInf_le_of_le ((mem_primeSupport I p).mpr (Ideal.dvd_iff_le.mpr hP.1))
    exact le_rfl

theorem primeProduct_coprime {S T : Finset (HeightOneSpectrum R)}
    (hST : Disjoint S T) : IsCoprime (primeProduct S) (primeProduct T) := by
  unfold primeProduct
  apply IsCoprime.prod_left
  intro p hp
  apply IsCoprime.prod_right
  intro q hq
  apply p.isCoprime_of_ne q
  intro hpq
  subst q
  exact Finset.disjoint_left.mp hST hp hq

theorem primeProduct_split (S T : Finset (HeightOneSpectrum R)) :
    primeProduct S = primeProduct (S ∩ T) * primeProduct (S \ T) := by
  have he : S = (S ∩ T) ∪ (S \ T) := by
    ext p
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hd : Disjoint (S ∩ T) (S \ T) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_inter.mp hp).2
  calc
    _ = primeProduct ((S ∩ T) ∪ (S \ T)) := congrArg primeProduct he
    _ = _ := Finset.prod_union hd

theorem gcd_primeProducts (S T : Finset (HeightOneSpectrum R)) :
    gcd (primeProduct S) (primeProduct T) = primeProduct (S ∩ T) := by
  have hm : S.val.map HeightOneSpectrum.asIdeal ∩ T.val.map HeightOneSpectrum.asIdeal =
      (S ∩ T).val.map HeightOneSpectrum.asIdeal := by
    apply (Multiset.Nodup.ext
      (Multiset.Nodup.inter_left _ (S.nodup.map HeightOneSpectrum.asIdeal_injective))
      ((S ∩ T).nodup.map HeightOneSpectrum.asIdeal_injective)).mpr
    intro P
    constructor
    · intro hP
      obtain ⟨hp, hq⟩ := Multiset.mem_inter.mp hP
      obtain ⟨p, hp, hpP⟩ := Multiset.mem_map.mp hp
      obtain ⟨q, hq, hqP⟩ := Multiset.mem_map.mp hq
      have hpq : p = q := HeightOneSpectrum.asIdeal_injective (hpP.trans hqP.symm)
      subst q
      exact Multiset.mem_map.mpr ⟨p, Finset.mem_inter.mpr ⟨hp, hq⟩, hpP⟩
    · intro hP
      obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hP
      exact Multiset.mem_inter.mpr
        ⟨Multiset.mem_map.mpr ⟨p, (Finset.mem_inter.mp hp).1, rfl⟩,
          Multiset.mem_map.mpr ⟨p, (Finset.mem_inter.mp hp).2, rfl⟩⟩
  rw [Ideal.gcd_eq_sup, Ideal.sup_eq_prod_inf_factors (primeProduct_ne_bot S)
    (primeProduct_ne_bot T), normalizedFactors_primeProduct,
    normalizedFactors_primeProduct, hm, Finset.prod_map_val] <;> rfl

def extractedSupport (n b₁ b₂ : (Ideal R)⁰) : Finset (HeightOneSpectrum R) :=
  primeSupport n ∩ primeSupport (b₁ * b₂)

def remainingSupport (n b₁ b₂ : (Ideal R)⁰) : Finset (HeightOneSpectrum R) :=
  primeSupport n \ primeSupport (b₁ * b₂)

def commonSupport (n₁ n₂ b₁ b₂ : (Ideal R)⁰) : Finset (HeightOneSpectrum R) :=
  (primeSupport n₁ ∩ primeSupport n₂) \ primeSupport (b₁ * b₂)

def residualSupport (n₁ n₂ b₁ b₂ : (Ideal R)⁰) : Finset (HeightOneSpectrum R) :=
  (primeSupport n₁ \ primeSupport n₂) \ primeSupport (b₁ * b₂)

def A (n b₁ b₂ : (Ideal R)⁰) : Ideal R := primeProduct (extractedSupport n b₁ b₂)
def remaining (n b₁ b₂ : (Ideal R)⁰) : Ideal R := primeProduct (remainingSupport n b₁ b₂)
def C (n₁ n₂ b₁ b₂ : (Ideal R)⁰) : Ideal R := primeProduct (commonSupport n₁ n₂ b₁ b₂)
def u (n₁ n₂ b₁ b₂ : (Ideal R)⁰) : Ideal R := primeProduct (residualSupport n₁ n₂ b₁ b₂)

theorem A_eq_gcd (n b₁ b₂ : (Ideal R)⁰) (hn : Squarefree n.val) :
    A n b₁ b₂ = gcd n.val (b₁.val * b₂.val).radical := by
  rw [show (b₁.val * b₂.val).radical = primeProduct (primeSupport (b₁ * b₂)) from
    radical_eq_primeProduct (b₁ * b₂), ← primeProduct_support n hn, gcd_primeProducts] <;> rfl

theorem commonSupport_eq_inter_remaining (n₁ n₂ b₁ b₂ : (Ideal R)⁰) :
    commonSupport n₁ n₂ b₁ b₂ =
      remainingSupport n₁ b₁ b₂ ∩ remainingSupport n₂ b₁ b₂ := by
  ext p
  simp only [commonSupport, remainingSupport, Finset.mem_sdiff, Finset.mem_inter]
  tauto

theorem C_eq_gcd (n₁ n₂ b₁ b₂ : (Ideal R)⁰) :
    C n₁ n₂ b₁ b₂ = gcd (remaining n₁ b₁ b₂) (remaining n₂ b₁ b₂) := by
  rw [remaining, remaining, gcd_primeProducts, ← commonSupport_eq_inter_remaining] <;> rfl

theorem remaining_eq_C_mul_u (n₁ n₂ b₁ b₂ : (Ideal R)⁰) :
    remaining n₁ b₁ b₂ = C n₁ n₂ b₁ b₂ * u n₁ n₂ b₁ b₂ := by
  have hc : remainingSupport n₁ b₁ b₂ ∩ primeSupport n₂ = commonSupport n₁ n₂ b₁ b₂ := by
    ext p
    simp only [remainingSupport, commonSupport, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hu : remainingSupport n₁ b₁ b₂ \ primeSupport n₂ = residualSupport n₁ n₂ b₁ b₂ := by
    ext p
    simp only [remainingSupport, residualSupport, Finset.mem_sdiff]
    tauto
  rw [remaining, primeProduct_split _ (primeSupport n₂), hc, hu] <;> rfl

theorem first_decomposition (n₁ n₂ b₁ b₂ : (Ideal R)⁰) (hn₁ : Squarefree n₁.val)
    (hn₂ : Squarefree n₂.val) :
    n₁.val = A n₁ b₁ b₂ * C n₁ n₂ b₁ b₂ * u n₁ n₂ b₁ b₂ ∧
      n₂.val = A n₂ b₁ b₂ * C n₁ n₂ b₁ b₂ * u n₂ n₁ b₁ b₂ := by
  have hleft (n m : (Ideal R)⁰) (hn : Squarefree n.val) :
      n.val = A n b₁ b₂ * C n m b₁ b₂ * u n m b₁ b₂ := by
    calc
      _ = primeProduct (primeSupport n) := (primeProduct_support n hn).symm
      _ = A n b₁ b₂ * remaining n b₁ b₂ :=
        primeProduct_split (primeSupport n) (primeSupport (b₁ * b₂))
      _ = _ := by rw [remaining_eq_C_mul_u, mul_assoc]
  refine ⟨hleft n₁ n₂ hn₁, ?_⟩
  have hc : C n₂ n₁ b₁ b₂ = C n₁ n₂ b₁ b₂ := by
    unfold C commonSupport
    rw [Finset.inter_comm]
  simpa only [hc] using hleft n₂ n₁ hn₂

theorem first_factors_squarefree (n₁ n₂ b₁ b₂ : (Ideal R)⁰) :
    Squarefree (A n₁ b₁ b₂) ∧ Squarefree (A n₂ b₁ b₂) ∧
      Squarefree (C n₁ n₂ b₁ b₂) ∧ Squarefree (u n₁ n₂ b₁ b₂) ∧
      Squarefree (u n₂ n₁ b₁ b₂) :=
  ⟨squarefree_primeProduct _, squarefree_primeProduct _, squarefree_primeProduct _,
    squarefree_primeProduct _, squarefree_primeProduct _⟩

theorem first_factors_ne_zero (n₁ n₂ b₁ b₂ : (Ideal R)⁰) :
    A n₁ b₁ b₂ ≠ 0 ∧ A n₂ b₁ b₂ ≠ 0 ∧ C n₁ n₂ b₁ b₂ ≠ 0 ∧
      u n₁ n₂ b₁ b₂ ≠ 0 ∧ u n₂ n₁ b₁ b₂ ≠ 0 :=
  ⟨primeProduct_ne_bot _, primeProduct_ne_bot _, primeProduct_ne_bot _,
    primeProduct_ne_bot _, primeProduct_ne_bot _⟩

/-- The actual residual columns are coprime, the common factor is
coprime to both, and all three are coprime to the full cube radical. -/
theorem first_factors_coprime (n₁ n₂ b₁ b₂ : (Ideal R)⁰) :
    IsCoprime (u n₁ n₂ b₁ b₂) (u n₂ n₁ b₁ b₂) ∧
      IsCoprime (C n₁ n₂ b₁ b₂) (u n₁ n₂ b₁ b₂ * u n₂ n₁ b₁ b₂) ∧
      IsCoprime (C n₁ n₂ b₁ b₂ * u n₁ n₂ b₁ b₂ * u n₂ n₁ b₁ b₂)
        (b₁.val * b₂.val).radical := by
  have huc : Disjoint (residualSupport n₁ n₂ b₁ b₂) (residualSupport n₂ n₁ b₁ b₂) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    simp only [residualSupport, Finset.mem_sdiff] at hp hq
    tauto
  have hc1 : Disjoint (commonSupport n₁ n₂ b₁ b₂) (residualSupport n₁ n₂ b₁ b₂) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    simp only [commonSupport, residualSupport, Finset.mem_sdiff, Finset.mem_inter] at hp hq
    tauto
  have hc2 : Disjoint (commonSupport n₁ n₂ b₁ b₂) (residualSupport n₂ n₁ b₁ b₂) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    simp only [commonSupport, residualSupport, Finset.mem_sdiff, Finset.mem_inter] at hp hq
    tauto
  have hcB : Disjoint (commonSupport n₁ n₂ b₁ b₂) (primeSupport (b₁ * b₂)) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.mem_sdiff.mp hp).2 hq
  have huB (n m : (Ideal R)⁰) :
      Disjoint (residualSupport n m b₁ b₂) (primeSupport (b₁ * b₂)) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.mem_sdiff.mp hp).2 hq
  refine ⟨primeProduct_coprime huc,
    (primeProduct_coprime hc1).mul_right (primeProduct_coprime hc2), ?_⟩
  rw [show (b₁.val * b₂.val).radical = primeProduct (primeSupport (b₁ * b₂)) from
    radical_eq_primeProduct (b₁ * b₂)]
  exact ((primeProduct_coprime hcB).mul_left (primeProduct_coprime (huB n₁ n₂))).mul_left
    (primeProduct_coprime (huB n₂ n₁))

theorem primeExponent_eq_zero_iff (I : (Ideal R)⁰) (p : HeightOneSpectrum R) :
    primeExponents I p = 0 ↔ ¬ p.asIdeal ∣ I.val := by
  simpa only [primeSupport, Finsupp.mem_support_iff, not_not] using
    not_congr (mem_primeSupport I p)

/-- Identification with the left residual support in the actual finite
local conductor calculation. The ambient support may be enlarged. -/
theorem residualSupport_eq_leftResidual (n₁ n₂ b₁ b₂ : (Ideal R)⁰)
    (Q : Finset (HeightOneSpectrum R)) (hn₁ : primeSupport n₁ ⊆ Q) :
    residualSupport n₁ n₂ b₁ b₂ =
      SupportPartition.leftResidual Q (primeExponents (b₁ * b₂))
        (fun p => decide (p.asIdeal ∣ n₁.val)) (fun p => decide (p.asIdeal ∣ n₂.val)) := by
  ext p
  have hQ : p.asIdeal ∣ n₁.val → p ∈ Q := fun hp => hn₁ ((mem_primeSupport n₁ p).mpr hp)
  simp only [residualSupport, Finset.mem_sdiff, mem_primeSupport,
    SupportPartition.leftResidual, Finset.mem_filter, primeExponent_eq_zero_iff,
    decide_eq_true_eq, decide_eq_false_iff_not]
  tauto

theorem residualSupport_eq_rightResidual (n₁ n₂ b₁ b₂ : (Ideal R)⁰)
    (Q : Finset (HeightOneSpectrum R)) (hn₂ : primeSupport n₂ ⊆ Q) :
    residualSupport n₂ n₁ b₁ b₂ =
      SupportPartition.rightResidual Q (primeExponents (b₁ * b₂))
        (fun p => decide (p.asIdeal ∣ n₁.val)) (fun p => decide (p.asIdeal ∣ n₂.val)) := by
  ext p
  have hQ : p.asIdeal ∣ n₂.val → p ∈ Q := fun hp => hn₂ ((mem_primeSupport n₂ p).mpr hp)
  simp only [residualSupport, Finset.mem_sdiff, mem_primeSupport,
    SupportPartition.rightResidual, Finset.mem_filter, primeExponent_eq_zero_iff,
    decide_eq_true_eq, decide_eq_false_iff_not]
  tauto

theorem commonSupport_eq_commonResidual (n₁ n₂ b₁ b₂ : (Ideal R)⁰)
    (Q : Finset (HeightOneSpectrum R)) (hn₁ : primeSupport n₁ ⊆ Q) :
    commonSupport n₁ n₂ b₁ b₂ =
      SupportPartition.commonResidual Q (primeExponents (b₁ * b₂))
        (fun p => decide (p.asIdeal ∣ n₁.val)) (fun p => decide (p.asIdeal ∣ n₂.val)) := by
  ext p
  have hQ : p.asIdeal ∣ n₁.val → p ∈ Q := fun hp => hn₁ ((mem_primeSupport n₁ p).mpr hp)
  simp only [commonSupport, Finset.mem_sdiff, Finset.mem_inter, mem_primeSupport,
    SupportPartition.commonResidual, Finset.mem_filter, primeExponent_eq_zero_iff,
    decide_eq_true_eq]
  tauto

def pairCommon (x₁ x₂ : (Ideal R)⁰) : Ideal R :=
  primeProduct (primeSupport x₁ ∩ primeSupport x₂)

def pairResidual (x₁ x₂ : (Ideal R)⁰) : Ideal R :=
  primeProduct (primeSupport x₁ \ primeSupport x₂)

theorem pairCommon_eq_gcd (x₁ x₂ : (Ideal R)⁰)
    (hx₁ : Squarefree x₁.val) (hx₂ : Squarefree x₂.val) :
    pairCommon x₁ x₂ = gcd x₁.val x₂.val := by
  rw [← primeProduct_support x₁ hx₁, ← primeProduct_support x₂ hx₂,
    gcd_primeProducts] <;> rfl

/-- The second expanded square has an actual common-factor decomposition
with pairwise coprime squarefree factors. The original columns determine
every factor; no chosen decomposition is supplied by the caller. -/
theorem second_decomposition (x₁ x₂ : (Ideal R)⁰)
    (hx₁ : Squarefree x₁.val) (hx₂ : Squarefree x₂.val) :
    x₁.val = pairCommon x₁ x₂ * pairResidual x₁ x₂ ∧
      x₂.val = pairCommon x₁ x₂ * pairResidual x₂ x₁ ∧
      pairCommon x₁ x₂ = gcd x₁.val x₂.val ∧
      Squarefree (pairCommon x₁ x₂) ∧ Squarefree (pairResidual x₁ x₂) ∧
      Squarefree (pairResidual x₂ x₁) ∧
      IsCoprime (pairCommon x₁ x₂) (pairResidual x₁ x₂ * pairResidual x₂ x₁) ∧
      IsCoprime (pairResidual x₁ x₂) (pairResidual x₂ x₁) := by
  have hleft : x₁.val = pairCommon x₁ x₂ * pairResidual x₁ x₂ :=
    (primeProduct_support x₁ hx₁).symm.trans
      (primeProduct_split (primeSupport x₁) (primeSupport x₂))
  have hright : x₂.val = pairCommon x₁ x₂ * pairResidual x₂ x₁ := by
    have h := (primeProduct_support x₂ hx₂).symm.trans
      (primeProduct_split (primeSupport x₂) (primeSupport x₁))
    simpa only [pairCommon, pairResidual, Finset.inter_comm] using h
  have hc1 : Disjoint (primeSupport x₁ ∩ primeSupport x₂)
      (primeSupport x₁ \ primeSupport x₂) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    simp only [Finset.mem_inter, Finset.mem_sdiff] at hp hq
    tauto
  have hc2 : Disjoint (primeSupport x₁ ∩ primeSupport x₂)
      (primeSupport x₂ \ primeSupport x₁) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    simp only [Finset.mem_inter, Finset.mem_sdiff] at hp hq
    tauto
  have h12 : Disjoint (primeSupport x₁ \ primeSupport x₂)
      (primeSupport x₂ \ primeSupport x₁) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    simp only [Finset.mem_sdiff] at hp hq
    tauto
  exact ⟨hleft, hright, pairCommon_eq_gcd x₁ x₂ hx₁ hx₂,
    squarefree_primeProduct _, squarefree_primeProduct _, squarefree_primeProduct _,
    (primeProduct_coprime hc1).mul_right (primeProduct_coprime hc2), primeProduct_coprime h12⟩

def divisorResidual (I D : (Ideal R)⁰) : Ideal R :=
  primeProduct (primeSupport I \ primeSupport D)

/-- A divisor chosen in the actual squarefree Poisson mask determines
its complementary ideal. This supplies `d₂ * (g' / d₂) = g'` directly
from the original divisor index, with all source zeros still exact. -/
theorem squarefree_divisor_decomposition (I D : (Ideal R)⁰)
    (hI : Squarefree I.val) (hD : D.val ∣ I.val) :
    I.val = D.val * divisorResidual I D ∧
      IsCoprime D.val (divisorResidual I D) ∧
      Squarefree (divisorResidual I D) ∧ divisorResidual I D ≠ 0 := by
  have hsub : primeSupport D ⊆ primeSupport I := by
    intro p hp
    exact (mem_primeSupport I p).mpr (((mem_primeSupport D p).mp hp).trans hD)
  have hDs : Squarefree D.val := hI.squarefree_of_dvd hD
  have he : I.val = D.val * divisorResidual I D := by
    have h := primeProduct_split (primeSupport I) (primeSupport D)
    rw [Finset.inter_eq_right.mpr hsub, primeProduct_support I hI,
      primeProduct_support D hDs] at h
    exact h
  have hcop : IsCoprime D.val (divisorResidual I D) := by
    rw [← primeProduct_support D hDs]
    apply primeProduct_coprime
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.mem_sdiff.mp hq).2 hp
  exact ⟨he, hcop, squarefree_primeProduct _, primeProduct_ne_bot _⟩

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstSourceDecomposition

end
