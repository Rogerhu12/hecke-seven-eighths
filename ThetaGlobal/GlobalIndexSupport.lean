import ThetaGlobal.GlobalProjectFrequency
import ThetaGlobal.ReflectedArithmetic
import HeckeGeneral.Characters.SIntegerSexticPowerMask

/-!
# The literal reflected coefficient satisfies the supported-coordinate rules

The optional-branch restrictions are consequences of actual zero-extended
coefficients.  They are not added to ReflectionIndex and are not assumed
as a global frequency bijection.  This preserves the paper's enlarged
index, while making its nonzero part suitable for unique reconstruction.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GlobalIndexSupport

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
  (D : ThetaArithmeticData K S)

theorem mem_exteriorSupport (I : ExteriorIdeal K S) (p : ExteriorPrime K S) :
    p ∈ exteriorSupport K S I ↔ primeExponents I.val p.val ≠ 0 := by
  constructor
  · intro h
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp h
    have he : q.val = p.val := congrArg Subtype.val hq
    exact Finsupp.mem_support_iff.mp (he ▸ q.property)
  · intro h
    let q : {p : HeightOneSpectrum (𝓞 K) // p ∈ idealPrimeSupport K I.val} :=
      ⟨p.val, Finsupp.mem_support_iff.mpr h⟩
    exact Finset.mem_image.mpr ⟨q, Finset.mem_attach _ q, Subtype.ext rfl⟩

theorem exponent_primeSetIdeal (T : Finset (ExteriorPrime K S)) (p : ExteriorPrime K S) :
    primeExponents (primeSetIdeal K S T).val p.val = if p ∈ T then 1 else 0 := by
  change primeExponents (squarefreeIdeal K (T.image Subtype.val)) p.val = _
  rw [primeExponents_squarefreeIdeal]
  have hm : p.val ∈ T.image Subtype.val ↔ p ∈ T := by
    simp only [Finset.mem_image, Subtype.val_injective.eq_iff, exists_eq_right]
  simp only [hm]

theorem prime_dvd_primeSetIdeal (T : Finset (ExteriorPrime K S))
    (p : ExteriorPrime K S) (hp : p ∈ T) :
    p.val.asIdeal ∣ (primeSetIdeal K S T).val.val := by
  apply (mem_idealPrimeSupport_iff K _ p.val).mp
  apply Finsupp.mem_support_iff.mpr
  rw [exponent_primeSetIdeal, if_pos hp]
  exact one_ne_zero

theorem exponent_zero_of_coprime (I J : ExteriorIdeal K S)
    (h : IsCoprime I.val.val J.val.val) (p : ExteriorPrime K S)
    (hp : p.val.asIdeal ∣ J.val.val) : primeExponents I.val p.val = 0 := by
  by_contra hn
  have hi := (mem_idealPrimeSupport_iff K I.val p.val).mp
    (Finsupp.mem_support_iff.mpr hn)
  have htop : (⊤ : Ideal (𝓞 K)) ≤ p.val.asIdeal := by
    rw [← h.sup_eq]
    exact sup_le (Ideal.dvd_iff_le.mp hi) (Ideal.dvd_iff_le.mp hp)
  exact p.val.isPrime.ne_top (top_le_iff.mp htop)

theorem residue_generator_zero (I : ExteriorIdeal K S) (p : ExteriorPrime K S)
    (hp : p.val.asIdeal ∣ I.val.val) :
    sIntegerSexticResidueMap K S p.val p.property (D.generator I) = 0 := by
  apply (sIntegerSexticResidueMap_eq_zero_iff_mem_map K S p.val p.property _).mpr
  apply Ideal.map_mono (f := algebraMap (𝓞 K) (S.integer K))
    (Ideal.dvd_iff_le.mp hp)
  rw [← D.generator_span I]
  exact Ideal.mem_span_singleton_self _

theorem idealSymbol_generator_zero (I J : ExteriorIdeal K S)
    (p : ExteriorPrime K S) (hpI : p.val.asIdeal ∣ I.val.val)
    (hpJ : p.val.asIdeal ∣ J.val.val) :
    idealSymbol K S D I (D.generator J) = 0 := by
  apply sIntegerSexticIdealEvaluation_eq_zero_of_badPrime K S D.root6 D.primitive6
    D.embedding I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun q hq => D.away_six q (I.property q hq)) _ p.val hpI
  exact residue_generator_zero K S D J p hpJ

variable (d : MarkedDatum K S) (i : ReflectionIndex K S d) (θ : HeckeCharacter K)

theorem frozenOmega_nonzero
    (hi : ReflectedArithmetic.reflectedCoefficient K S D d i θ ≠ 0) :
    frozenOmega K S D d i θ ≠ 0 := by
  intro h
  apply hi
  simp [ReflectedArithmetic.reflectedCoefficient, h]

theorem active_localWeyl_nonzero
    (hi : ReflectedArithmetic.reflectedCoefficient K S D d i θ ≠ 0)
    (p : ExteriorPrime K S) (hp : p ∈ i.activeFrozen) :
    localWeylScalar K S D p (rowDigit K S d p)
      (primeExponents i.numeratorFrozen.val p.val) ≠ 0 := by
  have h := frozenOmega_nonzero K S D d i θ hi
  unfold frozenOmega at h
  have hprod := (mul_ne_zero_iff.mp h).2
  exact (mul_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp hprod p hp)).1

theorem optional_frozen_exponent_zero
    (hi : ReflectedArithmetic.reflectedCoefficient K S D d i θ ≠ 0)
    (p : ExteriorPrime K S) (hp : p ∈ i.activeFrozen)
    (hj : (rowDigit K S d p).val = 0) :
    primeExponents i.numeratorFrozen.val p.val = 0 := by
  have h := active_localWeyl_nonzero K S D d i θ hi p hp
  have hj' : rowDigit K S d p = 0 := Fin.ext hj
  rw [hj'] at h
  exact GlobalProjectFrequency.localWeylScalar_zero_digit_nonzero_implies_exponent_zero
    K S D p _ h

theorem marked_column_exponent_zero
    (hi : ReflectedArithmetic.reflectedCoefficient K S D d i θ ≠ 0)
    (p : ExteriorPrime K S) (hp : p ∈ i.activeMarks) :
    primeExponents i.c.val p.val = 0 := by
  by_contra hn
  have hc := (mem_idealPrimeSupport_iff K i.c.val p.val).mp
    (Finsupp.mem_support_iff.mpr hn)
  have hz := idealSymbol_generator_zero K S D
    (activeMarkedIdeal K S d i) i.c p (prime_dvd_primeSetIdeal K S i.activeMarks p hp) hc
  apply hi
  simp [ReflectedArithmetic.reflectedCoefficient, hz]

def branch : GlobalFrequency.Branch (ExteriorPrime K S) where
  active := (i.activeFrozen ∪ i.activeMarks : Finset _) 
  a := fun p => primeExponents i.numeratorFrozen.val p.val
  c := fun p => primeExponents i.c.val p.val
  n := fun p => primeExponents i.n.val p.val

def mandatory : Set (ExteriorPrime K S) :=
  {p | p ∈ frozenPrimes K S d ∧ (rowDigit K S d p).val ≠ 0}

/-- Every nonzero literal reflected arithmetic coefficient is in the
domain where the valuation reconstruction is injective. -/
theorem supported
    (hi : ReflectedArithmetic.reflectedCoefficient K S D d i θ ≠ 0) :
    GlobalFrequency.Supported (mandatory K S d) (branch K S d i) := by
  refine {
    a_outside := ?_
    c_active := ?_
    n_active := ?_
    c_squarefree := ?_
    a_digits := i.frozen_digits
    mandatory_active := ?_
    optional_zero := ?_ }
  · intro p hp
    by_contra hn
    exact hp (Finset.mem_union_left _
      (i.frozen_support ((mem_exteriorSupport K S i.numeratorFrozen p).mpr hn)))
  · intro p hp
    rcases Finset.mem_union.mp hp with hf | hm
    · exact exponent_zero_of_coprime K S i.c (activeFrozenIdeal K S d i) i.c_coprime
        p (prime_dvd_primeSetIdeal K S i.activeFrozen p hf)
    · exact marked_column_exponent_zero K S D d i θ hi p hm
  · intro p hp
    apply exponent_zero_of_coprime K S i.n
      (exteriorMul K S (activeFrozenIdeal K S d i) (activeMarkedIdeal K S d i))
      i.n_coprime p
    rcases Finset.mem_union.mp hp with hf | hm
    · exact dvd_mul_of_dvd_left (prime_dvd_primeSetIdeal K S i.activeFrozen p hf) _
    · exact dvd_mul_of_dvd_right (prime_dvd_primeSetIdeal K S i.activeMarks p hm) _
  · intro p
    exact Multiset.nodup_iff_count_le_one.mp
      ((squarefree_iff_nodup_normalizedFactors (nonZeroDivisors.coe_ne_zero i.c.val)).mp
        i.c_squarefree) p.val.asIdeal
  · intro p hp
    exact Finset.mem_union_left _ (i.nonzero_active p hp.1 hp.2)
  · intro p hp hm
    by_cases hf : p ∈ i.activeFrozen
    · apply optional_frozen_exponent_zero K S D d i θ hi p hf
      by_contra hj
      exact hm ⟨i.frozen_subset hf, hj⟩
    · by_contra hn
      exact hf (i.frozen_support ((mem_exteriorSupport K S i.numeratorFrozen p).mpr hn))

theorem marks_disjoint_frozen : Disjoint d.marks (frozenPrimes K S d) := by
  apply Finset.disjoint_left.mpr
  intro p hm hf
  rcases Finset.mem_union.mp hf with hf | hp
  · exact (d.marks_coprime p hm).2.1
      ((mem_idealPrimeSupport_iff K d.frozen.val p.val).mp
        (Finsupp.mem_support_iff.mpr ((mem_exteriorSupport K S d.frozen p).mp hf)))
  · exact (d.marks_coprime p hm).2.2
      ((mem_idealPrimeSupport_iff K d.puncture.val p.val).mp
        (Finsupp.mem_support_iff.mpr ((mem_exteriorSupport K S d.puncture p).mp hp)))

theorem exterior_ext (I J : ExteriorIdeal K S)
    (h : ∀ p : ExteriorPrime K S, primeExponents I.val p.val = primeExponents J.val p.val) :
    I = J := by
  apply Subtype.ext
  apply (primeExponentEquiv (R := 𝓞 K)).injective
  ext p
  by_cases hp : p ∈ S
  · have hi : primeExponents I.val p = 0 := by
      by_contra hn
      exact I.property p ((mem_idealPrimeSupport_iff K I.val p).mp
        (Finsupp.mem_support_iff.mpr hn)) hp
    have hj : primeExponents J.val p = 0 := by
      by_contra hn
      exact J.property p ((mem_idealPrimeSupport_iff K J.val p).mp
        (Finsupp.mem_support_iff.mpr hn)) hp
    exact hi.trans hj.symm
  · exact h ⟨p, hp⟩

/-- Disjoint prime-exponent supports imply coprimality of the actual
integral ideals. This uses Dedekind ideal factorization only. -/
theorem coprime_of_exponent_zeros (I J : ExteriorIdeal K S)
    (h : ∀ p : ExteriorPrime K S,
      primeExponents J.val p.val ≠ 0 → primeExponents I.val p.val = 0) :
    IsCoprime I.val.val J.val.val := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra hn
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (I.val.val ⊔ J.val.val) hn
  have hMn : M ≠ ⊥ := by
    intro hz
    apply nonZeroDivisors.coe_ne_zero I.val
    exact bot_unique ((le_sup_left.trans hle).trans hz.le)
  let p : HeightOneSpectrum (𝓞 K) := ⟨M, hM.isPrime, hMn⟩
  have hI : p.asIdeal ∣ I.val.val := Ideal.dvd_iff_le.mpr (le_sup_left.trans hle)
  have hJ : p.asIdeal ∣ J.val.val := Ideal.dvd_iff_le.mpr (le_sup_right.trans hle)
  let q : ExteriorPrime K S := ⟨p, I.property p hI⟩
  have hIe : primeExponents I.val p ≠ 0 :=
    Finsupp.mem_support_iff.mp ((mem_idealPrimeSupport_iff K I.val p).mpr hI)
  have hJe : primeExponents J.val p ≠ 0 :=
    Finsupp.mem_support_iff.mp ((mem_idealPrimeSupport_iff K J.val p).mpr hJ)
  exact hIe (h q hJe)

/-- The numerical branch and unit sector retain every data field of the
actual index. The two active sets are recovered separately because marks
and frozen/puncture primes are disjoint. -/
theorem index_eq_of_branch_unit (j : ReflectionIndex K S d)
    (hb : branch K S d i = branch K S d j) (hu : i.unitSector = j.unitSector) : i = j := by
  have ha : i.numeratorFrozen = j.numeratorFrozen :=
    exterior_ext K S _ _ (congrFun (congrArg GlobalFrequency.Branch.a hb))
  have hc : i.c = j.c :=
    exterior_ext K S _ _ (congrFun (congrArg GlobalFrequency.Branch.c hb))
  have hn : i.n = j.n :=
    exterior_ext K S _ _ (congrFun (congrArg GlobalFrequency.Branch.n hb))
  have hactive : (i.activeFrozen ∪ i.activeMarks : Finset _) = j.activeFrozen ∪ j.activeMarks :=
    Finset.coe_injective (congrArg GlobalFrequency.Branch.active hb)
  have hF : i.activeFrozen = j.activeFrozen := by
    ext p
    constructor
    · intro hp
      have hall : p ∈ j.activeFrozen ∪ j.activeMarks :=
        hactive ▸ Finset.mem_union_left _ hp
      rcases Finset.mem_union.mp hall with h | h
      · exact h
      · exact False.elim ((Finset.disjoint_left.mp (marks_disjoint_frozen K S d))
          (j.marks_subset h) (i.frozen_subset hp))
    · intro hp
      have hall : p ∈ i.activeFrozen ∪ i.activeMarks :=
        hactive.symm ▸ Finset.mem_union_left _ hp
      rcases Finset.mem_union.mp hall with h | h
      · exact h
      · exact False.elim ((Finset.disjoint_left.mp (marks_disjoint_frozen K S d))
          (i.marks_subset h) (j.frozen_subset hp))
  have hM : i.activeMarks = j.activeMarks := by
    ext p
    constructor
    · intro hp
      have hall : p ∈ j.activeFrozen ∪ j.activeMarks :=
        hactive ▸ Finset.mem_union_right _ hp
      rcases Finset.mem_union.mp hall with h | h
      · exact False.elim ((Finset.disjoint_left.mp (marks_disjoint_frozen K S d))
          (i.marks_subset hp) (j.frozen_subset h))
      · exact h
    · intro hp
      have hall : p ∈ i.activeFrozen ∪ i.activeMarks :=
        hactive.symm ▸ Finset.mem_union_right _ hp
      rcases Finset.mem_union.mp hall with h | h
      · exact False.elim ((Finset.disjoint_left.mp (marks_disjoint_frozen K S d))
          (j.marks_subset hp) (i.frozen_subset h))
      · exact h
  cases i
  cases j
  cases hF
  cases hM
  cases ha
  cases hc
  cases hn
  cases hu
  rfl

end ThetaGlobal.GlobalIndexSupport
