module

public import ThetaGlobal.GlobalProjectLocalPhases
public import ThetaGlobal.GlobalProjectDirectReindex

@[expose] public section

/-!
# The literal marked forward mask on an actual ideal generator

Ordinary digits give the zero-extended sextic character, punctures give
the whole-ideal coprimality mask, and marked constant averages give prime
divisibility.  Multiplicities remain in the actual prime-exponent vector.
In particular, an exponent divisible by six still has its unit cutoff.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section

namespace ThetaGlobal.GlobalProjectDirectMask

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open AlgebraicNumberTheory.PowerResidueSymbols
open ThetaGlobal.GlobalProjectLocalDigitTables ThetaGlobal.GlobalProjectForwardCoefficients
open ThetaGlobal.GlobalProjectMarkedSupport
open scoped NumberField Classical BigOperators nonZeroDivisors

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)

local notation "Sf" => (R.A.Sf : Set (HeightOneSpectrum (𝓞 F)))
local notation "P" => ThetaBranch.ExteriorPrime R.A

variable (Adata : ThetaArithmeticData F Sf)

theorem prime_dvd_iff_exponent_ne_zero (I : ExteriorIdeal F Sf) (p : P) :
    p.val.asIdeal ∣ I.val.val ↔ primeExponents I.val p.val ≠ 0 := by
  rw [← mem_idealPrimeSupport_iff F I.val p.val, Finsupp.mem_support_iff]

theorem coprime_iff_exponent_zero (I J : ExteriorIdeal F Sf) :
    IsCoprime I.val.val J.val.val ↔
      ∀ p ∈ exteriorSupport F Sf J, primeExponents I.val p.val = 0 := by
  constructor
  · intro h p hp
    exact GlobalIndexSupport.exponent_zero_of_coprime F Sf I J h p
      (support_dvd R J p hp)
  · intro h
    apply GlobalIndexSupport.coprime_of_exponent_zeros F Sf I J
    intro p hp
    exact h p ((GlobalIndexSupport.mem_exteriorSupport F Sf J p).mpr hp)

theorem generator_residue_zero_iff (I : ExteriorIdeal F Sf) (p : P) :
    ThetaBranch.unitResidue p.val (GlobalActualFrequency.generatorUnit F Sf Adata I) = 0 ↔
      p.val.asIdeal ∣ I.val.val := by
  rw [prime_dvd_iff_exponent_ne_zero R]
  by_cases he : primeExponents I.val p.val = 0
  · have ho : ThetaBranch.order p.val (GlobalActualFrequency.generatorUnit F Sf Adata I) = 0 := by
      rw [GlobalActualReindex.order_generator R.A Adata, he, Nat.cast_zero]
    exact iff_of_false (ThetaBranch.unitResidue_ne_zero p.val _ ho) (not_not.mpr he)
  · have ho : ThetaBranch.order p.val (GlobalActualFrequency.generatorUnit F Sf Adata I) ≠ 0 := by
      rw [GlobalActualReindex.order_generator R.A Adata]
      exact_mod_cast he
    simp only [ThetaBranch.unitResidue, dif_neg ho, he, not_false_eq_true]

theorem ordinary_generator (I : ExteriorIdeal F Sf) (p : P) (j : Fin 6) :
    localMask R Adata p j false (GlobalActualFrequency.generatorUnit F Sf Adata I) =
      if p.val.asIdeal ∣ I.val.val then 0 else
        primeEvaluation F Sf Adata (skeletonPrime R p) (Adata.generator I) ^ j.val := by
  have hz := generator_residue_zero_iff R Adata I p
  by_cases hp : p.val.asIdeal ∣ I.val.val
  · simp [localMask, hz.mpr hp, hp]
  · have he : primeExponents I.val p.val = 0 :=
      not_ne_iff.mp (fun h => hp ((prime_dvd_iff_exponent_ne_zero R I p).mpr h))
    have ho : ThetaBranch.order p.val (GlobalActualFrequency.generatorUnit F Sf Adata I) = 0 := by
      rw [GlobalActualReindex.order_generator R.A Adata, he, Nat.cast_zero]
    simp only [localMask, Bool.false_eq_true, if_false,
      if_neg (fun h => hp (hz.mp h)), if_neg hp,
      GlobalProjectLocalPhases.unitResidue_sInteger R p _ (Adata.generator I) rfl ho,
      primeEvaluation, sIntegerSexticEvaluation, thetaPrimeCharacter]

theorem marked_generator (I : ExteriorIdeal F Sf) (p : P) (j : Fin 6) :
    localMask R Adata p j true (GlobalActualFrequency.generatorUnit F Sf Adata I) =
      if p.val.asIdeal ∣ I.val.val then 1 else 0 := by
  simp only [localMask, Bool.true_eq, if_true, generator_residue_zero_iff R Adata I p]

/-- Reindex the actual ideal residue product, retaining every prime
divisor and its full multiplicity. -/
theorem idealSymbol_product (I : ExteriorIdeal F Sf) (a : Sf.integer F) :
    idealSymbol F Sf Adata I a =
      ∏ p ∈ exteriorSupport F Sf I,
        primeEvaluation F Sf Adata p a ^ primeExponents I.val p.val := by
  letI : Fintype (idealPrimeDivisors F I.val.val) :=
    (idealPrimeDivisors_finite F I.val.val (nonZeroDivisors.coe_ne_zero I.val)).fintype
  unfold idealSymbol sIntegerSexticIdealEvaluation
  apply Finset.prod_bij (fun p _ => (⟨p.val, I.property p.val p.property⟩ : P))
  · intro p _
    exact (GlobalIndexSupport.mem_exteriorSupport F Sf I _).mpr
      ((prime_dvd_iff_exponent_ne_zero R I _).mp p.property)
  · intro p _ q _ he
    exact Subtype.ext (congrArg Subtype.val he)
  · intro p hp
    exact ⟨⟨p.val, support_dvd R I p hp⟩, Finset.mem_univ _, Subtype.ext rfl⟩
  · intro p _
    congr 1
    exact (Ideal.count_associates_factors_eq (nonZeroDivisors.coe_ne_zero I.val)
      p.val.isPrime p.val.ne_bot).trans (primeExponents_apply I.val p.val).symm

variable (d : MarkedDatum F Sf)

def baseIdeal : ExteriorIdeal F Sf := exteriorMul F Sf d.moving d.frozen

theorem baseSupport :
    exteriorSupport F Sf (baseIdeal R d) =
      exteriorSupport F Sf d.moving ∪ exteriorSupport F Sf d.frozen := by
  ext p
  rw [Finset.mem_union, GlobalIndexSupport.mem_exteriorSupport,
    GlobalIndexSupport.mem_exteriorSupport, GlobalIndexSupport.mem_exteriorSupport]
  change primeExponents (d.moving.val * d.frozen.val) p.val ≠ 0 ↔ _
  rw [primeExponents_mul, Finsupp.add_apply]
  omega

theorem baseSupport_subset : exteriorSupport F Sf (baseIdeal R d) ⊆ support R d := by
  rw [baseSupport]
  intro p hp
  rcases Finset.mem_union.mp hp with hm | hf
  · exact Finset.mem_union_left _ hm
  · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_left _ hf))

theorem base_not_mark (p : P) (hp : p ∈ exteriorSupport F Sf (baseIdeal R d)) :
    p ∉ d.marks := by
  intro hm
  rw [baseSupport] at hp
  rcases Finset.mem_union.mp hp with h | h
  · exact (d.marks_coprime p hm).1 (support_dvd R d.moving p h)
  · exact (d.marks_coprime p hm).2.1 (support_dvd R d.frozen p h)

theorem puncture_not_mark (p : P) (hp : p ∈ exteriorSupport F Sf d.puncture) :
    p ∉ d.marks := by
  intro hm
  exact (d.marks_coprime p hm).2.2 (support_dvd R d.puncture p hp)

theorem digitAt_base (p : P) (hp : p ∈ exteriorSupport F Sf (baseIdeal R d)) :
    digitAt R d p = rowDigit F Sf d p := by
  by_cases hm : p ∈ exteriorSupport F Sf d.moving
  · have hf : primeExponents d.frozen.val p.val = 0 :=
      GlobalIndexSupport.exponent_zero_of_coprime F Sf d.frozen d.moving
        d.moving_frozen_coprime.symm p (support_dvd R d.moving p hm)
    have he : primeExponents (baseIdeal R d).val p.val = 1 := by
      change primeExponents (d.moving.val * d.frozen.val) p.val = 1
      rw [primeExponents_mul, Finsupp.add_apply, moving_exponent R d p, if_pos hm, hf]
    apply Fin.ext
    simp only [digitAt, if_pos hm, Fin.val_mk, rowDigit]
    change 1 = primeExponents (baseIdeal R d).val p.val % 6
    simpa only [he]
  · have hf : p ∈ frozenPrimes F Sf d := by
      rw [baseSupport] at hp
      exact Finset.mem_union_left _ ((Finset.mem_union.mp hp).resolve_left hm)
    simp only [digitAt, if_neg hm, if_pos hf]

theorem base_localMask (I : ExteriorIdeal F Sf) (p : P)
    (hp : p ∈ exteriorSupport F Sf (baseIdeal R d)) :
    localMask R Adata p (digitAt R d p) (markAt R d p)
      (GlobalActualFrequency.generatorUnit F Sf Adata I) =
        primeEvaluation F Sf Adata p (Adata.generator I) ^
          primeExponents (baseIdeal R d).val p.val := by
  have hm : markAt R d p = false := by simp [markAt, base_not_mark R d p hp]
  rw [hm, digitAt_base R d p hp, ordinary_generator]
  by_cases hdiv : p.val.asIdeal ∣ I.val.val
  · rw [if_pos hdiv]
    have hz : primeEvaluation F Sf Adata p (Adata.generator I) = 0 := by
      unfold primeEvaluation sIntegerSexticEvaluation
      rw [GlobalIndexSupport.residue_generator_zero F Sf Adata I p hdiv, map_zero]
    rw [hz, zero_pow ((GlobalIndexSupport.mem_exteriorSupport F Sf _ p).mp hp)]
  · rw [if_neg hdiv]
    have he : primeExponents I.val p.val = 0 :=
      not_ne_iff.mp (fun h => hdiv ((prime_dvd_iff_exponent_ne_zero R I p).mpr h))
    have ho : ThetaBranch.order p.val (GlobalActualFrequency.generatorUnit F Sf Adata I) = 0 := by
      rw [GlobalActualReindex.order_generator R.A Adata, he, Nat.cast_zero]
    have hn : sIntegerSexticResidueMap F Sf p.val p.property (Adata.generator I) ≠ 0 := by
      rw [← GlobalProjectLocalPhases.unitResidue_sInteger R p _ (Adata.generator I) rfl ho]
      exact ThetaBranch.unitResidue_ne_zero p.val _ ho
    have hsix : primeEvaluation F Sf Adata p (Adata.generator I) ^ 6 = 1 :=
      ThetaBranch.char_pow_six _
        (GlobalProjectFrequency.thetaPrimeCharacter_order_six F Sf Adata p) _ hn
    exact (pow_eq_pow_mod (primeExponents (baseIdeal R d).val p.val) hsix).symm

theorem outside_base_localMask (I : ExteriorIdeal F Sf)
    (hI : wholeIndexMask F Sf d.puncture d.marks I) (p : P)
    (hp : p ∈ support R d) (hn : p ∉ exteriorSupport F Sf (baseIdeal R d)) :
    localMask R Adata p (digitAt R d p) (markAt R d p)
      (GlobalActualFrequency.generatorUnit F Sf Adata I) = 1 := by
  by_cases hm : p ∈ d.marks
  · rw [show markAt R d p = true by simp [markAt, hm], marked_generator, if_pos (hI.2 p hm)]
  · have hpunc : p ∈ exteriorSupport F Sf d.puncture := by
      have hbase := baseSupport R d
      have hmove : p ∉ exteriorSupport F Sf d.moving :=
        fun h => hn (hbase.symm ▸ Finset.mem_union_left _ h)
      have hfroz : p ∉ exteriorSupport F Sf d.frozen :=
        fun h => hn (hbase.symm ▸ Finset.mem_union_right _ h)
      simpa only [support, frozenPrimes, Finset.mem_union, hmove, hfroz, hm,
        false_or, or_false] using hp
    have he : primeExponents I.val p.val = 0 :=
      (coprime_iff_exponent_zero R I d.puncture).mp hI.1 p hpunc
    have hdiv : ¬p.val.asIdeal ∣ I.val.val :=
      fun h => (prime_dvd_iff_exponent_ne_zero R I p).mp h he
    have hdigit : digitAt R d p = 0 := by
      have hmove : p ∉ exteriorSupport F Sf d.moving := by
        intro h
        apply hn
        rw [baseSupport]
        exact Finset.mem_union_left _ h
      have hbase : primeExponents (baseIdeal R d).val p.val = 0 :=
        not_ne_iff.mp (fun h => hn ((GlobalIndexSupport.mem_exteriorSupport F Sf _ p).mpr h))
      simp [digitAt, hmove, rowDigit, show primeExponents
        (exteriorMul F Sf d.moving d.frozen).val p.val = 0 from hbase]
    simp only [show markAt R d p = false by simp [markAt, hm], hdigit,
      ordinary_generator, if_neg hdiv, Fin.val_zero, pow_zero]

theorem maskProduct_of_wholeIndexMask (I : ExteriorIdeal F Sf)
    (hI : wholeIndexMask F Sf d.puncture d.marks I) :
    (∏ p ∈ support R d, localMask R Adata p (digitAt R d p) (markAt R d p)
      (GlobalActualFrequency.generatorUnit F Sf Adata I)) =
        idealSymbol F Sf Adata (baseIdeal R d) (Adata.generator I) := by
  rw [idealSymbol_product]
  symm
  calc
    _ = ∏ p ∈ exteriorSupport F Sf (baseIdeal R d),
        localMask R Adata p (digitAt R d p) (markAt R d p)
          (GlobalActualFrequency.generatorUnit F Sf Adata I) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact (base_localMask R Adata d I p hp).symm
    _ = _ := Finset.prod_subset (baseSupport_subset R d)
      (fun p hp hn => outside_base_localMask R Adata d I hI p hp hn)

theorem maskProduct_of_not_wholeIndexMask (I : ExteriorIdeal F Sf)
    (hI : ¬ wholeIndexMask F Sf d.puncture d.marks I) :
    (∏ p ∈ support R d, localMask R Adata p (digitAt R d p) (markAt R d p)
      (GlobalActualFrequency.generatorUnit F Sf Adata I)) = 0 := by
  by_cases hc : IsCoprime I.val.val d.puncture.val.val
  · have hm : ¬ ∀ p ∈ d.marks, p.val.asIdeal ∣ I.val.val := fun h => hI ⟨hc, h⟩
    push_neg at hm
    obtain ⟨p, hp, hdiv⟩ := hm
    apply Finset.prod_eq_zero (Finset.mem_union_right _ (Finset.mem_union_right _ hp))
    rw [show markAt R d p = true by simp [markAt, hp], marked_generator, if_neg hdiv]
  · have hp : ¬ ∀ p ∈ exteriorSupport F Sf d.puncture, primeExponents I.val p.val = 0 :=
      fun h => hc ((coprime_iff_exponent_zero R I d.puncture).mpr h)
    push_neg at hp
    obtain ⟨p, hp, he⟩ := hp
    apply Finset.prod_eq_zero (Finset.mem_union_right _
      (Finset.mem_union_left _ (Finset.mem_union_right _ hp)))
    rw [show markAt R d p = false by simp [markAt, puncture_not_mark R d p hp],
      ordinary_generator, if_pos ((prime_dvd_iff_exponent_ne_zero R I p).mpr he)]

/-- The mask is exactly the original whole-index predicate, with the
remaining row character evaluated on the fixed generator. -/
theorem maskProduct (I : ExteriorIdeal F Sf) :
    (∏ p ∈ support R d, localMask R Adata p (digitAt R d p) (markAt R d p)
      (GlobalActualFrequency.generatorUnit F Sf Adata I)) =
      if wholeIndexMask F Sf d.puncture d.marks I then
        idealSymbol F Sf Adata (baseIdeal R d) (Adata.generator I) else 0 := by
  split_ifs with h
  · exact maskProduct_of_wholeIndexMask R Adata d I h
  · exact maskProduct_of_not_wholeIndexMask R Adata d I h

variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
  (D : SourceFactorization R Q T)

theorem forwardCoefficient_generator (H : Input R D Adata) (I : ExteriorIdeal F Sf) :
    GlobalProjectDigitProduct.forwardCoefficient R (row R d) (weight R Adata d)
      (GlobalActualFrequency.generatorUnit F Sf Adata I) =
      if wholeIndexMask F Sf d.puncture d.marks I then
        idealSymbol F Sf Adata (baseIdeal R d) (Adata.generator I) else 0 := by
  rw [weight, forwardCoefficient_literal R D Adata H (row R d) (digits R d) (marks R d)
    _ (Adata.generator I).property]
  simp only [digits, marks]
  rw [← prod_exteriorRows R (row R d), exteriorRows_eq R d]
  exact maskProduct R Adata d I

end ThetaGlobal.GlobalProjectDirectMask
