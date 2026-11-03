import HeckeSkeleton.GramDefinitions
import HeckeGeneral.Analysis.SixthPowerFreeDecomposition
import HeckeGeneral.Analysis.FrequencyRowCounting
import HeckeGeneral.Analysis.IdealAmplifierSmallPower

/-!
GR-07 (exceptional frequency count).

Orbits of nonzero S-integers modulo sixth powers of S-units whose ideal has every
prime exponent outside the support of `A` divisible by six are counted by
(exceptional ideals of norm at most `X`) times (sixth-power unit sectors).
An exceptional ideal splits (sixth-power-free part)*(amplifier)^6, with the free
part supported on `A` (at most `6^(#primes of A)` choices) and the amplifier of
norm at most `X^(1/6)`, so the ideal count is `<< N(A)^eps X^(1/6)`.

The passage from orbits to (ideal, sector) pairs is constructed directly from
the contraction ideal and a reference S-integer for each ideal; no probe data,
generator system or principal-ideal hypothesis on the S-integers is used.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.GramExceptionalCount
open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors
-- Additional namespace used only in the proofs (sixth-power-free decomposition).
open HeckeGeneral.Analysis.ConditionalMoments
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-! ### Counting exceptional ideals -/

omit [Fintype S] in
/-- The exceptional condition on actual ideal valuations. -/
def ExceptionalSixthIdeal (C J : NonzeroIdeal K) : Prop :=
  ∀ p : HeightOneSpectrum (𝓞 K), p ∉ idealPrimeSupport K C →
    6 ∣ primeExponents J p

/-- Actual sixth-power-free ideals supported on the specified ideal C. -/
abbrev SupportedSixthBase (C : NonzeroIdeal K) :=
  {I : NonzeroIdeal K // SixthPowerFreeIdeal I ∧
    ∀ p : HeightOneSpectrum (𝓞 K), p ∉ idealPrimeSupport K C → primeExponents I p = 0}

def supportedSixthCoordinates (C : NonzeroIdeal K) (I : SupportedSixthBase K C) :
    (idealPrimeSupport K C) → Fin 6 :=
  fun p => ⟨primeExponents I.val p.val,
    (sixthPowerFreeIdeal_iff_primeExponents_lt I.val).mp I.property.1 p.val⟩

theorem supportedSixthCoordinates_injective (C : NonzeroIdeal K) :
    Function.Injective (supportedSixthCoordinates K C) := by
  intro I J h
  apply Subtype.ext
  apply (primeExponentEquiv (R := 𝓞 K)).injective
  apply Finsupp.ext
  intro p
  by_cases hp : p ∈ idealPrimeSupport K C
  · exact congrArg Fin.val (congrFun h ⟨p, hp⟩)
  · exact (I.property.2 p hp).trans (J.property.2 p hp).symm

instance finite_supportedSixthBase (C : NonzeroIdeal K) : Finite (SupportedSixthBase K C) :=
  Finite.of_injective (supportedSixthCoordinates K C) (supportedSixthCoordinates_injective K C)

/-- Each genuine supported base is determined by one of six exponents at
each prime of C. This also handles C = 1. -/
theorem card_supportedSixthBase_le (C : NonzeroIdeal K) :
    Nat.card (SupportedSixthBase K C) ≤ 6 ^ (idealPrimeSupport K C).card := by
  have h := Nat.card_le_card_of_injective
    (supportedSixthCoordinates K C) (supportedSixthCoordinates_injective K C)
  rw [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card (α := idealPrimeSupport K C),
    Fintype.card_coe] at h
  exact h

def exceptionalSupportedBase (C J : NonzeroIdeal K) (hJ : ExceptionalSixthIdeal K C J) :
    SupportedSixthBase K C :=
  ⟨sixthPowerFreePart J, sixthPowerFreePart_isSixthPowerFree J, by
    intro p hp
    rw [primeExponents_sixthPowerFreePart]
    exact Nat.mod_eq_zero_of_dvd (hJ p hp)⟩

/-- Taking a sixth root of the actual norm costs no base-norm factor,
since every nonzero integral ideal has norm at least one. -/
theorem sixthPowerAmplifier_norm_le {X : ℝ} (hX : 0 ≤ X)
    (J : NonzeroIdeal K) (hJ : idealNorm K J ≤ X) :
    idealNorm K (sixthPowerAmplifierPart J) ≤ X ^ (1 / 6 : ℝ) := by
  have hA : 0 ≤ idealNorm K (sixthPowerAmplifierPart J) := (idealNorm_pos K _).le
  have hpow : idealNorm K (sixthPowerAmplifierPart J) ^ 6 ≤ X := by
    apply le_trans _ hJ
    rw [idealNorm_sixthPowerFree_decomposition J]
    exact le_mul_of_one_le_left (pow_nonneg hA _) (one_le_idealNorm K _)
  have h := (Real.le_rpow_inv_iff_of_pos hA hX (by norm_num : (0 : ℝ) < 6)).mpr
    (by rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; exact hpow)
  simpa only [one_div] using h

def exceptionalIdealCutoff (C : NonzeroIdeal K) (X : ℝ) : Finset (NonzeroIdeal K) :=
  (dyadicIdealSupport K (X / 2)).filter (ExceptionalSixthIdeal K C)

theorem mem_exceptionalIdealCutoff {C J : NonzeroIdeal K} {X : ℝ} (hX : 0 ≤ X) :
    J ∈ exceptionalIdealCutoff K C X ↔ idealNorm K J ≤ X ∧ ExceptionalSixthIdeal K C J := by
  rw [exceptionalIdealCutoff, Finset.mem_filter,
    mem_dyadicIdealSupport_iff K (div_nonneg hX (by norm_num))]
  rw [show 2 * (X / 2) = X by ring]

/-- The finite count uses the actual arithmetic decomposition, not a
postulated parametrization or a surjective list with unproved coverage. -/
theorem exceptionalIdealCutoff_card_le (C : NonzeroIdeal K) {X : ℝ} (hX : 0 ≤ X) :
    (exceptionalIdealCutoff K C X).card ≤
      6 ^ (idealPrimeSupport K C).card *
        (dyadicIdealSupport K (X ^ (1 / 6 : ℝ) / 2)).card := by
  let f : {J : NonzeroIdeal K // J ∈ exceptionalIdealCutoff K C X} →
      SupportedSixthBase K C ×
        {A : NonzeroIdeal K // A ∈ dyadicIdealSupport K (X ^ (1 / 6 : ℝ) / 2)} :=
    fun J => (exceptionalSupportedBase K C J.val
      ((mem_exceptionalIdealCutoff K hX).mp J.property).2,
      ⟨sixthPowerAmplifierPart J.val, by
        apply (mem_dyadicIdealSupport_iff K (by positivity) _).mpr
        rw [show 2 * (X ^ (1 / 6 : ℝ) / 2) = X ^ (1 / 6 : ℝ) by ring]
        exact sixthPowerAmplifier_norm_le K hX J.val
          ((mem_exceptionalIdealCutoff K hX).mp J.property).1⟩)
  have hf : Function.Injective f := by
    intro I J h
    have hb : sixthPowerFreePart I.val = sixthPowerFreePart J.val :=
      congrArg (fun x => x.1.val) h
    have ha : sixthPowerAmplifierPart I.val = sixthPowerAmplifierPart J.val :=
      congrArg (fun x => x.2.val) h
    apply Subtype.ext
    calc
      I.val = sixthPowerFreePart I.val * sixthPowerAmplifierPart I.val ^ 6 :=
        (sixthPowerFreePart_mul_amplifier_sixth I.val).symm
      _ = sixthPowerFreePart J.val * sixthPowerAmplifierPart J.val ^ 6 := by rw [hb, ha]
      _ = J.val := sixthPowerFreePart_mul_amplifier_sixth J.val
  have hcard := Nat.card_le_card_of_injective f hf
  have hbase := card_supportedSixthBase_le K C
  have hfirst : (exceptionalIdealCutoff K C X).card ≤
      Nat.card (SupportedSixthBase K C) *
        (dyadicIdealSupport K (X ^ (1 / 6 : ℝ) / 2)).card := by
    simpa only [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_coe] using hcard
  exact hfirst.trans (Nat.mul_le_mul_right _ hbase)

/-- A single K-dependent constant works for every C and every X >= 1. -/
theorem exceptionalIdealCutoff_sixth_root_count :
    ∃ A : ℝ, 0 < A ∧ ∀ (C : NonzeroIdeal K) (X : ℝ), 1 ≤ X →
      ((exceptionalIdealCutoff K C X).card : ℝ) ≤
        A * (6 : ℝ) ^ (idealPrimeSupport K C).card * X ^ (1 / 6 : ℝ) := by
  obtain ⟨A, hA, hcount⟩ := dyadicIdealSupport_linear_count K
  refine ⟨A, hA, fun C X hX => ?_⟩
  have hr : 1 ≤ X ^ (1 / 6 : ℝ) := Real.one_le_rpow hX (by norm_num)
  have hc : ((exceptionalIdealCutoff K C X).card : ℝ) ≤
      (6 : ℝ) ^ (idealPrimeSupport K C).card *
        ((dyadicIdealSupport K (X ^ (1 / 6 : ℝ) / 2)).card : ℝ) := by
    exact_mod_cast exceptionalIdealCutoff_card_le K C (zero_le_one.trans hX)
  apply hc.trans
  calc
    _ ≤ (6 : ℝ) ^ (idealPrimeSupport K C).card * (A * X ^ (1 / 6 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hcount _ hr) (by positivity)
    _ = _ := by ring

/-- Reuse the verified two-to-the-support-cardinality bound at epsilon/3.
Cubing dominates six-to-the-cardinality and gives the exact epsilon loss. -/
theorem exists_six_pow_support_le_norm_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ C : NonzeroIdeal K,
      (6 : ℝ) ^ (idealPrimeSupport K C).card ≤ A * idealNorm K C ^ ε := by
  obtain ⟨A, hA, hbound⟩ := exists_two_pow_card_le_idealNorm_rpow K
    (div_pos hε (by norm_num : (0 : ℝ) < 3))
  refine ⟨A ^ 3, pow_pos hA _, fun C => ?_⟩
  let T := idealPrimeSupport K C
  have htwo : (2 : ℝ) ^ T.card ≤ A * idealNorm K C ^ (ε / 3) :=
    (hbound T).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (idealNorm_pos K _).le
        (idealNorm_squarefreeIdeal_le_of_primeSupport_subset K C T (fun _ h => h))
        (by positivity)) hA.le)
  calc
    (6 : ℝ) ^ T.card ≤ (8 : ℝ) ^ T.card := pow_le_pow_left₀ (by norm_num) (by norm_num) T.card
    _ = ((2 : ℝ) ^ T.card) ^ 3 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    _ ≤ (A * idealNorm K C ^ (ε / 3)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) htwo 3
    _ = A ^ 3 * idealNorm K C ^ ε := by
      have hpow : (idealNorm K C ^ (ε / 3)) ^ 3 = idealNorm K C ^ ε := by
        rw [← Real.rpow_natCast (idealNorm K C ^ (ε / 3)) 3,
          ← Real.rpow_mul (idealNorm_pos K C).le]
        congr 1
        ring
      rw [mul_pow, hpow]

/-- The exceptional ideal count with the uniform norm loss, for `X >= 1`. -/
theorem exceptionalIdealCutoff_small_power_count_ge_one {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ (C : NonzeroIdeal K) (X : ℝ), 1 ≤ X →
      ((exceptionalIdealCutoff K C X).card : ℝ) ≤
        A * idealNorm K C ^ ε * X ^ (1 / 6 : ℝ) := by
  obtain ⟨B, hB, hcount⟩ := exceptionalIdealCutoff_sixth_root_count K
  obtain ⟨D, hD, hsmall⟩ := exists_six_pow_support_le_norm_rpow K hε
  refine ⟨B * D, mul_pos hB hD, fun C X hX => (hcount C X hX).trans ?_⟩
  calc
    _ ≤ B * (D * idealNorm K C ^ ε) * X ^ (1 / 6 : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hsmall C) hB.le)
        (Real.rpow_nonneg (zero_le_one.trans hX) _)
    _ = _ := by ring

/-- The same bound for every positive `X`: below one the cutoff is empty. -/
theorem exceptionalIdealCutoff_small_power_count {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ (C : NonzeroIdeal K) (X : ℝ), 0 < X →
      ((exceptionalIdealCutoff K C X).card : ℝ) ≤
        A * idealNorm K C ^ ε * X ^ (1 / 6 : ℝ) := by
  obtain ⟨A, hA, hcount⟩ := exceptionalIdealCutoff_small_power_count_ge_one K hε
  refine ⟨A, hA, fun C X hX => ?_⟩
  by_cases h1 : 1 ≤ X
  · exact hcount C X h1
  · have hempty : exceptionalIdealCutoff K C X = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro J hJ
      have := ((mem_exceptionalIdealCutoff K hX.le).mp hJ).1
      exact h1 ((one_le_idealNorm K J).trans this)
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    have hn := idealNorm_pos K C
    positivity

/-! ### From orbits to ideals and unit sectors -/

/-- The ideal of an orbit: the contraction of its principal modulus. -/
abbrev orbitIdeal (q : HeckeSkeleton.Gram.Orbit K S) : NonzeroIdeal K :=
  actualSIntegerOrbitIdeal K S q

theorem orbitIdeal_val_out (q : HeckeSkeleton.Gram.Orbit K S) :
    (orbitIdeal K S q).val = sIntegerModulusContraction K S q.out.val :=
  (congrArg (actualSIntegerOrbitContraction K S) (Quotient.out_eq q)).symm.trans
    (actualSIntegerOrbitContraction_mk K S q.out)

theorem orbitIdeal_norm (q : HeckeSkeleton.Gram.Orbit K S) :
    (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val = idealNorm K (orbitIdeal K S q) :=
  actualSIntegerOrbitNorm_eq_absNorm_contraction K S q

/-- A nonzero S-integer whose contraction is `J`, chosen when one exists. -/
def refElement (J : NonzeroIdeal K) : NonzeroRingElements (S.integer K) :=
  haveI : Nonempty (NonzeroRingElements (S.integer K)) := ⟨⟨1, one_ne_zero⟩⟩
  Classical.epsilon fun a : NonzeroRingElements (S.integer K) =>
    sIntegerModulusContraction K S a.val = J.val

omit [Fintype S] in
theorem refElement_spec (J : NonzeroIdeal K) (a : NonzeroRingElements (S.integer K))
    (ha : sIntegerModulusContraction K S a.val = J.val) :
    sIntegerModulusContraction K S (refElement K S J).val = J.val := by
  have : Nonempty (NonzeroRingElements (S.integer K)) := ⟨⟨1, one_ne_zero⟩⟩
  exact Classical.epsilon_spec (p := fun a : NonzeroRingElements (S.integer K) =>
    sIntegerModulusContraction K S a.val = J.val) ⟨a, ha⟩

/-- Equal contractions give associate S-integers, hence a global S-unit relating them. -/
theorem exists_sUnit_mul_eq (a b : NonzeroRingElements (S.integer K))
    (h : sIntegerModulusContraction K S a.val = sIntegerModulusContraction K S b.val) :
    ∃ s : S.unit K, ((s : Kˣ) : K) * (b.val : K) = (a.val : K) := by
  have hspan : Ideal.span ({a.val} : Set (S.integer K)) =
      Ideal.span ({b.val} : Set (S.integer K)) := by
    rw [← map_sIntegerModulusContraction K S a.val,
      ← map_sIntegerModulusContraction K S b.val, h]
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan.symm
  refine ⟨(S.unitEquivUnitsInteger K).symm u, ?_⟩
  have h1 : ((((S.unitEquivUnitsInteger K) ((S.unitEquivUnitsInteger K).symm u) :
      (S.integer K)ˣ) : S.integer K) : K) =
      ((((S.unitEquivUnitsInteger K).symm u : S.unit K) : Kˣ) : K) := rfl
  rw [MulEquiv.apply_symm_apply] at h1
  rw [← h1]
  have h2 := congrArg (fun z : S.integer K => (z : K)) hu
  rw [mul_comm]
  exact h2

theorem orbit_contraction_eq (q : HeckeSkeleton.Gram.Orbit K S) :
    sIntegerModulusContraction K S q.out.val =
      sIntegerModulusContraction K S (refElement K S (orbitIdeal K S q)).val := by
  have h1 := orbitIdeal_val_out K S q
  rw [refElement_spec K S (orbitIdeal K S q) q.out h1.symm]
  exact h1.symm

/-- The S-unit sector of an orbit relative to the reference element of its ideal. -/
def orbitSector (q : HeckeSkeleton.Gram.Orbit K S) : S.unit K :=
  (exists_sUnit_mul_eq K S q.out (refElement K S (orbitIdeal K S q))
    (orbit_contraction_eq K S q)).choose

theorem orbitSector_spec (q : HeckeSkeleton.Gram.Orbit K S) :
    ((orbitSector K S q : Kˣ) : K) * ((refElement K S (orbitIdeal K S q)).val : K) =
      (q.out.val : K) :=
  (exists_sUnit_mul_eq K S q.out (refElement K S (orbitIdeal K S q))
    (orbit_contraction_eq K S q)).choose_spec

/-- An orbit is determined by its ideal and its sixth-power unit sector. -/
theorem orbit_eq_of_ideal_sector_eq (q q' : HeckeSkeleton.Gram.Orbit K S)
    (hJ : orbitIdeal K S q = orbitIdeal K S q')
    (hs : (QuotientGroup.mk (orbitSector K S q) : SixthUnitClasses K S) =
      QuotientGroup.mk (orbitSector K S q')) : q = q' := by
  have hmem : orbitSector K S q / orbitSector K S q' ∈ sixthPowerUnits K S :=
    QuotientGroup.eq_iff_div_mem.mp hs
  have h1 := orbitSector_spec K S q
  have h2 := orbitSector_spec K S q'
  rw [hJ] at h1
  have hrel : MulAction.orbitRel (sIntegerUnitSubgroup K S (sixthPowerUnits K S))
      (NonzeroRingElements (S.integer K)) q.out q'.out := by
    apply (sIntegerOrbitRelation_iff K S (sixthPowerUnits K S) _ _).mpr
    refine ⟨⟨orbitSector K S q / orbitSector K S q', hmem⟩, ?_⟩
    have hne : (((orbitSector K S q' : S.unit K) : Kˣ) : K) ≠ 0 := Units.ne_zero _
    change ((((orbitSector K S q / orbitSector K S q' : S.unit K)) : Kˣ) : K) *
      (q'.out.val : K) = (q.out.val : K)
    rw [← h1, ← h2]
    simp only [Subgroup.coe_div, Units.val_div_eq_div_val]
    field_simp
  exact (Quotient.out_eq q).symm.trans ((Quotient.sound hrel).trans (Quotient.out_eq q'))

/-- The exceptional orbits of norm at most `X` embed into exceptional ideals times sectors. -/
def exceptionalCutoffEmbedding (C : NonzeroIdeal K) {X : ℝ} (hX : 0 ≤ X) :
    HeckeSkeleton.Gram.exceptionalCutoff K S C X ↪
      ({J : NonzeroIdeal K // J ∈ exceptionalIdealCutoff K C X} × SixthUnitClasses K S) where
  toFun q :=
    (⟨orbitIdeal K S q.val.val, (mem_exceptionalIdealCutoff K hX).mpr
      ⟨by
        rw [← orbitIdeal_norm]
        exact q.val.property, q.property⟩⟩,
      QuotientGroup.mk (orbitSector K S q.val.val))
  inj' q r h := by
    have hJ : orbitIdeal K S q.val.val = orbitIdeal K S r.val.val :=
      congrArg (fun x => x.1.val) h
    have hs := congrArg Prod.snd h
    exact Subtype.ext (Subtype.ext (orbit_eq_of_ideal_sector_eq K S _ _ hJ hs))

/-- Exceptional frequency count. -/
theorem exceptional_frequency_count {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : NonzeroIdeal K) (X : ℝ), 0 < X →
      Finite (HeckeSkeleton.Gram.exceptionalCutoff K S A X) ∧
      (Nat.card (HeckeSkeleton.Gram.exceptionalCutoff K S A X) : ℝ) ≤
        C * idealNorm K A ^ ε * X ^ (1 / 6 : ℝ) := by
  obtain ⟨B, hB, hcount⟩ := exceptionalIdealCutoff_small_power_count K hε
  have hM : (0 : ℝ) < Nat.card (SixthUnitClasses K S) := by
    exact_mod_cast Nat.card_pos (α := SixthUnitClasses K S)
  refine ⟨(Nat.card (SixthUnitClasses K S) : ℝ) * B, mul_pos hM hB, fun A X hX => ?_⟩
  let e := exceptionalCutoffEmbedding K S A hX.le
  refine ⟨Finite.of_injective e e.injective, ?_⟩
  have hc : Nat.card (HeckeSkeleton.Gram.exceptionalCutoff K S A X) ≤
      (exceptionalIdealCutoff K A X).card * Nat.card (SixthUnitClasses K S) := by
    have h := Nat.card_le_card_of_injective e e.injective
    simpa only [Nat.card_prod, Nat.card_eq_finsetCard] using h
  have hc' : (Nat.card (HeckeSkeleton.Gram.exceptionalCutoff K S A X) : ℝ) ≤
      ((exceptionalIdealCutoff K A X).card : ℝ) * Nat.card (SixthUnitClasses K S) := by
    exact_mod_cast hc
  calc
    _ ≤ ((exceptionalIdealCutoff K A X).card : ℝ) * Nat.card (SixthUnitClasses K S) := hc'
    _ ≤ (B * idealNorm K A ^ ε * X ^ (1 / 6 : ℝ)) * Nat.card (SixthUnitClasses K S) :=
      mul_le_mul_of_nonneg_right (hcount A X hX) hM.le
    _ = _ := by ring

end HeckeSkeleton.GramExceptionalCount
