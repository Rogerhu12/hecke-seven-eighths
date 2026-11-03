import SIntegerSexticZeroFrequency

/-! SOURCE ONLY, UNRUN. Actual prime reductions detect units of the
S-integer quotient, including the zero ring. The diagonal mass is its
number of units, with no Euler-phi/cardinality formula assumed. -/
noncomputable section
namespace HeckeGeneral.Arithmetic
open NumberField
open scoped Classical

private theorem quotient_mk_isUnit_iff_span_sup {R : Type*} [CommRing R]
    (I : Ideal R) (a : R) :
    IsUnit (Ideal.Quotient.mk I a) ↔ Ideal.span ({a} : Set R) ⊔ I = ⊤ := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv'.mp h
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hm : b * a - 1 ∈ I := Ideal.Quotient.eq.mp (by simpa using hb)
    apply (Ideal.eq_top_iff_one _).mpr
    apply Ideal.mem_span_singleton_sup.mpr
    refine ⟨b, -(b * a - 1), I.neg_mem hm, ?_⟩
    ring
  · intro h
    have hm : (1 : R) ∈ Ideal.span ({a} : Set R) ⊔ I := by rw [h]; trivial
    obtain ⟨b, z, hz, he⟩ := Ideal.mem_span_singleton_sup.mp hm
    apply isUnit_iff_exists_inv'.mpr
    refine ⟨Ideal.Quotient.mk I b, ?_⟩
    apply Ideal.Quotient.eq.mpr
    have he' : b * a - 1 = -z := by rw [← he]; ring
    simpa only [he'] using I.neg_mem hz

theorem integral_quotient_isUnit_iff_prime_nonzero
    (K : Type*) [Field K] [NumberField K] (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (a : 𝓞 K) :
    IsUnit (Ideal.Quotient.mk I a) ↔
      ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I →
        Ideal.Quotient.mk p.asIdeal a ≠ 0 := by
  rw [quotient_mk_isUnit_iff_span_sup]
  constructor
  · intro h p hp ha
    have hle : Ideal.span ({a} : Set (𝓞 K)) ⊔ I ≤ p.asIdeal :=
      sup_le ((Ideal.span_singleton_le_iff_mem p.asIdeal).mpr (Ideal.Quotient.eq_zero_iff_mem.mp ha))
        (Ideal.dvd_iff_le.mp hp)
    exact p.isPrime.ne_top (top_le_iff.mp (h ▸ hle))
  · intro h
    by_contra htop
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ htop
    have hP0 : P ≠ ⊥ := by
      intro hz
      exact hI (le_bot_iff.mp ((le_sup_right.trans hle).trans_eq hz))
    let p : IsDedekindDomain.HeightOneSpectrum (𝓞 K) := ⟨P, hP.isPrime, hP0⟩
    exact h p (Ideal.dvd_iff_le.mpr (le_sup_right.trans hle))
      (Ideal.Quotient.eq_zero_iff_mem.mpr
        ((le_sup_left.trans hle) (Ideal.mem_span_singleton_self a)))

end HeckeGeneral.Arithmetic

namespace HeckeGeneral.Characters
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.Arithmetic.PeriodicFourier
open scoped Classical BigOperators
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (I : Ideal (𝓞 K)) (hI : I ≠ 0)
variable (hS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → p ∉ S)
variable (h6 : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → (6 : 𝓞 K) ∉ p.asIdeal)
local notation "J" => I.map (algebraMap (𝓞 K) (S.integer K))
local notation "Q" => S.integer K ⧸ J
local notation "Φ" => sIntegerSexticIdealQuotientFunction K S ζ hζ σ I hI hS h6

include hI in
theorem sIntegerSexticQuotient_isUnit_iff_prime_nonzero (q : Q) :
    IsUnit q ↔ ∀ p : HeightOneSpectrum (𝓞 K), ∀ hp : p.asIdeal ∣ I,
      sexticIdealPrimeQuotientMap K S I hS ⟨p, hp⟩ q ≠ 0 := by
  have hcop := sexticIdeal_coprime_S K S I hS
  let e := sIntegerResidueEquiv K S I hcop
  obtain ⟨q₀, rfl⟩ := e.surjective q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q₀
  have hu : IsUnit (e (Ideal.Quotient.mk I a)) ↔ IsUnit (Ideal.Quotient.mk I a) :=
    ⟨fun h => by simpa using h.map e.symm.toMonoidHom,
     fun h => h.map e.toMonoidHom⟩
  have hmap (p : HeightOneSpectrum (𝓞 K)) (hp : p.asIdeal ∣ I) :
      sexticIdealPrimeQuotientMap K S I hS ⟨p, hp⟩ (e (Ideal.Quotient.mk I a)) =
        Ideal.Quotient.mk p.asIdeal a := by
    rw [show e (Ideal.Quotient.mk I a) =
        Ideal.Quotient.mk J (algebraMap (𝓞 K) (S.integer K) a) from
          sIntegerResidueEquiv_mk K S I hcop a,
      sexticIdealPrimeQuotientMap_mk K S I hS ⟨p, hp⟩ _,
      sIntegerSexticResidueMap_algebraMap]
  rw [hu, integral_quotient_isUnit_iff_prime_nonzero K I hI a]
  constructor
  · intro h p hp
    rw [hmap p hp]
    exact h p hp
  · intro h p hp
    rw [← hmap p hp]
    exact h p hp

theorem norm_sq_sIntegerSexticIdealQuotientFunction (q : Q) :
    ‖Φ q‖ ^ 2 = if IsUnit q then (1 : ℝ) else 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [sIntegerSexticIdealQuotientFunction_mk]
  by_cases hu : IsUnit (Ideal.Quotient.mk J a)
  · rw [if_pos hu]
    have hg := (sIntegerSexticQuotient_isUnit_iff_prime_nonzero K S I hI hS _).mp hu
    have hn := norm_sIntegerSexticIdealEvaluation_eq_one K S ζ hζ σ I hI hS h6 a
      (fun p hp => by
        rw [← sexticIdealPrimeQuotientMap_mk K S I hS ⟨p, hp⟩ a]
        exact hg p hp)
    rw [hn, one_pow]
  · rw [if_neg hu]
    have hg := mt (sIntegerSexticQuotient_isUnit_iff_prime_nonzero K S I hI hS _).mpr hu
    push_neg at hg
    obtain ⟨p, hp, hz⟩ := hg
    have hz' : sIntegerSexticResidueMap K S p (hS p hp) a = 0 := by
      rw [← sexticIdealPrimeQuotientMap_mk K S I hS ⟨p, hp⟩ a]
      exact hz
    rw [sIntegerSexticIdealEvaluation_eq_zero_of_badPrime K S ζ hζ σ I hI hS h6 a p hp hz',
      norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

/-- Units as the subtype of unit elements; valid in the zero ring too. -/
private def actualUnitsEquivUnitElements (R : Type*) [CommRing R] :
    Rˣ ≃ {x : R // IsUnit x} where
  toFun u := ⟨u.val, u.isUnit⟩
  invFun x := x.property.unit
  left_inv u := Units.ext (IsUnit.unit_spec u.isUnit)
  right_inv x := Subtype.ext (IsUnit.unit_spec x.property)

theorem sIntegerSexticFiniteCorrelation_one_one_zero_eq_card_units :
    letI : Finite Q := finite_sIntegerSexticIdealQuotient K S I hI hS
    letI : Fintype Q := Fintype.ofFinite Q
    sIntegerSexticFiniteCorrelation K S ζ hζ σ I hI hS h6 1 1 0 =
      (Fintype.card Qˣ : ℂ) := by
  letI : Finite Q := finite_sIntegerSexticIdealQuotient K S I hI hS
  letI : Fintype Q := Fintype.ofFinite Q
  rw [sIntegerSexticFiniteCorrelation_one_one_zero K S ζ hζ σ I hI hS h6]
  simp_rw [norm_sq_sIntegerSexticIdealQuotientFunction K S ζ hζ σ I hI hS h6]
  have hc : Fintype.card {q : Q // IsUnit q} = Fintype.card Qˣ :=
    (Fintype.card_congr (actualUnitsEquivUnitElements Q)).symm
  have hfilter : (Finset.univ.filter (fun q : Q => IsUnit q)).card = Fintype.card Qˣ := by
    have hh := Fintype.card_of_subtype (p := fun q : Q => IsUnit q) (Finset.univ.filter (fun q : Q => IsUnit q))
      (by intro q; simp)
    exact hh.symm.trans hc
  simp only [apply_ite, Complex.ofReal_one, Complex.ofReal_zero]
  rw [← Finset.sum_filter]
  simp [hfilter]

end HeckeGeneral.Characters
