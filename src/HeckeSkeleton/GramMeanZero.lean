import HeckeSkeleton.GramDefinitions

/-!
# Mean zero of the residual sextic character (obligation GR-05)

Let `I` be an exterior ideal having a prime divisor `p` whose multiplicity is
not divisible by six.  The zero-extended ideal residue character
`columnCharacter` is multiplicative on the finite ring `R/I'` (`R = O_{K,S}`,
`I' = I R`).  We use the Chinese remainder theorem in `O_K` to build a class
`y` which is a unit modulo `I`, which reduces to a prescribed unit `g` modulo
`p` and to `1` modulo every other prime divisor of `I`.  Choosing `g` with
`χ_p(g)^e ≠ 1` (the sextic residue character has exact order six), the
character takes a value different from `1` on this unit, and the
substitution `x ↦ y x` (a bijection of `R/I'`) forces the full sum to vanish.
-/
set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.GramMeanZero
open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Orthogonality: a multiplicative function on a finite commutative ring which
differs from `1` at some unit sums to zero. -/
theorem sum_eq_zero_of_unit_ne_one {A : Type*} [CommRing A] [Fintype A]
    (f : A → ℂ) (hf : ∀ x y, f (x * y) = f x * f y) (u : Aˣ) (hu : f u ≠ 1) :
    ∑ x, f x = 0 := by
  have h : ∑ x, f x = f u * ∑ x, f x := by
    calc ∑ x, f x = ∑ x, f ((u : A) * x) :=
          (Equiv.sum_comp (Units.mulLeft u) f).symm
      _ = ∑ x, f u * f x := by simp only [hf]
      _ = f u * ∑ x, f x := (Finset.mul_sum _ _ _).symm
  have h2 : (1 - f u) * ∑ x, f x = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3).symm hu
  · exact h3

section Quotient

variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (I : Ideal (𝓞 K)) (hI : I ≠ 0)
variable (hS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → p ∉ S)
variable (h6 : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → (6 : 𝓞 K) ∉ p.asIdeal)

/-- The zero-extended ideal residue function is multiplicative on the quotient. -/
theorem quotientFunction_mul
    (x y : S.integer K ⧸ I.map (algebraMap (𝓞 K) (S.integer K))) :
    sIntegerSexticIdealQuotientFunction K S ζ hζ σ I hI hS h6 (x * y) =
      sIntegerSexticIdealQuotientFunction K S ζ hζ σ I hI hS h6 x *
        sIntegerSexticIdealQuotientFunction K S ζ hζ σ I hI hS h6 y := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, sIntegerSexticIdealQuotientFunction_mk,
    sIntegerSexticIdealQuotientFunction_mk, sIntegerSexticIdealQuotientFunction_mk,
    sIntegerSexticIdealEvaluation_mul]

omit [Fintype S] in
include hI in
/-- Chinese remainder theorem in `𝓞 K`: a class prescribed modulo one prime
divisor `p` of `I` and equal to `1` modulo all the other prime divisors, which
is coprime to `I`. -/
theorem exists_crt_element (p : HeightOneSpectrum (𝓞 K)) (hp : p.asIdeal ∣ I)
    (g : 𝓞 K ⧸ p.asIdeal) (hg : g ≠ 0) :
    ∃ y : 𝓞 K, Ideal.Quotient.mk p.asIdeal y = g ∧
      (∀ q : HeightOneSpectrum (𝓞 K), q.asIdeal ∣ I → q ≠ p →
        Ideal.Quotient.mk q.asIdeal y = 1) ∧
      I ⊔ Ideal.span ({y} : Set (𝓞 K)) = ⊤ := by
  obtain ⟨g', rfl⟩ := Ideal.Quotient.mk_surjective g
  let s : Finset (HeightOneSpectrum (𝓞 K)) := (idealPrimeDivisors_finite K I hI).toFinset
  have hmem : ∀ q : HeightOneSpectrum (𝓞 K), q ∈ s ↔ q.asIdeal ∣ I := fun q => by
    simp [s, idealPrimeDivisors]
  let x : s → 𝓞 K := fun q => if q.val = p then g' else 1
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := s)
    (fun q : HeightOneSpectrum (𝓞 K) => q.asIdeal) (fun _ => 1)
    (fun q _ => q.prime)
    (fun q _ q' _ hne h => hne (HeightOneSpectrum.ext h)) x
  have hpy : y - g' ∈ p.asIdeal := by
    have := hy p ((hmem p).mpr hp)
    simpa [x] using this
  have hqy : ∀ q : HeightOneSpectrum (𝓞 K), q.asIdeal ∣ I → q ≠ p →
      y - 1 ∈ q.asIdeal := by
    intro q hq hqp
    have := hy q ((hmem q).mpr hq)
    simpa [x, hqp] using this
  refine ⟨y, Ideal.Quotient.eq.mpr hpy, ?_, ?_⟩
  · intro q hq hqp
    rw [← map_one (Ideal.Quotient.mk q.asIdeal)]
    exact Ideal.Quotient.eq.mpr (hqy q hq hqp)
  · by_contra hne
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ hne
    have hI_le : I ≤ M := le_trans le_sup_left hIM
    have hyM : y ∈ M := hIM (Ideal.mem_sup_right (Ideal.mem_span_singleton_self y))
    have hMbot : M ≠ ⊥ := fun h => hI (le_bot_iff.mp (h ▸ hI_le))
    let q : HeightOneSpectrum (𝓞 K) := ⟨M, hM.isPrime, hMbot⟩
    have hq : q.asIdeal ∣ I := Ideal.dvd_iff_le.mpr hI_le
    by_cases hqp : q = p
    · apply hg
      have hyp : y ∈ p.asIdeal := by
        have : y ∈ q.asIdeal := hyM
        rwa [hqp] at this
      have hg'p : g' ∈ p.asIdeal := by
        have := p.asIdeal.sub_mem hyp hpy
        simpa using this
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hg'p
    · have h1 := hqy q hq hqp
      have h1M : (1 : 𝓞 K) ∈ M := by
        have := M.sub_mem hyM h1
        simpa using this
      exact hM.ne_top ((Ideal.eq_top_iff_one _).mpr h1M)

include hI in
/-- The value of the ideal residue function on the class of `y` determined by
the Chinese remainder construction: only the factor of `p` survives. -/
theorem quotientFunction_mk_algebraMap
    (p : HeightOneSpectrum (𝓞 K)) (hp : p.asIdeal ∣ I) (y : 𝓞 K)
    (hyq : ∀ q : HeightOneSpectrum (𝓞 K), q.asIdeal ∣ I → q ≠ p →
        Ideal.Quotient.mk q.asIdeal y = 1) :
    sIntegerSexticIdealQuotientFunction K S ζ hζ σ I hI hS h6
      (Ideal.Quotient.mk (I.map (algebraMap (𝓞 K) (S.integer K)))
        (algebraMap (𝓞 K) (S.integer K) y)) =
    sexticResidueCharacter K ζ hζ σ p (h6 p hp) (Ideal.Quotient.mk p.asIdeal y) ^
      idealPrimeMultiplicity K p I := by
  let _ : Fintype (idealPrimeDivisors K I) :=
    (idealPrimeDivisors_finite K I hI).fintype
  rw [sIntegerSexticIdealQuotientFunction_mk]
  unfold sIntegerSexticIdealEvaluation
  rw [Finset.prod_eq_single (⟨p, hp⟩ : idealPrimeDivisors K I)]
  · simp only [sIntegerSexticEvaluation_algebraMap, sexticResidueEvaluation]
  · intro b _ hb
    have hbp : b.val ≠ p := fun h => hb (Subtype.ext h)
    simp only [sIntegerSexticEvaluation_algebraMap, sexticResidueEvaluation,
      hyq b.val b.property hbp, map_one, one_pow]
  · intro h
    exact absurd (Finset.mem_univ _) h

include hS in
/-- A class represented by an integer coprime to `I` is a unit of the actual
S-integer residue ring. -/
theorem isUnit_mk_algebraMap (y : 𝓞 K) (hcop : I ⊔ Ideal.span ({y} : Set (𝓞 K)) = ⊤) :
    IsUnit (Ideal.Quotient.mk (I.map (algebraMap (𝓞 K) (S.integer K)))
      (algebraMap (𝓞 K) (S.integer K) y)) := by
  have h1 : IsUnit (Ideal.Quotient.mk I y) := isUnit_quotient_of_sup_span_eq_top y I hcop
  have h2 := h1.map (sIntegerResidueEquiv K S I (sexticIdeal_coprime_S K S I hS))
  rwa [sIntegerResidueEquiv_mk] at h2

/-- Mean zero of the zero-extended ideal residue function over the residue ring
when some prime divisor has multiplicity prime to six. -/
theorem sum_quotientFunction_eq_zero
    (hbad : ∃ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I ∧
      ¬ 6 ∣ idealPrimeMultiplicity K p I)
    [Fintype (S.integer K ⧸ I.map (algebraMap (𝓞 K) (S.integer K)))] :
    ∑ x, sIntegerSexticIdealQuotientFunction K S ζ hζ σ I hI hS h6 x = 0 := by
  obtain ⟨p, hp, hnot⟩ := hbad
  have : p.asIdeal.IsMaximal := p.isMaximal
  let _ : Field (𝓞 K ⧸ p.asIdeal) := Ideal.Quotient.field _
  obtain ⟨g, hg⟩ : ∃ g : (𝓞 K ⧸ p.asIdeal)ˣ,
      sexticResidueCharacter K ζ hζ σ p (h6 p hp) (g : 𝓞 K ⧸ p.asIdeal) ^
        idealPrimeMultiplicity K p I ≠ 1 := by
    by_contra h
    apply hnot
    have hpow : sexticResidueCharacter K ζ hζ σ p (h6 p hp) ^
        idealPrimeMultiplicity K p I = 1 := by
      apply MulChar.ext
      intro g
      rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
      by_contra hg
      exact h ⟨g, hg⟩
    have := orderOf_dvd_of_pow_eq_one hpow
    rwa [sexticResidueCharacter_order] at this
  obtain ⟨y, hyp, hyq, hycop⟩ := exists_crt_element K I hI p hp
    (g : 𝓞 K ⧸ p.asIdeal) g.ne_zero
  obtain ⟨u, hu⟩ := isUnit_mk_algebraMap K S I hS y hycop
  apply sum_eq_zero_of_unit_ne_one _ (quotientFunction_mul K S ζ hζ σ I hI hS h6) u
  rw [hu, quotientFunction_mk_algebraMap K S ζ hζ σ I hI hS h6 p hp y hyq, hyp]
  exact hg

end Quotient

/-- GR-05: the residual sextic character has mean zero over the exterior
residue ring whenever some prime divisor of `I` has multiplicity not divisible
by six. -/
theorem residual_character_mean_zero (P : ProbeData K S) (I : ExteriorIdeal K S)
    (hI : ∃ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val.val ∧
      ¬ 6 ∣ idealPrimeMultiplicity K p I.val.val) :
    (∑' x : ThetaQuotient K S I, HeckeSkeleton.Gram.columnCharacter K S P I x) = 0 := by
  have : Finite (ThetaQuotient K S I) :=
    finite_sIntegerSexticIdealQuotient K S I.val.val
      (nonZeroDivisors.coe_ne_zero I.val) I.property
  let _ : Fintype (ThetaQuotient K S I) := Fintype.ofFinite _
  rw [tsum_fintype]
  exact sum_quotientFunction_eq_zero K S P.arithmetic.root6 P.arithmetic.primitive6
    P.arithmetic.embedding I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => P.arithmetic.away_six p (I.property p hp)) hI

end HeckeSkeleton.GramMeanZero
