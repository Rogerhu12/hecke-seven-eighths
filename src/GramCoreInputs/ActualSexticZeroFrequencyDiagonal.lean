import SIntegerSexticOriginalCorrelationDefinition
import SIntegerSexticQuotientUnitCount

/-! Actual zero-frequency diagonal support. SOURCE CANDIDATE, UNCOMPILED.
The off-diagonal statement compares principal ideals, not literal generators.
The diagonal unit count includes unit moduli and the singleton zero ring. -/

noncomputable section
namespace HeckeGeneral.Arithmetic.PeriodicFourier
open scoped Classical BigOperators

variable {R : Type*} [CommRing R]

/-- In a zero-frequency fibre, invertible residue columns force the two
principal ideals to coincide. No PID or finite quotient is needed. -/
theorem zeroFrequency_principalIdeal_eq_of_units
    (u v : R) (p : commonFactorFullFibre (⊤ : Ideal R) u v 0)
    (hx : IsUnit p.val.1) (hy : IsUnit p.val.2) :
    Ideal.span ({u} : Set R) = Ideal.span ({v} : Set R) := by
  obtain ⟨⟨x, y⟩, hp⟩ := p
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hr := commonFactorFullFibre_residual_congruences (⊤ : Ideal R) u v 0 x y hp
  have hx' : IsUnit (Ideal.Quotient.mk (Ideal.span ({u} : Set R)) x) := by
    let e := Ideal.quotEquivOfEq (show
      commonFactorColumnIdeal (⊤ : Ideal R) u = Ideal.span ({u} : Set R)
      from Ideal.top_mul _)
    have hmap := hx.map e.toMonoidHom
    change IsUnit (e (Ideal.Quotient.mk (commonFactorColumnIdeal (⊤ : Ideal R) u) x)) at hmap
    simpa only [e, Ideal.quotEquivOfEq_mk] using hmap
  have hy' : IsUnit (Ideal.Quotient.mk (Ideal.span ({v} : Set R)) y) := by
    let e := Ideal.quotEquivOfEq (show
      commonFactorColumnIdeal (⊤ : Ideal R) v = Ideal.span ({v} : Set R)
      from Ideal.top_mul _)
    have hmap := hy.map e.toMonoidHom
    change IsUnit (e (Ideal.Quotient.mk (commonFactorColumnIdeal (⊤ : Ideal R) v) y)) at hmap
    simpa only [e, Ideal.quotEquivOfEq_mk] using hmap
  have hvx : Ideal.Quotient.mk (Ideal.span ({u} : Set R)) v *
      Ideal.Quotient.mk (Ideal.span ({u} : Set R)) x = 0 := by
    rw [← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa using hr.1)
  have huy : Ideal.Quotient.mk (Ideal.span ({v} : Set R)) u *
      Ideal.Quotient.mk (Ideal.span ({v} : Set R)) y = 0 := by
    rw [← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa using hr.2)
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv'.mp hx'
  obtain ⟨c, hc⟩ := isUnit_iff_exists_inv'.mp hy'
  have hv : v ∈ Ideal.span ({u} : Set R) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    calc
      Ideal.Quotient.mk _ v = Ideal.Quotient.mk _ v * (b * Ideal.Quotient.mk _ x) := by rw [hb, mul_one]
      _ = b * (Ideal.Quotient.mk _ v * Ideal.Quotient.mk _ x) := by ring
      _ = 0 := by rw [hvx, mul_zero]
  have hu : u ∈ Ideal.span ({v} : Set R) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    calc
      Ideal.Quotient.mk _ u = Ideal.Quotient.mk _ u * (c * Ideal.Quotient.mk _ y) := by rw [hc, mul_one]
      _ = c * (Ideal.Quotient.mk _ u * Ideal.Quotient.mk _ y) := by ring
      _ = 0 := by rw [huy, mul_zero]
  exact le_antisymm ((Ideal.span_singleton_le_iff_mem (Ideal.span ({v} : Set R))).mpr hu)
    ((Ideal.span_singleton_le_iff_mem (Ideal.span ({u} : Set R))).mpr hv)

/-- Cancellation identifies the genuine modulus-u-squared zero fibre
with its diagonal residue column, including when u is a unit. -/
def zeroFrequencyDiagonalFibreEquiv [IsDomain R] (u : R) (hu : u ≠ 0) :
    (R ⧸ commonFactorColumnIdeal (⊤ : Ideal R) u) ≃
      commonFactorFullFibre (⊤ : Ideal R) u u 0 where
  toFun q := ⟨(q, q), by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    change Ideal.Quotient.mk _ (u * x) - Ideal.Quotient.mk _ (u * x) =
      Ideal.Quotient.mk _ 0
    simp⟩
  invFun p := p.val.1
  left_inv _ := rfl
  right_inv p := by
    obtain ⟨⟨x, y⟩, hp⟩ := p
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hr := (commonFactorFullFibre_relation_mk_iff (⊤ : Ideal R) u u 0 x y).mp hp
    have hxy : x - y ∈ Ideal.span ({u} : Set R) := by
      apply (commonFactor_principal_cancel u (x - y) u hu).mp
      simpa only [commonFactorTotalIdeal, Ideal.top_mul,
        Ideal.span_singleton_mul_span_singleton, sub_zero, mul_sub] using hr
    apply Subtype.ext
    exact Prod.ext rfl (Ideal.Quotient.eq.mpr (by
      simpa only [commonFactorColumnIdeal, Ideal.top_mul] using hxy))

end HeckeGeneral.Arithmetic.PeriodicFourier

namespace HeckeGeneral.Characters
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.Arithmetic.PeriodicFourier
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
local notation "R" => S.integer K
local notation "N" => NonzeroRingElements R
local notation "w" => originalColumnWeight K S ζ hζ σ hS6

/-- The actual zero extension is precisely the unit-element indicator
after taking norm squared; prime exponents divisible by six retain zero. -/
theorem norm_sq_originalColumnWeight (u : N)
    (q : R ⧸ commonFactorColumnIdeal (⊤ : Ideal R) u.val) :
    ‖w u q‖ ^ 2 = if IsUnit q then (1 : ℝ) else 0 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  let I := sIntegerModulusContraction K S u.val
  have hI : I ≠ 0 := sIntegerModulusContraction_ne_bot K S u.val u.property
  have hS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → p ∉ S :=
    sIntegerSexticCommonFactor_exterior K S u
  have h6 : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → (6 : 𝓞 K) ∉ p.asIdeal :=
    fun p hp h => hS p hp (hS6 h)
  have hn := norm_sq_sIntegerSexticIdealQuotientFunction K S ζ hζ σ I hI hS h6
    (Ideal.Quotient.mk _ x)
  rw [sIntegerSexticIdealQuotientFunction_mk] at hn
  have heq : commonFactorColumnIdeal (⊤ : Ideal R) u.val =
      I.map (algebraMap (𝓞 K) R) := by
    change commonFactorColumnIdeal (⊤ : Ideal R) u.val =
      (sIntegerModulusContraction K S u.val).map (algebraMap (𝓞 K) R)
    rw [map_sIntegerModulusContraction]
    exact Ideal.top_mul _
  let e := Ideal.quotEquivOfEq heq
  have hunit : IsUnit (Ideal.Quotient.mk (commonFactorColumnIdeal (⊤ : Ideal R) u.val) x) ↔
      IsUnit (Ideal.Quotient.mk (I.map (algebraMap (𝓞 K) R)) x) := by
    constructor
    · intro h
      have hmap := h.map e.toMonoidHom
      change IsUnit (e (Ideal.Quotient.mk (commonFactorColumnIdeal (⊤ : Ideal R) u.val) x)) at hmap
      simpa only [e, Ideal.quotEquivOfEq_mk] using hmap
    · intro h
      have hmap := h.map e.symm.toMonoidHom
      change IsUnit (e.symm (Ideal.Quotient.mk (I.map (algebraMap (𝓞 K) R)) x)) at hmap
      simpa only [e, Ideal.quotEquivOfEq_symm, Ideal.quotEquivOfEq_mk] using hmap
  rw [originalColumnWeight_mk]
  simp only [hunit]
  simpa only [sIntegerSexticSymbol, I] using hn

theorem originalColumnWeight_ne_zero_iff_isUnit (u : N)
    (q : R ⧸ commonFactorColumnIdeal (⊤ : Ideal R) u.val) :
    w u q ≠ 0 ↔ IsUnit q := by
  have hn := norm_sq_originalColumnWeight K S ζ hζ σ hS6 u q
  by_cases hq : IsUnit q
  · simp only [if_pos hq] at hn
    refine ⟨fun _ => hq, fun _ hz => ?_⟩
    rw [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hn
    exact zero_ne_one hn
  · simp only [if_neg hq] at hn
    have hz : w u q = 0 := norm_eq_zero.mp (eq_zero_of_pow_eq_zero hn)
    simp [hz, hq]

/-- Each surviving genuine zero-frequency summand is on equal principal
ideals. Associate but distinct generators are deliberately retained. -/
theorem originalFull_zero_surviving_principalIdeal_eq (u v : N)
    (p : commonFactorFullFibre (⊤ : Ideal R) u.val v.val 0)
    (hp : w u p.val.1 * starRingEnd ℂ (w v p.val.2) ≠ 0) :
    Ideal.span ({u.val} : Set R) = Ideal.span ({v.val} : Set R) := by
  have hh := mul_ne_zero_iff.mp hp
  apply zeroFrequency_principalIdeal_eq_of_units u.val v.val p
  · exact (originalColumnWeight_ne_zero_iff_isUnit K S ζ hζ σ hS6 u p.val.1).mp hh.1
  · apply (originalColumnWeight_ne_zero_iff_isUnit K S ζ hζ σ hS6 v p.val.2).mp
    intro hz
    exact hh.2 (by simp [hz])

/-- Genuine full correlation vanishes off the principal-ideal diagonal,
without squarefreeness or coprimality assumptions on the moduli. -/
theorem sIntegerSexticOriginalFullCorrelation_zero_of_principalIdeal_ne (u v : N)
    (huv : Ideal.span ({u.val} : Set R) ≠ Ideal.span ({v.val} : Set R)) :
    sIntegerSexticOriginalFullCorrelation K S ζ hζ σ hS6 u v 0 = 0 := by
  unfold sIntegerSexticOriginalFullCorrelation
  apply Finset.sum_eq_zero
  intro p _
  by_contra hp
  exact huv (originalFull_zero_surviving_principalIdeal_eq K S ζ hζ σ hS6 u v p hp)

/-- The same support test in the ordinary integral-ideal labels used by
the actual allowed generators. Extension is not an additional premise. -/
theorem sIntegerSexticOriginalFullCorrelation_zero_of_contraction_ne (u v : N)
    (huv : sIntegerModulusContraction K S u.val ≠
      sIntegerModulusContraction K S v.val) :
    sIntegerSexticOriginalFullCorrelation K S ζ hζ σ hS6 u v 0 = 0 := by
  apply sIntegerSexticOriginalFullCorrelation_zero_of_principalIdeal_ne K S ζ hζ σ hS6 u v
  intro h
  apply huv
  exact congrArg (Ideal.comap (algebraMap (𝓞 K) R)) h

/-- Literal equal generators give the number of units of the actual
principal residue ring, with its actual complex conjugation. -/
theorem sIntegerSexticOriginalFullCorrelation_self_zero (u : N) :
    sIntegerSexticOriginalFullCorrelation K S ζ hζ σ hS6 u u 0 =
      (Nat.card ((R ⧸ Ideal.span ({u.val} : Set R))ˣ) : ℂ) := by
  let Q := R ⧸ commonFactorColumnIdeal (⊤ : Ideal R) u.val
  letI : Finite (R ⧸ Ideal.span ({u.val} : Set R)) :=
    finite_sIntegerPrincipalResidue K S u.val u.property
  letI : Finite Q := Finite.of_equiv _ (originalColumnEquiv K S u).symm.toEquiv
  letI : Fintype Q := Fintype.ofFinite Q
  let e := zeroFrequencyDiagonalFibreEquiv u.val u.property
  letI : Finite (commonFactorFullFibre (⊤ : Ideal R) u.val u.val 0) :=
    Finite.of_equiv Q e
  letI : Fintype (commonFactorFullFibre (⊤ : Ideal R) u.val u.val 0) := by
    classical
    unfold commonFactorFullFibre
    infer_instance
  have hreindex : sIntegerSexticOriginalFullCorrelation K S ζ hζ σ hS6 u u 0 =
      ∑ q : Q, ((‖w u q‖ ^ 2 : ℝ) : ℂ) := by
    change (∑ p : commonFactorFullFibre (⊤ : Ideal R) u.val u.val 0,
      w u p.val.1 * starRingEnd ℂ (w u p.val.2)) = _
    calc
      _ = ∑ q : Q, w u (e q).val.1 * starRingEnd ℂ (w u (e q).val.2) :=
        (e.sum_comp (fun p => w u p.val.1 * starRingEnd ℂ (w u p.val.2))).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro q _
        change w u q * starRingEnd ℂ (w u q) = _
        rw [Complex.mul_conj']
        simp
  rw [hreindex]
  simp_rw [norm_sq_originalColumnWeight K S ζ hζ σ hS6]
  let eu : Qˣ ≃ {q : Q // IsUnit q} :=
    { toFun := fun z => ⟨z.val, z.isUnit⟩
      invFun := fun z => z.property.unit
      left_inv := fun z => Units.ext (IsUnit.unit_spec z.isUnit)
      right_inv := fun z => Subtype.ext (IsUnit.unit_spec z.property) }
  have hc : Fintype.card {q : Q // IsUnit q} = Fintype.card Qˣ :=
    (Fintype.card_congr eu).symm
  have hfilter : (Finset.univ.filter (fun q : Q => IsUnit q)).card = Fintype.card Qˣ := by
    have hh := Fintype.card_of_subtype (p := fun q : Q => IsUnit q)
      (Finset.univ.filter (fun q : Q => IsUnit q))
      (by intro q; simp)
    exact hh.symm.trans hc
  simp only [apply_ite, Complex.ofReal_one, Complex.ofReal_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hfilter]
  congr 1
  exact Nat.card_eq_fintype_card.symm.trans
    (Nat.card_congr (Units.mapEquiv (originalColumnEquiv K S u).toMulEquiv).toEquiv)

end HeckeGeneral.Characters
