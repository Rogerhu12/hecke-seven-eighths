import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualFrequencyPartition

/-!
# Complete correlations with arbitrary actual generators

Changing the two generators induces equivalences of all three complete
quotients.  The opposite generator units rescale the two summation
variables and contribute only character values of norm one.  The
frequency itself is unchanged.  This transports the actual local-table
bound and frequency extraction to independently chosen generators.
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckePort.Moments HeckePort.Moments.CommonSupport HeckePort.Moments.ProductCRT

section Ring

variable {R : Type*} [CommRing R] [IsDomain R]

theorem full_correlation_norm_generator_change
    (a b a' b' : R)
    (ha : Ideal.span ({a} : Set R) = Ideal.span {a'})
    (hb : Ideal.span ({b} : Set R) = Ideal.span {b'})
    [Fintype (CommonSupport.Residue a)] [Fintype (CommonSupport.Residue b)]
    [Fintype (CommonSupport.Residue a')] [Fintype (CommonSupport.Residue b')]
    (χ : MulChar (CommonSupport.Residue a) ℂ)
    (ψ : MulChar (CommonSupport.Residue b) ℂ)
    (χ' : MulChar (CommonSupport.Residue a') ℂ)
    (ψ' : MulChar (CommonSupport.Residue b') ℂ)
    (hχ : ∀ x : R, χ' (Ideal.Quotient.mk _ x) = χ (Ideal.Quotient.mk _ x))
    (hψ : ∀ x : R, ψ' (Ideal.Quotient.mk _ x) = ψ (Ideal.Quotient.mk _ x))
    (h : R) :
    ‖fullModulusCorrelation a' b' χ' ψ' h‖ =
      ‖fullModulusCorrelation a b χ ψ h‖ := by
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp ha
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hb
  have hm : Ideal.span ({a * b} : Set R) = Ideal.span {a' * b'} := by
    rw [← Ideal.span_singleton_mul_span_singleton, ha, hb,
      Ideal.span_singleton_mul_span_singleton]
  let eA := Ideal.quotEquivOfEq ha
  let eB := Ideal.quotEquivOfEq hb
  let eM := Ideal.quotEquivOfEq hm
  let vA : (CommonSupport.Residue a)ˣ :=
    Units.map (Ideal.Quotient.mk (Ideal.span {a})).toMonoidHom v
  let uB : (CommonSupport.Residue b)ˣ :=
    Units.map (Ideal.Quotient.mk (Ideal.span {b})).toMonoidHom u
  have hleft (x : CommonSupport.Residue a) :
      eM (scaledResidue a b (a * b) rfl ((vA : CommonSupport.Residue a) * x)) =
        scaledResidue a' b' (a' * b') rfl (eA x) := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk (Ideal.span {a' * b'}) (b * ((v : R) * x)) =
      Ideal.Quotient.mk (Ideal.span {a' * b'}) (b' * x)
    apply congrArg (Ideal.Quotient.mk (Ideal.span {a' * b'}))
    rw [← hv]
    ring
  have hright (y : CommonSupport.Residue b) :
      eM (scaledResidue b a (a * b) (mul_comm a b)
        ((uB : CommonSupport.Residue b) * y)) =
        scaledResidue b' a' (a' * b') (mul_comm a' b') (eB y) := by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk (Ideal.span {a' * b'}) (a * ((u : R) * y)) =
      Ideal.Quotient.mk (Ideal.span {a' * b'}) (a' * y)
    apply congrArg (Ideal.Quotient.mk (Ideal.span {a' * b'}))
    rw [← hu]
    ring
  have hca (x : CommonSupport.Residue a) : χ' (eA x) = χ x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simpa only [eA, Ideal.quotEquivOfEq_mk] using hχ x
  have hcb (y : CommonSupport.Residue b) : ψ' (eB y) = ψ y := by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    simpa only [eB, Ideal.quotEquivOfEq_mk] using hψ y
  have hc (x : CommonSupport.Residue a) (y : CommonSupport.Residue b) :
      scaledResidue a b (a * b) rfl ((vA : CommonSupport.Residue a) * x) -
        scaledResidue b a (a * b) (mul_comm a b) ((uB : CommonSupport.Residue b) * y) =
          Ideal.Quotient.mk _ h ↔
      scaledResidue a' b' (a' * b') rfl (eA x) -
        scaledResidue b' a' (a' * b') (mul_comm a' b') (eB y) =
          Ideal.Quotient.mk _ h := by
    constructor
    · intro hh
      have he := congrArg eM hh
      simpa only [map_sub, hleft, hright, eM, Ideal.quotEquivOfEq_mk] using he
    · intro hh
      apply eM.injective
      simpa only [map_sub, hleft, hright, eM, Ideal.quotEquivOfEq_mk] using hh
  have heq :
      fullCorrelation
        (fun x => scaledResidue a b (a * b) rfl ((vA : CommonSupport.Residue a) * x))
        (fun y => scaledResidue b a (a * b) (mul_comm a b)
          ((uB : CommonSupport.Residue b) * y)) χ ψ (Ideal.Quotient.mk _ h) =
      fullModulusCorrelation a' b' χ' ψ' h := by
    unfold fullModulusCorrelation fullCorrelation
    apply Fintype.sum_equiv eA.toEquiv
    intro x
    apply Fintype.sum_equiv eB.toEquiv
    intro y
    simp only [hc, hca, hcb, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  rw [← heq, fullCorrelation_unit_change, norm_mul, norm_mul, norm_star,
    norm_char_unit, norm_char_unit, one_mul, one_mul]
  rfl

end Ring

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

theorem generated_correlation_norm_generator_change
    (I J : A.Exterior) (a b a' b' : A.R)
    (ha : A.Generates I a) (hb : A.Generates J b)
    (ha' : A.Generates I a') (hb' : A.Generates J b') (h : A.R) :
    ‖generatedIdealCorrelation (σ := σ) I J a' b' ha' hb' h‖ =
      ‖generatedIdealCorrelation (σ := σ) I J a b ha hb h‖ := by
  letI : Finite (A.R ⧸ Ideal.span {a}) := by
    rw [ha.2]
    exact A.exteriorResidue_finite I
  letI : Finite (A.R ⧸ Ideal.span {b}) := by
    rw [hb.2]
    exact A.exteriorResidue_finite J
  letI : Finite (A.R ⧸ Ideal.span {a'}) := by
    rw [ha'.2]
    exact A.exteriorResidue_finite I
  letI : Finite (A.R ⧸ Ideal.span {b'}) := by
    rw [hb'.2]
    exact A.exteriorResidue_finite J
  letI : Fintype (A.R ⧸ Ideal.span {a}) := Fintype.ofFinite _
  letI : Fintype (A.R ⧸ Ideal.span {b}) := Fintype.ofFinite _
  letI : Fintype (A.R ⧸ Ideal.span {a'}) := Fintype.ofFinite _
  letI : Fintype (A.R ⧸ Ideal.span {b'}) := Fintype.ofFinite _
  change ‖fullModulusCorrelation a' b'
      (generatedIdealCharacter (σ := σ) I a' ha')
      (generatedIdealCharacter (σ := σ) J b' hb') h‖ =
    ‖fullModulusCorrelation a b
      (generatedIdealCharacter (σ := σ) I a ha)
      (generatedIdealCharacter (σ := σ) J b hb) h‖
  apply full_correlation_norm_generator_change a b a' b'
    (ha.2.trans ha'.2.symm) (hb.2.trans hb'.2.symm)
  · intro x
    rw [generatedIdealCharacter_mk, generatedIdealCharacter_mk]
  · intro x
    rw [generatedIdealCharacter_mk, generatedIdealCharacter_mk]

section Product
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actual_complete_correlation_gcd_radical_bound_of_generates
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (a b : A.R)
    (ha : A.Generates (primePowerProduct p m) a)
    (hb : A.Generates (primePowerProduct p n) b) (h : A.R) :
    ‖generatedIdealCorrelation (σ := σ) (primePowerProduct p m) (primePowerProduct p n)
      a b ha hb h‖ ≤
      (Ideal.absNorm (gcd (primePowerProduct p m).val (primePowerProduct p n).val) : ℝ) /
        A.exteriorNorm (unitFrequencyRadical C p m n h) := by
  rw [generated_correlation_norm_generator_change
    (primePowerProduct p m) (primePowerProduct p n)
    (primePowerProductGenerator C p m) (primePowerProductGenerator C p n) a b
    (primePowerProduct_generates C p m) (primePowerProduct_generates C p n) ha hb h]
  exact actual_complete_correlation_gcd_radical_bound C p hp m n hm h

theorem actual_product_correlation_frequency_ideal_extract_of_generates
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (a b : A.R) (ha : A.Generates (primePowerProduct p m) a)
    (hb : A.Generates (primePowerProduct p n) b)
    (Ih : A.Exterior) (h : A.R) (hh : A.Generates Ih h)
    (hne : generatedIdealCorrelation (σ := σ) (primePowerProduct p m) (primePowerProduct p n)
      a b ha hb h ≠ 0) :
    ∃ h' : A.R, ∃ Ih' : A.Exterior,
      A.Generates Ih' h' ∧
      h = primePowerProductGenerator C p (fun i => min (m i) (n i)) *
        nonunitFrequencyGenerator C p m n h * h' ∧
      Ih.val = gcd (primePowerProduct p m).val (primePowerProduct p n).val *
        (nonunitFrequencyRadical C p m n h).val * Ih'.val ∧
      A.exteriorNorm Ih =
        (Ideal.absNorm (gcd (primePowerProduct p m).val (primePowerProduct p n).val) : ℝ) *
          A.exteriorNorm (nonunitFrequencyRadical C p m n h) * A.exteriorNorm Ih' := by
  have hnorm := generated_correlation_norm_generator_change (σ := σ)
    (primePowerProduct p m) (primePowerProduct p n)
    (primePowerProductGenerator C p m) (primePowerProductGenerator C p n) a b
    (primePowerProduct_generates C p m) (primePowerProduct_generates C p n) ha hb h
  have hz : generatedIdealCorrelation (σ := σ) (primePowerProduct p m) (primePowerProduct p n)
      (primePowerProductGenerator C p m) (primePowerProductGenerator C p n)
      (primePowerProduct_generates C p m) (primePowerProduct_generates C p n) h ≠ 0 := by
    intro he
    apply hne
    apply norm_eq_zero.mp
    rw [hnorm, he, norm_zero]
  exact actual_product_correlation_frequency_ideal_extract C p hp m n Ih h hh hz

end Product
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.generated_correlation_norm_generator_change
#print axioms HeckeSkeleton.Moments.EngineStep.actual_complete_correlation_gcd_radical_bound_of_generates
#print axioms HeckeSkeleton.Moments.EngineStep.actual_product_correlation_frequency_ideal_extract_of_generates
