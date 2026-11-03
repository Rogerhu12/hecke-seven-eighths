import GeneratorMaskWitness
import HeckeAxiom.ArithmeticChoice

/-!
# The generator mask witness of an Axiom arithmetic choice (GR-12-MASK)

Axiom's allowed-generator recipe chooses a complement `B` of the unit image
`E` in the S-local sixth-power classes `V`, which include the infinite places.
For a totally complex field every complex local unit is a sixth power, so
dropping the infinite components is an injective map `π` from `V` to the
finite-place quotients used by the Gram witness. The witness takes
`C6 := π(B)`: generator classes lie in it by `allowed`, it is disjoint from the
S-unit image since `E ⊓ B = ⊥`, and S-unit localization is injective by
Axiom's local power injection (the class group of the S-integers is trivial).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeAxiom.GeneratorMask

open NumberField IsDedekindDomain
open DedekindZetaZeroFree DedekindZetaZeroFree.SArithmeticData
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Arithmetic.AllowedGeneratorConstruction
open HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in
/-- Every unit of a complex completion is a sixth power. -/
theorem complex_completion_sixth_power {w : InfinitePlace F} (hw : w.IsComplex)
    (u : w.Completionˣ) : ∃ b : w.Completionˣ, b ^ 6 = u := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (e u) (by norm_num : 0 < 6)
  have hr0 : r ≠ 0 := by
    rintro rfl
    have h0 : e (u : w.Completion) = 0 := by rw [← hr]; norm_num
    exact u.ne_zero ((map_eq_zero_iff e e.injective).mp h0)
  have he0 : e.symm r ≠ 0 := by
    intro h
    exact hr0 ((map_eq_zero_iff e.symm e.symm.injective).mp h)
  refine ⟨Units.mk0 (e.symm r) he0, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← map_pow, hr, RingEquiv.symm_apply_apply]

variable (A : SArithmeticData F)

/-- Finite-place components of a local idele, modulo local sixth powers. -/
def finitePart : A.G →* sameSLocalPowerQuotients F A.Sf 6 where
  toFun x q := QuotientGroup.mk' _ (x.2 q)
  map_one' := by funext q; simp
  map_mul' x y := by funext q; simp

theorem sixthPowers_le_ker : A.sixthPowers ≤ (finitePart A).ker := by
  rintro x ⟨y, rfl⟩
  rw [MonoidHom.mem_ker]
  funext q
  apply (QuotientGroup.eq_one_iff _).mpr
  exact ⟨y.2 q, by simp [Prod.pow_snd]⟩

/-- Dropping the infinite places on the S-local sixth-power classes. -/
def finiteProjection : A.V →* sameSLocalPowerQuotients F A.Sf 6 :=
  QuotientGroup.lift (M := sameSLocalPowerQuotients F A.Sf 6) A.sixthPowers (finitePart A)
    (sixthPowers_le_ker A)

theorem finiteProjection_mk (x : A.G) :
    finiteProjection A (QuotientGroup.mk' A.sixthPowers x) = finitePart A x := rfl

/-- For a totally complex field the projection loses nothing. -/
theorem finiteProjection_injective [IsTotallyComplex F] :
    Function.Injective (finiteProjection A) := by
  rw [injective_iff_map_eq_one]
  intro v hv
  induction v using QuotientGroup.induction_on with
  | H x =>
    have hfin : ∀ q, ∃ b, b ^ 6 = x.2 q := fun q => by
      have hq := congrFun hv q
      exact (QuotientGroup.eq_one_iff _).mp hq
    have hinf : ∀ w : InfinitePlace F, ∃ b : w.Completionˣ, b ^ 6 = x.1 w :=
      fun w => complex_completion_sixth_power (IsTotallyComplex.isComplex w) _
    choose b1 hb1 using hinf
    choose b2 hb2 using hfin
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨(b1, b2), Prod.ext (funext hb1) (funext hb2)⟩

/-- The projection of a rational class is the field-unit localization. -/
theorem finiteProjection_rationalClass (x : Fˣ) :
    finiteProjection A (ThetaReflectionData.rationalClass A x) =
      fieldLocalPowerClassHom F A.Sf 6 x := rfl

/-- The S-unit localization factors through the unit image `E`. -/
theorem sUnitPowerLocalization_mem_map (y : A.U ⧸ A.unitSixthPowers) :
    ∃ e ∈ A.E, finiteProjection A e = sUnitPowerLocalization F A.Sf 6 y := by
  induction y using QuotientGroup.induction_on with
  | H u =>
    refine ⟨ThetaReflectionData.rationalClass A (u : Fˣ),
      ⟨A.diagonal (u : Fˣ), ⟨(u : Fˣ), u.property, rfl⟩, rfl⟩, ?_⟩
    rfl

variable {S₀ : Finset (HeightOneSpectrum (𝓞 F))} {root12 : F} {σ : F →+* ℂ}
variable (X : ArithmeticChoice F S₀ root12 σ)

/-- The recipe generator, as a field unit, is the data's generator. -/
theorem generatorFieldUnit_eq (I : ExteriorIdeal F (X.places : Set (HeightOneSpectrum (𝓞 F)))) :
    generatorFieldUnit F X.places X.thetaData I =
      (recipeOfContext X.A X.C).generator ((exteriorEquiv X.A).symm I) := by
  apply Units.ext
  exact thetaArithmeticData_generator X.A (recipeOfContext X.A X.C) σ X.different I

/-- The S-unit localization is injective for the chosen data. -/
theorem localization_injective [IsTotallyComplex F] :
    Function.Injective (sUnitPowerLocalization F X.places 6) := by
  apply sUnitPowerLocalization_injective_of_detection
  intro x hx
  have hloc :
      (∀ w : InfinitePlace F, ∃ b : w.Completionˣ, b ^ 6 = (X.A.diagonal x.val).1 w) ∧
      (∀ v : {v // v ∈ X.A.Sf}, ∃ b : (v.val.adicCompletion F)ˣ,
        b ^ 6 = (X.A.diagonal x.val).2 v) :=
    ⟨fun w => complex_completion_sixth_power (IsTotallyComplex.isComplex w) _,
      fun v => hx v.val v.property⟩
  exact X.A.local_power_injection F X.C.classGroup_trivial 6 (by simp) x hloc

/-- The generator mask witness of an Axiom arithmetic choice. -/
def witness [IsTotallyComplex F]
    (hallowed : AllowedGeneratorInput F (X.places : Set (HeightOneSpectrum (𝓞 F)))
      X.thetaData) :
    GeneratorMaskWitness F where
  S := X.places
  D := X.thetaData
  C6 := (recipeOfContext X.A X.C).B.map (finiteProjection X.A)
  generator_class_mem I := by
    refine ⟨ThetaReflectionData.rationalClass X.A
      ((recipeOfContext X.A X.C).generator ((exteriorEquiv X.A).symm I)),
      (recipeOfContext X.A X.C).allowed _, ?_⟩
    rw [finiteProjection_rationalClass]
    unfold generatorSameSClass
    rw [generatorFieldUnit_eq]
  disjoint6 := by
    rw [Subgroup.disjoint_def]
    rintro z ⟨y, rfl⟩ ⟨b, hb, hbz⟩
    obtain ⟨e, he, hez⟩ := sUnitPowerLocalization_mem_map X.A y
    have heb : e = b := finiteProjection_injective X.A (hez.trans hbz.symm)
    have h1 : e = 1 := by
      have hdis := (recipeOfContext X.A X.C).complement.disjoint
      exact (Subgroup.disjoint_def.mp hdis) he (heb ▸ hb)
    rw [← hez, h1, map_one]
  localization_injective := localization_injective X
  allowed := hallowed
  totallyComplex := inferInstance

@[simp] theorem witness_S [IsTotallyComplex F]
    (hallowed : AllowedGeneratorInput F (X.places : Set (HeightOneSpectrum (𝓞 F)))
      X.thetaData) :
    (witness X hallowed).S = X.places := rfl

@[simp] theorem witness_D [IsTotallyComplex F]
    (hallowed : AllowedGeneratorInput F (X.places : Set (HeightOneSpectrum (𝓞 F)))
      X.thetaData) :
    (witness X hallowed).D = X.thetaData := rfl

end HeckeAxiom.GeneratorMask
