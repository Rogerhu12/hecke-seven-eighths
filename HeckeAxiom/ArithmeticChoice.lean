import HeckeAxiom.AllowedGeneratorAdapter
import HeckeGeneral.Characters.LocalStandardAnnihilator
import DedekindZetaZeroFree.Arithmetic.Units.PrincipalizingRayCharacterContext
import DedekindZetaZeroFree.Moments.Probes.PrincipalArithmeticEnlargement
import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.TrivialCharacter

/-!
# One Axiom arithmetic choice for the skeleton's base data

For a finite initial set of primes, a primitive twelfth root of unity and a
complex embedding, the AxiomMath construction supplies an `SArithmeticData`
whose finite set contains the initial one and the support of the different,
whose `Sf`-integers have trivial class group, together with a general
arithmetic context for a principal ray character whose idele correction is
trivial. This is the input of Axiom's shared principal probe construction.

From the context's own allowed integral generators and the correction's
complement we obtain an allowed-generator recipe, hence the skeleton's
`ThetaArithmeticData` on `Sf` and its multiplicativity. No second, independent
choice of generators or of the finite set is made.
-/

noncomputable section

namespace HeckeAxiom

open NumberField IsDedekindDomain
open DedekindZetaZeroFree DedekindZetaZeroFree.SArithmeticData
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton

variable {F : Type} [Field F] [NumberField F]

section Recipe

variable (A : SArithmeticData F)

/-- `Sf`-units with trivial class in `V` are exactly sixth powers of `Sf`-units,
once the class group is trivial. -/
theorem unit_kernel_of_classGroup (hCl : Subsingleton (ClassGroup A.R)) :
    A.U ⊓ (ThetaReflectionData.rationalClass A).ker = ThetaReflectionData.rationalGamma A := by
  ext u
  constructor
  · rintro ⟨hu, hker⟩
    obtain ⟨g, hg⟩ : A.diagonal u ∈ A.sixthPowers := (QuotientGroup.eq_one_iff _).mp hker
    let ε : A.U := ⟨u, hu⟩
    have hloc :
        (∀ w, ∃ b, b ^ 6 = (A.diagonal ε.val).1 w) ∧
        (∀ v, ∃ b, b ^ 6 = (A.diagonal ε.val).2 v) :=
      ⟨fun w => ⟨g.1 w, congrArg (fun x : A.G => x.1 w) hg⟩,
        fun v => ⟨g.2 v, congrArg (fun x : A.G => x.2 v) hg⟩⟩
    obtain ⟨b, hb⟩ := A.local_power_injection F hCl 6 (by simp) ε hloc
    exact ⟨b.val, b.property, congrArg Subtype.val hb⟩
  · rintro ⟨b, hb, rfl⟩
    refine ⟨A.U.pow_mem hb 6, ?_⟩
    change QuotientGroup.mk' A.sixthPowers (A.diagonal (b ^ 6)) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨A.diagonal b, (map_pow A.diagonal b 6).symm⟩

variable {σ : F →+* ℂ} {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

/-- The allowed-generator recipe of an arithmetic context: the correction's
complement, with the context's allowed integral generators. -/
def recipeOfContext (C : A.GeneralArithmeticContext σ η hS) : ThetaBranch.AllowedRecipe A where
  B := C.correction.B
  complement := C.correction.B_complement.1
  unit_kernel := unit_kernel_of_classGroup A C.classGroup_trivial
  generator I := Classical.choose (Classical.choose_spec (C.allowed_integral I))
  generates I := ⟨Classical.choose (C.allowed_integral I),
    (Classical.choose_spec (Classical.choose_spec (C.allowed_integral I))).1,
    (Classical.choose_spec (Classical.choose_spec (C.allowed_integral I))).2.1⟩
  allowed I := (Classical.choose_spec (Classical.choose_spec (C.allowed_integral I))).2.2

@[simp] theorem recipeOfContext_B (C : A.GeneralArithmeticContext σ η hS) :
    (recipeOfContext A C).B = C.correction.B := rfl

end Recipe

omit [NumberField F] in
private theorem isPrincipal_cast {m n : Ideal (𝓞 F)} [NumberField F] (h : m = n)
    (η : RayClassCharacter F n) (hη : η.IsPrincipal) :
    (h.symm ▸ η : RayClassCharacter F m).IsPrincipal := by
  subst h
  exact hη

theorem trivialRayCharacter_isPrincipal :
    (AbelianQuotient.trivialRayCharacter F).IsPrincipal := by
  intro I hI _
  simp [AbelianQuotient.trivialRayCharacter_apply, hI]

variable (F)

/-- One Axiom arithmetic choice: the data, the principal character and the
general arithmetic context that the shared principal probe construction uses. -/
structure ArithmeticChoice (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (root12 : F)
    (σ : F →+* ℂ) where
  A : SArithmeticData F
  initial : S₀ ⊆ A.Sf
  root : A.zeta12 = root12
  hS : A.ContainsTraceBadPlaces
  η : RayClassCharacter F A.modulus
  principal : η.IsPrincipal
  C : A.GeneralArithmeticContext σ η hS
  principalIdele : C.correction.η_id = 1
  containsDifferent : PoissonS.ContainsDifferent F A.Sf
  different : ∀ p : HeightOneSpectrum (𝓞 F), p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 F))) →
    HeckeGeneral.Characters.localDifferentExponent F p = 0

theorem exists_arithmeticChoice (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (root12 : F)
    (h12 : IsPrimitiveRoot root12 12) (σ : F →+* ℂ) :
    Nonempty (ArithmeticChoice F S₀ root12 σ) := by
  obtain ⟨T, hT₀, hT⟩ := exists_finiteS_localDifferentExponent_eq_zero F S₀
  obtain ⟨S, hST, hroot, hmod, -, -⟩ := exists_generalArithmeticContext F T ⊤ top_ne_bot
    root12 h12 σ (AbelianQuotient.trivialRayCharacter F)
  have hη := isPrincipal_cast hmod _ (trivialRayCharacter_isPrincipal (F := F))
  obtain ⟨A, hsub, hrootA, hmodA, hS, hdiff, C, hC⟩ :=
    PrincipalProbeConstruction.exists_enlarged_principal_context S σ _ hη
  have hTA : T ⊆ A.Sf := fun v hv => hsub (S.bad_subset (hST ▸ hv))
  exact ⟨{ A := A
           initial := hT₀.trans hTA
           root := hrootA.trans hroot
           hS := hS
           η := _
           principal := isPrincipal_cast hmodA _ hη
           C := C
           principalIdele := hC
           containsDifferent := hdiff
           different := different_outside_of_subset A hT hTA }⟩

variable {F}

namespace ArithmeticChoice

variable {S₀ : Finset (HeightOneSpectrum (𝓞 F))} {root12 : F} {σ : F →+* ℂ}
variable (X : ArithmeticChoice F S₀ root12 σ)

/-- The finite set of the choice; it is the skeleton's `excludedPlaces`. -/
abbrev places : Finset (HeightOneSpectrum (𝓞 F)) := X.A.Sf

/-- The skeleton's arithmetic data on the chosen set, from the context's recipe. -/
def thetaData : ThetaArithmeticData F (X.places : Set (HeightOneSpectrum (𝓞 F))) :=
  thetaArithmeticData X.A (recipeOfContext X.A X.C) σ X.different

theorem thetaData_root12 : X.thetaData.root12 = root12 := X.root

theorem thetaData_embedding : X.thetaData.embedding = σ := rfl

/-- The `multiplicative` field of `AllowedGeneratorInput` for the chosen data. -/
theorem thetaData_multiplicative
    (I J : ExteriorIdeal F (X.places : Set (HeightOneSpectrum (𝓞 F)))) :
    ∃ u : (X.places : Set (HeightOneSpectrum (𝓞 F))).unit F,
      X.thetaData.generator
          (HeckeGeneral.ThetaSkeleton.Global.exteriorMul F
            (X.places : Set (HeightOneSpectrum (𝓞 F))) I J) =
        ((X.places : Set (HeightOneSpectrum (𝓞 F))).unitEquivUnitsInteger F u).val ^ 6 *
          X.thetaData.generator I * X.thetaData.generator J :=
  thetaArithmeticData_multiplicative X.A (recipeOfContext X.A X.C) σ X.different
    X.C.classGroup_trivial I J

/-- Every prime of the initial set is excluded. -/
theorem initial_subset : S₀ ⊆ X.places := X.initial

end ArithmeticChoice

end HeckeAxiom
