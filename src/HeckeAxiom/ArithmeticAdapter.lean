import HeckeGeneral.Analysis.LocalThetaInput
import HeckeGeneral.Characters.LocalCanonicalFrequency
import DedekindZetaZeroFree.Arithmetic.Units.SArithmeticData
import DedekindZetaZeroFree.Theta.Whittaker.ExteriorFrequencyBranchCoordinates

/-!
# Axiom arithmetic data as the skeleton's theta arithmetic data

An AxiomMath `SArithmeticData` with an allowed generator recipe and a complex
embedding gives the actual `ThetaArithmeticData` on the same finite set `Sf`.
The generators are the recipe's own, so allowed-generator statements can later
be read off the same recipe rather than a second, independent choice.

Exterior ideals of the two libraries are identified through their underlying
ideals. The local different condition is a hypothesis: it holds as soon as `Sf`
contains a finite set containing the support of the different, which
`exists_finiteS_localDifferentExponent_eq_zero` provides for any initial set.
-/

noncomputable section

namespace HeckeAxiom

open NumberField IsDedekindDomain
open HeckeGeneral.Analysis HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton
open scoped nonZeroDivisors

variable {F : Type} [Field F] [NumberField F]
variable (A : DedekindZetaZeroFree.SArithmeticData F)

/-- A nonzero ideal is coprime to `cS` exactly when no prime of `Sf` divides it. -/
theorem sup_cS_eq_top_iff (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    I ⊔ A.cS = ⊤ ↔
      ∀ p : HeightOneSpectrum (𝓞 F), p.asIdeal ∣ I → p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 F))) := by
  constructor
  · intro h p hp hpS
    have hcS : A.cS ≤ p.asIdeal :=
      (Ideal.prod_le_inf : (∏ w ∈ A.Sf, w.asIdeal) ≤ A.Sf.inf (fun w => w.asIdeal)).trans
        (Finset.inf_le (Finset.mem_coe.mp hpS))
    have htop : (⊤ : Ideal (𝓞 F)) ≤ p.asIdeal := h ▸ sup_le (Ideal.le_of_dvd hp) hcS
    exact p.isPrime.ne_top (top_unique htop)
  · intro h
    refine (A.exterior_iff ⟨I, hI⟩).mpr fun v hv => ?_
    have hmax : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
    by_contra hne
    have hle : I ≤ v.asIdeal := by
      have := hmax.eq_of_le hne le_sup_right
      exact this ▸ le_sup_left
    exact h v (Ideal.dvd_iff_le.mpr hle) (Finset.mem_coe.mpr hv)

omit [NumberField F] in
private theorem ne_zero_of_ne_bot {I : Ideal (𝓞 F)} (h : I ≠ ⊥) : I ≠ 0 := by
  rwa [Ideal.zero_eq_bot]

omit [NumberField F] in
private theorem ne_bot_of_mem {I : Ideal (𝓞 F)} (h : I ∈ (Ideal (𝓞 F))⁰) : I ≠ ⊥ := by
  rw [← Ideal.zero_eq_bot]
  exact nonZeroDivisors.ne_zero h

/-- The exterior ideals of both libraries, with the same underlying ideal. -/
def exteriorEquiv : A.Exterior ≃ ExteriorIdeal F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) where
  toFun I := ⟨⟨I.val, mem_nonZeroDivisors_of_ne_zero (ne_zero_of_ne_bot I.property.1)⟩,
    (sup_cS_eq_top_iff A I.val I.property.1).mp I.property.2⟩
  invFun J := ⟨J.val.val, ne_bot_of_mem J.val.property,
    (sup_cS_eq_top_iff A J.val.val (ne_bot_of_mem J.val.property)).mpr J.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem exteriorEquiv_val (I : A.Exterior) : (exteriorEquiv A I).val.val = I.val := rfl

@[simp] theorem exteriorEquiv_symm_val (J : ExteriorIdeal F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))) :
    ((exteriorEquiv A).symm J).val = J.val.val := rfl

variable (allowed : DedekindZetaZeroFree.ThetaBranch.AllowedRecipe A) (σ : F →+* ℂ)

/-- The recipe generator of an exterior ideal, as an `Sf`-integer. -/
def recipeGenerator (J : ExteriorIdeal F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))) : A.R :=
  Classical.choose (allowed.generates ((exteriorEquiv A).symm J))

theorem recipeGenerator_spec (J : ExteriorIdeal F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))) :
    A.Generates ((exteriorEquiv A).symm J) (recipeGenerator A allowed J) ∧
      (allowed.generator ((exteriorEquiv A).symm J) : F) = (recipeGenerator A allowed J : F) :=
  Classical.choose_spec (allowed.generates ((exteriorEquiv A).symm J))

/-- The skeleton's arithmetic data on `Sf`, with the recipe's generators, the
recipe's twelfth root and its square, and the given complex embedding. -/
def thetaArithmeticData
    (hdiff : ∀ p : HeightOneSpectrum (𝓞 F), p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 F))) →
      localDifferentExponent F p = 0) :
    ThetaArithmeticData F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) where
  root12 := A.zeta12
  primitive12 := A.primitive_zeta12
  root6 := A.zeta12 ^ 2
  primitive6 := A.primitive_zeta12.pow (by decide) (by decide : 12 = 2 * 6)
  embedding := σ
  away_six p hp h6 := hp (Finset.mem_coe.mpr (A.above_six p h6))
  different_outside := hdiff
  generator J := recipeGenerator A allowed J
  generator_ne_zero J := (recipeGenerator_spec A allowed J).1.1
  generator_span J := (recipeGenerator_spec A allowed J).1.2

/-- The data's generators are exactly the recipe's generators. -/
theorem thetaArithmeticData_generator
    (hdiff : ∀ p : HeightOneSpectrum (𝓞 F), p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 F))) →
      localDifferentExponent F p = 0)
    (J : ExteriorIdeal F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))) :
    (((thetaArithmeticData A allowed σ hdiff).generator J : A.R) : F) =
      (allowed.generator ((exteriorEquiv A).symm J) : F) :=
  (recipeGenerator_spec A allowed J).2.symm

/-- The different condition, from any finite set inside `Sf` that already
contains the support of the different. -/
theorem different_outside_of_subset {S₀ : Finset (HeightOneSpectrum (𝓞 F))}
    (h₀ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S₀ → localDifferentExponent F v = 0)
    (hsub : S₀ ⊆ A.Sf) :
    ∀ p : HeightOneSpectrum (𝓞 F), p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 F))) →
      localDifferentExponent F p = 0 :=
  fun p hp => h₀ p fun h => hp (Finset.mem_coe.mpr (hsub h))

end HeckeAxiom
