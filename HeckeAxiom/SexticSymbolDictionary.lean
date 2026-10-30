import HeckeAxiom.ArithmeticChoice
import HeckeGeneral.Characters.SIntegerSexticIdealComparison
import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Sextic.Reciprocity

/-!
# The two sextic residue symbols agree

At a prime outside `Sf`, the skeleton's sextic evaluation of an `Sf`-integer,
normalized by `ζ₁₂²` and the embedding `σ`, is `σ` of Axiom's normalized sextic
residue. Both depend only on the residue class, and an `Sf`-integer has an
integral representative modulo the prime; for integral elements both libraries
already identify their symbol with the class field theory prime power residue
symbol, which carries no choice of root.
-/

noncomputable section

namespace HeckeAxiom

open NumberField IsDedekindDomain
open DedekindZetaZeroFree DedekindZetaZeroFree.SArithmeticData
open HeckeGeneral.Characters

variable {F : Type} [Field F] [NumberField F]
variable (A : SArithmeticData F)

/-- `ζ₁₂²` is a primitive sixth root of unity. -/
theorem zeta12_sq_primitive : IsPrimitiveRoot (A.zeta12 ^ 2) 6 :=
  A.primitive_zeta12.pow (by decide) (by decide : 12 = 2 * 6)

theorem six_not_mem (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 F)))) : (6 : 𝓞 F) ∉ v.asIdeal :=
  fun h6 => hv (Finset.mem_coe.mpr (A.above_six v h6))

/-- A prime outside `Sf` is an exterior ideal of the Axiom data. -/
def primeExterior (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 F)))) : A.Exterior :=
  ⟨v.asIdeal, v.ne_bot, (sup_cS_eq_top_iff A v.asIdeal v.ne_bot).mpr fun p hp hpS => by
    have hle : v.asIdeal ≤ p.asIdeal := Ideal.le_of_dvd hp
    have heq : v.asIdeal = p.asIdeal := v.isPrime.isMaximal v.ne_bot |>.eq_of_le
      p.isPrime.ne_top hle
    exact hv (by rwa [show v = p from HeightOneSpectrum.ext heq])⟩

@[simp] theorem primeExterior_val (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 F)))) : (primeExterior A v hv).val = v.asIdeal :=
  rfl

variable (σ : F →+* ℂ)

/-- Prime-level agreement of the two sextic symbols, for every `Sf`-integer. -/
theorem sexticEvaluation_eq_sexticResidue (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 F)))) (x : A.R) :
    sIntegerSexticEvaluation F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) v hv (A.zeta12 ^ 2)
        (zeta12_sq_primitive A) σ (six_not_mem A v hv) x =
      σ (A.sexticResidue (primeExterior A v hv) x) := by
  set P := primeExterior A v hv
  obtain ⟨r, hr⟩ : ∃ r : 𝓞 F, Ideal.Quotient.mk (A.extendIdeal P) (algebraMap (𝓞 F) A.R r) =
      Ideal.Quotient.mk (A.extendIdeal P) x := by
    obtain ⟨q, hq⟩ := (ArithGaussCRT.exteriorQuotientEquiv A P).surjective
      (Ideal.Quotient.mk _ x)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨r, (ArithGaussCRT.exteriorQuotientEquiv_mk A P r).symm.trans hq⟩
  have hA : A.sexticResidue P x = A.sexticResidue P (algebraMap (𝓞 F) A.R r) := by
    simp only [SArithmeticData.sexticResidue, SArithmeticData.residueValue, hr]
  have hH : sIntegerSexticEvaluation F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) v hv
        (A.zeta12 ^ 2) (zeta12_sq_primitive A) σ (six_not_mem A v hv) x =
      sIntegerSexticEvaluation F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) v hv
        (A.zeta12 ^ 2) (zeta12_sq_primitive A) σ (six_not_mem A v hv)
        (algebraMap (𝓞 F) A.R r) := by
    simp only [sIntegerSexticEvaluation, sIntegerSexticResidueMap, RingHom.comp_apply]
    exact congrArg _ (congrArg _ hr.symm)
  rw [hA, hH, sIntegerSexticEvaluation_algebraMap,
    sexticResidueEvaluation_eq_zeroExtended_powerResidueSymbol]
  split_ifs with hrv
  · have := Ideal.Quotient.nontrivial_iff.mpr (A.residue_extendIdeal_ne_top P v.isPrime.ne_top)
    have hnu : ¬ IsUnit (Ideal.Quotient.mk (A.extendIdeal P) (algebraMap (𝓞 F) A.R r)) := by
      rw [← ArithGaussCRT.exteriorQuotientEquiv_mk A P r,
        Ideal.Quotient.eq_zero_iff_mem.mpr (show r ∈ P.val from hrv), map_zero]
      exact not_isUnit_zero
    rw [ArithmeticContext.actual_sextic_nonunit A P _ hnu, map_zero]
  · rw [ArithmeticContext.actual_sextic_prime_integral_cft A P v rfl
      (ArithmeticContext.actual_outside_norm_coprime_six A v (fun h => hv (Finset.mem_coe.mpr h)))
      r hrv]

open AlgebraicNumberTheory.PowerResidueSymbols in
/-- Ideal-level agreement: the skeleton's sextic ideal evaluation of an
`Sf`-integer is `σ` of Axiom's sextic residue at the same exterior ideal. -/
theorem sexticIdealEvaluation_eq_sexticResidue (J : A.Exterior) (x : A.R)
    (hJ : J.val ≠ 0)
    (hS : ∀ p : HeightOneSpectrum (𝓞 F), p.asIdeal ∣ J.val →
      p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 F))))
    (h6 : ∀ p : HeightOneSpectrum (𝓞 F), p.asIdeal ∣ J.val → (6 : 𝓞 F) ∉ p.asIdeal) :
    sIntegerSexticIdealEvaluation F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) (A.zeta12 ^ 2)
        (zeta12_sq_primitive A) σ J.val hJ hS h6 x =
      σ (A.sexticResidue J x) := by
  classical
  let g : HeightOneSpectrum (𝓞 F) → F := fun v =>
    if hv : v ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 F))) then
      A.sexticResidue (primeExterior A v hv) x else 1
  have hg : ∀ (P : A.Exterior) (v : HeightOneSpectrum (𝓞 F)), P.val = v.asIdeal →
      g v = A.sexticResidue P x := by
    intro P v hP
    have hv : v ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 F))) :=
      (sup_cS_eq_top_iff A P.val P.property.1).mp P.property.2 v (hP ▸ dvd_refl _)
    simp only [g, dite_eq_left hv]
    exact congrArg (fun Q => A.sexticResidue Q x) (Subtype.ext hP.symm)
  rw [ArithmeticContext.actual_sextic_factorization_finprod A x g hg J]
  let _ := (idealPrimeDivisors_finite F J.val hJ).fintype
  have hsupp : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 F) =>
      g v ^ idealPrimeExponent v.asIdeal J.val) ⊆
        ((idealPrimeDivisors_finite F J.val hJ).toFinset : Set (HeightOneSpectrum (𝓞 F))) := by
    intro v hv
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, mem_idealPrimeDivisors]
    by_contra hnd
    apply hv
    have he : idealPrimeExponent v.asIdeal J.val = 0 := by
      unfold idealPrimeExponent
      rw [Multiset.count_eq_zero]
      exact fun hmem => hnd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hmem)
    simp [he]
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp, map_prod,
    Finset.prod_subtype ((idealPrimeDivisors_finite F J.val hJ).toFinset)
      (fun v => Set.Finite.mem_toFinset _)]
  unfold sIntegerSexticIdealEvaluation
  refine Fintype.prod_congr _ _ fun p => ?_
  have hv := hS p.val p.property
  have hmult : idealPrimeMultiplicity F p.val J.val = idealPrimeExponent p.val.asIdeal J.val :=
    Ideal.count_associates_factors_eq hJ p.val.isPrime p.val.ne_bot
  rw [map_pow, hmult, sexticEvaluation_eq_sexticResidue A σ p.val hv x]
  simp only [g, dite_eq_left hv]

/-- If a maximal ideal contains two exterior ideals, a generator of the second is
not a unit modulo the first. -/
theorem not_isUnit_of_common_maximal (I J : A.Exterior) (b : A.R) (hb : A.Generates J b)
    (M : Ideal (𝓞 F)) (hM : M.IsMaximal) (hIM : I.val ≤ M) (hJM : J.val ≤ M) :
    ¬ IsUnit (Ideal.Quotient.mk (A.extendIdeal I) b) := by
  have hM0 : M ≠ ⊥ := fun h => I.property.1 (eq_bot_iff.mpr (h ▸ hIM))
  let v : HeightOneSpectrum (𝓞 F) := ⟨M, hM.isPrime, hM0⟩
  have hv : v ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 F))) :=
    (sup_cS_eq_top_iff A I.val I.property.1).mp I.property.2 v (Ideal.dvd_iff_le.mpr hIM)
  let P := primeExterior A v hv
  have hle : A.extendIdeal I ≤ A.extendIdeal P := Ideal.map_mono hIM
  have hbP : b ∈ A.extendIdeal P :=
    (Ideal.map_mono hJM : A.extendIdeal J ≤ A.extendIdeal P)
      (show b ∈ A.extendIdeal J by rw [← hb.2]; exact Ideal.mem_span_singleton_self b)
  have := Ideal.Quotient.nontrivial_iff.mpr (A.residue_extendIdeal_ne_top P v.isPrime.ne_top)
  intro hu
  have hu' := hu.map (Ideal.Quotient.factor hle)
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hbP] at hu'
  exact not_isUnit_zero hu'

namespace ArithmeticChoice

variable {S₀ : Finset (HeightOneSpectrum (𝓞 F))} {root12 : F} {τ : F →+* ℂ}
variable (X : ArithmeticChoice F S₀ root12 τ)

/-- The skeleton's ideal symbol of the chosen data is `τ` of Axiom's residue. -/
theorem idealSymbol_eq (J : HeckeGeneral.ThetaSkeleton.ExteriorIdeal F (X.places : Set (HeightOneSpectrum (𝓞 F))))
    (a : X.A.R) :
    HeckeGeneral.ThetaSkeleton.Global.idealSymbol F (X.places : Set (HeightOneSpectrum (𝓞 F)))
        X.thetaData J a =
      τ (X.A.sexticResidue ((exteriorEquiv X.A).symm J) a) :=
  sexticIdealEvaluation_eq_sexticResidue X.A τ ((exteriorEquiv X.A).symm J) a _ _ _

/-- Sextic reciprocity for the chosen generators: the `reciprocity` field of
`AllowedGeneratorInput` (AR-ALLOWED-RECIPROCITY). Coprime pairs use the
context's reciprocity for allowed generators; otherwise both symbols vanish. -/
theorem idealSymbol_reciprocity
    (I J : HeckeGeneral.ThetaSkeleton.ExteriorIdeal F (X.places : Set (HeightOneSpectrum (𝓞 F)))) :
    HeckeGeneral.ThetaSkeleton.Global.idealSymbol F (X.places : Set (HeightOneSpectrum (𝓞 F)))
        X.thetaData I (X.thetaData.generator J) =
      HeckeGeneral.ThetaSkeleton.Global.idealSymbol F (X.places : Set (HeightOneSpectrum (𝓞 F)))
        X.thetaData J (X.thetaData.generator I) := by
  rw [X.idealSymbol_eq I, X.idealSymbol_eq J]
  congr 1
  have hI := recipeGenerator_spec X.A (recipeOfContext X.A X.C) I
  have hJ := recipeGenerator_spec X.A (recipeOfContext X.A X.C) J
  by_cases hcop : ((exteriorEquiv X.A).symm I).val ⊔ ((exteriorEquiv X.A).symm J).val = ⊤
  · exact X.C.reciprocity.1 _ _ _ _ _ _ hI.1 hJ.1 hI.2 hJ.2
      ((recipeOfContext X.A X.C).allowed _) ((recipeOfContext X.A X.C).allowed _) hcop
  · obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hcop
    change X.A.sexticResidue _ (recipeGenerator X.A (recipeOfContext X.A X.C) J) =
      X.A.sexticResidue _ (recipeGenerator X.A (recipeOfContext X.A X.C) I)
    rw [ArithmeticContext.actual_sextic_nonunit X.A _ _
        (not_isUnit_of_common_maximal X.A _ _ _ hJ.1 M hM (le_sup_left.trans hle)
          (le_sup_right.trans hle)),
      ArithmeticContext.actual_sextic_nonunit X.A _ _
        (not_isUnit_of_common_maximal X.A _ _ _ hI.1 M hM (le_sup_right.trans hle)
          (le_sup_left.trans hle))]

end ArithmeticChoice

end HeckeAxiom
