import HeckeGeneral.Analysis.HeckeFunctionalEquation
import HeckeGeneral.Characters.LocalConductor
import Mathlib.Tactic

/-!
Identify the finite scale used in the actual imported Tate functional equation.

The imported construction Mf6cc5d4cb452564c -> M0b8b452ededf3182 ->
Mbf3d750f6e1abdab chooses exactly F1Z.conductorOf K S rho as its Nf witness.
The latter is a finite product of prime norms with character-conductor plus
additive-character-level exponents. The results here compare those ACTUAL
exponents and that ACTUAL product with the local project's finite conductor.
No new or unrelated abstract functional equation is postulated.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.FunctionalEquationConductor

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Bridge HeckeGeneral.Analysis
open LanglandsTunnell.TateLocal
open P2MW.S_NumberField_TateGlobal_exists_entire_zetaIntegral_eq_mul_prod_Gamma_mul_eulerProduct_and_one_sub_eq_root_mul_cpow_of_archLocalChar_eq
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

private theorem fltLocalChar_eq_one_iff (χ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ) :
    NumberField.TateGlobal.localChar (complexIdeleCharacter K χ) v u = 1 ↔
      localComponent K v χ u = 1 := by
  rw [fltLocalChar_eq]
  constructor
  · intro h
    apply Subtype.ext
    exact congrArg (fun z : ℂˣ => (z : ℂ)) h
  · intro h
    rw [h, map_one]

/-- The two definitions use precisely the same unit filtration, including
the distinct depth-zero case of all integral units. -/
theorem trivialAtDepth_iff_higherUnits (χ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    TrivialAtDepth K χ v n ↔
      ∀ u ∈ higherUnitsAt K v n,
        NumberField.TateGlobal.localChar (complexIdeleCharacter K χ) v u = 1 := by
  have hnorm (u : (v.adicCompletion K)ˣ) :
      ‖u.val‖ = 1 ↔ (Valued.v u.val : WithZero (Multiplicative ℤ)) = 1 :=
    Valued.toNormedField.norm_eq_one_iff (L := v.adicCompletion K)
      (Γ₀ := WithZero (Multiplicative ℤ))
  cases n with
  | zero =>
    constructor
    · intro h u hu
      apply (fltLocalChar_eq_one_iff K χ v u).mpr
      exact h u ((hnorm u).mpr hu.1)
    · intro h u hu
      apply (fltLocalChar_eq_one_iff K χ v u).mp
      exact h u ⟨(hnorm u).mp hu, Or.inl rfl⟩
  | succ n =>
    constructor
    · intro h u hu
      apply (fltLocalChar_eq_one_iff K χ v u).mpr
      exact h u ((principalUnit_norm_iff_valuation K v u (n + 1)).mpr
        (hu.2.resolve_left (Nat.succ_ne_zero n)))
    · intro h u hu
      apply (fltLocalChar_eq_one_iff K χ v u).mp
      apply h u
      exact ⟨(hnorm u).mp (principalUnit_norm_one K v u (n + 1) (Nat.succ_pos n) hu),
        Or.inr ((principalUnit_norm_iff_valuation K v u (n + 1)).mp hu)⟩

/-- The main minimal-depth conductor satisfies the imported exact-conductor
predicate; the minimality witnesses are obtained from Nat.find minimality. -/
theorem hasConductorExponentAt_localConductorExponent (χ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) :
    HasConductorExponentAt K v
      (NumberField.TateGlobal.localChar (complexIdeleCharacter K χ) v)
      (localConductorExponent K χ v) := by
  refine ⟨(trivialAtDepth_iff_higherUnits K χ v _).mp
    (trivialAtDepth_localConductorExponent K χ v), ?_⟩
  intro n hn
  have hnot : ¬ (∀ u ∈ higherUnitsAt K v n,
      NumberField.TateGlobal.localChar (complexIdeleCharacter K χ) v u = 1) := by
    intro h
    have hle := localConductorExponent_le K χ v
      ((trivialAtDepth_iff_higherUnits K χ v n).mpr h)
    exact (Nat.not_le_of_gt hn) hle
  push_neg at hnot
  exact hnot

theorem fltConductorExponent_eq_localConductorExponent (χ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) :
    conductorExponentAt K v
      (NumberField.TateGlobal.localChar (complexIdeleCharacter K χ) v) =
      localConductorExponent K χ v :=
  conductorExponentAt_eq_of_hasConductorExponentAt K v
    (hasConductorExponentAt_localConductorExponent K χ v)

private theorem norm_finiteConductor_eq_primeProduct (χ : HeckeCharacter K) :
    ((finiteConductor K χ).val.absNorm : ℝ) =
      (conductorExponents K χ).prod
        (fun v n => (v.asIdeal.absNorm : ℝ) ^ n) := by
  have h := map_idealOfPrimeExponents
    (Ideal.absNorm : Ideal (𝓞 K) →*₀ ℕ).toMonoidHom (conductorExponents K χ)
  have hc := congrArg (fun n : ℕ => (n : ℝ)) h
  change ((idealOfPrimeExponents (conductorExponents K χ)).val.absNorm : ℝ) =
    (((conductorExponents K χ).prod
      (fun v n => v.asIdeal.absNorm ^ n) : ℕ) : ℝ) at hc
  simpa only [finiteConductor, Finsupp.prod, Nat.cast_prod, Nat.cast_pow] using hc

/-- The actual imported global Tate conductor is discriminant times the
norm of the actual finite conductor, for every unitary Hecke character. -/
theorem fltHeckeConductor_eq_discr_mul_finiteConductor (χ : HeckeCharacter K) :
    LanglandsTunnell.HeckeTate.heckeConductor K (complexIdeleCharacter K χ) =
      ((NumberField.discr K).natAbs : ℝ) * ((finiteConductor K χ).val.absNorm : ℝ) := by
  obtain ⟨T, hT⟩ := F1Z.exists_finset_forall_addCharLevel_psiLocal_eq_zero K
  let c : HeightOneSpectrum (𝓞 K) → ℝ :=
    fun v => (v.asIdeal.absNorm : ℝ) ^ localConductorExponent K χ v
  let d : HeightOneSpectrum (𝓞 K) → ℝ :=
    fun v => (v.asIdeal.absNorm : ℝ) ^ addCharLevel (NumberField.StandardAddChar.psiLocal K v)
  have hcSupport : Function.mulSupport c ⊆ (conductorExponents K χ).support := by
    intro v hv
    apply Finsupp.mem_support_iff.mpr
    intro h
    apply hv
    have hn : localConductorExponent K χ v = 0 := h
    simp only [c, hn, pow_zero]
  have hdSupport : Function.mulSupport d ⊆ (T : Set _) := by
    intro v hv
    by_contra hvT
    exact hv (by simp only [d, hT v hvT, zpow_zero])
  have hcFinite : Function.HasFiniteMulSupport c :=
    (conductorExponents K χ).support.finite_toSet.subset hcSupport
  have hdFinite : Function.HasFiniteMulSupport d := T.finite_toSet.subset hdSupport
  have hcProd : (∏ᶠ v, c v) = ((finiteConductor K χ).val.absNorm : ℝ) := by
    rw [finprod_eq_prod_of_mulSupport_subset c hcSupport,
      norm_finiteConductor_eq_primeProduct K χ]
    simp only [Finsupp.prod, c, conductorExponents_apply]
  have hdProd : (∏ᶠ v, d v) = ((NumberField.discr K).natAbs : ℝ) := by
    rw [finprod_eq_prod_of_mulSupport_subset d hdSupport,
      F1Z.natAbs_discr_eq_prod_absNorm_pow_addCharLevel K T hT]
    apply Finset.prod_congr rfl
    intro v _
    dsimp only [d]
    rw [← zpow_natCast]
    congr 1
    exact (Int.toNat_of_nonneg (F1Z.addCharLevel_psiLocal_nonneg K v)).symm
  calc
    LanglandsTunnell.HeckeTate.heckeConductor K (complexIdeleCharacter K χ) =
        ∏ᶠ v, c v * d v := by
      unfold LanglandsTunnell.HeckeTate.heckeConductor
      apply finprod_congr
      intro v
      rw [LanglandsTunnell.Converse.pinnedExp,
        fltConductorExponent_eq_localConductorExponent K χ v]
      have hqpos : 0 < (v.asIdeal.absNorm : ℝ) := by
        exact_mod_cast Nat.zero_lt_one.trans (one_lt_primeIdeal_absNorm K v)
      change (v.asIdeal.absNorm : ℝ) ^ ((localConductorExponent K χ v : ℤ) +
        addCharLevel (NumberField.StandardAddChar.psiLocal K v)) =
          (v.asIdeal.absNorm : ℝ) ^ localConductorExponent K χ v *
            (v.asIdeal.absNorm : ℝ) ^ addCharLevel (NumberField.StandardAddChar.psiLocal K v)
      rw [zpow_add₀ hqpos.ne', zpow_natCast]
    _ = (∏ᶠ v, c v) * (∏ᶠ v, d v) := finprod_mul_distrib hcFinite hdFinite
    _ = _ := by rw [hcProd, hdProd]; ring

theorem fltHeckeConductor_mul_normTwist (χ : HeckeCharacter K) (t : ℝ) :
    LanglandsTunnell.HeckeTate.heckeConductor K
        (complexIdeleCharacter K (χ * heckeNormTwist K t)) =
      LanglandsTunnell.HeckeTate.heckeConductor K (complexIdeleCharacter K χ) := by
  rw [fltHeckeConductor_eq_discr_mul_finiteConductor,
    fltHeckeConductor_eq_discr_mul_finiteConductor, finiteConductor_mul_normTwist]

/-- The pole-cleared norm branch has the same explicit discriminant scale,
independently of the moving pole height. -/
theorem fltHeckeConductor_normTwist (t : ℝ) :
    LanglandsTunnell.HeckeTate.heckeConductor K
        (complexIdeleCharacter K (heckeNormTwist K t)) =
      ((NumberField.discr K).natAbs : ℝ) := by
  rw [fltHeckeConductor_eq_discr_mul_finiteConductor, finiteConductor_normTwist]
  simp

/-- This is exactly the Nf expression selected by the imported construction,
with its original finite local-data matching hypotheses retained. -/
theorem conductorOf_eq_discr_mul_finiteConductor
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ρ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (χ : HeckeCharacter K)
    (hunr : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → UnramifiedAt K χ v)
    (hram : ∀ v ∈ S, ∀ u : (v.adicCompletion K)ˣ,
      (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
      ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
      NumberField.TateGlobal.localChar (complexIdeleCharacter K χ) v u = ρ v u) :
    F1Z.conductorOf K S ρ =
      ((NumberField.discr K).natAbs : ℝ) * ((finiteConductor K χ).val.absNorm : ℝ) := by
  rw [← F1Z.heckeConductor_eq_conductorOf K S ρ (complexIdeleCharacter K χ)
    (fun v hv => (fltUnramifiedAt_iff K χ v).mpr (hunr v hv)) hram]
  exact fltHeckeConductor_eq_discr_mul_finiteConductor K χ

end HeckeSkeleton.FunctionalEquationConductor
