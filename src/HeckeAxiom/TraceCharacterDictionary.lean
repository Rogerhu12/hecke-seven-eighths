import HeckeGeneral.Characters.SIntegerModulusPhase
import DedekindZetaZeroFree.Adeles.Approximation.SIntegerFiniteStrongApproximation
import DedekindZetaZeroFree.Adeles.Characters.GlobalTraceProductFormula
import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.CodifferentTraceDuality

/-!
# The two standard additive characters agree

At every finite place the skeleton's standard local character `psiLocal`
(from the standard adelic character) equals Axiom's `localTraceCharacter`
(the rational `p`-adic character of the local trace). Both global characters
are `e(Tr)` at infinity and trivial on the field, and both local characters are
trivial on the local integers, so on an element integral away from `v` each
local character at `v` is `e(-Tr)`. These elements are dense in the completion
at `v`, and both characters are continuous.

Consequently the skeleton's `S`-local principal phase is Axiom's field trace
character on the same finite set.
-/

noncomputable section

namespace HeckeAxiom

open NumberField IsDedekindDomain
open DedekindZetaZeroFree DedekindZetaZeroFree.SArithmeticData
open HeckeGeneral.Characters NumberField.StandardAddChar

variable {F : Type} [Field F] [NumberField F]

namespace TraceDictionary

theorem coe_mem_integers_of_sInteger (S : Finset (HeightOneSpectrum (𝓞 F)))
    (m : sIntegerRing F S) (w : HeightOneSpectrum (𝓞 F)) (hw : w ∉ S) :
    ((m : F) : w.adicCompletion F) ∈ w.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact Set.integer_valuation_le_one (S := (S : Set (HeightOneSpectrum (𝓞 F)))) F
    ⟨(m : F), m.property⟩ (fun h => hw (Finset.mem_coe.mp h))

theorem algebraMap_adicCompletion_apply (w : HeightOneSpectrum (𝓞 F)) (y : F) :
    algebraMap F (w.adicCompletion F) y = (y : w.adicCompletion F) := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  simp only [Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply]

theorem algebraMap_mem_integers_of_sInteger (S : Finset (HeightOneSpectrum (𝓞 F)))
    (m : sIntegerRing F S) (w : HeightOneSpectrum (𝓞 F)) (hw : w ∉ S) :
    algebraMap F (w.adicCompletion F) (m : F) ∈ w.adicCompletionIntegers F := by
  rw [algebraMap_adicCompletion_apply]
  exact coe_mem_integers_of_sInteger S m w hw

/-- On an element integral away from `v`, the standard local character at `v`
is `e(-Tr)`. -/
theorem psiLocal_singleton (v : HeightOneSpectrum (𝓞 F)) (m : sIntegerRing F {v}) :
    psiLocal F v (algebraMap F (v.adicCompletion F) (m : F)) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℚ F (m : F) : ℂ)) := by
  have hint : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ ({v} : Finset (HeightOneSpectrum (𝓞 F))) →
      (algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F)) w ∈ w.adicCompletionIntegers F := by
    intro w hw
    rw [FiniteAdeleRing.algebraMap_apply]
    exact coe_mem_integers_of_sInteger {v} m w hw
  have h := standardFiniteAddCharacter_eq_prod F
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F)) {v} hint
  rw [Finset.prod_singleton, FiniteAdeleRing.algebraMap_apply, standardFiniteAddCharacter_apply,
    stdAddChar_finitePrincipal] at h
  rw [algebraMap_adicCompletion_apply]
  exact h.symm

/-- On an element integral away from `v`, Axiom's local trace character at `v`
is `e(-Tr)`. -/
theorem localTraceCharacter_singleton (v : HeightOneSpectrum (𝓞 F)) (m : sIntegerRing F {v}) :
    (ResidueTrace.localTraceCharacter v (algebraMap F (v.adicCompletion F) (m : F)) : ℂ) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℚ F (m : F) : ℂ)) := by
  have hprod := ResidueTrace.diagonal_product_formula (m : F)
  rw [ResidueTraceFactorProductFormula.archTraceCharacter_product_eq_trace,
    finprod_eq_single _ v (fun w hw => CodifferentResidueSieve.localTraceCharacter_eq_one_of_integral w _
      (algebraMap_mem_integers_of_sInteger {v} m w (by simpa using hw)))] at hprod
  have hloc : ResidueTrace.localTraceCharacter v (algebraMap F (v.adicCompletion F) (m : F)) =
      Circle.exp (-(2 * Real.pi * ((Algebra.trace ℚ F (m : F) : ℚ) : ℝ))) := by
    rw [Circle.exp_neg]
    exact eq_inv_of_mul_eq_one_right hprod
  rw [hloc, Circle.coe_exp]
  congr 1
  push_cast
  ring

/-- The two standard local characters agree at every finite place. -/
theorem psiLocal_eq_localTraceCharacter (v : HeightOneSpectrum (𝓞 F)) (z : v.adicCompletion F) :
    psiLocal F v z = (ResidueTrace.localTraceCharacter v z : ℂ) := by
  classical
  let S : Finset (HeightOneSpectrum (𝓞 F)) := {v}
  let v' : S := ⟨v, Finset.mem_singleton_self v⟩
  let f : PoissonSFiniteDensity.Space F S → ℂ := fun y => psiLocal F v (y v')
  let g : PoissonSFiniteDensity.Space F S → ℂ :=
    fun y => (ResidueTrace.localTraceCharacter v (y v') : ℂ)
  have hf : Continuous f := (continuous_psiLocal F v).comp (continuous_apply v')
  have hg : Continuous g := continuous_subtype_val.comp
    ((ResidueTrace.continuous_localTraceCharacter v).comp (continuous_apply v'))
  have heq : f = g := (PoissonSFiniteDensity.diagonal_denseRange F S).equalizer hf hg (by
    funext m
    change psiLocal F v (algebraMap F (v.adicCompletion F) (m : F)) =
      (ResidueTrace.localTraceCharacter v (algebraMap F (v.adicCompletion F) (m : F)) : ℂ)
    rw [psiLocal_singleton v m, localTraceCharacter_singleton v m])
  have h := congr_fun heq (Pi.single v' z)
  simpa only [f, g, Pi.single_eq_same] using h

end TraceDictionary

/-- The skeleton's `Sf`-local principal phase is Axiom's field trace character. -/
theorem sLocalPrincipalPhase_eq_fieldTraceCharacter (A : SArithmeticData F) (y : F) :
    sLocalPrincipalPhase F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) y =
      (A.fieldTraceCharacter y : ℂ) := by
  change _ = (((∏ w, archTraceCharacter w ((sLocalDiagonal F A.Sf y).1 w)) *
    ∏ v : A.Sf, ResidueTrace.localTraceCharacter v.1 ((sLocalDiagonal F A.Sf y).2 v) : Circle) : ℂ)
  simp only [sLocalDiagonal_infinite, sLocalDiagonal_finite]
  rw [ResidueTraceFactorProductFormula.archTraceCharacter_product_eq_trace, Circle.coe_mul,
    Circle.coe_exp]
  change _ = _ * Circle.coeHom (∏ v : A.Sf, ResidueTrace.localTraceCharacter v.1
    (algebraMap F (v.1.adicCompletion F) y))
  rw [map_prod]
  unfold sLocalPrincipalPhase
  congr 1
  · congr 1
    push_cast
    ring
  · exact Fintype.prod_equiv (Equiv.subtypeEquivRight fun _ => Finset.mem_coe) _ _
      fun v => TraceDictionary.psiLocal_eq_localTraceCharacter v.val _

end HeckeAxiom
