import HeckeAxiom.ArithmeticAdapter
import DedekindZetaZeroFree.LargeSieve.CharacterBounds.AllIdealTransfer
import CubicSieve.ExteriorSieve

/-! The original S and the actual generators supply balanced arithmetic data.
No enlarged set of places, class-group assertion, or analytic recipe is an input. -/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.InitialArithmetic

open NumberField IsDedekindDomain
open DedekindZetaZeroFree
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped Classical NumberField

variable (K : Type) [Field K] [NumberField K]
variable (Sf : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (Sf : Set (HeightOneSpectrum (𝓞 K))))

def arithmeticData : SArithmeticData K where
  zeta12 := D.root12
  primitive_zeta12 := D.primitive12
  Sf := Sf
  S₀ := ∅
  bad_subset := Finset.empty_subset _
  modulus := ⊤
  modulus_ne_zero := top_ne_bot
  above_six := by
    intro v hv
    by_contra h
    exact D.away_six v h hv
  modulus_support := by
    intro v hv
    exact False.elim (v.isPrime.ne_top (top_le_iff.mp hv))

abbrev exteriorEquiv : (arithmeticData K Sf D).Exterior ≃
    ExteriorIdeal K (Sf : Set (HeightOneSpectrum (𝓞 K))) :=
  HeckeAxiom.exteriorEquiv (arithmeticData K Sf D)

theorem actual_generator (I : (arithmeticData K Sf D).Exterior) :
    (arithmeticData K Sf D).Generates I (D.generator (exteriorEquiv K Sf D I)) :=
  ⟨D.generator_ne_zero _, D.generator_span _⟩

/-- Move each actual generator by a sixth power of an S-unit into one compact box. -/
theorem exists_balanced_section :
    ∃ K_bal : Set (arithmeticData K Sf D).G, IsCompact K_bal ∧
      Nonempty ((arithmeticData K Sf D).BalancedIdealSection ⊤ K_bal) := by
  let A := arithmeticData K Sf D
  obtain ⟨C, hC, hcover⟩ := A.exists_compact_balanced_cover
  let K_bal : Set A.G := Subtype.val '' C
  have hcompact : IsCompact K_bal := hC.image continuous_subtype_val
  have hex : ∀ I : A.Exterior, ∃ (r : A.R) (a : Kˣ),
      A.Generates I r ∧ (a : K) = (r : K) ∧
      A.diagonal a / A.radialSection (A.exteriorNorm I) (A.exteriorNorm_pos I) ∈ K_bal := by
    intro I
    let r : A.R := D.generator (exteriorEquiv K Sf D I)
    have hg : A.Generates I r := actual_generator K Sf D I
    have hr : r ≠ 0 := hg.1
    have hspan : Ideal.span {r} = A.extendIdeal I := hg.2
    let a := Units.mk0 (r : K) (by exact_mod_cast hr)
    have ha : (a : K) = (r : K) := rfl
    let y : A.G1 := ⟨A.diagonal a /
      A.radialSection (A.exteriorNorm I) (A.exteriorNorm_pos I),
        A.normalized_generator_mem_G1 I r hg a ha⟩
    obtain ⟨γ, hγ⟩ := hcover y
    have hΓ : (γ.val : A.G) ∈ A.Gamma := γ.property
    obtain ⟨v, hv, hvγ⟩ := hΓ
    obtain ⟨u, hu, huv⟩ := hv
    let ε : A.U := ⟨u, hu⟩
    let r' : A.R := r * (A.unitEquiv ε ^ 6 : A.Rˣ)
    let a' : Kˣ := a * u ^ 6
    have ha' : (a' : K) = (r' : K) := by
      simp [a', r', ha, SArithmeticData.unitEquiv, ε]
    have hr' : A.Generates I r' := by
      refine ⟨mul_ne_zero hr (Units.ne_zero _), ?_⟩
      rw [Ideal.span_singleton_mul_right_unit (Units.isUnit _) r]
      exact hspan
    refine ⟨r', a', hr', ha', ?_⟩
    refine ⟨γ.val * y, hγ, ?_⟩
    change (γ.val : A.G) * (y : A.G) = _
    rw [← hvγ, ← huv]
    simp only [y, a', map_mul, map_pow, powMonoidHom_apply, div_eq_mul_inv]
    ac_rfl
  choose r a hr ha hb using hex
  refine ⟨K_bal, hcompact, ⟨{
    generator := r
    fieldUnit := a
    generates := hr
    fieldUnit_coe := ha
    allowed := ?_
    balanced := hb}⟩⟩
  intro I
  trivial

end CubicSieve.InitialArithmetic
