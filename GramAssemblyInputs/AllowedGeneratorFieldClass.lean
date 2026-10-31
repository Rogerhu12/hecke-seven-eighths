import FiniteSUnitPowerLocalization
import HeckeGeneral.Analysis.MarkedThetaReflection

/-!
Small extraction (GR-12 phase 2) of the definitions of `ActualAllowedGeneratorAdjustment`
that the generator-mask consumers use, without its Hilbert-isotropy dependencies:
`fieldLocalPowerClassHom`, `generatorFieldUnit`, `generatorSameSClass`, their simp
lemmas, the actual S-unit ratio of generators with equal spans, and the
exponent-`n` law of the same-S local power quotients.

Statements and proofs are verbatim from the old sources
(`ActualAllowedGeneratorAdjustment`, `SameSPrimaryHilbertPairings`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Arithmetic.AllowedGeneratorConstruction

open NumberField IsDedekindDomain
open scoped Classical

variable (K : Type) [Field K] [NumberField K]

/-- Actual local quotient exponent, coordinate by coordinate. -/
theorem sameSLocalPowerQuotients_pow_eq_one
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ)
    (x : sameSLocalPowerQuotients K S n) : x ^ n = 1 := by
  funext q
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom n : (q.val.adicCompletion K)ˣ →* (q.val.adicCompletion K)ˣ).range (x q)
  change (x q) ^ n = 1
  rw [← ha, ← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩

theorem sameSLocalPowerQuotients_one_mul
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) (g : sameSLocalPowerQuotients K S n) :
    (1 : sameSLocalPowerQuotients K S n) * g = g := by
  funext q
  exact one_mul (g q)

theorem sameSLocalPowerQuotients_eq_div_of_mul_eq
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) {a b c : sameSLocalPowerQuotients K S n}
    (h : a * c = b) : a = b / c := by
  funext q
  exact (eq_div_iff_mul_eq').mpr (show a q * c q = b q from congrFun h q)

/-- The adic-completion valuation of an integral element is the global valuation. -/
theorem valued_algebraMap_integer (v : HeightOneSpectrum (𝓞 K)) (t : 𝓞 K) :
    (Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) t) : WithZero (Multiplicative ℤ)) =
      v.valuation K (algebraMap (𝓞 K) K t) := by
  rw [IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K) t]
  exact HeightOneSpectrum.adicCompletion.valued_coe (K := K) (v := v) _

end HeckeGeneral.Arithmetic.AllowedGeneratorConstruction

namespace HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Arithmetic.AllowedGeneratorConstruction
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- Localization on arbitrary field units, including generators which are
not S-units. Its target is the actual same-S product used by the pairing. -/
def fieldLocalPowerClassHom (n : ℕ) : Kˣ →* sameSLocalPowerQuotients K S n where
  toFun a q := QuotientGroup.mk' _ (finiteUnitLocalization K q.val a)
  map_one' := by ext q; simp
  map_mul' a b := by ext q; simp

@[simp] theorem fieldLocalPowerClassHom_sUnit (n : ℕ)
    (u : (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    fieldLocalPowerClassHom K S n (u : Kˣ) = sUnitLocalPowerClassHom K S n u := rfl

@[simp] theorem sUnitPowerLocalization_mk (n : ℕ)
    (u : (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    sUnitPowerLocalization K S n (QuotientGroup.mk' _ u) =
      fieldLocalPowerClassHom K S n (u : Kˣ) := rfl

variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

/-- The actual nonzero field unit represented by the supplied ideal
generator. The supplied section has no compatibility assumptions. -/
def generatorFieldUnit (I : ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K)))) : Kˣ :=
  nonzeroSIntegerFieldUnit K (S : Set (HeightOneSpectrum (𝓞 K)))
    ⟨D.generator I, D.generator_ne_zero I⟩

def generatorSameSClass (I : ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K)))) :
    sameSLocalPowerQuotients K S 6 :=
  fieldLocalPowerClassHom K S 6 (generatorFieldUnit K S D I)

/-- Equal actual principal ideals supply an actual S-unit ratio. -/
theorem exists_sUnit_ratio_of_span_eq
    (a b : (S : Set (HeightOneSpectrum (𝓞 K))).integer K)
    (hab : Ideal.span ({a} : Set ((S : Set (HeightOneSpectrum (𝓞 K))).integer K)) =
      Ideal.span ({b} : Set ((S : Set (HeightOneSpectrum (𝓞 K))).integer K))) :
    ∃ u : (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
      b = (((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K u).val) * a := by
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hab
  refine ⟨((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K).symm v, ?_⟩
  rw [MulEquiv.apply_symm_apply]
  exact hv.symm.trans (mul_comm _ _)

end HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft
