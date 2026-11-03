import HeckeGeneral.Arithmetic.SIntegerModulusValuation
import HeckeGeneral.Characters.SIntegerModulusAdditive
import HeckeGeneral.Characters.ConductorCanonicalTrace
import HeckeGeneral.Characters.StandardFiniteFactorization

/-!
# Actual principal phases for an S-integer modulus

The frequency is the literal quotient h/c. Its completed valuation bounds
are proved from the contracted ideal. Standard global character
factorization identifies the resulting exterior phase with the positive
archimedean phase times the local factors in the original S.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open NumberField.StandardAddChar
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The positive standard principal character on the actual S-local factors. -/
def sLocalPrincipalPhase (x : K) : ℂ :=
  Complex.exp ((2 * Real.pi * Complex.I) * (Algebra.trace ℚ K x : ℂ)) *
    ∏ v : S, psiLocal K v.val (algebraMap K (v.val.adicCompletion K) x)

/-- All finite factors outside S and the actual modulus support are integral. -/
theorem sInteger_div_modulus_integral_outside
    (c : S.integer K) (hc : c ≠ 0) (h : S.integer K)
    (v : HeightOneSpectrum (𝓞 K)) (hvS : v ∉ S)
    (hvC : v ∉ sIntegerModulusPlaces K S c hc) :
    algebraMap K (v.adicCompletion K) ((h : K) / (c : K)) ∈
      v.adicCompletionIntegers K := by
  have hn : sIntegerModulusPrimeExponents K S c hc v = 0 :=
    Finsupp.notMem_support_iff.mp hvC
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  simpa only [hn, Int.natCast_zero, WithZero.exp_zero] using
    sInteger_div_modulus_completion_valuation_le K S c hc h v hvS

/-- Global cancellation leaves precisely the negative exterior local phase. -/
theorem sLocalPrincipalPhase_div_modulus_eq_exterior
    (c : S.integer K) (hc : c ≠ 0) (h : S.integer K) :
    sLocalPrincipalPhase K S ((h : K) / (c : K)) =
      ∏ v : sIntegerModulusPlaces K S c hc,
        psiLocal K v.val
          (-(algebraMap K (v.val.adicCompletion K) ((h : K) / (c : K)))) := by
  let x : K := (h : K) / (c : K)
  let P := sIntegerModulusPlaces K S c hc
  let F : HeightOneSpectrum (𝓞 K) → ℂ :=
    fun v => psiLocal K v (algebraMap K (v.adicCompletion K) (-x))
  have hdisj : Disjoint S.toFinset P := by
    apply Finset.disjoint_left.mpr
    intro v hvS hvP
    exact sIntegerModulusPlaces_not_mem K S c hc ⟨v, hvP⟩ (Set.mem_toFinset.mp hvS)
  have hint : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S.toFinset ∪ P →
      (algebraMap K (FiniteAdeleRing (𝓞 K) K) (-x)) v ∈
        v.adicCompletionIntegers K := by
    intro v hv
    have hvS : v ∉ S := fun h => hv (Finset.mem_union_left P (Set.mem_toFinset.mpr h))
    have hvP : v ∉ P := fun h => hv (Finset.mem_union_right S.toFinset h)
    change algebraMap K (v.adicCompletion K) (-x) ∈ _
    rw [map_neg]
    exact (v.adicCompletionIntegers K).neg_mem _
      (sInteger_div_modulus_integral_outside K S c hc h v hvS hvP)
  have htrace :
      Complex.exp ((2 * Real.pi * Complex.I) * (Algebra.trace ℚ K x : ℂ)) =
        (∏ v ∈ S.toFinset, F v) * (∏ v ∈ P, F v) := by
    calc
      _ = stdAddChar K ((0 : InfiniteAdeleRing K),
          algebraMap K (FiniteAdeleRing (𝓞 K) K) (-x)) := by
        rw [stdAddChar_finitePrincipal, map_neg]
        simp
      _ = ∏ v ∈ S.toFinset ∪ P, F v :=
        standardFiniteAddCharacter_eq_prod K _ _ hint
      _ = _ := Finset.prod_union hdisj
  have hcancel : (∏ v ∈ S.toFinset, F v) *
      (∏ v : S, psiLocal K v.val (algebraMap K (v.val.adicCompletion K) x)) = 1 := by
    rw [← Finset.prod_subtype S.toFinset (fun _ => Set.mem_toFinset)
      (fun v => psiLocal K v (algebraMap K (v.adicCompletion K) x))]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro v _
    dsimp only [F]
    rw [map_neg, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  change Complex.exp ((2 * Real.pi * Complex.I) * (Algebra.trace ℚ K x : ℂ)) * _ = _
  rw [htrace]
  calc
    _ = ((∏ v ∈ S.toFinset, F v) *
        (∏ v : S, psiLocal K v.val (algebraMap K (v.val.adicCompletion K) x))) *
          (∏ v ∈ P, F v) := by ring
    _ = ∏ v ∈ P, F v := by rw [hcancel, one_mul]
    _ = _ := by
      rw [← Finset.prod_coe_sort P F]
      apply Finset.prod_congr rfl
      intro v _
      dsimp only [F]
      rw [map_neg]

variable (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)

/-- The real h/c frequency, encoded in the actual finite quotient. -/
def sIntegerDivModulusFrequency (c : S.integer K) (hc : c ≠ 0) (h : S.integer K) :
    S.integer K ⧸ Ideal.span ({c} : Set (S.integer K)) :=
  sIntegerModulusFrequency K S c hc
    (fun v => algebraMap K (v.val.adicCompletion K) ((h : K) / (c : K)))
    (fun v => by
      rw [hS v.val (sIntegerModulusPlaces_not_mem K S c hc v), add_zero]
      exact sInteger_div_modulus_completion_valuation_le K S c hc h v.val
        (sIntegerModulusPlaces_not_mem K S c hc v))

/-- The actual S-local phase is the proved primitive character at the
actual h/c frequency; the frequency itself need not be a unit. -/
theorem sLocalPrincipalPhase_eq_modulusCharacter
    (c : S.integer K) (hc : c ≠ 0) (h a : S.integer K) :
    sLocalPrincipalPhase K S (((h : K) * (a : K)) / (c : K)) =
      sIntegerModulusAddCharacter K S c hc
        (sIntegerDivModulusFrequency K S hS c hc h *
          Ideal.Quotient.mk (Ideal.span ({c} : Set (S.integer K))) a) := by
  rw [sIntegerDivModulusFrequency, sIntegerModulusAddCharacter_frequency_mk K S c hc]
  change sLocalPrincipalPhase K S (((h * a : S.integer K) : K) / (c : K)) = _
  rw [sLocalPrincipalPhase_div_modulus_eq_exterior K S c hc (h * a)]
  apply Finset.prod_congr rfl
  intro v _
  congr 1
  change -(algebraMap K (v.val.adicCompletion K) (((h : K) * (a : K)) / (c : K))) = _
  rw [map_div₀, map_mul, map_div₀]
  ring

end HeckeGeneral.Characters
