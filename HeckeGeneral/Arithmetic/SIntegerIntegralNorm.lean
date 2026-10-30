import HeckeGeneral.Arithmetic.SIntegerIdealSaturation
import HeckeGeneral.Arithmetic.SIntegerOrbitNorm
import Mathlib.NumberTheory.NumberField.ProductFormula

/-!
# The actual S-local norm of an ordinary nonzero integer

The ordinary principal ideal is split into the prime powers inside and
outside the given finite set. At each exceptional prime the actual
completion norm cancels precisely the absolute norm of its prime power.
The remaining absolute ideal norm is therefore the actual S-local norm.
The argument uses factorization of ideals in a Dedekind domain and imposes
no principal-ideal-domain hypothesis on the ring of integers.

Build and declaration-audit evidence is tracked in docs/NEXT_POISSON.md.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

/-- The genuine ordinary principal ideal, with its nonzero proof retained. -/
def nonzeroIntegralPrincipalIdeal (d : 𝓞 K) (hd : d ≠ 0) : (Ideal (𝓞 K))⁰ :=
  ⟨Ideal.span ({d} : Set (𝓞 K)), mem_nonZeroDivisors_of_ne_zero (by
    intro h
    apply hd
    apply Ideal.span_singleton_eq_bot.mp
    simpa only [Ideal.zero_eq_bot] using h)⟩

@[simp] theorem nonzeroIntegralPrincipalIdeal_val (d : 𝓞 K) (hd : d ≠ 0) :
    (nonzeroIntegralPrincipalIdeal K d hd).val = Ideal.span ({d} : Set (𝓞 K)) := rfl

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

private theorem finsupp_prod_filter_mem_eq_prod_subtype
    {M : Type*} [CommMonoid M]
    (e : HeightOneSpectrum (𝓞 K) →₀ ℕ)
    (w : HeightOneSpectrum (𝓞 K) → ℕ → M) (hw : ∀ v, w v 0 = 1) :
    (e.filter (fun v => v ∈ S)).prod w = ∏ v : S, w v.val (e v.val) := by
  have hs : (e.filter (fun v => v ∈ S)).support ⊆ S.toFinset := by
    intro v hv
    rw [Finsupp.support_filter, Finset.mem_filter] at hv
    exact Set.mem_toFinset.mpr hv.2
  rw [Finsupp.prod_of_support_subset _ hs w (fun v _ => hw v)]
  calc
    (∏ v ∈ S.toFinset, w v ((e.filter (fun v => v ∈ S)) v)) =
        ∏ v ∈ S.toFinset, w v (e v) := by
      apply Finset.prod_congr rfl
      intro v hv
      rw [Finsupp.filter_apply_pos _ _ (Set.mem_toFinset.mp hv)]
    _ = ∏ v : S, w v.val (e v.val) :=
      Finset.prod_subtype S.toFinset (fun _ => Set.mem_toFinset) _

/-- Absolute ideal norm splits into the actual exceptional prime powers
and the actual ideal reconstructed from all exterior prime powers. -/
theorem absNorm_eq_inside_primeProduct_mul_outsideSIdeal
    (I : (Ideal (𝓞 K))⁰) :
    (I.val.absNorm : ℝ) =
      (∏ v : S, (v.val.asIdeal.absNorm : ℝ) ^ primeExponents I v.val) *
        ((outsideSIdeal K S I).val.absNorm : ℝ) := by
  let N : Ideal (𝓞 K) →* ℝ :=
    (Nat.castRingHom ℝ).toMonoidHom.comp Ideal.absNorm.toMonoidHom
  let e := primeExponents I
  let w : HeightOneSpectrum (𝓞 K) → ℕ → ℝ :=
    fun v n => (v.asIdeal.absNorm : ℝ) ^ n
  have hmap (f : HeightOneSpectrum (𝓞 K) →₀ ℕ) :
      N (idealOfPrimeExponents f).val = f.prod w :=
    map_idealOfPrimeExponents N f
  have hwhole : N I.val = e.prod w := by
    calc
      _ = N (idealOfPrimeExponents e).val :=
        congrArg (fun J : (Ideal (𝓞 K))⁰ => N J.val)
          (idealOfPrimeExponents_primeExponents I).symm
      _ = _ := hmap e
  change N I.val =
    (∏ v : S, w v.val (e v.val)) *
      N (idealOfPrimeExponents (e.filter (fun v => v ∉ S))).val
  calc
    _ = e.prod w := hwhole
    _ = (e.filter (fun v => v ∈ S)).prod w *
        (e.filter (fun v => v ∉ S)).prod w :=
      (Finsupp.prod_filter_mul_prod_filter_not (fun v => v ∈ S) e w).symm
    _ = _ := by
      rw [finsupp_prod_filter_mem_eq_prod_subtype K S e w (fun _ => pow_zero _),
        ← hmap]

/-- The actual finite completion norms cancel the exceptional ordinary
prime-power norms, with the full multiplicity at every prime retained. -/
theorem integral_finiteNorm_mul_insidePrimeNorm_eq_one
    (d : 𝓞 K) (hd : d ≠ 0) :
    (∏ v : S, ‖FinitePlace.embedding v.val (d : K)‖) *
      (∏ v : S, (v.val.asIdeal.absNorm : ℝ) ^
        primeExponents (nonzeroIntegralPrincipalIdeal K d hd) v.val) = 1 := by
  have hI : (Ideal.span ({d} : Set (𝓞 K))) ≠ 0 :=
    nonZeroDivisors.coe_ne_zero (nonzeroIntegralPrincipalIdeal K d hd)
  have hlocal (v : S) :
      ‖FinitePlace.embedding v.val (d : K)‖ *
        (v.val.asIdeal.absNorm : ℝ) ^
          primeExponents (nonzeroIntegralPrincipalIdeal K d hd) v.val = 1 := by
    have h := NumberField.HeightOneSpectrum.embedding_mul_absNorm K v.val hd
    rw [v.val.maxPowDividing_eq_pow_multiset_count hI, map_pow, Nat.cast_pow] at h
    simpa only [primeExponents_apply, nonzeroIntegralPrincipalIdeal_val,
      RingOfIntegers.coe_eq_algebraMap] using h
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun v _ => hlocal v

/-- The actual positive S-local norm of an ordinary nonzero integer equals
the absolute norm of its exterior ordinary ideal. The formula uses the
genuine local completion norms, rather than a substituted ideal norm. -/
theorem sLocalProductNorm_integral_eq_absNorm_outsideSIdeal
    (d : 𝓞 K) (hd : d ≠ 0) :
    mixedEmbedding.norm (mixedEmbedding K (d : K)) *
        (∏ v : S, ‖FinitePlace.embedding v.val (d : K)‖) =
      ((outsideSIdeal K S (nonzeroIntegralPrincipalIdeal K d hd)).val.absNorm : ℝ) := by
  let I := nonzeroIntegralPrincipalIdeal K d hd
  have harch : (I.val.absNorm : ℝ) =
      mixedEmbedding.norm (mixedEmbedding K (d : K)) := by
    change (Ideal.absNorm (Ideal.span ({d} : Set (𝓞 K))) : ℝ) = _
    rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, ← Rat.cast_intCast,
      Int.cast_abs, Algebra.coe_norm_int, mixedEmbedding.norm_eq_norm]
  have hsplit := absNorm_eq_inside_primeProduct_mul_outsideSIdeal K S I
  have hcancel := integral_finiteNorm_mul_insidePrimeNorm_eq_one K S d hd
  calc
    _ = (I.val.absNorm : ℝ) * (∏ v : S, ‖FinitePlace.embedding v.val (d : K)‖) := by
      rw [harch]
    _ = ((∏ v : S, (v.val.asIdeal.absNorm : ℝ) ^ primeExponents I v.val) *
        ((outsideSIdeal K S I).val.absNorm : ℝ)) *
        (∏ v : S, ‖FinitePlace.embedding v.val (d : K)‖) := by rw [hsplit]
    _ = ((outsideSIdeal K S I).val.absNorm : ℝ) *
        ((∏ v : S, ‖FinitePlace.embedding v.val (d : K)‖) *
          (∏ v : S, (v.val.asIdeal.absNorm : ℝ) ^ primeExponents I v.val)) := by ring
    _ = _ := by rw [hcancel, mul_one]

end HeckeGeneral.Arithmetic
