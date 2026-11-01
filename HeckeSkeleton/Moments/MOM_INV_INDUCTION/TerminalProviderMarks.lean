import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderFamily

/-!
# Original product marks become actual whole-index theta marks

Every tuple below chooses one prime from each surviving original list.
The coefficient is the product of the original individual coefficients;
the theta mark is the actual finite set of those primes. The source
identities use finite support before commuting the completed sums.
Cube priority keeps the frozen coefficient and deletes precisely the
original primes already assigned to the extracted cube.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalMarks

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOM_BASE
open HeckeSkeleton.Moments.MOMInvStep
open HeckeSkeleton.Moments.MOM_INV_STEP
open HeckePort.Moments
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable {σ : Type*} [DecidableEq σ]

def tuplePool (I : Finset σ) (L : σ → Finset (Ideal (𝓞 K))) :
    Finset (I → Ideal (𝓞 K)) := Fintype.piFinset (fun i => L i.val)

def tupleWeight (I : Finset σ) (a : σ → Ideal (𝓞 K) → ℂ)
    (q : I → Ideal (𝓞 K)) : ℂ := ∏ i : I, a i.val (q i)

def tuplePrime (I : Finset σ) (L : σ → Finset (Ideal (𝓞 K)))
    (hprime : ∀ i ∈ I, ∀ p ∈ L i, Prime p)
    (hexterior : ∀ i ∈ I, ∀ p ∈ L i, CanonicalChildren.IsExterior K S p)
    (q : tuplePool K I L) (i : I) : ExteriorPrime K S :=
  let hp := (Fintype.mem_piFinset.mp q.property) i
  let p := HeightOneSpectrum.ofPrime (hprime i.val i.property (q.val i) hp)
  ⟨p, (hexterior i.val i.property (q.val i) hp).2 p (dvd_refl _)⟩

def tuplePrimes (I : Finset σ) (L : σ → Finset (Ideal (𝓞 K)))
    (hprime : ∀ i ∈ I, ∀ p ∈ L i, Prime p)
    (hexterior : ∀ i ∈ I, ∀ p ∈ L i, CanonicalChildren.IsExterior K S p)
    (q : tuplePool K I L) : Finset (ExteriorPrime K S) :=
  Finset.univ.image (tuplePrime K S I L hprime hexterior q)

theorem tuplePrimes_divides (I : Finset σ) (L : σ → Finset (Ideal (𝓞 K)))
    (hprime : ∀ i ∈ I, ∀ p ∈ L i, Prime p)
    (hexterior : ∀ i ∈ I, ∀ p ∈ L i, CanonicalChildren.IsExterior K S p)
    (q : tuplePool K I L) (A : Ideal (𝓞 K)) :
    (∀ p ∈ tuplePrimes K S I L hprime hexterior q, p.val.asIdeal ∣ A) ↔
      ∀ i : I, q.val i ∣ A := by
  simp only [tuplePrimes, Finset.forall_mem_image, Finset.mem_univ, true_implies]
  rfl

/-- Literal product-of-sums expansion, including repeated choices.
Disjointness is required only for the later aggregation estimates. -/
theorem divisorMark_eq_whole_tuples
    (I : Finset σ) (L : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ)
    (hprime : ∀ i ∈ I, ∀ p ∈ L i, Prime p)
    (hexterior : ∀ i ∈ I, ∀ p ∈ L i, CanonicalChildren.IsExterior K S p)
    (A : Ideal (𝓞 K)) :
    divisorMark I L a A = ∑ q : tuplePool K I L,
      tupleWeight K I a q.val * wholeMarkWeight K S (tuplePrimes K S I L hprime hexterior q) A := by
  unfold divisorMark
  rw [← Finset.prod_coe_sort I
    (fun i => ∑ p ∈ L i, if p ∣ A then a i p else 0)]
  rw [Finset.prod_univ_sum]
  change (∑ q ∈ tuplePool K I L, ∏ i : I, if q i ∣ A then a i.val (q i) else 0) = _
  rw [← Finset.sum_coe_sort (tuplePool K I L)]
  apply Finset.sum_congr rfl
  intro q hq
  change (∏ i : I, if q.val i ∣ A then a i.val (q.val i) else 0) =
    tupleWeight K I a q.val *
      wholeMarkWeight K S (tuplePrimes K S I L hprime hexterior q) A
  rw [wholeMarkWeight, tuplePrimes_divides]
  by_cases h : ∀ i : I, q.val i ∣ A
  · simp only [if_pos h, mul_one, tupleWeight]
    apply Finset.prod_congr rfl
    intro i hi
    rw [if_pos (h i)]
  · rw [if_neg h, mul_zero]
    push_neg at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem tupleWeight_norm_le_one
    (I : Finset σ) (L : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ)
    (ha : ∀ i ∈ I, ∀ p ∈ L i, ‖a i p‖ ≤ 1) (q : tuplePool K I L) :
    ‖tupleWeight K I a q.val‖ ≤ 1 := by
  rw [tupleWeight, norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro i hi
  exact ha i.val i.property (q.val i) ((Fintype.mem_piFinset.mp q.property) i)

variable (D : ThetaArithmeticData K S)

theorem canonicalCompletedSum_eq_marked
    (θ : HeckeCharacter K) (m : S.integer K) (r : ExteriorIdeal K S)
    (d : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (X : ℝ) :
    canonicalCompletedSum (exteriorGamma K S D) (canonicalTau K S D θ m r.val.val) d V X =
      markedCompletedT (fun C B => canonicalCompletedTerm (exteriorGamma K S D)
        (canonicalTau K S D θ m r.val.val) (fun _ => 1) V X (C, B)) d := by
  apply tsum_congr
  intro C
  apply tsum_congr
  intro B
  simp only [canonicalCompletedTerm, Prod.fst, Prod.snd]
  split_ifs <;> ring

/-- Finite linearity of the genuine completed source. Compact test
support supplies the required summability for every original mark. -/
theorem canonicalCompletedSum_finset_linear {ι : Type*}
    (θ : HeckeCharacter K) (m : S.integer K) (r : ExteriorIdeal K S)
    (T : Finset ι) (a : ι → ℂ) (d : ι → Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (X U : ℝ) (hX : 0 < X)
    (hV : Function.support V ⊆ Set.Iic U) :
    canonicalCompletedSum (exteriorGamma K S D) (canonicalTau K S D θ m r.val.val)
        (fun A => ∑ i ∈ T, a i * d i A) V X =
      ∑ i ∈ T, a i * canonicalCompletedSum (exteriorGamma K S D)
        (canonicalTau K S D θ m r.val.val) (d i) V X := by
  simp_rw [canonicalCompletedSum_eq_marked]
  rw [markedCompletedT_finset_sum (actualCompletedSummand K S D θ m r V X U hX hV)]
  simp only [markedCompletedT_const_mul]

/-- Every tuple uses the original entire ideal `n*b³`; this identity
produces the precise marked theta source required by reflection. -/
theorem canonicalCompletedSum_eq_marked_tuples
    (θ : HeckeCharacter K) (m : S.integer K) (r : ExteriorIdeal K S)
    (I : Finset σ) (L : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ)
    (hprime : ∀ i ∈ I, ∀ p ∈ L i, Prime p)
    (hexterior : ∀ i ∈ I, ∀ p ∈ L i, CanonicalChildren.IsExterior K S p)
    (V : ℝ → ℂ) (X U : ℝ) (hX : 0 < X)
    (hV : Function.support V ⊆ Set.Iic U) :
    canonicalCompletedSum (exteriorGamma K S D) (canonicalTau K S D θ m r.val.val)
        (divisorMark I L a) V X =
      ∑ q : tuplePool K I L, tupleWeight K I a q.val *
        completedThetaSum K S D θ m r (tuplePrimes K S I L hprime hexterior q) V X := by
  have hd : divisorMark I L a = fun A => ∑ q : tuplePool K I L,
      tupleWeight K I a q.val * wholeMarkWeight K S (tuplePrimes K S I L hprime hexterior q) A :=
    funext (divisorMark_eq_whole_tuples K S I L a hprime hexterior)
  rw [hd, canonicalCompletedSum_finset_linear K S D θ m r
    Finset.univ _ _ V X U hX hV]
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  have hb := canonicalCompletedSum_eq_weightedTheta K S D θ m r
    (tuplePrimes K S I L hprime hexterior q) (fun _ => 1) V X U hX hV
  simpa only [mul_one, weightedCompletedTheta_one] using hb

/-- The extracted cube receives its slots first. Every remaining
slot uses its original coefficient and its exact residual list. -/
theorem canonicalCompletedSum_cube_priority
    (θ : HeckeCharacter K) (m : S.integer K) (r : ExteriorIdeal K S)
    (I : Finset σ) (L : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ) (H : Ideal (𝓞 K))
    (hprime : ∀ i ∈ I, ∀ p ∈ L i, Prime p)
    (V : ℝ → ℂ) (X U : ℝ) (hX : 0 < X)
    (hV : Function.support V ⊆ Set.Iic U) :
    canonicalCompletedSum (exteriorGamma K S D) (canonicalTau K S D θ m r.val.val)
        (fun A => divisorMark I L a (H ^ 3 * A)) V X =
      ∑ J ∈ I.powerset, divisorMark J L a (H ^ 3) *
        canonicalCompletedSum (exteriorGamma K S D) (canonicalTau K S D θ m r.val.val)
          (divisorMark (I \ J) (residualDivisorLists (H ^ 3) L) a) V X := by
  have hd : (fun A => divisorMark I L a (H ^ 3 * A)) =
      fun A => ∑ J ∈ I.powerset, divisorMark J L a (H ^ 3) *
        divisorMark (I \ J) (residualDivisorLists (H ^ 3) L) a A :=
    funext (fun A => mark_priority I L a (H ^ 3) A hprime)
  rw [hd]
  exact canonicalCompletedSum_finset_linear K S D θ m r I.powerset _ _ V X U hX hV

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalMarks

end
