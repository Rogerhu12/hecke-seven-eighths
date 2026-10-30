import HeckeGeneral.Characters.LocalCanonicalFrequency
import FLTReuse.Mbb4ca29c119a4960
import FLTReuse.M8b1d7aa14f2cc110
import FLTReuse.M55164c2a16500130
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Actual local residue cosets and their negative-sign Fourier transforms

The residue representative is a genuine local integer. Its coset is the
valuation ball of radius `exp (-n)`, including depth zero. Compactness and
local constancy are proved by identifying this ball with the translate of
`pi^n O_v`. The transform retains the chosen additive Haar measure and the
actual different exponent of the standard local character.

Build and declaration-audit evidence is tracked in docs/NEXT_POISSON.md.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField.StandardAddChar NumberField.AdelicFourier
open LanglandsTunnell.TateLocal MeasureTheory
open scoped Classical

variable (K : Type) [Field K] [NumberField K]

/-- An actual local integer representing the given residue class. -/
def localResidueLift (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (r : LocalResidueRing K v n) : LocalIntegerRing K v :=
  (Ideal.Quotient.mk_surjective r).choose

@[simp] theorem localResidueLift_mk (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (r : LocalResidueRing K v n) :
    Ideal.Quotient.mk (localMaximalIdeal K v ^ n) (localResidueLift K v n r) = r :=
  (Ideal.Quotient.mk_surjective r).choose_spec

/-- The actual additive coset, considered in the whole completion. -/
def localResidueCosetSet (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (r : LocalResidueRing K v n) : Set (v.adicCompletion K) :=
  {z | Valued.v (z - (localResidueLift K v n r : v.adicCompletion K)) ≤
    WithZero.exp (-(n : ℤ))}

/-- Membership agrees with literal reduction of every local integer. -/
theorem mem_localResidueCosetSet_iff (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (r : LocalResidueRing K v n) (x : LocalIntegerRing K v) :
    (x : v.adicCompletion K) ∈ localResidueCosetSet K v n r ↔
      Ideal.Quotient.mk (localMaximalIdeal K v ^ n) x = r := by
  calc
    _ ↔ Ideal.Quotient.mk (localMaximalIdeal K v ^ n) x =
        Ideal.Quotient.mk (localMaximalIdeal K v ^ n) (localResidueLift K v n r) := by
      rw [Ideal.Quotient.eq]
      exact (local_mem_maximalIdeal_pow_iff_valuation K v
        (x - localResidueLift K v n r) n).symm
    _ ↔ _ := by rw [localResidueLift_mk]

/-- The valuation ball is the actual translate of the uniformizer-power ideal. -/
theorem localResidueCosetSet_eq_image (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (r : LocalResidueRing K v n) :
    localResidueCosetSet K v n r =
      (fun z : v.adicCompletion K =>
        (localResidueLift K v n r : v.adicCompletion K) + localUniformizer K v ^ n * z) ''
          (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  ext z
  constructor
  · intro hz
    have hzv : Valued.v (z - (localResidueLift K v n r : v.adicCompletion K)) ≤
        WithZero.exp (-(n : ℤ)) := hz
    have hzi : z - (localResidueLift K v n r : v.adicCompletion K) ∈
        v.adicCompletionIntegers K := by
      rw [mem_adicCompletionIntegers]
      exact hzv.trans (WithZero.exp_le_exp.mpr (show -(n : ℤ) ≤ 0 by omega))
    let x : LocalIntegerRing K v := ⟨z - (localResidueLift K v n r), hzi⟩
    have hx : x ∈ localMaximalIdeal K v ^ n :=
      (local_mem_maximalIdeal_pow_iff_valuation K v x n).mpr hzv
    rw [localMaximalIdeal, local_maximalIdeal_pow_eq_span_uniformizer_pow] at hx
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hx
    refine ⟨(t : v.adicCompletion K), t.property, ?_⟩
    have ht' := congrArg (fun b : LocalIntegerRing K v => (b : v.adicCompletion K)) ht
    change z - (localResidueLift K v n r : v.adicCompletion K) =
      localUniformizer K v ^ n * (t : v.adicCompletion K) at ht'
    change (localResidueLift K v n r : v.adicCompletion K) +
      localUniformizer K v ^ n * (t : v.adicCompletion K) = z
    rw [← ht']
    ring
  · rintro ⟨t, ht, rfl⟩
    let x : LocalIntegerRing K v := ⟨t, ht⟩
    have hx : localUniformizerInteger K v ^ n * x ∈ localMaximalIdeal K v ^ n := by
      rw [localMaximalIdeal, local_maximalIdeal_pow_eq_span_uniformizer_pow]
      exact Ideal.mem_span_singleton.mpr ⟨x, rfl⟩
    have hv := (local_mem_maximalIdeal_pow_iff_valuation K v _ n).mp hx
    change Valued.v (localUniformizer K v ^ n * t) ≤ WithZero.exp (-(n : ℤ)) at hv
    change Valued.v (((localResidueLift K v n r : v.adicCompletion K) +
      localUniformizer K v ^ n * t) - (localResidueLift K v n r)) ≤ _
    simpa only [add_sub_cancel_left] using hv

theorem isCompact_localResidueCosetSet (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (r : LocalResidueRing K v n) : IsCompact (localResidueCosetSet K v n r) := by
  letI : CompactSpace (LocalIntegerRing K v) :=
    NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v
  have hO : IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    isCompact_iff_compactSpace.mpr inferInstance
  rw [localResidueCosetSet_eq_image]
  exact hO.image (continuous_const.add (continuous_const.mul continuous_id))

theorem isClopen_localResidueCosetSet (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (r : LocalResidueRing K v n) : IsClopen (localResidueCosetSet K v n r) := by
  let e : v.adicCompletion K ≃ₜ v.adicCompletion K :=
    (Homeomorph.mulLeft₀ (localUniformizer K v ^ n)
      (pow_ne_zero n (localUniformizer_ne_zero K v))).trans
      (Homeomorph.addLeft (localResidueLift K v n r : v.adicCompletion K))
  have hO : IsClopen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    Valued.isClopen_valuationSubring (v.adicCompletion K)
  rw [localResidueCosetSet_eq_image]
  change IsClopen (e '' (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
  exact ⟨e.isClosedMap _ hO.isClosed, e.isOpenMap _ hO.isOpen⟩

def localResidueCosetIndicator (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (r : LocalResidueRing K v n) : v.adicCompletion K → ℂ :=
  (localResidueCosetSet K v n r).indicator (fun _ => 1)

theorem localResidueCosetIndicator_locallyConstant_compactSupport
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (r : LocalResidueRing K v n) :
    IsLocallyConstant (localResidueCosetIndicator K v n r) ∧
      HasCompactSupport (localResidueCosetIndicator K v n r) :=
  IsSchwartzBruhat.indicator_const (isClopen_localResidueCosetSet K v n r)
    (isCompact_localResidueCosetSet K v n r) 1

@[simp] theorem localResidueCosetIndicator_integer (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (r : LocalResidueRing K v n) (a : LocalIntegerRing K v) :
    localResidueCosetIndicator K v n r (a : v.adicCompletion K) =
      if Ideal.Quotient.mk (localMaximalIdeal K v ^ n) a = r then 1 else 0 := by
  simp only [localResidueCosetIndicator, Set.indicator, mem_localResidueCosetSet_iff]

/-- Replacing the chosen lift by any actual local representative preserves the coset. -/
theorem localResidueCosetSet_eq_center_ball (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (r : LocalResidueRing K v n) (center : LocalIntegerRing K v)
    (hcenter : Ideal.Quotient.mk (localMaximalIdeal K v ^ n) center = r) :
    localResidueCosetSet K v n r =
      {z : v.adicCompletion K | Valued.v (z - (center : v.adicCompletion K)) ≤
        WithZero.exp (-(n : ℤ))} := by
  have hd : Valued.v ((localResidueLift K v n r : v.adicCompletion K) - center) ≤
      WithZero.exp (-(n : ℤ)) :=
    (local_mem_maximalIdeal_pow_iff_valuation K v
      (localResidueLift K v n r - center) n).mp
      (Ideal.Quotient.eq.mp ((localResidueLift_mk K v n r).trans hcenter.symm))
  have hd' : Valued.v ((center : v.adicCompletion K) - localResidueLift K v n r) ≤
      WithZero.exp (-(n : ℤ)) := by
    rw [Valuation.map_sub_swap]
    exact hd
  ext z
  constructor
  · intro hz
    calc
      Valued.v (z - (center : v.adicCompletion K)) =
          Valued.v ((z - (localResidueLift K v n r : v.adicCompletion K)) +
            ((localResidueLift K v n r : v.adicCompletion K) - center)) := by congr 1; ring
      _ ≤ max (Valued.v (z - (localResidueLift K v n r : v.adicCompletion K)))
          (Valued.v ((localResidueLift K v n r : v.adicCompletion K) - center)) :=
        Valuation.map_add _ _ _
      _ ≤ _ := max_le hz hd
  · intro hz
    change Valued.v (z - (localResidueLift K v n r : v.adicCompletion K)) ≤ _
    calc
      _ = Valued.v ((z - (center : v.adicCompletion K)) +
          ((center : v.adicCompletion K) - localResidueLift K v n r)) := by congr 1; ring
      _ ≤ max (Valued.v (z - (center : v.adicCompletion K)))
          (Valued.v ((center : v.adicCompletion K) - localResidueLift K v n r)) :=
        Valuation.map_add _ _ _
      _ ≤ _ := max_le hz hd'

/-- A coset with a supplied actual local integer center, allowing global CRT lifts. -/
def localIntegerResidueCosetIndicator (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (center : LocalIntegerRing K v) : v.adicCompletion K → ℂ :=
  {z : v.adicCompletion K | Valued.v (z - (center : v.adicCompletion K)) ≤
    WithZero.exp (-(n : ℤ))}.indicator (fun _ => 1)

theorem localResidueCosetIndicator_eq_center (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (r : LocalResidueRing K v n) (center : LocalIntegerRing K v)
    (hcenter : Ideal.Quotient.mk (localMaximalIdeal K v ^ n) center = r) :
    localResidueCosetIndicator K v n r = localIntegerResidueCosetIndicator K v n center := by
  unfold localResidueCosetIndicator localIntegerResidueCosetIndicator
  rw [localResidueCosetSet_eq_center_ball K v n r center hcenter]

theorem localIntegerResidueCosetIndicator_locallyConstant_compactSupport
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (center : LocalIntegerRing K v) :
    IsLocallyConstant (localIntegerResidueCosetIndicator K v n center) ∧
      HasCompactSupport (localIntegerResidueCosetIndicator K v n center) := by
  rw [← localResidueCosetIndicator_eq_center K v n
    (Ideal.Quotient.mk (localMaximalIdeal K v ^ n) center) center rfl]
  exact localResidueCosetIndicator_locallyConstant_compactSupport K v n _

@[simp] theorem localIntegerResidueCosetIndicator_integer (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (center a : LocalIntegerRing K v) :
    localIntegerResidueCosetIndicator K v n center (a : v.adicCompletion K) =
      if Ideal.Quotient.mk (localMaximalIdeal K v ^ n) a =
        Ideal.Quotient.mk (localMaximalIdeal K v ^ n) center then 1 else 0 := by
  rw [← localResidueCosetIndicator_eq_center K v n
    (Ideal.Quotient.mk (localMaximalIdeal K v ^ n) center) center rfl]
  exact localResidueCosetIndicator_integer K v n _ a

/-- An integral residue coset contains no nonintegral point of the completion. -/
theorem localIntegerResidueCosetIndicator_nonzero_integral
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (center : LocalIntegerRing K v)
    (z : v.adicCompletion K)
    (hz : localIntegerResidueCosetIndicator K v n center z ≠ 0) :
    z ∈ v.adicCompletionIntegers K := by
  have hball : Valued.v (z - (center : v.adicCompletion K)) ≤
      WithZero.exp (-(n : ℤ)) := by
    by_contra h
    exact hz (by simp [localIntegerResidueCosetIndicator, Set.indicator, h])
  have hsmall : Valued.v (z - (center : v.adicCompletion K)) ≤ 1 :=
    hball.trans (WithZero.exp_le_exp.mpr (show -(n : ℤ) ≤ 0 by omega))
  have hc : Valued.v (center : v.adicCompletion K) ≤ 1 := by
    simpa only [mem_adicCompletionIntegers] using center.property
  rw [mem_adicCompletionIntegers]
  calc
    Valued.v z = Valued.v ((z - (center : v.adicCompletion K)) + center) := by
      rw [sub_add_cancel]
    _ ≤ max (Valued.v (z - (center : v.adicCompletion K)))
        (Valued.v (center : v.adicCompletion K)) := Valuation.map_add _ _ _
    _ ≤ 1 := max_le hsmall hc

variable (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
  [BorelSpace (v.adicCompletion K)]
  (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]

/-- Negative-sign Fourier formula with arbitrary additive Haar normalization.
The support uses the actual different exponent, without any self-duality assumption. -/
theorem fourierIntegral_localResidueCosetIndicator (n : ℕ)
    (r : LocalResidueRing K v n) (w : v.adicCompletion K) :
    fourierIntegral (psiLocal K v) μ (localResidueCosetIndicator K v n r) w =
      psiLocal K v (-((localResidueLift K v n r : v.adicCompletion K) * w)) *
        ((μ.real {z : v.adicCompletion K | Valued.v z ≤ WithZero.exp (-(n : ℤ))} : ℝ) : ℂ) *
        (if Valued.v w ≤ WithZero.exp (localDifferentExponent K v + (n : ℤ)) then 1 else 0) := by
  have hlevel := standardLocalAddCharacter_level K v
  rw [addCharLevel_psiLocal_eq_count_differentIdeal] at hlevel
  have h := tateFourier_indicator_setOf_valued_sub_le K v μ (psiLocal K v)
    (localDifferentExponent K v) hlevel.1 hlevel.2
    (localResidueLift K v n r : v.adicCompletion K) (n : ℤ) (-w)
  have hsign : fourierIntegral (psiLocal K v) μ (localResidueCosetIndicator K v n r) w =
      tateFourier (psiLocal K v) μ (localResidueCosetIndicator K v n r) (-w) := by
    unfold fourierIntegral tateFourier
    congr 1
    funext z
    rw [mul_neg, mul_comm]
  rw [hsign]
  simpa only [localResidueCosetIndicator, localResidueCosetSet, Set.indicator,
    Set.mem_setOf_eq, Valuation.map_neg, mul_neg] using h

/-- Explicit ball mass; the original Haar mass of `O_v` remains present. -/
theorem fourierIntegral_localResidueCosetIndicator_mass (n : ℕ)
    (r : LocalResidueRing K v n) (w : v.adicCompletion K) :
    fourierIntegral (psiLocal K v) μ (localResidueCosetIndicator K v n r) w =
      psiLocal K v (-((localResidueLift K v n r : v.adicCompletion K) * w)) *
        (((v.asIdeal.absNorm : ℝ) ^ (-(n : ℤ)) *
          μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℝ) : ℂ) *
        (if Valued.v w ≤ WithZero.exp (localDifferentExponent K v + (n : ℤ)) then 1 else 0) := by
  rw [fourierIntegral_localResidueCosetIndicator, measureReal_setOf_valued_le_exp]

/-- The negative-sign transform at any actual local integer center, without
identifying it with the independently chosen residue lift. -/
theorem fourierIntegral_localIntegerResidueCosetIndicator (n : ℕ)
    (center : LocalIntegerRing K v) (w : v.adicCompletion K) :
    fourierIntegral (psiLocal K v) μ (localIntegerResidueCosetIndicator K v n center) w =
      psiLocal K v (-((center : v.adicCompletion K) * w)) *
        ((μ.real {z : v.adicCompletion K | Valued.v z ≤ WithZero.exp (-(n : ℤ))} : ℝ) : ℂ) *
        (if Valued.v w ≤ WithZero.exp (localDifferentExponent K v + (n : ℤ)) then 1 else 0) := by
  have hlevel := standardLocalAddCharacter_level K v
  rw [addCharLevel_psiLocal_eq_count_differentIdeal] at hlevel
  have h := tateFourier_indicator_setOf_valued_sub_le K v μ (psiLocal K v)
    (localDifferentExponent K v) hlevel.1 hlevel.2 (center : v.adicCompletion K) (n : ℤ) (-w)
  have hsign : fourierIntegral (psiLocal K v) μ (localIntegerResidueCosetIndicator K v n center) w =
      tateFourier (psiLocal K v) μ (localIntegerResidueCosetIndicator K v n center) (-w) := by
    unfold fourierIntegral tateFourier
    congr 1
    funext z
    rw [mul_neg, mul_comm]
  rw [hsign]
  simpa only [localIntegerResidueCosetIndicator, Set.indicator,
    Set.mem_setOf_eq, Valuation.map_neg, mul_neg] using h

theorem fourierIntegral_localIntegerResidueCosetIndicator_mass (n : ℕ)
    (center : LocalIntegerRing K v) (w : v.adicCompletion K) :
    fourierIntegral (psiLocal K v) μ (localIntegerResidueCosetIndicator K v n center) w =
      psiLocal K v (-((center : v.adicCompletion K) * w)) *
        (((v.asIdeal.absNorm : ℝ) ^ (-(n : ℤ)) *
          μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℝ) : ℂ) *
        (if Valued.v w ≤ WithZero.exp (localDifferentExponent K v + (n : ℤ)) then 1 else 0) := by
  rw [fourierIntegral_localIntegerResidueCosetIndicator, measureReal_setOf_valued_le_exp]

end HeckeGeneral.Characters
