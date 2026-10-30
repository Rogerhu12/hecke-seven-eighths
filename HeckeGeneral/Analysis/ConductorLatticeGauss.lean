import HeckeGeneral.Analysis.LatticeFiniteMask
import HeckeGeneral.Characters.ConductorTraceFrequency

/-!
The finite coefficients of actual trace-lattice Poisson are canonical conductor
Gauss sums at their actual residue frequencies. A polar frequency need not give
a unit residue: the nonunit case vanishes, and the unit case has squared norm
equal to the conductor norm. No primitivity hypothesis is inserted on a frequency.

-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField HeckeGeneral.Arithmetic HeckeGeneral.Characters
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

local instance conductorResidueFintype (χ : HeckeCharacter K) :
    Fintype (𝓞 K ⧸ (finiteConductor K χ).val) := Fintype.ofFinite _

private theorem gaussSum_fintype_independent {R : Type*} [CommRing R]
    (χ : MulChar R ℂ) (η : AddChar R ℂ) (A B : Fintype R) :
    (letI : Fintype R := A; gaussSum χ η) =
      (letI : Fintype R := B; gaussSum χ η) := by
  cases Subsingleton.elim A B
  rfl

/-- Every actual polar vector comes from the actual inverse-different ideal. -/
theorem exists_integralPolarFrequency (c : (Ideal (𝓞 K))⁰)
    (m : dualLattice (traceIdealLattice K (integralIdealUnit K c))) :
    ∃ ξ : K,
      ξ ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ *
        (c.val : FractionalIdeal (𝓞 K)⁰ K)⁻¹ ∧
      (m : mixedEmbedding.euclidean.mixedSpace K) =
        traceConjugation K (traceEmbedding K ξ) := by
  let m₀ : mixedEmbedding.euclidean.mixedSpace K := m
  have hm : m₀ ∈ dualLattice (traceIdealLattice K (integralIdealUnit K c)) := m.property
  rw [dualLattice_traceIdealLattice, conjugateTraceIdealLattice] at hm
  obtain ⟨x, hx, hxm⟩ := hm
  obtain ⟨ξ, hξ, hξx⟩ := exists_traceEmbedding_eq_of_mem_traceIdealLattice K
    (traceDualIdealUnit K (integralIdealUnit K c)) hx
  refine ⟨ξ, ?_, ?_⟩
  · simpa only [coe_traceDualIdealUnit_eq_inverseDifferent_mul_inv,
      coe_integralIdealUnit] using hξ
  · change traceConjugation K x = (m : mixedEmbedding.euclidean.mixedSpace K) at hxm
    rw [← hξx] at hxm
    exact hxm.symm

def integralPolarFrequency (c : (Ideal (𝓞 K))⁰)
    (m : dualLattice (traceIdealLattice K (integralIdealUnit K c))) : K :=
  (exists_integralPolarFrequency K c m).choose

theorem integralPolarFrequency_mem (c : (Ideal (𝓞 K))⁰)
    (m : dualLattice (traceIdealLattice K (integralIdealUnit K c))) :
    integralPolarFrequency K c m ∈
      (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ *
        (c.val : FractionalIdeal (𝓞 K)⁰ K)⁻¹ :=
  (exists_integralPolarFrequency K c m).choose_spec.1

theorem integralPolarFrequency_spec (c : (Ideal (𝓞 K))⁰)
    (m : dualLattice (traceIdealLattice K (integralIdealUnit K c))) :
    (m : mixedEmbedding.euclidean.mixedSpace K) =
      traceConjugation K (traceEmbedding K (integralPolarFrequency K c m)) :=
  (exists_integralPolarFrequency K c m).choose_spec.2

def conductorLatticeFrequency (χ : HeckeCharacter K)
    (m : dualLattice (traceIdealLattice K (integralIdealUnit K (finiteConductor K χ)))) :
    𝓞 K ⧸ (finiteConductor K χ).val :=
  conductorTraceFrequency K χ (integralPolarFrequency K (finiteConductor K χ) m)
    (integralPolarFrequency_mem K (finiteConductor K χ) m)

/-- The actual Poisson phase, including its positive trace sign. -/
theorem integralLatticeAddCharacter_eq_canonical (χ : HeckeCharacter K)
    (m : dualLattice (traceIdealLattice K (integralIdealUnit K (finiteConductor K χ)))) :
    integralLatticeAddCharacter K (finiteConductor K χ) m =
      (canonicalConductorAddCharacter K χ).mulShift (conductorLatticeFrequency K χ m) := by
  ext a
  refine Quotient.inductionOn' a ?_
  intro a
  change integralLatticeAddCharacter K (finiteConductor K χ) m (Ideal.Quotient.mk _ a) =
    ((canonicalConductorAddCharacter K χ).mulShift (conductorLatticeFrequency K χ m))
      (Ideal.Quotient.mk _ a)
  rw [integralLatticeAddCharacter_trace K (finiteConductor K χ) m
      (integralPolarFrequency K (finiteConductor K χ) m)
      (integralPolarFrequency_spec K (finiteConductor K χ) m), AddChar.mulShift_apply]
  simpa [conductorLatticeFrequency]
    using positiveTracePhase_eq_canonicalConductor_frequency K χ
      (integralPolarFrequency K (finiteConductor K χ) m)
      (integralPolarFrequency_mem K (finiteConductor K χ) m) a

def canonicalGaussFrequency (χ : HeckeCharacter K)
    (b : 𝓞 K ⧸ (finiteConductor K χ).val) : ℂ :=
  gaussSum (conductorMulCharacter K χ) ((canonicalConductorAddCharacter K χ).mulShift b)

theorem canonicalGaussFrequency_nonunit (χ : HeckeCharacter K)
    (b : 𝓞 K ⧸ (finiteConductor K χ).val) (hb : ¬ IsUnit b) :
    canonicalGaussFrequency K χ b = 0 := by
  unfold canonicalGaussFrequency canonicalConductorAddCharacter
  rw [AddChar.mulShift_mulShift]
  calc
    _ = conductorGaussFrequency K χ ((canonicalConductorAdditiveUnit K χ).val * b) := by
      rw [conductorGaussFrequency_eq_gaussSum]
      exact gaussSum_fintype_independent _ _ _ _
    _ = 0 := conductorGaussFrequency_nonunit K χ _
      (fun h => hb (isUnit_of_mul_isUnit_right h))

theorem canonicalGaussFrequency_unit (χ : HeckeCharacter K)
    (u : (𝓞 K ⧸ (finiteConductor K χ).val)ˣ) :
    canonicalGaussFrequency K χ u.val =
      (conductorUnitCharacter K χ u : ℂ)⁻¹ * canonicalConductorGauss K χ := by
  unfold canonicalGaussFrequency canonicalConductorGauss
  rw [gaussSum_mulShift_eq]
  congr 1
  · rw [MulChar.inv_apply_eq_inv, conductorMulCharacter_unit, Ring.inverse_eq_inv]
  · exact gaussSum_fintype_independent _ _ _ _

theorem canonicalGaussFrequency_norm_sq (χ : HeckeCharacter K)
    (b : 𝓞 K ⧸ (finiteConductor K χ).val) :
    ‖canonicalGaussFrequency K χ b‖ ^ 2 =
      if IsUnit b then (Ideal.absNorm (finiteConductor K χ).val : ℝ) else 0 := by
  by_cases hb : IsUnit b
  · rw [ite_eq_left hb]
    obtain ⟨u, rfl⟩ := hb
    rw [canonicalGaussFrequency_unit, norm_mul, norm_inv, Circle.norm_coe,
      inv_one, one_mul, canonicalConductorGauss_norm_sq]
  · rw [ite_eq_right hb, canonicalGaussFrequency_nonunit K χ b hb, norm_zero, zero_pow (by decide)]

/-- The coefficient in the already proved weighted Poisson identity has exact
unit support, determined from the polar vector rather than assumed. -/
theorem conductorLatticeGauss_eq (χ : HeckeCharacter K)
    (m : dualLattice (traceIdealLattice K (integralIdealUnit K (finiteConductor K χ)))) :
    gaussSum (conductorMulCharacter K χ)
      (integralLatticeAddCharacter K (finiteConductor K χ) m) =
        canonicalGaussFrequency K χ (conductorLatticeFrequency K χ m) := by
  rw [integralLatticeAddCharacter_eq_canonical]
  rfl

theorem conductorLatticeGauss_norm_sq (χ : HeckeCharacter K)
    (m : dualLattice (traceIdealLattice K (integralIdealUnit K (finiteConductor K χ)))) :
    ‖gaussSum (conductorMulCharacter K χ)
      (integralLatticeAddCharacter K (finiteConductor K χ) m)‖ ^ 2 =
        if IsUnit (conductorLatticeFrequency K χ m) then
          (Ideal.absNorm (finiteConductor K χ).val : ℝ) else 0 := by
  rw [conductorLatticeGauss_eq, canonicalGaussFrequency_norm_sq]

/-- Every actual polar coefficient has the uniform bound needed in a lattice tail,
with the dependence on the actual Hecke conductor retained. -/
theorem conductorLatticeGauss_norm_le (χ : HeckeCharacter K)
    (m : dualLattice (traceIdealLattice K (integralIdealUnit K (finiteConductor K χ)))) :
    ‖gaussSum (conductorMulCharacter K χ)
      (integralLatticeAddCharacter K (finiteConductor K χ) m)‖ ≤
        Real.sqrt (Ideal.absNorm (finiteConductor K χ).val : ℝ) := by
  apply Real.le_sqrt_of_sq_le
  rw [conductorLatticeGauss_norm_sq]
  split_ifs
  · exact le_rfl
  · exact Nat.cast_nonneg _

end HeckeGeneral.Analysis
