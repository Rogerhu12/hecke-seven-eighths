import HeckeGeneral.Characters.LocalConductorGauss

/-! Nonunit-frequency vanishing of the actual primitive local conductor Gauss transform. -/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

local instance frequencyResidueUnitFintype (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Fintype (LocalResidueRing K v n)ˣ := Fintype.ofFinite _

local instance frequencyResidueDualFintype (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Fintype (LocalResidueDual K v n) := Fintype.ofFinite _

/-- A nonunit frequency annihilates the final principal-unit layer modulo `m^(n+1)`. -/
theorem localResidue_nonunit_frequency_fixed (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (b : LocalResidueRing K v (n + 1)) (hb : ¬ IsUnit b)
    (a : (LocalResidueRing K v (n + 1))ˣ)
    (ha : a ∈ (localResidueUnitTransition K v (Nat.le_succ n)).ker) : a.val * b = b := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hx : x ∈ localMaximalIdeal K v := by
    change ¬ IsUnit x
    exact fun h => hb (h.map (Ideal.Quotient.mk _))
  obtain ⟨u, rfl⟩ := localUnitReduction_surjective K v (n + 1) a
  have hu : u ∈ principalUnits K v n := by
    change localUnitReduction K v n u = 1
    change localResidueUnitTransition K v (Nat.le_succ n)
      (localUnitReduction K v (n + 1) u) = 1 at ha
    simpa only [localResidueUnitTransition_reduction] using ha
  have herr : u.val - 1 ∈ localMaximalIdeal K v ^ n :=
    (mem_principalUnits_iff K v n u).mp hu
  have hprod : (u.val - 1) * x ∈ localMaximalIdeal K v ^ (n + 1) := by
    rw [pow_succ]
    exact Ideal.mul_mem_mul herr hx
  change Ideal.Quotient.mk (localMaximalIdeal K v ^ (n + 1)) u.val *
    Ideal.Quotient.mk _ x = Ideal.Quotient.mk _ x
  rw [← map_mul]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  simpa only [sub_mul, one_mul] using hprod

def localResidueGaussFrequency (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (χ : LocalResidueDual K v n) (η : AddChar (LocalResidueRing K v n) Circle)
    (b : LocalResidueRing K v n) : ℂ := localResidueGauss K v n χ (η.mulShift b)

theorem localResidueGaussFrequency_unit (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (χ : LocalResidueDual K v n) (η : AddChar (LocalResidueRing K v n) Circle)
    (b : (LocalResidueRing K v n)ˣ) :
    localResidueGaussFrequency K v n χ η b.val =
      (χ b : ℂ)⁻¹ * localResidueGauss K v n χ η :=
  localResidueGauss_mulShift_eq K v n χ η b

/-- The multiplicative conductor alone forces the nonunit-frequency support condition. -/
theorem localResidueGaussFrequency_nonunit (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (χ : LocalResidueDual K v (n + 1)) (hχ : PrimitiveLocalResidueCharacter K v (n + 1) χ)
    (η : AddChar (LocalResidueRing K v (n + 1)) Circle)
    (b : LocalResidueRing K v (n + 1)) (hb : ¬ IsUnit b) :
    localResidueGaussFrequency K v (n + 1) χ η b = 0 := by
  obtain ⟨a, ha, hχa⟩ := primitiveLocalResidueCharacter_detects_kernel K v hχ (Nat.lt_succ_self n)
  apply localResidueGauss_eq_zero_of_shift_invariant K v (n + 1) χ (η.mulShift b) a hχa
  apply AddChar.ext
  intro x
  change η (b * (a.val * x)) = η (b * x)
  rw [← mul_assoc, mul_comm b a.val, localResidue_nonunit_frequency_fixed K v n b hb a ha]

theorem localResidueGaussFrequency_support (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (χ : LocalResidueDual K v (n + 1)) (hχ : PrimitiveLocalResidueCharacter K v (n + 1) χ)
    (η : AddChar (LocalResidueRing K v (n + 1)) Circle) :
    Function.support (localResidueGaussFrequency K v (n + 1) χ η) ⊆
      {b : LocalResidueRing K v (n + 1) | IsUnit b} := by
  intro b hb
  by_contra h
  exact hb (localResidueGaussFrequency_nonunit K v n χ hχ η b h)

theorem localResidueGaussFrequency_nonunit_allDepth (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (χ : LocalResidueDual K v n) (hχ : PrimitiveLocalResidueCharacter K v n χ)
    (η : AddChar (LocalResidueRing K v n) Circle)
    (b : LocalResidueRing K v n) (hb : ¬ IsUnit b) :
    localResidueGaussFrequency K v n χ η b = 0 := by
  cases n with
  | zero =>
    have hs : Subsingleton (LocalResidueRing K v 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
    have : IsUnit b := by
      have he : b = 1 := hs.elim _ _
      rw [he]
      exact isUnit_one
    exact False.elim (hb this)
  | succ n =>
    exact localResidueGaussFrequency_nonunit K v n χ hχ η b hb

theorem conductorResidueGaussFrequency_nonunit (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) (η : AddChar
      (LocalResidueRing K v (localConductorExponent K χ v)) Circle)
    (b : LocalResidueRing K v (localConductorExponent K χ v)) (hb : ¬ IsUnit b) :
    localResidueGaussFrequency K v (localConductorExponent K χ v)
      (conductorResidueCharacter K v χ) η b = 0 :=
  localResidueGaussFrequency_nonunit_allDepth K v _ _
    (conductorResidueCharacter_isPrimitive K v χ) η b hb

theorem localResidueGaussFrequency_unit_norm (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (χ : LocalResidueDual K v n) (η : AddChar (LocalResidueRing K v n) Circle)
    (b : (LocalResidueRing K v n)ˣ) :
    ‖localResidueGaussFrequency K v n χ η b.val‖ = ‖localResidueGauss K v n χ η‖ := by
  rw [localResidueGaussFrequency_unit, norm_mul, norm_inv, Circle.norm_coe, inv_one, one_mul]

theorem localResidueGauss_as_Fourier (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (χ : LocalResidueDual K v n) (η : AddChar (LocalResidueRing K v n) Circle) :
    localResidueGauss K v n χ η =
      finiteFourierCoeff (LocalResidueRing K v n)ˣ (fun u => (η u.val : ℂ)) χ⁻¹ := by
  simp only [localResidueGauss, finiteFourierCoeff, MonoidHom.inv_apply, Circle.coe_inv, inv_inv]
  apply Finset.sum_congr rfl
  intro u _
  exact mul_comm _ _

theorem localResidueAddCharacter_unit_expansion (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (η : AddChar (LocalResidueRing K v n) Circle) (u : (LocalResidueRing K v n)ˣ) :
    (η u.val : ℂ) = (Nat.card (LocalResidueRing K v n)ˣ : ℂ)⁻¹ *
      ∑ χ : LocalResidueDual K v n, localResidueGauss K v n χ⁻¹ η * (χ u : ℂ) := by
  have he := congrFun (finiteFourier_inverse_coeff (LocalResidueRing K v n)ˣ
    (fun u => (η u.val : ℂ))) u
  symm
  simpa only [finiteFourierInverse, localResidueGauss_as_Fourier, inv_inv] using he

end HeckeGeneral.Characters
