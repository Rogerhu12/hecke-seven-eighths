import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalRawNormalization

/-!
# The exceptional raw mass follows from the original atoms

The data below contain only norm windows for actual frozen ideals,
the formal rectangle product, and each retained prime atom.  In
particular there is no hypothesis about a source polynomial, its raw
mass, an exceptional sum, or the final terminal budget.  The frozen
scalar is estimated using its original central denominators.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis HeckePort.Moments

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k : ℕ}

/-- Numerical atom windows fixed for the literal allocation, before
the original exceptional row.  The exponent is computed from these
windows; it is not a freely chosen bound for the source. -/
structure ExceptionalAtomicScales (B : ActualColumnAllocation F k) where
  annulus : Fin k → ℝ
  profileSquare : Fin k → ℝ
  annulus_nonneg : ∀ i, 0 ≤ annulus i
  profileSquare_nonneg : ∀ i, 0 ≤ profileSquare i
  frozenExponent : ℝ
  rootConstant : ℝ
  rootExponent : ℝ
  rootConstant_nonneg : 0 ≤ rootConstant
  cutoffConstant : Fin B.keep.card → ℝ
  cutoffExponent : Fin B.keep.card → ℝ
  atomConstant : Fin B.keep.card → ℝ
  atomExponent : Fin B.keep.card → ℝ
  cutoffConstant_one : ∀ j, 1 ≤ cutoffConstant j
  cutoffExponent_nonneg : ∀ j, 0 ≤ cutoffExponent j
  atomConstant_nonneg : ∀ j, 0 ≤ atomConstant j

namespace ExceptionalAtomicScales

variable {B : ActualColumnAllocation F k} (U : ExceptionalAtomicScales B)

def frozenNumerator : ℝ :=
  ∏ i ∈ Finset.univ \ B.keep, U.annulus i * U.profileSquare i

def constant : ℝ :=
  Real.sqrt U.frozenNumerator * U.rootConstant *
    ∏ j, (idealCountConstant F * U.cutoffConstant j) * U.atomConstant j

def exponent : ℝ :=
  -U.frozenExponent / 2 + U.rootExponent +
    ∑ j, (U.cutoffExponent j + U.atomExponent j)

theorem frozenNumerator_nonneg : 0 ≤ U.frozenNumerator :=
  Finset.prod_nonneg (fun i _ =>
    mul_nonneg (U.annulus_nonneg i) (U.profileSquare_nonneg i))

theorem constant_nonneg : 0 ≤ U.constant :=
  mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) U.rootConstant_nonneg)
    (Finset.prod_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (zero_le_one.trans (one_le_idealCountConstant F))
        (zero_le_one.trans (U.cutoffConstant_one j))) (U.atomConstant_nonneg j))

end ExceptionalAtomicScales

/-- A live prime-atom window is itself derived from the original
individual character coefficient and profile.  Its central square-root
scale supplies exactly the half-length saving. -/
theorem sourcePrimeTerm_norm_le_power_from_profile
    (C : A.GeneralArithmeticContext σ η hS)
    (χ θ : HeckeCharacter F) (M : Ideal (𝓞 F) →* ℂ)
    (g h' : A.R) (w : HeightOneSpectrum (𝓞 F) → ℂ)
    (Z length B exponent : ℝ) (hZ : 0 < Z)
    (p : HeightOneSpectrum (𝓞 F))
    (hcoefficient : ‖sourcePrimeCoefficient χ θ M p‖ ≤ 1)
    (hprofile : ‖w p‖ ≤ B * Z ^ (exponent + length / 2)) :
    ‖sourcePrimeTerm (σ := σ) χ θ M g h' w (Z ^ length) p‖ ≤ B * Z ^ exponent := by
  have h := sourcePrimeTerm_norm_le_profile C χ θ M g h' w (Z ^ length)
    (B * Z ^ (exponent + length / 2)) p hcoefficient hprofile
  have hsqrt : Real.sqrt (Z ^ length) = Z ^ (length / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hZ.le]
    congr 1
    ring
  apply h.trans_eq
  rw [hsqrt, Real.rpow_add hZ]
  have hden : Z ^ (length / 2) ≠ 0 := (Real.rpow_pos_of_pos hZ _).ne'
  field_simp [hden] <;> ring

namespace AllocatedExceptionalSource

variable {Ψ : Ideal (𝓞 F) →* ℂ} {W₁ W₂ : ℝ → ℂ} {g h' : A.R}
variable (s : AllocatedExceptionalSource (V := V) (σ := σ) Ψ W₁ W₂ g h' k)

/-- Every hypothesis concerns a literal individual coefficient, prime,
or numerical scale.  The same record works for the negative frequency
on the right, since the residue norm theorem is uniform in frequency. -/
structure AtomicControl (Z : ℝ) (U : ExceptionalAtomicScales s.allocation) : Prop where
  base_pos : 0 < s.Zslot
  plain₁ : ‖sourcePlainCoefficient s.characters.plain s.characters.plainTwist
    s.characters.mask (s.allocation.plainDivisor 0)‖ ≤ 1
  plain₂ : ‖sourcePlainCoefficient s.characters.plain s.characters.plainTwist
    s.characters.mask (s.allocation.plainDivisor (Fin.succ 0))‖ ≤ 1
  frozen_prime : ∀ i ∈ Finset.univ \ s.allocation.keep,
    ‖sourcePrimeCoefficient (s.characters.slot i) (s.characters.slotTwist i)
      s.characters.mask (s.allocation.witness.2 i)‖ ≤ 1
  frozen_annulus : ∀ i ∈ Finset.univ \ s.allocation.keep,
    (Ideal.absNorm (s.allocation.witness.2 i).asIdeal : ℝ) ≤
      U.annulus i * s.Zslot ^ s.length i
  frozen_profile : ∀ i ∈ Finset.univ \ s.allocation.keep,
    ‖s.w i (s.allocation.witness.2 i)‖ ^ 2 ≤ U.profileSquare i
  frozen_norm : Z ^ U.frozenExponent ≤ (Ideal.absNorm s.allocation.frozenIdeal : ℝ)
  rectangle_product : s.product ≤ U.rootConstant ^ 2 * Z ^ (2 * U.rootExponent)
  prime_norm : ∀ j, ∀ p ∈ s.allocation.childSlots j,
    (Ideal.absNorm p.asIdeal : ℝ) ≤ U.cutoffConstant j * Z ^ U.cutoffExponent j
  prime_atom : ∀ j, ∀ p ∈ s.allocation.childSlots j,
    ‖sourcePrimeTerm (σ := σ) ((s.characters.restrictSlots s.allocation.keep).slot j)
      ((s.characters.restrictSlots s.allocation.keep).slotTwist j)
      (s.characters.restrictSlots s.allocation.keep).mask g h'
      (s.w (SlotRestriction.index s.allocation.keep j))
      (s.Zslot ^ s.length (SlotRestriction.index s.allocation.keep j)) p‖ ≤
        U.atomConstant j * Z ^ U.atomExponent j

private theorem power_square (Z e : ℝ) (hZ : 0 < Z) :
    (Z ^ e) ^ (2 : ℕ) = Z ^ (2 * e) := by
  rw [pow_two, ← Real.rpow_add hZ]
  congr 1
  ring

/-- The raw normalization in the centered estimate is now a theorem
of the atom windows.  The cost of every actual frozen and retained
occurrence is displayed in the computed constant and exponent. -/
theorem rawMass_le_atomic_power
    (C : A.GeneralArithmeticContext σ η hS) (Z : ℝ) (hZ : 1 ≤ Z)
    (U : ExceptionalAtomicScales s.allocation) (H : s.AtomicControl Z U) :
    s.rawMass ≤ U.constant * Z ^ U.exponent := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hs := s.allocation.scalar_norm_sq_le_frozen_norm C s.characters g h'
    s.Zslot H.base_pos s.length s.w U.annulus U.profileSquare H.plain₁ H.plain₂
    H.frozen_prime H.frozen_annulus H.frozen_profile
    U.annulus_nonneg U.profileSquare_nonneg
  have hs' : ‖s.allocation.scalar (σ := σ) s.characters g h' s.Zslot s.length s.w‖ ^ 2 ≤
      U.frozenNumerator / Z ^ U.frozenExponent :=
    hs.trans (div_le_div_of_nonneg_left U.frozenNumerator_nonneg
      (Real.rpow_pos_of_pos hz _) H.frozen_norm)
  have hscalar : ‖s.allocation.scalar (σ := σ) s.characters g h' s.Zslot s.length s.w‖ ≤
      Real.sqrt U.frozenNumerator * Z ^ (-U.frozenExponent / 2) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt U.frozenNumerator_nonneg, power_square _ _ hz,
      show 2 * (-U.frozenExponent / 2) = -U.frozenExponent by ring,
      Real.rpow_neg hz.le]
    simpa only [div_eq_mul_inv] using hs'
  have hroot : Real.sqrt s.product ≤ U.rootConstant * Z ^ U.rootExponent := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg U.rootConstant_nonneg (Real.rpow_nonneg hz.le _), ?_⟩
    simpa only [mul_pow, power_square _ _ hz] using H.rectangle_product
  have hcutoff (j) : 1 ≤ U.cutoffConstant j * Z ^ U.cutoffExponent j := by
    have he : 1 ≤ Z ^ U.cutoffExponent j :=
      Real.one_le_rpow hZ (U.cutoffExponent_nonneg j)
    exact one_le_mul_of_one_le_of_one_le (U.cutoffConstant_one j) he
  have hmass := s.rawMass_le_prime_windows
    (Real.sqrt U.frozenNumerator * Z ^ (-U.frozenExponent / 2))
    (U.rootConstant * Z ^ U.rootExponent) (by positivity)
    (mul_nonneg U.rootConstant_nonneg (Real.rpow_nonneg hz.le _)) hscalar hroot
    (fun j => U.cutoffConstant j * Z ^ U.cutoffExponent j)
    (fun j => U.atomConstant j * Z ^ U.atomExponent j) hcutoff
    (fun j => mul_nonneg (U.atomConstant_nonneg j) (Real.rpow_nonneg hz.le _))
    H.prime_norm H.prime_atom
  apply hmass.trans_eq
  have hprod : (∏ j, (idealCountConstant F *
        (U.cutoffConstant j * Z ^ U.cutoffExponent j)) *
          (U.atomConstant j * Z ^ U.atomExponent j)) =
      (∏ j, (idealCountConstant F * U.cutoffConstant j) * U.atomConstant j) *
        Z ^ (∑ j, (U.cutoffExponent j + U.atomExponent j)) := by
    rw [Real.rpow_sum_of_pos hz]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    rw [Real.rpow_add hz]
    ring
  rw [hprod]
  unfold ExceptionalAtomicScales.constant ExceptionalAtomicScales.exponent
  rw [Real.rpow_add hz, Real.rpow_add hz]
  ring

end AllocatedExceptionalSource

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.AllocatedExceptionalSource.rawMass_le_atomic_power

