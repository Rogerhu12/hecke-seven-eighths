import HeckeSkeleton.LowEnergy.GeneralHeight
import HeckeSkeleton.ThetaKernel

/-!
# Uniform polynomial background height on any positive kernel line

The contour, gamma factors and seminorm estimates are the original
kernel proof.  The gamma constant is selected before the finite-order
child and norm twist.  This makes the height dependence in arbitrary
power tails explicit as well as in the two energy lines.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.GeneralHeightTail

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.Characters
open HeckeSkeleton.ThetaKernel HeckeSkeleton.LowEnergy.GeneralHeight
open scoped Classical BigOperators NumberField

variable {K : Type} [Field K] [NumberField K]
variable {S : Set (HeightOneSpectrum (𝓞 K))} [Fintype S]
variable {F : FiniteMellinData K S}

theorem kernel_fixedAngular_decay [Finite (SixthLocalClasses K S)]
    (hF : FiniteMellinAdmissible K S F) (θ₀ : HeckeCharacter K)
    (A : ℝ) (J : ℕ) (hA : 0 ≤ A) (hJ : 4 * ncx K * A + 1 < J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (θ : HeckeCharacter K),
      (∀ v, archShift K θ v = archShift K θ₀ v) →
      ∀ (V : SmoothAnnularTest) (u : SixthUnitClasses K S)
        (κ : SixthLocalClasses K S) (y : ℝ), 0 < y →
      ‖mellinReflectionKernel K S F θ u κ V.toFun 0 y‖ ≤
        C * radialHeight K θ ^ (8 * ncx K * A) *
          testSeminorm V.toFun J A * y ^ (-A) := by
  obtain ⟨CM, hCM, hM⟩ := reflectionMultiplier_fixedAngular_bound hF
    (stripUniform_of_finite hF) θ₀ (σlo := A) (Λ := A) (by linarith) le_rfl
  let e := (J : ℝ) - 4 * ncx K * A
  have he : 1 < e := by dsimp [e]; linarith
  let L := ∫ t : ℝ, (1 + |t|) ^ (-e)
  have hL : 0 ≤ L := integral_nonneg (fun t => by positivity)
  refine ⟨(2 * Real.pi)⁻¹ * CM * 2 ^ J * 2 * L, by positivity, ?_⟩
  intro θ hang V u κ y hy
  have hM' : ∀ s : ℂ, A ≤ s.re → s.re ≤ A →
      ‖reflectionMultiplier K S F θ u κ s‖ ≤
        (CM * radialHeight K θ ^ (8 * ncx K * A)) *
          (1 + |s.im|) ^ (4 * ncx K * s.re) := by
    intro s hs0 hs1
    have h := hM θ hang u κ s hs0 hs1
    have heq : 4 * ncx K * (|A| + |A|) = 8 * ncx K * A := by
      rw [abs_of_nonneg hA]
      ring
    simpa only [heq] using h
  have hb := Gc_norm_le θ u κ V (σ := A) (h := 0) (J := J)
    (show 0 ≤ CM * radialHeight K θ ^ (8 * ncx K * A) by positivity)
    hM' (Nat.zero_le J) he (by dsimp [e]; norm_num; linarith) hy
  have hI : Iint V 0 A + Iint V J A ≤ 2 * testSeminorm V.toFun J A := by
    linarith [Iint_right_le V 0 J (Nat.zero_le _) A, Iint_right_le V J J le_rfl A]
  have hline : mellinReflectionKernel K S F θ u κ V.toFun 0 y = Gc F θ u κ V 0 A y := by
    rw [mellinReflectionKernel_eq_Gc]
    unfold Gc
    rw [fz_shift hF θ u κ V 0 hy (a := 0) (b := A) (by norm_num) (by linarith)]
  rw [hline]
  apply hb.trans
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hI (by positivity))
          (by positivity : 0 ≤ CM * radialHeight K θ ^ (8 * ncx K * A)))
        (by positivity : 0 ≤ y ^ (-A)))
      (by positivity : 0 ≤ (2 * Real.pi)⁻¹)) hL
  apply h.trans_eq
  dsimp [L]
  ring

/-- Constants precede every finite-order child and norm height. -/
theorem kernel_child_decay [Finite (SixthLocalClasses K S)]
    (hF : FiniteMellinAdmissible K S F) (θ₀ : HeckeCharacter K)
    (A : ℝ) (J : ℕ) (hA : 0 ≤ A) (hJ : 4 * ncx K * A + 1 < J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν : HeckeCharacter K), FiniteOrder ν →
      ∀ (t : ℝ) (V : SmoothAnnularTest) (u : SixthUnitClasses K S)
        (κ : SixthLocalClasses K S) (y : ℝ), 0 < y →
      ‖mellinReflectionKernel K S F (ν * θ₀ * heckeNormTwist K t) u κ V.toFun 0 y‖ ≤
        C * (1 + |t|) ^ (8 * ncx K * A) * testSeminorm V.toFun J A * y ^ (-A) := by
  obtain ⟨C, hC, hb⟩ := kernel_fixedAngular_decay hF θ₀ A J hA hJ
  have hbase : 0 ≤ radialHeight K θ₀ + ncx K := by
    have hH := radialHeight_ge_one K θ₀
    have hn := ncx_nonneg (K := K)
    linarith
  have hexp : 0 ≤ 8 * ncx K * A :=
    mul_nonneg (mul_nonneg (by norm_num) (ncx_nonneg (K := K))) hA
  refine ⟨C * (radialHeight K θ₀ + ncx K) ^ (8 * ncx K * A), by positivity, ?_⟩
  intro ν hν t V u κ y hy
  have h := hb (ν * θ₀ * heckeNormTwist K t) (archShift_child θ₀ ν hν t) V u κ y hy
  have hsemi : 0 ≤ testSeminorm V.toFun J A :=
    (Iint_nonneg V 0 A).trans (Iint_right_le V 0 J (Nat.zero_le _) A)
  have hp := Real.rpow_le_rpow (zero_le_one.trans (radialHeight_ge_one K _))
    (radialHeight_child_le θ₀ ν hν t) hexp
  rw [Real.mul_rpow hbase (by positivity)] at hp
  apply h.trans
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC) hsemi)
    (by positivity : 0 ≤ y ^ (-A))).trans_eq (by ring)

#print axioms kernel_fixedAngular_decay
#print axioms kernel_child_decay

end HeckeSkeleton.LowEnergy.GeneralHeightTail
