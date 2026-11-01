import HeckeSkeleton.LowEnergy.CommonMellinTail
import HeckeSkeleton.ThetaKernel.Core

/-!
# Actual common physical profile on both Mellin lines

The line 2 gives the genuine large-argument decay needed to sum every dual
dyad.  The seminorm order is chosen explicitly from the number of complex
places; all constants still precede the test, sector, class and scale.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.ActualCommonMellinTail
open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.Characters
open HeckeSkeleton.ThetaKernel
open HeckeSkeleton.LowEnergy.CommonMellinTail
open HeckeSkeleton.LowEnergy.CommonMellin (physicalArgument physicalArgument_pos)
open scoped BigOperators Topology NumberField

variable {K : Type} [Field K] [NumberField K]
variable {S : Set (HeightOneSpectrum (𝓞 K))} [Fintype S]
variable {F : FiniteMellinData K S}

/-- Two powers of integrable decay beyond the multiplier growth. -/
def order (K : Type) [Field K] [NumberField K] (p : ℕ) : ℕ :=
  p + Nat.ceil (8 * ncx K) + 2

def amplitude (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S)
    (V : SmoothAnnularTest) (Y t : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ *
    (mellin V.toFun (-vertical Y t) * reflectionMultiplier K S F θ u κ (vertical Y t))

def profile (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S)
    (V : SmoothAnnularTest) (Y t : ℝ) : ℂ :=
  density (amplitude F θ u κ V Y) Y t

theorem amplitude_eq_fz (θ : HeckeCharacter K)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S)
    (V : SmoothAnnularTest) (Y t : ℝ) :
    amplitude F θ u κ V Y t =
      (2 * (Real.pi : ℂ))⁻¹ * fz F θ u κ V 0 1 (vertical Y t) := by
  simp [amplitude, fz]

/-- The physically rescaled marked row has one active-mark denominator.
This applies after `physical_argument_cancel_mark` and normalization of dyads. -/
theorem kernel_physical_separation (θ : HeckeCharacter K)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S)
    (V : SmoothAnnularTest) {Y d P n b : ℝ}
    (hY : 0 < Y) (hd : 0 < d) (hP : 0 < P) (hn : 0 < n) (hb : 0 < b) :
    mellinReflectionKernel K S F θ u κ V.toFun (line Y) (physicalArgument Y d P n b) =
      (scalar Y : ℂ) * ∫ t : ℝ,
        profile F θ u κ V Y t * rowFactor Y d t * markFactor Y P t * columnFactor Y n b t := by
  unfold mellinReflectionKernel
  rw [← integral_const_mul]
  have heq : (fun t : ℝ => (2 * (Real.pi : ℂ))⁻¹ *
      kernelIntegrand K S F θ u κ V.toFun (line Y) (physicalArgument Y d P n b) t) =
      (fun t : ℝ => amplitude F θ u κ V Y t *
        ((physicalArgument Y d P n b : ℝ) : ℂ) ^ (-vertical Y t)) := by
    funext t
    simp only [amplitude, kernelIntegrand, vertical]
    ring
  rw [heq]
  exact integral_physical_separation (amplitude F θ u κ V Y) hY hd hP hn hb

/-- Literal sigma-zero physical kernel.  All surviving marks stay inside the
row sum, and their scale dependence is exactly the mark-only factor `P^w`. -/
theorem kernel_physical_separation_at_zero
    (θ : HeckeCharacter K) (hK : MellinKernelInput K S F θ)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S)
    (V : SmoothAnnularTest) {Y d P n b : ℝ}
    (hY : 0 < Y) (hd : 0 < d) (hP : 0 < P) (hn : 0 < n) (hb : 0 < b) :
    mellinReflectionKernel K S F θ u κ V.toFun 0 (physicalArgument Y d P n b) =
      (scalar Y : ℂ) * ∫ t : ℝ,
        profile F θ u κ V Y t * rowFactor Y d t * markFactor Y P t * columnFactor Y n b t := by
  rw [hK.line_independent V u κ 0 (line Y) (physicalArgument Y d P n b)
    (by norm_num) (by linarith [(line_bounds Y).1]) (physicalArgument_pos hY hd hP hn hb)]
  exact kernel_physical_separation θ u κ V hY hd hP hn hb

/-- The amplitude is continuous on the line selected for the whole block. -/
theorem continuous_amplitude (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S)
    (V : SmoothAnnularTest) (Y : ℝ) :
    Continuous (amplitude F θ u κ V Y) := by
  have hσ : -(1 / 3 : ℝ) < line Y := by linarith [(line_bounds Y).1]
  have h := (continuous_fz_line hF θ u κ V 0 (by norm_num : (0 : ℝ) < 1) hσ).const_mul
    ((2 * (Real.pi : ℂ))⁻¹)
  have heq : amplitude F θ u κ V Y =
      (fun t : ℝ => (2 * (Real.pi : ℂ))⁻¹ * fz F θ u κ V 0 1 (vertical Y t)) :=
    funext (fun t => amplitude_eq_fz (F := F) θ u κ V Y t)
  rw [heq]
  simpa only [vertical] using h

/-- Pointwise decay with a fixed seminorm.  The scale `Y` is absent from the
constant and from the majorant. -/
theorem amplitude_uniform_decay
    (hF : FiniteMellinAdmissible K S F) (hU : StripUniform hF)
    (θ : HeckeCharacter K) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : SmoothAnnularTest)
      (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (Y t : ℝ),
      ‖amplitude F θ u κ V Y t‖ ≤
        C * testSeminorm V.toFun (order K p) 2 * (1 + |t|) ^ (-((p : ℝ) + 2)) := by
  obtain ⟨CM, hCM, hM⟩ := reflectionMultiplier_bound hF hU θ
    (σlo := -(1 / 4 : ℝ)) (Λ := 2) (by norm_num) (by norm_num)
  let cπ : ℝ := ‖(2 * (Real.pi : ℂ))⁻¹‖
  refine ⟨cπ * CM * 2 ^ (order K p) * 2, by dsimp [cπ]; positivity, ?_⟩
  intro V u κ Y t
  have hline := line_bounds Y
  have hM' : ∀ s : ℂ, -(1 / 4 : ℝ) ≤ s.re → s.re ≤ 2 →
      ‖reflectionMultiplier K S F θ u κ s‖ ≤ CM * (1 + |s.im|) ^ (4 * ncx K * s.re) := by
    intro s hs0 hs1
    simpa only [ncx] using hM u κ s hs0 hs1
  have h := fz_pointwise_bound (F := F) θ u κ V hCM hM'
    (h := 0) (J := order K p) (by omega) (by norm_num : (0 : ℝ) < 1)
    hline.1 hline.2 t
  have hI (j : ℕ) (hj : j ≤ order K p) :
      Iint V j (line Y) ≤ testSeminorm V.toFun (order K p) 2 := by
    unfold line
    split_ifs
    · simpa only [neg_div] using Iint_left_le V j (order K p) hj 2
    · exact Iint_right_le V j (order K p) hj 2
  have hIsum : Iint V 0 (line Y) + Iint V (order K p) (line Y) ≤
      2 * testSeminorm V.toFun (order K p) 2 := by
    linarith [hI 0 (by omega), hI (order K p) le_rfl]
  have hsemi : 0 ≤ testSeminorm V.toFun (order K p) 2 :=
    (Iint_nonneg V 0 (line Y)).trans (hI 0 (by omega))
  have he : 4 * ncx K * line Y + (0 : ℝ) - (order K p : ℕ) ≤ -((p : ℝ) + 2) := by
    have hncx := ncx_nonneg (K := K)
    have hm := mul_le_mul_of_nonneg_left hline.2
      (show 0 ≤ 4 * ncx K by positivity)
    have hJ : (p : ℝ) + 8 * ncx K + 2 ≤ (order K p : ℝ) := by
      have hc := Nat.le_ceil (8 * ncx K)
      dsimp [order]
      push_cast
      linarith
    linarith
  have hpow : (1 + |t|) ^ (4 * ncx K * line Y + (0 : ℝ) - (order K p : ℕ)) ≤
      (1 + |t|) ^ (-((p : ℝ) + 2)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) he
  have hfz : ‖fz F θ u κ V 0 1 (vertical Y t)‖ ≤
      CM * (2 ^ (order K p) * (2 * testSeminorm V.toFun (order K p) 2)) *
        (1 + |t|) ^ (-((p : ℝ) + 2)) := by
    have h' : ‖fz F θ u κ V 0 1 (vertical Y t)‖ ≤
        CM * (2 ^ (order K p) * (Iint V 0 (line Y) + Iint V (order K p) (line Y))) *
          (1 + |t|) ^ (4 * ncx K * line Y + (0 : ℝ) - (order K p : ℕ)) := by
      simpa only [Real.one_rpow, mul_one, vertical, Nat.cast_zero] using h
    refine h'.trans ?_
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hIsum (by positivity)) hCM)
      hpow (by positivity) (by positivity)
  rw [amplitude_eq_fz, norm_mul]
  calc
    _ ≤ cπ * (CM * (2 ^ (order K p) * (2 * testSeminorm V.toFun (order K p) 2)) *
        (1 + |t|) ^ (-((p : ℝ) + 2))) :=
      mul_le_mul_of_nonneg_left hfz (norm_nonneg _)
    _ = _ := by ring

/-- Uniform weighted L1 norm of the actual common profile.  The quantifier
order keeps every row and marked coefficient independent of the profile. -/
theorem profile_uniform_weighted_L1
    (hF : FiniteMellinAdmissible K S F) (hU : StripUniform hF)
    (θ : HeckeCharacter K) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : SmoothAnnularTest)
      (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (Y : ℝ), 0 < Y →
      Integrable (fun t : ℝ => (1 + |t|) ^ p * ‖profile F θ u κ V Y t‖) ∧
      (∫ t : ℝ, (1 + |t|) ^ p * ‖profile F θ u κ V Y t‖) ≤
        C * testSeminorm V.toFun (order K p) 2 := by
  obtain ⟨C, hC, hbound⟩ := amplitude_uniform_decay hF hU θ p
  let L : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-(2 : ℝ))
  have hL : 0 ≤ L := integral_nonneg (fun t => by positivity)
  refine ⟨C * L, mul_nonneg hC hL, ?_⟩
  intro V u κ Y hY
  have hsemi : 0 ≤ testSeminorm V.toFun (order K p) 2 :=
    (Iint_nonneg V 0 2).trans (Iint_right_le V 0 (order K p) (by omega) 2)
  obtain ⟨hint, hle⟩ := weighted_density_integrable_and_bound
    (amplitude F θ u κ V Y) (continuous_amplitude hF θ u κ V Y) hY
    (mul_nonneg hC hsemi) p (fun t => hbound V u κ Y t)
  refine ⟨hint, hle.trans_eq ?_⟩
  change C * testSeminorm V.toFun (order K p) 2 * L = C * L * testSeminorm V.toFun (order K p) 2
  ring

/-- In the actual target context, the sixth local class group is finite.
Thus no additional uniform-strip hypothesis is needed by this specialization. -/
theorem profile_uniform_weighted_L1_of_finite
    [Finite (SixthLocalClasses K S)]
    (hF : FiniteMellinAdmissible K S F) (θ : HeckeCharacter K) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : SmoothAnnularTest)
      (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (Y : ℝ), 0 < Y →
      Integrable (fun t : ℝ => (1 + |t|) ^ p * ‖profile F θ u κ V Y t‖) ∧
      (∫ t : ℝ, (1 + |t|) ^ p * ‖profile F θ u κ V Y t‖) ≤
        C * testSeminorm V.toFun (order K p) 2 :=
  profile_uniform_weighted_L1 hF (stripUniform_of_finite hF) θ p

#print axioms kernel_physical_separation_at_zero
#print axioms amplitude_uniform_decay
#print axioms profile_uniform_weighted_L1
#print axioms profile_uniform_weighted_L1_of_finite

end HeckeSkeleton.LowEnergy.ActualCommonMellinTail
