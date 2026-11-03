import HeckeGeneral.Analysis.ActualSIntegerScaleDerivative
import Mathlib.Analysis.Calculus.TangentCone.Real

/-! Concrete support and Mellin derivative lemmas for the six Sobolev tests.
The per-target moment input below permits S/arithmetic data to be chosen
for that target; no one S is required to cover a whole conductor packet.
No analytic moment or scale-supremum estimate is proved here. -/

noncomputable section

namespace HeckeGeneral.Analysis.ActualSIntegerMoments

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis.SquarefreeAmplification
open scoped BigOperators Classical Topology

@[simp] theorem mellinLogTest_zero_index (s : ℂ) :
    mellinLogTest 0 s = dyadicMellinWeight s := by
  funext y
  simp [mellinLogTest]

theorem mellinLogTest_zero_of_ge (m : ℕ) (s : ℂ) {y : ℝ} (hy : 2 ≤ y) :
    mellinLogTest m s y = 0 := by
  simp [mellinLogTest, dyadicMellinWeight_zero_of_ge s hy]

theorem differentiableAt_mellinLogTest (m : ℕ) (s : ℂ) {y : ℝ} (hy : 0 < y) :
    DifferentiableAt ℝ (mellinLogTest m s) y := by
  have hl : DifferentiableAt ℝ (fun x : ℝ => -(Real.log x : ℂ)) y :=
    (Real.hasDerivAt_log hy.ne').ofReal_comp.neg.differentiableAt
  exact (hl.pow m).mul (differentiableAt_dyadicMellinWeight s hy)

/-- Vanishing of the derivative includes the smooth support boundary y=2. -/
theorem deriv_mellinLogTest_zero_of_ge (m : ℕ) (s : ℂ) {y : ℝ} (hy : 2 ≤ y) :
    deriv (mellinLogTest m s) y = 0 := by
  have hwithin : HasDerivWithinAt (mellinLogTest m s) 0 (Set.Ici y) y :=
    (hasDerivWithinAt_const y (Set.Ici y) (0 : ℂ)).congr
      (fun z hz => mellinLogTest_zero_of_ge m s (hy.trans hz))
      (mellinLogTest_zero_of_ge m s hy)
  exact (uniqueDiffWithinAt_Ici y).eq_deriv (Set.Ici y)
    (differentiableAt_mellinLogTest m s (by linarith)).hasDerivAt.hasDerivWithinAt hwithin

theorem scaleSobolevTest_zero_of_ge (i : Fin 2) (m : Fin 3) (s : ℂ)
    {y : ℝ} (hy : 2 ≤ y) : scaleSobolevTest i m s y = 0 := by
  unfold scaleSobolevTest
  split_ifs
  · exact mellinLogTest_zero_of_ge m.val s hy
  · simp only [scaleEulerTest, mellinLogTest_zero_of_ge m.val s hy,
      deriv_mellinLogTest_zero_of_ge m.val s hy, mul_zero, sub_self]

/-- Differentiation of the actual W_s with respect to complex s inserts -log y. -/
theorem hasDerivAt_dyadicMellinWeight_parameter (s : ℂ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun z : ℂ => dyadicMellinWeight z y) (mellinLogTest 1 s y) s := by
  have h := ((hasDerivAt_id s).neg.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).const_mul (sexticDyadicWeight y)
  convert h using 1
  · rfl
  · simp only [mellinLogTest, dyadicMellinWeight, pow_one,
      ← Complex.ofReal_log hy.le, Pi.neg_apply, id_eq]
    ring

theorem hasDerivAt_mellinLogTest_parameter (m : ℕ) (s : ℂ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun z : ℂ => mellinLogTest m z y) (mellinLogTest (m + 1) s y) s := by
  convert (hasDerivAt_dyadicMellinWeight_parameter s hy).const_mul
    ((-(Real.log y : ℂ)) ^ m) using 1
  · rfl
  · simp only [mellinLogTest, pow_succ]
    ring

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)

/-- Any test vanishing above 2 has the same actual finite sum in every
larger common envelope. This applies to the derived Sobolev tests too. -/
theorem sIntegerInversePolynomial_eq_largerEnvelope
    (η : HeckeCharacter K) (u : S.integer K) (W : ℝ → ℂ)
    (hW : ∀ y : ℝ, 2 ≤ y → W y = 0) {D R : ℝ} (hD : 0 < D) (hDR : D ≤ R) :
    sIntegerSexticInverseIdealPolynomial K S ζ hζ σ η
        (dyadicIdealSupport K D) u D W =
      sIntegerSexticInverseIdealPolynomial K S ζ hζ σ η
        (dyadicIdealSupport K R) u D W := by
  unfold sIntegerSexticInverseIdealPolynomial
  congr 1
  apply Finset.sum_subset
  · intro I hI
    exact (mem_dyadicIdealSupport_iff K (hD.le.trans hDR) I).mpr
      (((mem_dyadicIdealSupport_iff K hD.le I).mp hI).trans (by linarith))
  · intro I _ hI
    have hn : 2 * D < idealNorm K I :=
      lt_of_not_ge (fun h => hI ((mem_dyadicIdealSupport_iff K hD.le I).mpr h))
    have hy : 2 ≤ idealNorm K I / D := (le_div_iff₀ hD).mpr (by linarith)
    simp [sIntegerSexticInverseIdealTerm, hW _ hy]

/-- The log derivative now uses the standard actual support F(D), exactly
the Euler-test polynomial occurring in the finite-test moment input. -/
theorem hasDerivAt_actualSIntegerInversePolynomial_exp_euler
    (η : HeckeCharacter K) (q : ActualSIntegerOrbit K S) (s : ℂ) (t : ℝ) :
    HasDerivAt
      (fun x : ℝ => actualSIntegerInversePolynomial K S ζ hζ σ η q (Real.exp x) s)
      (sIntegerSexticInverseIdealPolynomial K S ζ hζ σ η
        (dyadicIdealSupport K (Real.exp t)) q.out.val (Real.exp t)
        (scaleEulerTest (dyadicMellinWeight s))) t := by
  convert hasDerivAt_actualSIntegerInversePolynomial_exp K S ζ hζ σ η q s t using 1
  rw [actualFiniteInverseLogPolynomial_eq]
  apply sIntegerInversePolynomial_eq_largerEnvelope
  · intro y hy
    have hz := scaleSobolevTest_zero_of_ge (1 : Fin 2) (0 : Fin 3) s hy
    simpa [scaleSobolevTest] using hz
  · exact Real.exp_pos t
  · linarith [Real.exp_pos t]

/-- Targetwise form of the uniform six-test moment. S and the arithmetic
data may be selected for this eta; real margins/losses remain explicit.
This is a source-calibration INPUT, not a proved analytic bound. -/
def ActualTargetZeroSlotSobolevMomentInput (η : HeckeCharacter K) : Prop :=
  ∀ δ ε : ℝ, 0 < δ → δ < 1 → 0 < ε →
    ∀ T : Set ℂ, IsCompact T →
      ∃ C H₀ : ℝ, 0 < C ∧ 1 ≤ H₀ ∧
        ∀ H : ℝ, H₀ ≤ H → ∀ D : ℝ, 0 < D → D ≤ H ^ (1 - δ) →
          ∀ s ∈ T, ∀ i : Fin 2, ∀ m : Fin 3,
            (∑ q : ActualBoundedSIntegerOrbits K S H,
              ‖sIntegerSexticInverseIdealPolynomial K S ζ hζ σ η
                (dyadicIdealSupport K D) q.val.out.val D
                (scaleSobolevTest i m s)‖ ^ 2) ≤ C * H ^ (1 + ε)

theorem ActualZeroSlotSobolevMomentInput.target
    (ω η : HeckeCharacter K) (hη : η ∈ HeckePacket K ω)
    (h : ActualZeroSlotSobolevMomentInput K S ζ hζ σ ω) :
    ActualTargetZeroSlotSobolevMomentInput K S ζ hζ σ η := by
  intro δ ε hδ hδ1 hε T hT
  exact h δ ε hδ hδ1 hε T hT η hη

end HeckeGeneral.Analysis.ActualSIntegerMoments
