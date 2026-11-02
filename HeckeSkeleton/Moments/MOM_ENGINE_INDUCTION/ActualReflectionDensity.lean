import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ReflectionProfileBudget
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RestorationRows

/-!
# One reflection-density budget for the actual recursive moment family

The three backgrounds permitted by MomentData are combined before any
node, row, profile budget or physical scale is selected.  Actual finite
row characters, actual conductor scales and the actual pruned remaining
deletion set then instantiate the analytic density theorem directly.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open HeckeSkeleton.Moments.UniformAmplify HeckePort.Moments
open HeckeSkeleton.ExplicitHeckeFunctionalEquation HeckeSkeleton.HeckeConductorNorm
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K]

/-- The common Euler order and constant precede the moving profile budget
P, every actual node and row, all remaining ideals, and all positive
physical scales.  The density uses exactly the coefficients and conductor
appearing in the literal row identity, with the chosen one of two lines. -/
theorem normalizedMomentReflectionDensity_uniform
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) (psiCharacter : HeckeCharacter K)
    {δ A B ε E0 : ℝ} (hδ : 0 < δ) (hδA : δ ≤ A)
    (hB : 0 < B) (hε : 0 < ε) (hE0 : 1 ≤ E0) (J cap : ℕ) :
    ∃ L : ℕ, J ≤ L ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P : ℝ), 1 ≤ P → ∀ (deletionBound : ℝ), 0 ≤ deletionBound →
      ∀ {omegaCharacter : HeckeCharacter K} (d : MomentData K omegaCharacter psiCharacter),
      d.geometry.slotCount ≤ cap → ∀ (u : NonzeroIdeal K) (V : SmoothAnnularTest),
      V.upper ≤ B → testSeminorm V.toFun L A ≤ P →
      ∀ (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
      (extra : NonzeroIdeal K → NonzeroIdeal K),
      (Ideal.absNorm (∏ Q ∈ rowRestorationDeletion S d extra u, Q) : ℝ) ^ ε ≤ deletionBound →
      ∀ (U long N : ℝ), 0 < U → 0 < N →
      let χ := d.plainBackground * d.rowCharacter u
      let b := idealCoefficient (primeCoefficient K χ)
      let bi := idealCoefficient (primeCoefficient K χ⁻¹)
      let E := rowRestorationDeletion S d extra u
      let Q := heckeConductorScale K χ
      let density := normalizedOrdinaryReflectionDensity K (P * E0) J d.geometry.slotCount
        χ V b bi E Q (U ^ long) N (ordinaryReflectionLine (N * U ^ long / Q))
      (∀ t, ‖density t‖ ≤ ordinaryReflectionEnvelope C (P ^ (cap + 3)) deletionBound t) ∧
      Integrable density ∧
      (∫ t : ℝ, ‖density t‖) ≤
        C * P ^ (cap + 3) * deletionBound * ∫ t : ℝ, (1 + |t|) ^ (-(2 : ℝ)) := by
  let backgrounds : Fin 3 → HeckeCharacter K :=
    fun i => if i = 0 then 1 else if i = 1 then psiCharacter else psiCharacter⁻¹
  choose order horder constant hconstant hbound using
    (fun i : Fin 3 => normalizedOrdinaryReflectionDensity_budget_uniform
      K hcomplex (backgrounds i) hδ hδA hB hε hE0 J cap)
  let L : ℕ := ∑ i : Fin 3, order i
  let C : ℝ := ∑ i : Fin 3, constant i
  have hL (i : Fin 3) : order i ≤ L :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => hconstant i)
  have hCi (i : Fin 3) : constant i ≤ C :=
    Finset.single_le_sum (fun k _ => hconstant k) (Finset.mem_univ i)
  refine ⟨L, (horder 0).trans (hL 0), C, hC, ?_⟩
  intro P hP deletionBound hdeletion omegaCharacter d hcap u V hupper hV
    S instS extra hdeleted U long N hU hN
  dsimp only
  let χ := d.plainBackground * d.rowCharacter u
  let b := idealCoefficient (primeCoefficient K χ)
  let bi := idealCoefficient (primeCoefficient K χ⁻¹)
  let E := rowRestorationDeletion S d extra u
  let Q := heckeConductorScale K χ
  let density := normalizedOrdinaryReflectionDensity K (P * E0) J d.geometry.slotCount
    χ V b bi E Q (U ^ long) N (ordinaryReflectionLine (N * U ^ long / Q))
  have ha : IdealCoeff b := heckeIdealCoeff_for_deletion χ
  have hai : IdealCoeff bi := heckeIdealCoeff_for_deletion χ⁻¹
  have hQ : 0 < Q := conductorScale_pos K χ
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hnode (i : Fin 3) (hbackground : d.plainBackground = backgrounds i) :
      (∀ t, ‖density t‖ ≤ ordinaryReflectionEnvelope C (P ^ (cap + 3)) deletionBound t) ∧
      Integrable density ∧
      (∫ t : ℝ, ‖density t‖) ≤
        C * P ^ (cap + 3) * deletionBound * ∫ t : ℝ, (1 + |t|) ^ (-(2 : ℝ)) := by
    have hprofile := (testSeminorm_mono_order V.toFun A (hL i)).trans hV
    have hb := hbound i P hP deletionBound hdeletion (d.rowCharacter u)
      (d.rowCharacter_finite u) V hupper hprofile b bi ha hai E
      (rowRestorationDeletion_prime S d extra u) hdeleted d.geometry.slotCount hcap
      Q (U ^ long) N hQ (Real.rpow_pos_of_pos hU long) hN
    rw [← hbackground] at hb
    have hint : Integrable density := hb.2.1
    have hpoint (t : ℝ) :
        ‖density t‖ ≤ ordinaryReflectionEnvelope C (P ^ (cap + 3)) deletionBound t := by
      apply (hb.1 t).trans
      unfold ordinaryReflectionEnvelope
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hCi i) (pow_nonneg hP0 _)) hdeletion)
        (Real.rpow_nonneg (by positivity) _)
    refine ⟨hpoint, hint, ?_⟩
    have hg := ordinaryReflectionEnvelope_data hC (pow_nonneg hP0 (cap + 3)) hdeletion
    rw [← hg.2.2.2]
    exact integral_mono hint.norm hg.2.2.1 hpoint
  rcases d.plain_background_spec with h | h | h
  · exact hnode 0 (by simpa only [backgrounds, if_pos rfl] using h)
  · exact hnode 1 (by simpa [backgrounds] using h)
  · exact hnode 2 (by simpa [backgrounds] using h)

end HeckeSkeleton.Moments.EngineInduction
