import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ActualCommonReflection
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ActualReflectionDensity
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.SourceProfileAnnulus
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ProfileOrderSchedule

/-!
# Uniform production of the actual ordinary reflection output

The requested child Euler order determines its normalization envelope,
the higher source Euler order, and the common scalar constant before
the moving profile budget, node, row, height, scale and cutoff. The
primitive row/remaining-ideal calibration proves the actual conductor
scales and deletion mass. The common scalar density is proved from
the genuine functional equation and Mellin estimates.

This module constructs the whole parent energy inequality, its finite
common kernel, exact mass, numerical child integrability and actual
normalized child profiles. No energy inequality or density bound is
an additional premise of this uniform theorem.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckeSkeleton.ThetaKernel
open HeckeSkeleton.HeckeConductorNorm HeckePort.Moments HeckePort.Moments.ReflectionMass
open HeckeSkeleton.Moments.UniformAmplify
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable [MeasurableSpace (ℕ × Bool)] [MeasurableSingletonClass (ℕ × Bool)]

/-- The chosen original plain profile, as its genuine common annular test. -/
def selectedPlainAnnularTest {d : MomentData K ω ψ} {L : ℕ} {A P lower upper : ℝ}
    (h : ModelProfileControl d L A P 0 lower upper 0) (first : Bool)
    (hlower : 0 < lower) (hinterval : lower ≤ upper) (u : NonzeroIdeal K) :
    SmoothAnnularTest :=
  sliceControlAnnularTest
    (f := (if first then d.plainTest₁ else d.plainTest₂).profile u 0)
    (by cases first with
        | false => exact modelProfileControl_plain₂ h u
        | true => exact modelProfileControl_plain₁ h u) hlower hinterval

theorem selectedPlainAnnularTest_seminorm
    {d : MomentData K ω ψ} {L : ℕ} {A P lower upper : ℝ}
    (h : ModelProfileControl d L A P 0 lower upper 0) (first : Bool)
    (hlower : 0 < lower) (hinterval : lower ≤ upper) (u : NonzeroIdeal K) :
    testSeminorm (selectedPlainAnnularTest h first hlower hinterval u).toFun L A ≤ P := by
  cases first with
  | false => simpa only [Real.rpow_zero, mul_one] using (modelProfileControl_plain₂ h u).2.2
  | true => simpa only [Real.rpow_zero, mul_one] using (modelProfileControl_plain₁ h u).2.2

/-- The actual reflection theorem with every analytic constant selected
before the full moving family. The only remaining premises are original
profile, arithmetic, character and numerical geometry facts. -/
theorem uniform_ordinaryReflection_output
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (omegaCharacter psiCharacter : HeckeCharacter K)
    {δ A upper ε : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 4) (hδA : δ ≤ A)
    (hupper : 0 < upper) (hε : 0 < ε) (childOrder cap : ℕ) :
    ∃ E0 : ℝ, ∃ hE0 : 1 ≤ E0, ∃ L : ℕ, childOrder ≤ L ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P lower : ℝ), 1 ≤ P → 0 < lower → lower ≤ 1 / 2 → 2 ≤ upper →
      ∀ (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
      (probe : ProbeData K S) (rows : RowCharacterInput K S probe)
      (d : MomentData K omegaCharacter psiCharacter)
      (a : RealParameters) (first : Bool) (extra : NonzeroIdeal K → NonzeroIdeal K)
      (U overhead loss : ℝ),
      1 < U → d.geometry.slotCount ≤ cap →
      ReflectionRowCalibration S probe rows (Node.ordinary d a) extra U →
      uniformReflectionConductorConstant S psiCharacter ≤ U ^ overhead →
      ε * (a.m + a.q + overhead) ≤ loss →
      (∀ u ∈ pairedRows d a U, ∀ I, d.commonMask u I =
        (completeIdealCommonMask K S u I && decide (IsCoprime I (extra u).val))) →
      (∀ u ∈ pairedRows d a U, ∀ t : ℝ,
        d.plainBackground * d.rowCharacter u ≠ heckeNormTwist K t) →
      ∀ (hprofiles : ModelProfileControl d L A P 0 lower upper 0)
      (hinterval : lower ≤ upper) (hPE : 1 ≤ P * E0) (cutoff : ℕ),
      let V := selectedPlainAnnularTest hprofiles first (by assumption) hinterval
      let weight := ordinaryReflectionEnvelope C (P ^ (cap + 3)) (U ^ loss)
      let child := (Node.ordinary d a).fixedLineReflectionChild first U (P * E0) hPE childOrder
      (Node.ordinary d a).normalizedEnergy U 0 ≤
        2 * rowRestorationEnergy true S (Node.ordinary d a) extra V
          (if first then d.plainTest₂ else d.plainTest₁) δ U
          (if first then a.n₁ else a.n₂) (if first then a.n₂ else a.n₁) cutoff +
        ∫ x, (child x).normalizedEnergy U 0 ∂reflectionCommonKernel volume weight cutoff ∧
      IsFiniteMeasure (reflectionCommonKernel volume weight cutoff) ∧
      Integrable (fun x => (child x).normalizedEnergy U 0)
        (reflectionCommonKernel volume weight cutoff) ∧
      (∀ x, ModelProfileControl (child x).data childOrder A 1 0 lower upper 0) ∧
      (reflectionCommonKernel volume weight cutoff).real Set.univ =
        8 * ((cutoff + 1 : ℕ) : ℝ) ^ 2 *
          (C * P ^ (cap + 3) * U ^ loss * ∫ t : ℝ, (1 + |t|) ^ (-(2 : ℝ))) ^ 2 := by
  obtain ⟨E0, hE0, hnormalize⟩ :=
    exists_normalizedOrdinaryPowerChild_budget_control (K := K)
      (omegaCharacter := omegaCharacter) (psiCharacter := psiCharacter) childOrder A
  obtain ⟨L, hL, C, hC, hdensity⟩ := normalizedMomentReflectionDensity_uniform
    hcomplex psiCharacter hδ hδA hupper hε hE0 childOrder cap
  refine ⟨E0, hE0, L, hL, C, hC, ?_⟩
  intro P lower hP hlower hlowerSmall hupperLarge S instS probe rows d a
    first extra U overhead loss hU hcount cal hfixed hloss hmask hcharacter hprofiles
    hinterval hPE cutoff
  dsimp only
  let V := selectedPlainAnnularTest hprofiles first hlower hinterval
  let weight := ordinaryReflectionEnvelope C (P ^ (cap + 3)) (U ^ loss)
  have hU0 : 0 < U := zero_lt_one.trans hU
  have hg := ordinaryReflectionEnvelope_data hC
    (pow_nonneg (zero_le_one.trans hP) (cap + 3)) (Real.rpow_nonneg hU0.le loss)
  have hdelete (u : NonzeroIdeal K) (hu : u ∈ pairedRows d a U) :
      (Ideal.absNorm (∏ Q ∈ rowRestorationDeletion S d extra u, Q) : ℝ) ^ ε ≤ U ^ loss := by
    have hm := (cal.scalar_bounds hU hfixed u hu).1
    calc
      _ ≤ (U ^ ((Node.ordinary d a).width + overhead)) ^ ε :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hm hε.le
      _ = U ^ (ε * (a.m + a.q + overhead)) := by
        rw [← Real.rpow_mul hU0.le]
        congr 1
        dsimp [Node.width, Node.ordinary]
        ring
      _ ≤ U ^ loss := Real.rpow_le_rpow_of_exponent_le hU.le hloss
  have hb (j : ℕ) (_hj : j ∈ Finset.range (cutoff + 1))
      (u : NonzeroIdeal K) (hu : u ∈ pairedRows d a U) (t : ℝ) :
      ‖actualReflectionDensity S d a first extra V U (P * E0) childOrder u j
        (actualReflectionSelectedLine d a first U u j) t‖ ≤ weight t := by
    have h := hdensity P hP (U ^ loss) (Real.rpow_nonneg hU0.le loss) d hcount u (V u)
      le_rfl (selectedPlainAnnularTest_seminorm hprofiles first hlower hinterval u)
      S extra (hdelete u hu) U (if first then a.n₁ else a.n₂) ((2 : ℝ) ^ j)
      hU0 (pow_pos (by norm_num : (0 : ℝ) < 2) j)
    simpa only [actualReflectionDensity, actualReflectionSelectedLine,
      reflectionFixedLine_choice] using h.1 t
  have he := pairedEnergy_reflection_commonKernel hcomplex S d a first extra V
    hδ hδsmall hU hPE (Real.rpow_pos_of_pos hU0
      (a.m + a.q - (if first then a.n₁ else a.n₂) + overhead)) childOrder cutoff
    hmask hcharacter (fun _ _ => rfl)
    (fun u hu => (cal.scalar_bounds hU hfixed u hu).2 (if first then a.n₁ else a.n₂))
    weight hg.1 hg.2.1 hg.2.2.1 hb
  refine ⟨he, reflectionCommonKernel_finite volume weight cutoff hg.2.1 hg.2.2.1,
    Node.fixedLineReflectionChild_integrable (Node.ordinary d a) first U (P * E0) hU0 hPE
      childOrder cutoff weight hg.2.1 hg.2.2.1, ?_, ?_⟩
  · intro x
    have hp := modelProfileControl_mono_order hprofiles hL
    exact hnormalize P hP d first (reflectionFixedLine x.1.2) (-x.2) lower upper
      hp hlowerSmall hupperLarge (reflectionFixedLine_bounds x.1.2)
  · rw [reflectionCommonKernel_mass volume weight cutoff hg.1 hg.2.1 hg.2.2.1, hg.2.2.2]

end HeckeSkeleton.Moments.EngineInduction
