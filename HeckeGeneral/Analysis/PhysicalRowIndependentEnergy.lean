import HeckeGeneral.Analysis.FrequencyRowOrbit
import HeckeGeneral.Analysis.ActualIndependentOrbitEnergy

/-! The independent-scale estimate on actual physical frequency rows.
The row-to-orbit embedding and its norm identity are proved; the literal
finite polynomial keeps the existing fixed-S/6 and base-row zero masks.
The only analytic input is the named targetwise scale-supremum moment. -/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (P : ProbeData K (S : Set (HeightOneSpectrum (𝓞 K))))

theorem physicalRow_independentEnergy
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (T : Set ℂ) (hT : IsCompact T)
    (χ : HeckeCharacter K)
    (hMI : ActualTargetZeroSlotScaleSupInput K (S : Set (HeightOneSpectrum (𝓞 K)))
      P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ U D : ℝ, 1 ≤ U → 1 ≤ D →
      ∀ R : Finset (FrequencyRow K (S : Set (HeightOneSpectrum (𝓞 K)))),
        (∀ u ∈ R, frequencyRowNorm K (S : Set (HeightOneSpectrum (𝓞 K))) u ≤ U) →
        ∀ s ∈ T,
          (∑ u ∈ R,
            ‖sIntegerSexticInverseIdealPolynomial K (S : Set (HeightOneSpectrum (𝓞 K)))
              P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding χ
              (dyadicIdealSupport K D)
              (frequencyRowElement K (S : Set (HeightOneSpectrum (𝓞 K))) P u)
              D (dyadicMellinWeight s)‖ ^ 2) ≤
            C * max U (U ^ (1 / 6 : ℝ) * D ^ (5 * (1 + c) / 6)) * (U * D) ^ ε := by
  obtain ⟨C, hC, henergy⟩ := actualTargetScaleSup_independentOrbitEnergy K S P.arithmetic
    hc hε T hT χ hMI
  refine ⟨C, hC, ?_⟩
  intro U D hU hD R hR s hs
  let e := frequencyRowOrbitEmbedding K (S : Set (HeightOneSpectrum (𝓞 K))) P
  have hnorm : ∀ q ∈ R.map e,
      actualSIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) q.val ≤ U := by
    intro q hq
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hq
    change actualSIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
      (frequencyRowOrbit K (S : Set (HeightOneSpectrum (𝓞 K))) P u) ≤ U
    rw [frequencyRowOrbit_norm]
    exact hR u hu
  have h := henergy U D hU hD (R.map e) hnorm s hs
  simpa only [Finset.sum_map, e, frequencyRowOrbitEmbedding,
    Function.Embedding.coeFn_mk, frequencyRowSixthPowerFreeOrbit, frequencyRowOrbit,
    actualSIntegerInversePolynomial_mk] using h

end HeckeGeneral.ThetaSkeleton.Physical
