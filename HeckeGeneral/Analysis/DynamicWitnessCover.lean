import HeckeGeneral.Analysis.TInputUniformWitnessCount
import HeckeGeneral.Analysis.TInputWitnessCoverage

/-! Uniform source moments can count a growing family of actual witnesses.
The labels need not form a fixed finite set. The threshold may vary with
scale and label. A separately verified small-power label count pays only
that power; all moment constants and height choices remain uniform.
-/

noncomputable section
namespace HeckeGeneral.Analysis.ConditionalMoments

open scoped Classical BigOperators

/-- One label-count threshold and one coverage threshold are selected for
the whole family. Height degree and ceiling are those of the moment input. -/
theorem polynomialHeightBound_dynamic_cover {ι υ : Type}
    (active : ℝ → Finset ι) (R : ℝ → ℝ → Finset υ)
    (W : ℝ → ℝ → ι → Finset υ) {p ε η : ℝ}
    (hW : UniformPolynomialHeightBound active (fun Z t i => ((W Z t i).card : ℝ))
      (fun _ _ => p) ε)
    (hlabels : ∃ L Zlabel : ℝ, 0 < L ∧ 1 ≤ Zlabel ∧
      ∀ Z, Zlabel ≤ Z → ((active Z).card : ℝ) ≤ L * Z ^ η)
    (Zcover : ℝ)
    (hcover : ∀ Z t, Zcover ≤ Z → ∀ u ∈ R Z t, ∃ i ∈ active Z, u ∈ W Z t i) :
    PolynomialHeightBound (fun Z t => ((R Z t).card : ℝ)) p (ε + η) := by
  obtain ⟨C, Z₀, A, ceiling, hC, hZ₀, hA, hc, hb⟩ := hW
  obtain ⟨L, Zlabel, hL, hZlabel, hlabel⟩ := hlabels
  refine ⟨L * C, max Zcover (max Zlabel Z₀), A, ceiling, mul_pos hL hC,
    hZ₀.trans ((le_max_right _ _).trans (le_max_right _ _)), hA, hc, ?_⟩
  intro Z t hZ ht
  have hZbase : Z₀ ≤ Z := (le_max_right _ _).trans ((le_max_right _ _).trans hZ)
  have hZlab : Zlabel ≤ Z := (le_max_left _ _).trans ((le_max_right _ _).trans hZ)
  have hZcov : Zcover ≤ Z := (le_max_left _ _).trans hZ
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one (hZ₀.trans hZbase)
  have hsub : R Z t ⊆ (active Z).biUnion (W Z t) := by
    intro u hu
    obtain ⟨i, hi, hui⟩ := hcover Z t hZcov u hu
    exact Finset.mem_biUnion.mpr ⟨i, hi, hui⟩
  have hcount : ((R Z t).card : ℝ) ≤ ∑ i ∈ active Z, ((W Z t i).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  calc
    _ ≤ ∑ i ∈ active Z, ((W Z t i).card : ℝ) := hcount
    _ ≤ ∑ i ∈ active Z, C * Z ^ (p + ε) * (1 + |t|) ^ A :=
      Finset.sum_le_sum fun i hi => hb Z t hZbase ht i hi
    _ = ((active Z).card : ℝ) * (C * Z ^ (p + ε) * (1 + |t|) ^ A) := by simp
    _ ≤ (L * Z ^ η) * (C * Z ^ (p + ε) * (1 + |t|) ^ A) :=
      mul_le_mul_of_nonneg_right (hlabel Z hZlab) (by positivity)
    _ = (L * C) * Z ^ (p + (ε + η)) * (1 + |t|) ^ A := by
      simp only [Real.rpow_add hZpos]
      ring

end HeckeGeneral.Analysis.ConditionalMoments

namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The finite unit-sector factor is fixed arithmetic data. It does not
grow with the active dyadic labels or affect their small-power loss. -/
theorem physicalRowCount_of_dynamic_witness_cover {ι : Type}
    (active : ℝ → Finset ι) (R : ℝ → ℝ → Finset (FrequencyRow K S))
    (W : ℝ → ℝ → ι → Finset (NonzeroIdeal K)) {p ε η : ℝ}
    (hW : UniformPolynomialHeightBound active (fun Z t i => ((W Z t i).card : ℝ))
      (fun _ _ => p) ε)
    (hlabels : ∃ L Zlabel : ℝ, 0 < L ∧ 1 ≤ Zlabel ∧
      ∀ Z, Zlabel ≤ Z → ((active Z).card : ℝ) ≤ L * Z ^ η)
    (Zcover : ℝ)
    (hcover : ∀ Z t, Zcover ≤ Z → ∀ u ∈ R Z t,
      ∃ i ∈ active Z, u.ideal.val ∈ W Z t i) :
    PolynomialHeightBound (fun Z t => ((R Z t).card : ℝ)) p (ε + η) := by
  have hI := polynomialHeightBound_dynamic_cover active
    (fun Z t => (R Z t).image (fun u => u.ideal.val)) W hW hlabels Zcover (by
      intro Z t hZ I hI
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hI
      exact hcover Z t hZ u hu)
  have hM : (0 : ℝ) < Nat.card (SixthUnitClasses K S) := by
    exact_mod_cast Nat.card_pos (α := SixthUnitClasses K S)
  apply polynomialHeightBound_mono (polynomialHeightBound_positive_mul hI hM)
  intro Z t _
  exact physicalRows_card_le_idealImage K S (R Z t)

end HeckeGeneral.ThetaSkeleton.Physical
