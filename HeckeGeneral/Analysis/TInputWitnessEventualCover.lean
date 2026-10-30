import HeckeGeneral.Analysis.TInputWitnessCoverage

/-!
Eventual coverage for the actual moment-witness counting consumer.
The cutoff is fixed after the whole finite family has been selected. It
only enlarges the eventual scale threshold; power, epsilon and height
degree/ceiling are unchanged. This permits absorbing a fixed finite
Theta-expansion factor into a positive scale loss without claiming that
the absorption holds at every scale Z >= 1.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open scoped Classical BigOperators

theorem polynomialHeightBound_eventually_mono {E F : ℝ → ℝ → ℝ} {p ε : ℝ}
    (hF : PolynomialHeightBound F p ε) (Zcover : ℝ)
    (hEF : ∀ Z t, Zcover ≤ Z → E Z t ≤ F Z t) :
    PolynomialHeightBound E p ε := by
  obtain ⟨C, Z₀, A, ceiling, hC, hZ₀, hA, hh, hb⟩ := hF
  refine ⟨C, max Zcover Z₀, A, ceiling, hC,
    hZ₀.trans (le_max_right _ _), hA, hh, ?_⟩
  intro Z t hZ ht
  exact (hEF Z t ((le_max_left _ _).trans hZ)).trans
    (hb Z t ((le_max_right _ _).trans hZ) ht)

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem physicalRowCount_of_eventual_witness_cover {ι : Type*} (F : Finset ι)
    (R : ℝ → ℝ → Finset (FrequencyRow K S))
    (W : ι → ℝ → ℝ → Finset (NonzeroIdeal K)) (Zcover : ℝ) {p ε : ℝ}
    (hcover : ∀ Z t, Zcover ≤ Z → ∀ u ∈ R Z t, ∃ i ∈ F, u.ideal.val ∈ W i Z t)
    (hW : ∀ i ∈ F, PolynomialHeightBound (fun Z t => ((W i Z t).card : ℝ)) p ε) :
    PolynomialHeightBound (fun Z t => ((R Z t).card : ℝ)) p ε := by
  have hcount := physicalRowCount_of_witness_cover K S F
    (fun Z t => if Zcover ≤ Z then R Z t else ∅) W (by
      intro Z t _ u hu
      by_cases h : Zcover ≤ Z
      · simp only [ite_eq_left h] at hu
        exact hcover Z t h u hu
      · simp [h] at hu) hW
  apply polynomialHeightBound_eventually_mono hcount Zcover
  intro Z t hZ
  simp only [ite_eq_left hZ, le_refl]

/-- The meshes precede the finite family. Its eventual coverage cutoff is
then fixed uniformly in scale and height. All estimates are still obtained
from actual MI/P polynomials; this adds no counting hypothesis. -/
theorem physicalRowCount_of_eventual_calibrated_moment_cover {ω : HeckeCharacter K}
    (cal : CanonicalAdmissibility ω) (hMI : MIInput ω cal) (hP : PInput ω cal)
    (b : RealBox) (ε : ℝ) (hε : 0 < ε) :
    ∃ meshMI meshP : ℝ, 0 < meshMI ∧ 0 < meshP ∧
      ∀ {ι : Type} (F : Finset ι) (f : ι → MomentWitnessFamily K ω)
        (R : ℝ → ℝ → Finset (FrequencyRow K S)) (p Zcover : ℝ),
        (∀ i ∈ F, (f i).Calibrated cal b (if (f i).paired then meshP else meshMI)) →
        (∀ i ∈ F, (f i).countPower ≤ p) →
        (∀ Z t, Zcover ≤ Z → ∀ u ∈ R Z t, ∃ i ∈ F, u.ideal.val ∈ (f i).rows Z t) →
        PolynomialHeightBound (fun Z t => ((R Z t).card : ℝ)) p ε := by
  obtain ⟨meshMI, meshP, hmeshMI, hmeshP, hbound⟩ :=
    physicalRowCount_of_calibrated_moment_cover K S cal hMI hP b ε hε
  refine ⟨meshMI, meshP, hmeshMI, hmeshP, ?_⟩
  intro ι F f R p Zcover hcal hp hcover
  have hcount := hbound F f (fun Z t => if Zcover ≤ Z then R Z t else ∅) p hcal hp (by
    intro Z t _ u hu
    by_cases h : Zcover ≤ Z
    · simp only [ite_eq_left h] at hu
      exact hcover Z t h u hu
    · simp [h] at hu)
  apply polynomialHeightBound_eventually_mono hcount Zcover
  intro Z t hZ
  simp only [ite_eq_left hZ, le_refl]

end HeckeGeneral.ThetaSkeleton.Physical
