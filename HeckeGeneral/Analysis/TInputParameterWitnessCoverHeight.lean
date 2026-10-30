import HeckeGeneral.Analysis.TInputParameterWitnessCover

/-! A cover may be available only below its own positive height ceiling.
Intersect that range with the moment range. The height degree is unchanged;
the scale threshold and label loss are the ones in the original consumer.
The nonnegative real-part bound holds for every source `RealBox.upper`.
-/

noncomputable section
namespace HeckeGeneral.Analysis.ConditionalMoments

open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

omit [NumberField K] in
theorem parameterHeightBound_dynamic_cover_bounded_height {n : ℕ} {ι υ : Type}
    (active : ℝ → Finset ι) (realBound : ℝ) (hreal : 0 ≤ realBound)
    (R : ℝ → (Fin n → ℝ) → Finset υ)
    (W : ℝ → (Fin n → ℝ) → (NonzeroIdeal K → Fin n → ℝ) →
      (NonzeroIdeal K → Fin n → ℝ) → ι → Finset υ)
    {power : ℝ → ι → ℝ} {p ε η : ℝ}
    (hW : ParameterHeightBound K active realBound
      (fun Z ξ σ τ i => ((W Z ξ σ τ i).card : ℝ)) power ε)
    (hpower : ∀ Z, 1 ≤ Z → ∀ i ∈ active Z, power Z i ≤ p)
    (hlabels : ∃ L Zlabel : ℝ, 0 < L ∧ 1 ≤ Zlabel ∧
      ∀ Z, Zlabel ≤ Z → ((active Z).card : ℝ) ≤ L * Z ^ η)
    (Zcover coverHeight : ℝ) (hheight : 0 < coverHeight)
    (hcover : ∀ Z ξ, Zcover ≤ Z → ‖ξ‖ ≤ Z ^ coverHeight →
      ∃ σ τ : ι → NonzeroIdeal K → Fin n → ℝ,
        (∀ i ∈ active Z, ∀ u, ‖σ i u‖ ≤ realBound) ∧
        (∀ i ∈ active Z, ∀ u, ‖τ i u‖ ≤ 1 + ‖ξ‖) ∧
        ∀ u ∈ R Z ξ, ∃ i ∈ active Z, u ∈ W Z ξ (σ i) (τ i) i) :
    ∃ C Z₀ A momentHeight : ℝ,
      0 < C ∧ 1 ≤ Z₀ ∧ 0 ≤ A ∧ 0 < momentHeight ∧
      0 < min coverHeight momentHeight ∧
      ∀ Z ξ, Z₀ ≤ Z → ‖ξ‖ ≤ Z ^ (min coverHeight momentHeight) →
        ((R Z ξ).card : ℝ) ≤ C * Z ^ (p + (ε + η)) * (1 + ‖ξ‖) ^ A := by
  let R' : ℝ → (Fin n → ℝ) → Finset υ :=
    fun Z ξ => if ‖ξ‖ ≤ Z ^ coverHeight then R Z ξ else ∅
  have hcover' : ∀ Z ξ, Zcover ≤ Z →
      ∃ σ τ : ι → NonzeroIdeal K → Fin n → ℝ,
        (∀ i ∈ active Z, ∀ u, ‖σ i u‖ ≤ realBound) ∧
        (∀ i ∈ active Z, ∀ u, ‖τ i u‖ ≤ 1 + ‖ξ‖) ∧
        ∀ u ∈ R' Z ξ, ∃ i ∈ active Z, u ∈ W Z ξ (σ i) (τ i) i := by
    intro Z ξ hZ
    by_cases hh : ‖ξ‖ ≤ Z ^ coverHeight
    · obtain ⟨σ, τ, hσ, hτ, hcov⟩ := hcover Z ξ hZ hh
      refine ⟨σ, τ, hσ, hτ, ?_⟩
      simpa only [R', ite_eq_left hh] using hcov
    · refine ⟨(fun _ _ => 0), (fun _ _ => 0), ?_, ?_, ?_⟩
      · intro i hi u
        simpa only [norm_zero] using hreal
      · intro i hi u
        simp only [norm_zero]
        positivity
      · simp only [R', ite_eq_right hh, Finset.notMem_empty, false_implies, implies_true]
  obtain ⟨C, Z₀, A, momentHeight, hC, hZ₀, hA, hm, hb⟩ :=
    parameterHeightBound_dynamic_cover K active realBound R' W hW hpower hlabels Zcover hcover'
  refine ⟨C, Z₀, A, momentHeight, hC, hZ₀, hA, hm, lt_min hheight hm, ?_⟩
  intro Z ξ hZ hξ
  have hZ1 : 1 ≤ Z := hZ₀.trans hZ
  have hcov : ‖ξ‖ ≤ Z ^ coverHeight := hξ.trans
    (Real.rpow_le_rpow_of_exponent_le hZ1 (min_le_left _ _))
  have hmoment : ‖ξ‖ ≤ Z ^ momentHeight := hξ.trans
    (Real.rpow_le_rpow_of_exponent_le hZ1 (min_le_right _ _))
  simpa only [R', ite_eq_left hcov] using hb Z ξ hZ hmoment

end HeckeGeneral.Analysis.ConditionalMoments

namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem physicalRowCount_of_parameter_dynamic_witness_cover_bounded_height
    {n : ℕ} {ι : Type}
    (active : ℝ → Finset ι) (realBound : ℝ) (hreal : 0 ≤ realBound)
    (R : ℝ → (Fin n → ℝ) → Finset (FrequencyRow K S))
    (W : ℝ → (Fin n → ℝ) → (NonzeroIdeal K → Fin n → ℝ) →
      (NonzeroIdeal K → Fin n → ℝ) → ι → Finset (NonzeroIdeal K))
    {power : ℝ → ι → ℝ} {p ε η : ℝ}
    (hW : ParameterHeightBound K active realBound
      (fun Z ξ σ τ i => ((W Z ξ σ τ i).card : ℝ)) power ε)
    (hpower : ∀ Z, 1 ≤ Z → ∀ i ∈ active Z, power Z i ≤ p)
    (hlabels : ∃ L Zlabel : ℝ, 0 < L ∧ 1 ≤ Zlabel ∧
      ∀ Z, Zlabel ≤ Z → ((active Z).card : ℝ) ≤ L * Z ^ η)
    (Zcover coverHeight : ℝ) (hheight : 0 < coverHeight)
    (hcover : ∀ Z ξ, Zcover ≤ Z → ‖ξ‖ ≤ Z ^ coverHeight →
      ∃ σ τ : ι → NonzeroIdeal K → Fin n → ℝ,
        (∀ i ∈ active Z, ∀ u, ‖σ i u‖ ≤ realBound) ∧
        (∀ i ∈ active Z, ∀ u, ‖τ i u‖ ≤ 1 + ‖ξ‖) ∧
        ∀ u ∈ R Z ξ, ∃ i ∈ active Z, u.ideal.val ∈ W Z ξ (σ i) (τ i) i) :
    ∃ C Z₀ A momentHeight : ℝ,
      0 < C ∧ 1 ≤ Z₀ ∧ 0 ≤ A ∧ 0 < momentHeight ∧
      0 < min coverHeight momentHeight ∧
      ∀ Z ξ, Z₀ ≤ Z → ‖ξ‖ ≤ Z ^ (min coverHeight momentHeight) →
        ((R Z ξ).card : ℝ) ≤ C * Z ^ (p + (ε + η)) * (1 + ‖ξ‖) ^ A := by
  have hI := parameterHeightBound_dynamic_cover_bounded_height K active realBound hreal
    (fun Z ξ => (R Z ξ).image (fun u => u.ideal.val)) W hW hpower hlabels
      Zcover coverHeight hheight (by
        intro Z ξ hZ hξ
        obtain ⟨σ, τ, hσ, hτ, hcov⟩ := hcover Z ξ hZ hξ
        refine ⟨σ, τ, hσ, hτ, ?_⟩
        intro I hI
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hI
        exact hcov u hu)
  obtain ⟨C, Z₀, A, momentHeight, hC, hZ₀, hA, hm, hmin, hb⟩ := hI
  have hM : (0 : ℝ) < Nat.card (SixthUnitClasses K S) := by
    exact_mod_cast Nat.card_pos (α := SixthUnitClasses K S)
  refine ⟨(Nat.card (SixthUnitClasses K S) : ℝ) * C, Z₀, A, momentHeight,
    mul_pos hM hC, hZ₀, hA, hm, hmin, ?_⟩
  intro Z ξ hZ hξ
  calc
    _ ≤ (Nat.card (SixthUnitClasses K S) : ℝ) *
        (((R Z ξ).image (fun u => u.ideal.val)).card : ℝ) :=
      physicalRows_card_le_idealImage K S (R Z ξ)
    _ ≤ (Nat.card (SixthUnitClasses K S) : ℝ) *
        (C * Z ^ (p + (ε + η)) * (1 + ‖ξ‖) ^ A) :=
      mul_le_mul_of_nonneg_left (hb Z ξ hZ hξ) hM.le
    _ = _ := by ring

end HeckeGeneral.ThetaSkeleton.Physical
