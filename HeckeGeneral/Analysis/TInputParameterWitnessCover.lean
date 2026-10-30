import HeckeGeneral.Analysis.TInputParameterUniformMoments
import HeckeGeneral.Analysis.TInputWitnessCoverage

/-!
# Continuous-parameter covers by a growing family of actual witnesses

`ParameterHeightBound` chooses constants before ALL row maps and labels.
Thus each label may use different row maps: the two universal quantifiers
commute, without enlarging the fixed dimension of the continuous height.
Only the small-power number of active labels is paid in the scale exponent.

The explicit coverage premise below selects whole row maps for each label.
Pointwise choices cannot be glued for an arbitrary data family that depends
nonlocally on the whole map. A physical calibration must establish that
coverage, or first prove the needed row-locality. No such locality or source
coverage is asserted here. Neither is a moment estimate assumed for the
final union; its count is proved from the individual actual witnesses.
-/

noncomputable section

namespace HeckeGeneral.Analysis.ConditionalMoments

open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

omit [NumberField K] in
/-- Different labels may use different row maps. The height degree and
ceiling are exactly those in the original uniform witness bound. -/
theorem parameterHeightBound_dynamic_cover {n : ℕ} {ι υ : Type}
    (active : ℝ → Finset ι) (realBound : ℝ)
    (R : ℝ → (Fin n → ℝ) → Finset υ)
    (W : ℝ → (Fin n → ℝ) → (NonzeroIdeal K → Fin n → ℝ) →
      (NonzeroIdeal K → Fin n → ℝ) → ι → Finset υ)
    {power : ℝ → ι → ℝ} {p ε η : ℝ}
    (hW : ParameterHeightBound K active realBound
      (fun Z ξ σ τ i => ((W Z ξ σ τ i).card : ℝ)) power ε)
    (hpower : ∀ Z, 1 ≤ Z → ∀ i ∈ active Z, power Z i ≤ p)
    (hlabels : ∃ L Zlabel : ℝ, 0 < L ∧ 1 ≤ Zlabel ∧
      ∀ Z, Zlabel ≤ Z → ((active Z).card : ℝ) ≤ L * Z ^ η)
    (Zcover : ℝ)
    (hcover : ∀ Z ξ, Zcover ≤ Z →
      ∃ σ τ : ι → NonzeroIdeal K → Fin n → ℝ,
        (∀ i ∈ active Z, ∀ u, ‖σ i u‖ ≤ realBound) ∧
        (∀ i ∈ active Z, ∀ u, ‖τ i u‖ ≤ 1 + ‖ξ‖) ∧
        ∀ u ∈ R Z ξ, ∃ i ∈ active Z, u ∈ W Z ξ (σ i) (τ i) i) :
    ∃ C Z₀ A ceiling : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧ 0 ≤ A ∧ 0 < ceiling ∧
      ∀ Z ξ, Z₀ ≤ Z → ‖ξ‖ ≤ Z ^ ceiling →
        ((R Z ξ).card : ℝ) ≤ C * Z ^ (p + (ε + η)) * (1 + ‖ξ‖) ^ A := by
  obtain ⟨C, Z₀, A, ceiling, hC, hZ₀, hA, hc, hb⟩ := hW
  obtain ⟨L, Zlabel, hL, hZlabel, hlabel⟩ := hlabels
  refine ⟨L * C, max Zcover (max Zlabel Z₀), A, ceiling, mul_pos hL hC,
    hZ₀.trans ((le_max_right _ _).trans (le_max_right _ _)), hA, hc, ?_⟩
  intro Z ξ hZ hξ
  have hZbase : Z₀ ≤ Z := (le_max_right _ _).trans ((le_max_right _ _).trans hZ)
  have hZlab : Zlabel ≤ Z := (le_max_left _ _).trans ((le_max_right _ _).trans hZ)
  have hZcov : Zcover ≤ Z := (le_max_left _ _).trans hZ
  have hZ1 : 1 ≤ Z := hZ₀.trans hZbase
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ1
  obtain ⟨σ, τ, hσ, hτ, hcov⟩ := hcover Z ξ hZcov
  have hsub : R Z ξ ⊆ (active Z).biUnion (fun i => W Z ξ (σ i) (τ i) i) := by
    intro u hu
    obtain ⟨i, hi, hui⟩ := hcov u hu
    exact Finset.mem_biUnion.mpr ⟨i, hi, hui⟩
  have hcount : ((R Z ξ).card : ℝ) ≤
      ∑ i ∈ active Z, ((W Z ξ (σ i) (τ i) i).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hiBound : ∀ i ∈ active Z,
      ((W Z ξ (σ i) (τ i) i).card : ℝ) ≤
        C * Z ^ (p + ε) * (1 + ‖ξ‖) ^ A := by
    intro i hi
    apply (hb Z ξ hZbase hξ (σ i) (τ i) (hσ i hi) (hτ i hi) i hi).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ1 (add_le_add (hpower Z hZ1 i hi) le_rfl))
        hC.le) (Real.rpow_nonneg (by positivity) _)
  calc
    _ ≤ ∑ i ∈ active Z, ((W Z ξ (σ i) (τ i) i).card : ℝ) := hcount
    _ ≤ ∑ i ∈ active Z, C * Z ^ (p + ε) * (1 + ‖ξ‖) ^ A :=
      Finset.sum_le_sum hiBound
    _ = ((active Z).card : ℝ) * (C * Z ^ (p + ε) * (1 + ‖ξ‖) ^ A) := by simp
    _ ≤ (L * Z ^ η) * (C * Z ^ (p + ε) * (1 + ‖ξ‖) ^ A) :=
      mul_le_mul_of_nonneg_right (hlabel Z hZlab) (by positivity)
    _ = (L * C) * Z ^ (p + (ε + η)) * (1 + ‖ξ‖) ^ A := by
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

/-- Actual frequency rows lose only the fixed number of sixth-unit sectors.
The label loss changes the scale exponent, never the height degree. -/
theorem physicalRowCount_of_parameter_dynamic_witness_cover {n : ℕ} {ι : Type}
    (active : ℝ → Finset ι) (realBound : ℝ)
    (R : ℝ → (Fin n → ℝ) → Finset (FrequencyRow K S))
    (W : ℝ → (Fin n → ℝ) → (NonzeroIdeal K → Fin n → ℝ) →
      (NonzeroIdeal K → Fin n → ℝ) → ι → Finset (NonzeroIdeal K))
    {power : ℝ → ι → ℝ} {p ε η : ℝ}
    (hW : ParameterHeightBound K active realBound
      (fun Z ξ σ τ i => ((W Z ξ σ τ i).card : ℝ)) power ε)
    (hpower : ∀ Z, 1 ≤ Z → ∀ i ∈ active Z, power Z i ≤ p)
    (hlabels : ∃ L Zlabel : ℝ, 0 < L ∧ 1 ≤ Zlabel ∧
      ∀ Z, Zlabel ≤ Z → ((active Z).card : ℝ) ≤ L * Z ^ η)
    (Zcover : ℝ)
    (hcover : ∀ Z ξ, Zcover ≤ Z →
      ∃ σ τ : ι → NonzeroIdeal K → Fin n → ℝ,
        (∀ i ∈ active Z, ∀ u, ‖σ i u‖ ≤ realBound) ∧
        (∀ i ∈ active Z, ∀ u, ‖τ i u‖ ≤ 1 + ‖ξ‖) ∧
        ∀ u ∈ R Z ξ, ∃ i ∈ active Z, u.ideal.val ∈ W Z ξ (σ i) (τ i) i) :
    ∃ C Z₀ A ceiling : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧ 0 ≤ A ∧ 0 < ceiling ∧
      ∀ Z ξ, Z₀ ≤ Z → ‖ξ‖ ≤ Z ^ ceiling →
        ((R Z ξ).card : ℝ) ≤ C * Z ^ (p + (ε + η)) * (1 + ‖ξ‖) ^ A := by
  have hI := parameterHeightBound_dynamic_cover K active realBound
    (fun Z ξ => (R Z ξ).image (fun u => u.ideal.val)) W hW hpower hlabels Zcover (by
      intro Z ξ hZ
      obtain ⟨σ, τ, hσ, hτ, hcov⟩ := hcover Z ξ hZ
      refine ⟨σ, τ, hσ, hτ, ?_⟩
      intro I hI
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hI
      exact hcov u hu)
  obtain ⟨C, Z₀, A, ceiling, hC, hZ₀, hA, hc, hb⟩ := hI
  have hM : (0 : ℝ) < Nat.card (SixthUnitClasses K S) := by
    exact_mod_cast Nat.card_pos (α := SixthUnitClasses K S)
  refine ⟨(Nat.card (SixthUnitClasses K S) : ℝ) * C, Z₀, A, ceiling,
    mul_pos hM hC, hZ₀, hA, hc, ?_⟩
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
