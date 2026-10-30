import HeckeGeneral.Analysis.SIntegerPeriodicFourierTail

/-! Actual finite orbit cutoffs and certified periodic Fourier truncation.
The full sum is proved summable from its finite head and summable tail. -/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Bridge MeasureTheory
open scoped Classical BigOperators nonZeroDivisors

private theorem finite_head_tail_split {Q : Type*} (n : Q → ℝ) (ρ X : ℝ)
    (hs : Set.Finite {q | ρ * n q ≤ X}) (F : Q → ℂ)
    (ht : Summable (fun q : {q : Q // X < ρ * n q} => F q.val)) :
    Summable F ∧
      (∑' q, F q) - ∑ q ∈ hs.toFinset, F q =
        ∑' q : {q : Q // X < ρ * n q}, F q.val := by
  let s : Set Q := {q | ρ * n q ≤ X}
  have hh : Summable (fun q : s => F q.val) := by
    letI := hs.fintype
    exact Summable.of_finite
  have hscompl : sᶜ = {q | X < ρ * n q} := by
    ext q
    simp only [s, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  have ht' : Summable (fun q : ↥(sᶜ) => F q.val) := by
    rw [hscompl]
    exact ht
  have hf : Summable F := summable_subtype_and_compl.mp ⟨hh, ht'⟩
  refine ⟨hf, ?_⟩
  have he := hf.sum_add_tsum_subtype_compl hs.toFinset
  have he' : (∑ q ∈ hs.toFinset, F q) +
      (∑' q : {q : Q // X < ρ * n q}, F q.val) = ∑' q, F q := by
    have htail : (∑' q : {q : Q // q ∉ hs.toFinset}, F q.val) =
        ∑' q : {q : Q // X < ρ * n q}, F q.val :=
      tsum_congr_subtype F (fun q => by
        simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le])
    rwa [htail] at he
  linear_combination -he'

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "T" => sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "L" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) [Γ.FiniteIndex]
local notation "Q" => SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ

theorem finite_sIntegerOrbitCutoff (ρ : {r : ℝ // 0 < r}) (X : ℝ) :
    Set.Finite {q : Q | ρ.val *
      (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val ≤ X} := by
  apply (finite_setOf_sIntegerOrbitNorm_le K
    (S : Set (HeightOneSpectrum (𝓞 K))) Γ (X / ρ.val)).subset
  intro q hq
  exact (le_div_iff₀' ρ.property).mpr hq

def sIntegerOrbitCutoff (ρ : {r : ℝ // 0 < r}) (X : ℝ) : Finset Q :=
  (finite_sIntegerOrbitCutoff K S Γ ρ X).toFinset

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- A single actual summand, retaining its periodic divisor coefficient. -/
def sIntegerPeriodicFourierProfileTerm
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (φ : SchwartzMap V ℂ) (c : OS) (hc : c ≠ 0)
    (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ)
    (hinv : ∀ u : Γ, ∀ a : OS,
      f (Ideal.Quotient.mk _
        (((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K u.val).val * a)) =
          f (Ideal.Quotient.mk _ a)) (d : OS) (ρ : {r : ℝ // 0 < r}) (q : Q) : ℂ :=
  sIntegerPeriodicFourierOrbitWeight K (S : Set (HeightOneSpectrum (𝓞 K)))
    hS Γ c hc f hinv d q *
  sUnitOrbitalProfile K (S : Set (HeightOneSpectrum (𝓞 K)))
    (sLocalTensorTestFunction K (S : Set (HeightOneSpectrum (𝓞 K)))
      (traceSchwartzFourier K φ) (sIntegerFiniteFourierTestFunction K S μv h))
    ⟨ρ.val * (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val,
      mul_pos ρ.property (sIntegerOrbitNorm K
        (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).property⟩

include ν in
/-- The finite cutoff error is exactly the actual tail, with a bound uniform
in all moving modulus data and the original archimedean Schwartz function. -/
theorem exists_sIntegerPeriodicFourier_truncation_bound
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (A : ℝ) (hA : 1 < A) (M : ℕ) (hM : Module.finrank ℤ L < M)
    (hOrder : (Module.finrank ℚ K : ℝ) * A ≤ M) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ c : OS, ∀ hc : c ≠ 0,
      ∀ f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ,
      ∀ hinv : ∀ u : Γ, ∀ a : OS,
        f (Ideal.Quotient.mk _
          (((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K u.val).val * a)) =
            f (Ideal.Quotient.mk _ a),
      ∀ d : OS, ∀ φ : SchwartzMap V ℂ, ∀ ρ : {r : ℝ // 0 < r}, ∀ X : ℝ, 1 ≤ X →
        let F := sIntegerPeriodicFourierProfileTerm K S Γ μv hS h φ c hc f hinv d ρ
        let error := (∑' q, F q) - ∑ q ∈ sIntegerOrbitCutoff K S Γ ρ X, F q
        Summable F ∧
          error = (∑' q : {q : Q // X < ρ.val *
            (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val}, F q.val) ∧
          ‖error‖ ≤ sIntegerPeriodicResidueL1 K
            (S : Set (HeightOneSpectrum (𝓞 K))) c hc
            (fun a => f (Ideal.Quotient.mk _ d * a)) *
            C * s.sup (schwartzSeminormFamily ℂ V ℂ) φ *
              (1 + ρ.val⁻¹) * X ^ (1 - A) := by
  obtain ⟨s, C, hC, htail⟩ := exists_sIntegerPeriodicFourierProfile_tail_bound
    K S Γ ν μv hS h hlc hcs A hA M hM hOrder
  refine ⟨s, C, hC, ?_⟩
  intro c hc f hinv d φ ρ X hX
  dsimp only
  let F := sIntegerPeriodicFourierProfileTerm K S Γ μv hS h φ c hc f hinv d ρ
  obtain ⟨ht, hb⟩ := htail φ c hc f hinv d ρ X hX
  have ht' : Summable (fun q : {q : Q // X < ρ.val *
      (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val} => F q.val) := ht
  obtain ⟨hf, he⟩ := finite_head_tail_split
    (fun q => (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val)
    ρ.val X (finite_sIntegerOrbitCutoff K S Γ ρ X) F ht'
  refine ⟨hf, he, ?_⟩
  change ‖(∑' q, F q) -
    ∑ q ∈ (finite_sIntegerOrbitCutoff K S Γ ρ X).toFinset, F q‖ ≤ _
  rw [he]
  exact hb

end HeckeGeneral.Analysis
