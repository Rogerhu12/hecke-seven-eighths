import HeckeGeneral.Analysis.IdealMobiusReciprocal
import HeckeGeneral.Analysis.HeckeEulerDeletion

/-!
Fixed finite prime deletion for the actual Moebius--Hecke ideal series.
The ideal mask below means that no prime in S divides the actual ideal.
This file only proves the identity on the absolute-convergence half-plane.
-/

noncomputable section
namespace HeckeGeneral.Analysis.IdealMobiusReciprocal
open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Arithmetic.IdealMobiusMask
open scoped BigOperators Classical nonZeroDivisors Topology

variable (K : Type) [Field K] [NumberField K]

def deletePrimes (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (p : HeightOneSpectrum (𝓞 K)) : ℂ :=
  if p ∈ S then 0 else a p

omit [NumberField K] in
theorem norm_deletePrimes_le_one (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1) :
    ∀ p, ‖deletePrimes K S a p‖ ≤ 1 := by
  intro p
  by_cases hp : p ∈ S <;> simp [deletePrimes, hp, ha p]

def avoids (S : Finset (HeightOneSpectrum (𝓞 K))) (I : NonzeroIdeal K) : Prop :=
  ∀ p ∈ S, ¬p.asIdeal ∣ I.val

def excludedTerm (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ) (I : NonzeroIdeal K) : ℂ :=
  if avoids K S I then term K a s I else 0

theorem avoids_squarefreeIdeal (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    avoids K S (squarefreeIdeal K T) ↔ Disjoint S T := by
  have hdiv (p : HeightOneSpectrum (𝓞 K)) :
      p.asIdeal ∣ (squarefreeIdeal K T).val ↔ p ∈ T := by
    rw [← SquarefreeAmplification.mem_idealPrimeSupport_iff K
      (SquarefreeAmplification.squarefreeIdeal K T) p,
      SquarefreeAmplification.idealPrimeSupport_squarefreeIdeal]
  constructor
  · intro h
    rw [Finset.disjoint_left]
    intro p hpS hpT
    exact h p hpS ((hdiv p).mpr hpT)
  · intro h p hpS hdvd
    exact Finset.disjoint_left.mp h hpS ((hdiv p).mp hdvd)

theorem term_deletePrimes (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ) (I : NonzeroIdeal K) :
    term K (deletePrimes K S a) s I = excludedTerm K S a s I := by
  by_cases hI : Squarefree I.val
  · obtain ⟨T, rfl⟩ := exists_squarefreeIdeal K I hI
    rw [excludedTerm, avoids_squarefreeIdeal, term_squarefreeIdeal, term_squarefreeIdeal]
    by_cases hd : Disjoint S T
    · rw [ite_eq_left hd]
      apply Finset.prod_congr rfl
      intro p hp
      have hpS : p ∉ S := fun hpS => Finset.disjoint_left.mp hd hpS hp
      simp [primeIdealRatio, deletePrimes, hpS]
    · rw [ite_eq_right hd]
      obtain ⟨p, hpS, hpT⟩ := Finset.not_disjoint_iff.mp hd
      apply Finset.prod_eq_zero hpT
      simp [primeIdealRatio, deletePrimes, hpS]
  · simp [excludedTerm, term, coefficient, dirichletTerm,
      moebius_of_not_squarefree hI]

theorem absolutelySummable_excluded (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) : Summable (fun I => ‖excludedTerm K S a s I‖) := by
  simpa only [term_deletePrimes] using
    absolutelySummable K (deletePrimes K S a) (norm_deletePrimes_le_one K S a ha) hs

theorem excluded_series_eq_inverse (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' I, excludedTerm K S a s I) =
      ((∏ p ∈ S, (1 - primeIdealRatio K a s p)) *
        idealDirichletSeries K (nonzeroIdealCoefficient a) s)⁻¹ := by
  have h := (hasProd_moebius_series K a ha hs).congr_cofinite₀
    (s := S) (fun p _ => primeIdealFactor_denominator_ne_zero K a ha hs p)
    (g := fun p => 1 - primeIdealRatio K (deletePrimes K S a) s p)
    (fun p hp => by simp [primeIdealRatio, deletePrimes, hp])
  have hg : (∏ p ∈ S, (1 - primeIdealRatio K (deletePrimes K S a) s p)) = 1 := by
    apply Finset.prod_eq_one
    intro p hp
    simp [primeIdealRatio, deletePrimes, hp]
  rw [hg, one_div, moebius_series_eq_inverse K a ha hs, ← mul_inv] at h
  have heq := (hasProd_moebius_series K (deletePrimes K S a)
    (norm_deletePrimes_le_one K S a ha) hs).unique h
  simpa only [term_deletePrimes, mul_comm] using heq

theorem hecke_excludedTerm_eq_literal (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) (I : NonzeroIdeal K) :
    excludedTerm K S (primeCoefficient K χ) s I =
      if (∀ p ∈ S, ¬p.asIdeal ∣ I.val) then
        (moebius I.val : ℂ) * heckeIdealCoefficient K χ I *
          (idealNorm K I : ℂ) ^ (-s) else 0 := by
  unfold excludedTerm
  split <;> split
  · rfl
  · rename_i h₁ h₂
    exact (h₂ h₁).elim
  · rename_i h₁ h₂
    exact (h₁ h₂).elim
  · rfl

/-- Absolute convergence for the literal S-excluded actual ideal sum. -/
theorem hecke_excluded_moebius_absolutelySummable (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : NonzeroIdeal K =>
      ‖if (∀ p ∈ S, ¬p.asIdeal ∣ I.val) then
        (moebius I.val : ℂ) * heckeIdealCoefficient K χ I *
          (idealNorm K I : ℂ) ^ (-s) else 0‖) := by
  have h := absolutelySummable_excluded K S (primeCoefficient K χ)
    (norm_primeCoefficient_le_one K χ) hs
  simp_rw [hecke_excludedTerm_eq_literal] at h
  exact h

/-- The literal S-excluded actual ideal sum, preserving ramified zeros,
equals the reciprocal of the already-defined deleted continuation. -/
theorem hecke_excluded_moebius_series_eq_reciprocal (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    (∑' I : NonzeroIdeal K,
      if (∀ p ∈ S, ¬p.asIdeal ∣ I.val) then
        (moebius I.val : ℂ) * heckeIdealCoefficient K χ I *
          (idealNorm K I : ℂ) ^ (-s) else 0) =
      (heckeDeletedContinuation K χ S s)⁻¹ := by
  have hP : heckeEulerDeletionPolynomial K χ S s =
      ∏ p ∈ S, (1 - primeIdealRatio K (primeCoefficient K χ) s p) := by
    simp only [heckeEulerDeletionPolynomial, finiteEulerPolynomial,
      eulerPolynomial, primeIdealRatio, residueCard, Complex.ofReal_natCast]
  rw [heckeDeletedContinuation, hP, heckeContinuation_eq_series K χ hs]
  have h := excluded_series_eq_inverse K S (primeCoefficient K χ)
    (norm_primeCoefficient_le_one K χ) hs
  simp_rw [hecke_excludedTerm_eq_literal] at h
  have hL : idealDirichletSeries K (nonzeroIdealCoefficient (primeCoefficient K χ)) s =
      heckeLSeries K χ s := rfl
  rw [hL] at h
  exact h

end HeckeGeneral.Analysis.IdealMobiusReciprocal
