import HeckeSkeleton.Moments.MOM_BASE.Arithmetic
import HeckeSkeleton.Moments.MOM_BASE.CubeInversion
import HeckePort.Moments.Descent.Completion

/-!
# Canonical cube completion on the literal theta coefficients

This module specializes the ideal cube inversion to `ThetaArithmeticData`.
The completed sum is exactly `completedTerm`, with its original puncture
and whole-index marks. No formal replacement for the theta coefficient or
unproved finite-support premise is used.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_BASE

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckePort.CenteredMomentGenerator
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- Zero extension of the actual Gauss coefficient to all integral ideals. -/
def exteriorGamma (I : Ideal (𝓞 K)) : ℂ :=
  if h : IsExterior K S I then thetaGamma K S D (toExterior K S I h) 2 else 0

theorem exteriorGamma_apply (I : ExteriorIdeal K S) :
    exteriorGamma K S D I.val.val = thetaGamma K S D I 2 := by
  have h : IsExterior K S I.val.val := ⟨nonZeroDivisors.coe_ne_zero I.val, I.property⟩
  simp only [exteriorGamma, dif_pos h] <;> rfl

theorem canonicalTau_eq_zero_of_not_exterior (θ : HeckeCharacter K)
    (m : S.integer K) (r I : Ideal (𝓞 K)) (hI : ¬ IsExterior K S I) :
    canonicalTau K S D θ m r I = 0 := by
  by_cases h0 : I = ⊥
  · subst I
    simp [canonicalTau, idealCoefficientHom]
  · have hbad : ∃ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I ∧ p ∈ S := by
      by_contra h
      apply hI
      refine ⟨h0, ?_⟩
      intro p hp hpS
      exact h ⟨p, hp, hpS⟩
    obtain ⟨p, hp, hpS⟩ := hbad
    exact canonicalTau_eq_zero_of_excluded K S D θ m r I p hpS hp

/-- A whole-index tuple of marks, before cube extraction. -/
def wholeMarkWeight (Q : Finset (ExteriorPrime K S)) (I : Ideal (𝓞 K)) : ℂ :=
  if ∀ p ∈ Q, p.val.asIdeal ∣ I then 1 else 0

@[simp] theorem wholeMarkWeight_empty (I : Ideal (𝓞 K)) :
    wholeMarkWeight K S ∅ I = 1 := by simp [wholeMarkWeight]

theorem completedIdeal_val (C B : ExteriorIdeal K S) :
    (completedIdeal K S C B).val.val = C.val.val * B.val.val ^ 3 := by
  simp only [completedIdeal, exteriorMul, Submonoid.coe_mul]
  ring

theorem completedIdeal_norm (C B : ExteriorIdeal K S) :
    exteriorNorm K S (completedIdeal K S C B) =
      cubeIdealNorm C.val.val * cubeIdealNorm B.val.val ^ 3 := by
  unfold exteriorNorm cubeIdealNorm
  rw [completedIdeal_val, map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]

/-- The whole-index weight stays outside the literal completed coefficient. -/
def weightedCompletedTheta (θ : HeckeCharacter K) (m : S.integer K)
    (r : ExteriorIdeal K S) (Q : Finset (ExteriorPrime K S))
    (d : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' CB : ExteriorIdeal K S × ExteriorIdeal K S,
    completedTerm K S D θ m r Q V X CB *
      d (completedIdeal K S CB.1 CB.2).val.val

@[simp] theorem weightedCompletedTheta_one (θ : HeckeCharacter K) (m : S.integer K)
    (r : ExteriorIdeal K S) (Q : Finset (ExteriorPrime K S))
    (V : ℝ → ℂ) (X : ℝ) :
    weightedCompletedTheta K S D θ m r Q (fun _ => 1) V X =
      completedThetaSum K S D θ m r Q V X := by
  simp [weightedCompletedTheta, completedThetaSum]

/-- Exact term-by-term identification, including all original zeros. -/
theorem canonicalCompletedTerm_eq_actual (θ : HeckeCharacter K) (m : S.integer K)
    (r : ExteriorIdeal K S) (Q : Finset (ExteriorPrime K S))
    (d : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (X : ℝ)
    (C B : ExteriorIdeal K S) :
    canonicalCompletedTerm (exteriorGamma K S D)
      (canonicalTau K S D θ m r.val.val)
      (fun A => wholeMarkWeight K S Q A * d A) V X (C.val.val, B.val.val) =
      completedTerm K S D θ m r Q V X (C, B) *
        d (completedIdeal K S C B).val.val := by
  have hA := completedIdeal_val K S C B
  simp only [canonicalCompletedTerm, exteriorGamma_apply]
  rw [← hA, canonicalTau_apply]
  simp only [completedTerm, wholeIndexMask, wholeMarkWeight]
  rw [completedIdeal_norm]
  change (if Squarefree C.val.val then
    thetaGamma K S D C 2 *
      (heckeIdealCoefficient K θ (completedIdeal K S C B).val *
        idealSymbol K S D (completedIdeal K S C B) m *
        (if IsCoprime (completedIdeal K S C B).val.val r.val.val then 1 else 0)) /
      ((Real.sqrt (cubeIdealNorm C.val.val) : ℂ) * (cubeIdealNorm B.val.val : ℂ)) *
      ((if ∀ p ∈ Q, p.val.asIdeal ∣ (completedIdeal K S C B).val.val then 1 else 0) *
        d (completedIdeal K S C B).val.val) *
      V (cubeIdealNorm C.val.val * cubeIdealNorm B.val.val ^ 3 / X)
    else 0) = _
  have hNC : exteriorNorm K S C = cubeIdealNorm C.val.val := rfl
  have hNB : exteriorNorm K S B = cubeIdealNorm B.val.val := rfl
  rw [hNC, hNB]
  by_cases hc : Squarefree C.val.val <;>
    by_cases hr : IsCoprime (completedIdeal K S C B).val.val r.val.val <;>
      by_cases hQ : ∀ p ∈ Q, p.val.asIdeal ∣ (completedIdeal K S C B).val.val <;>
        simp [hc, hr, hQ] <;> ring

private theorem canonicalCompletedTerm_support_exterior (θ : HeckeCharacter K)
    (m : S.integer K) (r : Ideal (𝓞 K)) (d : Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (X : ℝ) (C B : Ideal (𝓞 K))
    (hne : canonicalCompletedTerm (exteriorGamma K S D)
      (canonicalTau K S D θ m r) d V X (C, B) ≠ 0) :
    IsExterior K S C ∧ IsExterior K S B := by
  have hC : IsExterior K S C := by
    by_contra h
    exact hne (by simp [canonicalCompletedTerm, exteriorGamma, h])
  have hB : IsExterior K S B := by
    by_contra h
    have hA : ¬ IsExterior K S (C * B ^ 3) := by
      intro hA
      have hb0 : B ≠ ⊥ := by
        intro hz
        exact hA.1 (by simp [hz])
      apply h
      refine ⟨hb0, ?_⟩
      intro p hp
      exact hA.2 p (dvd_mul_of_dvd_right (dvd_trans hp (dvd_pow_self B (by decide))) C)
    have hz := canonicalTau_eq_zero_of_not_exterior K S D θ m r (C * B ^ 3) hA
    exact hne (by simp [canonicalCompletedTerm, hz])
  exact ⟨hC, hB⟩

private theorem exteriorPair_injective : Function.Injective
    (fun CB : ExteriorIdeal K S × ExteriorIdeal K S => (CB.1.val.val, CB.2.val.val)) := by
  intro A B h
  exact Prod.ext (Subtype.ext (Subtype.ext (congrArg Prod.fst h)))
    (Subtype.ext (Subtype.ext (congrArg Prod.snd h)))

/-- The canonical completion is the repository's actual marked theta sum. -/
theorem canonicalCompletedSum_eq_weightedTheta (θ : HeckeCharacter K) (m : S.integer K)
    (r : ExteriorIdeal K S) (Q : Finset (ExteriorPrime K S))
    (d : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (X U : ℝ)
    (hX : 0 < X) (hV : Function.support V ⊆ Set.Iic U) :
    canonicalCompletedSum (exteriorGamma K S D)
      (canonicalTau K S D θ m r.val.val)
      (fun A => wholeMarkWeight K S Q A * d A) V X =
      weightedCompletedTheta K S D θ m r Q d V X := by
  rw [canonicalCompletedSum_eq_tsum _ _ _ V X U hX hV]
  have hs : Function.support (canonicalCompletedTerm (exteriorGamma K S D)
      (canonicalTau K S D θ m r.val.val)
      (fun A => wholeMarkWeight K S Q A * d A) V X) ⊆
      Set.range (fun CB : ExteriorIdeal K S × ExteriorIdeal K S =>
        (CB.1.val.val, CB.2.val.val)) := by
    rintro ⟨C, B⟩ hCB
    obtain ⟨hC, hB⟩ := canonicalCompletedTerm_support_exterior
      K S D θ m r.val.val _ V X C B hCB
    exact ⟨(toExterior K S C hC, toExterior K S B hB), rfl⟩
  rw [← (exteriorPair_injective K S).tsum_eq hs]
  apply tsum_congr
  rintro ⟨C, B⟩
  exact canonicalCompletedTerm_eq_actual K S D θ m r Q d V X C B

/-- Actual completed summands instantiate the finite-support interface
used throughout `HeckePort.Moments.Descent.Completion`. -/
theorem actualCompletedSummand (θ : HeckeCharacter K) (m : S.integer K)
    (r : ExteriorIdeal K S) (V : ℝ → ℂ) (X U : ℝ)
    (hX : 0 < X) (hV : Function.support V ⊆ Set.Iic U) :
    HeckePort.Moments.CompletedSummand
      (fun C B => canonicalCompletedTerm (exteriorGamma K S D)
        (canonicalTau K S D θ m r.val.val) (fun _ => 1) V X (C, B)) where
  zero_left := canonicalCompletedTerm_bot_left _ _ _ V X
  zero_right := canonicalCompletedTerm_bot_right _ _ _ V X
  finite_support := canonicalCompletedTerm_finite_support _ _ _ V X U hX hV

/-- The exact canonical bridge of Lemma 4.3, with arbitrary whole-index
weight and the actual original Hecke/symbol/puncture coefficient. -/
theorem canonicalThetaBridge (θ : HeckeCharacter K) (m : S.integer K)
    (r : ExteriorIdeal K S) (d : Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (X U : ℝ) (hX : 0 < X)
    (hV : Function.support V ⊆ Set.Iic U) :
    (∑' C : ExteriorIdeal K S, if Squarefree C.val.val then
      thetaGamma K S D C 2 * canonicalTau K S D θ m r.val.val C.val.val /
        (Real.sqrt (exteriorNorm K S C) : ℂ) * d C.val.val *
          V (exteriorNorm K S C / X) else 0) =
      ∑' H : ExteriorIdeal K S,
        (moebius H.val.val : ℂ) * canonicalTau K S D θ m r.val.val H.val.val ^ 3 /
          (exteriorNorm K S H : ℂ) *
          weightedCompletedTheta K S D θ m r ∅
            (fun A => d (H.val.val ^ 3 * A)) V (X / exteriorNorm K S H ^ 3) := by
  have hinj : Function.Injective (fun I : ExteriorIdeal K S => I.val.val) := by
    intro I J h
    exact Subtype.ext (Subtype.ext h)
  have hleft : Function.support (fun C : Ideal (𝓞 K) => if Squarefree C then
      exteriorGamma K S D C * canonicalTau K S D θ m r.val.val C /
        (Real.sqrt (cubeIdealNorm C) : ℂ) * d C * V (cubeIdealNorm C / X) else 0) ⊆
      Set.range (fun I : ExteriorIdeal K S => I.val.val) := by
    intro C hC
    have he : IsExterior K S C := by
      by_contra h
      exact hC (by simp [exteriorGamma, h])
    exact ⟨toExterior K S C he, rfl⟩
  have hright : Function.support (fun H : Ideal (𝓞 K) =>
      (moebius H : ℂ) * canonicalTau K S D θ m r.val.val H ^ 3 /
        (cubeIdealNorm H : ℂ) * canonicalCompletedSum (exteriorGamma K S D)
          (canonicalTau K S D θ m r.val.val) (fun A => d (H ^ 3 * A))
          V (X / cubeIdealNorm H ^ 3)) ⊆
      Set.range (fun I : ExteriorIdeal K S => I.val.val) := by
    intro H hH
    have he : IsExterior K S H := by
      by_contra h
      have hz := canonicalTau_eq_zero_of_not_exterior K S D θ m r.val.val H h
      exact hH (by simp [hz])
    exact ⟨toExterior K S H he, rfl⟩
  have h := canonicalCubeInversion (exteriorGamma K S D)
    (canonicalTau K S D θ m r.val.val) d V X U hX hV
  rw [← hinj.tsum_eq hleft, ← hinj.tsum_eq hright] at h
  simp only [exteriorGamma_apply] at h
  refine h.trans ?_
  apply tsum_congr
  intro H
  have hN : 0 < exteriorNorm K S H := idealNorm_pos K H.val
  have hscale : 0 < X / exteriorNorm K S H ^ 3 := div_pos hX (pow_pos hN 3)
  congr 1
  simpa only [wholeMarkWeight_empty, one_mul, cubeIdealNorm, exteriorNorm] using
    canonicalCompletedSum_eq_weightedTheta K S D θ m r ∅
      (fun A => d (H.val.val ^ 3 * A)) V (X / exteriorNorm K S H ^ 3) U hscale hV

end HeckeSkeleton.Moments.MOM_BASE
