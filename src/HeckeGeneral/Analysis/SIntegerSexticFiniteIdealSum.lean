import HeckeGeneral.Analysis.IdealSquarefreeSupport
import HeckeGeneral.Analysis.SIntegerSexticAmplification

/-!
Actual finite ideal sums for sextic inverse rows.  The zero extension below
deletes exactly ideals meeting the fixed S or the support of 6.  No extra
moving mask is supplied.  Reindexing requires coverage only of nonzero
terms, and missing terms inside the envelope must actually vanish.

The final amplification uses the SAME W and one common prime envelope at
D and at every D/q_A.  Constructing the finite supports from an analytic
test, counting allowed rows, and deriving MI energy bounds are not done here.
-/

noncomputable section

namespace HeckeGeneral.Analysis.SquarefreeAmplification

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.Arithmetic.IdealMobiusMask HeckeGeneral.Characters
open UniqueFactorizationMonoid
open scoped BigOperators Classical nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)

/-- A concrete fixed-S deletion condition, including the residue primes of 6. -/
def sexticIdealOutsideS (I : NonzeroIdeal K) : Prop :=
  ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val →
    p ∉ S ∧ (6 : 𝓞 K) ∉ p.asIdeal

/-- Actual ideal evaluation where admissible, and literal zero at every
ideal deleted by the fixed exceptional set or the support of 6. -/
def zeroExtendedSexticIdealEvaluation (I : NonzeroIdeal K) (u : S.integer K) : ℂ :=
  if h : sexticIdealOutsideS K S I then
    sIntegerSexticIdealEvaluation K S ζ hζ σ I.val (nonZeroDivisors.coe_ne_zero I)
      (fun p hp => (h p hp).1) (fun p hp => (h p hp).2) u
  else 0

theorem zeroExtendedSexticIdealEvaluation_eq_zero
    (I : NonzeroIdeal K) (u : S.integer K) (h : ¬sexticIdealOutsideS K S I) :
    zeroExtendedSexticIdealEvaluation K S ζ hζ σ I u = 0 := by
  simp only [zeroExtendedSexticIdealEvaluation, dite_eq_right h]

theorem zeroExtendedSexticIdealEvaluation_squarefreeIdeal
    (E : Finset (HeightOneSpectrum (𝓞 K)))
    (hES : ∀ p ∈ E, p ∉ S) (hE6 : ∀ p ∈ E, (6 : 𝓞 K) ∉ p.asIdeal)
    (T : Finset (HeightOneSpectrum (𝓞 K))) (hT : T ⊆ E) (u : S.integer K) :
    zeroExtendedSexticIdealEvaluation K S ζ hζ σ (squarefreeIdeal K T) u =
      sexticEnvelopeEvaluation K S ζ hζ σ E hES hE6 T hT u := by
  have hgood : sexticIdealOutsideS K S (squarefreeIdeal K T) := by
    intro p hp
    have hpE : p ∈ E := hT ((prime_dvd_primeProduct_iff K p T).mp hp)
    exact ⟨hES p hpE, hE6 p hpE⟩
  rw [zeroExtendedSexticIdealEvaluation, dite_eq_left hgood]
  rfl

/-- The literal ideal summand with the fixed background Hecke coefficient. -/
def sIntegerSexticInverseIdealTerm (η : HeckeCharacter K) (u : S.integer K)
    (D : ℝ) (W : ℝ → ℂ) (I : NonzeroIdeal K) : ℂ :=
  (moebius I.val : ℂ) * heckeIdealCoefficient K η I *
    zeroExtendedSexticIdealEvaluation K S ζ hζ σ I u ^ (-1 : ℤ) *
    W (idealNorm K I / D)

theorem sIntegerSexticInverseIdealTerm_eq_zero_of_deleted
    (η : HeckeCharacter K) (u : S.integer K) (D : ℝ) (W : ℝ → ℂ)
    (I : NonzeroIdeal K) (h : ¬sexticIdealOutsideS K S I) :
    sIntegerSexticInverseIdealTerm K S ζ hζ σ η u D W I = 0 := by
  simp [sIntegerSexticInverseIdealTerm,
    zeroExtendedSexticIdealEvaluation_eq_zero K S ζ hζ σ I u h]

theorem squarefree_of_sIntegerSexticInverseIdealTerm_ne_zero
    (η : HeckeCharacter K) (u : S.integer K) (D : ℝ) (W : ℝ → ℂ)
    (I : NonzeroIdeal K)
    (h : sIntegerSexticInverseIdealTerm K S ζ hζ σ η u D W I ≠ 0) :
    Squarefree I.val := by
  by_contra hn
  exact h (by simp [sIntegerSexticInverseIdealTerm, moebius_of_not_squarefree hn])

/-- The actual normalized finite ideal sum, with fixed-S zero extension. -/
def sIntegerSexticInverseIdealPolynomial (η : HeckeCharacter K)
    (F : Finset (NonzeroIdeal K)) (u : S.integer K) (D : ℝ) (W : ℝ → ℂ) : ℂ :=
  (Real.sqrt D : ℂ)⁻¹ *
    ∑ I ∈ F, sIntegerSexticInverseIdealTerm K S ζ hζ σ η u D W I

/-- Reindex the nonzero actual terms.  F may include deleted ideals and
nonsquarefree ideals; their terms vanish, so they impose no cover condition. -/
theorem sIntegerSexticInverseIdealSum_eq_squarefree
    (η : HeckeCharacter K) (F : Finset (NonzeroIdeal K)) (u : S.integer K)
    (E : Finset (HeightOneSpectrum (𝓞 K))) (D : ℝ) (W : ℝ → ℂ)
    (hcover : ∀ I ∈ F,
      sIntegerSexticInverseIdealTerm K S ζ hζ σ η u D W I ≠ 0 →
        idealPrimeSupport K I ⊆ E)
    (hsupport : ∀ I, idealPrimeSupport K I ⊆ E → I ∉ F →
      sIntegerSexticInverseIdealTerm K S ζ hζ σ η u D W I = 0) :
    (∑ I ∈ F, sIntegerSexticInverseIdealTerm K S ζ hζ σ η u D W I) =
      ∑ T ∈ E.powerset,
        sIntegerSexticInverseIdealTerm K S ζ hζ σ η u D W (squarefreeIdeal K T) := by
  have hsq := squarefree_of_sIntegerSexticInverseIdealTerm_ne_zero K S ζ hζ σ η u D W
  apply Finset.sum_bij_ne_zero (fun I _ _ => idealPrimeSupport K I)
  · intro I hI hn
    exact Finset.mem_powerset.mpr (hcover I hI hn)
  · intro I _ hi J _ hj hij
    calc
      I = squarefreeIdeal K (idealPrimeSupport K I) :=
        (squarefreeIdeal_primeSupport K I (hsq I hi)).symm
      _ = squarefreeIdeal K (idealPrimeSupport K J) := congrArg _ hij
      _ = J := squarefreeIdeal_primeSupport K J (hsq J hj)
  · intro T hTE hn
    have hmem : squarefreeIdeal K T ∈ F := by
      by_contra h
      have hsub : idealPrimeSupport K (squarefreeIdeal K T) ⊆ E := by
        simpa using Finset.mem_powerset.mp hTE
      exact hn (hsupport _ hsub h)
    exact ⟨squarefreeIdeal K T, hmem, hn, idealPrimeSupport_squarefreeIdeal K T⟩
  · intro I _ hi
    rw [squarefreeIdeal_primeSupport K I (hsq I hi)]

/-- The actual finite ideal sum equals the actual sextic row on an exterior
prime envelope.  The support conditions concern actual summands, so W is
not required to vanish on ideals removed by the fixed S deletion. -/
theorem sIntegerSexticInverseIdealPolynomial_eq_rowPolynomial
    (η : HeckeCharacter K) (F : Finset (NonzeroIdeal K)) (u : S.integer K)
    (E : Finset (HeightOneSpectrum (𝓞 K)))
    (hES : ∀ p ∈ E, p ∉ S) (hE6 : ∀ p ∈ E, (6 : 𝓞 K) ∉ p.asIdeal)
    (D : ℝ) (W : ℝ → ℂ)
    (hcover : ∀ I ∈ F,
      sIntegerSexticInverseIdealTerm K S ζ hζ σ η u D W I ≠ 0 →
        idealPrimeSupport K I ⊆ E)
    (hsupport : ∀ I, idealPrimeSupport K I ⊆ E → I ∉ F →
      sIntegerSexticInverseIdealTerm K S ζ hζ σ η u D W I = 0) :
    sIntegerSexticInverseIdealPolynomial K S ζ hζ σ η F u D W =
      sexticRowPolynomial K S ζ hζ σ E hES hE6 η u D W := by
  unfold sIntegerSexticInverseIdealPolynomial sexticRowPolynomial
  congr 1
  calc
    (∑ I ∈ F, sIntegerSexticInverseIdealTerm K S ζ hζ σ η u D W I) =
        ∑ T ∈ E.powerset,
          sIntegerSexticInverseIdealTerm K S ζ hζ σ η u D W (squarefreeIdeal K T) :=
      sIntegerSexticInverseIdealSum_eq_squarefree K S ζ hζ σ η F u E D W hcover hsupport
    _ = ∑ T ∈ E.powerset.attach,
          sIntegerSexticInverseIdealTerm K S ζ hζ σ η u D W (squarefreeIdeal K T.val) :=
      (Finset.sum_attach E.powerset
        (fun T => sIntegerSexticInverseIdealTerm K S ζ hζ σ η u D W
          (squarefreeIdeal K T))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro T _hT
      rw [sIntegerSexticInverseIdealTerm,
        zeroExtendedSexticIdealEvaluation_squarefreeIdeal K S ζ hζ σ E hES hE6
          T.val (Finset.mem_powerset.mp T.property) u]

/-- Exact finite-ideal amplification.  Only the row-one support at D and
the sixth-power-row supports at the finitely many D/q_A are needed.  One
common envelope P union Q and the identical W are retained throughout.
At each required scale F contains ALL nonzero actual summands, including
those potentially outside the envelope. It may also contain zero terms. -/
theorem sIntegerSexticInverseIdealPolynomial_amplification
    (η : HeckeCharacter K) (F : ℝ → Finset (NonzeroIdeal K))
    (P Q : Finset (HeightOneSpectrum (𝓞 K))) (hd : Disjoint P Q)
    (hES : ∀ p ∈ P ∪ Q, p ∉ S)
    (hE6 : ∀ p ∈ P ∪ Q, (6 : 𝓞 K) ∉ p.asIdeal)
    (a : S.integer K)
    (hP : ∀ p ∈ P, p.asIdeal ∣ sIntegerModulusContraction K S a)
    (hQ : ∀ p ∈ Q, ¬p.asIdeal ∣ sIntegerModulusContraction K S a)
    {D : ℝ} (hD : 0 < D) (W : ℝ → ℂ)
    (hcoverOne : ∀ I ∈ F D,
      sIntegerSexticInverseIdealTerm K S ζ hζ σ η 1 D W I ≠ 0 →
        idealPrimeSupport K I ⊆ P ∪ Q)
    (hsupportOne : ∀ I, I ∉ F D →
      sIntegerSexticInverseIdealTerm K S ζ hζ σ η 1 D W I = 0)
    (hcoverPower : ∀ A ∈ P.powerset,
      ∀ I ∈ F (D / idealNorm K (squarefreeIdeal K A)),
        sIntegerSexticInverseIdealTerm K S ζ hζ σ η (a ^ 6)
          (D / idealNorm K (squarefreeIdeal K A)) W I ≠ 0 →
            idealPrimeSupport K I ⊆ P ∪ Q)
    (hsupportPower : ∀ A ∈ P.powerset, ∀ I,
      I ∉ F (D / idealNorm K (squarefreeIdeal K A)) →
          sIntegerSexticInverseIdealTerm K S ζ hζ σ η (a ^ 6)
            (D / idealNorm K (squarefreeIdeal K A)) W I = 0) :
    sIntegerSexticInverseIdealPolynomial K S ζ hζ σ η (F D) 1 D W =
      ∑ A ∈ P.powerset,
        (moebius (squarefreeIdeal K A).val : ℂ) *
          heckeIdealCoefficient K η (squarefreeIdeal K A) *
          (Real.sqrt (idealNorm K (squarefreeIdeal K A)) : ℂ)⁻¹ *
          sIntegerSexticInverseIdealPolynomial K S ζ hζ σ η
            (F (D / idealNorm K (squarefreeIdeal K A))) (a ^ 6)
            (D / idealNorm K (squarefreeIdeal K A)) W := by
  rw [sIntegerSexticInverseIdealPolynomial_eq_rowPolynomial K S ζ hζ σ η
    (F D) 1 (P ∪ Q) hES hE6 D W hcoverOne
      (fun I _hIE hIF => hsupportOne I hIF)]
  rw [sexticRowPolynomial_amplification K S ζ hζ σ P Q hd hES hE6 η a hP hQ hD W]
  apply Finset.sum_congr rfl
  intro A hA
  rw [sIntegerSexticInverseIdealPolynomial_eq_rowPolynomial K S ζ hζ σ η
    (F (D / idealNorm K (squarefreeIdeal K A))) (a ^ 6) (P ∪ Q) hES hE6
    (D / idealNorm K (squarefreeIdeal K A)) W (hcoverPower A hA)
      (fun I _hIE hIF => hsupportPower A hA I hIF)]

end HeckeGeneral.Analysis.SquarefreeAmplification
