import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FixedChildFamily

/-!
# Exact finite support of the complete child atoms

The smooth norm profile need not vanish at primes removed by an
arithmetic mask. Its full Hecke coefficient times profile and mask does
vanish there. The finite sums below use that actual effective support.
All missing terms are proved to be zero; neither a polynomial identity
nor a source energy estimate is an input.

The original Cartesian source, its occurrence indices and the actual
child profiles remain unchanged. The same proof includes zero slots.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {ω ψ : HeckeCharacter F}

/-- Support of the actual one-ideal summand, with its original mask. -/
def EffectivePlainSupport (d : MomentData F ω ψ) (W : IdealTest F)
    (u : HeckeGeneral.Analysis.NonzeroIdeal F) (N t : ℝ)
    (S : Finset (HeckeGeneral.Analysis.NonzeroIdeal F)) : Prop :=
  ∀ I, heckeIdealCoefficient F (d.plainBackground * d.rowCharacter u) I *
    W.profile u t (idealNorm F I / N) * maskValue d u I.val ≠ 0 → I ∈ S

/-- The moving row is essential here: the actual prime coefficient and
its complete common mask are part of the nonzero test. -/
def EffectivePrimeSupport (d : MomentData F ω ψ)
    (i : Fin d.geometry.slotCount) (u : HeckeGeneral.Analysis.NonzeroIdeal F) (Z t : ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : Prop :=
  ∀ p, primeCoefficient F (d.rowCharacter u * d.slotCoefficient i) p *
    (d.geometry.slots i).profile t
      ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length) *
      maskValue d u p.asIdeal ≠ 0 → p ∈ S

theorem effectivePlainSupport_of_profile (d : MomentData F ω ψ) (W : IdealTest F)
    (u : HeckeGeneral.Analysis.NonzeroIdeal F) (N t : ℝ)
    (S : Finset (HeckeGeneral.Analysis.NonzeroIdeal F))
    (hS : W.support u t N ⊆ S) : EffectivePlainSupport d W u N t S := by
  intro I hI
  apply hS
  apply (W.support_spec u t N I).mpr
  intro hz
  exact hI (by rw [hz, mul_zero, zero_mul])

theorem effectivePrimeSupport_of_profile (d : MomentData F ω ψ)
    (i : Fin d.geometry.slotCount) (u : HeckeGeneral.Analysis.NonzeroIdeal F) (Z t : ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length) ⊆ S) :
    EffectivePrimeSupport d i u Z t S := by
  intro p hp
  apply hS
  apply ((d.geometry.slots i).support_spec t _ p).mpr
  intro hz
  exact hp (by rw [hz, mul_zero, zero_mul])

private theorem finite_sum_effective_support {X M : Type*} [AddCommMonoid M]
    (S T : Finset X) (f : X → M)
    (hS : ∀ x, f x ≠ 0 → x ∈ S) (hT : ∀ x, f x ≠ 0 → x ∈ T) :
    (∑ x ∈ S, f x) = ∑ x ∈ T, f x := by
  calc
    _ = ∑ x ∈ S ∪ T, f x := by
      apply Finset.sum_subset Finset.subset_union_left
      intro x _ hx
      by_contra hne
      exact hx (hS x hne)
    _ = _ := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro x _ hx
      by_contra hne
      exact hx (hT x hne)

/-- Exact finite zero extension at the level of individual ideal
summands. Pure profile support is not required to lie in the source. -/
theorem plainPolynomial_effective_support (d : MomentData F ω ψ) (W : IdealTest F)
    (u : HeckeGeneral.Analysis.NonzeroIdeal F) (N t : ℝ)
    (S : Finset (HeckeGeneral.Analysis.NonzeroIdeal F))
    (hS : EffectivePlainSupport d W u N t S) :
    plainPolynomial d W u N t =
      ∑ I ∈ S, (Real.sqrt N : ℂ)⁻¹ *
        (heckeIdealCoefficient F (d.plainBackground * d.rowCharacter u) I *
          W.profile u t (idealNorm F I / N) * maskValue d u I.val) := by
  rw [plainPolynomial, ← Finset.mul_sum]
  congr 1
  apply finite_sum_effective_support _ _ _ _ hS
  intro I hI
  apply (W.support_spec u t N I).mpr
  intro hz
  exact hI (by rw [hz, mul_zero, zero_mul])

theorem primePolynomial_effective_support (d : MomentData F ω ψ)
    (i : Fin d.geometry.slotCount) (u : HeckeGeneral.Analysis.NonzeroIdeal F) (Z t : ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : EffectivePrimeSupport d i u Z t S) :
    primePolynomial d i u Z t =
      ∑ p ∈ S, (Real.sqrt (Z ^ (d.geometry.slots i).length) : ℂ)⁻¹ *
        (primeCoefficient F (d.rowCharacter u * d.slotCoefficient i) p *
          (d.geometry.slots i).profile t
            ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length) *
              maskValue d u p.asIdeal) := by
  rw [primePolynomial, ← Finset.mul_sum]
  congr 1
  apply finite_sum_effective_support _ _ _ _ hS
  intro p hp
  apply ((d.geometry.slots i).support_spec t _ p).mpr
  intro hz
  exact hp (by rw [hz, mul_zero, zero_mul])

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem actual_child_polynomial_from_effective_terms (d : MomentData F ω ψ)
    (u : HeckeGeneral.Analysis.NonzeroIdeal F) (g h' : A.R)
    (D : ChildHeckeTermDictionary (σ := σ) d u g h')
    (N₁ N₂ Z t : ℝ)
    (S₁ S₂ : Finset (HeckeGeneral.Analysis.NonzeroIdeal F))
    (S : Fin d.geometry.slotCount → Finset (HeightOneSpectrum (𝓞 F)))
    (hS₁ : EffectivePlainSupport d d.plainTest₁ u N₁ t S₁)
    (hS₂ : EffectivePlainSupport d d.plainTest₂ u N₂ t S₂)
    (hS : ∀ i, EffectivePrimeSupport d i u Z t (S i))
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (w : Fin d.geometry.slotCount → HeightOneSpectrum (𝓞 F) → ℂ)
    (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal F → V)
    (x : Fin d.geometry.slotCount → HeightOneSpectrum (𝓞 F) → V) (ξ : V)
    (hW₁ : ∀ I ∈ S₁, w₁ I * jointPhase ξ (x₁ I) =
      d.plainTest₁.profile u t (idealNorm F I / N₁))
    (hW₂ : ∀ I ∈ S₂, w₂ I * jointPhase ξ (x₂ I) =
      d.plainTest₂.profile u t (idealNorm F I / N₂))
    (hW : ∀ i, ∀ p ∈ S i, w i p * jointPhase ξ (x i p) =
      (d.geometry.slots i).profile t
        ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length)) :
    jointFourierColumn (childCartesianColumns S₁ S₂ S)
      (childCartesianCoefficient
        (sourcePlainTerm (σ := σ) D.sourcePlain D.plainTwist D.sourceMask g h' w₁ N₁)
        (sourcePlainTerm (σ := σ) D.sourcePlain D.plainTwist D.sourceMask g h' w₂ N₂)
        (fun i => sourcePrimeTerm (σ := σ) (D.sourceSlot i) (D.slotTwist i) D.sourceMask
          g h' (w i) (Z ^ (d.geometry.slots i).length)))
      (childCartesianLocation x₁ x₂ x) ξ =
      plainPolynomial d d.plainTest₁ u N₁ t *
        plainPolynomial d d.plainTest₂ u N₂ t * slotProduct d u Z t := by
  rw [joint_cartesian_column_factorization,
    plainPolynomial_effective_support d d.plainTest₁ u N₁ t S₁ hS₁,
    plainPolynomial_effective_support d d.plainTest₂ u N₂ t S₂ hS₂, slotProduct]
  have h₁ : (∑ I ∈ S₁,
      sourcePlainTerm (σ := σ) D.sourcePlain D.plainTwist D.sourceMask g h' w₁ N₁ I *
        jointPhase ξ (x₁ I)) =
      ∑ I ∈ S₁, (Real.sqrt N₁ : ℂ)⁻¹ *
        (heckeIdealCoefficient F (d.plainBackground * d.rowCharacter u) I *
          d.plainTest₁.profile u t (idealNorm F I / N₁) * maskValue d u I.val) := by
    apply Finset.sum_congr rfl
    intro I hI
    exact sourcePlainTerm_calibrated d u g h' D d.plainTest₁ w₁ x₁ ξ N₁ t I (hW₁ I hI)
  have h₂ : (∑ I ∈ S₂,
      sourcePlainTerm (σ := σ) D.sourcePlain D.plainTwist D.sourceMask g h' w₂ N₂ I *
        jointPhase ξ (x₂ I)) =
      ∑ I ∈ S₂, (Real.sqrt N₂ : ℂ)⁻¹ *
        (heckeIdealCoefficient F (d.plainBackground * d.rowCharacter u) I *
          d.plainTest₂.profile u t (idealNorm F I / N₂) * maskValue d u I.val) := by
    apply Finset.sum_congr rfl
    intro I hI
    exact sourcePlainTerm_calibrated d u g h' D d.plainTest₂ w₂ x₂ ξ N₂ t I (hW₂ I hI)
  rw [h₁, h₂]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [primePolynomial_effective_support d i u Z t (S i) (hS i)]
  apply Finset.sum_congr rfl
  intro p hp
  exact sourcePrimeTerm_calibrated d u g h' D i (w i) (x i) ξ Z t p (hW i p hp)

variable {k : ℕ}

theorem fixed_child_polynomial_from_effective_terms
    (T : FixedChildCharacters F k) (d : MomentData F ω ψ)
    (count : d.geometry.slotCount = k) (length : Fin k → ℝ)
    (hlength : ∀ i, (d.geometry.slots i).length = length (Fin.cast count i))
    (u : HeckeGeneral.Analysis.NonzeroIdeal F) (g h' : A.R)
    (D : T.Calibration (σ := σ) d count u g h')
    (N₁ N₂ Z t : ℝ)
    (S₁ S₂ : Finset (HeckeGeneral.Analysis.NonzeroIdeal F))
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 F)))
    (hS₁ : EffectivePlainSupport d d.plainTest₁ u N₁ t S₁)
    (hS₂ : EffectivePlainSupport d d.plainTest₂ u N₂ t S₂)
    (hS : ∀ i, EffectivePrimeSupport d i u Z t (S (Fin.cast count i)))
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal F → V)
    (x : Fin k → HeightOneSpectrum (𝓞 F) → V) (ξ : V)
    (hW₁ : ∀ I ∈ S₁, w₁ I * jointPhase ξ (x₁ I) =
      d.plainTest₁.profile u t (idealNorm F I / N₁))
    (hW₂ : ∀ I ∈ S₂, w₂ I * jointPhase ξ (x₂ I) =
      d.plainTest₂.profile u t (idealNorm F I / N₂))
    (hW : ∀ i, ∀ p ∈ S (Fin.cast count i),
      w (Fin.cast count i) p * jointPhase ξ (x (Fin.cast count i) p) =
        (d.geometry.slots i).profile t
          ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length)) :
    jointFourierColumn (childCartesianColumns S₁ S₂ S)
      (T.coefficient (σ := σ) g h' N₁ N₂ Z length w₁ w₂ w)
      (childCartesianLocation x₁ x₂ x) ξ =
      plainPolynomial d d.plainTest₁ u N₁ t *
        plainPolynomial d d.plainTest₂ u N₂ t * slotProduct d u Z t := by
  subst k
  have hh := actual_child_polynomial_from_effective_terms d u g h' D.toDictionary
    N₁ N₂ Z t S₁ S₂ S hS₁ hS₂ hS w₁ w₂ w x₁ x₂ x ξ hW₁ hW₂ hW
  simpa only [FixedChildCharacters.coefficient,
    FixedChildCharacters.Calibration.toDictionary, Fin.cast_refl, id_eq, hlength] using hh

/-- A complete Fourier family has the same source c/x at every
parameter.  Actual row membership follows from the extracted ideal and
its norm identity.  No polynomial or column-energy premise is present. -/
theorem fixed_child_family_energy_from_effective_terms {H : Type*}
    (rows : Finset H) (Ih : H → A.Exterior) (h g : H → A.R) (Q : H → ℝ)
    (r : ∀ j, ActualChildRow (Ih j) (h j) (g j) (Q j))
    (T : H → FixedChildCharacters F k)
    (d : V → MomentData F ω ψ) (a : RealParameters) (Z : ℝ) (t : V → ℝ)
    (count : ∀ ξ, (d ξ).geometry.slotCount = k) (length : Fin k → ℝ)
    (hlength : ∀ ξ i, ((d ξ).geometry.slots i).length = length (Fin.cast (count ξ) i))
    (D : ∀ ξ j, (T j).Calibration (σ := σ) (d ξ) (count ξ)
      (r j).momentIdeal (g j) (r j).element)
    (S₁ S₂ : Finset (HeckeGeneral.Analysis.NonzeroIdeal F))
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 F)))
    (hS₁ : ∀ ξ, ∀ j ∈ rows, EffectivePlainSupport (d ξ) (d ξ).plainTest₁
      (r j).momentIdeal (Z ^ a.n₁) (t ξ) S₁)
    (hS₂ : ∀ ξ, ∀ j ∈ rows, EffectivePlainSupport (d ξ) (d ξ).plainTest₂
      (r j).momentIdeal (Z ^ a.n₂) (t ξ) S₂)
    (hS : ∀ ξ, ∀ j ∈ rows, ∀ i,
      EffectivePrimeSupport (d ξ) i (r j).momentIdeal Z (t ξ) (S (Fin.cast (count ξ) i)))
    (w₁ w₂ : H → HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (w : H → Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (x₁ x₂ : H → HeckeGeneral.Analysis.NonzeroIdeal F → V)
    (x : H → Fin k → HeightOneSpectrum (𝓞 F) → V)
    (hW₁ : ∀ ξ, ∀ j ∈ rows, ∀ I ∈ S₁,
      w₁ j I * jointPhase ξ (x₁ j I) =
        (d ξ).plainTest₁.profile (r j).momentIdeal (t ξ) (idealNorm F I / Z ^ a.n₁))
    (hW₂ : ∀ ξ, ∀ j ∈ rows, ∀ I ∈ S₂,
      w₂ j I * jointPhase ξ (x₂ j I) =
        (d ξ).plainTest₂.profile (r j).momentIdeal (t ξ) (idealNorm F I / Z ^ a.n₂))
    (hW : ∀ ξ, ∀ j ∈ rows, ∀ i, ∀ p ∈ S (Fin.cast (count ξ) i),
      w j (Fin.cast (count ξ) i) p * jointPhase ξ (x j (Fin.cast (count ξ) i) p) =
        ((d ξ).geometry.slots i).profile (t ξ)
          ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ ((d ξ).geometry.slots i).length))
    (q : H → ℂ) (W : ℝ) (B : ℕ) (hWnonneg : 0 ≤ W)
    (hweight : ∀ j ∈ rows, ‖q j‖ ≤ W)
    (hallowed : ∀ ξ, ∀ j ∈ rows, (d ξ).allowedRow (r j).momentIdeal)
    (hcutoff : ∀ j ∈ rows, A.exteriorNorm (Ih j) ≤ Q j * Z ^ (a.m + a.q))
    (hexception : ∀ ξ, ∀ j ∈ rows,
      if a.z = 0 then (d ξ).plainBackground * (d ξ).rowCharacter (r j).momentIdeal ≠ 1
      else (d ξ).rowCharacter (r j).momentIdeal ∉ (d ξ).theta)
    (hfiber : ∀ u : HeckeGeneral.Analysis.NonzeroIdeal F,
      (rows.filter (fun j => (r j).momentIdeal = u)).card ≤ B) :
    ∀ ξ, jointColumnEnergy rows (childCartesianColumns S₁ S₂ S) q
      (fun j => (T j).coefficient (σ := σ) (g j) (r j).element
        (Z ^ a.n₁) (Z ^ a.n₂) Z length (w₁ j) (w₂ j) (w j))
      (fun j => childCartesianLocation (x₁ j) (x₂ j) (x j)) ξ ≤
      W * (B : ℝ) * pairedEnergy (d ξ) a Z (t ξ) := by
  intro ξ
  let P : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ := fun u =>
    plainPolynomial (d ξ) (d ξ).plainTest₁ u (Z ^ a.n₁) (t ξ) *
      plainPolynomial (d ξ) (d ξ).plainTest₂ u (Z ^ a.n₂) (t ξ) *
        slotProduct (d ξ) u Z (t ξ)
  have hpoly (j : H) (hj : j ∈ rows) :=
    fixed_child_polynomial_from_effective_terms (T j) (d ξ) (count ξ) length (hlength ξ)
      (r j).momentIdeal (g j) (r j).element (D ξ j)
      (Z ^ a.n₁) (Z ^ a.n₂) Z (t ξ) S₁ S₂ S
      (hS₁ ξ j hj) (hS₂ ξ j hj) (hS ξ j hj) (w₁ j) (w₂ j) (w j)
      (x₁ j) (x₂ j) (x j) ξ (hW₁ ξ j hj) (hW₂ ξ j hj) (hW ξ j hj)
  have hrows (j : H) (hj : j ∈ rows) : (r j).momentIdeal ∈ pairedRows (d ξ) a Z :=
    (r j).mem_pairedRows (d ξ) a Z (hallowed ξ j hj) (hcutoff j hj) (hexception ξ j hj)
  have hmass (u : HeckeGeneral.Analysis.NonzeroIdeal F) :
      (∑ j ∈ rows with (r j).momentIdeal = u, ‖q j‖) ≤ W * (B : ℝ) := by
    calc
      _ ≤ ∑ _j ∈ rows with (r _j).momentIdeal = u, W :=
        Finset.sum_le_sum (fun j hj => hweight j (Finset.mem_filter.mp hj).1)
      _ = ((rows.filter (fun j => (r j).momentIdeal = u)).card : ℝ) * W := by simp
      _ ≤ (B : ℝ) * W := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hfiber u)) hWnonneg
      _ = _ := mul_comm _ _
  have hb := weightedEnergy_fiber_bound rows (pairedRows (d ξ) a Z)
    (fun j => (r j).momentIdeal) (fun j => ‖q j‖) (fun _ => W * (B : ℝ))
    P hrows (fun u _ => hmass u)
  have he : jointColumnEnergy rows (childCartesianColumns S₁ S₂ S) q
      (fun j => (T j).coefficient (σ := σ) (g j) (r j).element
        (Z ^ a.n₁) (Z ^ a.n₂) Z length (w₁ j) (w₂ j) (w j))
      (fun j => childCartesianLocation (x₁ j) (x₂ j) (x j)) ξ =
      weightedEnergy rows (fun j => ‖q j‖) (fun j => P (r j).momentIdeal) := by
    unfold jointColumnEnergy weightedEnergy
    apply Finset.sum_congr rfl
    intro j hj
    rw [hpoly j hj]
  rw [he]
  simpa only [weightedEnergy, pairedEnergy, Finset.mul_sum, P, Function.comp_apply] using hb

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.plainPolynomial_effective_support
#print axioms HeckeSkeleton.Moments.EngineStep.actual_child_polynomial_from_effective_terms
#print axioms HeckeSkeleton.Moments.EngineStep.fixed_child_family_energy_from_effective_terms
