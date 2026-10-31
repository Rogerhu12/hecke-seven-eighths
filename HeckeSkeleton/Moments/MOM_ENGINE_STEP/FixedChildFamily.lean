import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualChildRows

/-!
# Fixed source columns and a genuine Fourier family of children

The source characters, masks, coefficients, finite columns and locations
are fixed before the Fourier parameter.  Only the actual child test
profiles may vary with that parameter.  Slot count and lengths are fixed,
but no equality of the full slot geometry is imposed.

The arithmetic calibration is per ideal and per prime, and records the
actual finite-ray membership in theta.  The polynomial and energy
identities are conclusions of the single-term dictionaries.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}

/-- The arithmetic factors of one fixed source branch. -/
structure FixedChildCharacters (F : Type) [Field F] [NumberField F] (k : ℕ) where
  plain : HeckeCharacter F
  slot : Fin k → HeckeCharacter F
  plainTwist : HeckeCharacter F
  slotTwist : Fin k → HeckeCharacter F
  mask : Ideal (𝓞 F) →* ℂ
  fixedRay : Finset (HeckeCharacter F)
  plainTwist_mem : plainTwist ∈ fixedRay
  slotTwist_mem : ∀ i, slotTwist i ∈ fixedRay

namespace FixedChildCharacters

variable {k : ℕ} {ω ψ : HeckeCharacter F}

/-- Only original one-ideal/one-prime arithmetic identities and actual
theta membership occur in this calibration. -/
structure Calibration (T : FixedChildCharacters F k) (d : MomentData F ω ψ)
    (count : d.geometry.slotCount = k) (u : NonzeroIdeal F) (g h' : A.R) : Prop where
  fixedRay_mem_theta : ∀ θ ∈ T.fixedRay, θ ∈ d.theta
  plain : ∀ I : NonzeroIdeal F,
    heckeIdealCoefficient F (d.plainBackground * d.rowCharacter u) I * maskValue d u I.val =
      sourcePlainCoefficient T.plain T.plainTwist T.mask I *
        actualIdealResidue (A := A) (σ := σ) I.val g *
          actualIdealResidue (A := A) (σ := σ) I.val h'
  slot : ∀ (i : Fin d.geometry.slotCount) (p : HeightOneSpectrum (𝓞 F)),
    primeCoefficient F (d.rowCharacter u * d.slotCoefficient i) p * maskValue d u p.asIdeal =
      sourcePrimeCoefficient (T.slot (Fin.cast count i)) (T.slotTwist (Fin.cast count i)) T.mask p *
        actualIdealResidue (A := A) (σ := σ) p.asIdeal g *
          actualIdealResidue (A := A) (σ := σ) p.asIdeal h'

def Calibration.toDictionary {T : FixedChildCharacters F k} {d : MomentData F ω ψ}
    {count : d.geometry.slotCount = k} {u : NonzeroIdeal F} {g h' : A.R}
    (D : T.Calibration (σ := σ) d count u g h') :
    ChildHeckeTermDictionary (σ := σ) d u g h' where
  sourcePlain := T.plain
  sourceSlot i := T.slot (Fin.cast count i)
  sourceMask := T.mask
  fixedRay := T.fixedRay
  fixedRay_mem_theta := D.fixedRay_mem_theta
  plainTwist := T.plainTwist
  plainTwist_mem := T.plainTwist_mem
  slotTwist i := T.slotTwist (Fin.cast count i)
  slotTwist_mem i := T.slotTwist_mem (Fin.cast count i)
  plain := D.plain
  slot := D.slot

/-- The entire fixed coefficient, with the actual frequency g*h'. -/
def coefficient (T : FixedChildCharacters F k) (g h' : A.R)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : NonzeroIdeal F → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ) :
    (NonzeroIdeal F × NonzeroIdeal F) × (Fin k → HeightOneSpectrum (𝓞 F)) → ℂ :=
  childCartesianCoefficient
    (sourcePlainTerm (σ := σ) T.plain T.plainTwist T.mask g h' w₁ N₁)
    (sourcePlainTerm (σ := σ) T.plain T.plainTwist T.mask g h' w₂ N₂)
    (fun i => sourcePrimeTerm (σ := σ) (T.slot i) (T.slotTwist i) T.mask
      g h' (w i) (Z ^ length i))

end FixedChildCharacters

section Polynomial

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ω ψ : HeckeCharacter F} {k : ℕ}

/-- Transport only the slot indices and lengths.  The prime test profiles
remain those of the actual child, and can vary independently of the
fixed source coefficient. -/
theorem fixed_child_polynomial_from_terms
    (T : FixedChildCharacters F k) (d : MomentData F ω ψ)
    (count : d.geometry.slotCount = k) (length : Fin k → ℝ)
    (hlength : ∀ i, (d.geometry.slots i).length = length (Fin.cast count i))
    (u : NonzeroIdeal F) (g h' : A.R)
    (D : T.Calibration (σ := σ) d count u g h')
    (N₁ N₂ Z t : ℝ)
    (S₁ S₂ : Finset (NonzeroIdeal F))
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 F)))
    (hS₁ : d.plainTest₁.support u t N₁ ⊆ S₁)
    (hS₂ : d.plainTest₂.support u t N₂ ⊆ S₂)
    (hS : ∀ i, (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length) ⊆
      S (Fin.cast count i))
    (w₁ w₂ : NonzeroIdeal F → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (x₁ x₂ : NonzeroIdeal F → V)
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
  have hh := actual_child_polynomial_from_terms d u g h' D.toDictionary
    N₁ N₂ Z t S₁ S₂ S hS₁ hS₂ hS w₁ w₂ w x₁ x₂ x ξ hW₁ hW₂ hW
  simpa only [FixedChildCharacters.coefficient,
    FixedChildCharacters.Calibration.toDictionary, Fin.cast_refl, hlength] using hh

/-- A complete Fourier family has the same source c/x at every
parameter.  Actual row membership follows from the extracted ideal and
its norm identity.  No polynomial or column-energy premise is present. -/
theorem fixed_child_family_energy_from_terms {H : Type*}
    (rows : Finset H) (Ih : H → A.Exterior) (h g : H → A.R) (Q : H → ℝ)
    (r : ∀ j, ActualChildRow (Ih j) (h j) (g j) (Q j))
    (T : H → FixedChildCharacters F k)
    (d : V → MomentData F ω ψ) (a : RealParameters) (Z : ℝ) (t : V → ℝ)
    (count : ∀ ξ, (d ξ).geometry.slotCount = k) (length : Fin k → ℝ)
    (hlength : ∀ ξ i, ((d ξ).geometry.slots i).length = length (Fin.cast (count ξ) i))
    (D : ∀ ξ j, (T j).Calibration (σ := σ) (d ξ) (count ξ)
      (r j).momentIdeal (g j) (r j).element)
    (S₁ S₂ : Finset (NonzeroIdeal F))
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 F)))
    (hS₁ : ∀ ξ, ∀ j ∈ rows, (d ξ).plainTest₁.support
      (r j).momentIdeal (t ξ) (Z ^ a.n₁) ⊆ S₁)
    (hS₂ : ∀ ξ, ∀ j ∈ rows, (d ξ).plainTest₂.support
      (r j).momentIdeal (t ξ) (Z ^ a.n₂) ⊆ S₂)
    (hS : ∀ ξ i, ((d ξ).geometry.slots i).support (t ξ)
      (Z ^ ((d ξ).geometry.slots i).length) ⊆ S (Fin.cast (count ξ) i))
    (w₁ w₂ : H → NonzeroIdeal F → ℂ)
    (w : H → Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (x₁ x₂ : H → NonzeroIdeal F → V)
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
    (hfiber : ∀ u : NonzeroIdeal F,
      (rows.filter (fun j => (r j).momentIdeal = u)).card ≤ B) :
    ∀ ξ, jointColumnEnergy rows (childCartesianColumns S₁ S₂ S) q
      (fun j => (T j).coefficient (σ := σ) (g j) (r j).element
        (Z ^ a.n₁) (Z ^ a.n₂) Z length (w₁ j) (w₂ j) (w j))
      (fun j => childCartesianLocation (x₁ j) (x₂ j) (x j)) ξ ≤
      W * (B : ℝ) * pairedEnergy (d ξ) a Z (t ξ) := by
  intro ξ
  let P : NonzeroIdeal F → ℂ := fun u =>
    plainPolynomial (d ξ) (d ξ).plainTest₁ u (Z ^ a.n₁) (t ξ) *
      plainPolynomial (d ξ) (d ξ).plainTest₂ u (Z ^ a.n₂) (t ξ) *
        slotProduct (d ξ) u Z (t ξ)
  have hpoly (j : H) (hj : j ∈ rows) :=
    fixed_child_polynomial_from_terms (T j) (d ξ) (count ξ) length (hlength ξ)
      (r j).momentIdeal (g j) (r j).element (D ξ j)
      (Z ^ a.n₁) (Z ^ a.n₂) Z (t ξ) S₁ S₂ S
      (hS₁ ξ j hj) (hS₂ ξ j hj) (hS ξ) (w₁ j) (w₂ j) (w j)
      (x₁ j) (x₂ j) (x j) ξ (hW₁ ξ j hj) (hW₂ ξ j hj) (hW ξ j hj)
  have hrows (j : H) (hj : j ∈ rows) : (r j).momentIdeal ∈ pairedRows (d ξ) a Z :=
    (r j).mem_pairedRows (d ξ) a Z (hallowed ξ j hj) (hcutoff j hj) (hexception ξ j hj)
  have hmass (u : NonzeroIdeal F) :
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

end Polynomial

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.fixed_child_polynomial_from_terms
#print axioms HeckeSkeleton.Moments.EngineStep.fixed_child_family_energy_from_terms

