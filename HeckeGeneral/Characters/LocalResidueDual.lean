import HeckeGeneral.Characters.PrincipalUnitTopology
import HeckeGeneral.Characters.FiniteCircleFourier

/-! Finite dual groups, depth inflation, and orthogonality for completed local residues. -/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

abbrev LocalResidueDual (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :=
  (LocalResidueRing K v n)ˣ →* Circle

instance finite_localResidueDual (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Finite (LocalResidueDual K v n) := finite_circleDual (LocalResidueRing K v n)ˣ

theorem natCard_localResidueDual (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Nat.card (LocalResidueDual K v n) = Nat.card (LocalResidueRing K v n)ˣ :=
  natCard_circleDual (LocalResidueRing K v n)ˣ

instance finite_localUnitDepthCharacter (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Finite (localUnitDepthCharacter K v n) :=
  Finite.of_equiv (LocalResidueDual K v n) (localUnitDepthCharacterEquiv K v n)

theorem natCard_localUnitDepthCharacter (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Nat.card (localUnitDepthCharacter K v n) = Nat.card (LocalResidueRing K v n)ˣ := by
  rw [← Nat.card_congr (localUnitDepthCharacterEquiv K v n), natCard_localResidueDual]

theorem localUnitDepthCharacter_card_bound (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Nat.card (localUnitDepthCharacter K v n) ≤ residueCard K v ^ n := by
  rw [natCard_localUnitDepthCharacter, ← Nat.card_congr (principalUnitsQuotientEquiv K v n).toEquiv]
  exact principalUnits_index_bound K v n

theorem localResidueDual_separates (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    {x : (LocalResidueRing K v n)ˣ} (hx : x ≠ 1) :
    ∃ ψ : LocalResidueDual K v n, ψ x ≠ 1 := circleDual_separates (LocalResidueRing K v n)ˣ hx

/-- A unit is principal of depth `n` precisely when every depth-`n` character kills it. -/
theorem principalUnits_eq_intersection_character_kernels (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (u : (LocalIntegerRing K v)ˣ) :
    u ∈ principalUnits K v n ↔ ∀ ψ : LocalResidueDual K v n,
      localResidueCharacterLift K v n ψ u = 1 := by
  change localUnitReduction K v n u = 1 ↔ ∀ ψ : LocalResidueDual K v n,
    ψ (localUnitReduction K v n u) = 1
  exact (forall_circleDual_apply_eq_one_iff (LocalResidueRing K v n)ˣ _).symm

def localResidueDualInflation (v : HeightOneSpectrum (𝓞 K)) {m n : ℕ} (hmn : m ≤ n) :
    LocalResidueDual K v m →* LocalResidueDual K v n where
  toFun ψ := ψ.comp (localResidueUnitTransition K v hmn)
  map_one' := by apply MonoidHom.ext; intro x; rfl
  map_mul' ψ θ := by apply MonoidHom.ext; intro x; rfl

theorem localResidueDualInflation_injective (v : HeightOneSpectrum (𝓞 K)) {m n : ℕ}
    (hmn : m ≤ n) : Function.Injective (localResidueDualInflation K v hmn) := by
  intro ψ θ h
  apply MonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := localResidueUnitTransition_surjective K v hmn x
  exact congrArg (fun f : LocalResidueDual K v n => f y) h

theorem localResidueCharacterLift_inflation (v : HeightOneSpectrum (𝓞 K)) {m n : ℕ}
    (hmn : m ≤ n) (ψ : LocalResidueDual K v m) :
    localResidueCharacterLift K v n (localResidueDualInflation K v hmn ψ) =
      localResidueCharacterLift K v m ψ := by
  apply ContinuousMonoidHom.ext
  intro u
  change ψ (localResidueUnitTransition K v hmn (localUnitReduction K v n u)) =
    ψ (localUnitReduction K v m u)
  rw [localResidueUnitTransition_reduction]

theorem localResidueDualInflation_comp (v : HeightOneSpectrum (𝓞 K)) {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) (ψ : LocalResidueDual K v l) :
    localResidueDualInflation K v hmn (localResidueDualInflation K v hlm ψ) =
      localResidueDualInflation K v (hlm.trans hmn) ψ := by
  apply MonoidHom.ext
  intro y
  change ψ (localResidueUnitTransition K v hlm (localResidueUnitTransition K v hmn y)) = _
  exact congrArg (fun f : (LocalResidueRing K v n)ˣ →* (LocalResidueRing K v l)ˣ => ψ (f y))
    (localResidueUnitTransition_comp K v hmn hlm)

def PrimitiveLocalResidueCharacter (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (ψ : LocalResidueDual K v n) : Prop :=
  ∀ m : ℕ, ∀ hmn : m < n, ¬ ∃ θ : LocalResidueDual K v m,
    localResidueDualInflation K v hmn.le θ = ψ

theorem conductorResidueCharacter_isPrimitive (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) :
    PrimitiveLocalResidueCharacter K v (localConductorExponent K χ v)
      (conductorResidueCharacter K v χ) := by
  intro m hm ⟨θ, hθ⟩
  apply conductorResidueCharacter_primitive K v χ hm
  exact ⟨θ, hθ⟩

theorem localResidueDualInflation_range_iff_kernel (v : HeightOneSpectrum (𝓞 K))
    {m n : ℕ} (hmn : m ≤ n) (ψ : LocalResidueDual K v n) :
    ψ ∈ Set.range (localResidueDualInflation K v hmn) ↔
      (localResidueUnitTransition K v hmn).ker ≤ ψ.ker := by
  constructor
  · rintro ⟨θ, rfl⟩ y hy
    change θ (localResidueUnitTransition K v hmn y) = 1
    rw [show localResidueUnitTransition K v hmn y = 1 from hy, map_one]
  · intro h
    let θ := (localResidueUnitTransition K v hmn).liftOfSurjective
      (localResidueUnitTransition_surjective K v hmn) ⟨ψ, h⟩
    refine ⟨θ, MonoidHom.ext fun y => ?_⟩
    exact MonoidHom.liftOfRightInverse_comp_apply (localResidueUnitTransition K v hmn)
      (Function.surjInv (localResidueUnitTransition_surjective K v hmn))
      (Function.rightInverse_surjInv (localResidueUnitTransition_surjective K v hmn)) ⟨ψ, h⟩ y

section Orthogonality

local instance residueUnitFintype (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Fintype (LocalResidueRing K v n)ˣ := Fintype.ofFinite _

local instance residueDualFintype (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Fintype (LocalResidueDual K v n) := Fintype.ofFinite _

theorem localResidueCharacter_orthogonality (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (ψ θ : LocalResidueDual K v n) :
    (∑ u : (LocalResidueRing K v n)ˣ, (ψ u : ℂ) * star (θ u : ℂ)) =
      if ψ = θ then (Nat.card (LocalResidueRing K v n)ˣ : ℂ) else 0 :=
  by
    classical
    exact sum_circleCharacter_mul_conj (LocalResidueRing K v n)ˣ ψ θ

theorem localResidueDual_orthogonality (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (u w : (LocalResidueRing K v n)ˣ) :
    (∑ ψ : LocalResidueDual K v n, (ψ u : ℂ) * (ψ w : ℂ)⁻¹) =
      if u = w then (Nat.card (LocalResidueRing K v n)ˣ : ℂ) else 0 :=
  by
    classical
    have h := sum_circleDual_mul_inv (LocalResidueRing K v n)ˣ u w
    by_cases huw : u = w
    · simpa [huw] using h
    · simpa [huw] using h

theorem localResidueFourier_inversion (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (F : (LocalResidueRing K v n)ˣ → ℂ) :
    finiteFourierInverse _ (finiteFourierCoeff _ F) = F := finiteFourier_inverse_coeff _ F

end Orthogonality

end HeckeGeneral.Characters
