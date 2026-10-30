import HeckePort.Moments.Descent.MixedRow
import HeckePort.Moments.Descent.MarkedStratum

/-!
# Controlled local multipliers

Port of the formal part of openai/math `OAI/NumberTheory/DirichletL/Descent/ControlledMultiplier.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`.

openai evaluates, for a `ControlledStratumArithmetic` datum `D` of the cubic Eisenstein field, the
sum over the units `v` of the residue rings `Eis ⧸ span {p i}` of the local Fourier weight times
the conjugate Gauss character `star (complexCharacter (D.relativeGamma …))` times the cusp phase
`breveE (…)`.  The arithmetic input is `controlled_phase_product` (a `ℤ[ω]` Jacobi/Kubota identity,
`A3_A4_frequency_product`); it is the hypothesis `hphase` below (the phase factors as a fixed factor
times a product of the local multipliers `frequencyMultiplier`).  The rest is formal and ported:

* `fullLocalFourierWeight` and `controlled_local_multiplier_of_phase` (the `Fintype.prod_sum`
  interchange of `controlled_local_multiplier`);
* `mixedPrimeFunction_units`: the per-slot identity of `mixedActiveBracket_eq_units`, i.e. the
  Fourier-coefficient/multiplier sum for the mixed prime function is the sum of the
  `mixedFrequencyRow` over the units, whose closed form is `mixed_frequency_units`;
* `controlled_mixed_multiplier_of_phase`: their combination.
-/

noncomputable section

namespace HeckePort.Moments

open scoped BigOperators Classical

section Product

variable {ι : Type*} [Fintype ι]

def fullLocalFourierWeight {V : ι → Type*} (coeff : ∀ i, V i → ℂ) (v : ∀ i, V i) : ℂ :=
  ∏ i, coeff i (v i)

theorem controlled_local_multiplier_of_phase {V : ι → Type*} [∀ i, Fintype (V i)]
    (coeff mult : ∀ i, V i → ℂ) (Phase : (∀ i, V i) → ℂ) (c : ℂ)
    (hphase : ∀ v, Phase v = c * ∏ i, mult i (v i)) :
    (∑ v : ∀ i, V i, fullLocalFourierWeight coeff v * Phase v) =
      c * ∏ i, ∑ w : V i, coeff i w * mult i w := by
  rw [Fintype.prod_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [hphase v, fullLocalFourierWeight, Finset.prod_mul_distrib]
  ring

/-- openai `controlled_mixed_multiplier`, given the closed form `brk i` of each local sum
(`mixedActiveBracket_eq_units`) and the phase factorization. -/
theorem controlled_mixed_multiplier_of_phase {V : ι → Type*} [∀ i, Fintype (V i)]
    (coeff mult : ∀ i, V i → ℂ) (Phase : (∀ i, V i) → ℂ) (c : ℂ) (brk : ι → ℂ)
    (hphase : ∀ v, Phase v = c * ∏ i, mult i (v i))
    (hbrk : ∀ i, (∑ w : V i, coeff i w * mult i w) = brk i) :
    (∑ v : ∀ i, V i, fullLocalFourierWeight coeff v * Phase v) = c * ∏ i, brk i := by
  rw [controlled_local_multiplier_of_phase coeff mult Phase c hphase]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => hbrk i)

end Product

section Local

variable {F : Type*} [Field F] [Fintype F]

/-- The mixed prime function of one slot: the zero mark if the slot is marked, the power of
the character otherwise. -/
def mixedSlotFunction (χ : MulChar F ℂ) (j : ℕ) (marked : Bool) (t : F) : ℂ :=
  if marked then zeroMark t else (χ ^ j) t

theorem mixedPrimeFunction_units (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) (σ ε : Fˣ)
    (x : F) (marked : Bool) :
    (∑ v : Fˣ, finiteAdditiveFourierCoeff ψ (mixedSlotFunction χ j marked) v *
      frequencyMultiplier χ ψ σ ε x v) =
      ∑ v : Fˣ, mixedFrequencyRow χ ψ marked j σ ε x v := by
  cases marked
  · have h : mixedSlotFunction χ j false = fun t => (χ ^ j) t := by
      funext t; simp [mixedSlotFunction]
    rw [h]
    simp [mixedFrequencyRow, frequencyRow]
  · have h : mixedSlotFunction χ j true = zeroMark := by
      funext t; simp [mixedSlotFunction]
    rw [h]
    simp [mixedFrequencyRow, markedFrequencyRow]

/-- openai `mixedActiveBracket_eq_units`: with the closed forms of `mixed_frequency_units`. -/
theorem mixedActiveBracket_eq_units (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) (σ ε : Fˣ)
    (x : F) (marked : Bool) (Am Au : ℂ)
    (hmarked : localReflectionActive zeroMark χ ψ σ ε x = Am)
    (hunits : (∑ h : Fˣ, frequencyRow χ ψ j σ ε x h) = Au) :
    (∑ v : Fˣ, finiteAdditiveFourierCoeff ψ (mixedSlotFunction χ j marked) v *
      frequencyMultiplier χ ψ σ ε x v) = if marked then Am else Au := by
  rw [mixedPrimeFunction_units]
  exact mixed_frequency_units χ ψ j σ ε x Am Au hmarked hunits marked

end Local

end HeckePort.Moments

end
