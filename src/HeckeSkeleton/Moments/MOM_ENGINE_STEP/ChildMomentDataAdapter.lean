import HeckeSkeleton.Moments.MOM_ENGINE_STEP.JointKernel
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.MomentDataAdapter

/-!
# From actual separated columns to the repository's paired moment

The inputs calibrate individual rows, their images in the actual
nonexceptional row set, and the number of source rows above each ideal.
The energy comparison is proved by the finite fiber sum.  Neither an
energy inequality nor a parent recurrence is an input.

The same row map, fiber bound and weight bound work for every Fourier
parameter.  The actual `MomentData` may vary with that parameter, as its
test profiles do after Fourier separation.  There is no finite-support
assumption on the Fourier parameter.  Once this comparison is applied,
`actual_paired_capacity_step` acts on the same actual `pairedEnergy`.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A bounded actual row fiber and a pointwise polynomial calibration give
the paired-energy comparison uniformly over all Fourier parameters. -/
theorem joint_column_energy_le_actual_paired {H ι : Type*}
    (rows : Finset H) (columns : Finset ι)
    (q : H → ℂ) (c : H → ι → ℂ) (x : H → ι → V)
    (d : V → MomentData K ω ψ) (a : RealParameters) (Z : ℝ) (t : V → ℝ)
    (rowMap : H → NonzeroIdeal K) (W : ℝ) (B : ℕ) (hW : 0 ≤ W)
    (hweight : ∀ h ∈ rows, ‖q h‖ ≤ W)
    (hrows : ∀ ξ : V, ∀ h ∈ rows, rowMap h ∈ pairedRows (d ξ) a Z)
    (hfiber : ∀ u : NonzeroIdeal K,
      (rows.filter (fun h => rowMap h = u)).card ≤ B)
    (hpoly : ∀ ξ : V, ∀ h ∈ rows,
      jointFourierColumn columns (c h) (x h) ξ =
        plainPolynomial (d ξ) (d ξ).plainTest₁ (rowMap h) (Z ^ a.n₁) (t ξ) *
          plainPolynomial (d ξ) (d ξ).plainTest₂ (rowMap h) (Z ^ a.n₂) (t ξ) *
            slotProduct (d ξ) (rowMap h) Z (t ξ)) :
    ∀ ξ : V, jointColumnEnergy rows columns q c x ξ ≤
      W * (B : ℝ) * pairedEnergy (d ξ) a Z (t ξ) := by
  intro ξ
  let P : NonzeroIdeal K → ℂ := fun u =>
    plainPolynomial (d ξ) (d ξ).plainTest₁ u (Z ^ a.n₁) (t ξ) *
      plainPolynomial (d ξ) (d ξ).plainTest₂ u (Z ^ a.n₂) (t ξ) *
        slotProduct (d ξ) u Z (t ξ)
  have he : jointColumnEnergy rows columns q c x ξ =
      weightedEnergy rows (fun h => ‖q h‖) (P ∘ rowMap) := by
    unfold jointColumnEnergy weightedEnergy
    apply Finset.sum_congr rfl
    intro h hh
    rw [hpoly ξ h hh]
    rfl
  have hmass (u : NonzeroIdeal K) :
      (∑ h ∈ rows with rowMap h = u, ‖q h‖) ≤ W * (B : ℝ) := by
    calc
      _ ≤ ∑ _h ∈ rows with rowMap _h = u, W :=
        Finset.sum_le_sum (fun h hh => hweight h (Finset.mem_filter.mp hh).1)
      _ = ((rows.filter (fun h => rowMap h = u)).card : ℝ) * W := by simp
      _ ≤ (B : ℝ) * W :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hfiber u)) hW
      _ = _ := mul_comm _ _
  have hb := weightedEnergy_fiber_bound rows (pairedRows (d ξ) a Z) rowMap
    (fun h => ‖q h‖) (fun _ => W * (B : ℝ)) P (hrows ξ)
    (fun u _ => hmass u)
  rw [he]
  simpa only [weightedEnergy, pairedEnergy, Finset.mul_sum, P, Function.comp_apply] using hb

/-- An injective source-row map has no fiber loss.  All test profiles and
their common masks remain those of the actual child `MomentData`. -/
theorem joint_column_energy_le_actual_paired_of_injective {H ι : Type*}
    (rows : Finset H) (columns : Finset ι)
    (q : H → ℂ) (c : H → ι → ℂ) (x : H → ι → V)
    (d : V → MomentData K ω ψ) (a : RealParameters) (Z : ℝ) (t : V → ℝ)
    (rowMap : H → NonzeroIdeal K) (W : ℝ) (hW : 0 ≤ W)
    (hweight : ∀ h ∈ rows, ‖q h‖ ≤ W)
    (hrows : ∀ ξ : V, ∀ h ∈ rows, rowMap h ∈ pairedRows (d ξ) a Z)
    (hinj : Set.InjOn rowMap (rows : Set H))
    (hpoly : ∀ ξ : V, ∀ h ∈ rows,
      jointFourierColumn columns (c h) (x h) ξ =
        plainPolynomial (d ξ) (d ξ).plainTest₁ (rowMap h) (Z ^ a.n₁) (t ξ) *
          plainPolynomial (d ξ) (d ξ).plainTest₂ (rowMap h) (Z ^ a.n₂) (t ξ) *
            slotProduct (d ξ) (rowMap h) Z (t ξ)) :
    ∀ ξ : V, jointColumnEnergy rows columns q c x ξ ≤
      W * pairedEnergy (d ξ) a Z (t ξ) := by
  have hfiber (u : NonzeroIdeal K) :
      (rows.filter (fun h => rowMap h = u)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro h hh k hk
    exact hinj (Finset.mem_filter.mp hh).1 (Finset.mem_filter.mp hk).1
      ((Finset.mem_filter.mp hh).2.trans (Finset.mem_filter.mp hk).2.symm)
  simpa only [Nat.cast_one, mul_one] using
    joint_column_energy_le_actual_paired rows columns q c x d a Z t rowMap W 1 hW
      hweight hrows hfiber hpoly

end HeckeSkeleton.Moments.EngineStep

end

#print axioms HeckeSkeleton.Moments.EngineStep.joint_column_energy_le_actual_paired
#print axioms HeckeSkeleton.Moments.EngineStep.joint_column_energy_le_actual_paired_of_injective
