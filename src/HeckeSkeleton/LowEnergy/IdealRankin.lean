import HeckeSkeleton.LowEnergy.IdealRows
import HeckeSkeleton.LowEnergy.Rankin
import HeckeSkeleton.LowEnergy.IdealMajorant

/-!
# Powerful-ideal counting for every number field

These are actual ideals of `𝓞 K`; no class number one, principal ideal,
unique-factorization-of-elements, or sieve hypothesis occurs.

The proof uses the canonical injective square--cube decomposition from
`IdealRows.lean` and the proved Dedekind-zeta majorant from
`HeckeSkeleton.LowEnergy.IdealMajorant`. The same constant controls both
`# {powerful I : NI ≤ X}` and the weighted `sum (NI)^(-1/2)` budget.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowEnergy.IdealRankin

open NumberField HeckeSkeleton.LowEnergy.IdealRows
open scoped Classical BigOperators nonZeroDivisors NumberField

variable (K : Type*) [Field K] [NumberField K]

abbrev PowerfulIdeal := {I : (Ideal (𝓞 K))⁰ // Powerful I}

def idealNorm (I : (Ideal (𝓞 K))⁰) : ℝ := I.val.absNorm

def powerfulNorm (I : PowerfulIdeal K) : ℝ := idealNorm K I.val

theorem idealNorm_pos (I : (Ideal (𝓞 K))⁰) : 0 < idealNorm K I := by
  change (0 : ℝ) < (I.val.absNorm : ℝ)
  exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I

theorem powerfulNorm_pos (I : PowerfulIdeal K) : 0 < powerfulNorm K I :=
  idealNorm_pos K I.val

/-- The half-plane `s > 1/2` is the exact range needed by the elementary
square--cube majorant. The cube squarefreeness is safely dropped in the bound. -/
theorem summable_powerful_ideal_norm_rpow {s : ℝ} (hs : (1 / 2 : ℝ) < s) :
    Summable (fun I : PowerfulIdeal K => powerfulNorm K I ^ (-s)) := by
  apply Rankin.summable_square_cube (idealNorm K) (powerfulNorm K)
    (powerfulPair (R := 𝓞 K)) (fun I => (idealNorm_pos K I).le) powerfulPair_injective
  · intro I
    exact norm_powerful_decomposition I.val I.property
  · exact HeckeSkeleton.LowEnergy.summable_nonzeroIdeal_norm_rpow K (show 1 < 2 * s by linarith)
  · exact HeckeSkeleton.LowEnergy.summable_nonzeroIdeal_norm_rpow K (show 1 < 3 * s by linarith)

/-- Both powerful-ideal budgets are proved from number-field zeta convergence.
No target energy estimate appears among the assumptions. -/
theorem powerful_count_and_half_mass (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset (PowerfulIdeal K)) (X : ℝ), 1 ≤ X →
      (∀ I ∈ s, powerfulNorm K I ≤ X) →
      (s.card : ℝ) ≤ C * X ^ ((1 / 2 : ℝ) + eps) ∧
      (∑ I ∈ s, powerfulNorm K I ^ (-(1 / 2 : ℝ))) ≤ C * X ^ eps :=
  Rankin.cardinality_and_half_mass (powerfulNorm K) (powerfulNorm_pos K) eps heps
    (summable_powerful_ideal_norm_rpow K (by linarith))

/-- The same result on the ambient nonzero-ideal type, with the hypotheses
on each member of the actual finite set. This is convenient for row fibres. -/
theorem powerful_count_and_half_mass_on_finset (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset (Ideal (𝓞 K))⁰) (X : ℝ), 1 ≤ X →
      (∀ I ∈ s, Powerful I ∧ idealNorm K I ≤ X) →
      (s.card : ℝ) ≤ C * X ^ ((1 / 2 : ℝ) + eps) ∧
      (∑ I ∈ s, idealNorm K I ^ (-(1 / 2 : ℝ))) ≤ C * X ^ eps := by
  obtain ⟨C, hC, hbound⟩ := powerful_count_and_half_mass K eps heps
  refine ⟨C, hC, ?_⟩
  intro s X hX hs
  let e : s ↪ PowerfulIdeal K :=
    ⟨fun I => ⟨I.val, (hs I.val I.property).1⟩,
      fun I J h => Subtype.ext (congrArg (fun A : PowerfulIdeal K => A.val) h)⟩
  let t : Finset (PowerfulIdeal K) := s.attach.map e
  have ht : ∀ I ∈ t, powerfulNorm K I ≤ X := by
    intro I hI
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_map.mp hI
    exact (hs J.val J.property).2
  have h := hbound t X hX ht
  constructor
  · simpa only [t, Finset.card_map, Finset.card_attach] using h.1
  · have hh := h.2
    simp only [t, Finset.sum_map] at hh
    change (∑ I ∈ s.attach, idealNorm K I.val ^ (-(1 / 2 : ℝ))) ≤ C * X ^ eps at hh
    rw [Finset.sum_attach s (fun I => idealNorm K I ^ (-(1 / 2 : ℝ)))] at hh
    exact hh

/-- The actual half-norm budget also absorbs a fixed nonnegative power
arising from the local-state count. -/
theorem powerful_weighted_half_mass (eps rho : ℝ) (heps : 0 < eps) (hrho : 0 ≤ rho) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset (Ideal (𝓞 K))⁰) (X : ℝ), 1 ≤ X →
      (∀ I ∈ s, Powerful I ∧ idealNorm K I ≤ X) →
      (∑ I ∈ s, idealNorm K I ^ (-(1 / 2 : ℝ) + rho)) ≤ C * X ^ (eps + rho) := by
  obtain ⟨C, hC, hbound⟩ := powerful_count_and_half_mass_on_finset K eps heps
  refine ⟨C, hC, ?_⟩
  intro s X hX hs
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  calc
    _ ≤ ∑ I ∈ s, idealNorm K I ^ (-(1 / 2 : ℝ)) * X ^ rho := by
      apply Finset.sum_le_sum
      intro I hI
      rw [Real.rpow_add (idealNorm_pos K I)]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (idealNorm_pos K I).le (hs I hI).2 hrho)
        (Real.rpow_nonneg (idealNorm_pos K I).le _)
    _ = (∑ I ∈ s, idealNorm K I ^ (-(1 / 2 : ℝ))) * X ^ rho :=
      (Finset.sum_mul ..).symm
    _ ≤ (C * X ^ eps) * X ^ rho := mul_le_mul_of_nonneg_right
      (hbound s X hX hs).2 (Real.rpow_nonneg hXpos.le _)
    _ = C * X ^ (eps + rho) := by rw [Real.rpow_add hXpos]; ring

/-- The powerful part never enlarges the norm of the original physical row. -/
theorem idealNorm_powerfulPart_le (I : (Ideal (𝓞 K))⁰) :
    idealNorm K (powerfulPart I) ≤ idealNorm K I := by
  have hd : Ideal.absNorm (powerfulPart I).val ∣ Ideal.absNorm I.val :=
    map_dvd Ideal.absNorm (powerfulPart_dvd I)
  change ((powerfulPart I).val.absNorm : ℝ) ≤ (I.val.absNorm : ℝ)
  exact_mod_cast Nat.le_of_dvd (Ideal.absNorm_pos_of_nonZeroDivisors I) hd

/-- The weighted powerful-part budget on any genuine set of physical ideals.
An image finset counts each frozen powerful part exactly once. -/
theorem powerful_part_half_mass (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset (Ideal (𝓞 K))⁰) (X : ℝ), 1 ≤ X →
      (∀ I ∈ s, idealNorm K I ≤ X) →
      (∑ A ∈ s.image powerfulPart, idealNorm K A ^ (-(1 / 2 : ℝ))) ≤ C * X ^ eps := by
  obtain ⟨C, hC, hbound⟩ := powerful_count_and_half_mass_on_finset K eps heps
  refine ⟨C, hC, ?_⟩
  intro s X hX hs
  apply (hbound (s.image powerfulPart) X hX ?_).2
  intro A hA
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hA
  exact ⟨powerfulPart_powerful I, (idealNorm_powerfulPart_le K I).trans (hs I hI)⟩

/-- Exponent allocation for any fixed ambient row length. -/
theorem powerful_part_half_mass_at_scale (L eps : ℝ) (hL : 0 ≤ L) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset (Ideal (𝓞 K))⁰) (Z : ℝ), 1 ≤ Z →
      (∀ I ∈ s, idealNorm K I ≤ Z ^ L) →
      (∑ A ∈ s.image powerfulPart, idealNorm K A ^ (-(1 / 2 : ℝ))) ≤ C * Z ^ eps := by
  let delta := eps / (L + 1)
  have hdelta : 0 < delta := div_pos heps (by linarith)
  obtain ⟨C, hC, hbound⟩ := powerful_part_half_mass K delta hdelta
  refine ⟨C, hC, ?_⟩
  intro s Z hZ hs
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have h := hbound s (Z ^ L) (Real.one_le_rpow hZ hL) hs
  have hprod : L * delta ≤ eps := by
    have he : delta * (L + 1) = eps := by dsimp [delta]; field_simp
    nlinarith
  calc
    _ ≤ C * (Z ^ L) ^ delta := h
    _ = C * Z ^ (L * delta) := by rw [← Real.rpow_mul hz.le]
    _ ≤ C * Z ^ eps := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ hprod) hC.le

#print axioms summable_powerful_ideal_norm_rpow
#print axioms powerful_count_and_half_mass
#print axioms powerful_count_and_half_mass_on_finset
#print axioms powerful_weighted_half_mass
#print axioms idealNorm_powerfulPart_le
#print axioms powerful_part_half_mass
#print axioms powerful_part_half_mass_at_scale

end HeckeSkeleton.LowEnergy.IdealRankin
