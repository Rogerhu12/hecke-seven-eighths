import HeckePort.CenteredMoment.IdealMobius
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Finite ideal Möbius inversion for cube completion

The inversion below is on the actual ideal monoid of the ring of integers.
Its arithmetic input is the proved divisor sum for the ideal Möbius function.
Finite support is an intermediate algebraic hypothesis; `CubeInversion`
discharges it for every compactly supported test and arbitrary whole-index
weight.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_BASE

open scoped NumberField Classical BigOperators
open UniqueFactorizationMonoid DedekindZetaZeroFree.LargeSieve
open HeckePort.IdealMobiusDivisorSum

variable {K : Type*} [Field K] [NumberField K]

/-- Multiplication by a nonzero ideal enumerates its divisible ideals
without repetition. This requires no summability assumption. -/
theorem cube_tsum_ideal_divisible (H : Ideal (𝓞 K)) (hH : H ≠ ⊥)
    (f : Ideal (𝓞 K) → ℂ) :
    (∑' I : Ideal (𝓞 K), if H ∣ I then f I else 0) =
      ∑' B : Ideal (𝓞 K), f (H * B) := by
  let F : Ideal (𝓞 K) → ℂ := fun I => if H ∣ I then f I else 0
  have hrange : Function.support F ⊆ Set.range (fun B : Ideal (𝓞 K) => H * B) := by
    intro I hI
    have hd : H ∣ I := by
      by_contra hn
      exact hI (by simp only [F, ite_eq_right hn])
    obtain ⟨B, hB⟩ := hd
    exact ⟨B, hB.symm⟩
  have ht := (mul_right_injective₀ hH).tsum_eq hrange
  calc
    _ = ∑' B : Ideal (𝓞 K), F (H * B) := ht.symm
    _ = _ := by
      apply tsum_congr
      intro B
      simp only [F, dvd_mul_right, ite_true]

/-- The finite divisor pool of a finite ideal family. -/
def cubeDivisorPool (T : Finset (Ideal (𝓞 K))) : Finset (Ideal (𝓞 K)) :=
  T.biUnion idealDivisors

theorem cubeDivisorPool_mem {T : Finset (Ideal (𝓞 K))}
    {I H : Ideal (𝓞 K)} (hI : I ∈ T) (hI0 : I ≠ ⊥) (hHI : H ∣ I) :
    H ∈ cubeDivisorPool T :=
  Finset.mem_biUnion.mpr ⟨I, hI, (mem_idealDivisors hI0).mpr hHI⟩

theorem cubeDivisorPool_ne_zero {T : Finset (Ideal (𝓞 K))}
    {H : Ideal (𝓞 K)} (hH : H ∈ cubeDivisorPool T) : H ≠ ⊥ := by
  obtain ⟨I, _, hHI⟩ := Finset.mem_biUnion.mp hH
  exact ne_bot_of_mem_idealDivisors hHI

/-- Möbius inversion of multiplicative dilations of an arbitrary finitely
supported ideal function. This includes every original zero in `f`. -/
theorem tsum_moebius_dilates (f : Ideal (𝓞 K) → ℂ)
    (hf : Function.HasFiniteSupport f) (hf0 : f ⊥ = 0) :
    (∑' H : Ideal (𝓞 K), (moebius H : ℂ) *
      ∑' B : Ideal (𝓞 K), f (H * B)) = f ⊤ := by
  classical
  let T : Finset (Ideal (𝓞 K)) := hf.toFinset
  let P := cubeDivisorPool T
  have hT (I : Ideal (𝓞 K)) : I ∈ T ↔ f I ≠ 0 := by
    exact Set.Finite.mem_toFinset hf
  have houtside (H : Ideal (𝓞 K)) (hH : H ∉ P) :
      (moebius H : ℂ) * (∑' B : Ideal (𝓞 K), f (H * B)) = 0 := by
    by_cases hH0 : H = ⊥
    · simp [hH0, hf0]
    have hzero (B : Ideal (𝓞 K)) : f (H * B) = 0 := by
      by_contra hn
      have hHB0 : H * B ≠ ⊥ := by
        intro hz
        exact hn (by simpa only [hz] using hf0)
      exact hH (cubeDivisorPool_mem ((hT _).mpr hn) hHB0 (dvd_mul_right H B))
    simp only [hzero, tsum_zero, mul_zero]
  rw [tsum_eq_sum houtside]
  have hterm (H : Ideal (𝓞 K)) (hH : H ∈ P) :
      (moebius H : ℂ) * (∑' B : Ideal (𝓞 K), f (H * B)) =
        ∑' I : Ideal (𝓞 K), (moebius H : ℂ) * (if H ∣ I then f I else 0) := by
    rw [← cube_tsum_ideal_divisible H (cubeDivisorPool_ne_zero hH), tsum_mul_left]
  rw [Finset.sum_congr rfl hterm]
  have hsum (H : Ideal (𝓞 K)) :
      Summable (fun I : Ideal (𝓞 K) =>
        (moebius H : ℂ) * (if H ∣ I then f I else 0)) := by
    have hs := ((summable_of_hasFiniteSupport hf).indicator
      {I : Ideal (𝓞 K) | H ∣ I}).mul_left (moebius H : ℂ)
    simpa only [Set.indicator_apply, Set.mem_setOf_eq] using hs
  rw [← Summable.tsum_finsetSum (fun H _ => hsum H)]
  have heval (I : Ideal (𝓞 K)) :
      (∑ H ∈ P, (moebius H : ℂ) * (if H ∣ I then f I else 0)) =
        if I = ⊤ then f ⊤ else 0 := by
    by_cases hfI : f I = 0
    · by_cases hI : I = ⊤
      · subst I
        simp [hfI]
      · simp [hfI, hI]
    have hI0 : I ≠ ⊥ := by
      intro hz
      exact hfI (by simpa only [hz] using hf0)
    have hsub : idealDivisors I ⊆ P := by
      intro H hH
      exact cubeDivisorPool_mem ((hT I).mpr hfI) hI0 ((mem_idealDivisors hI0).mp hH)
    calc
      _ = ∑ H ∈ idealDivisors I,
          (moebius H : ℂ) * (if H ∣ I then f I else 0) := by
        symm
        apply Finset.sum_subset hsub
        intro H _ hn
        have hnd : ¬ H ∣ I := fun hd => hn ((mem_idealDivisors hI0).mpr hd)
        simp [hnd]
      _ = (∑ H ∈ idealDivisors I, (moebius H : ℂ)) * f I := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro H hH
        rw [if_pos ((mem_idealDivisors hI0).mp hH)]
      _ = if I = ⊤ then f ⊤ else 0 := by
        rw [sum_moebius_divisors I hI0]
        by_cases hI : I = ⊤ <;> simp [hI]
  simp_rw [heval]
  simp

theorem cube_moebius_dilates_summable (F : Ideal (𝓞 K) × Ideal (𝓞 K) → ℂ)
    (hF : Function.HasFiniteSupport F) (hF0 : ∀ C, F (C, ⊥) = 0) :
    Summable (fun HC : Ideal (𝓞 K) × Ideal (𝓞 K) =>
      (moebius HC.1 : ℂ) * ∑' B : Ideal (𝓞 K), F (HC.2, HC.1 * B)) := by
  classical
  let T := hF.toFinset
  let C := T.image Prod.fst
  let P := cubeDivisorPool (T.image Prod.snd)
  apply summable_of_hasFiniteSupport
  apply (P.product C).finite_toSet.subset
  intro HC hHC
  have hex : ∃ B : Ideal (𝓞 K), F (HC.2, HC.1 * B) ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hHC (by simp [hn])
  obtain ⟨B, hB⟩ := hex
  have hmem : (HC.2, HC.1 * B) ∈ T := (Set.Finite.mem_toFinset hF).mpr hB
  have hprod0 : HC.1 * B ≠ ⊥ := by
    intro hz
    exact hB (by simpa only [hz] using hF0 HC.2)
  apply Finset.mem_product.mpr
  exact ⟨cubeDivisorPool_mem (Finset.mem_image_of_mem Prod.snd hmem)
    hprod0 (dvd_mul_right HC.1 B), Finset.mem_image_of_mem Prod.fst hmem⟩

/-- The two-variable version used for squarefree/cube sums. -/
theorem tsum_moebius_cube_dilates (F : Ideal (𝓞 K) × Ideal (𝓞 K) → ℂ)
    (hF : Function.HasFiniteSupport F) (hF0 : ∀ C, F (C, ⊥) = 0) :
    (∑' C : Ideal (𝓞 K), F (C, ⊤)) =
      ∑' H : Ideal (𝓞 K), (moebius H : ℂ) *
        ∑' C : Ideal (𝓞 K), ∑' B : Ideal (𝓞 K), F (C, H * B) := by
  have hslice (C : Ideal (𝓞 K)) : Function.HasFiniteSupport (fun B => F (C, B)) := by
    apply (hF.image Prod.snd).subset
    intro B hB
    exact ⟨(C, B), hB, rfl⟩
  calc
    _ = ∑' C : Ideal (𝓞 K), ∑' H : Ideal (𝓞 K),
        (moebius H : ℂ) * ∑' B : Ideal (𝓞 K), F (C, H * B) := by
      exact tsum_congr (fun C => (tsum_moebius_dilates (fun B => F (C, B))
        (hslice C) (hF0 C)).symm)
    _ = ∑' H : Ideal (𝓞 K), ∑' C : Ideal (𝓞 K),
        (moebius H : ℂ) * ∑' B : Ideal (𝓞 K), F (C, H * B) := by
      exact (cube_moebius_dilates_summable F hF hF0).tsum_comm
    _ = _ := by
      apply tsum_congr
      intro H
      exact tsum_mul_left

end HeckeSkeleton.Moments.MOM_BASE
