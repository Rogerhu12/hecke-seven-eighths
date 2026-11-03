module

public import HeckeSkeleton.Moments.MOM_INV_STEP.FixedTripleEnergy

/-!
# Counting divisor rows in a fixed sector graph

For the first-outer error measure, the second source can be completed
with unit common, overlap and bare frequency. Its child row is then a
divisor of q₀ times the retained label. The sector is determined by that
divisor. This costs one ideal-divisor factor, with no count of historical
cube pairs and no multiplicity from the sector quotient.
-/

@[expose] public section
noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.DivisorRowMass

open NumberField IsDedekindDomain DedekindZetaZeroFree.LargeSieve
open HeckeSkeleton.Moments.MOMInvStep.FixedTripleFibers
open HeckeSkeleton.Moments.MOMInvStep.FixedTripleEnergy
open scoped Classical BigOperators NumberField

variable {K : Type*} [Field K] [NumberField K] {Sector : Type*}

def test (sector : Ideal (𝓞 K) → Sector) : SecondChild K Sector → ℂ :=
  fun x => if x.2.2.1 ∣ x.1.q0 * x.2.1 ∧ x.2.2.2 = sector x.2.2.1 then 1 else 0

theorem test_one (sector : Ideal (𝓞 K) → Sector) (γ : OuterTriple K)
    (f : Ideal (𝓞 K)) (y : Ideal (𝓞 K) × Sector)
    (hd : y.1 ∣ γ.q0 * f) (hs : y.2 = sector y.1) :
    test sector (γ,f,y) = 1 := by
  simp [test, hd, hs]

theorem row_sum_le (sector : Ideal (𝓞 K) → Sector)
    (rows : Finset (Ideal (𝓞 K) × Sector)) (γ : OuterTriple K)
    (f : Ideal (𝓞 K)) (hq : γ.q0 ≠ 0) (hf : f ≠ 0) :
    (∑ y ∈ rows, ‖test sector (γ,f,y)‖ ^ 2) ≤
      ((idealDivisors (γ.q0 * f)).card : ℝ) := by
  let R := rows.filter (fun y => y.1 ∣ γ.q0 * f ∧ y.2 = sector y.1)
  have he : (∑ y ∈ rows, ‖test sector (γ,f,y)‖ ^ 2) = (R.card : ℝ) := by
    calc
      _ = ∑ y ∈ rows, if y.1 ∣ γ.q0 * f ∧ y.2 = sector y.1 then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro y hy
        by_cases h : y.1 ∣ γ.q0 * f ∧ y.2 = sector y.1 <;> simp [test, h]
      _ = (R.card : ℝ) := by
        rw [← Finset.sum_filter]
        simp [R]
  let encode (y : R) : idealDivisors (γ.q0 * f) :=
    ⟨y.val.1, (mem_idealDivisors (mul_ne_zero hq hf)).mpr
      (Finset.mem_filter.mp y.property).2.1⟩
  have hinj : Function.Injective encode := by
    intro y z h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun d : idealDivisors (γ.q0 * f) => d.val) h
    · have hi : y.val.1 = z.val.1 :=
        congrArg (fun d : idealDivisors (γ.q0 * f) => d.val) h
      exact (Finset.mem_filter.mp y.property).2.2.trans
        ((congrArg sector hi).trans (Finset.mem_filter.mp z.property).2.2.symm)
  rw [he]
  have hc : R.card ≤ (idealDivisors (γ.q0 * f)).card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective encode hinj
  exact_mod_cast hc

theorem childEnergy_le (sector : Ideal (𝓞 K) → Sector) (slotCap : ℕ)
    (labels : Finset (Ideal (𝓞 K))) (rows : Finset (Ideal (𝓞 K) × Sector))
    (hlabels : ∀ f ∈ labels, f ≠ 0) (γ : OuterTriple K) (hq : γ.q0 ≠ 0) :
    childEnergy slotCap labels rows (test sector) γ ≤
      ((idealDivisors γ.q0).card : ℝ) *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ) ^ (10 + 4 * slotCap) := by
  unfold childEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro f hf
  have hd : ((idealDivisors (γ.q0 * f)).card : ℝ) ≤
      ((idealDivisors γ.q0).card : ℝ) * ((idealDivisors f).card : ℝ) := by
    exact_mod_cast divisor_card_mul_le γ.q0 f hq (hlabels f hf)
  calc
    _ ≤ labelDivisorWeight slotCap f * ((idealDivisors (γ.q0 * f)).card : ℝ) :=
      mul_le_mul_of_nonneg_left (row_sum_le sector rows γ f hq (hlabels f hf))
        (labelDivisorWeight_nonneg slotCap f)
    _ ≤ labelDivisorWeight slotCap f *
        (((idealDivisors γ.q0).card : ℝ) * ((idealDivisors f).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hd (labelDivisorWeight_nonneg slotCap f)
    _ = _ := by
      unfold labelDivisorWeight
      rw [show 10 + 4 * slotCap = (9 + 4 * slotCap) + 1 by omega, pow_succ]
      ring

theorem exists_label_mass_bound (p : ℕ) (hp : 0 < p) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (labels : Finset (Ideal (𝓞 K))) (X : ℝ),
      1 ≤ X → (∀ f ∈ labels, (f.absNorm : ℝ) ≤ X) →
      (∑ f ∈ labels, ((idealDivisors f).card : ℝ) ^ p) ≤ C * X ^ (1 + ε) := by
  obtain ⟨A,hA,hcount, hfinite⟩ := exists_ideal_count_bound_finset K
  obtain ⟨B,hB,hdiv⟩ := exists_divisor_power_bound (K := K) p hp ε hε
  refine ⟨A * B, one_le_mul_of_one_le_of_one_le hA hB, ?_⟩
  intro labels X hX hlabels
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  calc
    _ ≤ ∑ _f ∈ labels, B * X ^ ε := by
      apply Finset.sum_le_sum
      intro f hf
      exact (hdiv f).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hlabels f hf) hε.le) hB0)
    _ = (labels.card : ℝ) * (B * X ^ ε) := by simp
    _ ≤ (A * X) * (B * X ^ ε) :=
      mul_le_mul_of_nonneg_right (hfinite X hX labels hlabels) (by positivity)
    _ = (A * B) * X ^ (1 + ε) := by
      rw [Real.rpow_add hX0, Real.rpow_one]
      ring

/-- The constant precedes all source packets and all sector graphs.
Only the actual triple and retained-label norm windows are required. -/
theorem exists_packet_mass_bound
    (sectorTransport : Ideal (𝓞 K) → Ideal (𝓞 K) → (Sector ≃ Sector))
    (slotCap : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Jo Jn : ℕ}
      (P : ReconstructionPacket (K := K) (Sector := Sector)
        sectorTransport slotCap Jo Jn)
      (sector : Ideal (𝓞 K) → Sector) (Xq Xt Xf : ℝ),
      1 ≤ Xq → 1 ≤ Xt → 1 ≤ Xf →
      (∀ x ∈ originalSource P.source P.oldLists P.newLists P.keep,
        (x.outer.q0.absNorm : ℝ) ≤ Xq ∧
        (x.outer.quotient.absNorm : ℝ) ≤ Xt ∧ x.outer.residual = 1) →
      (∀ f ∈ P.labels, (f.absNorm : ℝ) ≤ Xf) →
      (∑ γ ∈ P.triples, tripleDivisorWeight slotCap γ * P.energy (test sector) γ) ≤
        C * (Xq * Xt) ^ (1 + ε) * Xq ^ ε * Xf ^ (1 + ε) := by
  obtain ⟨A,hA,htriples⟩ := ReconstructionPacket.exists_tripleMass_bound
    (K := K) (Sector := Sector) (sectorTransport := sectorTransport)
    (slotCap := slotCap) ε hε
  obtain ⟨B,hB,hdiv⟩ := exists_divisor_power_bound (K := K) 1 (by omega) ε hε
  obtain ⟨C,hC,hlabels⟩ := exists_label_mass_bound
    (K := K) (10 + 4 * slotCap) (by omega) ε hε
  refine ⟨A * B * C, mul_pos (mul_pos hA (zero_lt_one.trans_le hB))
    (zero_lt_one.trans_le hC), ?_⟩
  intro Jo Jn P sector Xq Xt Xf hq ht hf hsource hlabel
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hmass : P.tripleMass ≤ A * (Xq * Xt) ^ (1 + ε) := by
    simpa only [mul_one] using htriples P Xq Xt 1 hq ht (le_refl 1)
      (fun x hx => ⟨(hsource x hx).1, (hsource x hx).2.1, by
        rw [(hsource x hx).2.2]
        norm_num⟩)
  have hpoint (γ : OuterTriple K) (hγ : γ ∈ P.triples) :
      P.energy (test sector) γ ≤ (B * Xq ^ ε) * (C * Xf ^ (1 + ε)) := by
    have hqγ : (γ.q0.absNorm : ℝ) ≤ Xq := by
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
      exact (hsource x hx).1
    have hdivγ : ((idealDivisors γ.q0).card : ℝ) ≤ B * Xq ^ ε := by
      have h := hdiv γ.q0
      rw [pow_one] at h
      exact h.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hqγ hε.le) hB0)
    apply (childEnergy_le sector slotCap P.labels P.rows P.label_nonzero γ
      (P.outer_nonzero γ hγ).1).trans
    exact mul_le_mul hdivγ (hlabels P.labels Xf hf hlabel)
      (Finset.sum_nonneg fun _ _ => pow_nonneg (Nat.cast_nonneg _) _) (by positivity)
  calc
    _ ≤ ∑ γ ∈ P.triples, tripleDivisorWeight slotCap γ *
        ((B * Xq ^ ε) * (C * Xf ^ (1 + ε))) := by
      apply Finset.sum_le_sum
      intro γ hγ
      exact mul_le_mul_of_nonneg_left (hpoint γ hγ)
        (tripleDivisorWeight_nonneg slotCap γ)
    _ = P.tripleMass * ((B * Xq ^ ε) * (C * Xf ^ (1 + ε))) := by
      rw [← Finset.sum_mul]
      rfl
    _ ≤ (A * (Xq * Xt) ^ (1 + ε)) *
        ((B * Xq ^ ε) * (C * Xf ^ (1 + ε))) :=
      mul_le_mul_of_nonneg_right hmass (by positivity)
    _ = _ := by ring

end HeckeSkeleton.Moments.MOM_INV_STEP.DivisorRowMass

end

