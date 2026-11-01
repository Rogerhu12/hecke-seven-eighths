import HeckeSkeleton.LowEnergy.ConcreteIdealBlock

/-!
# Uniform hybrid bounds for reconstructed actual ideal rows

The hypotheses in `FiniteReconstruction` are finite arithmetic support,
coefficient bounds, and the local Möbius identity. They contain no operator
or energy conclusion. The only analytic inputs of the main theorem are
the two large-sieve bounds for arbitrary coefficients. Every divisor and
harmonic cost is derived over the actual ideal monoid of the number field.
-/

namespace HeckeSkeleton.LowEnergy.KeepOriginalRow

open NumberField Ideal HeckeSkeleton.LowHybrid
open scoped BigOperators NumberField Classical
noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def IdealQuadraticInput (Ext : Ideal (𝓞 K) → Prop)
    (quad : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ C : ℝ, 0 < C ∧
    ∀ X Y : ℝ, 1 ≤ X → 1 ≤ Y →
    ∀ rows cols : Finset (Ideal (𝓞 K)),
      (∀ I ∈ rows, Ext I ∧ Squarefree I ∧ (Ideal.absNorm I : ℝ) ≤ X) →
      (∀ J ∈ cols, Ext J ∧ Squarefree J ∧ (Ideal.absNorm J : ℝ) ≤ Y) →
      ∀ f : Ideal (𝓞 K) → ℂ,
      (∑ I ∈ rows, ‖∑ J ∈ cols, f J * quad I J‖ ^ 2) ≤
        C * (X * Y) ^ eps * (X + Y) * ∑ J ∈ cols, ‖f J‖ ^ 2

def IdealCubicInput (Ext : Ideal (𝓞 K) → Prop)
    (cubic : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ C : ℝ, 0 < C ∧
    ∀ X Y : ℝ, 1 ≤ X → 1 ≤ Y →
    ∀ rows cols : Finset (Ideal (𝓞 K)),
      (∀ I ∈ rows, Ext I ∧ Squarefree I ∧ (Ideal.absNorm I : ℝ) ≤ X) →
      (∀ J ∈ cols, Ext J ∧ Squarefree J ∧ (Ideal.absNorm J : ℝ) ≤ Y) →
      ∀ f : Ideal (𝓞 K) → ℂ,
      (∑ I ∈ rows, ‖∑ J ∈ cols, f J * cubic J I‖ ^ 2) ≤
        C * (X * Y) ^ eps * (X + Y + (X * Y) ^ (2 / 3 : ℝ)) *
          ∑ J ∈ cols, ‖f J‖ ^ 2

/-- Finite arithmetic data after unique square extraction. Every field is
an actual coefficient, support, divisibility, or local identity statement. -/
structure FiniteReconstruction (Ext : Ideal (𝓞 K) → Prop)
    (K0 N0 B0 L0 : ℝ) where
  rows : Finset (Ideal (𝓞 K))
  ts : Finset (Ideal (𝓞 K))
  cs : Finset (Ideal (𝓞 K))
  ms : Finset (Ideal (𝓞 K))
  hs : Finset (Ideal (𝓞 K))
  ps : Finset (Ideal (𝓞 K))
  a : Ideal (𝓞 K) → ℂ
  beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ
  divisors : Ideal (𝓞 K) → Finset (Ideal (𝓞 K))
  mu : Ideal (𝓞 K) → ℂ
  row_support : ∀ I ∈ rows, Ext I ∧ Squarefree I ∧ (Ideal.absNorm I : ℝ) ≤ K0
  t_support : ∀ I ∈ ts, Ext I ∧ (Ideal.absNorm I : ℝ) ≤ B0
  c_support : ∀ I ∈ cs, Ext I ∧ (Ideal.absNorm I : ℝ) ≤ N0
  m_support : ∀ I ∈ ms, Ext I ∧ (Ideal.absNorm I : ℝ) ≤ N0
  h_support : ∀ I ∈ hs, Ext I ∧ (Ideal.absNorm I : ℝ) ≤ B0
  p_support : ∀ I ∈ ps, Ext I ∧ Squarefree I ∧ (Ideal.absNorm I : ℝ) ≤ L0
  a_norm : ∀ P ∈ ps, ‖a P‖ ≤ 1
  beta_norm : ∀ t c m h, ‖beta t c m h‖ ≤ 1
  coefficient_support : ReconstructedSupport beta N0 B0
  mu_norm : ∀ D, ‖mu D‖ ≤ 1
  divisor_dvd : ∀ k ∈ rows, ∀ D ∈ divisors k, D ∣ k
  mobius : ∀ k ∈ rows, ∀ n,
    mask k n = ∑ D ∈ divisors k, if D ∣ n then mu D else 0

def FiniteReconstruction.row
    {Ext : Ideal (𝓞 K) → Prop} {K0 N0 B0 L0 : ℝ}
    (d : FiniteReconstruction Ext K0 N0 B0 L0)
    (cubic quad : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (k : Ideal (𝓞 K)) : ℂ :=
  reconstructedRow cubic quad d.ts d.cs d.ms d.hs d.ps d.a d.beta k

private theorem four_scales
    (K0 N0 B0 L0 : ℝ) (hK : 1 ≤ K0) (hN : 1 ≤ N0) (hB : 1 ≤ B0) (hL : 1 ≤ L0) :
    1 ≤ K0 * N0 * B0 * L0 ∧
    K0 ≤ K0 * N0 * B0 * L0 ∧ N0 ≤ K0 * N0 * B0 * L0 ∧
    B0 ≤ K0 * N0 * B0 * L0 ∧ L0 ≤ K0 * N0 * B0 * L0 ∧
    N0 * B0 ≤ K0 * N0 * B0 * L0 ∧
    K0 * (N0 * B0) ≤ K0 * N0 * B0 * L0 ∧
    N0 * L0 ≤ K0 * N0 * B0 * L0 := by
  have hK0 := zero_le_one.trans hK
  have hN0 := zero_le_one.trans hN
  have hB0 := zero_le_one.trans hB
  have hL0 := zero_le_one.trans hL
  have hKN : 1 ≤ K0 * N0 := one_le_mul_of_one_le_of_one_le hK hN
  have hNB : 1 ≤ N0 * B0 := one_le_mul_of_one_le_of_one_le hN hB
  have hKBL : 1 ≤ K0 * B0 * L0 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK hB) hL
  have hNBL : 1 ≤ N0 * B0 * L0 := one_le_mul_of_one_le_of_one_le hNB hL
  have hKNL : 1 ≤ K0 * N0 * L0 := one_le_mul_of_one_le_of_one_le hKN hL
  have hKNB : 1 ≤ K0 * N0 * B0 := one_le_mul_of_one_le_of_one_le hKN hB
  refine ⟨one_le_mul_of_one_le_of_one_le hKNB hL, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hNBL hK0]
  · nlinarith [mul_le_mul_of_nonneg_left hKBL hN0]
  · nlinarith [mul_le_mul_of_nonneg_left hKNL hB0]
  · nlinarith [mul_le_mul_of_nonneg_left hKNB hL0]
  · have hKL : 1 ≤ K0 * L0 := one_le_mul_of_one_le_of_one_le hK hL
    nlinarith [mul_le_mul_of_nonneg_left hKL (mul_nonneg hN0 hB0)]
  · nlinarith [mul_le_mul_of_nonneg_left hL (mul_nonneg (mul_nonneg hK0 hN0) hB0)]
  · have hKB : 1 ≤ K0 * B0 := one_le_mul_of_one_le_of_one_le hK hB
    nlinarith [mul_le_mul_of_nonneg_left hKB (mul_nonneg hN0 hL0)]

/-- Uniform actual-ideal hybrid estimate for the literal reconstructed row.
The constant precedes all four scales, finite supports and coefficients.
The only analytic assumptions are the two arbitrary-coefficient sieves. -/
theorem finite_reconstructed_hybrid_energy
    (Ext : Ideal (𝓞 K) → Prop)
    (hext_ne : ∀ I, Ext I → I ≠ ⊥)
    (hext_mul : ∀ I J, Ext I → Ext J → Ext (I * J))
    (hext_dvd : ∀ I J, Ext I → J ∣ I → Ext J)
    (cubic quad : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hmul_left : ∀ D P n, cubic (D * P) n = cubic D n * cubic P n)
    (hmul_right : ∀ P n m, Ext P → cubic P (n * m) = cubic P n * cubic P m)
    (hcubic_norm : ∀ P n, ‖cubic P n‖ ≤ 1)
    (hquadratic : IdealQuadraticInput Ext quad)
    (hcubic : IdealCubicInput Ext cubic)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ K0 N0 B0 L0 : ℝ,
      1 ≤ K0 → 1 ≤ N0 → 1 ≤ B0 → 1 ≤ L0 →
      ∀ d : FiniteReconstruction Ext K0 N0 B0 L0,
      (∑ k ∈ d.rows, ‖d.row cubic quad k‖ ^ 2) ≤
        C * (K0 * N0 * B0 * L0) ^ eps * (K0 + N0 * B0) * B0 *
          (N0 + L0 + (N0 * L0) ^ (2 / 3 : ℝ)) := by
  classical
  let eta : ℝ := eps / 13
  have heta : 0 < eta := by dsimp [eta]; positivity
  obtain ⟨Cq, hCq, hquad⟩ := hquadratic eta heta
  obtain ⟨Cc, hCc, hcub⟩ := hcubic eta heta
  obtain ⟨Cd, hCd, hdiv⟩ :=
    HeckeSkeleton.LowEnergy.two_pow_idealPrimeSupport_small_power K eta heta
  obtain ⟨Ch, hCh, hharm⟩ := HeckeSkeleton.LowEnergy.ideal_harmonic_small_power K eta heta
  have hCdpos : 0 < Cd := zero_lt_one.trans_le hCd
  have hChpos : 0 < Ch := zero_lt_one.trans_le hCh
  let Ctotal : ℝ := Cd ^ 4 * Cq * Cc * Ch ^ 7
  refine ⟨Ctotal, by dsimp [Ctotal]; positivity, ?_⟩
  intro K0 N0 B0 L0 hK hN hB hL d
  let W : ℝ := K0 * N0 * B0 * L0
  obtain ⟨hW, hKW, hNW, hBW, hLW, hNBW, hKNBW, hNLW⟩ := four_scales K0 N0 B0 L0 hK hN hB hL
  change 1 ≤ W at hW
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hK0 : 0 ≤ K0 := zero_le_one.trans hK
  have hN0 : 0 ≤ N0 := zero_le_one.trans hN
  have hB0 : 0 ≤ B0 := zero_le_one.trans hB
  have hL0 : 0 ≤ L0 := zero_le_one.trans hL
  have hNB : 1 ≤ N0 * B0 := one_le_mul_of_one_le_of_one_le hN hB
  let Fcost : ℝ := Cd * W ^ eta
  let Hcost : ℝ := Ch * W ^ eta
  let Q : ℝ := Cq * W ^ eta * (K0 + N0 * B0)
  let S : ℝ := Cc * W ^ eta * (N0 + L0 + (N0 * L0) ^ (2 / 3 : ℝ))
  have hF : 0 ≤ Fcost := by dsimp [Fcost]; positivity
  have hH : 0 ≤ Hcost := by dsimp [Hcost]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  let ds : Finset (Ideal (𝓞 K)) := d.rows.biUnion d.divisors
  let localBlocks := fun k : Ideal (𝓞 K) => d.divisors k ×ˢ d.divisors k
  let block := fun D r : Ideal (𝓞 K) =>
    concreteBlock cubic quad d.ts d.cs d.ms d.hs d.ps d.a d.beta N0 B0 D r
  have hds (D : Ideal (𝓞 K)) (hD : D ∈ ds) :
      Ext D ∧ D ≠ ⊥ ∧ (Ideal.absNorm D : ℝ) ≤ K0 := by
    obtain ⟨k, hk, hDk⟩ := Finset.mem_biUnion.mp hD
    have hdivisor := d.divisor_dvd k hk D hDk
    have hext := hext_dvd k D (d.row_support k hk).1 hdivisor
    exact ⟨hext, hext_ne D hext,
      (ideal_norm_le_of_dvd D k (d.row_support k hk).2.1.ne_zero hdivisor).trans
        (d.row_support k hk).2.2⟩
  have hquot_ext (D : Ideal (𝓞 K)) (hD : D ≠ ⊥)
      (s : Finset (Ideal (𝓞 K))) (hs : ∀ I ∈ s, Ext I)
      (P : Ideal (𝓞 K)) (hP : P ∈ quotientSupport D s) : Ext P :=
    hext_dvd (D * P) P (hs _ ((mem_quotientSupport D P hD s).mp hP)) (dvd_mul_left P D)
  have hnorm_bound (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
      (hIW : (Ideal.absNorm I : ℝ) ≤ W) :
      (2 : ℝ) ^ (HeckeSkeleton.LowEnergy.idealPrimeSupport K I).card ≤ Fcost := by
    exact (hdiv I hI).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hIW heta.le) (zero_le_one.trans hCd))
  have hdivcard (k : Ideal (𝓞 K)) (hk : k ∈ d.rows) :
      ((d.divisors k).card : ℝ) ≤ Fcost := by
    have hc : (d.divisors k).card ≤
        2 ^ (HeckeSkeleton.LowEnergy.idealPrimeSupport K k).card := by
      apply HeckeSkeleton.LowEnergy.squarefree_divisor_finset_card_le K k
        (d.row_support k hk).2.1.ne_zero (d.divisors k)
      intro D hD
      have hd := d.divisor_dvd k hk D hD
      exact ⟨Squarefree.squarefree_of_dvd hd (d.row_support k hk).2.1, hd⟩
    have hcr : ((d.divisors k).card : ℝ) ≤
        (2 : ℝ) ^ (HeckeSkeleton.LowEnergy.idealPrimeSupport K k).card := by exact_mod_cast hc
    exact hcr.trans (hnorm_bound k (d.row_support k hk).2.1.ne_zero
      ((d.row_support k hk).2.2.trans hKW))
  have hharmonic (s : Finset (Ideal (𝓞 K)))
      (hne : ∀ I ∈ s, I ≠ ⊥) (hcut : ∀ I ∈ s, (Ideal.absNorm I : ℝ) ≤ W) :
      (∑ I ∈ s, 1 / (Ideal.absNorm I : ℝ)) ≤ Hcost := hharm W hW s hne hcut
  have htH : (∑ t ∈ d.ts, 1 / (Ideal.absNorm t : ℝ)) ≤ Hcost :=
    hharmonic d.ts (fun t ht => hext_ne t (d.t_support t ht).1)
      (fun t ht => (d.t_support t ht).2.trans hBW)
  have hhH : (∑ h ∈ d.hs, 1 / (Ideal.absNorm h : ℝ)) ≤ Hcost :=
    hharmonic d.hs (fun h hh => hext_ne h (d.h_support h hh).1)
      (fun h hh => (d.h_support h hh).2.trans hBW)
  have hdsH : (∑ D ∈ ds, 1 / (Ideal.absNorm D : ℝ)) ≤ Hcost :=
    hharmonic ds (fun D hD => (hds D hD).2.1)
      (fun D hD => (hds D hD).2.2.trans hKW)
  have hquotH (D : Ideal (𝓞 K)) (hD : D ∈ ds)
      (s : Finset (Ideal (𝓞 K))) (X : ℝ) (hXW : X ≤ W)
      (hs : ∀ I ∈ s, Ext I ∧ (Ideal.absNorm I : ℝ) ≤ X) :
      (∑ I ∈ quotientSupport D s, 1 / (Ideal.absNorm I : ℝ)) ≤ Hcost := by
    apply hharmonic (quotientSupport D s)
    · intro I hI
      exact hext_ne I (hquot_ext D (hds D hD).2.1 s (fun P hP => (hs P hP).1) I hI)
    · intro I hI
      exact (quotientSupport_norm_le D (hds D hD).2.1 s X
        (fun P hP => ⟨hext_ne P (hs P hP).1, (hs P hP).2⟩) I hI).trans hXW
  have hadmissible (D : Ideal (𝓞 K)) (hD : D ∈ ds)
      (r : Ideal (𝓞 K)) (hr : r ∈ ds) :
      (block D r).Admissible (d.rows.filter (fun k => (D, r) ∈ localBlocks k))
        (Q * Fcost) (S * Fcost) (B0 / (Ideal.absNorm r : ℝ)) Hcost := by
    apply concreteBlock_admissible cubic quad hcubic_norm
      (d.rows.filter (fun k => (D, r) ∈ localBlocks k))
      d.ts d.cs d.ms d.hs d.ps d.a d.beta N0 B0 Q S Fcost Fcost Hcost D r
      hQ hF hF hB0 (hds D hD).2.1 (hds r hr).2.1
      (fun t ht => hext_ne t (d.t_support t ht).1)
      (fun c hc => hext_ne c (d.c_support c hc).1)
      (fun h hh => hext_ne h (d.h_support h hh).1)
      d.a_norm d.beta_norm d.coefficient_support
      (hquotH D hD d.ps L0 hLW (fun P hP => ⟨(d.p_support P hP).1, (d.p_support P hP).2.2⟩))
    · intro J hJ
      have hj := quadraticTargets_support d.ms d.hs N0 B0 J hJ
      have hc : (((goodQuadraticPairs d.ms d.hs N0 B0).filter
          (fun x => x.1 * x.2 = J)).card : ℝ) ≤
          (2 : ℝ) ^ (HeckeSkeleton.LowEnergy.idealPrimeSupport K J).card := by
        exact_mod_cast HeckeSkeleton.LowEnergy.ideal_product_fiber_card_le K
          (goodQuadraticPairs d.ms d.hs N0 B0) J hj.1
      exact hc.trans (hnorm_bound J hj.1.ne_zero (hj.2.trans hNBW))
    · intro J hJ
      have hj := cubicTargets_support d.ms (quotientSupport r d.cs) N0 J hJ
      have hc : (((goodCubicPairs d.ms (quotientSupport r d.cs) N0).filter
          (fun x => x.2 * x.1 = J)).card : ℝ) ≤
          (2 : ℝ) ^ (HeckeSkeleton.LowEnergy.idealPrimeSupport K J).card := by
        have hh := HeckeSkeleton.LowEnergy.ideal_product_fiber_card_le K
          (goodCubicPairs d.ms (quotientSupport r d.cs) N0) J hj.1
        have hh' : (((goodCubicPairs d.ms (quotientSupport r d.cs) N0).filter
            (fun x => x.1 * x.2 = J)).card : ℝ) ≤
            (2 : ℝ) ^ (HeckeSkeleton.LowEnergy.idealPrimeSupport K J).card := by exact_mod_cast hh
        simpa only [mul_comm] using hh'
      exact hc.trans (hnorm_bound J hj.1.ne_zero (hj.2.trans hNW))
    · intro f
      have hb := hquad K0 (N0 * B0) hK hNB
        (d.rows.filter (fun k => (D, r) ∈ localBlocks k))
        (quadraticTargets d.ms d.hs N0 B0)
        (fun k hk => d.row_support k (Finset.mem_filter.mp hk).1)
        (by
          intro J hJ
          have hj := quadraticTargets_support d.ms d.hs N0 B0 J hJ
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hJ
          have hp := Finset.mem_product.mp (Finset.mem_filter.mp hx).1
          exact ⟨hext_mul x.1 x.2 (d.m_support x.1 hp.1).1
            (d.h_support x.2 hp.2).1, hj⟩) f
      have he :
          (∑ k ∈ d.rows.filter (fun k => (D, r) ∈ localBlocks k),
            ‖∑ J ∈ quadraticTargets d.ms d.hs N0 B0, quad k J * f J‖ ^ 2) =
          ∑ k ∈ d.rows.filter (fun k => (D, r) ∈ localBlocks k),
            ‖∑ J ∈ quadraticTargets d.ms d.hs N0 B0, f J * quad k J‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro k hk
        congr 2
        apply Finset.sum_congr rfl
        intro J hJ
        ring
      rw [he]
      apply hb.trans
      dsimp only [Q]
      have hp := Real.rpow_le_rpow (mul_nonneg hK0 (mul_nonneg hN0 hB0)) hKNBW heta.le
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hCq.le)
          (by positivity)) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    · intro f
      have hb := hcub N0 L0 hN hL
        (cubicTargets d.ms (quotientSupport r d.cs) N0) (quotientSupport D d.ps)
        (by
          intro J hJ
          have hj := cubicTargets_support d.ms (quotientSupport r d.cs) N0 J hJ
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hJ
          have hp := Finset.mem_product.mp (Finset.mem_filter.mp hx).1
          exact ⟨hext_mul x.2 x.1
            (hquot_ext r (hds r hr).2.1 d.cs (fun c hc => (d.c_support c hc).1) x.2 hp.2)
            (d.m_support x.1 hp.1).1, hj⟩)
        (by
          intro P hP
          exact ⟨hquot_ext D (hds D hD).2.1 d.ps
              (fun P hP => (d.p_support P hP).1) P hP,
            quotientSupport_squarefree D (hds D hD).2.1 d.ps
              (fun P hP => (d.p_support P hP).2.1) P hP,
            quotientSupport_norm_le D (hds D hD).2.1 d.ps L0
              (fun P hP => ⟨(d.p_support P hP).2.1.ne_zero, (d.p_support P hP).2.2⟩) P hP⟩) f
      apply hb.trans
      dsimp only [S]
      have hp := Real.rpow_le_rpow (mul_nonneg hN0 hL0) hNLW heta.le
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hCc.le)
          (by positivity)) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hrow (k : Ideal (𝓞 K)) (hk : k ∈ d.rows) :
      d.row cubic quad k =
        ∑ dr ∈ localBlocks k, (d.mu dr.1 * d.mu dr.2) *
          ((1 / (Real.sqrt (Ideal.absNorm dr.1 : ℝ) : ℂ)) * (block dr.1 dr.2).row k) := by
    have he := reconstructedRow_eq_normalForm Ext cubic quad hmul_left hmul_right
      d.ts d.cs d.ms d.hs d.ps (d.divisors k) d.a d.beta d.mu k (d.mobius k hk)
      (by
        intro D hD P hP
        have hextD := hext_dvd k D (d.row_support k hk).1 (d.divisor_dvd k hk D hD)
        exact hquot_ext D (hext_ne D hextD) d.ps (fun P hP => (d.p_support P hP).1) P hP)
    simpa only [FiniteReconstruction.row, localBlocks, Finset.sum_product, block,
      concreteBlock_row_eq cubic quad d.ts d.cs d.ms d.hs d.ps d.a d.beta N0 B0 d.coefficient_support]
      using he
  have hglobal := hybrid_energy_of_weighted_blocks d.rows ds ds localBlocks block
    (fun _ dr => d.mu dr.1 * d.mu dr.2)
    (fun D => (Ideal.absNorm D : ℝ)) (fun r => (Ideal.absNorm r : ℝ)) (fun _ => Hcost)
    (Fcost ^ 2) (Q * Fcost) (S * Fcost) B0 Hcost Hcost Hcost
    (sq_nonneg _) (mul_nonneg hQ hF) (mul_nonneg hS hF) hB0 hH hH hH
    (fun D hD => HeckeSkeleton.LowEnergy.ideal_norm_pos K D (hds D hD).2.1)
    (fun r hr => HeckeSkeleton.LowEnergy.ideal_norm_pos K r (hds r hr).2.1)
    (fun _ _ => hH)
    (by
      intro k hk dr hdr
      obtain ⟨hD, hr⟩ := Finset.mem_product.mp hdr
      exact Finset.mem_product.mpr ⟨Finset.mem_biUnion.mpr ⟨k, hk, hD⟩,
        Finset.mem_biUnion.mpr ⟨k, hk, hr⟩⟩)
    (by
      intro k hk dr hdr
      rw [norm_mul]
      exact (mul_le_mul (d.mu_norm dr.1) (d.mu_norm dr.2)
        (norm_nonneg _) (by norm_num)).trans_eq (by norm_num))
    (by
      intro k hk
      have hb := pow_le_pow_left₀ (Nat.cast_nonneg (d.divisors k).card) (hdivcard k hk) 2
      simpa only [localBlocks, Finset.card_product, Nat.cast_mul, pow_two] using hb)
    hadmissible
    (fun _ _ _ _ => htH)
    (fun _ _ r hr => hquotH r hr d.cs N0 hNW d.c_support)
    (fun _ _ _ _ => hhH)
  have henergy :
      (∑ k ∈ d.rows, ‖d.row cubic quad k‖ ^ 2) ≤
        Fcost ^ 2 * (Q * Fcost) * (S * Fcost) * B0 * Hcost ^ 2 * Hcost * Hcost *
          (∑ D ∈ ds, Hcost / (Ideal.absNorm D : ℝ)) *
          (∑ r ∈ ds, 1 / (Ideal.absNorm r : ℝ)) := by
    have he : (∑ k ∈ d.rows, ‖d.row cubic quad k‖ ^ 2) =
        ∑ k ∈ d.rows, ‖∑ dr ∈ localBlocks k, (d.mu dr.1 * d.mu dr.2) *
          ((1 / (Real.sqrt (Ideal.absNorm dr.1 : ℝ) : ℂ)) * (block dr.1 dr.2).row k)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hrow k hk]
    rw [he]
    exact hglobal
  have hDmass : (∑ D ∈ ds, Hcost / (Ideal.absNorm D : ℝ)) ≤ Hcost ^ 2 := by
    calc
      _ = Hcost * ∑ D ∈ ds, 1 / (Ideal.absNorm D : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro D hD
        ring
      _ ≤ Hcost * Hcost := mul_le_mul_of_nonneg_left hdsH hH
      _ = _ := by ring
  have hpre : 0 ≤ Fcost ^ 2 * (Q * Fcost) * (S * Fcost) * B0 *
      Hcost ^ 2 * Hcost * Hcost := by positivity
  have hDmass0 : 0 ≤ ∑ D ∈ ds, Hcost / (Ideal.absNorm D : ℝ) :=
    Finset.sum_nonneg (fun D hD => div_nonneg hH (Nat.cast_nonneg _))
  have hpower : (W ^ eta) ^ 13 = W ^ eps := by
    rw [← Real.rpow_mul_natCast hW0]
    congr 1
    dsimp only [eta]
    ring
  calc
    _ ≤ Fcost ^ 2 * (Q * Fcost) * (S * Fcost) * B0 * Hcost ^ 2 * Hcost * Hcost *
        (∑ D ∈ ds, Hcost / (Ideal.absNorm D : ℝ)) *
        (∑ r ∈ ds, 1 / (Ideal.absNorm r : ℝ)) := henergy
    _ ≤ Fcost ^ 2 * (Q * Fcost) * (S * Fcost) * B0 * Hcost ^ 2 * Hcost * Hcost *
        (Hcost ^ 2) * Hcost := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hDmass hpre) hdsH
        (Finset.sum_nonneg (fun r hr => one_div_nonneg.mpr (Nat.cast_nonneg _)))
        (mul_nonneg hpre (sq_nonneg _))
    _ = Ctotal * (W ^ eta) ^ 13 * (K0 + N0 * B0) * B0 *
        (N0 + L0 + (N0 * L0) ^ (2 / 3 : ℝ)) := by
      dsimp only [Fcost, Hcost, Q, S, Ctotal]
      ring
    _ = _ := by rw [hpower]

#print axioms finite_reconstructed_hybrid_energy

end
end HeckeSkeleton.LowEnergy.KeepOriginalRow
