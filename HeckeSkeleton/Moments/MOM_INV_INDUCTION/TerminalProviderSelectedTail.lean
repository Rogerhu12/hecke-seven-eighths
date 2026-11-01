import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderTail

/-!
# Absolute tails selected by actual dyadic rectangles

The omitted rectangles form a subset of the literal off-threshold
range. The same genuine Mellin-kernel majorant bounds every such subset,
without discarding a coupled cutoff inside a reflected hybrid block.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalSelectedTail

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.ActualReflection
  HeckeSkeleton.LowEnergy.ActualReflectionReindex
  HeckeSkeleton.LowEnergy.ActualFrozenCharges
  HeckeSkeleton.LowEnergy.ActualFrozenIndependence
  HeckeSkeleton.LowEnergy.ActualHybridEntry
  HeckeSkeleton.LowEnergy.ActualSeparatedBlock
  HeckeSkeleton.LowEnergy.ActualSymbols
  HeckeSkeleton.LowEnergy.ActualClassSlices
open HeckeSkeleton.LowEnergy
open ThetaGlobal.ReflectedAbsolute
open TerminalMellin TerminalSlices TerminalExponent
open scoped Classical BigOperators nonZeroDivisors NumberField

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

local notation "Ext" => ExteriorIdeal K S

open TerminalTail

variable (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)

def value (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (a : Ext → ℂ) (V : ℝ → ℂ) (X : ℝ)
    (keep : Ext × Ext → Prop) [DecidablePred keep]
    (ps : Finset Ext) (k : Ext) : ℂ :=
  ∑ P ∈ ps, a P * ∑' cb : Ext × Ext,
    if keep cb then GeneralReflectedEnergy.atom K S D f s F θ V X k P cb.1 cb.2 else 0

/-- Absolute convergence is available before cutting the original dual
source into rectangles and a complementary tail. -/
theorem atom_summable
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (V : SmoothAnnularTest) {Z L Nstar H za : ℝ} (hZ : 1 < Z)
    (hsource : GeneralReflectedEnergy.BoundedSource K S f Z L Nstar H za)
    (k P : Ext) (hk : GeneralReflectedEnergy.InAnnulus K S Z H k)
    (hP : GeneralReflectedEnergy.InAnnulus K S Z za P) :
    Summable (fun cb : Ext × Ext =>
      GeneralReflectedEnergy.atom K S D f s F θ V.toFun (Z ^ Nstar) k P cb.1 cb.2) := by
  obtain ⟨C, hC, hkernel⟩ := kernel_bound K S F θ hreflection.kernel 2 (by norm_num)
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hq := ThetaGlobal.ReflectedAbsoluteProject.testSeminorm_nonneg
    V.toFun (kernelOrder K 2) 2
  let B := ‖inactiveWeight K S f‖ * C *
    testSeminorm V.toFun (kernelOrder K 2) 2 * (256 * Z ^ (18 * L))
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hb (cb : Ext × Ext) :
      ‖GeneralReflectedEnergy.atom K S D f s F θ V.toFun (Z ^ Nstar) k P cb.1 cb.2‖ ≤
        B * (inverseSquare (exteriorNorm K S cb.1) *
          inverseSquare (exteriorNorm K S cb.2)) := by
    have hy := argument_pos K S f s (Real.rpow_pos_of_pos hz Nstar) k P cb.1 cb.2
    have hn := atom_norm_le_kernel K S D f s hreflection.allowed_generators F θ
      hreflection.exterior_unramified V.toFun (Z ^ Nstar) k P cb.1 cb.2
    have hh := hkernel V (QuotientGroup.mk f.rowUnit)
      (blockFrequency (frozenClass K S D f s) (generatorLocalClass K S D k)
        (generatorLocalClass K S D P) (generatorLocalClass K S D cb.1)
        (generatorLocalClass K S D cb.2)) _ hy
    have he : argument K S f s (Z ^ Nstar) k P cb.1 cb.2 ^ (-(2 : ℝ)) =
        inverseSquare (argument K S f s (Z ^ Nstar) k P cb.1 cb.2) := by
      rw [Real.rpow_neg hy.le, Real.rpow_two]
      rfl
    rw [he] at hh
    have hi := argument_inverseSquare_le K S f s hZ hsource k P cb.1 cb.2 hk hP
    apply (hn.trans (mul_le_mul_of_nonneg_left hh (norm_nonneg _))).trans
    exact (mul_le_mul_of_nonneg_left hi
      (show 0 ≤ ‖inactiveWeight K S f‖ * (C * testSeminorm V.toFun (kernelOrder K 2) 2)
        by positivity)).trans_eq (by dsimp only [B]; ring)
  have hnorm : Summable (fun cb : Ext × Ext =>
      ‖GeneralReflectedEnergy.atom K S D f s F θ V.toFun (Z ^ Nstar) k P cb.1 cb.2‖) :=
    ((column_mass_summable K S).mul_left B).of_nonneg_of_le (fun _ => norm_nonneg _) hb
  exact hnorm.of_norm

theorem norm_bound
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (A C : ℝ) (J : ℕ) (hA : 2 ≤ A) (hC : 0 ≤ C)
    (hkernel : ∀ (V : SmoothAnnularTest) (u : SixthUnitClasses K S)
      (κ : SixthLocalClasses K S) (y : ℝ), 0 < y →
      ‖mellinReflectionKernel K S F θ u κ V.toFun 0 y‖ ≤ C * testSeminorm V.toFun J A * y ^ (-A))
    (V : SmoothAnnularTest) (Z L Nstar H za tau amp : ℝ) (hZ : 1 < Z)
    (keep : Ext × Ext → Prop) [DecidablePred keep]
    (hkeep : ∀ cb, keep cb →
      Z ^ (GeneralReflectedEnergy.threshold K S f s Z Nstar H za + tau) <
        exteriorNorm K S cb.1 * exteriorNorm K S cb.2 ^ 3)
    (hsource : GeneralReflectedEnergy.BoundedSource K S f Z L Nstar H za)
    (hamp : 0 ≤ amp) (ps : Finset Ext) (a : Ext → ℂ) (k : Ext)
    (hk : GeneralReflectedEnergy.InAnnulus K S Z H k)
    (hps : ∀ P ∈ ps, GeneralReflectedEnergy.InAnnulus K S Z za P)
    (ha : ∀ P ∈ ps, ‖a P‖ ≤ amp) :
    ‖value K S D f s F θ a V.toFun (Z ^ Nstar) keep ps k‖ ≤
      (ps.card : ℝ) * amp * ‖inactiveWeight K S f‖ * C * testSeminorm V.toFun J A *
        ((256 * 16 ^ (A - 2)) * Z ^ (18 * L - tau * (A - 2))) * idealMass K S ^ 2 := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hq : 0 ≤ testSeminorm V.toFun J A :=
    ThetaGlobal.ReflectedAbsoluteProject.testSeminorm_nonneg _ _ _
  let B := ‖inactiveWeight K S f‖ * C * testSeminorm V.toFun J A *
    ((256 * 16 ^ (A - 2)) * Z ^ (18 * L - tau * (A - 2)))
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let term (P : Ext) (cb : Ext × Ext) : ℂ :=
    if keep cb then
      GeneralReflectedEnergy.atom K S D f s F θ V.toFun (Z ^ Nstar) k P cb.1 cb.2
    else 0
  have hterm (P : Ext) (hP : P ∈ ps) (cb : Ext × Ext) :
      ‖term P cb‖ ≤ B *
        (inverseSquare (exteriorNorm K S cb.1) * inverseSquare (exteriorNorm K S cb.2)) := by
    dsimp only [term]
    split_ifs with ht
    · have hy := argument_pos K S f s (Real.rpow_pos_of_pos hz Nstar) k P cb.1 cb.2
      have hkern := hkernel V (QuotientGroup.mk f.rowUnit)
        (blockFrequency (frozenClass K S D f s) (generatorLocalClass K S D k)
          (generatorLocalClass K S D P) (generatorLocalClass K S D cb.1)
          (generatorLocalClass K S D cb.2)) _ hy
      have hn := atom_norm_le_kernel K S D f s hreflection.allowed_generators F θ
        hreflection.exterior_unramified V.toFun (Z ^ Nstar) k P cb.1 cb.2
      have ht := tail_power_bound K S f s hZ hA hsource k P cb.1 cb.2 hk (hps P hP) (hkeep cb ht)
      apply (hn.trans (mul_le_mul_of_nonneg_left hkern (norm_nonneg _))).trans
      have hh := mul_le_mul_of_nonneg_left ht
        (show 0 ≤ ‖inactiveWeight K S f‖ * (C * testSeminorm V.toFun J A) by positivity)
      simpa only [B, mul_assoc] using hh
    · simp only [norm_zero]
      exact mul_nonneg hB (mul_nonneg (inverseSquare_nonneg _) (inverseSquare_nonneg _))
  have hsum (P : Ext) (hP : P ∈ ps) :
      ‖∑' cb : Ext × Ext, term P cb‖ ≤ B * idealMass K S ^ 2 := by
    have hmajor := (column_mass_summable K S).mul_left B
    have hnorm : Summable (fun cb : Ext × Ext => ‖term P cb‖) :=
      hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) (hterm P hP)
    calc
      _ ≤ ∑' cb : Ext × Ext, ‖term P cb‖ := norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' cb : Ext × Ext, B *
          (inverseSquare (exteriorNorm K S cb.1) * inverseSquare (exteriorNorm K S cb.2)) :=
        hnorm.tsum_le_tsum (hterm P hP) hmajor
      _ = B * idealMass K S ^ 2 := by rw [tsum_mul_left, column_mass]
  unfold value
  calc
    _ ≤ ∑ P ∈ ps, ‖a P * ∑' cb : Ext × Ext, term P cb‖ := norm_sum_le _ _
    _ ≤ ∑ _P ∈ ps, amp * (B * idealMass K S ^ 2) := by
      apply Finset.sum_le_sum
      intro P hP
      rw [norm_mul]
      exact mul_le_mul (ha P hP) (hsum P hP) (norm_nonneg _) hamp
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      dsimp only [B]
      ring

theorem fixed_period_energy
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (L tau saving : ℝ) (hL : 0 < L) (htau : 0 < tau) (hsaving : 0 < saving) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
        (V : SmoothAnnularTest) (Z Nstar H za amp : ℝ),
      1 < Z → GeneralReflectedEnergy.BoundedSource K S f Z L Nstar H za → 0 ≤ amp →
      ∀ (keep : Ext × Ext → Prop) [DecidablePred keep],
      (∀ cb, keep cb →
        Z ^ (GeneralReflectedEnergy.threshold K S f s Z Nstar H za + tau) <
          exteriorNorm K S cb.1 * exteriorNorm K S cb.2 ^ 3) →
      ∀ (rows ps : Finset Ext) (a : Ext → ℂ),
      (∀ k ∈ rows, GeneralReflectedEnergy.InAnnulus K S Z H k) →
      (∀ P ∈ ps, GeneralReflectedEnergy.InAnnulus K S Z za P) →
      (∀ P ∈ ps, ‖a P‖ ≤ amp) →
      (∑ k ∈ rows, ‖value K S D f s F θ a V.toFun (Z ^ Nstar) keep ps k‖ ^ 2) ≤
        C * amp ^ 2 *
          testSeminorm V.toFun (kernelOrder K (tailShift L tau saving)) (tailShift L tau saving) ^ 2 *
          ‖inactiveWeight K S f‖ ^ 2 * Z ^ (-saving) := by
  let A := tailShift L tau saving
  have hA : 2 ≤ A := tailShift_ge_two hL.le htau hsaving.le
  obtain ⟨C, hC, hk⟩ := kernel_bound K S F θ hreflection.kernel A (by linarith)
  let B := 4 * idealMass K S * C * (256 * 16 ^ (A - 2)) * idealMass K S ^ 2
  have hm := idealMass_nonneg K S
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let Cout := 4 * idealMass K S * B ^ 2
  have hCout : 0 ≤ Cout := by dsimp only [Cout]; positivity
  refine ⟨1 + Cout, by positivity, ?_⟩
  intro f s V Z Nstar H za amp hZ hsource hamp keep _hdec hkeep rows ps a hrows hps ha
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hq : 0 ≤ testSeminorm V.toFun (kernelOrder K A) A :=
    ThetaGlobal.ReflectedAbsoluteProject.testSeminorm_nonneg _ _ _
  have hm := idealMass_nonneg K S
  have hcard (R : Finset Ext) (hR : ∀ I ∈ R, exteriorNorm K S I ≤ 2 * Z ^ L) :
      (R.card : ℝ) ≤ 4 * idealMass K S * Z ^ (2 * L) := by
    have hh := card_le_mass K S R (2 * Z ^ L) (by positivity) hR
    apply hh.trans_eq
    rw [mul_pow, ← Real.rpow_mul_natCast hz.le]
    norm_num
    have he : L * (2 : ℝ) = 2 * L := by ring
    rw [he]
    ring
  have hrowsCard : (rows.card : ℝ) ≤ 4 * idealMass K S * Z ^ (2 * L) := by
    apply hcard
    intro k hk
    exact (hrows k hk).2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.le hsource.2.2.1) (by norm_num))
  have hpsCard : (ps.card : ℝ) ≤ 4 * idealMass K S * Z ^ (2 * L) := by
    apply hcard
    intro P hP
    exact (hps P hP).2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.le hsource.2.2.2.2.1) (by norm_num))
  have hrow (k : Ext) (hkr : k ∈ rows) :
      ‖value K S D f s F θ a V.toFun (Z ^ Nstar) keep ps k‖ ≤
        B * amp * testSeminorm V.toFun (kernelOrder K A) A * ‖inactiveWeight K S f‖ *
          Z ^ (20 * L - tau * (A - 2)) := by
    have hh := norm_bound K S D f s F θ hreflection A C (kernelOrder K A) hA hC hk
      V Z L Nstar H za tau amp hZ keep hkeep hsource hamp ps a k (hrows k hkr) hps ha
    have hc := mul_le_mul_of_nonneg_right hpsCard
      (show 0 ≤ amp * ‖inactiveWeight K S f‖ * C *
        testSeminorm V.toFun (kernelOrder K A) A *
        ((256 * 16 ^ (A - 2)) * Z ^ (18 * L - tau * (A - 2))) * idealMass K S ^ 2 by positivity)
    apply hh.trans
    apply (by simpa only [mul_assoc] using hc : _ ≤ _).trans_eq
    calc
      _ = B * amp * testSeminorm V.toFun (kernelOrder K A) A * ‖inactiveWeight K S f‖ *
          (Z ^ (2 * L) * Z ^ (18 * L - tau * (A - 2))) := by dsimp only [B]; ring
      _ = _ := by rw [← Real.rpow_add hz]; congr 1 <;> congr 1 <;> ring
  let R := B * amp * testSeminorm V.toFun (kernelOrder K A) A * ‖inactiveWeight K S f‖ *
    Z ^ (20 * L - tau * (A - 2))
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  calc
    _ ≤ ∑ _k ∈ rows, R ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk'
      exact pow_le_pow_left₀ (norm_nonneg _) (hrow k hk') 2
    _ = (rows.card : ℝ) * R ^ 2 := by simp
    _ ≤ (4 * idealMass K S * Z ^ (2 * L)) * R ^ 2 :=
      mul_le_mul_of_nonneg_right hrowsCard (sq_nonneg _)
    _ = Cout * amp ^ 2 * testSeminorm V.toFun (kernelOrder K A) A ^ 2 *
        ‖inactiveWeight K S f‖ ^ 2 * Z ^ (-saving) := by
      have hexp : 2 * L + (20 * L - tau * (A - 2)) * 2 = -saving := by
        dsimp only [A, tailShift]
        field_simp [htau.ne']
        <;> ring
      dsimp only [R, Cout]
      simp only [mul_pow]
      rw [← Real.rpow_mul_natCast hz.le]
      have hpow : Z ^ (2 * L) * Z ^ ((20 * L - tau * (A - 2)) * 2) = Z ^ (-saving) := by
        rw [← Real.rpow_add hz, hexp]
      calc
        _ = (4 * idealMass K S * B ^ 2) * amp ^ 2 *
            testSeminorm V.toFun (kernelOrder K A) A ^ 2 * ‖inactiveWeight K S f‖ ^ 2 *
            (Z ^ (2 * L) * Z ^ ((20 * L - tau * (A - 2)) * 2)) := by ring
        _ = _ := by rw [hpow]
    _ ≤ _ := by
      dsimp only [A]
      gcongr
      linarith

theorem uniform_energy
    (backgrounds : Finset (HeckeCharacter K))
    (R : GeneralReflectedEnergy.ReflectionFamily K S D backgrounds)
    (L tau saving : ℝ) (hL : 0 < L) (htau : 0 < tau) (hsaving : 0 < saving) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (θ : HeckeCharacter K), θ ∈ backgrounds →
      ∀ (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
        (V : SmoothAnnularTest) (Z Nstar H za amp : ℝ),
      1 < Z → GeneralReflectedEnergy.BoundedSource K S f Z L Nstar H za → 0 ≤ amp →
      ∀ (keep : Ext × Ext → Prop) [DecidablePred keep],
      (∀ cb, keep cb →
        Z ^ (GeneralReflectedEnergy.threshold K S f s Z Nstar H za + tau) <
          exteriorNorm K S cb.1 * exteriorNorm K S cb.2 ^ 3) →
      ∀ (rows ps : Finset Ext) (a : Ext → ℂ),
      (∀ k ∈ rows, GeneralReflectedEnergy.InAnnulus K S Z H k) →
      (∀ P ∈ ps, GeneralReflectedEnergy.InAnnulus K S Z za P) →
      (∀ P ∈ ps, ‖a P‖ ≤ amp) →
      (∑ k ∈ rows, ‖value K S D f s (R.data θ) θ a V.toFun
        (Z ^ Nstar) keep ps k‖ ^ 2) ≤
        C * amp ^ 2 * testSeminorm V.toFun (kernelOrder K (tailShift L tau saving))
          (tailShift L tau saving) ^ 2 * ‖inactiveWeight K S f‖ ^ 2 * Z ^ (-saving) := by
  choose C hC hb using fun θ : backgrounds => fixed_period_energy K S D
    (R.data θ.val) θ.val (R.reflection θ.val θ.property) L tau saving hL htau hsaving
  have hCsum : 0 ≤ ∑ θ : backgrounds, C θ :=
    Finset.sum_nonneg (fun θ _ => (hC θ).le)
  refine ⟨1 + ∑ θ : backgrounds, C θ, by positivity, ?_⟩
  intro θ hθ f s V Z Nstar H za amp hZ hsource hamp keep _hdec hkeep rows ps a hr hp ha
  have hh := hb ⟨θ, hθ⟩ f s V Z Nstar H za amp hZ hsource hamp keep hkeep rows ps a hr hp ha
  have hconst : C ⟨θ, hθ⟩ ≤ 1 + ∑ θ : backgrounds, C θ := by
    have hs : C ⟨θ, hθ⟩ ≤ ∑ θ : backgrounds, C θ :=
      Finset.single_le_sum (fun θ _ => (hC θ).le) (Finset.mem_univ _)
    linarith
  exact hh.trans (by gcongr)

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalSelectedTail

end
