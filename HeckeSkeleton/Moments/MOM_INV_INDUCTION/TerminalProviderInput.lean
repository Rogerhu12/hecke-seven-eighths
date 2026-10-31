import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderExponent

/-!
# Constructing the general reflected block input

The canonical block statement is derived from the two original sieve
hypotheses and the actual period's finite Mellin kernel. This module
makes no canonical endpoint or induction assumption. The original
row, active-mark, and squarefree-column zero conditions are first
filtered exactly, then the real reflected exponent is calculated.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalInput

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.ActualReflection
  HeckeSkeleton.LowEnergy.ActualReflectionReindex
  HeckeSkeleton.LowEnergy.ActualFrozenIndependence
  HeckeSkeleton.LowEnergy.ActualSeparatedBlock
  HeckeSkeleton.LowEnergy.ActualSieveDictionary
open HeckeSkeleton.LowEnergy
open TerminalMellin TerminalSlices TerminalExponent
open scoped Classical BigOperators nonZeroDivisors NumberField

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

local notation "Ext" => ExteriorIdeal K S

/-- One period, with all source and dyadic data quantified after the
constant. The derivative order is common to every period. -/
theorem fixed_period_block_energy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (hquadratic : ExteriorQuadraticBound K S D)
    (hcubic : ExteriorCubicBound K S D)
    (L eps : ℝ) (hL : 0 < L) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
        (V : SmoothAnnularTest) (Z Nstar H za v ell amp : ℝ),
      1 < Z → H ≤ L → za ≤ L → v ≤ L → ell ≤ L →
      0 ≤ H → 0 ≤ za → 0 ≤ v → 0 ≤ ell → 0 ≤ amp →
      ∀ (rows ps cs bs : Finset Ext) (a : Ext → ℂ),
      (∀ k ∈ rows, GeneralReflectedEnergy.InAnnulus K S Z H k) →
      (∀ P ∈ ps, GeneralReflectedEnergy.InAnnulus K S Z za P) →
      (∀ c ∈ cs, GeneralReflectedEnergy.InAnnulus K S Z v c) →
      (∀ b ∈ bs, GeneralReflectedEnergy.InAnnulus K S Z ell b) →
      (∀ P ∈ ps, ‖a P‖ ≤ amp) →
      (∑ k ∈ rows,
        ‖GeneralReflectedEnergy.block K S D f s F θ a V.toFun (Z ^ Nstar) ps cs bs k‖ ^ 2) ≤
        C * amp ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
          ‖inactiveWeight K S f‖ ^ 2 *
          Z ^ (GeneralReflectedEnergy.exponent K S f s Z Nstar H za v ell + eps) := by
  let delta := eps / (4 * L + 1)
  have hd : 0 < delta := div_pos heps (by linarith)
  obtain ⟨C, hC, hb⟩ := TerminalSlices.block_energy K S D F
    hreflection.kernel.finite_admissible θ hreflection.kernel
    hreflection.exterior_unramified hreflection.allowed_generators hquadratic hcubic delta hd
  refine ⟨C * (192 * 16 ^ delta), by positivity, ?_⟩
  intro f s V Z Nstar H za v ell amp hZ hH hza hv hell hH0 hza0 hv0 hell0 hamp
    rows ps cs bs a hrows hps hcs hbs ha
  have hz : 0 < Z := zero_lt_one.trans hZ
  by_cases ha0 : amp = 0
  · have haz (P : Ext) (hP : P ∈ ps) : a P = 0 :=
      norm_eq_zero.mp (le_antisymm (ha0 ▸ ha P hP) (norm_nonneg _))
    have hzero (k : Ext) : GeneralReflectedEnergy.block K S D f s F θ a V.toFun
        (Z ^ Nstar) ps cs bs k = 0 := by
      unfold GeneralReflectedEnergy.block
      apply Finset.sum_eq_zero
      intro P hP
      rw [haz P hP, zero_mul]
    simp only [hzero, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero,
      ha0, mul_zero, zero_mul, le_refl]
  have hamp' : 0 < amp := lt_of_le_of_ne hamp (Ne.symm ha0)
  have hpow (u : ℝ) (hu : 0 ≤ u) : 1 ≤ 2 * Z ^ u := by
    have hh := Real.one_le_rpow hZ.le hu
    linarith
  have hratio (u : ℝ) (I : Ext) (hI : GeneralReflectedEnergy.InAnnulus K S Z u I) :
      1 ≤ exteriorNorm K S I / Z ^ u ∧ exteriorNorm K S I / Z ^ u ≤ 2 := by
    exact ⟨(le_div_iff₀ (Real.rpow_pos_of_pos hz _)).mpr (by simpa using hI.1),
      (div_le_iff₀ (Real.rpow_pos_of_pos hz _)).mpr hI.2⟩
  have hh := hb f s V (Z ^ Nstar) (Z ^ H) (Z ^ za) (Z ^ v) (Z ^ ell)
    (2 * Z ^ H) (2 * Z ^ za) (2 * Z ^ v) (2 * Z ^ ell)
    (Real.rpow_pos_of_pos hz _) (Real.rpow_pos_of_pos hz _) (Real.rpow_pos_of_pos hz _)
    (Real.rpow_pos_of_pos hz _) (Real.rpow_pos_of_pos hz _)
    (hpow H hH0) (hpow za hza0) (hpow v hv0) (hpow ell hell0)
    (rows.filter (RowAdmissible K S f)) (ps.filter (MarkAdmissible K S f))
    (cs.filter (fun c => Squarefree c.val.val)) bs
    (fun k hk => ⟨(Finset.mem_filter.mp hk).2, (hrows k (Finset.mem_filter.mp hk).1).2⟩)
    (fun P hP => ⟨(Finset.mem_filter.mp hP).2, (hps P (Finset.mem_filter.mp hP).1).2⟩)
    (fun c hc => ⟨(Finset.mem_filter.mp hc).2, (hcs c (Finset.mem_filter.mp hc).1).2⟩)
    (fun b hb => (hbs b hb).2)
    (fun k hk => hratio H k (hrows k (Finset.mem_filter.mp hk).1))
    (fun P hP => hratio za P (hps P (Finset.mem_filter.mp hP).1))
    (fun c hc => hratio v c (hcs c (Finset.mem_filter.mp hc).1))
    (fun b hb => hratio ell b (hbs b hb)) a amp hamp'
    (fun P hP => ha P (Finset.mem_filter.mp hP).1)
  rw [← block_energy_eq_filter] at hh
  have hpre : 0 ≤ C * amp ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
      ‖inactiveWeight K S f‖ ^ 2 := by positivity
  have hn := mul_le_mul_of_nonneg_left
    (actual_factor_le K S f s hZ Nstar H za v ell delta) hpre
  have he : delta * (H + v + ell + za) ≤ eps := by
    have hsum : H + v + ell + za ≤ 4 * L := by linarith
    have hid : delta * (4 * L + 1) = eps := by
      dsimp [delta]
      field_simp
    nlinarith
  have hnum := Real.rpow_le_rpow_of_exponent_le hZ.le
    (add_le_add_left he (GeneralReflectedEnergy.exponent K S f s Z Nstar H za v ell))
  calc
    _ ≤ (C * amp ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
        ‖inactiveWeight K S f‖ ^ 2) *
        ((192 * 16 ^ delta) * Z ^
          (GeneralReflectedEnergy.exponent K S f s Z Nstar H za v ell +
            delta * (H + v + ell + za))) :=
      hh.trans (by simpa only [mul_assoc] using hn)
    _ ≤ (C * amp ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
        ‖inactiveWeight K S f‖ ^ 2) *
        ((192 * 16 ^ delta) * Z ^
          (GeneralReflectedEnergy.exponent K S f s Z Nstar H za v ell + eps)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnum (by positivity)) hpre
    _ = _ := by ring

/-- The finite period inventory is fixed before any source data. Its
maximum block constant comes from the genuine per-period kernels. -/
theorem uniform_block_energy [Finite (SixthLocalClasses K S)]
    (backgrounds : Finset (HeckeCharacter K))
    (R : GeneralReflectedEnergy.ReflectionFamily K S D backgrounds)
    (hquadratic : ExteriorQuadraticBound K S D)
    (hcubic : ExteriorCubicBound K S D)
    (L lo hi eps : ℝ) (hL : 0 < L) (_hlo : 0 < lo) (_hhi : lo ≤ hi) (heps : 0 < eps) :
    ∃ C Z₀ A : ℝ, ∃ J : ℕ,
      0 < C ∧ 1 < Z₀ ∧ 0 ≤ A ∧
      ∀ (θ : HeckeCharacter K), θ ∈ backgrounds →
      MarkedCoefficientReflectionInput K S D (R.data θ) θ →
      ∀ (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
        (V : SmoothAnnularTest) (Z Nstar H za v ell amp : ℝ),
      Z₀ ≤ Z → GeneralReflectedEnergy.BoundedSource K S f Z L Nstar H za →
      0 ≤ v → v ≤ L → 0 ≤ ell → ell ≤ L → 0 ≤ amp →
      Function.support V.toFun ⊆ Set.Icc lo hi →
      ∀ (rows ps cs bs : Finset Ext) (a : Ext → ℂ),
      (∀ k ∈ rows, GeneralReflectedEnergy.InAnnulus K S Z H k) →
      (∀ P ∈ ps, GeneralReflectedEnergy.InAnnulus K S Z za P) →
      (∀ c ∈ cs, GeneralReflectedEnergy.InAnnulus K S Z v c) →
      (∀ b ∈ bs, GeneralReflectedEnergy.InAnnulus K S Z ell b) →
      (∀ P ∈ ps, ‖a P‖ ≤ amp) →
      (∑ k ∈ rows, ‖GeneralReflectedEnergy.block K S D f s (R.data θ) θ a
        V.toFun (Z ^ Nstar) ps cs bs k‖ ^ 2) ≤
        C * amp ^ 2 * testSeminorm V.toFun J A ^ 2 * ‖inactiveWeight K S f‖ ^ 2 *
          Z ^ (GeneralReflectedEnergy.exponent K S f s Z Nstar H za v ell + eps) := by
  classical
  choose C hC hb using fun θ : backgrounds => fixed_period_block_energy K S D
    (R.data θ.val) θ.val (R.reflection θ.val θ.property) hquadratic hcubic L eps hL heps
  refine ⟨1 + ∑ θ : backgrounds, C θ, 2, 2, ActualCommonMellinTail.order K 0,
    by positivity, by norm_num, by norm_num, ?_⟩
  intro θ hθ _hreflection f s V Z Nstar H za v ell amp hZ hsource hv hvL hell hellL
    hamp _hV rows ps cs bs a hr hp hc hd ha
  have hz : 1 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hh := hb ⟨θ, hθ⟩ f s V Z Nstar H za v ell amp hz
    hsource.2.2.1 hsource.2.2.2.2.1 hvL hellL
    hsource.2.1 hsource.2.2.2.1 hv hell hamp rows ps cs bs a hr hp hc hd ha
  have hconst : C ⟨θ, hθ⟩ ≤ 1 + ∑ θ : backgrounds, C θ := by
    have hs : C ⟨θ, hθ⟩ ≤ ∑ θ : backgrounds, C θ :=
      Finset.single_le_sum (fun θ _ => (hC θ).le) (Finset.mem_univ _)
    linarith
  exact hh.trans (by gcongr)

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalInput

end
