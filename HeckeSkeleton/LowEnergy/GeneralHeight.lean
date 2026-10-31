import HeckeSkeleton.LowEnergy.ActualCommonMellinTail
import HeckeGeneral.Characters.InfinityPacket

/-!
# Polynomial norm-twist height for a fixed angular background

The constant in the gamma estimate is selected before every radial
parameter.  This follows by applying the existing gamma theorem at
radial parameter zero and translating the imaginary argument.  No
uniform estimate in an unbounded angular weight is asserted.

The final profile bound is uniform over all characters with the fixed
angular shifts, in particular all finite-order children and norm twists
of one fixed background.  It uses the actual Hecke infinity parameters.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.GeneralHeight

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.Characters
open HeckeSkeleton.ThetaKernel
open HeckeSkeleton.LowEnergy.CommonMellinTail
open HeckeSkeleton.LowEnergy.ActualCommonMellinTail
open scoped Classical BigOperators NumberField

variable (K : Type) [Field K] [NumberField K]

/-- Additive height of the actual radial parameters. -/
def radialHeight (θ : HeckeCharacter K) : ℝ :=
  1 + ∑ v : {v : InfinitePlace K // v.IsComplex}, |archRadial K θ v|

theorem radialHeight_ge_one (θ : HeckeCharacter K) : 1 ≤ radialHeight K θ := by
  unfold radialHeight
  have h := Finset.sum_nonneg (fun v (_ : v ∈ Finset.univ) => abs_nonneg (archRadial K θ v))
  linarith

theorem radial_le_height (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) :
    1 + |archRadial K θ v| ≤ radialHeight K θ := by
  unfold radialHeight
  exact add_le_add_left (Finset.single_le_sum (fun w _ => abs_nonneg (archRadial K θ w))
    (Finset.mem_univ v)) 1

theorem placeFactor_shift (α ρ : ℝ) (s : ℂ) :
    placeFactor α ρ s = placeFactor α 0 (s + Complex.I * ρ) := by
  unfold placeFactor
  congr 3 <;> ring

/-- The gamma constant precedes the radial parameter. -/
theorem place_bound_uniform_radial {α σlo Λ : ℝ} (hα : 1 / 2 ≤ α)
    (hlo : -(1 / 3 : ℝ) < σlo) (hΛ : σlo ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℝ) (s : ℂ), σlo ≤ s.re → s.re ≤ Λ →
      ‖placeFactor α ρ s‖ ≤ C * (1 + |ρ|) ^ (4 * (|σlo| + |Λ|)) *
        (1 + |s.im|) ^ (4 * s.re) := by
  obtain ⟨C, hC, hb⟩ := place_bound 0 hα hlo hΛ
  refine ⟨C, hC, ?_⟩
  intro ρ s hs0 hs1
  have hzre : (s + Complex.I * (ρ : ℂ)).re = s.re := by simp
  have hzim : (s + Complex.I * (ρ : ℂ)).im = s.im + ρ := by simp
  have h := hb (s + Complex.I * ρ) (by rwa [hzre]) (by rwa [hzre])
  rw [← placeFactor_shift, hzre, hzim] at h
  have hsh := rpow_shift_bound (4 * s.re) ρ s.im
  have hexp : |4 * s.re| ≤ 4 * (|σlo| + |Λ|) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have hs : |s.re| ≤ |σlo| + |Λ| := by
      rcases abs_cases s.re with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he]
      · linarith [le_abs_self Λ, abs_nonneg σlo]
      · linarith [neg_le_abs σlo, abs_nonneg Λ]
    linarith
  have hp : (1 + |ρ|) ^ |4 * s.re| ≤ (1 + |ρ|) ^ (4 * (|σlo| + |Λ|)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg ρ]) hexp
  have hshift := hsh.trans (mul_le_mul_of_nonneg_right hp (by positivity))
  apply h.trans
  exact (mul_le_mul_of_nonneg_left hshift hC).trans_eq (by ring)

/-- A single polynomial in the actual radial height controls the complete
archimedean product, with all angular shifts fixed before the constant. -/
theorem gammaPart_fixedAngular_bound (θ₀ : HeckeCharacter K)
    {σlo Λ : ℝ} (hlo : -(1 / 3 : ℝ) < σlo) (hΛ : σlo ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (θ : HeckeCharacter K),
      (∀ v, archShift K θ v = archShift K θ₀ v) →
      ∀ s : ℂ, σlo ≤ s.re → s.re ≤ Λ →
      ‖gammaPart K θ s‖ ≤
        C * radialHeight K θ ^ (4 * ncx K * (|σlo| + |Λ|)) *
          (1 + |s.im|) ^ (4 * ncx K * s.re) := by
  have hv := fun v : {v : InfinitePlace K // v.IsComplex} =>
    place_bound_uniform_radial (archShift_ge θ₀ v) hlo hΛ
  choose c hc0 hc using hv
  refine ⟨∏ v, c v, Finset.prod_nonneg (fun v _ => hc0 v), ?_⟩
  intro θ hang s hs0 hs1
  have hH : 0 < radialHeight K θ := zero_lt_one.trans_le (radialHeight_ge_one K θ)
  have hT : 0 < 1 + |s.im| := by positivity
  have hlocal (v : {v : InfinitePlace K // v.IsComplex}) :
      ‖placeFactor (archShift K θ v) (archRadial K θ v) s‖ ≤
        c v * (radialHeight K θ ^ (4 * (|σlo| + |Λ|)) *
          (1 + |s.im|) ^ (4 * s.re)) := by
    rw [hang v]
    have h := hc v (archRadial K θ v) s hs0 hs1
    have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + |archRadial K θ v|)
      (radial_le_height K θ v) (by positivity : 0 ≤ 4 * (|σlo| + |Λ|))
    apply h.trans
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (hc0 v))
      (by positivity)).trans_eq (by ring)
  unfold gammaPart
  rw [norm_prod]
  calc
    _ ≤ ∏ v : {v : InfinitePlace K // v.IsComplex},
        c v * (radialHeight K θ ^ (4 * (|σlo| + |Λ|)) *
          (1 + |s.im|) ^ (4 * s.re)) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun v _ => hlocal v)
    _ = (∏ v, c v) *
        ((radialHeight K θ ^ (4 * (|σlo| + |Λ|))) ^
          Fintype.card {v : InfinitePlace K // v.IsComplex} *
        ((1 + |s.im|) ^ (4 * s.re)) ^ Fintype.card {v : InfinitePlace K // v.IsComplex}) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, mul_pow]
    _ = _ := by
      rw [← Real.rpow_mul_natCast hH.le, ← Real.rpow_mul_natCast hT.le]
      dsimp only [ncx]
      congr 2 <;> congr 1 <;> ring

variable {K}
variable {S : Set (HeightOneSpectrum (𝓞 K))} [Fintype S]
variable {F : FiniteMellinData K S}

/-- Actual finite Mellin factors and actual gamma factors share this
uniform bound, with the finite input fixed before the constant. -/
theorem reflectionMultiplier_fixedAngular_bound
    (hF : FiniteMellinAdmissible K S F) (hU : StripUniform hF)
    (θ₀ : HeckeCharacter K) {σlo Λ : ℝ}
    (hlo : -(1 / 3 : ℝ) < σlo) (hΛ : σlo ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (θ : HeckeCharacter K),
      (∀ v, archShift K θ v = archShift K θ₀ v) →
      ∀ (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (s : ℂ),
      σlo ≤ s.re → s.re ≤ Λ →
      ‖reflectionMultiplier K S F θ u κ s‖ ≤
        C * radialHeight K θ ^ (4 * ncx K * (|σlo| + |Λ|)) *
          (1 + |s.im|) ^ (4 * ncx K * s.re) := by
  obtain ⟨Cg, hCg, hg⟩ := gammaPart_fixedAngular_bound K θ₀ hlo hΛ
  obtain ⟨Cf, hCf, hf⟩ := finiteMellinFactor_bound hF hU hlo (hlo.trans_le hΛ)
  have hA := F.A₀_pos
  refine ⟨‖F.C₀⁻¹‖ * (F.A₀ ^ (2 * σlo) + F.A₀ ^ (2 * Λ)) * Cf * Cg,
    by positivity, ?_⟩
  intro θ hang u κ s hs0 hs1
  have hAn : ‖(F.A₀ : ℂ) ^ (2 * s)‖ ≤ F.A₀ ^ (2 * σlo) + F.A₀ ^ (2 * Λ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hA]
    have he : (2 * s).re = 2 * s.re := by simp
    rw [he]
    exact rpow_two_strip_le hA hs0 hs1
  have hfinite := hf u κ s hs0 hs1
  have hgamma := hg θ hang s hs0 hs1
  rw [reflectionMultiplier_eq, norm_mul, norm_mul, norm_mul]
  calc
    _ ≤ ‖F.C₀⁻¹‖ * (F.A₀ ^ (2 * σlo) + F.A₀ ^ (2 * Λ)) * Cf *
        (Cg * radialHeight K θ ^ (4 * ncx K * (|σlo| + |Λ|)) *
          (1 + |s.im|) ^ (4 * ncx K * s.re)) := by gcongr
    _ = _ := by ring

/-- Fixed angular types include every finite-order child and every global
norm twist.  This equality uses the actual Hecke weight formulas. -/
theorem archShift_child (θ₀ ν : HeckeCharacter K) (hν : FiniteOrder ν) (t : ℝ)
    (v : {v : InfinitePlace K // v.IsComplex}) :
    archShift K (ν * θ₀ * heckeNormTwist K t) v = archShift K θ₀ v := by
  unfold archShift
  rw [heckeComplexWeight_mul, heckeComplexWeight_mul,
    heckeComplexWeight_finiteOrder K v.val v.property hν,
    heckeComplexWeight_normTwist, zero_add, add_zero]

theorem archRadial_child (θ₀ ν : HeckeCharacter K) (hν : FiniteOrder ν) (t : ℝ)
    (v : {v : InfinitePlace K // v.IsComplex}) :
    archRadial K (ν * θ₀ * heckeNormTwist K t) v = archRadial K θ₀ v + t := by
  unfold archRadial
  rw [heckeComplexParameter_mul, heckeComplexParameter_mul,
    heckeComplexParameter_finiteOrder K v.val v.property hν,
    heckeComplexParameter_normTwist]
  ring

theorem radialHeight_child_le (θ₀ ν : HeckeCharacter K) (hν : FiniteOrder ν) (t : ℝ) :
    radialHeight K (ν * θ₀ * heckeNormTwist K t) ≤
      (radialHeight K θ₀ + ncx K) * (1 + |t|) := by
  have hsum : (∑ v : {v : InfinitePlace K // v.IsComplex},
      |archRadial K (ν * θ₀ * heckeNormTwist K t) v|) ≤
      (∑ v : {v : InfinitePlace K // v.IsComplex}, |archRadial K θ₀ v|) + ncx K * |t| := by
    calc
      _ ≤ ∑ v : {v : InfinitePlace K // v.IsComplex}, (|archRadial K θ₀ v| + |t|) := by
        apply Finset.sum_le_sum
        intro v hv
        rw [archRadial_child θ₀ ν hν t v]
        exact abs_add_le _ _
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, ncx]
  have hH := radialHeight_ge_one K θ₀
  have hn := ncx_nonneg (K := K)
  dsimp only [radialHeight] at hH ⊢
  nlinarith [abs_nonneg t]

theorem amplitude_fixedAngular_decay
    (hF : FiniteMellinAdmissible K S F) (hU : StripUniform hF)
    (θ₀ : HeckeCharacter K) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (θ : HeckeCharacter K),
      (∀ v, archShift K θ v = archShift K θ₀ v) →
      ∀ (V : SmoothAnnularTest)
      (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (Y t : ℝ),
      ‖amplitude F θ u κ V Y t‖ ≤
        C * radialHeight K θ ^ (9 * ncx K) * testSeminorm V.toFun (order K p) 2 * (1 + |t|) ^ (-((p : ℝ) + 2)) := by
  obtain ⟨Cbase, hCbase, hMbase⟩ := reflectionMultiplier_fixedAngular_bound hF hU θ₀
    (σlo := -(1 / 4 : ℝ)) (Λ := 2) (by norm_num) (by norm_num)
  let cπ : ℝ := ‖(2 * (Real.pi : ℂ))⁻¹‖
  refine ⟨cπ * Cbase * 2 ^ (order K p) * 2, by dsimp [cπ]; positivity, ?_⟩
  intro θ hang V u κ Y t
  let CM := Cbase * radialHeight K θ ^ (9 * ncx K)
  have hCM : 0 ≤ CM := by dsimp [CM]; positivity
  have hM (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (s : ℂ)
      (hs0 : -(1 / 4 : ℝ) ≤ s.re) (hs1 : s.re ≤ 2) :
      ‖reflectionMultiplier K S F θ u κ s‖ ≤ CM * (1 + |s.im|) ^ (4 * ncx K * s.re) := by
    have h := hMbase θ hang u κ s hs0 hs1
    have he : 4 * ncx K * (|-(1 / 4 : ℝ)| + |(2 : ℝ)|) = 9 * ncx K := by
      norm_num
      ring
    simpa only [he] using h
  have hline := line_bounds Y
  have hM' : ∀ s : ℂ, -(1 / 4 : ℝ) ≤ s.re → s.re ≤ 2 →
      ‖reflectionMultiplier K S F θ u κ s‖ ≤ CM * (1 + |s.im|) ^ (4 * ncx K * s.re) := by
    intro s hs0 hs1
    exact hM u κ s hs0 hs1
  have h := fz_pointwise_bound (F := F) θ u κ V hCM hM'
    (h := 0) (J := order K p) (by omega) (by norm_num : (0 : ℝ) < 1)
    hline.1 hline.2 t
  have hI (j : ℕ) (hj : j ≤ order K p) :
      Iint V j (line Y) ≤ testSeminorm V.toFun (order K p) 2 := by
    unfold line
    split_ifs
    · simpa only [neg_div] using Iint_left_le V j (order K p) hj 2
    · exact Iint_right_le V j (order K p) hj 2
  have hIsum : Iint V 0 (line Y) + Iint V (order K p) (line Y) ≤
      2 * testSeminorm V.toFun (order K p) 2 := by
    linarith [hI 0 (by omega), hI (order K p) le_rfl]
  have hsemi : 0 ≤ testSeminorm V.toFun (order K p) 2 :=
    (Iint_nonneg V 0 (line Y)).trans (hI 0 (by omega))
  have he : 4 * ncx K * line Y + (0 : ℝ) - (order K p : ℕ) ≤ -((p : ℝ) + 2) := by
    have hncx := ncx_nonneg (K := K)
    have hm := mul_le_mul_of_nonneg_left hline.2
      (show 0 ≤ 4 * ncx K by positivity)
    have hJ : (p : ℝ) + 8 * ncx K + 2 ≤ (order K p : ℝ) := by
      have hc := Nat.le_ceil (8 * ncx K)
      dsimp [order]
      push_cast
      linarith
    linarith
  have hpow : (1 + |t|) ^ (4 * ncx K * line Y + (0 : ℝ) - (order K p : ℕ)) ≤
      (1 + |t|) ^ (-((p : ℝ) + 2)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) he
  have hfz : ‖fz F θ u κ V 0 1 (vertical Y t)‖ ≤
      CM * (2 ^ (order K p) * (2 * testSeminorm V.toFun (order K p) 2)) *
        (1 + |t|) ^ (-((p : ℝ) + 2)) := by
    have h' : ‖fz F θ u κ V 0 1 (vertical Y t)‖ ≤
        CM * (2 ^ (order K p) * (Iint V 0 (line Y) + Iint V (order K p) (line Y))) *
          (1 + |t|) ^ (4 * ncx K * line Y + (0 : ℝ) - (order K p : ℕ)) := by
      simpa only [Real.one_rpow, mul_one, vertical, Nat.cast_zero] using h
    refine h'.trans ?_
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hIsum (by positivity)) hCM)
      hpow (by positivity) (by positivity)
  rw [amplitude_eq_fz, norm_mul]
  calc
    _ ≤ cπ * (CM * (2 ^ (order K p) * (2 * testSeminorm V.toFun (order K p) 2)) *
        (1 + |t|) ^ (-((p : ℝ) + 2))) :=
      mul_le_mul_of_nonneg_left hfz (norm_nonneg _)
    _ = _ := by dsimp [CM]; ring


theorem profile_fixedAngular_weighted_L1
    (hF : FiniteMellinAdmissible K S F) (hU : StripUniform hF)
    (θ₀ : HeckeCharacter K) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (θ : HeckeCharacter K),
      (∀ v, archShift K θ v = archShift K θ₀ v) →
      ∀ (V : SmoothAnnularTest)
      (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (Y : ℝ), 0 < Y →
      Integrable (fun t : ℝ => (1 + |t|) ^ p * ‖profile F θ u κ V Y t‖) ∧
      (∫ t : ℝ, (1 + |t|) ^ p * ‖profile F θ u κ V Y t‖) ≤
        C * radialHeight K θ ^ (9 * ncx K) * testSeminorm V.toFun (order K p) 2 := by
  obtain ⟨C, hC, hbound⟩ := amplitude_fixedAngular_decay hF hU θ₀ p
  let L : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-(2 : ℝ))
  have hL : 0 ≤ L := integral_nonneg (fun t => by positivity)
  refine ⟨C * L, mul_nonneg hC hL, ?_⟩
  intro θ hang V u κ Y hY
  have hsemi : 0 ≤ testSeminorm V.toFun (order K p) 2 :=
    (Iint_nonneg V 0 2).trans (Iint_right_le V 0 (order K p) (by omega) 2)
  obtain ⟨hint, hle⟩ := weighted_density_integrable_and_bound
    (amplitude F θ u κ V Y) (continuous_amplitude hF θ u κ V Y) hY
    (mul_nonneg (mul_nonneg hC (by positivity)) hsemi) p
    (fun t => hbound θ hang V u κ Y t)
  refine ⟨hint, hle.trans_eq ?_⟩
  change C * radialHeight K θ ^ (9 * ncx K) * testSeminorm V.toFun (order K p) 2 * L =
    C * L * radialHeight K θ ^ (9 * ncx K) * testSeminorm V.toFun (order K p) 2
  ring


/-- The profile constant precedes every finite-order child and norm
height.  The displayed exponent is fixed by the number of complex places. -/
theorem profile_child_weighted_L1 [Finite (SixthLocalClasses K S)]
    (hF : FiniteMellinAdmissible K S F) (θ₀ : HeckeCharacter K) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν : HeckeCharacter K), FiniteOrder ν →
      ∀ (t : ℝ) (V : SmoothAnnularTest)
        (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (Y : ℝ), 0 < Y →
      Integrable (fun s : ℝ => (1 + |s|) ^ p *
        ‖profile F (ν * θ₀ * heckeNormTwist K t) u κ V Y s‖) ∧
      (∫ s : ℝ, (1 + |s|) ^ p *
        ‖profile F (ν * θ₀ * heckeNormTwist K t) u κ V Y s‖) ≤
        C * (1 + |t|) ^ (9 * ncx K) * testSeminorm V.toFun (order K p) 2 := by
  obtain ⟨C, hC, hb⟩ := profile_fixedAngular_weighted_L1 hF (stripUniform_of_finite hF) θ₀ p
  have hbase : 0 ≤ radialHeight K θ₀ + ncx K := by
    have hH := radialHeight_ge_one K θ₀
    have hn := ncx_nonneg (K := K)
    linarith
  refine ⟨C * (radialHeight K θ₀ + ncx K) ^ (9 * ncx K), by positivity, ?_⟩
  intro ν hν t V u κ Y hY
  obtain ⟨hi, he⟩ := hb (ν * θ₀ * heckeNormTwist K t)
    (archShift_child θ₀ ν hν t) V u κ Y hY
  refine ⟨hi, he.trans ?_⟩
  have hsemi : 0 ≤ testSeminorm V.toFun (order K p) 2 :=
    (Iint_nonneg V 0 2).trans (Iint_right_le V 0 (order K p) (by omega) 2)
  have hp := Real.rpow_le_rpow (zero_le_one.trans (radialHeight_ge_one K _))
    (radialHeight_child_le θ₀ ν hν t) (mul_nonneg (by norm_num) (ncx_nonneg (K := K)))
  rw [Real.mul_rpow hbase (by positivity)] at hp
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC) hsemi).trans_eq
    (by ring)

#print axioms place_bound_uniform_radial
#print axioms reflectionMultiplier_fixedAngular_bound
#print axioms radialHeight_child_le
#print axioms profile_child_weighted_L1

end HeckeSkeleton.LowEnergy.GeneralHeight
