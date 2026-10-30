import HeckeSkeleton.ThetaKernel.Gamma
import HeckeSkeleton.ThetaKernel.Finite

/-! Holomorphy on `Re s > -1/3` and polynomial strip bounds for the reflection
multiplier. -/

noncomputable section
namespace HeckeSkeleton.ThetaKernel
open NumberField IsDedekindDomain HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.Characters
open HeckeGeneral.Analysis
open scoped Classical BigOperators ComplexConjugate

/-- One complex place of the Gamma part of the reflection multiplier. -/
def placeFactor (α ρ : ℝ) (s : ℂ) : ℂ :=
  (Complex.Gamma ((α : ℂ) + s + Complex.I * ρ + 1 / 6) /
      Complex.Gamma ((α : ℂ) - s - Complex.I * ρ + 1 / 6)) *
    (Complex.Gamma ((α : ℂ) + s + Complex.I * ρ - 1 / 6) /
      Complex.Gamma ((α : ℂ) - s - Complex.I * ρ - 1 / 6))

variable (K : Type) [Field K] [NumberField K]

def gammaPart (θ : HeckeCharacter K) (s : ℂ) : ℂ :=
  ∏ v : {v : InfinitePlace K // v.IsComplex}, placeFactor (archShift K θ v) (archRadial K θ v) s

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (F : FiniteMellinData K S)

theorem reflectionMultiplier_eq (θ : HeckeCharacter K) (u : SixthUnitClasses K S)
    (κ : SixthLocalClasses K S) (s : ℂ) :
    reflectionMultiplier K S F θ u κ s =
      F.C₀⁻¹ * (F.A₀ : ℂ) ^ (2 * s) * finiteMellinFactor K S F u κ s * gammaPart K θ s := rfl

variable {K S F}

theorem differentiableAt_placeFactor {α : ℝ} (ρ : ℝ) (hα : 1 / 2 ≤ α) {s : ℂ}
    (hs : -(1 / 3 : ℝ) < s.re) : DifferentiableAt ℂ (placeFactor α ρ) s := by
  have hnum : ∀ c : ℝ, 0 < α + c + s.re →
      DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma ((α : ℂ) + s + Complex.I * ρ + c)) s := by
    intro c hc
    have hd : DifferentiableAt ℂ Complex.Gamma ((α : ℂ) + s + Complex.I * ρ + c) := by
      refine Complex.differentiableAt_Gamma _ (fun m h => ?_)
      have := congrArg Complex.re h
      simp at this
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    exact hd.comp s (by fun_prop)
  have hden : ∀ c : ℝ, DifferentiableAt ℂ
      (fun s : ℂ => (Complex.Gamma ((α : ℂ) - s - Complex.I * ρ + c))⁻¹) s := fun c =>
    (Complex.differentiable_one_div_Gamma _).comp s (by fun_prop)
  have h1 := hnum (1 / 6) (by linarith)
  have h2 := hnum (-(1 / 6)) (by linarith)
  have h3 := hden (1 / 6)
  have h4 := hden (-(1 / 6))
  unfold placeFactor
  simp only [div_eq_mul_inv]
  have e1 : (fun s : ℂ => Complex.Gamma ((α : ℂ) + s + Complex.I * ρ + 1 / 6)) =
      fun s : ℂ => Complex.Gamma ((α : ℂ) + s + Complex.I * ρ + ((1 / 6 : ℝ) : ℂ)) := by
    ext s; push_cast; rfl
  have e2 : (fun s : ℂ => Complex.Gamma ((α : ℂ) + s + Complex.I * ρ - 1 / 6)) =
      fun s : ℂ => Complex.Gamma ((α : ℂ) + s + Complex.I * ρ + ((-(1 / 6) : ℝ) : ℂ)) := by
    ext s; push_cast; ring_nf
  have e3 : (fun s : ℂ => (Complex.Gamma ((α : ℂ) - s - Complex.I * ρ + 1 / 6))⁻¹) =
      fun s : ℂ => (Complex.Gamma ((α : ℂ) - s - Complex.I * ρ + ((1 / 6 : ℝ) : ℂ)))⁻¹ := by
    ext s; push_cast; rfl
  have e4 : (fun s : ℂ => (Complex.Gamma ((α : ℂ) - s - Complex.I * ρ - 1 / 6))⁻¹) =
      fun s : ℂ => (Complex.Gamma ((α : ℂ) - s - Complex.I * ρ + ((-(1 / 6) : ℝ) : ℂ)))⁻¹ := by
    ext s; push_cast; ring_nf
  rw [← e1] at h1; rw [← e2] at h2; rw [← e3] at h3; rw [← e4] at h4
  exact (h1.mul h3).mul (h2.mul h4)

theorem place_bound {α : ℝ} (ρ : ℝ) (hα : 1 / 2 ≤ α) {σlo Λ : ℝ} (hlo : -(1 / 3 : ℝ) < σlo)
    (hΛ : σlo ≤ Λ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ s : ℂ, σlo ≤ s.re → s.re ≤ Λ →
      ‖placeFactor α ρ s‖ ≤ c * (1 + |s.im|) ^ (4 * s.re) := by
  obtain ⟨C1, hC1, h1⟩ := norm_Gamma_quot_complex_bound (β := α + 1 / 6) (by linarith)
    (by linarith) hΛ
  obtain ⟨C2, hC2, h2⟩ := norm_Gamma_quot_complex_bound (β := α - 1 / 6) (by linarith)
    (by linarith) hΛ
  refine ⟨C1 * C2 * (1 + |ρ|) ^ (4 * (|σlo| + |Λ|)), by positivity, ?_⟩
  intro s hs0 hs1
  set z : ℂ := s + Complex.I * ρ with hz
  have hzre : z.re = s.re := by simp [hz]
  have hzim : z.im = s.im + ρ := by simp [hz]
  have q1 := h1 z (by rw [hzre]; exact hs0) (by rw [hzre]; exact hs1)
  have q2 := h2 z (by rw [hzre]; exact hs0) (by rw [hzre]; exact hs1)
  have eq1 : placeFactor α ρ s =
      (Complex.Gamma (((α + 1 / 6 : ℝ) : ℂ) + z) / Complex.Gamma (((α + 1 / 6 : ℝ) : ℂ) - z)) *
      (Complex.Gamma (((α - 1 / 6 : ℝ) : ℂ) + z) / Complex.Gamma (((α - 1 / 6 : ℝ) : ℂ) - z)) := by
    unfold placeFactor
    have a1 : (α : ℂ) + s + Complex.I * ρ + 1 / 6 = ((α + 1 / 6 : ℝ) : ℂ) + z := by
      rw [hz]; push_cast; ring
    have a2 : (α : ℂ) - s - Complex.I * ρ + 1 / 6 = ((α + 1 / 6 : ℝ) : ℂ) - z := by
      rw [hz]; push_cast; ring
    have a3 : (α : ℂ) + s + Complex.I * ρ - 1 / 6 = ((α - 1 / 6 : ℝ) : ℂ) + z := by
      rw [hz]; push_cast; ring
    have a4 : (α : ℂ) - s - Complex.I * ρ - 1 / 6 = ((α - 1 / 6 : ℝ) : ℂ) - z := by
      rw [hz]; push_cast; ring
    rw [a1, a2, a3, a4]
  rw [eq1, norm_mul]
  have hT : 0 < 1 + |z.im| := by positivity
  have hprod : ‖Complex.Gamma (((α + 1 / 6 : ℝ) : ℂ) + z) / Complex.Gamma (((α + 1 / 6 : ℝ) : ℂ) - z)‖ *
      ‖Complex.Gamma (((α - 1 / 6 : ℝ) : ℂ) + z) / Complex.Gamma (((α - 1 / 6 : ℝ) : ℂ) - z)‖ ≤
      C1 * C2 * (1 + |s.im + ρ|) ^ (4 * s.re) := by
    have := mul_le_mul q1 q2 (norm_nonneg _) (by positivity)
    refine this.trans (le_of_eq ?_)
    rw [hzre, hzim]
    have : (1 + |s.im + ρ|) ^ (4 * s.re) =
        (1 + |s.im + ρ|) ^ (2 * s.re) * (1 + |s.im + ρ|) ^ (2 * s.re) := by
      rw [← Real.rpow_add (by positivity)]; ring_nf
    rw [this]; ring
  refine hprod.trans ?_
  have hsh := rpow_shift_bound (4 * s.re) ρ s.im
  have hsh' : (1 + |s.im + ρ|) ^ (4 * s.re) ≤ (1 + |ρ|) ^ (4 * (|σlo| + |Λ|)) *
      (1 + |s.im|) ^ (4 * s.re) := by
    refine hsh.trans ?_
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg ρ])
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4)]
    have : |s.re| ≤ |σlo| + |Λ| := by
      rcases abs_cases s.re with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
      · have := le_abs_self Λ; have := abs_nonneg σlo; linarith
      · have := neg_le_abs σlo; have := abs_nonneg Λ; linarith
    linarith
  calc C1 * C2 * (1 + |s.im + ρ|) ^ (4 * s.re)
      ≤ C1 * C2 * ((1 + |ρ|) ^ (4 * (|σlo| + |Λ|)) * (1 + |s.im|) ^ (4 * s.re)) :=
        mul_le_mul_of_nonneg_left hsh' (by positivity)
    _ = _ := by ring

theorem archShift_ge (θ : HeckeCharacter K) (v : {v : InfinitePlace K // v.IsComplex}) :
    1 / 2 ≤ archShift K θ v := by
  unfold archShift
  have : (0 : ℝ) ≤ ((|heckeComplexWeight K v.val v.property θ| : ℤ) : ℝ) :=
    Int.cast_nonneg (abs_nonneg _)
  linarith

theorem differentiableAt_gammaPart (θ : HeckeCharacter K) {s : ℂ} (hs : -(1 / 3 : ℝ) < s.re) :
    DifferentiableAt ℂ (gammaPart K θ) s := by
  unfold gammaPart
  exact DifferentiableAt.fun_finsetProd (fun v _ =>
    differentiableAt_placeFactor _ (archShift_ge θ v) hs)

theorem gammaPart_bound (θ : HeckeCharacter K) {σlo Λ : ℝ} (hlo : -(1 / 3 : ℝ) < σlo)
    (hΛ : σlo ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σlo ≤ s.re → s.re ≤ Λ →
      ‖gammaPart K θ s‖ ≤ C * (1 + |s.im|) ^
        (4 * (Fintype.card {v : InfinitePlace K // v.IsComplex} : ℝ) * s.re) := by
  have hv := fun v : {v : InfinitePlace K // v.IsComplex} =>
    place_bound (archRadial K θ v) (archShift_ge θ v) hlo hΛ
  choose c hc0 hc using hv
  refine ⟨∏ v, c v, Finset.prod_nonneg (fun v _ => hc0 v), ?_⟩
  intro s h0 h1
  unfold gammaPart
  rw [norm_prod]
  calc ∏ v : {v : InfinitePlace K // v.IsComplex},
        ‖placeFactor (archShift K θ v) (archRadial K θ v) s‖
      ≤ ∏ v : {v : InfinitePlace K // v.IsComplex}, c v * (1 + |s.im|) ^ (4 * s.re) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun v _ => hc v s h0 h1)
    _ = (∏ v, c v) * ((1 + |s.im|) ^ (4 * s.re)) ^ Fintype.card {v : InfinitePlace K // v.IsComplex} := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    _ = _ := by
        rw [← Real.rpow_mul_natCast (by positivity)]
        congr 2; ring

theorem rpow_two_strip_le {A : ℝ} (hA : 0 < A) {σ σlo Λ : ℝ} (h0 : σlo ≤ σ) (h1 : σ ≤ Λ) :
    A ^ (2 * σ) ≤ A ^ (2 * σlo) + A ^ (2 * Λ) := by
  have p0 : 0 ≤ A ^ (2 * σlo) := by positivity
  have p1 : 0 ≤ A ^ (2 * Λ) := by positivity
  rcases le_or_gt 1 A with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h (show 2 * σ ≤ 2 * Λ by linarith)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge hA h.le (show 2 * σlo ≤ 2 * σ by linarith)
    linarith

theorem differentiableAt_reflectionMultiplier (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) {s : ℂ}
    (hs : -(1 / 3 : ℝ) < s.re) : DifferentiableAt ℂ (reflectionMultiplier K S F θ u κ) s := by
  have hA : (F.A₀ : ℂ) ≠ 0 := by exact_mod_cast F.A₀_pos.ne'
  have h1 : DifferentiableAt ℂ (fun s : ℂ => (F.A₀ : ℂ) ^ (2 * s)) s :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl hA)
  have h2 := differentiableAt_finiteMellinFactor hF u κ hs
  have h3 := differentiableAt_gammaPart (K := K) θ hs
  unfold reflectionMultiplier
  exact ((((differentiableAt_const _).mul h1).mul h2).mul h3 :)

theorem reflectionMultiplier_bound_aux (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) {σlo Λ : ℝ} (hlo : -(1 / 3 : ℝ) < σlo) (hΛ : σlo ≤ Λ) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (s : ℂ),
      σlo ≤ s.re → s.re ≤ Λ →
      ‖reflectionMultiplier K S F θ u κ s‖ ≤
        (‖F.C₀⁻¹‖ * (F.A₀ ^ (2 * σlo) + F.A₀ ^ (2 * Λ)) *
          max (finiteStripConst hF u κ σlo Λ) 0 * Cg) * (1 + |s.im|) ^
        (4 * (Fintype.card {v : InfinitePlace K // v.IsComplex} : ℝ) * s.re) := by
  obtain ⟨Cg, hCg0, hCg⟩ := gammaPart_bound (K := K) θ hlo hΛ
  have hA := F.A₀_pos
  refine ⟨Cg, hCg0, ?_⟩
  intro u κ s h0 h1
  rw [reflectionMultiplier_eq, norm_mul, norm_mul, norm_mul]
  have hAn : ‖(F.A₀ : ℂ) ^ (2 * s)‖ ≤ F.A₀ ^ (2 * σlo) + F.A₀ ^ (2 * Λ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hA]
    have : (2 * s).re = 2 * s.re := by simp
    rw [this]
    exact rpow_two_strip_le hA h0 h1
  have hf := (finiteMellinFactor_norm_le hF u κ hlo (lt_of_lt_of_le hlo hΛ) s h0 h1).trans
    (le_max_left (finiteStripConst hF u κ σlo Λ) 0)
  have hg := hCg s h0 h1
  have p : 0 ≤ (1 + |s.im|) ^
        (4 * (Fintype.card {v : InfinitePlace K // v.IsComplex} : ℝ) * s.re) := by positivity
  calc ‖F.C₀⁻¹‖ * ‖(F.A₀ : ℂ) ^ (2 * s)‖ * ‖finiteMellinFactor K S F u κ s‖ * ‖gammaPart K θ s‖
      ≤ ‖F.C₀⁻¹‖ * (F.A₀ ^ (2 * σlo) + F.A₀ ^ (2 * Λ)) * max (finiteStripConst hF u κ σlo Λ) 0 *
          (Cg * (1 + |s.im|) ^
        (4 * (Fintype.card {v : InfinitePlace K // v.IsComplex} : ℝ) * s.re)) := by
        gcongr
    _ = _ := by ring

theorem reflectionMultiplier_bound_pt (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S)
    {σlo Λ : ℝ} (hlo : -(1 / 3 : ℝ) < σlo) (hΛ : σlo ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σlo ≤ s.re → s.re ≤ Λ →
      ‖reflectionMultiplier K S F θ u κ s‖ ≤ C * (1 + |s.im|) ^
        (4 * (Fintype.card {v : InfinitePlace K // v.IsComplex} : ℝ) * s.re) := by
  obtain ⟨Cg, hCg0, hCg⟩ := reflectionMultiplier_bound_aux hF θ hlo hΛ
  exact ⟨‖F.C₀⁻¹‖ * (F.A₀ ^ (2 * σlo) + F.A₀ ^ (2 * Λ)) *
    max (finiteStripConst hF u κ σlo Λ) 0 * Cg, by have := F.A₀_pos; positivity,
    fun s h0 h1 => hCg u κ s h0 h1⟩

theorem reflectionMultiplier_bound (hF : FiniteMellinAdmissible K S F) (hU : StripUniform hF)
    (θ : HeckeCharacter K) {σlo Λ : ℝ} (hlo : -(1 / 3 : ℝ) < σlo) (hΛ : σlo ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (s : ℂ),
      σlo ≤ s.re → s.re ≤ Λ →
      ‖reflectionMultiplier K S F θ u κ s‖ ≤ C * (1 + |s.im|) ^
        (4 * (Fintype.card {v : InfinitePlace K // v.IsComplex} : ℝ) * s.re) := by
  obtain ⟨Cg, hCg0, hCg⟩ := reflectionMultiplier_bound_aux hF θ hlo hΛ
  obtain ⟨B, hB⟩ := hU σlo Λ hlo (lt_of_lt_of_le hlo hΛ)
  have hA := F.A₀_pos
  refine ⟨‖F.C₀⁻¹‖ * (F.A₀ ^ (2 * σlo) + F.A₀ ^ (2 * Λ)) * max B 0 * Cg, by positivity,
    fun u κ s h0 h1 => ?_⟩
  refine (hCg u κ s h0 h1).trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have : max (finiteStripConst hF u κ σlo Λ) 0 ≤ max B 0 := max_le_max (hB u κ) le_rfl
  have h2 : 0 ≤ ‖F.C₀⁻¹‖ * (F.A₀ ^ (2 * σlo) + F.A₀ ^ (2 * Λ)) := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this h2) hCg0

end HeckeSkeleton.ThetaKernel
