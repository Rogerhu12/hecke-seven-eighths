import HeckeSkeleton.ThetaKernel.Deriv

/-!
# The theta reflection kernel: integrability, line independence, derivative bound

Generic versions (for an arbitrary `F : FiniteMellinData K S` satisfying
`FiniteMellinAdmissible K S F` and an arbitrary period character `θ`) of the
three kernel obligations `TH-KERNEL-INTEGRABLE`, `TH-KERNEL-LINE-INDEPENDENT`,
`TH-KERNEL-DERIVATIVE-BOUND` of `HeckeSkeleton/Theta.lean`.
-/

noncomputable section
namespace HeckeSkeleton.ThetaKernel
open NumberField IsDedekindDomain MeasureTheory Set Filter
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.Characters
open scoped Classical BigOperators ComplexConjugate Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (F : FiniteMellinData K S)

/-- TH-KERNEL-INTEGRABLE (generic). -/
theorem kernel_integrable (θ : HeckeCharacter K) (hF : FiniteMellinAdmissible K S F) :
    ∀ (V : SmoothAnnularTest) u κ σ y, -(1 / 3 : ℝ) < σ → 0 < y →
      Integrable (kernelIntegrand K S F θ u κ V.toFun σ y) := by
  intro V u κ σ y hσ hy
  have : kernelIntegrand K S F θ u κ V.toFun σ y =
      fun t : ℝ => fz F θ u κ V 0 y ((σ : ℂ) + (t : ℂ) * Complex.I) :=
    funext (kernelIntegrand_eq_fz F θ u κ V σ y)
  rw [this]
  exact fz_integrable hF θ u κ V 0 hy hσ

/-- TH-KERNEL-LINE-INDEPENDENT (generic). -/
theorem kernel_line_independent (θ : HeckeCharacter K) (hF : FiniteMellinAdmissible K S F) :
    ∀ (V : SmoothAnnularTest) u κ σ σ' y,
      -(1 / 3 : ℝ) < σ → -(1 / 3 : ℝ) < σ' → 0 < y →
      mellinReflectionKernel K S F θ u κ V.toFun σ y =
        mellinReflectionKernel K S F θ u κ V.toFun σ' y := by
  intro V u κ σ σ' y hσ hσ' hy
  rw [mellinReflectionKernel_eq_Gc, mellinReflectionKernel_eq_Gc]
  unfold Gc
  rcases le_total σ σ' with h | h
  · rw [fz_shift hF θ u κ V 0 hy hσ h]
  · rw [fz_shift hF θ u κ V 0 hy hσ' h]

variable {K S F}

theorem eulerOrder_congr_Ioi {f g : ℝ → ℂ} (hfg : ∀ y, 0 < y → f y = g y) (m : ℕ) :
    ∀ y, 0 < y → eulerDerivativeOrder m f y = eulerDerivativeOrder m g y := by
  induction m with
  | zero => simpa [eulerDerivativeOrder] using hfg
  | succ m ih =>
    intro y hy
    rw [eulerDerivativeOrder_succ, eulerDerivativeOrder_succ]
    show (y : ℂ) * deriv (eulerDerivativeOrder m f) y =
      (y : ℂ) * deriv (eulerDerivativeOrder m g) y
    congr 1
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [Ioi_mem_nhds hy] with x hx using ih x hx

theorem eulerOrder_Gc (hF : FiniteMellinAdmissible K S F) (θ : HeckeCharacter K)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (V : SmoothAnnularTest)
    {σ : ℝ} (hσ : -(1 / 3 : ℝ) < σ) (m : ℕ) :
    ∀ y, 0 < y → eulerDerivativeOrder m (fun y => Gc F θ u κ V 0 σ y) y =
      Gc F θ u κ V m σ y := by
  induction m with
  | zero => intro y _; simp [eulerDerivativeOrder]
  | succ m ih =>
    intro y hy
    rw [eulerDerivativeOrder_succ]
    show (y : ℂ) * deriv (eulerDerivativeOrder m (fun y => Gc F θ u κ V 0 σ y)) y = _
    have hev : eulerDerivativeOrder m (fun y => Gc F θ u κ V 0 σ y) =ᶠ[𝓝 y]
        fun y => Gc F θ u κ V m σ y := by
      filter_upwards [Ioi_mem_nhds hy] with x hx using ih x hx
    rw [hev.deriv_eq, (hasDerivAt_Gc hF θ u κ V m hσ hy).deriv]
    have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    field_simp

theorem norm_two_pi_inv : ‖(2 * (Real.pi : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
  rw [norm_inv, norm_mul]
  simp [abs_of_pos Real.pi_pos]

theorem Gc_norm_le (θ : HeckeCharacter K) (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S)
    (V : SmoothAnnularTest) {σ CM : ℝ} (hCM : 0 ≤ CM)
    (hM : ∀ s : ℂ, σ ≤ s.re → s.re ≤ σ →
      ‖reflectionMultiplier K S F θ u κ s‖ ≤ CM * (1 + |s.im|) ^ (4 * ncx K * s.re))
    {h J : ℕ} (hhJ : h ≤ J) {e : ℝ} (he : 1 < e)
    (hexp : 4 * ncx K * σ + (h : ℝ) - J ≤ -e) {y : ℝ} (hy : 0 < y) :
    ‖Gc F θ u κ V h σ y‖ ≤ (2 * Real.pi)⁻¹ *
      (CM * (2 ^ J * (Iint V 0 σ + Iint V J σ)) * y ^ (-σ)) * ∫ t : ℝ, (1 + |t|) ^ (-e) := by
  unfold Gc
  rw [norm_mul, norm_two_pi_inv]
  have hint := (integrable_one_add_abs_rpow_neg he).const_mul
    (CM * (2 ^ J * (Iint V 0 σ + Iint V J σ)) * y ^ (-σ))
  have hle : ‖∫ t : ℝ, fz F θ u κ V h y ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      ∫ t : ℝ, (CM * (2 ^ J * (Iint V 0 σ + Iint V J σ)) * y ^ (-σ)) * (1 + |t|) ^ (-e) := by
    refine norm_integral_le_of_norm_le hint (ae_of_all _ (fun t => ?_))
    refine (fz_pointwise_bound (F := F) θ u κ V hCM hM hhJ hy le_rfl le_rfl t).trans ?_
    have hT1 : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
    have := Real.rpow_le_rpow_of_exponent_le hT1 hexp
    have hB : 0 ≤ CM * (2 ^ J * (Iint V 0 σ + Iint V J σ)) * y ^ (-σ) := by
      have := Iint_nonneg V 0 σ; have := Iint_nonneg V J σ
      positivity
    exact mul_le_mul_of_nonneg_left this hB
  rw [integral_const_mul] at hle
  have : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  exact mul_le_mul_of_nonneg_left hle this |>.trans (le_of_eq (by ring))

variable (K S F)

/-- TH-KERNEL-DERIVATIVE-BOUND (generic), under the uniformity hypothesis
`StripUniform hF` (the constant must be uniform in the local class `κ`); this is
implied by finiteness of `SixthLocalClasses K S`, see `kernel_derivative_bound`. -/
theorem kernel_derivative_bound_of_uniform (θ : HeckeCharacter K)
    (hF : FiniteMellinAdmissible K S F) (hU : StripUniform hF) :
    ∀ (A : ℝ) (h J : ℕ), 0 ≤ A →
      4 * (Fintype.card {v : InfinitePlace K // v.IsComplex} : ℝ) * A + h + 1 < J →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : SmoothAnnularTest) u κ y, 0 < y →
        ‖eulerDerivativeOrder h
          (mellinReflectionKernel K S F θ u κ V.toFun 0) y‖ ≤
        C * testSeminorm V.toFun J A * min (y ^ (1 / 4 : ℝ)) (y ^ (-A)) := by
  intro A h J hA hJ
  have hncx : ncx K = (Fintype.card {v : InfinitePlace K // v.IsComplex} : ℝ) := rfl
  have hr := ncx_nonneg (K := K)
  have hJ' : 4 * ncx K * A + h + 1 < J := by rw [hncx]; linarith
  have hhJ : h ≤ J := by
    have : (h : ℝ) ≤ J := by nlinarith
    exact_mod_cast this
  obtain ⟨CM1, hCM1, hM1⟩ := reflectionMultiplier_bound hF hU θ (σlo := (-1 / 4 : ℝ))
    (Λ := (-1 / 4 : ℝ)) (by norm_num) le_rfl
  obtain ⟨CM2, hCM2, hM2⟩ := reflectionMultiplier_bound hF hU θ (σlo := A) (Λ := A)
    (by linarith) le_rfl
  have he1 : 1 < (J : ℝ) - h := by
    have : (h : ℝ) + 1 < J := by nlinarith
    linarith
  have he2 : 1 < (J : ℝ) - h - 4 * ncx K * A := by linarith
  set c1 : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-((J : ℝ) - h)) with hc1
  set c2 : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-((J : ℝ) - h - 4 * ncx K * A)) with hc2
  have hc1n : 0 ≤ c1 := integral_nonneg (fun t => by positivity)
  have hc2n : 0 ≤ c2 := integral_nonneg (fun t => by positivity)
  set a1 : ℝ := (2 * Real.pi)⁻¹ * (CM1 * 2 ^ J * 2) * c1 with ha1
  set a2 : ℝ := (2 * Real.pi)⁻¹ * (CM2 * 2 ^ J * 2) * c2 with ha2
  have ha1n : 0 ≤ a1 := by positivity
  have ha2n : 0 ≤ a2 := by positivity
  refine ⟨max a1 a2, le_max_of_le_left ha1n, ?_⟩
  intro V u κ y hy
  set Sm := testSeminorm V.toFun J A with hSm
  have hSm0 : 0 ≤ Sm := (Iint_nonneg V 0 (-1 / 4)).trans (Iint_left_le V 0 J (Nat.zero_le _) A)
  have hI1 : Iint V 0 (-1 / 4) + Iint V J (-1 / 4) ≤ 2 * Sm := by
    have := Iint_left_le V 0 J (Nat.zero_le _) A
    have := Iint_left_le V J J le_rfl A
    linarith
  have hI2 : Iint V 0 A + Iint V J A ≤ 2 * Sm := by
    have := Iint_right_le V 0 J (Nat.zero_le _) A
    have := Iint_right_le V J J le_rfl A
    linarith
  -- identify the Euler derivative with the line integrals
  have hK0 : ∀ y, 0 < y → mellinReflectionKernel K S F θ u κ V.toFun 0 y =
      Gc F θ u κ V 0 (-1 / 4) y := by
    intro y hy
    rw [mellinReflectionKernel_eq_Gc]
    unfold Gc
    rw [fz_shift hF θ u κ V 0 hy (a := (-1 / 4 : ℝ)) (b := 0) (by norm_num) (by norm_num)]
  have hE : eulerDerivativeOrder h (mellinReflectionKernel K S F θ u κ V.toFun 0) y =
      Gc F θ u κ V h (-1 / 4) y := by
    rw [eulerOrder_congr_Ioi (g := fun y => Gc F θ u κ V 0 (-1 / 4) y) hK0 h y hy]
    exact eulerOrder_Gc hF θ u κ V (σ := (-1 / 4 : ℝ)) (by norm_num) h y hy
  have hEA : Gc F θ u κ V h (-1 / 4) y = Gc F θ u κ V h A y := by
    unfold Gc
    rw [fz_shift hF θ u κ V h hy (a := (-1 / 4 : ℝ)) (b := A) (by norm_num) (by linarith)]
  -- the two line bounds
  have b1 := Gc_norm_le θ u κ V (σ := (-1 / 4 : ℝ)) (CM := CM1) hCM1
    (fun s h0 h1 => hM1 u κ s h0 h1) hhJ he1 (by nlinarith) hy
  have b2 := Gc_norm_le θ u κ V (σ := A) (CM := CM2) hCM2
    (fun s h0 h1 => hM2 u κ s h0 h1) hhJ he2 (by nlinarith) hy
  have yp1 : y ^ (-(-1 / 4 : ℝ)) = y ^ (1 / 4 : ℝ) := by norm_num
  rw [yp1] at b1
  have hy1 : 0 ≤ y ^ (1 / 4 : ℝ) := by positivity
  have hy2 : 0 ≤ y ^ (-A) := by positivity
  have n1 : ‖eulerDerivativeOrder h (mellinReflectionKernel K S F θ u κ V.toFun 0) y‖ ≤
      max a1 a2 * Sm * y ^ (1 / 4 : ℝ) := by
    rw [hE]
    refine b1.trans ?_
    have : (2 * Real.pi)⁻¹ * (CM1 * (2 ^ J * (Iint V 0 (-1 / 4) + Iint V J (-1 / 4))) *
        y ^ (1 / 4 : ℝ)) * c1 ≤ a1 * Sm * y ^ (1 / 4 : ℝ) := by
      have hpos : 0 ≤ (2 * Real.pi)⁻¹ * c1 := by positivity
      calc _ = ((2 * Real.pi)⁻¹ * c1) * (CM1 * (2 ^ J * (Iint V 0 (-1 / 4) + Iint V J (-1 / 4)))) *
              y ^ (1 / 4 : ℝ) := by ring
        _ ≤ ((2 * Real.pi)⁻¹ * c1) * (CM1 * (2 ^ J * (2 * Sm))) * y ^ (1 / 4 : ℝ) := by
            gcongr
        _ = _ := by rw [ha1]; ring
    refine this.trans ?_
    gcongr
    exact le_max_left _ _
  have n2 : ‖eulerDerivativeOrder h (mellinReflectionKernel K S F θ u κ V.toFun 0) y‖ ≤
      max a1 a2 * Sm * y ^ (-A) := by
    rw [hE, hEA]
    refine b2.trans ?_
    have : (2 * Real.pi)⁻¹ * (CM2 * (2 ^ J * (Iint V 0 A + Iint V J A)) * y ^ (-A)) * c2 ≤
        a2 * Sm * y ^ (-A) := by
      have hpos : 0 ≤ (2 * Real.pi)⁻¹ * c2 := by positivity
      calc _ = ((2 * Real.pi)⁻¹ * c2) * (CM2 * (2 ^ J * (Iint V 0 A + Iint V J A))) * y ^ (-A) := by
              ring
        _ ≤ ((2 * Real.pi)⁻¹ * c2) * (CM2 * (2 ^ J * (2 * Sm))) * y ^ (-A) := by
            gcongr
        _ = _ := by rw [ha2]; ring
    refine this.trans ?_
    gcongr
    exact le_max_right _ _
  have hC : 0 ≤ max a1 a2 * Sm := mul_nonneg (le_max_of_le_left ha1n) hSm0
  calc _ ≤ min (max a1 a2 * Sm * y ^ (1 / 4 : ℝ)) (max a1 a2 * Sm * y ^ (-A)) := le_min n1 n2
    _ = max a1 a2 * Sm * min (y ^ (1 / 4 : ℝ)) (y ^ (-A)) := by
        rw [mul_min_of_nonneg _ _ hC]

/-- TH-KERNEL-DERIVATIVE-BOUND (generic), for finite `SixthLocalClasses K S`. -/
theorem kernel_derivative_bound [Finite (SixthLocalClasses K S)] (θ : HeckeCharacter K)
    (hF : FiniteMellinAdmissible K S F) :
    ∀ (A : ℝ) (h J : ℕ), 0 ≤ A →
      4 * (Fintype.card {v : InfinitePlace K // v.IsComplex} : ℝ) * A + h + 1 < J →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : SmoothAnnularTest) u κ y, 0 < y →
        ‖eulerDerivativeOrder h
          (mellinReflectionKernel K S F θ u κ V.toFun 0) y‖ ≤
        C * testSeminorm V.toFun J A * min (y ^ (1 / 4 : ℝ)) (y ^ (-A)) :=
  kernel_derivative_bound_of_uniform K S F θ hF (stripUniform_of_finite hF)

end HeckeSkeleton.ThetaKernel
