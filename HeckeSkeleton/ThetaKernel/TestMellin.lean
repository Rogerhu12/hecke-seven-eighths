import HeckeGeneral.Analysis.GlobalThetaData

/-! Mellin transforms of smooth annular tests: entireness, Euler integration by
parts, and the weighted bounds `|w|^j |M V(-w)| ≤ ∫ |E^j V| y^{-σ-1}`. -/

noncomputable section
namespace HeckeSkeleton.ThetaKernel
open MeasureTheory Set Filter HeckeGeneral.ThetaSkeleton.Global
open scoped ContDiff Topology

/-- Smooth functions vanishing outside `[a,b]`. -/
structure Good (a b : ℝ) (g : ℝ → ℂ) : Prop where
  pos : 0 < a
  smooth : ContDiff ℝ ∞ g
  zero : ∀ y, y ∉ Icc a b → g y = 0

variable {a b : ℝ} {g : ℝ → ℂ}

theorem Good.eventually_zero (h : Good a b g) {y : ℝ} (hy : y ∉ Icc a b) :
    ∀ᶠ x in 𝓝 y, g x = 0 := by
  have : ∀ᶠ x in 𝓝 y, x ∉ Icc a b := (isClosed_Icc.isOpen_compl).mem_nhds hy
  filter_upwards [this] with x hx using h.zero x hx

theorem Good.euler (h : Good a b g) : Good a b (fun y : ℝ => (y : ℂ) * deriv g y) := by
  refine ⟨h.pos, (Complex.ofRealCLM.contDiff (𝕜 := ℝ)).mul (contDiff_infty_iff_deriv.mp h.smooth).2, ?_⟩
  intro y hy
  have h0 : deriv g y = 0 := by
    have : g =ᶠ[𝓝 y] fun _ => (0 : ℂ) := h.eventually_zero hy
    rw [this.deriv_eq]; simp
  simp [h0]

theorem Good.eulerDerivativeOrder (h : Good a b g) (j : ℕ) :
    Good a b (HeckeGeneral.ThetaSkeleton.Global.eulerDerivativeOrder j g) := by
  induction j with
  | zero => simpa [HeckeGeneral.ThetaSkeleton.Global.eulerDerivativeOrder] using h
  | succ j ih =>
    have : HeckeGeneral.ThetaSkeleton.Global.eulerDerivativeOrder (j + 1) g =
        fun y : ℝ => (y : ℂ) * deriv (HeckeGeneral.ThetaSkeleton.Global.eulerDerivativeOrder j g) y := by
      unfold HeckeGeneral.ThetaSkeleton.Global.eulerDerivativeOrder
      rw [Function.iterate_succ_apply']
      rfl
    rw [this]
    exact ih.euler

theorem Good.continuous (h : Good a b g) : Continuous g := h.smooth.continuous

theorem Good.integrableOn_mellin (h : Good a b g) (s : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • g t) (Ioi 0) := by
  have ha := h.pos
  have hc : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • g t) (Icc a b) := by
    intro t ht
    have : t ≠ 0 := (lt_of_lt_of_le ha ht.1).ne'
    exact ((Complex.continuousAt_ofReal_cpow_const t (s - 1) (Or.inr this)).smul
      h.continuous.continuousAt).continuousWithinAt
  refine IntegrableOn.of_forall_sdiff_eq_zero (hc.integrableOn_Icc) measurableSet_Ioi ?_
  intro x hx
  have : x ∉ Icc a b := hx.2
  simp [h.zero x this]

theorem Good.mellin_euler (h : Good a b g) (s : ℂ) :
    mellin (fun y : ℝ => (y : ℂ) * deriv g y) s = -s * mellin g s := by
  have hd : Differentiable ℝ g := h.smooth.differentiable (by simp)
  have hE := h.euler
  have cpow_sub_one_mul : ∀ {x : ℝ}, 0 < x → (x : ℂ) ^ (s - 1) * (x : ℂ) = (x : ℂ) ^ s := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
    have h1 : (x : ℂ) ^ s = (x : ℂ) ^ (s - 1) * (x : ℂ) ^ (1 : ℂ) := by
      rw [← Complex.cpow_add (s - 1) 1 hx0, show s - 1 + 1 = s by ring]
    rw [h1, Complex.cpow_one]
  have hu : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ s) (s * (x : ℂ) ^ (s - 1)) x := by
    intro x hx
    by_cases hs : s = 0
    · subst hs
      simpa using hasDerivAt_const x (1 : ℂ)
    · exact hasDerivAt_ofReal_cpow_const (ne_of_gt hx) hs
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt g (deriv g x) x :=
    fun x _ => (hd x).hasDerivAt
  have hpt : ∀ x : ℝ, 0 < x →
      (x : ℂ) ^ (s - 1) * ((x : ℂ) * deriv g x) = (x : ℂ) ^ s * deriv g x := by
    intro x hx
    rw [← mul_assoc, cpow_sub_one_mul hx]
  have hconv := hE.integrableOn_mellin s
  have huv' : IntegrableOn (fun x : ℝ => (x : ℂ) ^ s * deriv g x) (Ioi 0) := by
    refine hconv.congr_fun (fun x hx => ?_) measurableSet_Ioi
    exact hpt x hx
  have hu'v : IntegrableOn (fun x : ℝ => (s * (x : ℂ) ^ (s - 1)) * g x) (Ioi 0) := by
    have h0 := h.integrableOn_mellin s
    have h1 : Integrable (fun x : ℝ => s * ((x : ℂ) ^ (s - 1) * g x))
        (volume.restrict (Ioi 0)) := by
      simpa only [smul_eq_mul] using h0.const_mul s
    simpa only [mul_assoc, IntegrableOn] using h1
  have hzero : Tendsto (fun x : ℝ => (x : ℂ) ^ s * g x) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT h.pos] with x hx
    rw [h.zero x (fun hm => absurd hm.1 (not_le.mpr hx.2))]; simp
  have hinf : Tendsto (fun x : ℝ => (x : ℂ) ^ s * g x) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop b] with x hx
    rw [h.zero x (fun hm => absurd hm.2 (not_le.mpr hx))]; simp
  have key := integral_Ioi_mul_deriv_eq_deriv_mul (a := (0 : ℝ))
    (u := fun x : ℝ => (x : ℂ) ^ s) (u' := fun x : ℝ => s * (x : ℂ) ^ (s - 1))
    (v := g) (v' := deriv g) (a' := 0) (b' := 0) hu hv huv' hu'v hzero hinf
  have hcongr : (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) • ((x : ℂ) * deriv g x))
      = ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ s * deriv g x := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    simpa only [smul_eq_mul] using hpt x hx
  have hkey2 : (∫ x in Ioi (0 : ℝ), (s * (x : ℂ) ^ (s - 1)) * g x)
      = s * ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * g x := by
    simp only [mul_assoc]
    rw [integral_const_mul]
  simp only [mellin, smul_eq_mul] at hcongr ⊢
  rw [hcongr, key, hkey2]
  ring

theorem eulerDerivativeOrder_succ (f : ℝ → ℂ) (j : ℕ) :
    eulerDerivativeOrder (j + 1) f =
      fun y : ℝ => (y : ℂ) * deriv (eulerDerivativeOrder j f) y := by
  unfold eulerDerivativeOrder
  rw [Function.iterate_succ_apply']
  rfl

variable (V : SmoothAnnularTest)

theorem good_toFun : Good V.lower V.upper V.toFun :=
  ⟨V.lower_pos, V.smooth, fun y hy => Function.notMem_support.mp (fun h => hy (V.support h))⟩

/-- Euler iterates of the test. -/
def eul (j : ℕ) : ℝ → ℂ := eulerDerivativeOrder j V.toFun

theorem good_eul (j : ℕ) : Good V.lower V.upper (eul V j) :=
  (good_toFun V).eulerDerivativeOrder j

theorem mellin_eul (j : ℕ) (s : ℂ) :
    mellin (eul V j) s = (-s) ^ j * mellin V.toFun s := by
  induction j with
  | zero => simp [eul, eulerDerivativeOrder]
  | succ j ih =>
    have : eul V (j + 1) = fun y : ℝ => (y : ℂ) * deriv (eul V j) y :=
      eulerDerivativeOrder_succ V.toFun j
    rw [this, (good_eul V j).mellin_euler, ih, pow_succ]
    ring

/-- The weighted absolute Mellin integrals of Euler derivatives. -/
def Iint (j : ℕ) (σ : ℝ) : ℝ := ∫ y in Ioi (0 : ℝ), ‖eul V j y‖ * y ^ (-σ - 1)

theorem integrableOn_Iint (j : ℕ) (σ : ℝ) :
    IntegrableOn (fun y : ℝ => ‖eul V j y‖ * y ^ (-σ - 1)) (Ioi 0) := by
  have h : IntegrableOn (fun a : ℝ => ‖(a : ℂ) ^ (((-σ : ℝ) : ℂ) - 1) • eul V j a‖) (Ioi 0) :=
    ((good_eul V j).integrableOn_mellin ((-σ : ℝ) : ℂ)).norm
  refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
  have hy' : (0 : ℝ) < y := hy
  simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hy']
  simp [mul_comm]

theorem Iint_nonneg (j : ℕ) (σ : ℝ) : 0 ≤ Iint V j σ :=
  setIntegral_nonneg measurableSet_Ioi (fun y hy => by
    have : (0 : ℝ) < y := hy
    positivity)

theorem norm_pow_mul_mellin_le (j : ℕ) (σ t : ℝ) :
    ‖(σ : ℂ) + t * Complex.I‖ ^ j * ‖mellin V.toFun (-((σ : ℂ) + t * Complex.I))‖ ≤
      Iint V j σ := by
  set w : ℂ := (σ : ℂ) + t * Complex.I with hw
  have h := mellin_eul V j (-w)
  rw [neg_neg] at h
  have h1 : ‖w‖ ^ j * ‖mellin V.toFun (-w)‖ = ‖mellin (eul V j) (-w)‖ := by
    rw [h, norm_mul, norm_pow]
  rw [h1, mellin]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
  have hy' : (0 : ℝ) < y := hy
  simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hy']
  have : (-w - 1).re = -σ - 1 := by simp [hw]
  rw [this, mul_comm]

theorem Iint_add_eq (j : ℕ) (A : ℝ) :
    Iint V j (-1 / 4) + Iint V j A = testIntegral V.toFun j A := by
  unfold Iint testIntegral
  rw [← integral_add (integrableOn_Iint V j _) (integrableOn_Iint V j _)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
  have hy' : (0 : ℝ) < y := hy
  have e1 : y ^ (-(-1 / 4 : ℝ) - 1) = y ^ (1 / 4 : ℝ) / y := by
    rw [← Real.rpow_sub_one hy'.ne']; norm_num
  have e2 : y ^ (-A - 1) = y ^ (-A) / y := by
    rw [← Real.rpow_sub_one hy'.ne']
  unfold eul
  rw [e1, e2]
  field_simp

theorem testIntegral_le_seminorm (j J : ℕ) (hj : j ≤ J) (A : ℝ) :
    testIntegral V.toFun j A ≤ testSeminorm V.toFun J A := by
  unfold testSeminorm
  exact (le_max_right _ _).trans
    (Finset.le_sup' (fun j => max 0 (testIntegral V.toFun j A))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))

theorem Iint_left_le (j J : ℕ) (hj : j ≤ J) (A : ℝ) :
    Iint V j (-1 / 4) ≤ testSeminorm V.toFun J A := by
  have := Iint_add_eq V j A
  have := Iint_nonneg V j A
  have := testIntegral_le_seminorm V j J hj A
  linarith

theorem Iint_right_le (j J : ℕ) (hj : j ≤ J) (A : ℝ) :
    Iint V j A ≤ testSeminorm V.toFun J A := by
  have := Iint_add_eq V j A
  have := Iint_nonneg V j (-1 / 4)
  have := testIntegral_le_seminorm V j J hj A
  linarith

theorem Iint_strip_le (j : ℕ) {σ σ1 σ2 : ℝ} (h1 : σ1 ≤ σ) (h2 : σ ≤ σ2) :
    Iint V j σ ≤ Iint V j σ1 + Iint V j σ2 := by
  unfold Iint
  rw [← integral_add (integrableOn_Iint V j _) (integrableOn_Iint V j _)]
  refine setIntegral_mono_on (integrableOn_Iint V j _)
    ((integrableOn_Iint V j _).add (integrableOn_Iint V j _)) measurableSet_Ioi (fun y hy => ?_)
  have hy' : (0 : ℝ) < y := hy
  have : y ^ (-σ - 1) ≤ y ^ (-σ1 - 1) + y ^ (-σ2 - 1) := by
    rcases le_or_gt 1 y with hy1 | hy1
    · have := Real.rpow_le_rpow_of_exponent_le hy1 (show -σ - 1 ≤ -σ1 - 1 by linarith)
      have := Real.rpow_nonneg hy'.le (-σ2 - 1)
      linarith
    · have := Real.rpow_le_rpow_of_exponent_ge hy' hy1.le (show -σ2 - 1 ≤ -σ - 1 by linarith)
      have := Real.rpow_nonneg hy'.le (-σ1 - 1)
      linarith
  show ‖eul V j y‖ * y ^ (-σ - 1) ≤ ‖eul V j y‖ * y ^ (-σ1 - 1) + ‖eul V j y‖ * y ^ (-σ2 - 1)
  calc _ ≤ ‖eul V j y‖ * (y ^ (-σ1 - 1) + y ^ (-σ2 - 1)) :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := by ring

theorem one_add_pow_le (x : ℝ) (hx : 0 ≤ x) (J : ℕ) : (1 + x) ^ J ≤ 2 ^ J * (1 + x ^ J) := by
  rcases le_or_gt x 1 with h | h
  · calc (1 + x) ^ J ≤ 2 ^ J := pow_le_pow_left₀ (by linarith) (by linarith) J
      _ ≤ 2 ^ J * (1 + x ^ J) := by
          have : 0 ≤ x ^ J := pow_nonneg hx J
          nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) J]
  · calc (1 + x) ^ J ≤ (2 * x) ^ J := pow_le_pow_left₀ (by linarith) (by linarith) J
      _ = 2 ^ J * x ^ J := mul_pow _ _ _
      _ ≤ 2 ^ J * (1 + x ^ J) := by
          have : 0 ≤ x ^ J := pow_nonneg hx J
          nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) J]

/-- The rapid-decay estimate for the Mellin transform on a vertical line. -/
theorem pow_mul_norm_mellin_le (J : ℕ) (σ t : ℝ) :
    (1 + ‖(σ : ℂ) + t * Complex.I‖) ^ J * ‖mellin V.toFun (-((σ : ℂ) + t * Complex.I))‖ ≤
      2 ^ J * (Iint V 0 σ + Iint V J σ) := by
  set w : ℂ := (σ : ℂ) + t * Complex.I with hw
  have h0 := norm_pow_mul_mellin_le V 0 σ t
  have h1 := norm_pow_mul_mellin_le V J σ t
  rw [← hw] at h0 h1
  simp only [pow_zero, one_mul] at h0
  calc (1 + ‖w‖) ^ J * ‖mellin V.toFun (-w)‖
      ≤ (2 ^ J * (1 + ‖w‖ ^ J)) * ‖mellin V.toFun (-w)‖ :=
        mul_le_mul_of_nonneg_right (one_add_pow_le _ (norm_nonneg w) J) (norm_nonneg _)
    _ = 2 ^ J * (‖mellin V.toFun (-w)‖ + ‖w‖ ^ J * ‖mellin V.toFun (-w)‖) := by ring
    _ ≤ 2 ^ J * (Iint V 0 σ + Iint V J σ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith

theorem differentiable_mellin_neg : Differentiable ℂ (fun w : ℂ => mellin V.toFun (-w)) := by
  have hs : ∀ s : ℂ, DifferentiableAt ℂ (mellin V.toFun) s := by
    intro s
    have hz : ∀ (e : ℝ), V.toFun =O[atTop] (fun x : ℝ => x ^ e) ∧
        V.toFun =O[𝓝[>] 0] (fun x : ℝ => x ^ e) := by
      intro e
      constructor
      · have : V.toFun =ᶠ[atTop] fun _ => (0 : ℂ) := by
          filter_upwards [eventually_gt_atTop V.upper] with x hx
          exact (good_toFun V).zero x (fun hm => absurd hm.2 (not_le.mpr hx))
        exact this.trans_isBigO (Asymptotics.isBigO_zero _ _)
      · have : V.toFun =ᶠ[𝓝[>] 0] fun _ => (0 : ℂ) := by
          filter_upwards [Ioo_mem_nhdsGT V.lower_pos] with x hx
          exact (good_toFun V).zero x (fun hm => absurd hm.1 (not_le.mpr hx.2))
        exact this.trans_isBigO (Asymptotics.isBigO_zero _ _)
    exact mellin_differentiableAt_of_isBigO_rpow
      (V.smooth.continuous.locallyIntegrable.locallyIntegrableOn _)
      (a := s.re + 1) (b := s.re - 1) (by simpa using (hz (-(s.re + 1))).1) (by linarith)
      (by simpa using (hz (-(s.re - 1))).2) (by linarith)
  intro w
  exact (hs (-w)).comp w differentiableAt_id.neg

end HeckeSkeleton.ThetaKernel
