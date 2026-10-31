import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstGaussPool

/-!
# One common Fourier measure after the actual first prime pool

The Fourier parameter runs over the whole Euclidean space. All main and
correction polynomials use the same earlier pool. Their integrability is
proved from finite column sums and Schwartz decay, so the integral
comparison does not assume an analytic energy bound or finite Fourier
support. The final theorem starts from the genuine coupled kernel form.
-/

noncomputable section
open scoped Classical BigOperators NumberField FourierTransform SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem jointPhase_neg (ξ x : V) : jointPhase ξ (-x) = star (jointPhase ξ x) := by
  simp only [jointPhase, inner_neg_right, AddChar.map_neg_eq_inv,
    Circle.coe_inv_eq_conj, starRingEnd_apply]

namespace FirstGaussPoolData

variable {ι : Type*}

def twistedCoefficient (c : ι → ℂ) (x : ι → V) (ξ : V) (i : ι) : ℂ :=
  c i * jointPhase ξ (x i)

theorem whole_twisted_eq_fourier {H : Type*}
    (d : FirstGaussPoolData C P ι) (c : ι → ℂ) (G : ι → H → ℂ)
    (x : ι → V) (h : H) (ξ : V) :
    wholePolynomial d.columns (d.adjustedCoefficient (twistedCoefficient c x ξ)) G h =
      jointFourierColumn d.columns (fun i => d.adjustedCoefficient c i * G i h) x ξ := by
  unfold wholePolynomial jointFourierColumn adjustedCoefficient twistedCoefficient
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem mainEnergy_twisted_eq (d : FirstGaussPoolData C P ι)
    (c : ι → ℂ) (x : ι → V) (ξ : V) :
    d.mainEnergy (twistedCoefficient c x ξ) =
      jointColumnEnergy d.mainRows d.columns (fun _ => 1)
        (fun h i => d.adjustedCoefficient c i * d.finiteColumn i h)
        (fun _ => x) ξ := by
  simp only [mainEnergy, jointColumnEnergy, whole_twisted_eq_fourier,
    norm_one, one_mul]

theorem errorEnergy_twisted_eq (d : FirstGaussPoolData C P ι)
    (c : ι → ℂ) (x : ι → V) (t : ℕ) (ξ : V) :
    d.errorEnergy (twistedCoefficient c x ξ) t =
      jointColumnEnergy d.eligible d.columns (fun _ => 1)
        (fun hp i => d.adjustedCoefficient c i * d.errorColumn t i hp)
        (fun _ => x) ξ := by
  simp only [errorEnergy, jointColumnEnergy, whole_twisted_eq_fourier,
    norm_one, one_mul]

def mainMass (d : FirstGaussPoolData C P ι) (c : ι → ℂ) : ℝ :=
  jointColumnMass d.mainRows d.columns (fun _ => 1)
    (fun h i => d.adjustedCoefficient c i * d.finiteColumn i h)

def errorMass (d : FirstGaussPoolData C P ι) (c : ι → ℂ) (t : ℕ) : ℝ :=
  jointColumnMass d.eligible d.columns (fun _ => 1)
    (fun hp i => d.adjustedCoefficient c i * d.errorColumn t i hp)

/-- A finite constant used only to prove convergence of the actual pool
integral. The descent estimate itself retains the explicit energies. -/
def mass (d : FirstGaussPoolData C P ι) (c : ι → ℂ) : ℝ :=
  (4 / d.density) * (d.multiplicity * d.mainMass c +
    d.errorMass c 1 + d.errorMass c 6 + d.errorMass c 7)

theorem energy_twisted_le_mass (d : FirstGaussPoolData C P ι)
    (c : ι → ℂ) (x : ι → V) (ξ : V) :
    d.energy (twistedCoefficient c x ξ) ≤ d.mass c := by
  have hm : d.mainEnergy (twistedCoefficient c x ξ) ≤ d.mainMass c := by
    rw [mainEnergy_twisted_eq]
    exact jointColumnEnergy_le_mass _ _ _ _ _ _
  have he (t : ℕ) : d.errorEnergy (twistedCoefficient c x ξ) t ≤ d.errorMass c t := by
    rw [errorEnergy_twisted_eq]
    exact jointColumnEnergy_le_mass _ _ _ _ _ _
  exact mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hm d.multiplicity_nonneg) (he 1)) (he 6)) (he 7))
    (div_nonneg (by norm_num) d.density_pos.le)

theorem continuous_energy_twisted (d : FirstGaussPoolData C P ι)
    (c : ι → ℂ) (x : ι → V) :
    Continuous (fun ξ => d.energy (twistedCoefficient c x ξ)) := by
  simp_rw [energy, mainEnergy_twisted_eq, errorEnergy_twisted_eq]
  exact continuous_const.mul
    ((((continuous_const.mul (continuous_jointColumnEnergy _ _ _ _ _)).add
      (continuous_jointColumnEnergy _ _ _ _ _)).add
      (continuous_jointColumnEnergy _ _ _ _ _)).add
      (continuous_jointColumnEnergy _ _ _ _ _))

end FirstGaussPoolData

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Actual pool output on both sides is integrable against the same
Fourier measure. No separate integrability assumption is required. -/
theorem first_gauss_pool_kernel_integrable {ι κ : Type*}
    (F : 𝓢(V, ℂ)) (left : FirstGaussPoolData C P ι) (right : FirstGaussPoolData C P κ)
    (c : ι → ℂ) (d : κ → ℂ) (x : ι → V) (y : κ → V)
    (W : ℝ) (hW : 0 ≤ W) :
    Integrable (fun ξ : V => ‖(𝓕 F) ξ‖ *
      (Real.sqrt (W * left.energy (FirstGaussPoolData.twistedCoefficient c x ξ)) *
        Real.sqrt (W * right.energy (FirstGaussPoolData.twistedCoefficient d y ξ)))) := by
  have hc : Continuous (fun ξ : V =>
      Real.sqrt (W * left.energy (FirstGaussPoolData.twistedCoefficient c x ξ)) *
        Real.sqrt (W * right.energy (FirstGaussPoolData.twistedCoefficient d y ξ))) :=
    (Real.continuous_sqrt.comp
      ((continuous_const : Continuous (fun _ : V => W)).mul
        (left.continuous_energy_twisted c x))).mul
      (Real.continuous_sqrt.comp
        ((continuous_const : Continuous (fun _ : V => W)).mul
          (right.continuous_energy_twisted d y)))
  apply ((𝓕 F).integrable (μ := (volume : Measure V))).norm.mul_bdd
    hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ξ => by
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    exact mul_le_mul
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (left.energy_twisted_le_mass c x ξ) hW))
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (right.energy_twisted_le_mass d y ξ) hW))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- Genuine common-kernel separation followed by one actual pool on each
whole Cauchy polynomial. The pool `P`, both arithmetic row charts, and
all finite carriers are fixed before the common Fourier variable. -/
theorem first_gauss_pool_kernel_bound {H ι κ : Type*}
    (F : 𝓢(V, ℂ)) (left : FirstGaussPoolData C P ι) (right : FirstGaussPoolData C P κ)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (rows : Finset H) (frequencyLeft frequencyRight : H → A.R)
    (hleft_inj : Set.InjOn frequencyLeft (rows : Set H))
    (hright_inj : Set.InjOn frequencyRight (rows : Set H))
    (hleft_rows : rows.image frequencyLeft ⊆ left.rows)
    (hright_rows : rows.image frequencyRight ⊆ right.rows)
    (q : H → ℂ) (W : ℝ) (hW : 0 ≤ W) (hq : ∀ h ∈ rows, ‖q h‖ ≤ W)
    (c : ι → ℂ) (d : κ → ℂ) (x : ι → V) (y : κ → V) (z : H → V) :
    ‖jointKernelPairing F rows left.columns right.columns q
      (fun h i => c i * left.gaussColumn hDiff i (frequencyLeft h))
      (fun h j => d j * right.gaussColumn hDiff j (frequencyRight h))
      (fun h i => z h + x i) (fun _ j => y j)‖ ≤
      ∫ ξ : V, ‖(𝓕 F) ξ‖ *
        (Real.sqrt (W * left.energy (FirstGaussPoolData.twistedCoefficient c x ξ)) *
          Real.sqrt (W * right.energy
            (FirstGaussPoolData.twistedCoefficient d (fun j => -y j) ξ))) := by
  have he := joint_kernel_paired_cauchy F rows left.columns right.columns q
    (fun h i => c i * left.gaussColumn hDiff i (frequencyLeft h))
    (fun h j => d j * right.gaussColumn hDiff j (frequencyRight h))
    (fun h i => z h + x i) (fun _ j => y j)
  have hold := joint_kernel_energy_integrable F rows left.columns right.columns q
    (fun h i => c i * left.gaussColumn hDiff i (frequencyLeft h))
    (fun h j => star (d j * right.gaussColumn hDiff j (frequencyRight h)))
    (fun h i => z h + x i) (fun _ j => y j)
  simp_rw [joint_energy_gauss_rows, joint_energy_conjugate_gauss_rows,
    ← jointPhase_neg] at he hold
  apply he.trans
  apply integral_mono hold
    (first_gauss_pool_kernel_integrable F left right c d x (fun j => -y j) W hW)
  intro ξ
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply mul_le_mul
  · exact Real.sqrt_le_sqrt (left.weighted_energy_bound hDiff rows frequencyLeft
      hleft_inj hleft_rows q W hW hq (FirstGaussPoolData.twistedCoefficient c x ξ))
  · exact Real.sqrt_le_sqrt (right.weighted_energy_bound hDiff rows frequencyRight
      hright_inj hright_rows q W hW hq
        (FirstGaussPoolData.twistedCoefficient d (fun j => -y j) ξ))
  · exact Real.sqrt_nonneg _
  · exact Real.sqrt_nonneg _

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.first_gauss_pool_kernel_integrable
#print axioms HeckeSkeleton.Moments.EngineStep.first_gauss_pool_kernel_bound
