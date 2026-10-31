import ActualSexticCoefficientBound
import ActualMeanZeroProductPoisson

/-! UNCOMPILED / native 0. A genuine fixed-S-fiber weight on the actual
common-denominator period quotient and its actual trace-product lattice.
It has the original q_C bound and proved mean zero for nonexceptional k.
The S-place part of the period remains explicit in the final norm ratio. -/

noncomputable section
namespace HeckeGeneral.Characters.ActualGramCoefficientBoundDraft
open AlgebraicNumberTheory.PowerResidueSymbols
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open ActualGramJointMeanDraft ActualGramJointChartDraft ActualGramJointChartCoverDraft
open ActualTraceProductResidueQuotientDraft ActualMeanZeroProductPoissonDraft
open ActualNormalizedLatticeMaskDraft
open scoped Classical BigOperators nonZeroDivisors FourierTransform

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
local notation "NZ" => NonzeroRingElements (S.integer K)
variable (c k : NonzeroRingElements (S.integer K))
local notation "C" => actualFrequencyIdeal K S c
local notation "J" => actualFrequencyIdeal K S k
local notation "hc" => actualFrequencyIdeal_ne_zero K S c
local notation "hk" => actualFrequencyIdeal_ne_zero K S k
local notation "hCS" => actualFrequencyIdeal_exterior K S c
local notation "hJS" => actualFrequencyIdeal_exterior K S k
local notation "P" => jointPlaces K C J hc hk
local notation "A" => jointResidues K C J hc hk
local notation "h6" => jointAwaySix K S C J hc hk hCS hJS hS6
local notation "red" => jointReduction K S C J hc hk hCS hJS
local notation:max "Q" N:max => periodQuotient K S ζ hζ C J hc hk N
local notation:max "U" N:max => 𝓞 K ⧸ clearedSModulus K S ζ hζ N
local notation:max "e" N:max => chartCRT K S ζ hζ C J hc hk hCS hJS N
local instance periodicResidueField (p : P) : Field (residue K C J hc hk p) := Ideal.Quotient.field _
local instance periodicResidueFintype (p : P) : Fintype (residue K C J hc hk p) := Fintype.ofFinite _

def fixedChartPeriodIdeal (N : ℕ) : (Ideal (𝓞 K))⁰ :=
  ⟨clearedSModulus K S ζ hζ N * jointRadical K C J hc hk,
    mem_nonZeroDivisors_of_ne_zero (mul_ne_zero
      (clearedSModulus_ne_zero K S ζ hζ N) (jointRadical_ne_zero K C J hc hk))⟩

local instance periodFinite (N : ℕ) : Finite (Q N) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ (mul_ne_zero
    (clearedSModulus_ne_zero K S ζ hζ N) (jointRadical_ne_zero K C J hc hk))
local instance periodFintype (N : ℕ) : Fintype (Q N) := Fintype.ofFinite _
local instance sPeriodFinite (N : ℕ) : Finite (U N) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ (clearedSModulus_ne_zero K S ζ hζ N)
local instance sPeriodFintype (N : ℕ) : Fintype (U N) := Fintype.ofFinite _

/-- Actual CRT, regrouped to separate the S residue pair from the exterior pair. -/
def separatedChartCRT (N : ℕ) : (Q N × Q N) ≃ ((U N × U N) × (A × A)) where
  toFun q := (((e N q.1).1, (e N q.2).1), ((e N q.1).2, (e N q.2).2))
  invFun q := ((e N).symm (q.1.1, q.2.1), (e N).symm (q.1.2, q.2.2))
  left_inv q := by
    apply Prod.ext <;> simp only [Prod.mk.eta, RingEquiv.symm_apply_apply]
  right_inv q := by
    simp only [RingEquiv.apply_symm_apply]

/-- The fixed-S pair is retained as an actual zero mask. Exterior coordinates
are scaled by the actual common denominator, including all zero residues. -/
def fixedChartPeriodWeight (N M : ℕ) (a₁ a₂ : U N) (d b₁ b₂ : NZ)
    (q : Q N × Q N) : ℂ :=
  if ((e N q.1).1, (e N q.2).1) = (a₁, a₂) then
    actualChartPhase K S ζ hζ σ k b₁ b₂ *
      jointCoefficient K ζ hζ σ C J hc hk h6 (red d.val) (red k.val)
        (denominatorScale K S C J hc hk hCS hJS M (e N q.1).2,
         denominatorScale K S C J hc hk hCS hJS M (e N q.2).2)
  else 0

theorem norm_fixedChartPeriodWeight_le_absNorm (N M : ℕ) (a₁ a₂ : U N)
    (d b₁ b₂ : NZ) (q : Q N × Q N) :
    ‖fixedChartPeriodWeight K S ζ hζ σ hS6 c k N M a₁ a₂ d b₁ b₂ q‖ ≤
      (Ideal.absNorm C : ℝ) := by
  unfold fixedChartPeriodWeight
  split_ifs
  · rw [norm_mul, norm_actualChartPhase K ζ hζ σ S, one_mul]
    exact norm_jointCoefficient_le_absNorm K ζ hζ σ C J hc hk h6 _ _ _
  · rw [norm_zero]
    exact Nat.cast_nonneg _

theorem sum_fixedChartPeriodWeight_eq_zero (N M : ℕ) (a₁ a₂ : U N)
    (d b₁ b₂ : NZ) (p : P) (hpC : ¬ p.val.asIdeal ∣ C)
    (hpJ : ¬ 6 ∣ idealPrimeMultiplicity K p.val J) :
    (∑ q, fixedChartPeriodWeight K S ζ hζ σ hS6 c k N M a₁ a₂ d b₁ b₂ q) = 0 := by
  let ds := denominatorScale K S C J hc hk hCS hJS M
  have hsum : (∑ m : A × A,
      jointCoefficient K ζ hζ σ C J hc hk h6 (red d.val) (red k.val)
        (ds m.1, ds m.2)) = 0 := by
    calc
      _ = ∑ m : A × A,
          jointCoefficient K ζ hζ σ C J hc hk h6 (red d.val) (red k.val) m :=
        Fintype.sum_equiv (ds.prodCongr ds) _ _ (fun _ => rfl)
      _ = 0 := sum_jointCoefficient_eq_zero K ζ hζ σ C J hc hk h6 p hpC hpJ _ _
  calc
    _ = ∑ q : (U N × U N) × (A × A),
        if q.1 = (a₁, a₂) then
          actualChartPhase K S ζ hζ σ k b₁ b₂ *
            jointCoefficient K ζ hζ σ C J hc hk h6 (red d.val) (red k.val)
              (ds q.2.1, ds q.2.2) else 0 :=
      Fintype.sum_equiv (separatedChartCRT K S ζ hζ c k N) _ _ (fun _ => rfl)
    _ = 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_eq_zero
      intro s _
      by_cases hs : s = (a₁, a₂)
      · simp only [if_pos hs]
        rw [← Finset.mul_sum, hsum, mul_zero]
      · simp only [if_neg hs, Finset.sum_const_zero]

local notation:max "Fiber" N:max a:max => chartFiber K S ζ hζ C J hc hk hCS hJS N a

/-- Exact value on the constructed ordinary fiber, before applying any estimate. -/
theorem fixedChartPeriodWeight_on_fiber (N M : ℕ) (a₁ a₂ : U N)
    (d b₁ b₂ : NZ) (q₁ : Fiber N a₁) (q₂ : Fiber N a₂) :
    fixedChartPeriodWeight K S ζ hζ σ hS6 c k N M a₁ a₂ d b₁ b₂ (q₁.val, q₂.val) =
      actualChartPhase K S ζ hζ σ k b₁ b₂ *
        jointCoefficient K ζ hζ σ C J hc hk h6 (red d.val) (red k.val)
          (scaledChartFiberEquiv K S ζ hζ C J hc hk hCS hJS N M a₁ q₁,
           scaledChartFiberEquiv K S ζ hζ C J hc hk hCS hJS N M a₂ q₂) := by
  unfold fixedChartPeriodWeight
  rw [if_pos (Prod.ext q₁.property q₂.property)]
  rfl

/-- On the same actual fixed fibers, the quotient weight is the literal
raw sextic times actual RCorrection times the residual extension. -/
theorem fixedChartPeriodWeight_eq_original_on_representatives
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
    (d m₀₁ m₀₂ : NZ) (M L : ℕ) (a z₁ z₂ : 𝓞 K)
    (hd : algebraMap (𝓞 K) (S.integer K) ((finiteSIntegerDenominator K S) ^ L) *
      d.val = algebraMap (𝓞 K) (S.integer K) a)
    (h₁ : algebraMap (𝓞 K) (S.integer K) ((finiteSIntegerDenominator K S) ^ M) *
      m₀₁.val = algebraMap (𝓞 K) (S.integer K) z₁)
    (h₂ : algebraMap (𝓞 K) (S.integer K) ((finiteSIntegerDenominator K S) ^ M) *
      m₀₂.val = algebraMap (𝓞 K) (S.integer K) z₂)
    (hb₁ : (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₀₁)).2 ∈
      finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ))
    (hb₂ : (sLocalNonzeroIntegerDiagonal K S (divisorColumn K S d m₀₂)).2 ∈
      finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ))
    (q₁ : Fiber (M + L) (Ideal.Quotient.mk _ z₁))
    (q₂ : Fiber (M + L) (Ideal.Quotient.mk _ z₂)) :
    fixedChartPeriodWeight K S ζ hζ σ hS6 c k (M + L) M
      (Ideal.Quotient.mk _ z₁) (Ideal.Quotient.mk _ z₂) d
      (divisorColumn K S d m₀₁) (divisorColumn K S d m₀₂) (q₁.val, q₂.val) =
    originalChartCoefficient K S ζ hζ σ hS6 c k d
      (fiberRepresentative K S ζ hζ C J hc hk hCS hJS (M + L) M _ q₁)
      (fiberRepresentative K S ζ hζ C J hc hk hCS hJS (M + L) M _ q₂) := by
  let m₁ := fiberRepresentative K S ζ hζ C J hc hk hCS hJS (M + L) M _ q₁
  let m₂ := fiberRepresentative K S ζ hζ C J hc hk hCS hJS (M + L) M _ q₂
  have hchart₁ : divisorColumn K S d m₁ ∈
      fixedSChart K S ζ hζ (divisorColumn K S d m₀₁) :=
    divisorColumn_chart_of_cleared_congruence K S ζ hζ M L d _ m₀₁ a _ z₁ hd
      (fiberRepresentative_clear K S ζ hζ C J hc hk hCS hJS (M + L) M _ q₁) h₁
      (ordinaryRepresentative_sub_mem K S ζ hζ C J hc hk hCS hJS (M + L) z₁ q₁)
  have hchart₂ : divisorColumn K S d m₂ ∈
      fixedSChart K S ζ hζ (divisorColumn K S d m₀₂) :=
    divisorColumn_chart_of_cleared_congruence K S ζ hζ M L d _ m₀₂ a _ z₂ hd
      (fiberRepresentative_clear K S ζ hζ C J hc hk hCS hJS (M + L) M _ q₂) h₂
      (ordinaryRepresentative_sub_mem K S ζ hζ C J hc hk hCS hJS (M + L) z₂ q₂)
  rw [fixedChartPeriodWeight_on_fiber,
    scaledChartFiberEquiv_eq_representative_reduction,
    scaledChartFiberEquiv_eq_representative_reduction]
  exact (raw_mul_RCorrection_mul_residual_eq_chart_jointCoefficient
    K S ζ hζ σ hS6 c k Γ d m₁ (divisorColumn K S d m₀₁)
    m₂ (divisorColumn K S d m₀₂) hchart₁ hchart₂ hb₁ hb₂).symm

/-- Transport to the actual lattice quotient, rather than an abstract mask. -/
def fixedChartLatticeWeight (N M : ℕ) (a₁ a₂ : U N) (d b₁ b₂ : NZ)
    (q : LatticeQuotient (ordinaryProductLattice K)
      (integralProductLattice K (fixedChartPeriodIdeal K S ζ hζ c k N))) : ℂ :=
  fixedChartPeriodWeight K S ζ hζ σ hS6 c k N M a₁ a₂ d b₁ b₂
    (traceProductResidueEquiv K (fixedChartPeriodIdeal K S ζ hζ c k N) q)

@[simp] theorem fixedChartLatticeWeight_mk_integer (N M : ℕ) (a₁ a₂ : U N)
    (d b₁ b₂ : NZ) (z₁ z₂ : 𝓞 K) :
    fixedChartLatticeWeight K S ζ hζ σ hS6 c k N M a₁ a₂ d b₁ b₂
      (latticeQuotientMap (ordinaryProductLattice K)
        (integralProductLattice K (fixedChartPeriodIdeal K S ζ hζ c k N))
        (traceProductIntegerEquiv K (z₁, z₂))) =
      fixedChartPeriodWeight K S ζ hζ σ hS6 c k N M a₁ a₂ d b₁ b₂
        (Ideal.Quotient.mk _ z₁, Ideal.Quotient.mk _ z₂) := by
  unfold fixedChartLatticeWeight
  rw [traceProductResidueEquiv_mk_integer]
  rfl

theorem norm_fixedChartLatticeWeight_le_absNorm (N M : ℕ) (a₁ a₂ : U N)
    (d b₁ b₂ : NZ) (q : LatticeQuotient (ordinaryProductLattice K)
      (integralProductLattice K (fixedChartPeriodIdeal K S ζ hζ c k N))) :
    ‖fixedChartLatticeWeight K S ζ hζ σ hS6 c k N M a₁ a₂ d b₁ b₂ q‖ ≤
      (Ideal.absNorm C : ℝ) :=
  norm_fixedChartPeriodWeight_le_absNorm K S ζ hζ σ hS6 c k N M a₁ a₂ d b₁ b₂ _

theorem sum_fixedChartLatticeWeight_eq_zero (N M : ℕ) (a₁ a₂ : U N)
    (d b₁ b₂ : NZ) (p : P) (hpC : ¬ p.val.asIdeal ∣ C)
    (hpJ : ¬ 6 ∣ idealPrimeMultiplicity K p.val J) :
    (∑ q, fixedChartLatticeWeight K S ζ hζ σ hS6 c k N M a₁ a₂ d b₁ b₂ q) = 0 := by
  letI : Fintype (𝓞 K ⧸ (fixedChartPeriodIdeal K S ζ hζ c k N : Ideal (𝓞 K))) :=
    inferInstanceAs (Fintype (Q N))
  calc
    _ = ∑ q : Q N × Q N,
        fixedChartPeriodWeight K S ζ hζ σ hS6 c k N M a₁ a₂ d b₁ b₂ q :=
      Fintype.sum_equiv
        (traceProductResidueEquiv K (fixedChartPeriodIdeal K S ζ hζ c k N)).toEquiv
        _ _ (fun _ => rfl)
    _ = 0 := sum_fixedChartPeriodWeight_eq_zero K S ζ hζ σ hS6 c k N M a₁ a₂
      d b₁ b₂ p hpC hpJ

/-- The actual normalized finite Fourier coefficient has the precise q_C
bound at every dual frequency, including nonprimitive frequencies. -/
theorem norm_fixedChart_normalized_mask_le_absNorm (N M : ℕ) (a₁ a₂ : U N)
    (d b₁ b₂ : NZ)
    (m : dualLattice (integralProductLattice K (fixedChartPeriodIdeal K S ζ hζ c k N))) :
    ‖normalizedLatticeMaskCoefficient (ordinaryProductLattice K)
      (integralProductLattice K (fixedChartPeriodIdeal K S ζ hζ c k N))
      (fixedChartLatticeWeight K S ζ hζ σ hS6 c k N M a₁ a₂ d b₁ b₂) m‖ ≤
      (Ideal.absNorm C : ℝ) :=
  norm_normalizedLatticeMaskCoefficient_le _ _ _
    (norm_fixedChartLatticeWeight_le_absNorm K S ζ hζ σ hS6 c k N M a₁ a₂ d b₁ b₂) m

theorem fixedChart_normalized_mask_zero (N M : ℕ) (a₁ a₂ : U N)
    (d b₁ b₂ : NZ) (p : P) (hpC : ¬ p.val.asIdeal ∣ C)
    (hpJ : ¬ 6 ∣ idealPrimeMultiplicity K p.val J) :
    normalizedLatticeMaskCoefficient (ordinaryProductLattice K)
      (integralProductLattice K (fixedChartPeriodIdeal K S ζ hζ c k N))
      (fixedChartLatticeWeight K S ζ hζ σ hS6 c k N M a₁ a₂ d b₁ b₂) 0 = 0 :=
  normalizedLatticeMaskCoefficient_zero_of_sum_zero _ _ _
    (sum_fixedChartLatticeWeight_eq_zero K S ζ hζ σ hS6 c k N M a₁ a₂ d b₁ b₂ p hpC hpJ)

variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

include S Γ in
/-- The actual arithmetic quotient weight discharges both weight premises
of the uniform mean-zero product Poisson theorem. Constants precede c,k,
the denominator exponents, the divisor, centers, test, scale and translation. -/
theorem exists_uniform_fixedChartLatticeWeight_bound (B : ℕ) (hB : 2 < B) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (c k : NZ) (N M : ℕ)
      (a₁ a₂ : 𝓞 K ⧸ clearedSModulus K S ζ hζ N) (d b₁ b₂ : NZ)
      (p : jointPlaces K (actualFrequencyIdeal K S c) (actualFrequencyIdeal K S k)
        (actualFrequencyIdeal_ne_zero K S c) (actualFrequencyIdeal_ne_zero K S k)),
      (¬ p.val.asIdeal ∣ actualFrequencyIdeal K S c) →
      (¬ 6 ∣ idealPrimeMultiplicity K p.val (actualFrequencyIdeal K S k)) →
      ∀ (F : SchwartzMap (traceProductSpace K) ℂ) (X : ℝ), 0 < X →
      ∀ v : traceProductSpace K,
      ‖productPeriodicSum K (fixedChartPeriodIdeal K S ζ hζ c k N)
        (fixedChartLatticeWeight K S ζ hζ σ hS6 c k N M a₁ a₂ d b₁ b₂) F X v‖ ≤
      C₀ * (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
        SchwartzMap.seminorm ℂ (Module.finrank ℚ K * B) 0 (𝓕 F) * X ^ 2 *
        ((Ideal.absNorm (fixedChartPeriodIdeal K S ζ hζ c k N).val : ℝ) / X) ^ B := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_uniform_productPeriodicSum_bound K S Γ B hB
  refine ⟨C₀, hC₀, ?_⟩
  intro c k N M a₁ a₂ d b₁ b₂ p hpC hpJ F X hX v
  exact hbound (fixedChartPeriodIdeal K S ζ hζ c k N)
    (fixedChartLatticeWeight K S ζ hζ σ hS6 c k N M a₁ a₂ d b₁ b₂) F X
    (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) hX (Nat.cast_nonneg _)
    (norm_fixedChartLatticeWeight_le_absNorm K S ζ hζ σ hS6 c k N M a₁ a₂ d b₁ b₂)
    (sum_fixedChartLatticeWeight_eq_zero K S ζ hζ σ hS6 c k N M a₁ a₂
      d b₁ b₂ p hpC hpJ) v

end HeckeGeneral.Characters.ActualGramCoefficientBoundDraft
