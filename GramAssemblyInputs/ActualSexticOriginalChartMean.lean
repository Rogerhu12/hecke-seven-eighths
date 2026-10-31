import ActualSexticChartRepresentatives

/-! UNCOMPILED / native 0. Complete finite mean of the literal original
raw sextic coefficient times the actual S correction and the stipulated
prime-power residual extension, on two fixed genuine S charts. The
chart's selected representatives are constructed, not supplied. -/

noncomputable section
namespace HeckeGeneral.Characters
namespace ActualGramJointChartCoverDraft
open AlgebraicNumberTheory.PowerResidueSymbols
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open ActualGramJointMeanDraft ActualGramJointChartDraft
open scoped Classical BigOperators ComplexConjugate
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
local notation "D" => finiteSIntegerDenominator K S
local notation "OS" => S.integer K
local notation "NZ" => NonzeroRingElements OS
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
local instance ActualSexticOriginalChartMean_residueField (p : P) : Field (residue K C J hc hk p) := Ideal.Quotient.field _
local instance ActualSexticOriginalChartMean_residueFintype (p : P) : Fintype (residue K C J hc hk p) := Fintype.ofFinite _
local instance ActualSexticOriginalChartMean_fiberFintype (N : ℕ) (a : 𝓞 K ⧸ clearedSModulus K S ζ hζ N) :
    Fintype (chartFiber K S ζ hζ C J hc hk hCS hJS N a) :=
  Fintype.ofEquiv A (chartFiberEquiv K S ζ hζ C J hc hk hCS hJS N a).symm

local notation:max "F" N:max z:max => chartFiber K S ζ hζ C J hc hk hCS hJS N
  (Ideal.Quotient.mk (clearedSModulus K S ζ hζ N) z)
local notation:max "rep" N:max M:max z:max q:max => fiberRepresentative K S ζ hζ C J hc hk hCS hJS N M
  (Ideal.Quotient.mk (clearedSModulus K S ζ hζ N) z) q
local notation "active" => fun n : NZ => Prod.snd (sLocalNonzeroIntegerDiagonal K S n)

/-- Literal original coefficient, without replacing the actual correction. -/
def originalChartCoefficient (d m₁ m₂ : NZ) : ℂ :=
  (sIntegerSexticRawCoefficient K S ζ hζ σ hS6
      (divisorColumn K S d m₁) (divisorColumn K S d m₂) k *
    sIntegerSexticRCorrection K S ζ hζ σ
      (divisorColumn K S d m₁) (divisorColumn K S d m₂)) *
    actualResidualExtension K S ζ hζ σ C J hc hk hCS hJS hS6
      d.val k.val m₁.val m₂.val

/-- Concrete complete mean; clearing equalities are only arithmetic chart
coordinates. No CRT independence, vanishing, or coprimality is assumed. -/
theorem sum_originalChartCoefficient_eq_zero
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
    (d m₀₁ m₀₂ : NZ) (M L : ℕ) (a z₁ z₂ : 𝓞 K)
    (hd : algebraMap (𝓞 K) OS (D ^ L) * d.val = algebraMap (𝓞 K) OS a)
    (h₁ : algebraMap (𝓞 K) OS (D ^ M) * m₀₁.val = algebraMap (𝓞 K) OS z₁)
    (h₂ : algebraMap (𝓞 K) OS (D ^ M) * m₀₂.val = algebraMap (𝓞 K) OS z₂)
    (hb₁ : active (divisorColumn K S d m₀₁) ∈
      finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ))
    (hb₂ : active (divisorColumn K S d m₀₂) ∈
      finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ))
    (p : P) (hpC : ¬ p.val.asIdeal ∣ C)
    (hpJ : ¬ 6 ∣ idealPrimeMultiplicity K p.val J) :
    (∑ q : F (M + L) z₁ × F (M + L) z₂,
      originalChartCoefficient K S ζ hζ σ hS6 c k d
        (rep (M + L) M z₁ q.1) (rep (M + L) M z₂ q.2)) = 0 := by
  have hchart₁ (q : F (M + L) z₁) :
      divisorColumn K S d (rep (M + L) M z₁ q) ∈
        fixedSChart K S ζ hζ (divisorColumn K S d m₀₁) :=
    divisorColumn_chart_of_cleared_congruence K S ζ hζ M L d _ m₀₁ a _ z₁ hd
      (fiberRepresentative_clear K S ζ hζ C J hc hk hCS hJS (M + L) M _ q) h₁
      (ordinaryRepresentative_sub_mem K S ζ hζ C J hc hk hCS hJS (M + L) z₁ q)
  have hchart₂ (q : F (M + L) z₂) :
      divisorColumn K S d (rep (M + L) M z₂ q) ∈
        fixedSChart K S ζ hζ (divisorColumn K S d m₀₂) :=
    divisorColumn_chart_of_cleared_congruence K S ζ hζ M L d _ m₀₂ a _ z₂ hd
      (fiberRepresentative_clear K S ζ hζ C J hc hk hCS hJS (M + L) M _ q) h₂
      (ordinaryRepresentative_sub_mem K S ζ hζ C J hc hk hCS hJS (M + L) z₂ q)
  have hpoint (q : F (M + L) z₁ × F (M + L) z₂) :
      originalChartCoefficient K S ζ hζ σ hS6 c k d
        (rep (M + L) M z₁ q.1) (rep (M + L) M z₂ q.2) =
      actualChartPhase K S ζ hζ σ k (divisorColumn K S d m₀₁)
        (divisorColumn K S d m₀₂) *
      jointCoefficient K ζ hζ σ C J hc hk h6 (red d.val) (red k.val)
        (scaledChartFiberEquiv K S ζ hζ C J hc hk hCS hJS (M + L) M _ q.1,
         scaledChartFiberEquiv K S ζ hζ C J hc hk hCS hJS (M + L) M _ q.2) := by
    rw [scaledChartFiberEquiv_eq_representative_reduction,
      scaledChartFiberEquiv_eq_representative_reduction]
    exact raw_mul_RCorrection_mul_residual_eq_chart_jointCoefficient
      K S ζ hζ σ hS6 c k Γ d (rep (M + L) M z₁ q.1)
      (divisorColumn K S d m₀₁) (rep (M + L) M z₂ q.2)
      (divisorColumn K S d m₀₂) (hchart₁ q.1) (hchart₂ q.2) hb₁ hb₂
  simp_rw [hpoint]
  exact sum_scaled_chart_jointCoefficient_eq_zero
    K S ζ hζ C J hc hk hCS hJS σ hS6 (M + L) M _ _ p hpC hpJ d.val k.val _

/-- Uniform common-exponent clearing for two actual columns. -/
theorem exists_exactS_clear_pair (m₁ m₂ : OS) :
    ∃ M : ℕ, ∃ z₁ z₂ : 𝓞 K,
      algebraMap (𝓞 K) OS (D ^ M) * m₁ = algebraMap (𝓞 K) OS z₁ ∧
      algebraMap (𝓞 K) OS (D ^ M) * m₂ = algebraMap (𝓞 K) OS z₂ := by
  obtain ⟨M₁, z₁, h₁⟩ := exists_exactS_clear K S m₁
  obtain ⟨M₂, z₂, h₂⟩ := exists_exactS_clear K S m₂
  refine ⟨M₁ + M₂, D ^ M₂ * z₁, D ^ M₁ * z₂, ?_, ?_⟩
  · calc
      _ = algebraMap (𝓞 K) OS (D ^ M₂) *
          (algebraMap (𝓞 K) OS (D ^ M₁) * m₁) := by rw [pow_add, map_mul]; ring
      _ = _ := by rw [h₁, map_mul]
  · calc
      _ = algebraMap (𝓞 K) OS (D ^ M₁) *
          (algebraMap (𝓞 K) OS (D ^ M₂) * m₂) := by rw [pow_add, map_mul]; ring
      _ = _ := by rw [h₂, map_mul]

/-- No supplied clearing data: actual d and chart centers produce a common
finite period and the complete original coefficient has zero mean there. -/
theorem exists_sum_originalChartCoefficient_eq_zero
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
    (d m₀₁ m₀₂ : NZ)
    (hb₁ : active (divisorColumn K S d m₀₁) ∈
      finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ))
    (hb₂ : active (divisorColumn K S d m₀₂) ∈
      finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ))
    (p : P) (hpC : ¬ p.val.asIdeal ∣ C)
    (hpJ : ¬ 6 ∣ idealPrimeMultiplicity K p.val J) :
    ∃ M L : ℕ, ∃ a z₁ z₂ : 𝓞 K,
      algebraMap (𝓞 K) OS (D ^ L) * d.val = algebraMap (𝓞 K) OS a ∧
      algebraMap (𝓞 K) OS (D ^ M) * m₀₁.val = algebraMap (𝓞 K) OS z₁ ∧
      algebraMap (𝓞 K) OS (D ^ M) * m₀₂.val = algebraMap (𝓞 K) OS z₂ ∧
      (∑ q : F (M + L) z₁ × F (M + L) z₂,
        originalChartCoefficient K S ζ hζ σ hS6 c k d
          (rep (M + L) M z₁ q.1) (rep (M + L) M z₂ q.2)) = 0 := by
  obtain ⟨L, a, hd⟩ := exists_exactS_clear K S d.val
  obtain ⟨M, z₁, z₂, h₁, h₂⟩ := exists_exactS_clear_pair K S m₀₁.val m₀₂.val
  exact ⟨M, L, a, z₁, z₂, hd, h₁, h₂,
    sum_originalChartCoefficient_eq_zero K S ζ hζ σ hS6 c k Γ d m₀₁ m₀₂
      M L a z₁ z₂ hd h₁ h₂ hb₁ hb₂ p hpC hpJ⟩

end ActualGramJointChartCoverDraft
end HeckeGeneral.Characters
