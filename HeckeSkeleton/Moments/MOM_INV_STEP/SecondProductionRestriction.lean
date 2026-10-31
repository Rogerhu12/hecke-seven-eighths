import HeckeSkeleton.Moments.MOM_INV_STEP.SecondProductionBoxes

/-!
# Restricting the genuine production source to its first slice

The first live-source and fixed-center indicators occur in the original
outer weight. This file moves them exactly into a finite source subset
before reconstructing canonical children. Zero-weight records outside
the chosen first center therefore cannot enlarge the child packet with
incompatible geometric data. All second marks, source zeros, actual
columns and common spectral measures are unchanged.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondProductionRestriction

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FirstParentRows FirstToSecondData CommonKernel ActualProductionBoxes
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

section Weight

variable {σ : Type*} (T : FirstParentEnergy.Data K S (σ := σ))

def weightOn
    (w : ∀ o : OuterIndex K S D T, FirstOuterCenters.Overlap K S D T o → ℝ)
    (q : ∀ o : OuterIndex K S D T, FirstOuterCenters.Overlap K S D T o → Prop)
    (o : OuterIndex K S D T) (e : FirstOuterCenters.Overlap K S D T o) : ℝ :=
  if q o e then w o e else 0

theorem weightOn_nonneg
    (w : ∀ o : OuterIndex K S D T, FirstOuterCenters.Overlap K S D T o → ℝ)
    (q : ∀ o : OuterIndex K S D T, FirstOuterCenters.Overlap K S D T o → Prop)
    (hw : ∀ o e, 0 ≤ w o e)
    (o : OuterIndex K S D T) (e : FirstOuterCenters.Overlap K S D T o) :
    0 ≤ weightOn K S D T w q o e := by
  unfold weightOn
  split_ifs
  · exact hw o e
  · exact le_rfl

end Weight

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable {σ : Type*} [DecidableEq σ]
variable (T : FirstParentEnergy.Data K S (σ := σ))
variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
variable (hbase : 1 < T.columns.base)
variable (R : OuterIndex K S D T → {r : ℝ // 0 < r})
variable (U : {r : ℝ // 0 < r}) (J₁ : Finset σ) (s : ℝ)
variable (H₂ : ∀ o : OuterIndex K S D T,
  ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K))) →
    Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)) → ℝ)
local notation "Idx" => ProductionIndex K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂
local notation "X" => sourceScale K S T U

def sourceSubset
    (q : ∀ o : OuterIndex K S D T, FirstOuterCenters.Overlap K S D T o → Prop)
    (P : Finset Idx) : Finset Idx :=
  P.filter (fun i => q i.1 i.2.1)

@[simp] theorem mem_sourceSubset
    (q : ∀ o : OuterIndex K S D T, FirstOuterCenters.Overlap K S D T o → Prop)
    (P : Finset Idx) (i : Idx) :
    i ∈ sourceSubset K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ q P ↔
      i ∈ P ∧ q i.1 i.2.1 := by
  simp only [sourceSubset, Finset.mem_filter]

variable (w : ∀ o : OuterIndex K S D T, FirstOuterCenters.Overlap K S D T o → ℝ)
variable (q : ∀ o : OuterIndex K S D T, FirstOuterCenters.Overlap K S D T o → Prop)
variable (ε : ℝ) (side₁ : Bool)

theorem scalar_weightOn (i : Idx) :
    SecondProductionIntegral.scalar K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
      (weightOn K S D T w q) ε i =
    if q i.1 i.2.1 then
      SecondProductionIntegral.scalar K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ w ε i
    else 0 := by
  by_cases hq : q i.1 i.2.1 <;>
    simp [SecondProductionIntegral.scalar, weightOn, hq]

/-- Exact restriction of the actual Fourier/Mellin source integral.
This holds for signed weights; no positivity or energy estimate is
needed to remove the original zero-weight records. -/
theorem sourceIntegral_weightOn (m : ℕ) (side₂ : Bool) (P : Finset Idx)
    (b : SecondMobiusGeometry.Index X) (J₂ : Finset σ) :
    SecondProductionIntegral.sourceIntegral K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
      (weightOn K S D T w q) ε side₁ m side₂ P b J₂ =
    SecondProductionIntegral.sourceIntegral K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
      w ε side₁ m side₂
      (sourceSubset K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ q P) b J₂ := by
  rw [SecondProductionIntegral.sourceIntegral_eq_sum,
    SecondProductionIntegral.sourceIntegral_eq_sum]
  simp only [sourceSubset, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  rw [scalar_weightOn K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ w q ε i]
  by_cases hq : q i.1 i.2.1 <;> simp [hq]

/-- The full literal adaptive second total, carrying the original
first-slice indicator, is a sum of exactly restricted source integrals. -/
theorem actualTotal_weightOn (m : ℕ) (side₂ : Bool) :
    SecondProductionIntegral.actualTotal K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
      (weightOn K S D T w q) ε side₁ m side₂ =
    SecondProductionIntegral.cauchyMass K S T J₁ s *
      ∑ b : SecondMobiusGeometry.Index X, ∑ J₂ ∈ (T.columns.slots \ J₁).powerset,
        SecondProductionIntegral.sourceIntegral K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
          w ε side₁ m side₂
          (sourceSubset K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ q
            (SecondProductionIntegral.bin K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
              Finset.univ b)) b J₂ := by
  rw [SecondProductionIntegral.actualTotal_eq_integrals]
  apply congrArg (fun z : ℝ => SecondProductionIntegral.cauchyMass K S T J₁ s * z)
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro J₂ hJ₂
  exact sourceIntegral_weightOn K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
    w q ε side₁ m side₂ _ b J₂

/-- The original first-slice restriction commutes with the automatic
norm partition. In particular every later packet uses the same slice. -/
theorem normBox_sourceSubset (hmask : T.mask = ∅) (P : Finset Idx)
    (Z L : ℝ) (j : BoxIndex Z L) :
    SecondProductionBoxes.normBox K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
      (sourceSubset K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ q P) Z L j =
    sourceSubset K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ q
      (SecondProductionBoxes.normBox K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
        P Z L j) := by
  ext i
  simp only [sourceSubset, SecondProductionBoxes.normBox, Finset.mem_filter]
  tauto

section FirstCenter

variable {ι : Type*} [Fintype ι]
variable (grid : ι → {r : ℝ // 0 < r})
variable (centers : FirstOuterCenters.Centering K S D T grid)
variable (alive : OuterIndex K S D T → Prop) (k : ι)

def firstSlice (P : Finset Idx) : Finset Idx :=
  sourceSubset K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
    (fun o e => alive o ∧ centers.assignment side₁ o e = k) P

/-- The two center inequalities are genuine consequences of membership
in the first slice, before the second common and overlap are chosen. -/
theorem firstSlice_center_bounds (P : Finset Idx) (i : Idx)
    (hi : i ∈ firstSlice K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
      side₁ grid centers alive k P) :
    (grid k).val ≤ FirstOuterCenters.extractedNorm K S D T side₁ i.1 i.2.1 ∧
      FirstOuterCenters.extractedNorm K S D T side₁ i.1 i.2.1 ≤ 2 * (grid k).val := by
  have hk := (Finset.mem_filter.mp hi).2.2
  exact ⟨by simpa only [hk] using centers.lower side₁ i.1 i.2.1,
    by simpa only [hk] using centers.upper side₁ i.1 i.2.1⟩

end FirstCenter

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondProductionRestriction

end

