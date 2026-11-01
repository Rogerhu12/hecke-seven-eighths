import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderGeneratedNodes

/-!
# The uniform node hypothesis implies the complete provider premise

Every quantifier in `AllSmallerPieces` is retained: both branches, both
marked subsets, the actual first center, the second cube bin, the full
norm box, both continuous frequencies, and every frozen triple and
smooth piece. Geometry is proved before the recursive estimate is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderUniformChildren

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open HeckeSkeleton.Moments.MOM_INV_STEP
open CanonicalNormPools FirstParentRows FirstToSecondData ActualProductionBoxes
open HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderNodes
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
variable {σ : Type u} [DecidableEq σ]
variable (T : FirstParentEnergy.Data K S (σ := σ))
variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
variable (hbase : 1 < T.columns.base) (hmask : T.mask = ∅)
variable (A Z M r ell V h tau : ℝ) (hZ : 1 < Z)
local notation "Rcap" => FirstOuterPhysicalCap.radius K S D Γ T hmask
  Z (ActualUniformProduction.boxCap A) M r ell V h tau (zero_lt_one.trans hZ)
local notation "Grid" => FirstParentCentering.grid Z A 1
variable (H : OuterIndex K S D T → {r : ℝ // 0 < r})
  (oldLabels : Finset (ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K)))))
variable (centers : FirstOuterCenters.Centering K S D T (FirstParentCentering.grid Z A 1))
variable (hprime : ∀ q ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists q, Prime p)
variable (hweights : ∀ q ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists q,
  ‖T.columns.primeWeights q p‖ ≤ 1)
variable (slotCap : ℕ) (hcap : T.columns.slots.card ≤ slotCap)
local notation "Alive" => FirstLiveCappedFreeEnergy.alive K S D Γ T H oldLabels

/-- This is the actual uniform recursive-premise adapter. The only
energy hypothesis is the preceding stage's bound on the full genuine
node class, with strictly smaller row budget and updated margins. -/
theorem all_smaller_pieces_of_uniform
    (Λ : HeckeCharacter K) (Q z c d eta Fcap lo hi Rmax eps Cih : ℝ) (markLengths : σ → ℝ)
    (t : Finset (ℕ × ℕ)) (hA : 1 ≤ A)
    (hr : r ∈ Set.Icc (0 : ℝ) A) (hell : ell ∈ Set.Icc (0 : ℝ) A)
    (hV : 0 ≤ V) (hh : h ∈ Set.Icc (0 : ℝ) 1)
    (hwidth : 2 ≤ Z ^ h) (hmesh : h ≤ eta / 16) (hstep : eta ≤ d / 16)
    (heta : 0 ≤ eta) (hd : 0 ≤ d) (hM : M ≤ Rmax)
    (hbase_eq : T.columns.base = Z) (hscale : T.scale.val = Z ^ r)
    (hcube : ∀ q ∈ T.cubes, height K Sset q ≤ Z ^ (ell + h))
    (hparent : HeckePort.Moments.CanonicalMargins (r + 3 * ell + V) M Q z c)
    (hnonterminal : d ≤ ell + V) (hRho : T.columns.puncture ≠ 0)
    (hRhoNorm : (Ideal.absNorm T.columns.puncture.radical : ℝ) ≤ Z ^ Q)
    (hlambda : T.columns.lambda = Λ)
    (hcal : ThetaCalibrationInput K Sset D T.columns.lambda G)
    (hbg : ∀ q : HeightOneSpectrum (𝓞 K), q ∉ Sset →
      UnramifiedAt K T.columns.background q)
    (hmarks : MarkConditions K S slotCap Z z lo hi T.columns.slots
      T.columns.primeLists T.columns.primeWeights markLengths)
    (hF : r + 3 * ell + V ≤ Fcap)
    (hih : UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
      (Fcap + 11 * eta) (c - 7 * eta) z lo hi eps (Rmax - d) Cih t) :
    ActualUniformProduction.AllSmallerPieces
      (K := K) (S := S) (D := D) (Γ := Γ) (T := T) (hmask := hmask)
      (A := A) (Z := Z) (M := M) (r := r) (ell := ell) (V := V) (h := h) (tau := tau)
      (hZ := hZ) (Θ := Θ) (ψ := ψ) (G := G) (hν := hν) (hG := hG) (hbase := hbase)
      (H := H) (oldLabels := oldLabels) (centers := centers)
      (hprime := hprime) (hweights := hweights) (slotCap := slotCap) (hcap := hcap)
      eps Cih t := by
  have hgeometry := ActualStepGeometry.all_children_geometry K S D Γ T Θ ψ G hν hG
    hbase hmask A Z M r ell V h tau hZ H oldLabels centers hprime hweights slotCap hcap
    Q z c d eta hA hr hell hV hh hwidth hmesh hstep hbase_eq hscale hcube hparent
    hnonterminal hRho hRhoNorm
  intro side₁ k J₁ hJ₁ s side₂ b J₂ hJ₂ hJ₂remaining j
  let U := FirstCenteredPositiveEnergy.centerScale T.scale (Grid k)
  let H₂ := FirstSecondErrorBridge.cutoff K S D T Rcap U Z tau
  have hz0 : 0 < Z := zero_lt_one.trans hZ
  have hZ2 : 2 ≤ Z := by
    have hp := Real.rpow_le_rpow_of_exponent_le hZ.le hh.2
    rw [Real.rpow_one] at hp
    exact hwidth.trans hp
  have hL : 0 ≤ ActualUniformProduction.boxCap A := by
    unfold ActualUniformProduction.boxCap
    linarith
  have hUscale : U.val = Z ^ r / (Grid k).val := by
    change T.scale.val / (Grid k).val = _
    rw [hscale]
  have hU : U.val ≤ Z ^ A := by
    rw [hUscale]
    exact (div_le_self (Real.rpow_nonneg hz0.le _)
      (FirstParentCentering.grid_one_le Z A 1 k)).trans
      (Real.rpow_le_rpow_of_exponent_le hZ.le hr.2)
  have hX : sourceScale K S T U ≤ Z ^ A := by
    rwa [sourceScale_eq K S T hbase U]
  have hXpos : 0 < sourceScale K S T U := by
    rw [sourceScale_eq K S T hbase U]
    exact U.property
  have hb : ∀ q ∈ T.cubes, height K Sset q ≤ Z ^ ActualUniformProduction.boxCap A := by
    intro q hq
    exact (hcube q hq).trans (Real.rpow_le_rpow_of_exponent_le hZ.le
      (by unfold ActualUniformProduction.boxCap; linarith [hell.2, hh.2]))
  have hfirst : 2 * T.scale.val ≤ Z ^ ActualUniformProduction.boxCap A := by
    calc
      2 * T.scale.val ≤ Z * Z ^ r := mul_le_mul hZ2 hscale.le T.scale.property.le hz0.le
      _ = Z ^ (1 + r) := by rw [Real.rpow_add hz0, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le
        (by unfold ActualUniformProduction.boxCap; linarith [hr.2])
  have hsecond : 4 * sourceScale K S T U ≤ Z ^ ActualUniformProduction.boxCap A := by
    have h4 : (4 : ℝ) ≤ Z ^ (2 : ℝ) := by rw [Real.rpow_two]; nlinarith
    calc
      4 * sourceScale K S T U ≤ Z ^ (2 : ℝ) * Z ^ A :=
        mul_le_mul h4 hX hXpos.le (Real.rpow_nonneg hz0.le _)
      _ = Z ^ (2 + A) := (Real.rpow_add hz0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le
        (by unfold ActualUniformProduction.boxCap; linarith)
  have hrow := ActualClosedBoxBudget.prescribed_radius_eq K S D Γ T Θ ψ G hν hG hbase
    Rcap U J₁ s H₂ hmask Grid centers Alive k side₁ Finset.univ b Z
    (ActualUniformProduction.boxCap A) j h hZ M r ell V tau rfl
  exact ProviderGeneratedNodes.smaller_piece_bound_of_uniform K S D Γ T Θ ψ G hν hG
    hbase Rcap U J₁ s H₂ hmask Grid centers Alive k side₁ Finset.univ b Z
    (ActualUniformProduction.boxCap A) j hprime hweights hJ₁ J₂ hJ₂ slotCap hcap
    h hZ hh.1 hwidth hb hfirst hsecond Λ M r ell V tau z c d eta Fcap lo hi Rmax eps Cih
    markLengths t hL heta hd hM hbase_eq hUscale
    (FirstSecondErrorBridge.cutoff_eq_production K S D T hbase Rcap U Z tau)
    hrow hlambda hcal hbg hRho hmarks hF side₂
    (hgeometry side₁ k J₁ hJ₁ s side₂ b J₂ hJ₂ hJ₂remaining j) hih

/-- The actual generated row geometry supplies 3d/2, uniformly over
all source boxes and both Cauchy branches. No part of that gain is lost
when converting a preceding-stage node bound to the provider premise. -/
theorem all_smaller_pieces_of_uniform_sharp
    (Λ : HeckeCharacter K) (Q z c d eta Fcap lo hi Rmax eps Cih : ℝ) (markLengths : σ → ℝ)
    (t : Finset (ℕ × ℕ)) (hA : 1 ≤ A)
    (hr : r ∈ Set.Icc (0 : ℝ) A) (hell : ell ∈ Set.Icc (0 : ℝ) A)
    (hV : 0 ≤ V) (hh : h ∈ Set.Icc (0 : ℝ) 1)
    (hwidth : 2 ≤ Z ^ h) (hmesh : h ≤ eta / 16) (hstep : eta ≤ d / 16)
    (heta : 0 ≤ eta) (hd : 0 ≤ d) (hM : M ≤ Rmax)
    (hbase_eq : T.columns.base = Z) (hscale : T.scale.val = Z ^ r)
    (hcube : ∀ q ∈ T.cubes, height K Sset q ≤ Z ^ (ell + h))
    (hparent : HeckePort.Moments.CanonicalMargins (r + 3 * ell + V) M Q z c)
    (hnonterminal : d ≤ ell + V) (hRho : T.columns.puncture ≠ 0)
    (hRhoNorm : (Ideal.absNorm T.columns.puncture.radical : ℝ) ≤ Z ^ Q)
    (hlambda : T.columns.lambda = Λ)
    (hcal : ThetaCalibrationInput K Sset D T.columns.lambda G)
    (hbg : ∀ q : HeightOneSpectrum (𝓞 K), q ∉ Sset →
      UnramifiedAt K T.columns.background q)
    (hmarks : MarkConditions K S slotCap Z z lo hi T.columns.slots
      T.columns.primeLists T.columns.primeWeights markLengths)
    (hF : r + 3 * ell + V ≤ Fcap)
    (hih : UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
      (Fcap + 11 * eta) (c - 7 * eta) z lo hi eps (Rmax - 3 * d / 2) Cih t) :
    ActualUniformProduction.AllSmallerPieces
      (K := K) (S := S) (D := D) (Γ := Γ) (T := T) (hmask := hmask)
      (A := A) (Z := Z) (M := M) (r := r) (ell := ell) (V := V) (h := h) (tau := tau)
      (hZ := hZ) (Θ := Θ) (ψ := ψ) (G := G) (hν := hν) (hG := hG) (hbase := hbase)
      (H := H) (oldLabels := oldLabels) (centers := centers)
      (hprime := hprime) (hweights := hweights) (slotCap := slotCap) (hcap := hcap)
      eps Cih t := by
  have hgeometry := ActualStepGeometry.all_children_geometry K S D Γ T Θ ψ G hν hG
    hbase hmask A Z M r ell V h tau hZ H oldLabels centers hprime hweights slotCap hcap
    Q z c d eta hA hr hell hV hh hwidth hmesh hstep hbase_eq hscale hcube hparent
    hnonterminal hRho hRhoNorm
  intro side₁ k J₁ hJ₁ s side₂ b J₂ hJ₂ hJ₂remaining j
  let U := FirstCenteredPositiveEnergy.centerScale T.scale (Grid k)
  let H₂ := FirstSecondErrorBridge.cutoff K S D T Rcap U Z tau
  have hz0 : 0 < Z := zero_lt_one.trans hZ
  have hZ2 : 2 ≤ Z := by
    have hp := Real.rpow_le_rpow_of_exponent_le hZ.le hh.2
    rw [Real.rpow_one] at hp
    exact hwidth.trans hp
  have hL : 0 ≤ ActualUniformProduction.boxCap A := by
    unfold ActualUniformProduction.boxCap
    linarith
  have hUscale : U.val = Z ^ r / (Grid k).val := by
    change T.scale.val / (Grid k).val = _
    rw [hscale]
  have hU : U.val ≤ Z ^ A := by
    rw [hUscale]
    exact (div_le_self (Real.rpow_nonneg hz0.le _)
      (FirstParentCentering.grid_one_le Z A 1 k)).trans
      (Real.rpow_le_rpow_of_exponent_le hZ.le hr.2)
  have hX : sourceScale K S T U ≤ Z ^ A := by
    rwa [sourceScale_eq K S T hbase U]
  have hXpos : 0 < sourceScale K S T U := by
    rw [sourceScale_eq K S T hbase U]
    exact U.property
  have hb : ∀ q ∈ T.cubes, height K Sset q ≤ Z ^ ActualUniformProduction.boxCap A := by
    intro q hq
    exact (hcube q hq).trans (Real.rpow_le_rpow_of_exponent_le hZ.le
      (by unfold ActualUniformProduction.boxCap; linarith [hell.2, hh.2]))
  have hfirst : 2 * T.scale.val ≤ Z ^ ActualUniformProduction.boxCap A := by
    calc
      2 * T.scale.val ≤ Z * Z ^ r := mul_le_mul hZ2 hscale.le T.scale.property.le hz0.le
      _ = Z ^ (1 + r) := by rw [Real.rpow_add hz0, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le
        (by unfold ActualUniformProduction.boxCap; linarith [hr.2])
  have hsecond : 4 * sourceScale K S T U ≤ Z ^ ActualUniformProduction.boxCap A := by
    have h4 : (4 : ℝ) ≤ Z ^ (2 : ℝ) := by rw [Real.rpow_two]; nlinarith
    calc
      4 * sourceScale K S T U ≤ Z ^ (2 : ℝ) * Z ^ A :=
        mul_le_mul h4 hX hXpos.le (Real.rpow_nonneg hz0.le _)
      _ = Z ^ (2 + A) := (Real.rpow_add hz0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le
        (by unfold ActualUniformProduction.boxCap; linarith)
  have hrow := ActualClosedBoxBudget.prescribed_radius_eq K S D Γ T Θ ψ G hν hG hbase
    Rcap U J₁ s H₂ hmask Grid centers Alive k side₁ Finset.univ b Z
    (ActualUniformProduction.boxCap A) j h hZ M r ell V tau rfl
  exact ProviderGeneratedNodes.smaller_piece_bound_of_uniform_sharp K S D Γ T Θ ψ G hν hG
    hbase Rcap U J₁ s H₂ hmask Grid centers Alive k side₁ Finset.univ b Z
    (ActualUniformProduction.boxCap A) j hprime hweights hJ₁ J₂ hJ₂ slotCap hcap
    h hZ hh.1 hwidth hb hfirst hsecond Λ M r ell V tau z c d eta Fcap lo hi Rmax eps Cih
    markLengths t hL heta hd hM hbase_eq hUscale
    (FirstSecondErrorBridge.cutoff_eq_production K S D T hbase Rcap U Z tau)
    hrow hlambda hcal hbg hRho hmarks hF side₂
    (hgeometry side₁ k J₁ hJ₁ s side₂ b J₂ hJ₂ hJ₂remaining j) hih

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderUniformChildren

end
