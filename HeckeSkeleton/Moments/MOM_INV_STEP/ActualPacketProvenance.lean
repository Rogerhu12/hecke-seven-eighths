import HeckeSkeleton.Moments.MOM_INV_STEP.ActualTwoPassChildren

/-!
# Provenance of every actual canonical child packet

Every source tuple, triple, label and row in the constructed packet comes
from an original arithmetic record. Enumerating both copies of each
original prime choice changes none of those ideals or sectors. Therefore
norm boxes and row bounds proved on the real production source transfer
to the packet without a new geometric assumption.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ActualPacketProvenance

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers FixedTripleEnergy ActualTwoPassChildren PositiveAssignedSource
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable {σ : Type*} [DecidableEq σ]
variable (C : CanonicalBlock.ColumnData K S σ)
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
local notation "transport" => ActualMaskReconstruction.sectorTransport K S D Γ
variable {N : Finset (ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K))))} {X : ℝ}
local notation "Bare" => BareSource (K := K) (S := S) (D := D) (Γ := Γ) (N := N) (X := X)

variable (hprime : ∀ j ∈ C.slots, ∀ p ∈ C.primeLists j, Prime p)
variable (hweights : ∀ j ∈ C.slots, ∀ p ∈ C.primeLists j, ‖C.primeWeights j p‖ ≤ 1)
variable (J₁ J₂ : Finset σ) (hJ₁ : J₁ ⊆ C.slots) (hJ₂ : J₂ ⊆ C.slots)
variable (T : Finset (PositiveAssignedSource.BareSource (K := K) (S := S) (D := D) (Γ := Γ) (N := N) (X := X))) (side : Bool) (slotCap : ℕ) (hcap : C.slots.card ≤ slotCap)
local notation "Q" => ActualTwoPassChildren.packet K S C D Γ hprime hweights
  J₁ J₂ hJ₁ hJ₂ T side slotCap hcap
local notation "Tuple" => SecondTuple K Sector (J₁.card + J₁.card) (J₂.card + J₂.card)

/-- Prime-choice duplication preserves the original arithmetic child,
including the exact unit sector, before any zero terms are removed. -/
theorem source_member (x : Tuple) (hx : x ∈ (Q).source) :
    ∃ B ∈ T, x.outer = B.outer ∧
      secondChild transport x = (B.outer,B.newLabel,B.newRow) := by
  change x ∈ (PositiveAssignedSource.source
    (firstLists K S C hprime J₁ hJ₁) (secondLists K S C hprime J₂ hJ₂)
      T side).image PositiveReconstruction.Source.tuple at hx
  obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hB
  exact ⟨q.1.val, q.1.property, rfl, rfl⟩

theorem live_source_member (x : Tuple)
    (hx : x ∈ originalSource (Q).source (Q).oldLists (Q).newLists (Q).keep) :
    ∃ B ∈ T, x.outer = B.outer ∧
      secondChild transport x = (B.outer,B.newLabel,B.newRow) :=
  source_member K S C D Γ hprime hweights J₁ J₂ hJ₁ hJ₂ T side slotCap hcap x
    (Finset.mem_filter.mp hx).1

theorem label_member (f : Ideal (𝓞 K)) (hf : f ∈ (Q).labels) :
    ∃ B ∈ T, f = B.newLabel := by
  change f ∈ (PositiveReconstructionPacket.liveTuples _ _ _).image
    (fun x => (secondChild transport x).2.1) at hf
  obtain ⟨x,hx,hf⟩ := Finset.mem_image.mp hf
  obtain ⟨B,hB,houter,hchild⟩ := live_source_member K S C D Γ hprime hweights
    J₁ J₂ hJ₁ hJ₂ T side slotCap hcap x hx
  exact ⟨B,hB,hf.symm.trans (congrArg (fun c : SecondChild K Sector => c.2.1) hchild)⟩

theorem row_member (y : Ideal (𝓞 K) × Sector) (hy : y ∈ (Q).rows) :
    ∃ B ∈ T, y = B.newRow := by
  change y ∈ (PositiveReconstructionPacket.liveTuples _ _ _).image
    (fun x => (secondChild transport x).2.2) at hy
  obtain ⟨x,hx,hy⟩ := Finset.mem_image.mp hy
  obtain ⟨B,hB,houter,hchild⟩ := live_source_member K S C D Γ hprime hweights
    J₁ J₂ hJ₁ hJ₂ T side slotCap hcap x hx
  exact ⟨B,hB,hy.symm.trans (congrArg (fun c : SecondChild K Sector => c.2.2) hchild)⟩

theorem triple_member (γ : OuterTriple K) (hγ : γ ∈ (Q).triples) :
    ∃ B ∈ T, γ = B.outer := by
  change γ ∈ (originalSource (Q).source (Q).oldLists (Q).newLists (Q).keep).image
    (fun x => x.outer) at hγ
  obtain ⟨x,hx,hγ⟩ := Finset.mem_image.mp hγ
  obtain ⟨B,hB,houter,hchild⟩ := live_source_member K S C D Γ hprime hweights
    J₁ J₂ hJ₁ hJ₂ T side slotCap hcap x hx
  exact ⟨B,hB,hγ.symm.trans houter⟩

/-- This is exactly the source condition of the proved fixed-triple
mass bound, now inherited from the original arithmetic records. -/
theorem source_norm_box (Xq Xt Xr : ℝ)
    (hsource : ∀ B ∈ T,
      (Ideal.absNorm B.outer.q0 : ℝ) ≤ Xq ∧
      (Ideal.absNorm B.outer.quotient : ℝ) ≤ Xt ∧
      (Ideal.absNorm B.outer.residual : ℝ) ≤ Xr)
    (x : Tuple) (hx : x ∈ originalSource (Q).source (Q).oldLists (Q).newLists (Q).keep) :
    (Ideal.absNorm x.outer.q0 : ℝ) ≤ Xq ∧
      (Ideal.absNorm x.outer.quotient : ℝ) ≤ Xt ∧
      (Ideal.absNorm x.outer.residual : ℝ) ≤ Xr := by
  obtain ⟨B,hB,houter,hchild⟩ := live_source_member K S C D Γ hprime hweights
    J₁ J₂ hJ₁ hJ₂ T side slotCap hcap x hx
  rw [houter]
  exact hsource B hB

theorem labels_norm_bound (V : ℝ)
    (hsource : ∀ B ∈ T, (Ideal.absNorm B.newLabel : ℝ) ≤ V)
    (f : Ideal (𝓞 K)) (hf : f ∈ (Q).labels) : (Ideal.absNorm f : ℝ) ≤ V := by
  obtain ⟨B,hB,rfl⟩ := label_member K S C D Γ hprime hweights
    J₁ J₂ hJ₁ hJ₂ T side slotCap hcap f hf
  exact hsource B hB

theorem rows_norm_bound (M : ℝ)
    (hsource : ∀ B ∈ T, (Ideal.absNorm B.newRow.1 : ℝ) ≤ M)
    (y : Ideal (𝓞 K) × Sector) (hy : y ∈ (Q).rows) : (Ideal.absNorm y.1 : ℝ) ≤ M := by
  obtain ⟨B,hB,rfl⟩ := row_member K S C D Γ hprime hweights
    J₁ J₂ hJ₁ hJ₂ T side slotCap hcap y hy
  exact hsource B hB

end HeckeSkeleton.Moments.MOM_INV_STEP.ActualPacketProvenance

end

