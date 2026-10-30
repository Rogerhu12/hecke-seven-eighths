import HeckeGeneral.Analysis.IdealThetaNormalization
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Algebra.Group.AddChar
import HeckeGeneral.Characters.FiniteCircleFourier
import HeckeGeneral.Arithmetic.IdealLatticeQuotient
import HeckeGeneral.Characters.ConductorGauss

/-!
Finite periodic weights on actual lattices. The quotient is the genuine
additive quotient of the larger lattice by the smaller lattice; it is not
an independently supplied finite parameter set. All infinite sums converge
by Schwartz decay on the actual lattices.
-/

noncomputable section

open Classical MeasureTheory Module NumberField
open scoped FourierTransform Real nonZeroDivisors

namespace HeckeGeneral.Analysis

open HeckeGeneral.Arithmetic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Schwartz translates are absolutely summable on any real inner-product lattice. -/
theorem summable_norm_schwartz_lattice (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (f : SchwartzMap E ℂ) (v : E) :
    Summable fun l : L => ‖f (v + l)‖ := by
  let A : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃ₗᵢ[ℝ] E :=
    (stdOrthonormalBasis ℝ E).repr.symm
  let L₀ := ZLattice.comap ℝ L A.toContinuousLinearEquiv.toLinearMap
  let f₀ : SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv f
  have h := SchwartzMap.PoissonSummation.Standard.summable_norm_translate L₀ f₀ (A.symm v)
  let he := (ZLattice.comap_equiv ℝ L A.toLinearEquiv).toEquiv
  have h' := he.summable_iff.mpr h
  refine h'.congr (fun l => ?_)
  change ‖f (A (A.symm v + A.symm (l : E)))‖ = ‖f (v + (l : E))‖
  rw [A.map_add, A.apply_symm_apply, A.apply_symm_apply]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The polar of a full lattice is itself a full lattice: an actual basis proof. -/
theorem dualLattice_eq_span_dualBasis (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    dualLattice L = Submodule.span ℤ (Set.range
      (LinearMap.BilinForm.dualBasis (innerₗ E) innerBilin_nondegenerate
        ((Free.chooseBasis ℤ L).ofZLatticeBasis ℝ))) := by
  classical
  change LinearMap.BilinForm.dualSubmodule (innerₗ E) L = _
  conv_lhs => rw [← (Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ]
  exact LinearMap.BilinForm.dualSubmodule_span_of_basis _ innerBilin_nondegenerate _

instance discreteTopology_dualLattice (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] : DiscreteTopology (dualLattice L) := by
  rw [dualLattice_eq_span_dualBasis]
  infer_instance

instance isZLattice_dualLattice (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] : IsZLattice ℝ (dualLattice L) := by
  constructor
  rw [dualLattice_eq_span_dualBasis]
  exact IsZLattice.span_top

/-- The subgroup of `L` consisting of points of `J`. -/
abbrev latticeSubgroup (L J : Submodule ℤ E) : AddSubgroup L :=
  J.toAddSubgroup.addSubgroupOf L.toAddSubgroup

/-- The actual quotient of the larger lattice by the smaller one. -/
abbrev LatticeQuotient (L J : Submodule ℤ E) := L ⧸ latticeSubgroup L J

def latticeQuotientMap (L J : Submodule ℤ E) : L →+ LatticeQuotient L J :=
  QuotientAddGroup.mk' (latticeSubgroup L J)

/-- A chosen lift of a quotient class. No equality depends on this choice. -/
def latticeRepresentative (L J : Submodule ℤ E) (q : LatticeQuotient L J) : L :=
  Quotient.out q

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem latticeQuotientMap_representative (L J : Submodule ℤ E)
    (q : LatticeQuotient L J) :
    latticeQuotientMap L J (latticeRepresentative L J q) = q := Quotient.out_eq' q

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem quotientMap_representative_add (L J : Submodule ℤ E) (hJL : J ≤ L)
    (q : LatticeQuotient L J) (j : J) :
    latticeQuotientMap L J (latticeRepresentative L J q + ⟨j, hJL j.property⟩) = q := by
  rw [map_add]
  have hj : latticeQuotientMap L J (⟨j, hJL j.property⟩ : L) = 0 := by
    change (⟨j, hJL j.property⟩ : L) ∈
      (QuotientAddGroup.mk' (latticeSubgroup L J)).ker
    rw [QuotientAddGroup.ker_mk']
    exact j.property
  rw [hj, add_zero, latticeQuotientMap_representative]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem representative_difference_mem (L J : Submodule ℤ E) (l : L) :
    (l : E) - latticeRepresentative L J (latticeQuotientMap L J l) ∈ J := by
  change l - latticeRepresentative L J (latticeQuotientMap L J l) ∈ latticeSubgroup L J
  apply QuotientAddGroup.eq_iff_sub_mem.mp
  exact (latticeQuotientMap_representative L J (latticeQuotientMap L J l)).symm

/-- Coset decomposition, retaining the actual smaller-lattice index. -/
def latticeCosetEquiv (L J : Submodule ℤ E) (hJL : J ≤ L) :
    LatticeQuotient L J × J ≃ L where
  toFun qj := latticeRepresentative L J qj.1 + ⟨qj.2, hJL qj.2.property⟩
  invFun l := (latticeQuotientMap L J l,
    ⟨(l : E) - latticeRepresentative L J (latticeQuotientMap L J l),
      representative_difference_mem L J l⟩)
  left_inv qj := by
    obtain ⟨q, j⟩ := qj
    apply Prod.ext
    · exact quotientMap_representative_add L J hJL q j
    · apply Subtype.ext
      dsimp only
      rw [quotientMap_representative_add]
      change ((latticeRepresentative L J q : E) + (j : E)) -
        latticeRepresentative L J q = j
      abel
  right_inv l := by
    apply Subtype.ext
    change (latticeRepresentative L J (latticeQuotientMap L J l) : E) +
      ((l : E) - latticeRepresentative L J (latticeQuotientMap L J l)) = l
    abel

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem latticeCosetEquiv_coe (L J : Submodule ℤ E) (hJL : J ≤ L)
    (q : LatticeQuotient L J) (j : J) :
    (latticeCosetEquiv L J hJL (q, j) : E) =
      (latticeRepresentative L J q : E) + j := rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem latticeQuotientMap_coset (L J : Submodule ℤ E) (hJL : J ≤ L)
    (q : LatticeQuotient L J) (j : J) :
    latticeQuotientMap L J (latticeCosetEquiv L J hJL (q, j)) = q := by
  exact quotientMap_representative_add L J hJL q j

omit [MeasurableSpace E] [BorelSpace E] in
/-- A finite periodic multiplier preserves genuine absolute lattice summability. -/
theorem summable_norm_weighted_lattice (L J : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] [Fintype (LatticeQuotient L J)]
    (w : LatticeQuotient L J → ℂ) (f : SchwartzMap E ℂ) (v : E) :
    Summable fun l : L => ‖w (latticeQuotientMap L J l) * f (v + l)‖ := by
  let B := ∑ q : LatticeQuotient L J, ‖w q‖
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => ?_)
    ((summable_norm_schwartz_lattice L f v).mul_left B)
  rw [norm_mul]
  gcongr
  exact Finset.single_le_sum (fun q _ => norm_nonneg (w q)) (Finset.mem_univ _)

omit [MeasurableSpace E] [BorelSpace E] in
/-- Decompose the actual weighted lattice sum into its actual quotient cosets. -/
theorem weighted_lattice_coset_sum (L J : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] [Fintype (LatticeQuotient L J)]
    (hJL : J ≤ L) (w : LatticeQuotient L J → ℂ) (f : SchwartzMap E ℂ) (v : E) :
    ∑' l : L, w (latticeQuotientMap L J l) * f (v + l) =
      ∑ q : LatticeQuotient L J, w q *
        ∑' j : J, f (v + (latticeRepresentative L J q : E) + j) := by
  let e := latticeCosetEquiv L J hJL
  have hs := (summable_norm_weighted_lattice L J w f v).of_norm
  have hs' := hs.comp_injective e.injective
  dsimp only [Function.comp_def] at hs'
  rw [← e.tsum_eq, hs'.tsum_prod, tsum_fintype]
  apply Finset.sum_congr rfl
  intro q _
  rw [← tsum_mul_left]
  apply tsum_congr
  intro j
  simp [e, add_assoc]

/-- The actual positive Fourier phase from the real inner product. -/
def latticePhase (v m : E) : ℂ := (Real.fourierChar (inner ℝ v m) : ℂ)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem norm_latticePhase (v m : E) : ‖latticePhase v m‖ = 1 := Circle.norm_coe _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem latticePhase_eq_exp (v m : E) :
    latticePhase v m = Complex.exp (2 * Real.pi * Complex.I * inner ℝ v m) := by
  rw [latticePhase, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem latticePhase_add (u v m : E) :
    latticePhase (u + v) m = latticePhase u m * latticePhase v m := by
  simp only [latticePhase, inner_add_left, AddChar.map_add_eq_mul, Circle.coe_mul]

private theorem fourierChar_intCast (n : ℤ) : Real.fourierChar (n : ℝ) = 1 := by
  apply Circle.coe_injective
  rw [Real.fourierChar_apply, Circle.coe_one]
  have h : (↑(2 * Real.pi * (n : ℝ)) : ℂ) * Complex.I =
      (n : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
  rw [h]
  exact Complex.exp_int_mul_two_pi_mul_I n

/-- The inner-product phase as an actual additive character of the larger lattice. -/
def latticePhaseCharacter (L : Submodule ℤ E) (m : E) : AddChar L Circle :=
  Real.fourierChar.compAddMonoidHom
    { toFun := fun l => inner ℝ (l : E) m
      map_zero' := by simp
      map_add' := by intro x y; simp [inner_add_left] }

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem latticePhaseCharacter_trivial_on (L J : Submodule ℤ E) (m : dualLattice J)
    (x : L) (hx : x ∈ latticeSubgroup L J) : latticePhaseCharacter L m x = 1 := by
  obtain ⟨n, hn⟩ := Submodule.mem_one.mp (m.property (x : E) hx)
  change Real.fourierChar (inner ℝ (x : E) (m : E)) = 1
  rw [real_inner_comm]
  change (n : ℝ) = inner ℝ (m : E) (x : E) at hn
  rw [← hn]
  exact fourierChar_intCast n

/-- The frequency character on the actual finite quotient. Integrality on the
smaller lattice is proved from polar-lattice membership. -/
def latticeFrequencyCharacter (L J : Submodule ℤ E) (m : dualLattice J) :
    AddChar (LatticeQuotient L J) Circle :=
  AddChar.toAddMonoidHomEquiv.symm
    (QuotientAddGroup.lift (latticeSubgroup L J)
      (latticePhaseCharacter L m).toAddMonoidHom (by
        intro x hx
        change latticePhaseCharacter L m x = 1
        exact latticePhaseCharacter_trivial_on L J m x hx))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem latticeFrequencyCharacter_mk (L J : Submodule ℤ E)
    (m : dualLattice J) (x : L) :
    latticeFrequencyCharacter L J m (latticeQuotientMap L J x) =
      Real.fourierChar (inner ℝ (x : E) (m : E)) := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem latticeFrequencyCharacter_representative (L J : Submodule ℤ E)
    (m : dualLattice J) (q : LatticeQuotient L J) :
    (latticeFrequencyCharacter L J m q : ℂ) =
      latticePhase (latticeRepresentative L J q : E) m := by
  conv_lhs => rw [← latticeQuotientMap_representative L J q, latticeFrequencyCharacter_mk]
  rfl

/-- The finite coefficient supplied by the actual frequency character. -/
def latticeMaskCoefficient (L J : Submodule ℤ E) [Fintype (LatticeQuotient L J)]
    (w : LatticeQuotient L J → ℂ) (m : dualLattice J) : ℂ :=
  ∑ q, w q * (latticeFrequencyCharacter L J m q : ℂ)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem latticeMaskCoefficient_representatives (L J : Submodule ℤ E)
    [Fintype (LatticeQuotient L J)] (w : LatticeQuotient L J → ℂ)
    (m : dualLattice J) :
    latticeMaskCoefficient L J w m = ∑ q,
      w q * latticePhase (latticeRepresentative L J q : E) m := by
  simp only [latticeMaskCoefficient, latticeFrequencyCharacter_representative]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- This is the existing finite Fourier coefficient, at the inverse frequency
character; the positive phase in Poisson summation determines the inverse. -/
theorem latticeMaskCoefficient_eq_finiteFourierCoeff (L J : Submodule ℤ E)
    [Fintype (LatticeQuotient L J)] (w : LatticeQuotient L J → ℂ)
    (m : dualLattice J) :
    latticeMaskCoefficient L J w m = HeckeGeneral.Characters.finiteFourierCoeff
      (Multiplicative (LatticeQuotient L J)) (fun q => w q.toAdd)
      ((latticeFrequencyCharacter L J m).toMonoidHom⁻¹) := by
  simp only [latticeMaskCoefficient, HeckeGeneral.Characters.finiteFourierCoeff,
    MonoidHom.inv_apply, Circle.coe_inv, inv_inv, AddChar.toMonoidHom_apply]
  exact (Multiplicative.toAdd : Multiplicative (LatticeQuotient L J) ≃
    LatticeQuotient L J).sum_comp (fun q => w q * (latticeFrequencyCharacter L J m q : ℂ))
    |>.symm

/-- The frequency-side Schwartz lattice sum converges absolutely. -/
theorem summable_norm_fourier_lattice (J : Submodule ℤ E)
    [DiscreteTopology J] [IsZLattice ℝ J] (f : SchwartzMap E ℂ) :
    Summable fun m : dualLattice J => ‖𝓕 ⇑f m‖ := by
  simpa [SchwartzMap.fourier_coe] using summable_norm_schwartz_lattice
    (dualLattice J) (𝓕 f) 0

theorem summable_fourier_lattice_phase (J : Submodule ℤ E)
    [DiscreteTopology J] [IsZLattice ℝ J] (f : SchwartzMap E ℂ) (v : E) :
    Summable fun m : dualLattice J => (𝓕 ⇑f m) * latticePhase v m := by
  apply Summable.of_norm
  simpa only [norm_mul, norm_latticePhase, mul_one] using summable_norm_fourier_lattice J f

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_latticeMaskCoefficient_le (L J : Submodule ℤ E)
    [Fintype (LatticeQuotient L J)] (w : LatticeQuotient L J → ℂ)
    (m : dualLattice J) : ‖latticeMaskCoefficient L J w m‖ ≤ ∑ q, ‖w q‖ := by
  calc
    ‖latticeMaskCoefficient L J w m‖ ≤
        ∑ q, ‖w q * (latticeFrequencyCharacter L J m q : ℂ)‖ :=
      norm_sum_le _ _
    _ = _ := by simp only [norm_mul, Circle.norm_coe, mul_one]

/-- The masked frequency sum is also genuinely absolutely convergent. -/
theorem summable_norm_fourier_lattice_mask (L J : Submodule ℤ E)
    [DiscreteTopology J] [IsZLattice ℝ J] [Fintype (LatticeQuotient L J)]
    (w : LatticeQuotient L J → ℂ) (f : SchwartzMap E ℂ) (v : E) :
    Summable fun m : dualLattice J =>
      ‖(𝓕 ⇑f m) * latticePhase v m * latticeMaskCoefficient L J w m‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    ((summable_norm_fourier_lattice J f).mul_right (∑ q, ‖w q‖))
  simp only [norm_mul, norm_latticePhase, mul_one]
  exact mul_le_mul_of_nonneg_left (norm_latticeMaskCoefficient_le L J w m) (norm_nonneg _)

/-- Actual Poisson summation with any finite periodic weight. The quotient
character coefficient is evaluated on `J`'s polar and the prefactor remains
the genuine `1 / covolume J`. -/
theorem weighted_lattice_poisson (L J : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] [DiscreteTopology J] [IsZLattice ℝ J]
    [Fintype (LatticeQuotient L J)] (hJL : J ≤ L)
    (w : LatticeQuotient L J → ℂ) (f : SchwartzMap E ℂ) (v : E) :
    ∑' l : L, w (latticeQuotientMap L J l) * f (v + l) =
      (1 / ZLattice.covolume J : ℂ) * ∑' m : dualLattice J,
        (𝓕 ⇑f m) * latticePhase v m * latticeMaskCoefficient L J w m := by
  have hps (q : LatticeQuotient L J) :
      (∑' j : J, f (v + (latticeRepresentative L J q : E) + j)) =
        (1 / ZLattice.covolume J : ℂ) * ∑' m : dualLattice J,
          (𝓕 ⇑f m) * latticePhase (v + latticeRepresentative L J q) m := by
    simpa only [latticePhase_eq_exp] using poissonSummation_innerProductSpace
      J f (v + latticeRepresentative L J q)
  calc
    _ = ∑ q : LatticeQuotient L J, w q *
        ((1 / ZLattice.covolume J : ℂ) * ∑' m : dualLattice J,
          (𝓕 ⇑f m) * latticePhase (v + latticeRepresentative L J q) m) := by
      rw [weighted_lattice_coset_sum L J hJL]
      simp_rw [hps]
    _ = (1 / ZLattice.covolume J : ℂ) * ∑ q : LatticeQuotient L J,
        ∑' m : dualLattice J, w q *
          ((𝓕 ⇑f m) * latticePhase (v + latticeRepresentative L J q) m) := by
      simp_rw [tsum_mul_left]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = (1 / ZLattice.covolume J : ℂ) * ∑' m : dualLattice J,
        ∑ q : LatticeQuotient L J, w q *
          ((𝓕 ⇑f m) * latticePhase (v + latticeRepresentative L J q) m) := by
      congr 1
      exact (Summable.tsum_finsetSum (s := Finset.univ) (fun q _ =>
        (summable_fourier_lattice_phase J f (v + latticeRepresentative L J q)).mul_left
          (w q))).symm
    _ = _ := by
      congr 1
      apply tsum_congr
      intro m
      rw [latticeMaskCoefficient_representatives, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      rw [latticePhase_add]
      ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem latticeFrequencyCharacter_zero (L J : Submodule ℤ E)
    (q : LatticeQuotient L J) : latticeFrequencyCharacter L J 0 q = 1 := by
  induction q using Quotient.inductionOn' with
  | h l =>
    change latticeFrequencyCharacter L J 0 (latticeQuotientMap L J l) = 1
    rw [latticeFrequencyCharacter_mk]
    simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem latticeMaskCoefficient_zero (L J : Submodule ℤ E)
    [Fintype (LatticeQuotient L J)] (w : LatticeQuotient L J → ℂ) :
    latticeMaskCoefficient L J w 0 = ∑ q, w q := by
  simp only [latticeMaskCoefficient, latticeFrequencyCharacter_zero, Circle.coe_one, mul_one]

/-- Both zero contributions are retained explicitly when passing to the two
nonzero sums. Neither zero term is replaced by an orbital profile at zero. -/
theorem weighted_lattice_poisson_nonzero (L J : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] [DiscreteTopology J] [IsZLattice ℝ J]
    [Fintype (LatticeQuotient L J)] (hJL : J ≤ L)
    (w : LatticeQuotient L J → ℂ) (f : SchwartzMap E ℂ) (v : E) :
    (∑' l : L, if l = 0 then 0 else w (latticeQuotientMap L J l) * f (v + l)) =
      (1 / ZLattice.covolume J : ℂ) *
        (∑' m : dualLattice J, if m = 0 then 0 else
          (𝓕 ⇑f m) * latticePhase v m * latticeMaskCoefficient L J w m) +
        (1 / ZLattice.covolume J : ℂ) * (𝓕 ⇑f 0) * (∑ q, w q) - w 0 * f v := by
  have hl := (summable_norm_weighted_lattice L J w f v).of_norm
  have hm := (summable_norm_fourier_lattice_mask L J w f v).of_norm
  have h := weighted_lattice_poisson L J hJL w f v
  rw [hl.tsum_eq_add_tsum_ite 0, hm.tsum_eq_add_tsum_ite 0] at h
  simp only [map_zero, latticePhase, inner_zero_right, AddChar.map_zero_eq_one,
    Circle.coe_one, mul_one, latticeMaskCoefficient_zero, Submodule.coe_zero, add_zero] at h
  simp only [latticePhase]
  linear_combination h

section IntegralIdeal

variable (K : Type*) [Field K] [NumberField K]

local instance residueFintype (c : (Ideal (𝓞 K))⁰) : Fintype (𝓞 K ⧸ c.val) :=
  Fintype.ofFinite _

local instance traceResidueSourceFintype (c : (Ideal (𝓞 K))⁰) :
    Fintype (traceIdealLattice K 1 ⧸
      (traceIdealLattice K (integralIdealUnit K c)).toAddSubgroup.addSubgroupOf
        (traceIdealLattice K 1).toAddSubgroup) := Fintype.ofFinite _

local instance traceQuotientFintype (c : (Ideal (𝓞 K))⁰) :
    Fintype (LatticeQuotient (traceIdealLattice K 1)
      (traceIdealLattice K (integralIdealUnit K c))) := by
  change Fintype (traceIdealLattice K 1 ⧸
    (traceIdealLattice K (integralIdealUnit K c)).toAddSubgroup.addSubgroupOf
      (traceIdealLattice K 1).toAddSubgroup)
  infer_instance

/-- An actual integral-residue weight pulled back along the arithmetic lattice quotient. -/
def integralLatticeWeight (c : (Ideal (𝓞 K))⁰) (w : (𝓞 K ⧸ c.val) → ℂ) :
    LatticeQuotient (traceIdealLattice K 1)
      (traceIdealLattice K (integralIdealUnit K c)) → ℂ :=
  fun q => w (traceLatticeResidueEquiv K c q)

/-- The trace phase, now on the actual residue ring. Its definition is forced by
the ideal lattice and its polar, not by a chosen primitive finite pairing. -/
def integralLatticeAddCharacter (c : (Ideal (𝓞 K))⁰)
    (m : dualLattice (traceIdealLattice K (integralIdealUnit K c))) :
    AddChar (𝓞 K ⧸ c.val) ℂ :=
  Circle.coeHom.compAddChar
    ((latticeFrequencyCharacter (traceIdealLattice K 1)
      (traceIdealLattice K (integralIdealUnit K c)) m).compAddMonoidHom
        (traceLatticeResidueEquiv K c).symm.toAddMonoidHom)

theorem integralLatticeAddCharacter_mk (c : (Ideal (𝓞 K))⁰)
    (m : dualLattice (traceIdealLattice K (integralIdealUnit K c))) (a : 𝓞 K) :
    integralLatticeAddCharacter K c m (Ideal.Quotient.mk c.val a) =
      latticePhase (traceEmbedding K (a : K)) m := by
  have he : (traceLatticeResidueEquiv K c).symm (Ideal.Quotient.mk c.val a) =
      latticeQuotientMap (traceIdealLattice K 1)
        (traceIdealLattice K (integralIdealUnit K c)) (traceIntegerLatticeEquiv K a) := by
    apply (traceLatticeResidueEquiv K c).injective
    rw [AddEquiv.apply_symm_apply]
    exact (traceLatticeResidueEquiv_mk_integer K c a).symm
  change (latticeFrequencyCharacter _ _ m
    ((traceLatticeResidueEquiv K c).symm (Ideal.Quotient.mk c.val a)) : ℂ) = _
  rw [he, latticeFrequencyCharacter_mk, traceIntegerLatticeEquiv_apply]
  rfl

theorem integralLatticeAddCharacter_norm (c : (Ideal (𝓞 K))⁰)
    (m : dualLattice (traceIdealLattice K (integralIdealUnit K c)))
    (a : 𝓞 K ⧸ c.val) : ‖integralLatticeAddCharacter K c m a‖ = 1 := Circle.norm_coe _

/-- For an embedded trace-dual frequency the phase is the positive rational
trace exponential. This fixes the sign when connecting finite local characters. -/
theorem integralLatticeAddCharacter_trace (c : (Ideal (𝓞 K))⁰)
    (m : dualLattice (traceIdealLattice K (integralIdealUnit K c))) (ξ : K)
    (hm : (m : mixedEmbedding.euclidean.mixedSpace K) =
      traceConjugation K (traceEmbedding K ξ)) (a : 𝓞 K) :
    integralLatticeAddCharacter K c m (Ideal.Quotient.mk c.val a) =
      Complex.exp (2 * Real.pi * Complex.I *
        (Algebra.trace ℚ K ((a : K) * ξ) : ℝ)) := by
  rw [integralLatticeAddCharacter_mk, latticePhase_eq_exp, hm,
    inner_traceEmbedding_traceConjugation]

theorem integralLatticeMaskCoefficient (c : (Ideal (𝓞 K))⁰)
    (w : (𝓞 K ⧸ c.val) → ℂ)
    (m : dualLattice (traceIdealLattice K (integralIdealUnit K c))) :
    latticeMaskCoefficient (traceIdealLattice K 1)
      (traceIdealLattice K (integralIdealUnit K c)) (integralLatticeWeight K c w) m =
        ∑ a : 𝓞 K ⧸ c.val, w a * integralLatticeAddCharacter K c m a := by
  rw [latticeMaskCoefficient]
  have h := (traceLatticeResidueEquiv K c).toEquiv.sum_comp
    (fun a => w a * integralLatticeAddCharacter K c m a)
  rw [← h]
  apply Finset.sum_congr rfl
  intro q _
  change w (traceLatticeResidueEquiv K c q) * (latticeFrequencyCharacter _ _ m q : ℂ) =
    w (traceLatticeResidueEquiv K c q) *
      (latticeFrequencyCharacter _ _ m ((traceLatticeResidueEquiv K c).symm
        (traceLatticeResidueEquiv K c q)) : ℂ)
  rw [AddEquiv.symm_apply_apply]

/-- Actual trace-lattice Poisson with a finite integral-residue weight and
explicit norm/discriminant normalization. -/
theorem integral_weighted_lattice_poisson (c : (Ideal (𝓞 K))⁰)
    (w : (𝓞 K ⧸ c.val) → ℂ)
    (f : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (v : mixedEmbedding.euclidean.mixedSpace K) :
    ∑' l : traceIdealLattice K 1,
      integralLatticeWeight K c w (latticeQuotientMap _ _ l) * f (v + l) =
      (1 / ((Ideal.absNorm c.val : ℝ) * Real.sqrt |discr K|) : ℂ) *
        ∑' m : dualLattice (traceIdealLattice K (integralIdealUnit K c)),
          (𝓕 ⇑f m) * latticePhase v m *
            (∑ a : 𝓞 K ⧸ c.val, w a * integralLatticeAddCharacter K c m a) := by
  simpa only [covolume_trace_integralIdealLattice, integralLatticeMaskCoefficient,
    Complex.ofReal_mul]
    using weighted_lattice_poisson (traceIdealLattice K 1)
      (traceIdealLattice K (integralIdealUnit K c)) (trace_integralIdealLattice_le K c)
      (integralLatticeWeight K c w) f v

/-- The actual finite-conductor multiplicative character is a valid mask;
its coefficient is the actual Gauss sum for the trace phase. No primitive
additive-character or Gauss nonvanishing assumption is inserted. -/
theorem conductor_weighted_lattice_poisson (χ : HeckeGeneral.Characters.HeckeCharacter K)
    (f : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (v : mixedEmbedding.euclidean.mixedSpace K) :
    ∑' l : traceIdealLattice K 1,
      integralLatticeWeight K (HeckeGeneral.Characters.finiteConductor K χ)
        (HeckeGeneral.Characters.conductorMulCharacter K χ) (latticeQuotientMap _ _ l) *
          f (v + l) =
      (1 / ((Ideal.absNorm (HeckeGeneral.Characters.finiteConductor K χ).val : ℝ) *
        Real.sqrt |discr K|) : ℂ) *
      ∑' m : dualLattice (traceIdealLattice K
        (integralIdealUnit K (HeckeGeneral.Characters.finiteConductor K χ))),
          (𝓕 ⇑f m) * latticePhase v m *
            gaussSum (HeckeGeneral.Characters.conductorMulCharacter K χ)
              (integralLatticeAddCharacter K (HeckeGeneral.Characters.finiteConductor K χ) m) := by
  simpa only [gaussSum] using integral_weighted_lattice_poisson K
    (HeckeGeneral.Characters.finiteConductor K χ)
      (HeckeGeneral.Characters.conductorMulCharacter K χ) f v

end IntegralIdeal

end HeckeGeneral.Analysis
