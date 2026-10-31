import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SUnitKummerPrimeSelection.Conclusion
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Tactic.NormNum

/-!
UNCOMPILED isolated candidate, 2026-10-11. No Lean/Lake was run.

Actual finite prime detectors for powers of actual S-units. The detector is
obtained by specializing the pinned CFT theorem to the bottom intermediate
field, whose Galois group is trivial. No local-global power implication or
injectivity hypothesis is supplied. This module deliberately does not claim
that its disjoint detector T is already the same set as its unit support S.

Upstream pin: n-yamaguchi-0729/ClassFieldTheory,
2eb22d6485af45f29c5219de6c49f196a61c4f49.
Main consumer: SUnitKummerPrimeSelection/Conclusion.lean:37.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Arithmetic.AllowedGeneratorConstruction

open NumberField IsDedekindDomain KummerTheory
open GlobalClassFieldTheory.ClassFieldAxiom
open scoped Classical IsMulCommutative

variable (K : Type) [Field K] [NumberField K]

/-- A finite set of actual finite places detects global prime-power classes
of actual S-units. Both S and T are constructed from the supplied finite S0.
The local conditions use the field-unit groups, including valuation data. -/
theorem exists_finite_primePower_sUnit_detector
    (S0 : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v) :
    ∃ S T : Finset (HeightOneSpectrum (𝓞 K)),
      S0 ⊆ S ∧ Disjoint S T ∧
      ∀ x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
        (∀ q ∈ T, ∃ z : (q.adicCompletion K)ˣ,
          z ^ (n : ℕ) =
            Units.map (algebraMap K (q.adicCompletion K)).toMonoidHom (x : Kˣ)) ↔
        ∃ y : (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
          y ^ (n : ℕ) = x := by
  classical
  let Omega := SeparableClosure K
  let E : IntermediateField K Omega := ⊥
  letI : Subsingleton Gal(E/K) := by
    refine ⟨fun f g => ?_⟩
    ext x
    obtain ⟨t, ht⟩ := (IntermediateField.botEquiv K Omega).symm.surjective x
    rw [← ht, IntermediateField.botEquiv_symm]
    rw [f.commutes, g.commutes]
  letI : Unique Gal(E/K) :=
    { default := 1
      uniq := fun _ => Subsingleton.elim _ _ }
  letI : IsMulCommutative Gal(E/K) := ⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩
  let eG : Gal(E/K) ≃* (Fin 0 → Multiplicative (ZMod (n : ℕ))) :=
    MulEquiv.ofUnique
  let S := enlargeByFiniteKummerRadicalSupport (K := K) (L := E) n hmu S0
  let T := sUnitKummerPrimeSet (K := K) (Omega := Omega) E n hmu
    p v hp hv hn 0 eG S0
  have hkernel :
      sUnitLocalPowerKernel (K := K) n S T =
        (sUnitFiniteKummerRadical (K := K) (L := E) n S).comap
          (SUnitGroup (K := K) S).subtype :=
    sUnitLocalPowerKernel_sUnitKummerPrimeSet_eq_comap_sUnitFiniteKummerRadical
      (K := K) (Omega := Omega) E n hmu p v hp hv hn 0 eG S0
  refine ⟨S, T,
    subset_enlargeByFiniteKummerRadicalSupport (K := K) (L := E) n hmu S0,
    (sUnitKummerPrimeSet_disjoint_enlargeByFiniteKummerRadicalSupport
      (K := K) (Omega := Omega) E n hmu p v hp hv hn 0 eG S0).symm, ?_⟩
  intro x
  constructor
  · intro hx
    have hxkernel : x ∈ sUnitLocalPowerKernel (K := K) n S T := by
      apply (mem_sUnitLocalPowerKernel_iff (K := K) n S T x).mpr
      intro q
      obtain ⟨z, hz⟩ := hx q.val q.property
      exact MonoidHom.mem_range.mpr ⟨z, by simpa only [powMonoidHom_apply] using hz⟩
    rw [hkernel] at hxkernel
    have hxrad : (x : Kˣ) ∈ sUnitFiniteKummerRadical (K := K) (L := E) n S :=
      hxkernel
    obtain ⟨_hxS, beta, hbeta⟩ :=
      (mem_sUnitFiniteKummerRadical_iff (K := K) (L := E) n S (x : Kˣ)).mp hxrad
    let y : Kˣ := Units.map (IntermediateField.botEquiv K Omega).toMonoidHom beta
    have hy : y ^ (n : ℕ) = (x : Kˣ) := by
      apply Units.ext
      change (IntermediateField.botEquiv K Omega) (beta : E) ^ (n : ℕ) = ((x : Kˣ) : K)
      rw [← map_pow]
      have hval : (beta : E) ^ (n : ℕ) =
          algebraMap K E ((x : Kˣ) : K) :=
        congrArg (fun u : Eˣ => (u : E)) hbeta
      exact (congrArg (IntermediateField.botEquiv K Omega) hval).trans
        (IntermediateField.botEquiv_def ((x : Kˣ) : K))
    have hyS : y ∈ SUnitGroup (K := K) S :=
      mem_sUnitGroup_of_pow_mem (K := K) S n y (by rw [hy]; exact x.property)
    refine ⟨⟨y, hyS⟩, ?_⟩
    exact Subtype.ext hy
  · rintro ⟨y, hy⟩ q hq
    refine ⟨Units.map (algebraMap K (q.adicCompletion K)).toMonoidHom (y : Kˣ), ?_⟩
    rw [← map_pow]
    exact congrArg (Units.map (algebraMap K (q.adicCompletion K)).toMonoidHom)
      (congrArg (fun z : (S : Set (HeightOneSpectrum (𝓞 K))).unit K => (z : Kˣ)) hy)

/-- The quadratic detector is available from the actual primitive sixth
root, without an additional roots-of-unity existence hypothesis. -/
theorem exists_finite_quadratic_sUnit_detector
    (S0 : Finset (HeightOneSpectrum (𝓞 K))) (zeta : K)
    (hzeta : IsPrimitiveRoot zeta 6) :
    ∃ S T : Finset (HeightOneSpectrum (𝓞 K)),
      S0 ⊆ S ∧ Disjoint S T ∧
      ∀ x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
        (∀ q ∈ T, ∃ z : (q.adicCompletion K)ˣ,
          z ^ 2 = Units.map (algebraMap K (q.adicCompletion K)).toMonoidHom (x : Kˣ)) ↔
        ∃ y : (S : Set (HeightOneSpectrum (𝓞 K))).unit K, y ^ 2 = x := by
  have hroot : IsPrimitiveRoot (zeta ^ 3) 2 :=
    IsPrimitiveRoot.pow (by decide) hzeta (by decide)
  have hmu : (primitiveRoots 2 K).Nonempty :=
    ⟨zeta ^ 3, (mem_primitiveRoots (by decide)).mpr hroot⟩
  exact exists_finite_primePower_sUnit_detector K S0 (2 : ℕ+) hmu 2 1
    (by norm_num) (by decide) (by norm_num)

/-- The cubic detector has the same concrete scope as the quadratic one.
Its support and detector need not coincide with the quadratic choices. -/
theorem exists_finite_cubic_sUnit_detector
    (S0 : Finset (HeightOneSpectrum (𝓞 K))) (zeta : K)
    (hzeta : IsPrimitiveRoot zeta 6) :
    ∃ S T : Finset (HeightOneSpectrum (𝓞 K)),
      S0 ⊆ S ∧ Disjoint S T ∧
      ∀ x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
        (∀ q ∈ T, ∃ z : (q.adicCompletion K)ˣ,
          z ^ 3 = Units.map (algebraMap K (q.adicCompletion K)).toMonoidHom (x : Kˣ)) ↔
        ∃ y : (S : Set (HeightOneSpectrum (𝓞 K))).unit K, y ^ 3 = x := by
  have hroot : IsPrimitiveRoot (zeta ^ 2) 3 :=
    IsPrimitiveRoot.pow (by decide) hzeta (by decide)
  have hmu : (primitiveRoots 3 K).Nonempty :=
    ⟨zeta ^ 2, (mem_primitiveRoots (by decide)).mpr hroot⟩
  exact exists_finite_primePower_sUnit_detector K S0 (3 : ℕ+) hmu 3 1
    (by norm_num) (by decide) (by norm_num)

end HeckeGeneral.Arithmetic.AllowedGeneratorConstruction
