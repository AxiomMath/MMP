module

public import MMP.AlgebraicGeometry.MMP.Fourfold.LogMinimalModel
public import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeSections
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.AutomorphismSchemeDimension
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.DerivedChowFourierMukai
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechDerivedSupportImmersion
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.MorphismToRelativeProj
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ResidueFunctionIntegral
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRochFull
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DimensionZeroSplitting
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafSections

/-!
# Riemann–Roch on curves, homogeneous generators, floor-section algebras and finite fibres

This file collects four results used in the study of projective fourfolds.

* **Riemann–Roch for a vector bundle on a curve.** Let `C` be a smooth projective curve over an
  algebraically closed field `k`, of genus `g = dim_k H¹(C, 𝒪_C)`, and `E` a locally free
  `𝒪_C`-module of rank `r`. Then `χ(C, E) = deg (det E) + r (1 - g)`, where `det E = ⋀ʳ E` and
  `deg L = χ(C, L) - χ(C, 𝒪_C)` is the degree of an invertible sheaf on a proper curve.
* **Homogeneous generators.** A finitely generated `ℕ`-graded `A`-algebra whose structure map
  lands in degree zero is generated as an `A`-algebra by finitely many homogeneous elements: the
  homogeneous components of any finite generating set will do.
* **Finite generation of the floor-section algebra.** Let `f : Y ⟶ Z` be a projective morphism of
  normal varieties over a field `k` and `D` a `ℚ`-divisor on `Y` with a positive Cartier multiple
  generated over `Z`. Then over every affine open `V ⊆ Z` the graded subring
  `⨁_{m ≥ 0} H⁰(f⁻¹V, 𝒪_Y(⌊mD⌋)) tᵐ` of `𝒦_Y(f⁻¹V)[t]` is a finitely generated
  `Γ(Z, V)`-algebra.
* **The non-isomorphism locus of a proper birational morphism.** Let `h : Y ⟶ Z` be a proper
  birational morphism of varieties over `k` with `Z` normal, and `z ∈ Z` a closed point. Then `h`
  is an isomorphism over a neighbourhood of `z` if and only if the fibre `h⁻¹(z)` is finite.

## Main results

* `MMP.Fourfold.eulerCharacteristic_eq_curveDegree_exteriorPower_add`:
  `χ(C, E) = deg (⋀ʳ E) + r (1 - g)`.
* `MMP.GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_of_finiteType`: a finitely
  generated graded `A`-algebra is generated over `A` by finitely many homogeneous elements.
* `MMP.Fourfold.QDivisor.IsRelativelySemiample.fg_roundDownSections`, and its form
  `MMP.Fourfold.fg_roundDownSections_of_isRelativelyFreeDivisor` for a `ℚ`-divisor with a
  relatively free Cartier Weil multiple, and
  `MMP.Fourfold.fg_roundDownSections_of_isRelativelyFreeDivisor_of_locallyOfFiniteType` over a
  base `Z` only locally of finite type over `k`.
* `MMP.Resolution.Bridges.exists_isIso_morphismRestrict_iff_finite_preimage_singleton`: `h` is an
  isomorphism over a neighbourhood of `z` if and only if `h⁻¹(z)` is finite.

## Implementation notes

* A vector bundle of rank `r` is a sheaf of modules `E` with
  `SheafOfModules.IsFiniteLocallyFreeOfRank E r`; its determinant is
  `AlgebraicGeometry.Scheme.Modules.exteriorPower E r`, finite locally free of rank
  `binom(r, r) = 1`, and its degree is `AlgebraicGeometry.curveDegree` in rank one. The genus is
  `AlgebraicGeometry.genus`, the dimension of `H¹(C, 𝒪_C)`, so the statement contains the
  identity `χ(C, 𝒪_C) = 1 - g`, i.e. `H⁰(C, 𝒪_C) = k`. The coherence of `E` that
  `AlgebraicGeometry.eulerCharacteristic` takes is supplied by properness over `k`.
* A graded `A`-algebra is `GradedAlgebra 𝒜` for `𝒜 : ℕ → Submodule A R`, which places the image
  of `A` in `𝒜 0`. Mathlib's `GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous` is the
  case `A = 𝒜 0`; here the generators generate over `A` itself.
* The floor-section algebra over `V` is described inside `𝒦_Y(f⁻¹V)[t]`, its degree-`m` part
  being `𝒪_Y(⌊mD⌋)(f⁻¹V)` (`MMP.Mori.Divisor.divisorialSubmodule` of
  `MMP.Mori.DivisorWithCoeffs.roundDown`). Finite generation over `Γ(Z, V)` is stated as:
  finitely many elements `G` of the algebra such that every element lies in the subring generated
  by `G` and the image of `Γ(Z, V)` under `f^#`. The source passes through the finiteness of
  twisted section modules over the section algebra of `𝒪_Y(qD)`; here the floor algebra is shown
  directly to be integral over finitely many generators of degree `q`.
* "`h` is an isomorphism over `V`" is `IsIso (h ∣_ V)` and the fibre `h⁻¹(z)` is the
  set-theoretic preimage `h ⁻¹' {z}`. Birationality is `AlgebraicGeometry.IsBirational`, which a
  birational morphism in the sense of `MMP.Mori.IsBirationalMorphism` between integral schemes
  satisfies by `MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism`.

## References

* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KM98]
* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], Corollary III.11.4.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace MMP.Fourfold

/-- **Riemann–Roch for vector bundles on a curve.** On a smooth projective curve `C` over an
algebraically closed field `k`, a locally free sheaf `E` of rank `r` satisfies
`χ(C, E) = deg (⋀ʳ E) + r (1 - g)`, where `g = AlgebraicGeometry.genus sC`. -/
@[mmp "lem_fourfold_curve_vector_bundle_euler"]
theorem eulerCharacteristic_eq_curveDegree_exteriorPower_add
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))
    [IsCurve k sC] [IsProjectiveVariety k sC] [Smooth sC]
    (E : C.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    haveI : E.IsCoherent :=
      Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k sC E r
    haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (Scheme.Modules.exteriorPower E r) 1 := by
      simpa only [Nat.choose_self] using
        Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower E r r
    eulerCharacteristic k sC E =
      curveDegree k sC (IsCurve.topologicalKrullDim_eq_one (f := sC)).le
          (Scheme.Modules.exteriorPower E r) 1 +
        (r : ℤ) * (1 - (genus sC : ℤ)) := by
  have hdim := (IsCurve.topologicalKrullDim_eq_one (f := sC)).le
  haveI := GenusOne.isIso_globalSections_of_isAlgClosed sC
  haveI :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k sC E r
  haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k sC
  rw [← curveDegree_eq_curveDegree_exteriorPower_of_isProper k sC hdim r E,
    curveDegree_eq_eulerCharacteristic_sub k sC hdim E r,
    eulerCharacteristic_unit_eq_one_sub_genus k sC hdim]
  ring

end MMP.Fourfold

namespace MMP.GradedAlgebra

/-- A finitely generated `ℕ`-graded `A`-algebra `R` (with `A` in degree zero) is generated as an
`A`-algebra by a finite set of homogeneous elements. -/
@[mmp "lem_fourfold_homogeneous_generators"]
theorem exists_finset_adjoin_eq_top_and_homogeneous_of_finiteType
    {A R : Type*} [CommSemiring A] [CommSemiring R] [Algebra A R]
    (𝒜 : ℕ → Submodule A R) [GradedAlgebra 𝒜] [Algebra.FiniteType A R] :
    ∃ s : Finset R, Algebra.adjoin A (s : Set R) = ⊤ ∧
      ∀ x ∈ s, SetLike.IsHomogeneousElem 𝒜 x := by
  classical
  obtain ⟨F, hF⟩ := Algebra.FiniteType.out (R := A) (A := R)
  let ι₀ := Σ (x : F), (DirectSum.decompose 𝒜 x.1).support
  let x (i : ι₀) : R := ((DirectSum.decompose 𝒜) i.1 i.2).1
  refine ⟨Finset.univ.image x, ?_,
    by simpa using fun f ↦ ⟨_, (DirectSum.decompose 𝒜 f.1 f.2).2⟩⟩
  rw [← top_le_iff, ← hF, Algebra.adjoin_le_iff]
  intro s hs
  rw [← DirectSum.sum_support_decompose 𝒜 s]
  exact sum_mem fun n hn ↦ Algebra.subset_adjoin (by simpa using ⟨⟨⟨s, hs⟩, n, hn⟩, rfl⟩)

end MMP.GradedAlgebra

namespace MMP.Fourfold

open MMP.Mori

/-! ### Finite generation of the floor-section algebra

Let `qD = B` be the Weil divisor of an `f`-generated Cartier divisor, `q > 0`. Then `f⁻¹V` is
covered by finitely many opens `W_i` on which a section `a_i ∈ H⁰(f⁻¹V, 𝒪_Y(B))` generates
`𝒪_Y(B)`. Let `C` be the subalgebra generated over `Γ(Z, V)` by the `a_i t^q`. Every
`u t^{qn}` with `u ∈ H⁰(f⁻¹V, 𝒪_Y(nB))` is integral over `C`: by the valuative criterion it lies
in every valuation ring `𝒪_v` containing `C`, since at the centre `x ∈ W_i` of `v` (which exists
by properness) `u = r a_iⁿ` with `r ∈ 𝒪_{Y,x}`, and
`u t^{qn} = r (a_i / a_{i₀})ⁿ (a_{i₀} t^q)ⁿ` for `i₀` maximizing `v(a_i t^q)`. A homogeneous
`s tᵐ` has `(s tᵐ)^q ∈ H⁰(𝒪_Y(mB)) t^{qm}` since `q ⌊mD⌋ ≤ mB`, so the whole algebra is
integral over `C`; as it embeds in a field essentially of finite type over the Nagata ring
`Γ(Z, V)`, it is finite over `C`, hence of finite type.
-/

/-! #### Finite type from integrality over a Nagata ring -/

section Nagata

/-- Linear independence over `F` of elements algebraic over `F` persists over the subalgebra
generated by an algebraically independent family. -/
private theorem linearIndependent_adjoin_of_algebraicIndependent {F L : Type*} [Field F] [Field L]
    [Algebra F L] {σ : Type*} {b : σ → L} (hb : AlgebraicIndependent (algebraicClosure F L) b)
    {ι : Type*} [Finite ι] {v : ι → algebraicClosure F L} (hv : LinearIndependent F v) :
    LinearIndependent (Algebra.adjoin F (Set.range b)) (fun i => (v i : L)) := by
  classical
  have := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hpoly : ∀ i, ∃ P : MvPolynomial σ F, MvPolynomial.aeval b P = (g i : L) :=
    fun i => (Algebra.adjoin_range_eq_range_aeval F b).le (g i).2
  choose P hP using hpoly
  let Q : MvPolynomial σ (algebraicClosure F L) :=
    ∑ i, MvPolynomial.C (v i) * MvPolynomial.map (algebraMap F (algebraicClosure F L)) (P i)
  have hQ : MvPolynomial.aeval b Q = 0 := by
    simp only [Q, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_map_algebraMap]
    rw [← hg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hP i, mul_comm]
    rfl
  have hcoeff : ∀ α i, (P i).coeff α = 0 := by
    intro α
    have h := congrArg (fun p : MvPolynomial _ _ => p.coeff α) (hb.eq_zero_of_aeval_eq_zero Q hQ)
    simp only [Q, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map,
      MvPolynomial.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at h
    refine (Fintype.linearIndependent_iff.mp hv) (fun i => (P i).coeff α) ?_
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, mul_comm]
  intro i
  apply Subtype.ext
  rw [← hP i]
  have : P i = 0 := MvPolynomial.ext _ _ fun α => by
    rw [hcoeff α i, MvPolynomial.coeff_zero, Finsupp.zero_apply]
  rw [this, map_zero]
  rfl

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- The algebraic closure of `F` in a field extension essentially of finite type is finite. -/
private theorem finiteDimensional_algebraicClosure {F L : Type*} [Field F] [Field L] [Algebra F L]
    [Algebra.EssFiniteType F L] : FiniteDimensional F (algebraicClosure F L) := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_isTranscendenceBasis (K := F) (L := L)
  have hb : AlgebraicIndependent (algebraicClosure F L) ((↑) : s → L) :=
    hs.1.extendScalars (algebraicClosure F L)
  set L0 := IntermediateField.adjoin F (Set.range ((↑) : s → L))
  have : Algebra.IsAlgebraic L0 L := hs.isAlgebraic_field
  have : Algebra.EssFiniteType L0 L := Algebra.EssFiniteType.of_comp F L0 L
  have : Module.Finite L0 L := Algebra.finite_of_essFiniteType_of_isAlgebraic
  refine Module.rank_lt_aleph0_iff.mp <|
    lt_of_le_of_lt (_root_.rank_le (n := Module.finrank L0 L) fun t ht => ?_)
    (Cardinal.natCast_lt_aleph0)
  have h2 : LinearIndependent L0 (fun i : t => ((i : algebraicClosure F L) : L)) :=
    (LinearIndependent.iff_fractionRing (Algebra.adjoin F (Set.range ((↑) : s → L))) L0).mp
      (linearIndependent_adjoin_of_algebraicIndependent hb ht)
  simpa using h2.fintype_card_le_finrank

/-- An `R`-algebra `S` embedded in a field essentially of finite type over the Nagata ring `R`
and integral over the subalgebra generated by a finite set is of finite type over `R`. -/
private theorem finiteType_of_isIntegral_adjoin {R S L : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Field L] [Algebra R L] (hR : IsNagataRing R) [Algebra.EssFiniteType R L]
    (Ψ : S →ₐ[R] L) (hΨ : Function.Injective Ψ) (g : Finset S)
    (hint : ∀ s : S, _root_.IsIntegral (Algebra.adjoin R (g : Set S)) s) :
    Algebra.FiniteType R S := by
  classical
  set C := Algebra.adjoin R (g : Set S)
  have hCft : Algebra.FiniteType R C := Algebra.FiniteType.adjoin_of_finite g.finite_toSet
  have hCN : IsNagataRing C := IsNagataRing.of_finiteType hR
  have : IsDomain S := hΨ.isDomain Ψ.toRingHom
  let : Algebra C L := (Ψ.toRingHom.comp (algebraMap C S)).toAlgebra
  have : FaithfulSMul C L :=
    (faithfulSMul_iff_algebraMap_injective C L).mpr (hΨ.comp Subtype.val_injective)
  let : Algebra (FractionRing C) L := FractionRing.liftAlgebra C L
  have : IsScalarTower C (FractionRing C) L := FractionRing.isScalarTower_liftAlgebra C L
  have : IsScalarTower R (FractionRing C) L := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    rw [IsScalarTower.algebraMap_apply R C (FractionRing C),
      ← IsScalarTower.algebraMap_apply C (FractionRing C) L]
    change _ = Ψ (algebraMap C S (algebraMap R C r))
    rw [← IsScalarTower.algebraMap_apply R C S, Ψ.commutes]
  have : Algebra.EssFiniteType (FractionRing C) L := Algebra.EssFiniteType.of_comp R _ L
  have : FiniteDimensional (FractionRing C) (algebraicClosure (FractionRing C) L) :=
    finiteDimensional_algebraicClosure
  have hfin := module_finite_integralClosure_of_isNagataRing (A := C) (FractionRing C)
    (algebraicClosure (FractionRing C) L) hCN
  set E := algebraicClosure (FractionRing C) L
  have hmemE : ∀ s : S, Ψ s ∈ E := fun s => by
    rw [mem_algebraicClosure_iff]
    have h1 : _root_.IsIntegral C (Ψ s) := by
      let ΨC : S →ₐ[C] L := { Ψ.toRingHom with commutes' := fun _ => rfl }
      exact (hint s).map ΨC
    exact (h1.tower_top (A := FractionRing C)).isAlgebraic
  have hintE : ∀ s : S, IsIntegral C (⟨Ψ s, hmemE s⟩ : E) := fun s => by
    let ΨC : S →ₐ[C] E :=
      { toFun := fun s => ⟨Ψ s, hmemE s⟩
        map_one' := Subtype.ext (map_one Ψ)
        map_mul' := fun a b => Subtype.ext (map_mul Ψ a b)
        map_zero' := Subtype.ext (map_zero Ψ)
        map_add' := fun a b => Subtype.ext (map_add Ψ a b)
        commutes' := fun _ => rfl }
    exact (hint s).map ΨC
  let φ : S →ₗ[C] integralClosure C E :=
    { toFun := fun s => ⟨⟨Ψ s, hmemE s⟩, hintE s⟩
      map_add' := fun a b => by ext; simp
      map_smul' := fun c a => by
        ext
        change Ψ (c • a) = (algebraMap C L c) * Ψ a
        rw [Algebra.smul_def, map_mul]
        rfl }
  have hφ : Function.Injective φ := fun a b h => hΨ (by
    simpa [φ] using congrArg (fun z : integralClosure C E => ((z : E) : L)) h)
  have : Module.Finite C S := Module.Finite.of_injective φ hφ
  exact Algebra.FiniteType.trans hCft (Module.Finite.finiteType (R := C) S)

end Nagata

/-! #### Centres of valuations and residue fields -/

section Centre

private theorem fromSpecResidueField_comp_eq {M Z : Scheme.{u}} (π : M ⟶ Z) {U : Z.Opens}
    (hU : IsAffineOpen U) (y : M) (hy : y ∈ π ⁻¹ᵁ U) :
    M.fromSpecResidueField y ≫ π = Spec.map (π.app U ≫ M.presheaf.germ (π ⁻¹ᵁ U) y hy ≫
      M.residue y) ≫ hU.fromSpec := by
  rw [Scheme.fromSpecResidueField, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
    ← hU.fromSpecStalk_eq_fromSpecStalk (x := π y) hy]
  dsimp only [IsAffineOpen.fromSpecStalk]
  simp only [← Category.assoc, ← Spec.map_comp]
  congr 2
  exact congrArg (· ≫ M.residue y) (Scheme.Hom.germ_stalkMap π U y hy)

/-- **Centres of valuations along a universally closed morphism.** A valuation ring of the residue
field at `y ∈ π⁻¹U` containing the image of `Γ(Z, U)` dominates the local ring of a
specialization `x ∈ π⁻¹U` of `y`. -/
private theorem exists_center_of_valuationSubring {M Z : Scheme.{u}} (π : M ⟶ Z)
    [UniversallyClosed π] {U : Z.Opens} (hU : IsAffineOpen U) (y : M) (hy : y ∈ π ⁻¹ᵁ U)
    (V : ValuationSubring (M.residueField y))
    (hV : ∀ r : Γ(Z, U), M.residue y (M.presheaf.germ (π ⁻¹ᵁ U) y hy (π.app U r)) ∈ V) :
    ∃ (x : M) (h : y ⤳ x), x ∈ π ⁻¹ᵁ U ∧
      ∀ t : M.presheaf.stalk x, M.residue y (M.presheaf.stalkSpecializes h t) ∈ V := by
  let K := M.residueField y
  let ρ : Γ(Z, U) ⟶ K := π.app U ≫ M.presheaf.germ (π ⁻¹ᵁ U) y hy ≫ M.residue y
  have hVmem : ∀ a, ρ.hom a ∈ V.toSubring := hV
  let φV : Γ(Z, U) ⟶ CommRingCat.of V :=
    CommRingCat.ofHom (ρ.hom.codRestrict V.toSubring hVmem)
  have hφ : φV ≫ CommRingCat.ofHom (algebraMap V K) = ρ := by
    ext; rfl
  have w : M.fromSpecResidueField y ≫ π =
      Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ (Spec.map φV ≫ hU.fromSpec) := by
    rw [fromSpecResidueField_comp_eq π hU y hy, ← Spec.map_comp_assoc, hφ]
  have H : ValuativeCriterion.Existence π :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed π) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) π).1
  obtain ⟨l, hl₁, hl₂⟩ :=
    (H (ValuativeCommSq.mk (R := V) (K := K) (M.fromSpecResidueField y)
      (Spec.map φV ≫ hU.fromSpec) ⟨w⟩)).exists_lift
  dsimp only at hl₁ hl₂
  let x := l (IsLocalRing.closedPoint V)
  have hyx : y ⤳ x := by
    simp_rw [x, ← Scheme.fromSpecResidueField_apply y (IsLocalRing.closedPoint K), ← hl₁]
    exact (IsLocalRing.specializes_closedPoint _).map l.continuous
  have hxU : x ∈ π ⁻¹ᵁ U := by
    have h2 := congrArg (fun h : Spec (CommRingCat.of V) ⟶ Z => h (IsLocalRing.closedPoint V)) hl₂
    change (l ≫ π) (IsLocalRing.closedPoint V) ∈ U
    rw [h2, ← SetLike.mem_coe, ← hU.range_fromSpec]
    exact ⟨_, rfl⟩
  refine ⟨x, hyx, hxU, fun t => ?_⟩
  let ψ : M.presheaf.stalk x ⟶ CommRingCat.of V := Scheme.stalkClosedPointTo l
  have hl : Spec.map ψ ≫ M.fromSpecStalk x = l := Scheme.Spec_stalkClosedPointTo_fromSpecStalk l
  have heq : ψ ≫ CommRingCat.ofHom (algebraMap V K) =
      M.presheaf.stalkSpecializes hyx ≫ M.residue y := by
    apply Spec.map_injective
    apply (cancel_mono (M.fromSpecStalk x)).mp
    rw [Spec.map_comp, Category.assoc, hl, hl₁, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    rfl
  have hval : algebraMap V K (ψ t) = M.residue y (M.presheaf.stalkSpecializes hyx t) :=
    congrArg (fun g => g.hom t) heq
  rw [← hval]
  exact (ψ t).2

/-- The residue field at a point over an affine open `U` of the base of a morphism locally of
finite type is essentially of finite type over `Γ(Z, U)`. -/
private theorem essFiniteType_residueField_of_mem {M Z : Scheme.{u}} (π : M ⟶ Z)
    [LocallyOfFiniteType π] {U : Z.Opens} (hU : IsAffineOpen U) (y : M) (hy : y ∈ π ⁻¹ᵁ U) :
    letI : Algebra Γ(Z, U) (M.residueField y) :=
      (π.app U ≫ M.presheaf.germ (π ⁻¹ᵁ U) y hy ≫ M.residue y).hom.toAlgebra
    Algebra.EssFiniteType Γ(Z, U) (M.residueField y) := by
  obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset (X := M) (x := y)
    (U := π ⁻¹ᵁ U) hy
  have e : V ≤ π ⁻¹ᵁ U := hVU
  let : Algebra Γ(Z, U) Γ(M, V) := (π.appLE U V e).hom.toAlgebra
  let : Algebra Γ(Z, U) (M.presheaf.stalk y) :=
    (π.app U ≫ M.presheaf.germ (π ⁻¹ᵁ U) y hy).hom.toAlgebra
  let : Algebra Γ(M, V) (M.presheaf.stalk y) := (M.presheaf.germ V y hyV).hom.toAlgebra
  let : Algebra Γ(Z, U) (M.residueField y) :=
    (π.app U ≫ M.presheaf.germ (π ⁻¹ᵁ U) y hy ≫ M.residue y).hom.toAlgebra
  let : Algebra (M.presheaf.stalk y) (M.residueField y) := (M.residue y).hom.toAlgebra
  have : IsScalarTower Γ(Z, U) Γ(M, V) (M.presheaf.stalk y) := by
    refine IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a ↦ ?_)
    change M.presheaf.germ (π ⁻¹ᵁ U) y hy (π.app U a) =
      M.presheaf.germ V y hyV (π.appLE U V e a)
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, M.presheaf.germ_res_apply]
  have : IsScalarTower Γ(Z, U) (M.presheaf.stalk y) (M.residueField y) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun _ ↦ rfl)
  have hft : Algebra.FiniteType Γ(Z, U) Γ(M, V) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType π ‹_› ⟨U, hU⟩ ⟨V, hV⟩ e
  have : IsLocalization (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl
      (M.presheaf.stalk y) := hV.isLocalization_stalk ⟨y, hyV⟩
  have : Algebra.EssFiniteType Γ(M, V) (M.presheaf.stalk y) :=
    Algebra.EssFiniteType.of_isLocalization _ (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl
  have : Algebra.EssFiniteType Γ(Z, U) (M.presheaf.stalk y) :=
    Algebra.EssFiniteType.comp Γ(Z, U) Γ(M, V) (M.presheaf.stalk y)
  exact Algebra.EssFiniteType.of_surjective
    (IsScalarTower.toAlgHom Γ(Z, U) (M.presheaf.stalk y) (M.residueField y))
    (M.residue_surjective y)

/-- The sections over an affine open of a scheme locally of finite type over a field form a
Nagata ring. -/
private theorem isNagataRing_of_locallyOfFiniteType {k : Type u} [Field k] {Z : Scheme.{u}}
    (sZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType sZ] {U : Z.Opens} (hU : IsAffineOpen U) :
    IsNagataRing Γ(Z, U) := by
  let : Algebra k Γ(Z, U) := ((Scheme.ΓSpecIso (.of k)).inv ≫ sZ.appLE ⊤ U (by simp)).hom.toAlgebra
  have : Algebra.FiniteType k Γ(Z, U) := by
    change RingHom.FiniteType ((Scheme.ΓSpecIso (.of k)).inv ≫ sZ.appLE ⊤ U (by simp)).hom
    rw [CommRingCat.hom_comp]
    exact (HasRingHomProperty.appLE @LocallyOfFiniteType sZ inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _).comp (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv.surjective)
  exact IsNagataRing.of_finiteType (A := k) IsNagataRing.of_field

end Centre

/-! #### Valuation rings -/

/-- In a valuation ring, among finitely many elements not all zero there is a nonzero one
dividing all the others: one of maximal valuation. -/
private theorem exists_div_mem_valuationSubring {L ι : Type*} [Field L] (V : ValuationSubring L)
    {T : Finset ι} (g : ι → L) (hne : ∃ t ∈ T, g t ≠ 0) :
    ∃ i ∈ T, g i ≠ 0 ∧ ∀ t ∈ T, g t / g i ∈ V := by
  classical
  obtain ⟨t0, ht0, hg0⟩ := hne
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (T.filter (g · ≠ 0)) (V.valuation ∘ g)
    ⟨t0, Finset.mem_filter.mpr ⟨ht0, hg0⟩⟩
  obtain ⟨hiT, hgi⟩ := Finset.mem_filter.mp hi
  refine ⟨i, hiT, hgi, fun t ht => ?_⟩
  by_cases hgt : g t = 0
  · simp [hgt]
  rw [← ValuationSubring.valuation_le_one_iff, map_div₀]
  exact div_le_one_of_le₀ (hmax t (Finset.mem_filter.mpr ⟨ht, hgt⟩)) zero_le'

/-! #### The floor-section algebra -/

section FloorAlgebra

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]

private theorem mul_mem_divisorialSubmodule {D D' : Divisor Y} {U : Y.Opens}
    {φ ψ : (rationalFunctionsPresheaf Y).obj (op U)} (hφ : φ ∈ D.divisorialSubmodule U)
    (hψ : ψ ∈ D'.divisorialSubmodule U) : φ * ψ ∈ (D + D').divisorialSubmodule U :=
  (Divisor.divisorialMul U ⟨φ, hφ⟩ ⟨ψ, hψ⟩).2

private theorem one_mem_divisorialSubmodule (U : Y.Opens) :
    (1 : (rationalFunctionsPresheaf Y).obj (op U)) ∈ (0 : Divisor Y).divisorialSubmodule U :=
  Divisor.IsDivisorialSection.one le_rfl U

private theorem pow_mem_divisorialSubmodule {D : Divisor Y} {U : Y.Opens}
    {φ : (rationalFunctionsPresheaf Y).obj (op U)} (hφ : φ ∈ D.divisorialSubmodule U) :
    ∀ n : ℕ, φ ^ n ∈ ((n : ℤ) • D).divisorialSubmodule U
  | 0 => by simpa using one_mem_divisorialSubmodule U
  | n + 1 => by
    rw [pow_succ, show ((n + 1 : ℕ) : ℤ) • D = (n : ℤ) • D + D by
      rw [Nat.cast_succ, add_smul, one_smul]]
    exact mul_mem_divisorialSubmodule (pow_mem_divisorialSubmodule hφ n) hφ

omit [IsLocallyNoetherian Y] [IsNormal Y] in
private theorem roundDown_add_le (D : QDivisor Y) (a b : ℕ) :
    DivisorWithCoeffs.roundDown ((a : ℚ) • D) + DivisorWithCoeffs.roundDown ((b : ℚ) • D) ≤
      DivisorWithCoeffs.roundDown (((a + b : ℕ) : ℚ) • D) := fun P => by
  change (DivisorWithCoeffs.roundDown ((a : ℚ) • D)).coeff P +
    (DivisorWithCoeffs.roundDown ((b : ℚ) • D)).coeff P ≤
      (DivisorWithCoeffs.roundDown (((a + b : ℕ) : ℚ) • D)).coeff P
  simp only [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul, Nat.cast_add,
    add_smul]
  exact Int.le_floor_add ((a : ℚ) • D.coeff P) ((b : ℚ) • D.coeff P)

omit [IsLocallyNoetherian Y] [IsNormal Y] in
private theorem roundDown_natCast_zero_smul (D : QDivisor Y) :
    DivisorWithCoeffs.roundDown (((0 : ℕ) : ℚ) • D) = 0 :=
  DivisorWithCoeffs.ext' fun P => by simp

variable (D : QDivisor Y) (U : Y.Opens)

/-- The floor-section algebra `⨁_{m ≥ 0} H⁰(U, 𝒪_Y(⌊mD⌋)) tᵐ`, as a subring of `𝒦_Y(U)[t]`. -/
private def floorAlgebra : Subring (Polynomial ((rationalFunctionsPresheaf Y).obj (op U))) where
  carrier := {p | ∀ m : ℕ,
    p.coeff m ∈ (DivisorWithCoeffs.roundDown ((m : ℚ) • D)).divisorialSubmodule U}
  zero_mem' m := by simp
  one_mem' m := by
    rw [Polynomial.coeff_one]
    split_ifs with h
    · subst h
      rw [roundDown_natCast_zero_smul]
      exact one_mem_divisorialSubmodule U
    · exact Submodule.zero_mem _
  add_mem' hp hq m := by
    rw [Polynomial.coeff_add]
    exact Submodule.add_mem _ (hp m) (hq m)
  neg_mem' hp m := by
    rw [Polynomial.coeff_neg]
    exact Submodule.neg_mem _ (hp m)
  mul_mem' {p q} hp hq m := by
    rw [Polynomial.coeff_mul]
    refine Submodule.sum_mem _ fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    refine Divisor.divisorialSubmodule_mono ?_ U
      (mul_mem_divisorialSubmodule (hp x.1) (hq x.2))
    rw [← hx]
    exact roundDown_add_le D x.1 x.2

private theorem monomial_mem_floorAlgebra {m : ℕ} {s : (rationalFunctionsPresheaf Y).obj (op U)}
    (hs : s ∈ (DivisorWithCoeffs.roundDown ((m : ℚ) • D)).divisorialSubmodule U) :
    Polynomial.monomial m s ∈ floorAlgebra D U := fun n => by
  rw [Polynomial.coeff_monomial]
  split_ifs with h
  · exact h ▸ hs
  · exact Submodule.zero_mem _

end FloorAlgebra

/-! #### Finite generation from local generators of `𝒪_Y(qD)` -/

section Main

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]

omit [IsLocallyNoetherian Y] [IsNormal Y] in
private theorem roundDown_natCast_mul_smul (D : QDivisor Y) {q : ℕ} (B : Divisor Y)
    (hB : ∀ P, (B.coeff P : ℚ) = q * D.coeff P) (n : ℕ) :
    DivisorWithCoeffs.roundDown (((q * n : ℕ) : ℚ) • D) = (n : ℤ) • B :=
  DivisorWithCoeffs.ext' fun P => by
    rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_smul, smul_eq_mul, smul_eq_mul, Nat.cast_mul,
      show (q : ℚ) * n * D.coeff P = ((n * B.coeff P : ℤ) : ℚ) by push_cast [hB P]; ring,
      Int.floor_intCast]

omit [IsLocallyNoetherian Y] [IsNormal Y] in
private theorem smul_roundDown_le (D : QDivisor Y) {q : ℕ} (B : Divisor Y)
    (hB : ∀ P, (B.coeff P : ℚ) = q * D.coeff P) (m : ℕ) :
    (q : ℤ) • DivisorWithCoeffs.roundDown ((m : ℚ) • D) ≤ (m : ℤ) • B := fun P => by
  change ((q : ℤ) • DivisorWithCoeffs.roundDown ((m : ℚ) • D)).coeff P ≤ ((m : ℤ) • B).coeff P
  rw [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_smul,
    DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul]
  have h1 : ((q * ⌊(m : ℚ) * D.coeff P⌋ : ℤ) : ℚ) ≤ ((m * B.coeff P : ℤ) : ℚ) := by
    push_cast
    rw [hB P]
    have := Int.floor_le ((m : ℚ) * D.coeff P)
    have hq : (0 : ℚ) ≤ q := Nat.cast_nonneg q
    nlinarith
  exact_mod_cast h1

private theorem monomial_natCast_mul_mem_floorAlgebra (D : QDivisor Y) {q : ℕ} (B : Divisor Y)
    (hB : ∀ P, (B.coeff P : ℚ) = q * D.coeff P) {U : Y.Opens} {n : ℕ}
    {u : (rationalFunctionsPresheaf Y).obj (op U)}
    (hu : u ∈ ((n : ℤ) • B).divisorialSubmodule U) :
    Polynomial.monomial (q * n) u ∈ floorAlgebra D U :=
  monomial_mem_floorAlgebra D U (by rwa [roundDown_natCast_mul_smul D B hB n])

/-- With `qD = B` integral, the floor algebra is integral over `C` as soon as every monomial
`u t^{qn}` with `u ∈ 𝒪_Y(nB)` is: the `q`-th power of a monomial of degree `m` is of that form. -/
private theorem isIntegral_floorAlgebra (D : QDivisor Y) {q : ℕ} (hq : 0 < q) (B : Divisor Y)
    (hB : ∀ P, (B.coeff P : ℚ) = q * D.coeff P) {U : Y.Opens} {C : Type*} [CommRing C]
    [Algebra C (floorAlgebra D U)]
    (h : ∀ (n : ℕ) (u : (rationalFunctionsPresheaf Y).obj (op U))
      (hu : u ∈ ((n : ℤ) • B).divisorialSubmodule U),
      _root_.IsIntegral C (⟨Polynomial.monomial (q * n) u,
        monomial_natCast_mul_mem_floorAlgebra D B hB hu⟩ : floorAlgebra D U))
    (p : floorAlgebra D U) : _root_.IsIntegral C p := by
  have hmon : ∀ (m : ℕ) (s : (rationalFunctionsPresheaf Y).obj (op U))
      (hs : Polynomial.monomial m s ∈ floorAlgebra D U),
      _root_.IsIntegral C (⟨Polynomial.monomial m s, hs⟩ : floorAlgebra D U) := by
    intro m s hs
    have hs' : s ∈ (DivisorWithCoeffs.roundDown ((m : ℚ) • D)).divisorialSubmodule U := by
      simpa using hs m
    have hsq : s ^ q ∈ ((m : ℤ) • B).divisorialSubmodule U :=
      Divisor.divisorialSubmodule_mono (smul_roundDown_le D B hB m) U
        (pow_mem_divisorialSubmodule hs' q)
    have hpow : (⟨Polynomial.monomial m s, hs⟩ : floorAlgebra D U) ^ q =
        ⟨Polynomial.monomial (q * m) (s ^ q),
          monomial_natCast_mul_mem_floorAlgebra D B hB hsq⟩ := by
      apply Subtype.ext
      simp only [SubmonoidClass.coe_pow, Polynomial.monomial_pow, mul_comm m q]
    exact IsIntegral.of_pow hq (hpow ▸ h m _ hsq)
  have hp : p = ∑ m ∈ (p : Polynomial ((rationalFunctionsPresheaf Y).obj (op U))).support,
      (⟨Polynomial.monomial m
          ((p : Polynomial ((rationalFunctionsPresheaf Y).obj (op U))).coeff m),
        monomial_mem_floorAlgebra D U (p.2 m)⟩ : floorAlgebra D U) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact (p : Polynomial ((rationalFunctionsPresheaf Y).obj (op U))).as_sum_support
  rw [hp]
  exact (integralClosure C (floorAlgebra D U)).sum_mem fun m _ => hmon m _ _

/-- The local expression `u = r aⁿ` at a point `x` of an open `W'` on which `a` is invertible
with inverse `b ∈ 𝒪_Y(-B)(W')`, for `u ∈ 𝒪_Y(nB)(W)`. -/
private theorem exists_stalk_mul_pow_eq {B : Divisor Y} {W W' : Y.Opens} (hW' : W' ≤ W)
    {Y0 : irreducibleComponents Y} (hη : componentGenericPoint Y Y0 ∈ W)
    (hηt : componentGenericPoint Y Y0 ∈ W') {x : Y} (hx : x ∈ W') (hxY0 : x ∈ Y0.1)
    {a : (rationalFunctionsPresheaf Y).obj (op W)}
    {b : (rationalFunctionsPresheaf Y).obj (op W')} (hb : b ∈ (-B).divisorialSubmodule W')
    (hab : (rationalFunctionsPresheaf Y).map (homOfLE hW').op a * b = 1) (n : ℕ)
    {u : (rationalFunctionsPresheaf Y).obj (op W)}
    (hu : u ∈ ((n : ℤ) • B).divisorialSubmodule W) :
    ∃ r : Y.presheaf.stalk x,
      (stalkToRationalFunctions Y hxY0).hom r * a ⟨Y0, hη⟩ ^ n = u ⟨Y0, hη⟩ := by
  let φ : (rationalFunctionsPresheaf Y).obj (op W') :=
    (rationalFunctionsPresheaf Y).map (homOfLE hW').op u * b ^ n
  have hφ : φ ∈ (0 : Divisor Y).divisorialSubmodule W' := by
    have h1 : (rationalFunctionsPresheaf Y).map (homOfLE hW').op u ∈
        ((n : ℤ) • B).divisorialSubmodule W' :=
      Divisor.IsDivisorialSection.map (homOfLE hW') hu
    have := mul_mem_divisorialSubmodule h1 (pow_mem_divisorialSubmodule hb n)
    rwa [smul_neg, add_neg_cancel] at this
  obtain ⟨r, hr⟩ := Divisor.IsDivisorialSection.exists_stalk_eq hφ hx hxY0
  refine ⟨r, ?_⟩
  rw [hr]
  have hab' : a ⟨Y0, hη⟩ * b ⟨Y0, hηt⟩ = 1 := congrFun hab ⟨Y0, hηt⟩
  change u ⟨Y0, hη⟩ * b ⟨Y0, hηt⟩ ^ n * _ = u ⟨Y0, hη⟩
  rw [mul_assoc, ← mul_pow, mul_comm (b _), hab', one_pow, mul_one]

/-- A subring `R` of finite type over `A` is generated as a subring by the image of `A` and
finitely many of its elements. -/
private theorem exists_finset_closure_of_finiteType {A S : Type*} [CommRing A] [CommRing S]
    (R : Subring S) [Algebra A R] [hft : Algebra.FiniteType A R] :
    ∃ G : Finset S, (∀ p ∈ G, p ∈ R) ∧
      ∀ p ∈ R, p ∈ Subring.closure (Set.range (fun a : A => (algebraMap A R a : S)) ∪ ↑G) := by
  classical
  obtain ⟨G0, hG0⟩ := hft.out
  refine ⟨G0.image Subtype.val, fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨p', -, rfl⟩ := Finset.mem_image.mp hp
    exact p'.2
  · have key : ∀ y ∈ Algebra.adjoin A (G0 : Set R), (y : S) ∈ Subring.closure
        (Set.range (fun a : A => (algebraMap A R a : S)) ∪ ↑(G0.image Subtype.val)) := by
      intro y hy
      induction hy using Algebra.adjoin_induction with
      | mem y hy =>
        exact Subring.subset_closure (Or.inr (Finset.mem_coe.mpr
          (Finset.mem_image_of_mem _ (Finset.mem_coe.mp hy))))
      | algebraMap r => exact Subring.subset_closure (Or.inl ⟨r, rfl⟩)
      | add y z _ _ hy hz => exact Subring.add_mem _ hy hz
      | mul y z _ _ hy hz => exact Subring.mul_mem _ hy hz
    exact key ⟨p, hp⟩ (hG0 ▸ Algebra.mem_top)

/-- **The integrality step at one valuation ring.** Let `a_i` be sections of `𝒪_Y(B)` over
`f⁻¹V` invertible on opens `W_i` covering `f⁻¹V`, with inverses in `𝒪_Y(-B)`, and let `χ` embed
`κ(η)` into a field `L`. If a valuation ring of `L` contains `Γ(Z, V)` and every `χ(aᵢ) X`, then
it contains `χ(u) Xⁿ` for every `u ∈ 𝒪_Y(nB)(f⁻¹V)`. -/
private theorem residue_mul_pow_mem_valuationSubring [IsIntegral Y] {Z : Scheme.{u}}
    (f : Y ⟶ Z) [IsProper f] {V : Z.Opens} (hV : IsAffineOpen V) {B : Divisor Y}
    {Y0 : irreducibleComponents Y} (hY0 : ∀ x : Y, x ∈ Y0.1)
    (hη : componentGenericPoint Y Y0 ∈ f ⁻¹ᵁ V) {L : Type*} [Field L]
    (χ : Y.residueField (componentGenericPoint Y Y0) →+* L) (V' : ValuationSubring L)
    (hι : Function.Injective (Y.residue (componentGenericPoint Y Y0)).hom)
    (hVR : ∀ r : Γ(Z, V), χ (Y.residue _ (Y.presheaf.germ (f ⁻¹ᵁ V) _ hη (f.app V r))) ∈ V')
    {ι : Type*} {T : Finset ι} {a : ι → (rationalFunctionsPresheaf Y).obj (op (f ⁻¹ᵁ V))}
    {Wx : ι → Y.Opens} (hWx : ∀ i, Wx i ≤ f ⁻¹ᵁ V)
    {b : ∀ i, (rationalFunctionsPresheaf Y).obj (op (Wx i))}
    (hb : ∀ i, b i ∈ (-B).divisorialSubmodule (Wx i))
    (hab : ∀ i, (rationalFunctionsPresheaf Y).map (homOfLE (hWx i)).op (a i) * b i = 1)
    (hcov : ∀ y ∈ f ⁻¹ᵁ V, ∃ i ∈ T, y ∈ Wx i) {X : L} (hX : X ≠ 0)
    (hVg : ∀ i ∈ T, χ ((Y.residue _).hom (a i ⟨Y0, hη⟩)) * X ∈ V') {n : ℕ}
    {u : (rationalFunctionsPresheaf Y).obj (op (f ⁻¹ᵁ V))}
    (hu : u ∈ ((n : ℤ) • B).divisorialSubmodule (f ⁻¹ᵁ V)) :
    χ ((Y.residue _).hom (u ⟨Y0, hη⟩)) * X ^ n ∈ V' := by
  have hmemη : ∀ O : Y.Opens, ∀ x ∈ O, componentGenericPoint Y Y0 ∈ O := fun O x hx =>
    (genericPoint_mem_iff Y0 O).mpr ⟨x, hx, hY0 x⟩
  obtain ⟨i1, hi1T, hηi1⟩ := hcov _ hη
  have he1 : χ ((Y.residue _).hom (a i1 ⟨Y0, hη⟩)) ≠ 0 := by
    refine (map_ne_zero χ).mpr fun he => ?_
    have h1 : a i1 ⟨Y0, hη⟩ * b i1 ⟨Y0, hηi1⟩ = 1 := congrFun (hab i1) ⟨Y0, hηi1⟩
    rw [hι (he.trans (map_zero _).symm), zero_mul] at h1
    exact zero_ne_one h1
  obtain ⟨i0, hi0T, hg0, hratio⟩ := exists_div_mem_valuationSubring V'
    (fun i => χ ((Y.residue _).hom (a i ⟨Y0, hη⟩)) * X) ⟨i1, hi1T, mul_ne_zero he1 hX⟩
  obtain ⟨x, _, hxU, hstx⟩ := exists_center_of_valuationSubring f hV _ hη (V'.comap χ) hVR
  obtain ⟨i, hiT, hxi⟩ := hcov x hxU
  obtain ⟨r, hr⟩ := exists_stalk_mul_pow_eq (hWx i) hη (hmemη _ x hxi) hxi (hY0 x) (hb i)
    (hab i) n hu
  have hdec : χ ((Y.residue _).hom (u ⟨Y0, hη⟩)) * X ^ n =
      χ ((Y.residue _).hom ((stalkToRationalFunctions Y (hY0 x)).hom r)) *
        (χ ((Y.residue _).hom (a i ⟨Y0, hη⟩)) * X /
          (χ ((Y.residue _).hom (a i0 ⟨Y0, hη⟩)) * X)) ^ n *
        (χ ((Y.residue _).hom (a i0 ⟨Y0, hη⟩)) * X) ^ n := by
    rw [mul_assoc, ← mul_pow, div_mul_cancel₀ _ hg0, ← hr]
    simp only [map_mul, map_pow]
    ring
  rw [hdec]
  exact mul_mem (mul_mem (hstx r) (pow_mem (hratio i hiT) n)) (pow_mem (hVg i0 hi0T) n)

/-- **Finite generation of the floor algebra from local generators.** Let `f : Y ⟶ Z` be proper
with `Y` integral, normal and locally Noetherian, `V ⊆ Z` an affine open with `Γ(Z, V)` Nagata,
and `D` a `ℚ`-divisor with `qD = B` integral for some `q > 0`. If every point of `f⁻¹V` has a
neighbourhood on which some section of `𝒪_Y(B)` over `f⁻¹V` is invertible, then the floor
algebra `⨁_m H⁰(f⁻¹V, 𝒪_Y(⌊mD⌋)) tᵐ` is generated over `Γ(Z, V)` by finitely many elements. -/
private theorem fg_floorAlgebra [IsIntegral Y] {Z : Scheme.{u}} (f : Y ⟶ Z) [IsProper f]
    {V : Z.Opens} (hV : IsAffineOpen V) (hA : IsNagataRing Γ(Z, V)) (D : QDivisor Y) {q : ℕ}
    (hq : 0 < q) (B : Divisor Y) (hB : ∀ P, (B.coeff P : ℚ) = q * D.coeff P)
    (hgen : ∀ x ∈ f ⁻¹ᵁ V, ∃ a ∈ B.divisorialSubmodule (f ⁻¹ᵁ V), ∃ (W : Y.Opens)
      (hW : W ≤ f ⁻¹ᵁ V), x ∈ W ∧ ∃ b ∈ (-B).divisorialSubmodule W,
        (rationalFunctionsPresheaf Y).map (homOfLE hW).op a * b = 1) :
    ∃ G : Finset (Polynomial ((rationalFunctionsPresheaf Y).obj (op (f ⁻¹ᵁ V)))),
      (∀ p ∈ G, p ∈ floorAlgebra D (f ⁻¹ᵁ V)) ∧
      ∀ p ∈ floorAlgebra D (f ⁻¹ᵁ V), p ∈ Subring.closure (Set.range (fun a : Γ(Z, V) =>
          Polynomial.C (algebraMap Γ(Y, f ⁻¹ᵁ V) _ (f.app V a))) ∪ ↑G) := by
  classical
  set W := f ⁻¹ᵁ V
  set K := (rationalFunctionsPresheaf Y).obj (op W)
  set R := floorAlgebra D W
  by_cases hne : (W : Set Y).Nonempty
  swap
  · have : Subsingleton (ToType K) :=
      ⟨fun φ ψ => funext fun Z => (hne ⟨_, Z.2⟩).elim⟩
    refine ⟨∅, by simp, fun p _ => ?_⟩
    rw [Subsingleton.elim p 0]
    exact Subring.zero_mem _
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨Y0, -⟩ := MMP.Mori.exists_mem_irreducibleComponents x0
  have hY0univ : ∀ x : Y, x ∈ Y0.1 := fun x => by
    rw [(irreducibleComponents_eq_singleton (X := Y)).le Y0.2]; trivial
  have hall : ∀ Y' : irreducibleComponents Y, Y' = Y0 := fun Y' =>
    Subtype.ext (((irreducibleComponents_eq_singleton (X := Y)).le Y'.2).trans
      ((irreducibleComponents_eq_singleton (X := Y)).le Y0.2).symm)
  set η := componentGenericPoint Y Y0
  have hη : η ∈ W := (genericPoint_mem_iff Y0 W).mpr ⟨x0, hx0, hY0univ x0⟩
  have hfield := RationalFunctions.isField_stalk Y Y0
  have hι : Function.Injective (Y.residue η).hom := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have h1 : c ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.residue_eq_zero_iff c).mp hc
    rwa [IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield] at h1
  let κ := Y.residueField η
  let evK : K →+* κ :=
    (Y.residue η).hom.comp (Pi.evalRingHom (fun Y' : {Y' : irreducibleComponents Y //
      componentGenericPoint Y Y' ∈ W} => Y.presheaf.stalk (componentGenericPoint Y Y'.1))
      ⟨Y0, hη⟩)
  have hevK : Function.Injective evK := by
    intro c d h
    funext Y'
    obtain rfl : Y' = ⟨Y0, hη⟩ := Subtype.ext (hall Y'.1)
    exact hι h
  let L := FractionRing (Polynomial κ)
  let Ψ0 : R →+* L :=
    (algebraMap (Polynomial κ) L).comp ((Polynomial.mapRingHom evK).comp R.subtype)
  have hΨ0 : Function.Injective Ψ0 := (IsFractionRing.injective (Polynomial κ) L).comp
    ((Polynomial.map_injective _ hevK).comp Subtype.val_injective)
  let Xb := algebraMap (Polynomial κ) L Polynomial.X
  have hXb : Xb ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial κ) L)).mpr Polynomial.X_ne_zero
  have hΨmono : ∀ (m : ℕ) (s : K) (hs : Polynomial.monomial m s ∈ R),
      Ψ0 ⟨Polynomial.monomial m s, hs⟩ = algebraMap κ L (evK s) * Xb ^ m := by
    intro m s hs
    change algebraMap (Polynomial κ) L (Polynomial.map evK (Polynomial.monomial m s)) = _
    rw [Polynomial.map_monomial, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
      IsScalarTower.algebraMap_apply κ (Polynomial κ) L]
    rfl
  -- the structure map `Γ(Z, V) → R`
  have hbaseMem : ∀ a : Γ(Z, V),
      Polynomial.C (algebraMap Γ(Y, W) K (f.app V a)) ∈ R := fun a => by
    rw [← Polynomial.monomial_zero_left]
    refine monomial_mem_floorAlgebra D W ?_
    rw [roundDown_natCast_zero_smul]
    exact Divisor.isDivisorialSection_algebraMap le_rfl _
  let ιR : Γ(Z, V) →+* R :=
    (Polynomial.C.comp ((algebraMap Γ(Y, W) K).comp (f.app V).hom)).codRestrict R hbaseMem
  let : Algebra Γ(Z, V) R := ιR.toAlgebra
  let ρ : Γ(Z, V) →+* κ := (f.app V ≫ Y.presheaf.germ W η hη ≫ Y.residue η).hom
  have hΨbase : ∀ r, Ψ0 (algebraMap Γ(Z, V) R r) = algebraMap κ L (ρ r) := by
    intro r
    change algebraMap (Polynomial κ) L (Polynomial.map evK
      (Polynomial.C (algebraMap Γ(Y, W) K (f.app V r)))) = _
    rw [Polynomial.map_C, IsScalarTower.algebraMap_apply κ (Polynomial κ) L,
      Polynomial.algebraMap_eq]
    rfl
  let : Algebra Γ(Z, V) κ := ρ.toAlgebra
  have hRL : ∀ r, algebraMap Γ(Z, V) L r = algebraMap κ L (ρ r) := fun r =>
    IsScalarTower.algebraMap_apply Γ(Z, V) κ L r
  have : Algebra.EssFiniteType Γ(Z, V) κ := essFiniteType_residueField_of_mem f hV η hη
  have : Algebra.EssFiniteType κ L := by
    have : Algebra.EssFiniteType (Polynomial κ) L :=
      Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors (Polynomial κ))
    exact Algebra.EssFiniteType.comp κ (Polynomial κ) L
  have : Algebra.EssFiniteType Γ(Z, V) L := Algebra.EssFiniteType.comp Γ(Z, V) κ L
  let Ψ : R →ₐ[Γ(Z, V)] L :=
    { Ψ0 with commutes' := fun r => (hΨbase r).trans (hRL r).symm }
  -- finitely many local generators
  choose a ha Wx hWx hxW b hb hab using hgen
  have hcomp : IsCompact (W : Set Y) :=
    QuasiCompact.isCompact_preimage (f := f) _ V.isOpen hV.isCompact
  obtain ⟨T, hT⟩ := hcomp.elim_finite_subcover
    (fun x : W => ((Wx x.1 x.2 : Y.Opens) : Set Y)) (fun x => (Wx x.1 x.2).isOpen)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxW x hx⟩)
  have hcov : ∀ y ∈ W, ∃ t ∈ T, y ∈ Wx t.1 t.2 := by
    intro y hy
    obtain ⟨t, ht, hyt⟩ := Set.mem_iUnion₂.mp (hT hy)
    exact ⟨t, ht, hyt⟩
  have hmono1 : ∀ t : W, Polynomial.monomial q (a t.1 t.2) ∈ R := fun t => by
    have := monomial_natCast_mul_mem_floorAlgebra D B hB (n := 1) (u := a t.1 t.2)
      (by rw [Nat.cast_one, one_smul]; exact ha t.1 t.2)
    rwa [mul_one] at this
  let gen : W → R := fun t => ⟨Polynomial.monomial q (a t.1 t.2), hmono1 t⟩
  let g : Finset R := T.image gen
  set C := Algebra.adjoin Γ(Z, V) (g : Set R)
  let : Algebra C L := (Ψ0.comp (algebraMap C R)).toAlgebra
  let ΨC : R →ₐ[C] L := { Ψ0 with commutes' := fun _ => rfl }
  have hΨgen : ∀ t, Ψ0 (gen t) = algebraMap κ L (evK (a t.1 t.2)) * Xb ^ q := fun t =>
    hΨmono q _ (hmono1 t)
  have hhom : ∀ (n : ℕ) (u : K) (hu : u ∈ ((n : ℤ) • B).divisorialSubmodule W),
      _root_.IsIntegral C
        (⟨Polynomial.monomial (q * n) u, monomial_natCast_mul_mem_floorAlgebra D B hB hu⟩ : R) := by
    intro n u hu
    rw [← isIntegral_algHom_iff ΨC hΨ0]
    refine isIntegralElem_of_forall_valuationSubring (algebraMap C L) fun V' hV' => ?_
    have hVC : ∀ c : C, Ψ0 c ∈ V' := fun c => hV' ⟨c, rfl⟩
    change Ψ0 ⟨Polynomial.monomial (q * n) u, monomial_natCast_mul_mem_floorAlgebra D B hB hu⟩ ∈ V'
    rw [hΨmono, pow_mul]
    refine residue_mul_pow_mem_valuationSubring f hV hY0univ hη (algebraMap κ L) V' hι
      (fun r => ?_) (a := fun t : W => a t.1 t.2) (fun t => hWx t.1 t.2) (fun t => hb t.1 t.2)
      (fun t => hab t.1 t.2) hcov (pow_ne_zero _ hXb) (fun t ht => ?_) hu
    · have h := hVC (algebraMap Γ(Z, V) C r)
      change Ψ0 (algebraMap Γ(Z, V) R r) ∈ V' at h
      exact (congrArg (· ∈ V') (hΨbase r)).mp h
    · have h : Ψ0 (gen t) ∈ V' := hVC ⟨_, Algebra.subset_adjoin
        (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ ht))⟩
      rwa [hΨgen] at h
  have := finiteType_of_isIntegral_adjoin hA Ψ hΨ0 g (isIntegral_floorAlgebra D hq B hB hhom)
  exact exists_finset_closure_of_finiteType R

end Main

/-! #### Local generators from local equations -/

section Generators

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]

/-- Off the support of `div ψ + B`, a regular function times `ψ⁻¹` is a section of `𝒪_Y(-B)`. -/
private theorem map_germ_mul_inv_mem_divisorialSubmodule [CompactSpace Y] {B : Divisor Y}
    (ψ : (RationalFunctions Y)ˣ) {O W : Y.Opens} (hWO : W ≤ O)
    (hW : ∀ y ∈ W, y ∉ ((principalDivisor ψ + B).supp : Set Y)) (c : Γ(Y, O)) :
    (rationalFunctionsPresheaf Y).map (homOfLE hWO).op
      (fun Y' => Y.presheaf.germ O _ Y'.2 c *
        ((ψ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Y'.1 :
          (rationalFunctionsPresheaf Y).obj (op O)) ∈ (-B).divisorialSubmodule W := by
  intro E hE
  have hcoeff : (principalDivisor ψ + B).coeff E = 0 := by
    by_contra hne
    obtain ⟨y, hyE, hyW⟩ := hE
    exact hW y hyW (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hne, hyE⟩)
  have hE0 : (principalDivisor ψ + B).coeff E = E.ord ψ + B.coeff E := by
    simp [DivisorWithCoeffs.coeff_add]
  rw [hE0] at hcoeff
  have h1 := Divisor.isDivisorialSection_algebraMap (D := 0) le_rfl c E
    (hE.mono (Set.inter_subset_inter_right _ hWO))
  have h2' : E.OrdGE (B.coeff E) (((ψ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y)
      E.component) := by
    refine Or.inr ?_
    rw [E.valuation_component, WithZero.exp_le_exp, PrimeDivisor.ord_inv]
    linarith
  have := h1.mul h2'
  convert this using 1
  · simp
  · rfl

/-- **A local generator extends over `f⁻¹V`.** Let `V ⊆ Z` be an affine open and `x ∈ f⁻¹V`.
If a unit `ψ` of `K(Y)` has `B + div ψ` effective on `f⁻¹U'` for an open `U' ∋ f(x)` and zero
along every prime divisor through `x`, then some section `a` of `𝒪_Y(B)` over `f⁻¹V` is
invertible, with inverse in `𝒪_Y(-B)`, on a neighbourhood of `x`. -/
private theorem exists_generator_of_isLocalEquation [CompactSpace Y] {Z : Scheme.{u}}
    (f : Y ⟶ Z) {V : Z.Opens} (hV : IsAffineOpen V) (B : Divisor Y) {x : Y}
    (hx : x ∈ f ⁻¹ᵁ V) {U' : Z.Opens} (hxU' : f x ∈ U') (ψ : (RationalFunctions Y)ˣ)
    (h1 : ∀ P : MMP.Mori.PrimeDivisor Y, (P.support ∩ f ⁻¹ᵁ U').Nonempty →
      0 ≤ B.coeff P + P.ord ψ)
    (h2 : ∀ P : MMP.Mori.PrimeDivisor Y, x ∈ P.support → B.coeff P + P.ord ψ = 0) :
    ∃ a ∈ B.divisorialSubmodule (f ⁻¹ᵁ V), ∃ (W : Y.Opens) (hW : W ≤ f ⁻¹ᵁ V), x ∈ W ∧
      ∃ b ∈ (-B).divisorialSubmodule W,
        (rationalFunctionsPresheaf Y).map (homOfLE hW).op a * b = 1 := by
  classical
  obtain ⟨g, hgle, hxg⟩ := hV.exists_basicOpen_le (V := V ⊓ U') ⟨f x, hx, hxU'⟩ hx
  set s : Γ(Y, f ⁻¹ᵁ V) := f.app V g
  set O := Y.basicOpen s
  have hOW : O ≤ f ⁻¹ᵁ V := Y.basicOpen_le s
  have hOU' : O ≤ f ⁻¹ᵁ U' := by
    intro y hy
    have : y ∈ f ⁻¹ᵁ Z.basicOpen g := by rw [Scheme.preimage_basicOpen]; exact hy
    exact (hgle this).2
  have hxO : x ∈ O := by
    have : x ∈ f ⁻¹ᵁ Z.basicOpen g := hxg
    rwa [Scheme.preimage_basicOpen] at this
  let ψK : Γ(B.divisorialSheaf, O) :=
    ⟨fun Y' => (ψ : RationalFunctions Y) Y'.1, MMP.Fourfold.isDivisorialSection_of_unit ψ
      fun P hP => h1 P (hP.mono (Set.inter_subset_inter_right _ hOU'))⟩
  have hloc := Divisor.isLocalizedModule_divisorialSheaf_restrictₗ B s
  obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, ha⟩ := IsLocalizedModule.surj (Submonoid.powers s)
    (Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictₗ B.divisorialSheaf
      (Y.basicOpen_le s)) ψK
  simp only [Submonoid.smul_def] at ha
  set v : Γ(Y, O) := Y.presheaf.map (homOfLE hOW).op s
  have hvu : IsUnit v := RingedSpace.isUnit_res_basicOpen Y.toRingedSpace s
  have hkey : ∀ Y' : {Y' : irreducibleComponents Y // componentGenericPoint Y Y' ∈ O},
      a.1 ⟨Y'.1, hOW Y'.2⟩ = Y.presheaf.germ O _ Y'.2 (v ^ m) * (ψ : RationalFunctions Y) Y'.1 := by
    intro Y'
    have h := congrFun (congrArg (fun z : Γ(B.divisorialSheaf, O) =>
      (show B.divisorialSubmodule O from z).1) ha) Y'
    refine h.symm.trans ?_
    change Y.presheaf.germ O _ Y'.2 (Y.presheaf.map (homOfLE hOW).op (s ^ m)) *
      (ψ : RationalFunctions Y) Y'.1 = _
    rw [map_pow]
  set w : Γ(Y, O) := ((hvu.unit⁻¹ : (Γ(Y, O))ˣ) : Γ(Y, O))
  have hvw : v * w = 1 := hvu.mul_val_inv
  let E0 : Divisor Y := principalDivisor ψ + B
  have hE0 : ∀ E, E0.coeff E = E.ord ψ + B.coeff E := fun E => by
    simp [E0, DivisorWithCoeffs.coeff_add]
  let W : Y.Opens := O ⊓ ⟨(E0.supp : Set Y)ᶜ, E0.isClosed_supp.isOpen_compl⟩
  have hWO : W ≤ O := inf_le_left
  have hWV : W ≤ f ⁻¹ᵁ V := hWO.trans hOW
  have hxW : x ∈ W := by
    refine ⟨hxO, fun h => ?_⟩
    obtain ⟨E, hne, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
    exact hne ((hE0 E).trans ((add_comm _ _).trans (h2 E hxE)))
  let β : (rationalFunctionsPresheaf Y).obj (op O) :=
    fun Y' => Y.presheaf.germ O _ Y'.2 (w ^ m) * ((ψ⁻¹ : (RationalFunctions Y)ˣ) :
      RationalFunctions Y) Y'.1
  refine ⟨a.1, a.2, W, hWV, hxW, (rationalFunctionsPresheaf Y).map (homOfLE hWO).op β, ?_, ?_⟩
  · exact map_germ_mul_inv_mem_divisorialSubmodule ψ hWO (fun y hy => hy.2) (w ^ m)
  · funext Y'
    have hY : componentGenericPoint Y Y'.1 ∈ O := hWO Y'.2
    have hk := hkey ⟨Y'.1, hY⟩
    change a.1 ⟨Y'.1, hWV Y'.2⟩ * (Y.presheaf.germ O _ hY (w ^ m) *
      ((ψ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Y'.1) = 1
    rw [hk]
    calc _ = Y.presheaf.germ O _ hY ((v * w) ^ m) *
          (((ψ * ψ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Y'.1) := by
            rw [mul_pow, map_mul, Units.val_mul, Pi.mul_apply]; ring
      _ = 1 := by rw [hvw, one_pow, map_one, mul_inv_cancel, Units.val_one, Pi.one_apply,
          one_mul]

end Generators

/-! #### Orders of rational functions on an integral scheme -/

section Orders

variable {Y : Scheme.{u}} [IsIntegral Y]

private theorem specializes_genericPoint (Z : irreducibleComponents Y) :
    componentGenericPoint Y Z ⤳ genericPoint Y :=
  (Inseparable.of_eq (componentGenericPoint_eq_genericPoint Z)).specializes

/-- A rational function `φ ∈ K(Y)`, read in every factor of `K(Y) = ∏_Z 𝒪_{Y,η_Z}`. -/
private noncomputable def toRationalFunctions : Y.functionField →+* RationalFunctions Y :=
  Pi.ringHom fun Z => (Y.presheaf.stalkSpecializes (specializes_genericPoint Z)).hom

private theorem stalkSpecializes_toRationalFunctions (Z : irreducibleComponents Y)
    (φ : Y.functionField) :
    (Y.presheaf.stalkSpecializes (genericPoint_specializes (componentGenericPoint Y Z))).hom
      (toRationalFunctions φ Z) = φ := by
  change (Y.presheaf.stalkSpecializes _).hom ((Y.presheaf.stalkSpecializes _).hom φ) = φ
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

variable [IsLocallyNoetherian Y] [IsNormal Y]

/-- `v_P` on the factor `𝒪_{Y,η}` of `K(Y)` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation (P : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y P.component)) :
    P.valuation s = (P.divisorialValuation
      ((Y.presheaf.stalkSpecializes
        (genericPoint_specializes (componentGenericPoint Y P.component))).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

/-- The order along `P` of the unit of `K(Y)` defined by `φ ≠ 0` is `ord_{η_P}(φ)`. -/
private theorem ord_toRationalFunctions (P : MMP.Mori.PrimeDivisor Y) {φ : Y.functionField}
    (hφ : φ ≠ 0) (ψ : (RationalFunctions Y)ˣ) (hψ : (ψ : RationalFunctions Y) =
      toRationalFunctions φ) : P.ord ψ = Scheme.ord φ P.genericPoint := by
  have h2 := valuation_eq_inv_divisorialValuation P ((ψ : RationalFunctions Y) P.component)
  rw [hψ, stalkSpecializes_toRationalFunctions, ← hψ, P.valuation_component,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hφ, ← WithZero.exp_neg,
    neg_neg] at h2
  exact WithZero.exp_injective h2

/-- A nonzero `φ ∈ K(Y)` gives a unit of `K(Y)` whose order along every `P` is `ord_{η_P}(φ)`. -/
private theorem exists_unit_ord_eq {φ : Y.functionField} (hφ : φ ≠ 0) :
    ∃ ψ : (RationalFunctions Y)ˣ, ∀ P : MMP.Mori.PrimeDivisor Y,
      P.ord ψ = Scheme.ord φ P.genericPoint :=
  ⟨⟨toRationalFunctions φ, toRationalFunctions φ⁻¹,
    by rw [← map_mul, mul_inv_cancel₀ hφ, map_one],
    by rw [← map_mul, inv_mul_cancel₀ hφ, map_one]⟩, fun P => ord_toRationalFunctions P hφ _ rfl⟩

end Orders

/-! #### Relatively free Cartier divisors -/

section RelativelyFree

/-- The Weil divisor of `-E` is minus the Weil divisor of `E`. -/
private theorem isWeilDivisorOfCartier_neg {X : Scheme.{u}} [IsLocallyNoetherian X]
    {E : X.CartierDivisor} {B : Divisor X}
    (hEB : MMP.Intersection.IsWeilDivisorOfCartier E B) :
    MMP.Intersection.IsWeilDivisorOfCartier (-E) (-B) := fun P => by
  have h := MMP.Intersection.isOrderAlong_primeDivisorOrder (-E) P
  rwa [map_neg, (hEB P).primeDivisorOrder_eq, ← DivisorWithCoeffs.coeff_neg] at h

/-- `ord φ⁻¹ = -ord φ` for a nonzero rational function `φ` on an integral scheme. -/
private theorem ord_inv_eq_neg {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {φ : X.functionField} (hφ : φ ≠ 0) (y : X) : Scheme.ord φ⁻¹ y = -Scheme.ord φ y := by
  have h := Scheme.ord_mul (x := y) hφ (inv_ne_zero hφ)
  rw [mul_inv_cancel₀ hφ, Scheme.ord_one] at h
  omega

/-- If `σ = r g⁻¹` with `r` a unit and `g` a local equation of `E` on `U`, an inverse of `σ` is a
section of `𝒪_X(-E)` over `U`. -/
private theorem mem_lineBundleSections_neg_of_mul_eq_one {X : Scheme.{u}} {E : X.CartierDivisor}
    {U : X.Opens} {g : (X.totalQuotientSheaf.obj.obj (op U))ˣ}
    (hg : MMP.Intersection.IsLocalEquationOn E U g) {r : Γ(X, U)} (hr : IsUnit r)
    {σ τ : X.totalQuotientSheaf.obj.obj (op U)}
    (hσ : σ = MMP.Intersection.toTotalQuotient U r * ((g⁻¹ : _ˣ) : _)) (hτσ : τ * σ = 1) :
    τ ∈ MMP.Intersection.lineBundleSections (-E) U := by
  refine (MMP.Intersection.mem_lineBundleSections_iff_of_isLocalEquationOn' hg.inv τ).2
    ⟨((hr.unit⁻¹ : _ˣ) : Γ(X, U)), ?_⟩
  rw [inv_inv]
  have h1 : MMP.Intersection.toTotalQuotient U ((hr.unit⁻¹ : _ˣ) : Γ(X, U)) *
      MMP.Intersection.toTotalQuotient U r = 1 := by
    rw [← map_mul, hr.val_inv_mul, map_one]
  calc _ = (MMP.Intersection.toTotalQuotient U ((hr.unit⁻¹ : _ˣ) : Γ(X, U)) * (g : _)) *
        (σ * τ) := by rw [mul_comm σ τ, hτσ, mul_one]
    _ = τ * ((MMP.Intersection.toTotalQuotient U ((hr.unit⁻¹ : _ˣ) : Γ(X, U)) *
        MMP.Intersection.toTotalQuotient U r) * ((g : _) * ((g⁻¹ : _ˣ) : _))) := by
          rw [hσ]; ring
    _ = τ := by rw [h1, Units.mul_inv, mul_one, mul_one]

/-- **Local equations of a relatively free Cartier divisor.** Let `E` be a Cartier divisor with
Weil divisor `B` on a normal integral locally Noetherian scheme, `f`-free for `f : Y ⟶ Z`. Every
`x ∈ Y` has an open `U' ∋ f(x)` and a unit `ψ` of `K(Y)` with `B + div ψ` effective on `f⁻¹U'`
and zero along every prime divisor through `x`: `ψ` is a section of `𝒪_Y(E)` over `f⁻¹U'`
generating it at `x`. -/
private theorem exists_isLocalEquation_of_isRelativelyFreeCartier {Y Z : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ Z) {E : Y.CartierDivisor}
    {B : Divisor Y} (hEB : MMP.Intersection.IsWeilDivisorOfCartier E B)
    (hfree : IsRelativelyFreeCartier f E) (x : Y) :
    ∃ (U' : Z.Opens) (_ : f x ∈ U') (ψ : (RationalFunctions Y)ˣ),
      (∀ P : MMP.Mori.PrimeDivisor Y, (P.support ∩ f ⁻¹ᵁ U').Nonempty →
        0 ≤ B.coeff P + P.ord ψ) ∧
      ∀ P : MMP.Mori.PrimeDivisor Y, x ∈ P.support → B.coeff P + P.ord ψ = 0 := by
  classical
  set L := MMP.CartierDivisor.sheaf E
  set adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have : Epi ((adj.homEquiv ((Scheme.Modules.pushforward f).obj L) L).symm
      (𝟙 ((Scheme.Modules.pushforward f).obj L))) := by
    rw [Stacks.Tag01VMVeryAmple.homEquiv_symm_id]
    exact hfree
  obtain ⟨V', -, bsec, hxb⟩ := Stacks.Tag01VMVeryAmple.exists_mem_nonvanishingLocusOn_of_epi_adjoint
    f (𝟙 ((Scheme.Modules.pushforward f).obj L)) x
  set W' := f ⁻¹ᵁ V' with hW'
  let b : Γ(L, W') := bsec
  have hxb' : x ∈ Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn L W' b := hxb
  obtain ⟨hxW', hgerm⟩ := hxb'
  set σ := MMP.CartierDivisorSheaf.sectionVal b
  -- a local equation of `E` at `x`, and `σ = r g⁻¹` with `r` a unit at `x`
  obtain ⟨U, hxU, g, hg⟩ := MMP.Intersection.exists_isLocalEquationOn E x
  set U1 := U ⊓ W'
  have hxU1 : x ∈ U1 := ⟨hxU, hxW'⟩
  have hg1 := MMP.Intersection.isLocalEquationOn_resUnit (homOfLE (inf_le_left : U1 ≤ U)) hg
  set g1 := MMP.Intersection.resUnit (homOfLE (inf_le_left : U1 ≤ U)) g
  set b1 : Γ(L, U1) := L.presheaf.map (homOfLE (inf_le_right : U1 ≤ W')).op b with hb1
  obtain ⟨r, hr⟩ := (MMP.Intersection.mem_lineBundleSections_iff_of_isLocalEquationOn' hg1
      (MMP.CartierDivisorSheaf.sectionVal b1)).1
    (MMP.CartierDivisor.sectionVal_mem_lineBundleSections b1)
  have hb1r : b1 = r • MMP.CartierDivisor.invSection hg1 :=
    MMP.CartierDivisorSheaf.sectionVal_injective hr.symm
  have hru : IsUnit (Y.presheaf.germ U1 x hxU1 r) := by
    by_contra hnu
    apply hgerm
    have h1 : L.presheaf.germ W' x hxW' b = L.presheaf.germ U1 x hxU1 b1 := by
      rw [hb1]
      exact (TopCat.Presheaf.germ_res_apply (C := Ab.{u}) L.presheaf
        (homOfLE (inf_le_right : U1 ≤ W')) x hxU1 b).symm
    rw [h1, hb1r, Stacks.ModuleStalk.germ_smul]
    exact Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal _).mpr hnu) Submodule.mem_top
  -- on `U2 = D(r)` the section `σ` is a unit of `𝓜_Y`
  set U2 := Y.basicOpen r
  have hU21 : U2 ≤ U1 := Y.basicOpen_le r
  have hU2W : U2 ≤ W' := hU21.trans inf_le_right
  have hxU2 : x ∈ U2 := (Scheme.mem_basicOpen Y r x hxU1).mpr hru
  set r2 : Γ(Y, U2) := Y.presheaf.map (homOfLE hU21).op r
  have hr2 : IsUnit r2 := RingedSpace.isUnit_res_basicOpen Y.toRingedSpace r
  have hg2 := MMP.Intersection.isLocalEquationOn_resUnit (homOfLE hU21) hg1
  set g2 := MMP.Intersection.resUnit (homOfLE hU21) g1
  set σ2 := Y.totalQuotientSheaf.obj.map (homOfLE hU2W).op σ
  have hσ2 : σ2 = MMP.Intersection.toTotalQuotient U2 r2 * ((g2⁻¹ : _ˣ) : _) := by
    have h := congrArg (Y.totalQuotientSheaf.obj.map (homOfLE hU21).op) hr
    rw [map_mul, ← MMP.Intersection.toTotalQuotient_res] at h
    refine Eq.trans ?_ h.symm
    erw [hb1, MMP.CartierDivisorSheaf.sectionVal_map, MMP.Intersection.totalQuotient_map_map]
    rfl
  have hσ2u : IsUnit σ2 := by
    rw [hσ2]
    exact (hr2.map (MMP.Intersection.toTotalQuotient U2)).mul (Units.isUnit _)
  -- the rational function `φ` of `σ`
  set ξ := genericPoint Y
  have hξ : ∀ (O : Y.Opens) (y : Y), y ∈ O → ξ ∈ O := fun O y hy =>
    ((genericPoint_spec Y).specializes trivial : ξ ⤳ y).mem_open O.isOpen hy
  have hξW' : ξ ∈ W' := hξ W' x hxW'
  set φ := totalQuotientStalkToFunctionField ξ (Y.totalQuotientSheaf.presheaf.germ W' ξ hξW' σ)
  have hσgerm : ∀ (y : Y) (hy : y ∈ W'), totalQuotientStalkToFunctionField y
      (Y.totalQuotientSheaf.presheaf.germ W' y hy σ) = φ := by
    intro y hy
    have hsp : ξ ⤳ y := (genericPoint_spec Y).specializes trivial
    rw [← MMP.Intersection.totalQuotientStalkToFunctionField_stalkSpecializes hsp,
      TopCat.Presheaf.germ_stalkSpecializes_apply]
  have hσ2germ : ∀ (y : Y) (hy : y ∈ U2), totalQuotientStalkToFunctionField y
      (Y.totalQuotientSheaf.presheaf.germ U2 y hy σ2) = φ := by
    intro y hy
    rw [TopCat.Presheaf.germ_res_apply]
    exact hσgerm y (hU2W hy)
  have hφ : φ ≠ 0 := by
    rw [← hσ2germ x hxU2]
    exact ((hσ2u.map (Y.totalQuotientSheaf.presheaf.germ U2 x hxU2).hom).map
      (totalQuotientStalkToFunctionField x).hom).ne_zero
  -- `B + div φ ≥ 0` on `W'`
  have : Nonempty W' := ⟨⟨x, hxW'⟩⟩
  have hge := (MMP.Intersection.mem_lineBundleSections_iff_forall_zero_le_ord_add hEB W' hφ σ
    hσgerm).1 (MMP.CartierDivisor.sectionVal_mem_lineBundleSections b)
  -- `-B + div φ⁻¹ ≥ 0` on `U2`, as `σ⁻¹` is a section of `𝒪_Y(-E)` there
  set τ : Y.totalQuotientSheaf.obj.obj (op U2) := (hσ2u.unit⁻¹).val
  have hτσ : τ * σ2 = 1 := hσ2u.val_inv_mul
  have hτgerm : ∀ (y : Y) (hy : y ∈ U2), totalQuotientStalkToFunctionField y
      (Y.totalQuotientSheaf.presheaf.germ U2 y hy τ) = φ⁻¹ := by
    intro y hy
    have h := congrArg (fun t => totalQuotientStalkToFunctionField y
      (Y.totalQuotientSheaf.presheaf.germ U2 y hy t)) hτσ
    simp only [map_mul, map_one, hσ2germ y hy] at h
    exact eq_inv_of_mul_eq_one_left h
  have : Nonempty U2 := ⟨⟨x, hxU2⟩⟩
  have hle := (MMP.Intersection.mem_lineBundleSections_iff_forall_zero_le_ord_add
    (isWeilDivisorOfCartier_neg hEB) U2
    (inv_ne_zero hφ) τ hτgerm).1 (mem_lineBundleSections_neg_of_mul_eq_one hg2 hr2 hσ2 hτσ)
  obtain ⟨ψ, hψ⟩ := exists_unit_ord_eq hφ
  refine ⟨V', hxW', ψ, fun P hP => ?_, fun P hxP => ?_⟩
  · rw [hψ, add_comm]
    exact hge P hP
  · have h1 := hge P ⟨x, hxP, hxW'⟩
    have h2 := hle P ⟨x, hxP, hxU2⟩
    rw [ord_inv_eq_neg hφ, DivisorWithCoeffs.coeff_neg] at h2
    rw [hψ]
    omega

end RelativelyFree

/-! #### The Weil divisor of a Cartier divisor -/

section Weil

open MMP.Intersection

/-- On a locally Noetherian scheme, a point of coheight zero lies in the support of no Cartier
divisor. -/
private theorem notMem_cartierSupport_of_coheight_eq_zero {X : Scheme.{u}}
    [IsLocallyNoetherian X] (A : X.CartierDivisor) {x : X} (hx : Order.coheight x = 0) :
    x ∉ cartierSupport A := by
  have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le (by simp [hx])
  have : IsArtinianRing (X.presheaf.stalk x) := isArtinianRing_iff_krullDimLE_zero.mpr this
  exact notMem_cartierSupport_of_isArtinianRing A x

/-- Every Cartier divisor on a Noetherian integral scheme has a Weil divisor. -/
private theorem exists_isWeilDivisorOfCartier {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [TopologicalSpace.NoetherianSpace X] (A : X.CartierDivisor) :
    ∃ w : Divisor X, IsWeilDivisorOfCartier A w := by
  have hfin := MMP.Mori.finite_setOf_genericPoint_mem (isClosed_cartierSupport A)
    (fun s hs h0 => notMem_cartierSupport_of_coheight_eq_zero A h0 hs)
  refine ⟨Finsupp.ofSupportFinite (fun P => primeDivisorOrder P A) (hfin.subset fun P hP => ?_),
    fun P => ?_⟩
  · by_contra h
    refine hP ((isOrderAlong_primeDivisorOrder A P).eq_zero_of_not_subset fun h' => h ?_)
    change (primeDivisorSubvariety P).genericPoint ∈ cartierSupport A
    exact genericPoint_mem_cartierSupport_iff.mpr h'
  · rw [MMP.Mori.DivisorWithCoeffs.coeff_apply, Finsupp.ofSupportFinite_coe]
    exact isOrderAlong_primeDivisorOrder A P

/-- The Weil divisor of the realization of `q • C`, for a `ℚ`-Cartier divisor `C` with Weil
`ℚ`-divisor `D`, is `q • D`. -/
private theorem coeff_eq_mul_of_isWeilDivisorOfCartier_realization {X : Scheme.{u}}
    [IsLocallyNoetherian X] {D : QDivisor X} {C : KCartierDivisor ℚ X}
    (hC : ∀ P : MMP.Mori.PrimeDivisor X,
      D.coeff P = C.sum fun E c => c * (primeDivisorOrder P E : ℚ)) {q : ℕ}
    (h : ∀ E, ∃ n : ℤ, ((q : ℚ) • C) E = n) {B : Divisor X}
    (hB : IsWeilDivisorOfCartier (KCartierDivisor.realization ((q : ℚ) • C) h) B)
    (P : MMP.Mori.PrimeDivisor X) : (B.coeff P : ℚ) = q * D.coeff P := by
  classical
  have hc : ∀ E, ((Classical.choose (h E) : ℤ) : ℚ) = ((q : ℚ) • C) E := fun E =>
    (Classical.choose_spec (h E)).symm
  rw [← (hB P).primeDivisorOrder_eq, KCartierDivisor.realization, Finsupp.sum, map_sum,
    Int.cast_sum, hC P, Finsupp.sum, Finset.mul_sum]
  have hz : ∀ E ∈ C.support, E ∉ ((q : ℚ) • C).support →
      (q : ℚ) * (C E * (primeDivisorOrder P E : ℚ)) = 0 := fun E _ hE => by
    rw [Finsupp.notMem_support_iff, Finsupp.smul_apply, smul_eq_mul] at hE
    rw [← mul_assoc, hE, zero_mul]
  rw [← Finset.sum_subset (Finsupp.support_smul (b := (q : ℚ)) (g := C)) hz]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [map_zsmul, smul_eq_mul, Int.cast_mul, hc, Finsupp.smul_apply, smul_eq_mul, mul_assoc]

end Weil

/-- **Finite generation of the floor-section algebra from local equations.** Let `f : Y ⟶ Z` be a
projective morphism from a normal variety over `k` to a `k`-scheme locally of finite type, `D` a
`ℚ`-divisor with `qD = B` integral for some `q > 0`, and suppose every `x ∈ Y` has an open
`U' ∋ f(x)` and a unit `ψ` of `K(Y)` with `B + div ψ` effective on `f⁻¹U'` and zero along every
prime divisor through `x`. Then over every affine open `V ⊆ Z` the floor algebra is generated
over `Γ(Z, V)` by finitely many elements. -/
private theorem fg_roundDownSections_of_exists_localEquation {k : Type u} [Field k]
    {Y Z : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType sZ]
    [IsLocallyNoetherian Y] [IsNormal Y] (hY : IsNormalVariety k sY)
    (f : Y ⟶ Z) (hf : IsProjective f) {D : QDivisor Y} {q : ℕ} (hq : 0 < q) (B : Divisor Y)
    (hB : ∀ P, (B.coeff P : ℚ) = q * D.coeff P)
    (hloc : ∀ x : Y, ∃ (U' : Z.Opens) (_ : f x ∈ U') (ψ : (RationalFunctions Y)ˣ),
      (∀ P : MMP.Mori.PrimeDivisor Y, (P.support ∩ f ⁻¹ᵁ U').Nonempty →
        0 ≤ B.coeff P + P.ord ψ) ∧
      ∀ P : MMP.Mori.PrimeDivisor Y, x ∈ P.support → B.coeff P + P.ord ψ = 0)
    (V : Z.Opens) (hV : IsAffineOpen V) :
    ∃ G : Finset (Polynomial ((rationalFunctionsPresheaf Y).obj (op (f ⁻¹ᵁ V)))),
      (∀ p ∈ G, ∀ m : ℕ,
        p.coeff m ∈ (DivisorWithCoeffs.roundDown ((m : ℚ) • D)).divisorialSubmodule (f ⁻¹ᵁ V)) ∧
      ∀ p : Polynomial ((rationalFunctionsPresheaf Y).obj (op (f ⁻¹ᵁ V))),
        (∀ m : ℕ,
          p.coeff m ∈ (DivisorWithCoeffs.roundDown ((m : ℚ) • D)).divisorialSubmodule (f ⁻¹ᵁ V)) →
        p ∈ Subring.closure (Set.range (fun a : Γ(Z, V) =>
          Polynomial.C (algebraMap Γ(Y, f ⁻¹ᵁ V) _ (f.app V a))) ∪ ↑G) := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : QuasiCompact sY := hY.1.toQuasiCompact
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsProper f := IsProjective.isProper hf
  exact fg_floorAlgebra f hV (isNagataRing_of_locallyOfFiniteType sZ hV) D hq B hB
    fun x hx => by
      obtain ⟨U', hxU', ψ, h1, h2⟩ := hloc x
      exact exists_generator_of_isLocalEquation f hV B hx hxU' ψ h1 h2

/-- **Finite generation of the floor-section algebra.** Let `f : Y ⟶ Z` be a projective morphism
of normal varieties over `k` and `D` a `ℚ`-divisor on `Y` semiample over `Z`. For every affine
open `V ⊆ Z` there are finitely many elements `G` of `⨁_{m ≥ 0} H⁰(f⁻¹V, 𝒪_Y(⌊mD⌋)) tᵐ ⊆
𝒦_Y(f⁻¹V)[t]` which, together with `Γ(Z, V)`, generate it as a ring. -/
@[mmp "lem_mmp_surface_rational_semiample_floor_algebra"]
theorem QDivisor.IsRelativelySemiample.fg_roundDownSections {k : Type u} [Field k]
    {Y Z : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [IsLocallyNoetherian Y] [IsNormal Y] (hY : IsNormalVariety k sY) (hZ : IsNormalVariety k sZ)
    (f : Y ⟶ Z) (hf : IsProjective f) (hfk : f ≫ sZ = sY)
    {D : QDivisor Y} (hD : QDivisor.IsRelativelySemiample f D) (V : Z.Opens) (hV : IsAffineOpen V) :
    ∃ G : Finset (Polynomial ((rationalFunctionsPresheaf Y).obj (op (f ⁻¹ᵁ V)))),
      (∀ p ∈ G, ∀ m : ℕ,
        p.coeff m ∈ (DivisorWithCoeffs.roundDown ((m : ℚ) • D)).divisorialSubmodule (f ⁻¹ᵁ V)) ∧
      ∀ p : Polynomial ((rationalFunctionsPresheaf Y).obj (op (f ⁻¹ᵁ V))),
        (∀ m : ℕ,
          p.coeff m ∈ (DivisorWithCoeffs.roundDown ((m : ℚ) • D)).divisorialSubmodule (f ⁻¹ᵁ V)) →
        p ∈ Subring.closure (Set.range (fun a : Γ(Z, V) =>
          Polynomial.C (algebraMap Γ(Y, f ⁻¹ᵁ V) _ (f.app V a))) ∪ ↑G) := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : QuasiCompact sY := hY.1.toQuasiCompact
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : TopologicalSpace.NoetherianSpace Y := by
    have : IsNoetherian Y := {}
    infer_instance
  obtain ⟨C, hC, q, hq, hint, hfree⟩ := hD
  obtain ⟨B, hEB⟩ := exists_isWeilDivisorOfCartier (KCartierDivisor.realization ((q : ℚ) • C) hint)
  have : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  refine fg_roundDownSections_of_exists_localEquation sY sZ hY f hf hq B
    (coeff_eq_mul_of_isWeilDivisorOfCartier_realization hC hint hEB)
    (exists_isLocalEquation_of_isRelativelyFreeCartier f hEB hfree) V hV

/-- **Finite generation of the floor-section algebra, Weil form, over a base of finite type.**
Let `f : Y ⟶ Z` be a projective morphism from a normal variety `Y` over `k` to a `k`-scheme `Z`
locally of finite type, and `D` a `ℚ`-divisor on `Y` such that `qD = B` for some `q > 0` and some
Cartier divisor `B` that is relatively free over `Z` (`MMP.Fourfold.IsRelativelyFreeDivisor`).
For every affine open `V ⊆ Z` there are finitely many elements `G` of
`⨁_{m ≥ 0} H⁰(f⁻¹V, 𝒪_Y(⌊mD⌋)) tᵐ ⊆ 𝒦_Y(f⁻¹V)[t]` which, together with `Γ(Z, V)`, generate it
as a ring. No normality of `Z` is assumed. -/
theorem fg_roundDownSections_of_isRelativelyFreeDivisor_of_locallyOfFiniteType {k : Type u}
    [Field k] {Y Z : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [LocallyOfFiniteType sZ] [IsLocallyNoetherian Y] [IsNormal Y] (hY : IsNormalVariety k sY)
    (f : Y ⟶ Z) (hf : IsProjective f) {D : QDivisor Y} {q : ℕ} (hq : 0 < q)
    (B : Divisor Y) (hB : ∀ P, (B.coeff P : ℚ) = q * D.coeff P) (hBc : B.IsCartier)
    (hfree : IsRelativelyFreeDivisor f B) (V : Z.Opens) (hV : IsAffineOpen V) :
    ∃ G : Finset (Polynomial ((rationalFunctionsPresheaf Y).obj (op (f ⁻¹ᵁ V)))),
      (∀ p ∈ G, ∀ m : ℕ,
        p.coeff m ∈ (DivisorWithCoeffs.roundDown ((m : ℚ) • D)).divisorialSubmodule (f ⁻¹ᵁ V)) ∧
      ∀ p : Polynomial ((rationalFunctionsPresheaf Y).obj (op (f ⁻¹ᵁ V))),
        (∀ m : ℕ,
          p.coeff m ∈ (DivisorWithCoeffs.roundDown ((m : ℚ) • D)).divisorialSubmodule (f ⁻¹ᵁ V)) →
        p ∈ Subring.closure (Set.range (fun a : Γ(Z, V) =>
          Polynomial.C (algebraMap Γ(Y, f ⁻¹ᵁ V) _ (f.app V a))) ∪ ↑G) :=
  have : IsIntegral Y := hY.1.toIsIntegral
  fg_roundDownSections_of_exists_localEquation sY sZ hY f hf hq B hB
    (exists_coeff_add_ord_eq_zero_of_isRelativelyFree f hBc hfree) V hV

/-- **Finite generation of the floor-section algebra, Weil form.** Let `f : Y ⟶ Z` be a projective
morphism of normal varieties over `k` and `D` a `ℚ`-divisor on `Y` such that `qD = B` for some
`q > 0` and some Cartier divisor `B` that is relatively free over `Z`
(`MMP.Fourfold.IsRelativelyFreeDivisor`). For every affine open `V ⊆ Z` there are finitely many
elements `G` of `⨁_{m ≥ 0} H⁰(f⁻¹V, 𝒪_Y(⌊mD⌋)) tᵐ ⊆ 𝒦_Y(f⁻¹V)[t]` which, together with
`Γ(Z, V)`, generate it as a ring. See
`MMP.Fourfold.fg_roundDownSections_of_isRelativelyFreeDivisor_of_locallyOfFiniteType` for a base
that is only locally of finite type over `k`. -/
theorem fg_roundDownSections_of_isRelativelyFreeDivisor {k : Type u} [Field k]
    {Y Z : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [IsLocallyNoetherian Y] [IsNormal Y] (hY : IsNormalVariety k sY) (hZ : IsNormalVariety k sZ)
    (f : Y ⟶ Z) (hf : IsProjective f) (hfk : f ≫ sZ = sY) {D : QDivisor Y} {q : ℕ} (hq : 0 < q)
    (B : Divisor Y) (hB : ∀ P, (B.coeff P : ℚ) = q * D.coeff P) (hBc : B.IsCartier)
    (hfree : IsRelativelyFreeDivisor f B) (V : Z.Opens) (hV : IsAffineOpen V) :
    ∃ G : Finset (Polynomial ((rationalFunctionsPresheaf Y).obj (op (f ⁻¹ᵁ V)))),
      (∀ p ∈ G, ∀ m : ℕ,
        p.coeff m ∈ (DivisorWithCoeffs.roundDown ((m : ℚ) • D)).divisorialSubmodule (f ⁻¹ᵁ V)) ∧
      ∀ p : Polynomial ((rationalFunctionsPresheaf Y).obj (op (f ⁻¹ᵁ V))),
        (∀ m : ℕ,
          p.coeff m ∈ (DivisorWithCoeffs.roundDown ((m : ℚ) • D)).divisorialSubmodule (f ⁻¹ᵁ V)) →
        p ∈ Subring.closure (Set.range (fun a : Γ(Z, V) =>
          Polynomial.C (algebraMap Γ(Y, f ⁻¹ᵁ V) _ (f.app V a))) ∪ ↑G) :=
  have : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  fg_roundDownSections_of_isRelativelyFreeDivisor_of_locallyOfFiniteType sY sZ hY f hf hq B hB hBc
    hfree V hV

end MMP.Fourfold

namespace MMP.Resolution.Bridges

/-- **The non-isomorphism locus of a proper birational morphism.** Let `h : Y ⟶ Z` be a proper
birational morphism of varieties over `k` with `Z` normal, and let `z` be a closed point of `Z`.
Then `h` restricts to an isomorphism `h⁻¹(V) ⟶ V` over some open neighbourhood `V` of `z` if and
only if the fibre `h⁻¹(z)` is finite. -/
@[mmp "lem_oai4_c1_nonisom_locus_positive_fibres"]
theorem exists_isIso_morphismRestrict_iff_finite_preimage_singleton {k : Type u} [Field k]
    {Y Z : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} (hY : IsVariety k sY)
    (hZ : IsVariety k sZ) [IsNormal Z] (h : Y ⟶ Z) (hh : h ≫ sZ = sY) [IsProper h]
    (hb : IsBirational h) {z : Z} (hz : IsClosed ({z} : Set Z)) :
    (∃ V : Z.Opens, z ∈ V ∧ IsIso (h ∣_ V)) ↔ (h ⁻¹' {z}).Finite := by
  refine ⟨fun ⟨V, hzV, _⟩ ↦ (subsingleton_preimage_of_isIso_morphismRestrict h V hzV).finite,
    fun hfin ↦ ?_⟩
  obtain ⟨⟨hO, hiso⟩, -⟩ := isIso_finiteFibreLocus_and_exceptionalSet_eq k hY hZ h hh hb
  exact ⟨⟨finiteFibreLocus h, hO⟩, hfin, hiso⟩

end MMP.Resolution.Bridges

end
