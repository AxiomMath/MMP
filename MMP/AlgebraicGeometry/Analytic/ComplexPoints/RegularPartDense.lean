module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPartDenseAnalytic
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPartManifold

/-!
# The regular part of a complex variety is dense in the classical topology

Let `X` be an irreducible complex variety and `Z ⊊ X` a Zariski closed subset. Then the regular
points off `Z`, `X_reg(ℂ) - Z`, are dense in `X(ℂ)` for the classical topology.

Near a point `p`, choose an affine open `U ∋ p`. The regular points of `X` off `Z` form a
nonempty Zariski open subset (it contains the generic point), so it contains a basic open
`D(h) ⊆ U` with `h ≠ 0`. The classical topology on `U(ℂ)` is that of pointwise convergence of
the global functions on `U`, and in it the points at which `h` does not vanish are dense
(`MMP.RegularPartDense.mem_closure_image_setOf_apply_ne_zero`). These points are
regular and off `Z`.

## Main results

* `MMP.UnderlyingSpace.mem_closure_setOf_evalTop_ne_zero`: on an affine integral
  scheme of finite type over `ℂ`, the `ℂ`-points at which a nonzero global function `h` does not
  vanish are dense.
* `MMP.UnderlyingSpace.dense_regularPart_diff`: for a Zariski closed `Z ⊊ X`,
  `X_reg(ℂ) - Z` is dense in `X(ℂ)`.
* `MMP.UnderlyingSpace.dense_regularPart`: `X_reg(ℂ)` is dense in `X(ℂ)`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [I. R. Shafarevich, *Basic Algebraic Geometry 2*], Chapter VII, §2.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace MMP

namespace UnderlyingSpace

/-- **Nonvanishing loci are dense, affine case.** On an affine integral scheme `X` of finite type
over `ℂ`, the `ℂ`-points at which a nonzero global function `h` does not vanish are dense in
`X(ℂ)` for the classical topology. -/
theorem mem_closure_setOf_evalTop_ne_zero {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsAffine X]
    [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] {h : Γ(X, ⊤)} (hh : h ≠ 0)
    (p : UnderlyingSpace ℂ X) : p ∈ closure {q : UnderlyingSpace ℂ X | evalTop q h ≠ 0} := by
  letI : Algebra ℂ Γ(X, ⊤) := (structureRingHom ℂ X).toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(X, ⊤) := finiteType_structureRingHom
  haveI : Nonempty X := ⟨p.toHom (IsLocalRing.closedPoint ℂ)⟩
  let φ : Γ(X, ⊤) →ₐ[ℂ] ℂ :=
    { evalRingHom (U := ⊤) p (Scheme.Hom.preimage_top _).ge with
      commutes' := evalTop_structureRingHom p }
  rw [isInducing_evalTop.closure_eq_preimage_closure_image, Set.mem_preimage]
  refine closure_mono ?_ (RegularPartDense.mem_closure_image_setOf_apply_ne_zero hh φ)
  rintro _ ⟨ψ, hψ, rfl⟩
  refine ⟨ofRingHom ψ.toRingHom ψ.commutes, ?_,
    funext (evalTop_ofRingHom ψ.toRingHom ψ.commutes)⟩
  simpa [evalTop_ofRingHom] using hψ

/-- **Removing a proper Zariski closed subset leaves the regular part dense.** For a complex
variety `X` and a Zariski closed `Z ⊊ X`, the regular points off `Z`, `X_reg(ℂ) - Z`, are dense
in `X(ℂ)` for the classical topology. -/
theorem dense_regularPart_diff {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [QuasiCompact (X ↘ Spec (.of ℂ))]
    {Z : Set X} (hZ : IsClosed Z) (hZne : Z ≠ Set.univ) :
    Dense (regularPart ℂ X \ {p | p.toHom (IsLocalRing.closedPoint ℂ) ∈ Z}) := by
  intro p
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := p.toHom (IsLocalRing.closedPoint ℂ)) (U := ⊤) trivial
  letI : U.toScheme.Over (Spec (.of ℂ)) := ⟨U.ι ≫ X ↘ Spec (.of ℂ)⟩
  haveI : U.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI : IsAffine U := hU
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  haveI : LocallyOfFiniteType (U.toScheme ↘ Spec (.of ℂ)) :=
    inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X ↘ Spec (.of ℂ)))
  obtain ⟨q, hq⟩ : p ∈ Set.range (mapFun (K := ℂ) U.ι) := by
    rw [range_mapFun_of_isOpenImmersion, Set.mem_setOf_eq, Scheme.Opens.opensRange_ι,
      top_le_preimage_iff]
    exact hxU
  have hη : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨_, trivial, hxU⟩
  have hηZ : genericPoint X ∉ Z := fun hg =>
    hZne (Set.eq_univ_of_univ_subset ((genericPoint_spec X).def ▸
      hZ.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hg)))
  let W : U.toScheme.Opens := U.ι ⁻¹ᵁ
    ⟨regularLocus X ∩ Zᶜ, (isOpen_regularLocus_of_isAlgebraicScheme ℂ X).inter hZ.isOpen_compl⟩
  have hyW : (⟨genericPoint X, hη⟩ : U.toScheme) ∈ W :=
    ⟨genericPoint_mem_regularLocus X, hηZ⟩
  obtain ⟨h, hhW, hyh⟩ := (isAffineOpen_top U.toScheme).exists_basicOpen_le
    (V := W) ⟨_, hyW⟩ trivial
  have hh : h ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hyh
    exact hyh
  have hcont : Continuous (mapFun (K := ℂ) U.ι) :=
    (isOpenEmbedding_map_of_isOpenImmersion U.ι).continuous
  rw [← hq]
  refine closure_mono ?_ (image_closure_subset_closure_image hcont
    ⟨q, mem_closure_setOf_evalTop_ne_zero hh q, rfl⟩)
  rintro _ ⟨q', hq', rfl⟩
  have hD : ⊤ ≤ q'.toHom ⁻¹ᵁ U.toScheme.basicOpen h :=
    (top_le_preimage_basicOpen_iff (U := ⊤) q' (Scheme.Hom.preimage_top _).ge h).mpr hq'
  rw [Set.mem_diff, mem_regularPart_iff, Set.mem_setOf_eq, toHom_mapFun]
  exact hhW (hD (Set.mem_univ _))

/-- **The regular part of a complex variety is dense.** For a complex variety `X` (reduced and
irreducible), the regular points `X_reg(ℂ)` are dense in `X(ℂ)` for the classical topology. -/
theorem dense_regularPart {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [QuasiCompact (X ↘ Spec (.of ℂ))] :
    Dense (regularPart ℂ X) := by
  simpa using dense_regularPart_diff (X := X) isClosed_empty Set.empty_ne_univ

end UnderlyingSpace

end MMP
