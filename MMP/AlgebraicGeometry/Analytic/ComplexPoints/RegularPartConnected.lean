module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPartDense
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPartComplement
public import MMP.RingTheory.Presentation.HypersurfacePresentation
public import MMP.AlgebraicGeometry.Variety.SingularLocus
/-!
# The regular part of a complex variety is connected

Let `X` be an irreducible complex variety of dimension `n`. Then `X_reg(ℂ)`, with the classical
topology, is a complex manifold of dimension `n`; for every Zariski closed `Z ⊊ X`,
`X_reg(ℂ) - Z` is connected and dense in `X(ℂ)`; and the singular locus is Zariski closed of
dimension smaller than that of `X`.

The new ingredient is connectedness. Choose a nonempty affine open `U ⊆ X` with ring `A`. The
regular locus of `U` contains a basic open `D(σ)`, `σ ≠ 0`. A hypersurface presentation of `A`
(Noether normalization `ℂ[x₁, …, xₛ] ⊆ A` and a primitive element `y` with minimal polynomial
`f`, conductor `c` and discriminant-type element `D`) gives `r ∈ ℂ[x]`, `r ≠ 0`, with `σ ∣ r`;
for `δ = c D r` the points of `U(ℂ)` where `δ` does not vanish form a connected set (a finite
unbranched covering of the complement of a hypersurface in `ℂˢ`, whose total space is connected
since `f` is irreducible). These points are regular, and they are dense in `X(ℂ)` since they are
the regular points off the proper Zariski closed set `X - D(δ)`. A set squeezed between a
connected set and its closure is connected, so `X_reg(ℂ)` is connected. Removing a Zariski closed
`Z` removes a locally analytic subset of the connected manifold `X_reg(ℂ)`, which keeps it
connected.

## Main results

* `MMP.UnderlyingSpace.exists_dvd_isPreconnected_setOf_evalTop_ne_zero`: on an
  affine integral scheme of finite type over `ℂ`, every nonzero global function divides a nonzero
  one whose nonvanishing locus in `X(ℂ)` is preconnected.
* `MMP.UnderlyingSpace.isPreconnected_regularPart`: `X_reg(ℂ)` is preconnected.
* `MMP.UnderlyingSpace.isConnected_regularPart_diff`: `X_reg(ℂ) - Z` is connected
  for a Zariski closed `Z ⊊ X`.
* `MMP.UnderlyingSpace.regularPart_isManifold_isConnected_dense`: the full
  statement.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [I. R. Shafarevich, *Basic Algebraic Geometry 2*], Chapter VII, §2.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
open MMP.Intersection.Scheme (dimension)
open scoped ContDiff Manifold

namespace MMP

namespace UnderlyingSpace

/-- **Preconnected nonvanishing loci, affine case.** On an affine integral scheme `X` of finite type
over `ℂ`, every nonzero global function `a` divides a nonzero global function `h` such that the
`ℂ`-points at which `h` does not vanish form a preconnected subset of `X(ℂ)`. -/
theorem exists_dvd_isPreconnected_setOf_evalTop_ne_zero {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsAffine X] [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
    {a : Γ(X, ⊤)} (ha : a ≠ 0) :
    ∃ h : Γ(X, ⊤), h ≠ 0 ∧ a ∣ h ∧
      IsPreconnected {q : UnderlyingSpace ℂ X | evalTop q h ≠ 0} := by
  letI : Algebra ℂ Γ(X, ⊤) := (structureRingHom ℂ X).toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(X, ⊤) := finiteType_structureRingHom
  obtain ⟨s, P, hinj, hc0, hdvd, D, hD0, hD⟩ :=
    SmoothLocusConnected.exists_hypersurfacePresentation Γ(X, ⊤)
  obtain ⟨r, hr0, har⟩ := hdvd a ha
  set δ := P.c * D * r
  have hδ : δ ≠ 0 := mul_ne_zero (mul_ne_zero hc0 hD0) hr0
  refine ⟨P.g δ, (map_ne_zero_iff _ hinj).mpr hδ, har.trans (map_dvd P.g (dvd_mul_left r _)), ?_⟩
  have hsep : ∀ x, MvPolynomial.eval x δ ≠ 0 → (P.f.map (MvPolynomial.eval x)).Separable :=
    fun x hx ↦ hD x (by
      simp only [δ, map_mul] at hx
      exact right_ne_zero_of_mul (left_ne_zero_of_mul hx))
  rw [← isInducing_evalTop.isPreconnected_image]
  convert P.isPreconnected_image_coe hδ (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) hsep using 1
  ext v
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨{ evalRingHom (U := ⊤) q (Scheme.Hom.preimage_top _).ge with
      commutes' := evalTop_structureRingHom q }, hq, rfl⟩
  · rintro ⟨ψ, hψ, rfl⟩
    have hev : evalTop (ofRingHom ψ.toRingHom ψ.commutes) = ⇑ψ :=
      funext (evalTop_ofRingHom ψ.toRingHom ψ.commutes)
    refine ⟨ofRingHom ψ.toRingHom ψ.commutes, ?_, hev⟩
    change evalTop _ (P.g δ) ≠ 0
    rwa [hev]

/-- The `ℂ`-points of `X` lying over the image of a basic open `D(h)` of an open `U ⊆ X` lie in the
image of the `ℂ`-points of `U` at which `h` does not vanish. -/
theorem subset_image_mapFun_setOf_evalTop_ne_zero {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    (U : X.Opens) [U.toScheme.Over (Spec (.of ℂ))] [U.ι.IsOver (Spec (.of ℂ))] (h : Γ(U, ⊤)) :
    {p : UnderlyingSpace ℂ X |
        p.toHom (IsLocalRing.closedPoint ℂ) ∈ (U.ι ''ᵁ U.toScheme.basicOpen h : Set X)} ⊆
      mapFun (K := ℂ) U.ι '' {q | evalTop q h ≠ 0} := by
  rintro p ⟨y, hy, hyp⟩
  obtain ⟨q, rfl⟩ : p ∈ Set.range (mapFun (K := ℂ) U.ι) := by
    rw [range_mapFun_of_isOpenImmersion, Set.mem_setOf_eq, Scheme.Opens.opensRange_ι,
      top_le_preimage_iff, ← hyp]
    exact (Scheme.Opens.range_ι U).subset ⟨y, rfl⟩
  refine ⟨q, ?_, rfl⟩
  have hqy : q.toHom (IsLocalRing.closedPoint ℂ) = y := by
    apply U.ι.isOpenEmbedding.injective
    have : (mapFun (K := ℂ) U.ι q).toHom (IsLocalRing.closedPoint ℂ) =
        U.ι (q.toHom (IsLocalRing.closedPoint ℂ)) := by
      rw [toHom_mapFun]
      rfl
    exact (hyp.trans this).symm
  have hq : ⊤ ≤ q.toHom ⁻¹ᵁ U.toScheme.basicOpen h := by
    rwa [top_le_preimage_iff, hqy]
  exact (top_le_preimage_basicOpen_iff (U := ⊤) q (Scheme.Hom.preimage_top _).ge h).mp hq

/-- **The regular part of a complex variety is preconnected.** For a complex variety `X`
(reduced and irreducible), the regular points `X_reg(ℂ)` form a preconnected subset of `X(ℂ)` for the
classical topology. -/
theorem isPreconnected_regularPart {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [QuasiCompact (X ↘ Spec (.of ℂ))] :
    IsPreconnected (regularPart ℂ X) := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := genericPoint X) (U := ⊤) trivial
  letI : U.toScheme.Over (Spec (.of ℂ)) := ⟨U.ι ≫ X ↘ Spec (.of ℂ)⟩
  haveI : U.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI : IsAffine U := hU
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  haveI : LocallyOfFiniteType (U.toScheme ↘ Spec (.of ℂ)) :=
    inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X ↘ Spec (.of ℂ)))
  let W : U.toScheme.Opens :=
    U.ι ⁻¹ᵁ ⟨regularLocus X, isOpen_regularLocus_of_isAlgebraicScheme ℂ X⟩
  have hyW : (⟨genericPoint X, hxU⟩ : U.toScheme) ∈ W := by
    change U.ι ⟨genericPoint X, hxU⟩ ∈ regularLocus X
    rw [Scheme.Opens.ι_apply]
    exact genericPoint_mem_regularLocus X
  obtain ⟨σ, hσW, hyσ⟩ := (isAffineOpen_top U.toScheme).exists_basicOpen_le
    (V := W) ⟨_, hyW⟩ trivial
  have hσ : σ ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hyσ
    exact hyσ
  obtain ⟨h, hh0, hσh, hT⟩ := exists_dvd_isPreconnected_setOf_evalTop_ne_zero hσ
  set T := {q : UnderlyingSpace ℂ U | evalTop q h ≠ 0}
  have hcont : Continuous (mapFun (K := ℂ) U.ι) :=
    (isOpenEmbedding_map_of_isOpenImmersion U.ι).continuous
  have hTc : IsPreconnected (mapFun (K := ℂ) U.ι '' T) := hT.image _ hcont.continuousOn
  have hreg : mapFun (K := ℂ) U.ι '' T ⊆ regularPart ℂ X := by
    rintro _ ⟨q', hq', rfl⟩
    have hq'σ : evalTop q' σ ≠ 0 := by
      obtain ⟨b, rfl⟩ := hσh
      have : evalRingHom (U := ⊤) q' (Scheme.Hom.preimage_top _).ge (σ * b) ≠ 0 := hq'
      rw [map_mul] at this
      exact left_ne_zero_of_mul this
    have hD : ⊤ ≤ q'.toHom ⁻¹ᵁ U.toScheme.basicOpen σ :=
      (top_le_preimage_basicOpen_iff (U := ⊤) q' (Scheme.Hom.preimage_top _).ge σ).mpr hq'σ
    rw [mem_regularPart_iff, toHom_mapFun]
    exact hσW (hD (Set.mem_univ _))
  let O : X.Opens := U.ι ''ᵁ U.toScheme.basicOpen h
  have hOne : (O : Set X)ᶜ ≠ Set.univ := by
    intro hO
    have hne : U.toScheme.basicOpen h ≠ ⊥ := by
      rwa [Ne, basicOpen_eq_bot_iff]
    obtain ⟨y, hy⟩ := (Opens.ne_bot_iff_nonempty _).mp hne
    exact (hO ▸ Set.mem_univ (U.ι y) : U.ι y ∈ (O : Set X)ᶜ) ⟨y, hy, rfl⟩
  have hsub : regularPart ℂ X \ {p | p.toHom (IsLocalRing.closedPoint ℂ) ∈ (O : Set X)ᶜ} ⊆
      mapFun (K := ℂ) U.ι '' T := fun p hp ↦
    subset_image_mapFun_setOf_evalTop_ne_zero U h (of_not_not hp.2)
  exact hTc.subset_closure hreg fun p _ ↦ closure_mono hsub
    ((dense_regularPart_diff (X := X) O.isOpen.isClosed_compl hOne).closure_eq ▸ Set.mem_univ p)

/-- **Removing a proper Zariski closed set leaves the regular part connected.** For a complex
variety `X` and a Zariski closed `Z ⊊ X`, `X_reg(ℂ) - Z` is a connected subset of `X(ℂ)`. -/
theorem isConnected_regularPart_diff {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [QuasiCompact (X ↘ Spec (.of ℂ))]
    {Z : Set X} (hZ : IsClosed Z) (hZne : Z ≠ Set.univ) :
    IsConnected (regularPart ℂ X \ {p | p.toHom (IsLocalRing.closedPoint ℂ) ∈ Z}) := by
  obtain ⟨p, hp, hpZ⟩ := exists_mem_regularPart_notMem hZ hZne
  exact ⟨⟨p, hp, hpZ⟩, isPreconnected_regularPart_diff hZ isPreconnected_regularPart⟩

/-- **The regular part of a complex variety** (Fulton, §19.1). Let `X` be an irreducible complex
variety of dimension `n`. Then
* `X_reg(ℂ)`, with the classical topology and its algebraic charts, is a complex manifold of
  complex dimension `n`;
* for every Zariski closed `Z ⊊ X`, `X_reg(ℂ) - Z` is connected and dense in `X(ℂ)`;
* the singular points form a Zariski closed set `S` (a closed point `x` is singular iff `x ∈ S`)
  of strictly smaller topological Krull dimension than `X`. -/
theorem regularPart_isManifold_isConnected_dense {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [QuasiCompact (X ↘ Spec (.of ℂ))]
    {n : ℕ} (hn : (n : WithBot ℕ∞) = dimension X) :
    (letI := regularChartedSpace (𝕜 := ℂ) hn;
      IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω (regularOpens ℂ X)) ∧
    (∀ Z : Set X, IsClosed Z → Z ≠ Set.univ →
      IsConnected (regularPart ℂ X \ {p | p.toHom (IsLocalRing.closedPoint ℂ) ∈ Z}) ∧
        Dense (regularPart ℂ X \ {p | p.toHom (IsLocalRing.closedPoint ℂ) ∈ Z})) ∧
    ∃ S : Set X, IsClosed S ∧ (∀ x : X, IsClosed ({x} : Set X) → (x ∉ regularLocus X ↔ x ∈ S)) ∧
      topologicalKrullDim S < topologicalKrullDim X :=
  ⟨isManifold_regularOpens hn, fun _ hZ hZne ↦
    ⟨isConnected_regularPart_diff hZ hZne, dense_regularPart_diff hZ hZne⟩,
    exists_isClosed_singularPoints ℂ X⟩

end UnderlyingSpace

end MMP
