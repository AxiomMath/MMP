module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksSectionIdeal
public import MMP.AlgebraicTopology.ComplexVectorBundle.OfStacksBundle
public import MMP.AlgebraicTopology.ThomClass.Basic
/-!
# The orientation class of a regular imbedding, for Stacks vector bundles (Fulton, §19.2)

Let `i : X → Y` be a regular imbedding of codimension `d` of complex schemes, with ideal sheaf
`𝓘` and normal bundle `N`. Choose a quasi-coherent `𝒪_Y`-module `ℰ`, finite locally free of rank
`e ≥ d`, and a section `σ : Y ⟶ 𝐕(ℰ)` of its vector bundle `π : 𝐕(ℰ) = Spec_Y(Sym ℰ) ⟶ Y`
with zero scheme `Z(σ) = X`. Choose an open neighbourhood `V` of `X` in `Y` (classical topology)
and a complex topological sub-bundle `C ⊆ 𝐕(ℰ)(ℂ)|_V` with `C|_X ⊕ N = 𝐕(ℰ)(ℂ)|_X`; then
`Q = 𝐕(ℰ)(ℂ)|_V / C` is a complex vector bundle of rank `d`, and the image `σ̄` of `σ` in `Q`
vanishes on `X`. If `σ̄` does not vanish on `V - X`, it is a map of pairs
`(V, V - X) → (Q, Q - 0_Q)`, and a class `u ∈ H^{2d}(Y, Y - X)` is an *orientation class of
`i`* if under the excision isomorphism `H^{2d}(Y, Y - X) ≅ H^{2d}(V, V - X)` it corresponds to
`σ̄^*(u_Q)`, `u_Q` the Thom class of `Q`.

## Main definitions

* `MMP.Modules.normalFibre`: the fibre `N_x ⊆ ℂᵉ` of the normal bundle of `Z(σ)` at a point
  `x ∈ Y(ℂ)`, in the coordinates of a chart `c` of `ℰ`.
* `MMP.Modules.RegularImbeddingOrientationDatum`: the data `(ℰ, σ, V, Q, 𝐕(ℰ)(ℂ)|_V → Q)`.
* `MMP.Modules.RegularImbeddingOrientationDatum.sectionBar`: the section `σ̄` of `Q`.
* `MMP.Modules.RegularImbeddingOrientationDatum.thomPullback`: the map
  `H^{2d}(Q, Q - 0_Q) → H^{2d}(V, V - X)`, `u ↦ σ̄^* u`.
* `MMP.Modules.IsRegularImbeddingOrientationClass`: orientation classes of `i`.

## Implementation notes

A chart `c = (W, b)` of `ℰ` (`MMP.Modules.Chart`) gives coordinates `π⁻¹W(ℂ) → ℂᵉ`
(`MMP.Modules.coord`, inverse `MMP.Modules.chartInv`), and the local coordinates
`σ^♯bₐ` of `σ` (`MMP.Modules.sectionCoord`) cut out `Z(σ)` (`MMP.Modules.ideal_zeroLocus`).
In these coordinates the fibre at `x` of `ℰ|_X → 𝓘/𝓘²`, `m ↦ σ^♯m`, is
`w ↦ ∑ₐ wₐ σ^♯bₐ mod 𝔪ₓ 𝓘ₓ`, whose kernel consists of the values `g(x)` of the relations
`∑ₐ gₐ σ^♯bₐ = 0` on neighbourhoods of `x`; `N_x`, the dual of `(𝓘/𝓘²)(x)`, is the annihilator
of this kernel (`normalFibre`).

The sub-bundle `C` and the quotient `Q` are given together by a surjective morphism of complex
topological vector bundles `𝐕(ℰ)(ℂ)|_V → Q`, Mathlib's `Bundle.VectorBundle ℂ F Q` on `V`, of
which `C` is the kernel: a continuous map over `V` which is complex linear and onto on each
fibre, in the chart coordinates. The condition `C|_X ⊕ N = 𝐕(ℰ)(ℂ)|_X` is that on the fibres over
`X(ℂ)` the kernel of `𝐕(ℰ)_x → Q_x` is a complement of `N_x`.

The excision isomorphism `H^{2d}(Y, Y - X) ≅ H^{2d}(V, V - X)` is the restriction along the
inclusion `V ⊆ Y`, which is how it enters the definition.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Bundle

namespace MMP.Modules

open UnderlyingSpace

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]

section Section

variable {E : Y.Modules} [E.IsQuasicoherent] {r : ℕ}

/-- A section `σ` of `π : 𝐕(ℰ) ⟶ Y` pulls `π⁻¹U` back to `U`. -/
lemma preimage_preimage_proj_of_comp_eq_id {σ : Y ⟶ totalSpace E} (hσ : σ ≫ proj E = 𝟙 Y)
    (U : Y.Opens) : σ ⁻¹ᵁ (proj E ⁻¹ᵁ U) = U := by
  rw [← Scheme.Hom.comp_preimage, hσ, Scheme.Hom.id_preimage]

/-- The point `σ(y)` of `𝐕(ℰ)(ℂ)` lies over `y`. -/
lemma mapFun_proj_mapFun_section {σ : Y ⟶ totalSpace E} [σ.IsOver (Spec (.of ℂ))]
    (hσ : σ ≫ proj E = 𝟙 Y) (y : UnderlyingSpace ℂ Y) : mapFun (proj E) (mapFun σ y) = y :=
  UnderlyingSpace.ext (by simp only [toHom_mapFun, Category.assoc, hσ, Category.comp_id])

/-- The local coordinates of `σ` restrict along inclusions of opens. -/
lemma map_sectionCoord (σ : Y ⟶ totalSpace E) (c : Chart E r) {W W' : Y.Opens}
    (hW : W ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)) (h : W' ≤ W) (a : Fin r) :
    Y.presheaf.map (homOfLE h).op (sectionCoord σ c hW a) = sectionCoord σ c (h.trans hW) a := by
  simp only [sectionCoord]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

/-- The fibre `N_x ⊆ ℂʳ` of the normal bundle of `Z(σ)` at a point `x ∈ Y(ℂ)`, in the
coordinates of the chart `c = (V, b)`: the annihilator of the values `g(x)` of the relations
`∑ₐ gₐ σ^♯bₐ = 0` among the local coordinates of `σ` on open neighbourhoods `W` of `x` in
`σ⁻¹(π⁻¹V) = V`. These values form the kernel of the fibre `ℂʳ = ℰ(x) → (𝓘/𝓘²)(x)`, so `N_x` is
the image of the dual inclusion `(𝓘/𝓘²)(x)^∨ ⊆ ℰ(x)^∨`. -/
def normalFibre (σ : Y ⟶ totalSpace E) (c : Chart E r) (x : UnderlyingSpace ℂ Y) :
    Submodule ℂ (Fin r → ℂ) :=
  ⨅ (W : Y.Opens) (hW : W ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)) (hx : ⊤ ≤ x.toHom ⁻¹ᵁ W)
    (g : Fin r → Γ(Y, W)) (_ : ∑ a, g a * sectionCoord σ c hW a = 0),
    LinearMap.ker (Fintype.linearCombination ℂ fun a ↦ UnderlyingSpace.eval x hx (g a))

/-- Membership in `normalFibre σ c x`: `w` annihilates the value at `x` of every relation
`∑ₐ gₐ σ^♯bₐ = 0` on an open neighbourhood of `x`. -/
lemma mem_normalFibre {σ : Y ⟶ totalSpace E} {c : Chart E r} {x : UnderlyingSpace ℂ Y}
    {w : Fin r → ℂ} :
    w ∈ normalFibre σ c x ↔ ∀ (W : Y.Opens) (hW : W ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1))
      (hx : ⊤ ≤ x.toHom ⁻¹ᵁ W) (g : Fin r → Γ(Y, W)),
      ∑ a, g a * sectionCoord σ c hW a = 0 →
        ∑ a, w a • UnderlyingSpace.eval x hx (g a) = 0 := by
  simp only [normalFibre, Submodule.mem_iInf, LinearMap.mem_ker, Fintype.linearCombination_apply]

end Section

/-- The data defining an orientation class of a closed imbedding `i : X → Y` of complex schemes
of codimension `d` (Fulton, §19.2): a quasi-coherent `𝒪_Y`-module `ℰ`, finite locally free of
rank `e ≥ d`, with a section `σ : Y ⟶ 𝐕(ℰ)` whose zero scheme is `X`; an open neighbourhood `V`
of `X(ℂ)` in `Y(ℂ)`; and a complex topological vector bundle `Q` of rank `d` on `V` with a
surjective bundle morphism `𝐕(ℰ)(ℂ)|_V → Q` whose kernel `C` satisfies `C|_X ⊕ N = 𝐕(ℰ)(ℂ)|_X`,
so that `Q = 𝐕(ℰ)(ℂ)|_V / C`, such that the induced section `σ̄` of `Q` does not vanish on
`V - X`. -/
structure RegularImbeddingOrientationDatum (i : X ⟶ Y) [i.IsOver (Spec (.of ℂ))] (d : ℕ) where
  /-- The rank `e` of `ℰ`. -/
  rank : ℕ
  le_rank : d ≤ rank
  /-- The `𝒪_Y`-module `ℰ`. -/
  E : Y.Modules
  [isQuasicoherent : E.IsQuasicoherent]
  [isFiniteLocallyFreeOfRank : SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E rank]
  /-- The section `σ` of `𝐕(ℰ)`. -/
  σ : Y ⟶ totalSpace E
  [isOver : σ.IsOver (Spec (.of ℂ))]
  comp_proj : σ ≫ proj E = 𝟙 Y
  zeroLocus_eq : zeroLocus E σ = i.ker
  /-- The open neighbourhood `V` of `X(ℂ)` in `Y(ℂ)`. -/
  nbhd : Set (UnderlyingSpace ℂ Y)
  isOpen_nbhd : IsOpen nbhd
  range_subset_nbhd : range (UnderlyingSpace.map i) ⊆ nbhd
  /-- The model fibre of `Q`. -/
  F : Type
  [normedAddCommGroup : NormedAddCommGroup F]
  [normedSpace : NormedSpace ℂ F]
  [finiteDimensional : FiniteDimensional ℂ F]
  finrank_F : Module.finrank ℂ F = d
  /-- The fibres of the quotient bundle `Q = 𝐕(ℰ)(ℂ)|_V / C`. -/
  Q : nbhd → Type
  [addCommGroup (x : nbhd) : AddCommGroup (Q x)]
  [module (x : nbhd) : Module ℂ (Q x)]
  [topologicalSpace (x : nbhd) : TopologicalSpace (Q x)]
  [topologicalSpaceTotal : TopologicalSpace (TotalSpace F Q)]
  [fiberBundle : FiberBundle F Q]
  [vectorBundle : _root_.VectorBundle ℂ F Q]
  /-- The quotient map `𝐕(ℰ)(ℂ)|_V → Q`. -/
  quot : {p : UnderlyingSpace ℂ (totalSpace E) // mapFun (proj E) p ∈ nbhd} → TotalSpace F Q
  continuous_quot : Continuous quot
  proj_quot (p) : (quot p).proj = ⟨mapFun (proj E) p.1, p.2⟩
  /-- In the coordinates `ℂᵉ` of a chart, the quotient map is linear and onto on the fibre over
  `x ∈ V`, and over `X(ℂ)` its kernel `C_x` is a complement of `N_x`. -/
  fibre (c : Chart E rank) (x : UnderlyingSpace ℂ Y) (hx : ⊤ ≤ x.toHom ⁻¹ᵁ c.1.1)
    (hxV : x ∈ nbhd) : ∃ L : (Fin rank → ℂ) →ₗ[ℂ] Q ⟨x, hxV⟩,
      (∀ w, quot ⟨chartInv c x hx w, by rwa [mapFun_proj_chartInv]⟩ = ⟨⟨x, hxV⟩, L w⟩) ∧
      Function.Surjective L ∧
      (x ∈ range (UnderlyingSpace.map i) → IsCompl (LinearMap.ker L) (normalFibre σ c x))
  /-- `σ̄` does not vanish on `V - X`. -/
  quot_sec_notMem (y : nbhd) (hy : y.1 ∉ range (UnderlyingSpace.map i)) :
    quot ⟨mapFun σ y, by rw [mapFun_proj_mapFun_section comp_proj]; exact y.2⟩ ∉
      range (Bundle.zeroSection F Q)

namespace RegularImbeddingOrientationDatum

attribute [instance] isQuasicoherent isFiniteLocallyFreeOfRank isOver normedAddCommGroup
  normedSpace finiteDimensional addCommGroup module topologicalSpace topologicalSpaceTotal
  fiberBundle vectorBundle

variable {i : X ⟶ Y} [i.IsOver (Spec (.of ℂ))] {d : ℕ} (D : RegularImbeddingOrientationDatum i d)

/-- The point `σ(y)` of `𝐕(ℰ)(ℂ)` lies over `y`. -/
lemma mapFun_proj_mapFun_σ (y : UnderlyingSpace ℂ Y) : mapFun (proj D.E) (mapFun D.σ y) = y :=
  mapFun_proj_mapFun_section D.comp_proj y

/-- The section `σ̄ : V → Q` induced by `σ`. -/
def sectionBar (y : D.nbhd) : TotalSpace D.F D.Q :=
  D.quot ⟨mapFun D.σ y, by rw [mapFun_proj_mapFun_σ]; exact y.2⟩

/-- The section `σ̄` is continuous. -/
lemma continuous_sectionBar : Continuous D.sectionBar :=
  D.continuous_quot.comp (((continuous_mapFun D.σ).comp continuous_subtype_val).subtype_mk _)

/-- `σ̄` is a section of `Q`. -/
@[simp]
lemma proj_sectionBar (y : D.nbhd) : (D.sectionBar y).proj = y := by
  rw [sectionBar, proj_quot]
  exact Subtype.ext (D.mapFun_proj_mapFun_σ _)

/-- `σ̄` maps `V - X` into `Q - 0_Q`. -/
lemma sectionBar_preimage_subset :
    D.sectionBar ⁻¹' range (Bundle.zeroSection D.F D.Q) ⊆
      Subtype.val ⁻¹' range (UnderlyingSpace.map i) := fun y hy ↦ by
  by_contra h
  exact D.quot_sec_notMem y h hy

/-- `σ̄` as a continuous map `V → Q`. -/
def sectionBarHom : TopCat.of D.nbhd ⟶ TopCat.of (TotalSpace D.F D.Q) :=
  TopCat.ofHom ⟨D.sectionBar, D.continuous_sectionBar⟩

variable (R : Type) [CommRing R]

/-- The map `H^{2d}(Q, Q - 0_Q) → H^{2d}(V, V - X)`, `u ↦ σ̄^* u`. -/
def thomPullback :
    cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace D.F D.Q))
        (range (Bundle.zeroSection D.F D.Q)) (2 * Module.finrank ℂ D.F : ℕ) ⟶
      cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of D.nbhd)
        (Subtype.val ⁻¹' range (UnderlyingSpace.map i)) (2 * d : ℕ) :=
  cohomologyWithSupports.pullback R (ModuleCat.of R R) D.sectionBarHom _ _ ≫
    cohomologyWithSupports.forget R (ModuleCat.of R R) (TopCat.of D.nbhd)
      D.sectionBar_preimage_subset _ ≫ eqToHom (by rw [D.finrank_F])

end RegularImbeddingOrientationDatum

variable (R : Type) [CommRing R]

/-- The restriction `H^j(Y, Y - Z) → H^j(V, V - Z)` along the inclusion of a subset `V ⊆ Y(ℂ)`;
for `V` open and `Z ⊆ V` closed it is the excision isomorphism. -/
def RegularImbeddingOrientationDatum.excisionRestrict (Z : Set (UnderlyingSpace ℂ Y))
    (V : Set (UnderlyingSpace ℂ Y)) (j : ℤ) :
    cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y)) Z j ⟶
      cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of V) (Subtype.val ⁻¹' Z) j :=
  cohomologyWithSupports.pullback R (ModuleCat.of R R)
    (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(V, UnderlyingSpace ℂ Y))) Z j

/-- An *orientation class* of a closed imbedding `i : X → Y` of complex schemes of codimension
`d`, with normal bundle `N` (Fulton, §19.2): a class `u ∈ H^{2d}(Y, Y - X)` for which there are a
quasi-coherent `𝒪_Y`-module `ℰ`, finite locally free of rank `e ≥ d`, with a section
`σ : Y ⟶ 𝐕(ℰ)` whose zero scheme is `X`, an open neighbourhood `V` of `X` in `Y`, and a complex
topological sub-bundle `C ⊆ 𝐕(ℰ)(ℂ)|_V` with `C|_X ⊕ N = 𝐕(ℰ)(ℂ)|_X`, such that, with
`Q = 𝐕(ℰ)(ℂ)|_V / C` and `σ̄` the induced section of `Q`, `σ̄` maps `(V, V - X)` to
`(Q, Q - 0_Q)` and `u` corresponds to `σ̄^*(u_Q)` under the excision isomorphism
`H^{2d}(Y, Y - X) ≅ H^{2d}(V, V - X)`, `u_Q` the Thom class of `Q`. -/
def IsRegularImbeddingOrientationClass (i : X ⟶ Y) [i.IsOver (Spec (.of ℂ))] (d : ℕ)
    (u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map i)) (2 * d : ℕ)) : Prop :=
  ∃ (D : RegularImbeddingOrientationDatum i d) (uQ : cohomologyWithSupports R (ModuleCat.of R R)
      (TopCat.of (TotalSpace D.F D.Q)) (range (Bundle.zeroSection D.F D.Q))
      (2 * Module.finrank ℂ D.F : ℕ)),
    MMP.IsThomClass (R := R) D.F D.Q uQ ∧
      (RegularImbeddingOrientationDatum.excisionRestrict R _ D.nbhd _).hom u =
        (D.thomPullback R).hom uQ

end MMP.Modules
