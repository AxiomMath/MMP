module

public import MMP.AlgebraicGeometry.Bertini.ReducedGeneralMember
public import StacksFrontier.AlgebraicGeometry.AmpleQuasiAffineCover.Basic
public import StacksFrontier.AlgebraicGeometry.AmplePowers.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.GeneratingSectionsPointValue
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinateSquare
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleLocalDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.GenericFibrePoint

/-!
# The image of the morphism of an ample free system

Let `X` be a proper scheme over a field `k`, `L` an ample invertible `𝒪_X`-module and
`ψ : V → Γ(X, L)` a `k`-linear map whose sections generate `L`, with morphism
`φ : X → 𝐏(V)`. Over the standard open `D₊(v)` of a vector `v` the morphism `φ` restricts to
`X_{ψ(v)} → D₊(v)`; the source is quasi-affine because `L` is ample, and the map is proper because
`X` is, so the source is affine and the restriction is finite. Hence the fibres of `φ` carry no
nontrivial specializations, and `dim X ≤ dim φ(X)`. In particular, when `dim X ≥ 2` the image of
`φ` has dimension at least two, which is the hypothesis of Bertini's irreducibility theorem
`MMP.Threefold.Bridges.exists_dense_open_geometricallyIntegral_zeroScheme`.

## Main results

* `MMP.Mori.isFinite_morphismRestrict_basicOpen_morphismOfGeneratingSections`: the restriction of
  `φ` over a standard open `D₊(v)` is finite.
* `MMP.Mori.eq_of_specializes_of_morphismOfGeneratingSections_eq`: two points of `X`, one a
  specialization of the other, with the same image under `φ` are equal.
* `MMP.Mori.topologicalKrullDim_le_range_morphismOfGeneratingSections`: `dim X ≤ dim φ(X)`.
* `MMP.Mori.two_le_topologicalKrullDim_range_morphismOfGeneratingSections`: the image of the
  morphism of a spanning family of sections of an ample `L` on a proper `X` of dimension at least
  two has dimension at least two.

## Implementation notes

The finiteness of `φ` is proved chart by chart, through `IsFinite = IsProper ⊓ IsAffineHom`: a
quasi-affine scheme proper over an affine one is affine, because its morphism to the spectrum of
its global sections is then a universally closed immersion, hence a closed immersion. The degree
of `L` along curves is not used.

## References

* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of 3.39
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace MMP.Mori

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule
  morphismOfGeneratingSections preimage_basicOpen_morphismOfGeneratingSections)
open Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare
  (morphismOfGeneratingSections_comp_projectiveSpaceOfModuleToSpec)
open Stacks.NonvanishingOpen (nonvanishingOpen)

attribute [local instance] globalSectionsModule

/-- **A quasi-affine scheme proper over an affine scheme is affine.** The morphism
`X → Spec Γ(X, 𝒪_X)` is an immersion, and it is universally closed since the composite
`X → Spec Γ(X, 𝒪_X) → Y` is; so it is a closed immersion into an affine scheme. -/
theorem isAffine_of_isQuasiAffine_of_isProper {X Y : Scheme.{u}} [X.IsQuasiAffine] [IsAffine Y]
    (f : X ⟶ Y) [IsProper f] : IsAffine X := by
  have hf : f = X.toSpecΓ ≫ Spec.map f.appTop ≫ Y.isoSpec.inv := by
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc]
    simp [Scheme.isoSpec]
  have : UniversallyClosed (X.toSpecΓ ≫ Spec.map f.appTop ≫ Y.isoSpec.inv) := by
    rw [← hf]; infer_instance
  have : UniversallyClosed X.toSpecΓ :=
    UniversallyClosed.of_comp_of_isSeparated X.toSpecΓ (Spec.map f.appTop ≫ Y.isoSpec.inv)
  have : IsClosedImmersion X.toSpecΓ :=
    IsClosedImmersion.of_isPreimmersion _ X.toSpecΓ.isClosedMap.isClosed_range
  exact isAffine_of_isAffineHom X.toSpecΓ

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
  {X : Scheme.{u}} [X.Over (Spec (.of k))] {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]

/-- The nonvanishing open of a global section of an ample invertible module is quasi-affine. -/
theorem isQuasiAffine_nonvanishingOpen_of_isAmple (hL : Stacks.Ample.IsAmple X L)
    (t : Γ(L, ⊤)) : (nonvanishingOpen X L t).toScheme.IsQuasiAffine := by
  have h := Stacks.AmpleQuasiAffineCover.isQuasiAffine_nonvanishingOpen_of_isAmple L hL
    (d := 1) le_rfl ((Stacks.Ample.tensorPowModuleOneIso X L).inv.app ⊤ t)
  have heq : nonvanishingOpen X (Stacks.Ample.tensorPowModule X L ((1 : ℕ) : ℤ))
      ((Stacks.Ample.tensorPowModuleOneIso X L).inv.app ⊤ t) = nonvanishingOpen X L t :=
    TopologicalSpace.Opens.ext
      (Stacks.Ample.nonvanishingLocus_congr (Stacks.Ample.tensorPowModuleOneIso X L).symm t)
  rwa [heq] at h

variable [IsProper (X ↘ Spec (.of k))]

/-- The morphism of a generating family of sections of an invertible module on a proper
`k`-scheme is proper. -/
theorem isProper_morphismOfGeneratingSections (ψ : V →ₗ[k] Γ(L, ⊤))
    (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) :
    IsProper (morphismOfGeneratingSections k V L ψ hψ) := by
  have : IsProper (morphismOfGeneratingSections k V L ψ hψ ≫
      AlgebraicGeometry.projectiveSpaceOfModuleToSpec k V) := by
    rw [morphismOfGeneratingSections_comp_projectiveSpaceOfModuleToSpec]; infer_instance
  have : IsSeparated (AlgebraicGeometry.projectiveSpaceOfModuleToSpec k V) := by
    change IsSeparated (AlgebraicGeometry.Proj.toSpecZero _ ≫ Spec.map _)
    infer_instance
  exact IsProper.of_comp _ (AlgebraicGeometry.projectiveSpaceOfModuleToSpec k V)

/-- **Over a standard open, the morphism of an ample free system is finite.** For `L` ample on a
proper `k`-scheme `X` and `ψ : V → Γ(X, L)` generating `L`, the restriction of
`φ : X → 𝐏(V)` over the standard open `D₊(v)` of a vector `v` is a finite morphism. -/
theorem isFinite_morphismRestrict_basicOpen_morphismOfGeneratingSections
    (hL : Stacks.Ample.IsAmple X L) (ψ : V →ₗ[k] Γ(L, ⊤))
    (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) (v : V) :
    IsFinite (morphismOfGeneratingSections k V L ψ hψ ∣_
      Proj.basicOpen (ProjectiveSpaceOfModule.symmetricGrading k V)
        (SymmetricAlgebra.ι k V v)) := by
  set φ := morphismOfGeneratingSections k V L ψ hψ
  set U := Proj.basicOpen (ProjectiveSpaceOfModule.symmetricGrading k V) (SymmetricAlgebra.ι k V v)
  have := isProper_morphismOfGeneratingSections ψ hψ
  have hUa : IsAffineOpen U := Proj.isAffineOpen_basicOpen _ _
    (ProjectiveSpaceOfModule.ι_mem_symmetricPower_one k V v) Nat.one_pos
  have : IsAffine U.toScheme := hUa
  have : (φ ⁻¹ᵁ U).toScheme.IsQuasiAffine := by
    have h := preimage_basicOpen_morphismOfGeneratingSections k V L ψ hψ v
    change φ ⁻¹ᵁ U = _ at h
    rw [h]
    exact isQuasiAffine_nonvanishingOpen_of_isAmple hL (ψ v)
  have : IsAffine (φ ⁻¹ᵁ U).toScheme := isAffine_of_isQuasiAffine_of_isProper (φ ∣_ U)
  exact IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩

/-- **The fibres of the morphism of an ample free system carry no nontrivial specializations.**
If `x ⤳ y` in `X` and `φ(x) = φ(y)`, then `x = y`. -/
theorem eq_of_specializes_of_morphismOfGeneratingSections_eq
    (hL : Stacks.Ample.IsAmple X L) (ψ : V →ₗ[k] Γ(L, ⊤))
    (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) {x y : X} (hxy : x ⤳ y)
    (h : morphismOfGeneratingSections k V L ψ hψ x = morphismOfGeneratingSections k V L ψ hψ y) :
    x = y := by
  set φ := morphismOfGeneratingSections k V L ψ hψ
  have hy : y ∈ ⨆ v : V, nonvanishingOpen X L (ψ v) := by rw [hψ]; trivial
  obtain ⟨v, hv⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  set U := Proj.basicOpen (ProjectiveSpaceOfModule.symmetricGrading k V) (SymmetricAlgebra.ι k V v)
  have hpre : φ ⁻¹ᵁ U = nonvanishingOpen X L (ψ v) :=
    preimage_basicOpen_morphismOfGeneratingSections k V L ψ hψ v
  have hyU : y ∈ φ ⁻¹ᵁ U := hpre ▸ hv
  have hxU : x ∈ φ ⁻¹ᵁ U := hxy.mem_open (φ ⁻¹ᵁ U).isOpen hyU
  have := isFinite_morphismRestrict_basicOpen_morphismOfGeneratingSections hL ψ hψ v
  have hsp : (⟨x, hxU⟩ : φ ⁻¹ᵁ U) ⤳ ⟨y, hyU⟩ := (subtype_specializes_iff _ _).2 hxy
  have hbase : (φ ∣_ U) ⟨x, hxU⟩ = (φ ∣_ U) ⟨y, hyU⟩ :=
    Subtype.ext ((morphismRestrict_base_coe φ U ⟨x, hxU⟩).trans
      (h.trans (morphismRestrict_base_coe φ U ⟨y, hyU⟩).symm))
  exact congrArg Subtype.val (eq_of_specializes_of_base_eq_of_isIntegralHom (φ ∣_ U) hsp hbase)

/-- **The morphism of an ample free system does not lower dimension.** For `L` ample on a proper
`k`-scheme `X` and `ψ : V → Γ(X, L)` generating `L`, `dim X ≤ dim φ(X)`. -/
theorem topologicalKrullDim_le_range_morphismOfGeneratingSections
    (hL : Stacks.Ample.IsAmple X L) (ψ : V →ₗ[k] Γ(L, ⊤))
    (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) :
    topologicalKrullDim X ≤
      topologicalKrullDim (Set.range (morphismOfGeneratingSections k V L ψ hψ)) :=
  Topology.topologicalKrullDim_le_of_continuous_of_specializes_injective
    (Set.rangeFactorization (morphismOfGeneratingSections k V L ψ hψ))
    (morphismOfGeneratingSections k V L ψ hψ).continuous.rangeFactorization
    fun _ _ hxy h => eq_of_specializes_of_morphismOfGeneratingSections_eq hL ψ hψ hxy
      (congrArg Subtype.val h)

open MMP.Threefold.Bridges (systemSection) in
/-- **The image of an ample free system on a proper scheme of dimension at least two has
dimension at least two.** Let `X` be a proper `k`-scheme with `dim X ≥ 2`, `L` an ample invertible
module and `s₀, …, s_N` global sections of `L` generating it. Then the image of the morphism
`φ : X → ℙᴺ` they define has dimension at least two; this is the hypothesis `hdim` of
`MMP.Threefold.Bridges.exists_dense_open_geometricallyIntegral_zeroScheme`. -/
theorem two_le_topologicalKrullDim_range_morphismOfGeneratingSections {N : ℕ}
    (hL : Stacks.Ample.IsAmple X L) (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) = ⊤)
    (hX : 2 ≤ topologicalKrullDim X) :
    2 ≤ topologicalKrullDim
      (Set.range (morphismOfGeneratingSections k (Fin (N + 1) → k) L (systemSection s) hs)) :=
  hX.trans (topologicalKrullDim_le_range_morphismOfGeneratingSections (k := k)
    (V := Fin (N + 1) → k) hL (systemSection s) hs)

end MMP.Mori
