module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs
public import StacksFrontier.AlgebraicGeometry.Curves.LargeDegreeVanishing
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ExceptionalComponentsMeet
public import StacksFrontier.AlgebraicGeometry.InvertibleModuleEndomorphismOverField

/-!
# Global functions and automorphisms of invertible sheaves after base change of a curve

Let `X` be a quasi-compact quasi-separated scheme over a field `k` whose ring of global functions
is `k`, that is `k ⟶ Γ(X, 𝒪_X)` is an isomorphism (for `X` integral and proper over an
algebraically closed field this is `AlgebraicGeometry.finrank_globalSections_eq_one`).

## Main results

* `MMP.Fourfold.isIso_constants_baseChange`: for every flat `k`-algebra `A`, the base change
  `X_A` again has global functions `A`, that is `A ⟶ Γ(X_A, 𝒪)` is an isomorphism. The proof is
  the flat base change of global sections along `k ⟶ A`, Mathlib's
  `AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`. In particular, over
  a field `k`, it holds for every field extension `K ⊇ k` and every local Artinian `k`-algebra.
* `MMP.Fourfold.isIso_constants_baseChange_of_isProper_isIntegral`: the same for `X` integral and
  proper over an algebraically closed field `k`.
* `MMP.Fourfold.exists_units_smul_id_of_iso_of_isInvertible`: over a field `K` with global
  functions `K`, every automorphism of an invertible sheaf is multiplication by a unit of `K`.
* `MMP.Fourfold.exists_units_smul_id_of_isInvertible_baseChange`: the composite, for an
  automorphism of an invertible sheaf on `X_K`, `X` integral and proper over `k = k̄`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Fourfold

/-- **Global functions are unchanged by flat base change.** If `X` is quasi-compact and
quasi-separated over a commutative ring `k` and `k ⟶ Γ(X, 𝒪_X)` is an isomorphism, then for
every flat `k`-algebra `A` and every base change `q : Y ⟶ Spec A` of `X`, `A ⟶ Γ(Y, 𝒪_Y)` is an
isomorphism. -/
theorem isIso_constants_baseChange {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    [Module.Flat k A]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (p : Y ⟶ X) (q : Y ⟶ Spec (.of A))
    (h : IsPullback p q f (Spec.map (CommRingCat.ofHom (algebraMap k A))))
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] :
    IsIso ((Scheme.ΓSpecIso (.of A)).inv ≫ q.appTop) := by
  have hfl : Flat (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
    Flat.SpecMap_iff.mpr (by
      show (algebraMap k A).Flat
      rw [RingHom.flat_algebraMap_iff]; infer_instance)
  have hc : IsCompact (⊤ : X.Opens).1 := by
    have := (quasiCompact_iff_compactSpace f).mp inferInstance
    exact isCompact_univ
  have hqs : IsQuasiSeparated (⊤ : X.Opens).1 := by
    have := (quasiSeparated_iff_quasiSeparatedSpace f).mp inferInstance
    exact isQuasiSeparated_univ
  have hiso := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right h (UY := ⊤)
    (by simp) (by simp) (by simp) (isAffineOpen_top _) (isAffineOpen_top _) hc hqs
  have hP := (isIso_pushoutSection_iff h _ _ _).mp hiso
  have key : ∀ {V W : Scheme.{u}} (m : V ⟶ W) (e : (⊤ : V.Opens) ≤ m ⁻¹ᵁ (⊤ : W.Opens)),
      m.appLE ⊤ ⊤ e = m.appTop := fun m _ => m.appLE_eq_app
  have e2 := hP.isIso_inr_of_isIso (inst := Eq.mpr (congrArg IsIso (key f _))
    (IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv _))
  have e3 : IsIso q.appTop := Eq.mp (congrArg IsIso (key q _)) e2
  exact IsIso.comp_isIso

/-- Under the hypotheses of `MMP.Fourfold.isIso_constants_baseChange`, the structure map
`A → Γ(Y, 𝒪_Y)` is bijective. -/
theorem bijective_constants_baseChange {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    [Module.Flat k A]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (p : Y ⟶ X) (q : Y ⟶ Spec (.of A))
    (h : IsPullback p q f (Spec.map (CommRingCat.ofHom (algebraMap k A))))
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] :
    Function.Bijective ((Scheme.ΓSpecIso (.of A)).inv ≫ q.appTop).hom :=
  (ConcreteCategory.isIso_iff_bijective _).mp (isIso_constants_baseChange f p q h)

/-- **`H⁰(X_A, 𝒪) = A` for `X` integral and proper over an algebraically closed field.** Here `X`
integral and proper over `k = k̄` has `Γ(X, 𝒪) = k`
(`AlgebraicGeometry.finrank_globalSections_eq_one`), and `A` is any `k`-algebra, e.g. a field
extension `K ⊇ k` or a local Artinian `k`-algebra. -/
theorem isIso_constants_baseChange_of_isProper_isIntegral
    {k A : Type u} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsIntegral X]
    (p : Y ⟶ X) (q : Y ⟶ Spec (.of A))
    (h : IsPullback p q f (Spec.map (CommRingCat.ofHom (algebraMap k A)))) :
    IsIso ((Scheme.ΓSpecIso (.of A)).inv ≫ q.appTop) := by
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) :=
    Stacks.Models.isIso_constants_of_finrank_globalSections_eq_one f
      (finrank_globalSections_eq_one k f)
  exact isIso_constants_baseChange f p q h

/-- **Automorphisms of an invertible sheaf are the unit scalars.** Let `q : Y ⟶ Spec K` be a scheme
over a field whose global functions are `K`, and `L` an invertible `𝒪_Y`-module. Every
automorphism of `L` is multiplication by a unit `c ∈ Kˣ`, for the `K`-linear structure
`AlgebraicGeometry.modulesLinearOverField` on `𝒪_Y`-modules. -/
theorem exists_units_smul_id_of_iso_of_isInvertible
    (K : Type u) [Field K] {Y : Scheme.{u}} (q : Y ⟶ Spec (.of K))
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appTop)]
    (L : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] (φ : L ≅ L) :
    letI := modulesLinearOverField K q
    ∃ c : Kˣ, φ.hom = (c : K) • 𝟙 L := by
  letI := modulesLinearOverField K q
  obtain ⟨c, hc⟩ := exists_eq_smul_id_of_isInvertible K q L φ.hom
  obtain ⟨d, hd⟩ := exists_eq_smul_id_of_isInvertible K q L φ.inv
  have hne := id_ne_zero_of_isInvertible K q L
  have h1 : (c * d) • 𝟙 L = (1 : K) • 𝟙 L := by
    have := φ.hom_inv_id
    rw [hc, hd, Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul] at this
    rw [one_smul]; exact this
  have h2 : (d * c) • 𝟙 L = (1 : K) • 𝟙 L := by
    have := φ.inv_hom_id
    rw [hc, hd, Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul] at this
    rw [one_smul]; exact this
  exact ⟨⟨c, d, smul_left_injective K hne h1, smul_left_injective K hne h2⟩, hc⟩

/-- **Automorphisms of an invertible sheaf on `X_K` are multiplication by a unit of `K`.** Let `X`
be integral and proper over an algebraically closed field `k`, `K ⊇ k` a field extension and
`Y = X_K`. Every automorphism of an invertible `𝒪_Y`-module is multiplication by some `c ∈ Kˣ`,
for the `K`-linear structure `AlgebraicGeometry.modulesLinearOverField`. -/
theorem exists_units_smul_id_of_isInvertible_baseChange
    {k K : Type u} [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsIntegral X]
    (p : Y ⟶ X) (q : Y ⟶ Spec (.of K))
    (h : IsPullback p q f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (L : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] (φ : L ≅ L) :
    letI := modulesLinearOverField K q
    ∃ c : Kˣ, φ.hom = (c : K) • 𝟙 L :=
  haveI := isIso_constants_baseChange_of_isProper_isIntegral f p q h
  exists_units_smul_id_of_iso_of_isInvertible K q L φ

end MMP.Fourfold

end
