module

public import MMP.AlgebraicGeometry.Analytic.JacobianLogarithm.PicardLogCoordinates

/-!
# Countable covers of the restriction points of a curve Jacobian

Let `X` be a smooth projective surface over `ℂ`, `ι : C ⟶ X` a smooth connected projective curve
on it with a point `σ`, and `J` the Jacobian of `C`, representing degree-zero line bundles on `C`
rigidified along `σ` through `eJ`. A `ℂ`-point `x` of `J` is a *restriction point* when its
rigidified class is the restriction to `C` of a line bundle on `X`. These points are the image of
`Pic(X) → Pic(C)` meeting `Pic⁰(C)`, a countable union of translates of the image of `Pic⁰(X)`,
so they lie in countably many Zariski-closed subsets of `J` of dimension at most `h¹(X, 𝒪_X)`.

This file sets up the restriction points and proves the passage from countably many algebraic
families mapping to `J` to the cover of `exp(V)` by closed subsets that the rationality argument
uses, `V ⊆ H¹(C^an, 𝒪)` being the image of `H¹(X^an, 𝒪)`.

## Main definitions

* `MMP.Analytic.SurfaceHodge.IsRestrictionPoint`: the rigidified class of a `ℂ`-point of `J` is
  the restriction to `C` of a line bundle on `X`.

## Main results

* `MMP.Analytic.SurfaceHodge.exists_countable_isClosed_cover_of_families`: the closures of the
  images of countably many morphisms to `J`, each of dimension at most `d`, form a countable
  closed cover of every set of points lying in their images.
* `MMP.Analytic.SurfaceHodge.exists_countable_isClosed_cover_of_isRestrictionPoint`: if the
  restriction points lie in the images of countably many morphisms whose image closures have
  dimension at most `h¹(X, 𝒪_X)`, if `Φ(V)` consists of restriction points and
  `h¹(X, 𝒪_X) ≤ dim V`, then `Φ(V)` is covered by countably many closed subsets of `J` of
  dimension at most `dim V`.

## Implementation notes

The class of a `ℂ`-point `x` is `eJ` applied to `x` viewed as an `Spec ℂ`-point of `J`; it is a
degree-zero rigidified class on `C ×_ℂ Spec ℂ`, compared with the pullback of a class of `X`
along `C ×_ℂ Spec ℂ ⟶ C ⟶ X`. Over the field `ℂ` every class of `C` is rigidified, since the
Picard group of `Spec ℂ` is trivial.

## References

* [D. Mumford, *Lectures on curves on an algebraic surface*], Lecture 19.
* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][griffithsharris1978], Ch. 2 §6.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MMP.Analytic MMP.Analytic.ComplexPoints

namespace MMP.Analytic.SurfaceHodge

/-- A `ℂ`-point `x` of the Jacobian `JX` of the curve `C` (representing the degree-zero
rigidified Picard functor through `eJ`) is a **restriction point** of `ι : C ⟶ X` when its class
is the restriction to `C` of a line bundle on `X`. -/
def IsRestrictionPoint {X C : Scheme.{0}} (ι : C ⟶ X) (f : C ⟶ Spec (.of ℂ)) [IsProper f]
    (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥(f.fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ f = 𝟙 _) {JX : Grp (Over (Spec (.of ℂ)))}
    (eJ : yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero f hdim σ hσ)
    (x : ComplexPoints JX.X.hom) : Prop :=
  ∃ y : Stacks.Picard.ofScheme X,
    Stacks.Picard.schemePullbackClass (pullback.fst f (𝟙 _) ≫ ι) y =
      Stacks.RigidifiedPicard.smallEquiv _
        (Multiplicative.toAdd ((eJ.hom.app (op (Over.mk (𝟙 _)))).hom
          (Over.homMk x.1 x.2))).1.1

/-- **Countable closed covers from families.** If every point of `S` lies in the image of one of
countably many morphisms `g k : T k ⟶ Y` whose image closures have dimension at most `d`, then
these closures are countably many closed subsets of `Y` of dimension at most `d` covering `S`. -/
theorem exists_countable_isClosed_cover_of_families {Y : Scheme.{0}} {κ : Type} [Countable κ]
    {T : κ → Scheme.{0}} (g : ∀ k, T k ⟶ Y) {d : WithBot ℕ∞}
    (hg : ∀ k, topologicalKrullDim (closure (Set.range (g k).base)) ≤ d) {S : Set Y}
    (hS : S ⊆ ⋃ k, Set.range (g k).base) :
    ∃ (κ' : Type) (_ : Countable κ') (T' : κ' → Set Y), (∀ k, IsClosed (T' k)) ∧
      (∀ k, topologicalKrullDim (T' k) ≤ d) ∧ S ⊆ ⋃ k, T' k :=
  ⟨κ, inferInstance, fun k => closure (Set.range (g k).base), fun _ => isClosed_closure,
    hg, hS.trans (Set.iUnion_mono fun _ => subset_closure)⟩

/-- **The cover of `Φ(V)` from the restriction points.** Let `ι : C ⟶ X` be a curve on a smooth
projective surface, `JX` the Jacobian of `C`, `Φ : ℂⁿ → JX(ℂ)` a map and `V ⊆ ℂⁿ` a complex
subspace. Suppose
* the restriction points of `JX` lie in the images of countably many morphisms `g k : T k ⟶ JX`
  whose image closures have dimension at most `h¹(X, 𝒪_X)`;
* `Φ v` is a restriction point for every `v ∈ V`;
* `h¹(X, 𝒪_X) ≤ dim V`.

Then `Φ(V)` is covered by countably many closed subsets of `JX` of dimension at most `dim V`.
The curve is assumed proper over `ℂ`. -/
theorem exists_countable_isClosed_cover_of_isRestrictionPoint {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))] {C : Scheme.{0}} (ι : C ⟶ X)
    [IsClosedImmersion ι] [IsProper (ι ≫ (X ↘ Spec (.of ℂ)))]
    [SmoothOfRelativeDimension 1 (ι ≫ (X ↘ Spec (.of ℂ)))] [ConnectedSpace C]
    (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥((ι ≫ (X ↘ Spec (.of ℂ))).fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ ι ≫ (X ↘ Spec (.of ℂ)) = 𝟙 _)
    {JX : Grp (Over (Spec (.of ℂ)))}
    (eJ : yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero _ hdim σ hσ)
    {κ : Type} [Countable κ] {T : κ → Scheme.{0}} (g : ∀ k, T k ⟶ JX.X.left)
    (hg : ∀ k, topologicalKrullDim (closure (Set.range (g k).base)) ≤
      Module.finrank ℂ (cohomologyOverField ℂ (X ↘ Spec (.of ℂ))
        (SheafOfModules.unit X.ringCatSheaf) 1))
    (hres : ∀ x : ComplexPoints JX.X.hom, IsRestrictionPoint ι _ hdim σ hσ eJ x →
      x.toScheme ∈ ⋃ k, Set.range (g k).base)
    {n : ℕ} (Φ : (Fin n → ℂ) → ComplexPoints JX.X.hom) (V : Submodule ℂ (Fin n → ℂ))
    (hΦ : ∀ v ∈ V, IsRestrictionPoint ι _ hdim σ hσ eJ (Φ v))
    (hV : Module.finrank ℂ (cohomologyOverField ℂ (X ↘ Spec (.of ℂ))
      (SheafOfModules.unit X.ringCatSheaf) 1) ≤ Module.finrank ℂ V) :
    ∃ (κ' : Type) (_ : Countable κ') (T' : κ' → Set JX.X.left), (∀ k, IsClosed (T' k)) ∧
      (∀ k, topologicalKrullDim (T' k) ≤ Module.finrank ℂ V) ∧
      ∀ v ∈ V, (Φ v).toScheme ∈ ⋃ k, T' k := by
  have hd : ((Module.finrank ℂ (cohomologyOverField ℂ (X ↘ Spec (.of ℂ))
      (SheafOfModules.unit X.ringCatSheaf) 1) : ℕ) : WithBot ℕ∞) ≤
      ((Module.finrank ℂ V : ℕ) : WithBot ℕ∞) := by exact_mod_cast hV
  obtain ⟨κ', hκ', T', hT', hdT', hcov⟩ := exists_countable_isClosed_cover_of_families g
    (fun k => (hg k).trans hd)
    (S := {y | ∃ v ∈ V, (Φ v).toScheme = y})
    (by rintro _ ⟨v, hv, rfl⟩; exact hres _ (hΦ v hv))
  exact ⟨κ', hκ', T', hT', hdT', fun v hv => hcov ⟨v, hv, rfl⟩⟩

end MMP.Analytic.SurfaceHodge
