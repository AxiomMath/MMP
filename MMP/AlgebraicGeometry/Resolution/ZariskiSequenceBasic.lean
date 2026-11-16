module

public import MMP.Attr
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowUp

/-!
# Zariski sequences of blow-ups

Let `R` be a local ring with closed point `y` of `Spec R`, and `f : Spec R ⟶ X` a morphism of
schemes. A *Zariski sequence* for `f` is a sequence `(Xᵢ, βᵢ, fᵢ)_{i ≥ 0}` with `X₀ = X`,
`f₀ = f`, and for every `i`: `Uᵢ ⊆ Xᵢ` is an open containing the point `xᵢ = fᵢ(y)`,
`Zᵢ ⊆ Uᵢ` is the reduced closed subscheme on the closure of `xᵢ` in `Uᵢ`, `Xᵢ₊₁ = Bl_{Zᵢ} Uᵢ`
with blow-up morphism `βᵢ : Xᵢ₊₁ ⟶ Uᵢ ⊆ Xᵢ`, and `fᵢ₊₁ : Spec R ⟶ Xᵢ₊₁` is a morphism with
`fᵢ₊₁ ≫ βᵢ = fᵢ`. Kollár–Mori take every `Uᵢ = Xᵢ`.

The case of interest is that of a discrete valuation ring `R ⊆ k(X)` with fraction field the
function field of an integral scheme `X`, dominating the local ring `𝒪_{x₀,X}` of a point `x₀`;
then `f` is the composite `Spec R ⟶ Spec 𝒪_{x₀,X} ⟶ X`, which is `MMP.Mori.fromSpecOfStalkLE`.

## Main definitions

* `MMP.Mori.centerIdeal`: for `g : Spec R ⟶ Y`, the ideal sheaf of the reduced closed subscheme
  on the closure of the image of the closed point.
* `MMP.Mori.fromSpecOfStalkLE`: the morphism `Spec R ⟶ Spec 𝒪_{x₀,X} ⟶ X` of a subring `R` of
  the function field containing the image of `𝒪_{x₀,X}`.
* `MMP.Mori.ZariskiSequence`: a Zariski sequence for a morphism `f : Spec R ⟶ X`.
* `MMP.Mori.ZariskiSequence.β`: the blow-up morphisms `βᵢ : Xᵢ₊₁ ⟶ Xᵢ`.

## Main results

* `MMP.Mori.ZariskiSequence.mor_closedPoint_mem`: `xᵢ ∈ Uᵢ`.
* `MMP.Mori.ZariskiSequence.mor_succ_comp_β`: `fᵢ₊₁ ≫ βᵢ = fᵢ`.

## Implementation notes

The schemes `Xᵢ` are given together with equalities `X₀ = X` and
`Xᵢ₊₁ = Bl_{Zᵢ} Uᵢ`, transported along `eqToHom`; the blow-up is
`AlgebraicGeometry.blowUp` (Stacks Tag 01OG) of the vanishing ideal
`Scheme.IdealSheafData.vanishingIdeal` of the closure, whose quotient is the reduced induced
structure.

Kollár–Mori blow up all of `Xᵢ`. Allowing an open `Uᵢ` through which `fᵢ` factors is more
general and costs nothing: the local rings at the points `xᵢ`, on which Zariski's argument runs,
are those of `Uᵢ`, since an open immersion induces isomorphisms of stalks.

The definition of the sequence uses only the morphism `f` and the closed point of `Spec R`, so it
is stated for an arbitrary local ring `R` and an arbitrary morphism `f`. The hypotheses that `R` is
a discrete valuation ring with fraction field `k(X)`, that `R` contains the ground field, and that
the inclusion `𝒪_{x₀,X} ⊆ R` is local, are not needed to state it; `MMP.Mori.fromSpecOfStalkLE`
only uses that `R` contains the image of `𝒪_{x₀,X}`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, Lemma 2.45]
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace MMP.Mori

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- For a morphism `g : Spec R ⟶ Y` from the spectrum of a local ring, the ideal sheaf of the
reduced closed subscheme of `Y` on the closure of the image of the closed point. This is the
centre of the blow-up in a Zariski sequence. -/
def centerIdeal {Y : Scheme.{u}} (g : Spec (.of R) ⟶ Y) : Y.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {g (IsLocalRing.closedPoint R)})

/-- The support of the centre ideal of `g` is the closure of the image of the closed point. -/
theorem support_centerIdeal {Y : Scheme.{u}} (g : Spec (.of R) ⟶ Y) :
    ((centerIdeal g).support : Set Y) = closure {g (IsLocalRing.closedPoint R)} := by
  simp [centerIdeal]

/-- For an irreducible scheme `X`, a point `x₀`, and a subring `R` of the function field `k(X)`
containing the image of the local ring `𝒪_{x₀,X}`, the morphism
`Spec R ⟶ Spec 𝒪_{x₀,X} ⟶ X` induced by the inclusion `𝒪_{x₀,X} ⟶ R`. -/
@[mmp "def_km1a_zariski_sequence"]
def fromSpecOfStalkLE {X : Scheme.{u}} [IrreducibleSpace X] (x₀ : X)
    (S : Subring X.functionField)
    (hS : ∀ s : X.presheaf.stalk x₀, algebraMap (X.presheaf.stalk x₀) X.functionField s ∈ S) :
    Spec (.of S) ⟶ X :=
  Spec.map (CommRingCat.ofHom ((algebraMap (X.presheaf.stalk x₀) X.functionField).codRestrict
    S hS)) ≫ X.fromSpecStalk x₀

/-- A *Zariski sequence* for a morphism `f : Spec R ⟶ X` from the spectrum of a local ring: schemes
`Xᵢ` (`obj i`) and morphisms `fᵢ : Spec R ⟶ Xᵢ` (`mor i`) with `X₀ = X`, `f₀ = f`, opens
`Uᵢ ⊆ Xᵢ` (`U i`) through which `fᵢ` factors, each `Xᵢ₊₁` the blow-up of `Uᵢ` in the reduced
closure of `fᵢ` of the closed point, and `fᵢ₊₁` a lift of `fᵢ` along the blow-up morphism
`Xᵢ₊₁ ⟶ Uᵢ ⊆ Xᵢ`. Taking every `Uᵢ = Xᵢ` gives the sequences of Kollár–Mori, Lemma 2.45. -/
@[mmp "def_km1a_zariski_sequence"]
structure ZariskiSequence (X : Scheme.{u}) (f : Spec (.of R) ⟶ X) where
  /-- The scheme `Xᵢ`. -/
  obj : ℕ → Scheme.{u}
  /-- The morphism `fᵢ : Spec R ⟶ Xᵢ`. -/
  mor : ∀ i, Spec (.of R) ⟶ obj i
  /-- `X₀ = X`. -/
  obj_zero : obj 0 = X
  /-- `f₀ = f`. -/
  mor_zero : mor 0 ≫ eqToHom obj_zero = f
  /-- The open `Uᵢ ⊆ Xᵢ` that is blown up. -/
  U : ∀ i, (obj i).Opens
  /-- The morphism `fᵢ`, as a morphism `Spec R ⟶ Uᵢ`. -/
  morOpen : ∀ i, Spec (.of R) ⟶ U i
  /-- `fᵢ` factors through `Uᵢ`. -/
  morOpen_ι : ∀ i, morOpen i ≫ (U i).ι = mor i
  /-- `Xᵢ₊₁` is the blow-up of `Uᵢ` in the reduced closure of `fᵢ(y)`. -/
  obj_succ : ∀ i, obj (i + 1) = blowUp (centerIdeal (morOpen i))
  /-- `fᵢ₊₁` lifts `fᵢ` along the blow-up morphism. -/
  mor_succ_comp : ∀ i,
    mor (i + 1) ≫ eqToHom (obj_succ i) ≫ blowUpToBase (centerIdeal (morOpen i)) = morOpen i

namespace ZariskiSequence

attribute [reassoc (attr := simp)] morOpen_ι mor_succ_comp

variable {X : Scheme.{u}} {f : Spec (.of R) ⟶ X} (S : ZariskiSequence X f)

/-- The image `fᵢ(y)` of the closed point lies in `Uᵢ`. -/
theorem mor_closedPoint_mem (i : ℕ) : S.mor i (IsLocalRing.closedPoint R) ∈ S.U i := by
  rw [← S.morOpen_ι]
  exact ((S.morOpen i) (IsLocalRing.closedPoint R)).2

/-- The blow-up morphism `βᵢ : Xᵢ₊₁ ⟶ Uᵢ ⊆ Xᵢ` of a Zariski sequence. -/
def β (i : ℕ) : S.obj (i + 1) ⟶ S.obj i :=
  eqToHom (S.obj_succ i) ≫ blowUpToBase (centerIdeal (S.morOpen i)) ≫ (S.U i).ι

/-- `βᵢ` is the composite `Xᵢ₊₁ = Bl(Uᵢ) ⟶ Uᵢ ⟶ Xᵢ` of the blow-up morphism and the open
immersion. -/
theorem β_eq (i : ℕ) : S.β i =
    eqToHom (S.obj_succ i) ≫ blowUpToBase (centerIdeal (S.morOpen i)) ≫ (S.U i).ι := rfl

/-- `fᵢ₊₁ ≫ βᵢ = fᵢ`. -/
@[reassoc (attr := simp)]
theorem mor_succ_comp_β (i : ℕ) : S.mor (i + 1) ≫ S.β i = S.mor i := by
  simp [β]

end ZariskiSequence

end MMP.Mori
