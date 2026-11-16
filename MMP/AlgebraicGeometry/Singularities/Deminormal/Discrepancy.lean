/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.Singularities.Deminormal.Dualizing
public import MMP.AlgebraicGeometry.Singularities.Semismooth.Defs
public import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
public import MMP.AlgebraicGeometry.Singularities.LogResolution.Basic

/-!
# Discrepancies over schemes satisfying (2.6.1)

Let `X` be a scheme of finite type and pure dimension `n` over a field `k` satisfying (2.6.1):
reduced, and at every point of codimension one either regular or with two regular branches
meeting transversally. Let `X° ⊆ X` be an open set containing every point of codimension `≤ 1`
on which the dualizing sheaf `ω_X` is invertible; its complement has codimension `≥ 2`
(`MMP.Flips.two_le_closedsCodimension_compl`). Let `ω` be a rational section of `ω_{X°}`,
generating it at every generic point of `X`, `K_X` the closure in `X` of its divisor of zeros and
poles on `X°`, and `D_X` an `ℝ`-divisor on `X` no component of which lies in the singular locus,
with `K_X + D_X = ∑ⱼ rⱼ Lⱼ` for Cartier divisors `Lⱼ` on `X`. For a proper morphism `f : Y ⟶ X`
birational in the sense of (2.6.2) and a prime divisor `E` of `Y` with `codim_X f(E) ≥ 2`, the
pull-back `f^*ω` is a rational section of `ω_Y` near the generic point of `E`, where `Y` is
regular, and `f^*Lⱼ` is defined since `f` is an isomorphism at the generic points. The
*discrepancy* `a(E, D_X)` is the coefficient of `E` in `div(f^*ω) - ∑ⱼ rⱼ f^*Lⱼ`.

The local rings of `X` at its codimension-one points need not be domains: at a double-crossing
point the completion is `κ[[u, v]]/(uv)`. Orders of vanishing are therefore lengths,
`ord(a) = length(𝒪/a𝒪)` (`Ring.ord`), additive on non-zero-divisors, and the order of `a/b` is
`ord(a) - ord(b)`.

## Main definitions

* `MMP.Flips.IsLocalGenerator`: a section `g` of an `𝒪_X`-module over `V` such that
  `r ↦ r · g` is an isomorphism `𝒪_V ≅ ℱ|_V`.
* `MMP.Flips.IsOrderOfSectionAt`: the order at a point `ξ` of a section `s` of an `𝒪_X`-module
  invertible near `ξ`: `ord_ξ(a) - ord_ξ(b)`, where `b · s = a · g` near `ξ` for a local
  generator `g`.
* `MMP.Flips.IsInvertibleBigOpen`: the admissible choices of `X°`.
* `MMP.Flips.pullbackSection`: the pull-back `f^*s` of a section of `ω_X`, through an isomorphism
  of `ω_Y` with `ω_X` over an open set where `f` is an isomorphism.
* `MMP.Flips.IsNonnormalDiscrepancyWith`: `a = a(E, D_X)` computed with the choices of `X°`, `ω`,
  `K_X`, the presentation `K_X + D_X = ∑ⱼ rⱼ Lⱼ`, the open set `U` over which `f` is an
  isomorphism and the isomorphism `ω_Y|_{f⁻¹U} ≅ ω_X|_U`.
* `MMP.Flips.IsNonnormalDiscrepancy`: `a = a(E, D_X)` for some such choices.

## Main results

* `MMP.Flips.isNonnormalDiscrepancyWith_iff_of_isInvertibleBigOpen`: the discrepancy does not
  depend on the choice of `X°`.

## Implementation notes

FA takes for `X°` the set of points that are regular or of the form (2.6.1). The openness of this
set is not available here, so `X°` is any open set containing every point of codimension `≤ 1`
on which `ω_X` is invertible (`MMP.Flips.IsInvertibleBigOpen`); the regular and double-crossing
points satisfy the second condition
(`MMP.Flips.IsDualizingSheaf.exists_restrict_iso_free_of_mem_doubleCrossingLocus`), and the
points of codimension `≤ 1` are regular or double-crossing points
(`MMP.Flips.mem_doubleCrossingLocus_of_coheight_le_one`). The set `X°` enters only through the
rational section `ω`, a section over an open `W ⊆ X°`;
`MMP.Flips.isNonnormalDiscrepancyWith_iff_of_isInvertibleBigOpen` shows that the discrepancy
computed on `X°₁` with `ω` is the one computed on `X°₂` with `ω|_{W ∩ X°₂}`.

The order of a section at a point `ξ` is computed on an open neighbourhood `V` of `ξ` carrying a
local generator `g`: for `a, b ∈ 𝒪(V)` with non-zero-divisor germs at `ξ`, `b · s = a · g` on an
open `V' ⊆ V ∩ W` containing every generic point of `X` that specializes to `ξ`. Since `X` is
reduced, a function on `V` vanishing on `V'` has zero germ at `ξ`, so the order does not depend
on the choices. The pull-back `f^*ω` is a section of `ω_Y` over `f⁻¹(W ∩ U)`, which contains the
generic points of `Y`; since `U` contains the points of codimension `≤ 1`, changing `ψ` changes
`f^*ω` by a unit of `𝒪(f⁻¹U)` whose order along `E` is zero.

The `Lⱼ` are Cartier divisors in the sense of `𝒦_X^*/𝒪_X^*`
(`AlgebraicGeometry.Scheme.CartierDivisor`), with Weil divisors
`MMP.Intersection.IsWeilDivisorOfCartier` and pull-backs `MMP.Intersection.IsPullback`: `X` and
`Y` are not normal, and on a non-normal scheme a Cartier divisor is not determined by its Weil
divisor, nor is `f^*Lⱼ`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.6, 16.3.3
* [Stacks Project, Tag 02MD](https://stacks.math.columbia.edu/tag/02MD)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.Flips

open MMP.Mori

/-! ### Orders of sections of invertible modules -/

section Order

variable {X : Scheme.{u}}

/-- A section `g ∈ Γ(V, ℱ)` of an `𝒪_X`-module is a *local generator* of `ℱ` on `V` if
`r ↦ r · g|_{V'}` is a bijection `Γ(V', 𝒪_X) → Γ(V', ℱ)` for every open `V' ⊆ V`, i.e.
`r ↦ r · g` is an isomorphism `𝒪_V ≅ ℱ|_V`. -/
def IsLocalGenerator (ℱ : X.Modules) {V : X.Opens} (g : Γ(ℱ, V)) : Prop :=
  ∀ (V' : X.Opens) (h : V' ≤ V),
    Function.Bijective fun r : Γ(X, V') => r • ℱ.presheaf.map (homOfLE h).op g

/-- **The order of a section at a point.** Let `ℱ` be an `𝒪_X`-module, `s ∈ Γ(W, ℱ)` and `ξ ∈ X`.
The integer `n` is *the order of `s` at `ξ`* if there are an open neighbourhood `V` of `ξ`, a local
generator `g` of `ℱ` on `V`, sections `a, b ∈ Γ(V, 𝒪_X)` whose germs at `ξ` are
non-zero-divisors, and an open `V' ⊆ V ∩ W` containing every generic point of `X` specializing to
`ξ`, with `b · s = a · g` on `V'` and `n = ord_ξ(a) - ord_ξ(b)`, where `ord_ξ(a)` is the (finite)
length of `𝒪_{X,ξ}/a𝒪_{X,ξ}`. That is, `s = (a/b) · g` near `ξ`. -/
def IsOrderOfSectionAt (ℱ : X.Modules) {W : X.Opens} (s : Γ(ℱ, W)) (ξ : X) (n : ℤ) : Prop :=
  ∃ (V : X.Opens) (hξ : ξ ∈ V) (g : Γ(ℱ, V)) (a b : Γ(X, V)) (V' : X.Opens) (hV' : V' ≤ V)
    (hW : V' ≤ W),
    IsLocalGenerator ℱ g ∧
    (∀ η : X, closure {η} ∈ irreducibleComponents X → η ⤳ ξ → η ∈ V') ∧
    X.presheaf.germ V ξ hξ a ∈ nonZeroDivisors (X.presheaf.stalk ξ) ∧
    X.presheaf.germ V ξ hξ b ∈ nonZeroDivisors (X.presheaf.stalk ξ) ∧
    X.presheaf.map (homOfLE hV').op b • ℱ.presheaf.map (homOfLE hW).op s =
      X.presheaf.map (homOfLE hV').op a • ℱ.presheaf.map (homOfLE hV').op g ∧
    ∃ la lb : ℕ, Ring.ord (X.presheaf.stalk ξ) (X.presheaf.germ V ξ hξ a) = la ∧
      Ring.ord (X.presheaf.stalk ξ) (X.presheaf.germ V ξ hξ b) = lb ∧ n = la - lb

/-- Composing two restriction maps of `𝒪_X`. -/
theorem presheaf_map_map {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op x) =
      X.presheaf.map (homOfLE (le_trans h₂ h₁)).op x :=
  TopCat.Presheaf.restrict_restrict h₂ h₁ x

/-- The restriction of a local generator is a local generator. -/
theorem IsLocalGenerator.restrict {ℱ : X.Modules} {V V₀ : X.Opens} {g : Γ(ℱ, V)}
    (hg : IsLocalGenerator ℱ g) (h : V₀ ≤ V) :
    IsLocalGenerator ℱ (ℱ.presheaf.map (homOfLE h).op g) :=
  fun (V' : X.Opens) (h' : V' ≤ V₀) => by
    simpa only [Intersection.modules_map_map] using hg V' (le_trans h' h)

/-- The order of a section at `ξ` is unchanged by restriction to an open set containing every
generic point of `X` specializing to `ξ`. -/
theorem isOrderOfSectionAt_restrict_iff {ℱ : X.Modules} {W W₀ : X.Opens} (s : Γ(ℱ, W))
    (h : W₀ ≤ W) {ξ : X}
    (hgen : ∀ η : X, closure {η} ∈ irreducibleComponents X → η ⤳ ξ → η ∈ W₀) (n : ℤ) :
    IsOrderOfSectionAt ℱ (ℱ.presheaf.map (homOfLE h).op s) ξ n ↔ IsOrderOfSectionAt ℱ s ξ n := by
  constructor
  · rintro ⟨V, hξ, g, a, b, V', hV', hW, hg, hgen', ha, hb, heq, hord⟩
    refine ⟨V, hξ, g, a, b, V', hV', le_trans hW h, hg, hgen', ha, hb, ?_, hord⟩
    rwa [Intersection.modules_map_map] at heq
  · rintro ⟨V, hξ, g, a, b, V', hV', hW, hg, hgen', ha, hb, heq, hord⟩
    refine ⟨V, hξ, g, a, b, V' ⊓ W₀, le_trans inf_le_left hV', inf_le_right, hg,
      fun η h1 h2 => ⟨hgen' η h1 h2, hgen η h1 h2⟩, ha, hb, ?_, hord⟩
    have := congrArg (ℱ.presheaf.map (homOfLE (inf_le_left : V' ⊓ W₀ ≤ V')).op) heq
    simp only [Scheme.Modules.map_smul, Intersection.modules_map_map, presheaf_map_map] at this
    rwa [Intersection.modules_map_map]

/-- A morphism of `𝒪_X`-modules commutes with restriction of sections. -/
theorem modulesHom_app_map {M N : X.Modules} (φ : M ⟶ N)
    {U V : X.Opens} (h : V ≤ U) (x : Γ(M, U)) :
    φ.app V (M.presheaf.map (homOfLE h).op x) = N.presheaf.map (homOfLE h).op (φ.app U x) :=
  NatTrans.naturality_apply φ.mapPresheaf (homOfLE h).op x

/-- An open set `X°` is an *admissible choice of `X°`* for the `𝒪_X`-module `ω` (FA Remark 2.6)
if it contains every point of codimension `≤ 1` and `ω` is free of rank one on a neighbourhood of
each of its points. -/
def IsInvertibleBigOpen (ω : X.Modules) (Xo : X.Opens) : Prop :=
  (∀ x : X, Order.coheight x ≤ 1 → x ∈ Xo) ∧
    ∀ x ∈ Xo, ∃ (V : X.Opens) (_ : x ∈ V),
      Nonempty (ω.restrict V.ι ≅ SheafOfModules.free.{u} (ULift.{u} (Fin 1)))

end Order

/-! ### Pull-backs of sections -/

section Pullback

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- **The pull-back of a section.** Let `f : Y ⟶ X` restrict to an isomorphism
`f⁻¹(U) ⟶ U` and let `ψ : ω_Y|_{f⁻¹U} ≅ ω_X|_U` (restriction along the open immersion
`f⁻¹(U) ⟶ U ⟶ X`). The pull-back of `s ∈ Γ(W, ω_X)` is the section `ψ⁻¹(s|_{W ∩ U})` of `ω_Y`
over `f⁻¹(W ∩ U)`. -/
def pullbackSection {U : X.Opens} [IsIso (f ∣_ U)] {ωX : X.Modules} {ωY : Y.Modules}
    (ψ : ωY.restrict (f ⁻¹ᵁ U).ι ≅ ωX.restrict (f ∣_ U ≫ U.ι)) {W : X.Opens} (s : Γ(ωX, W)) :
    Γ(ωY, (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U ≫ U.ι) ⁻¹ᵁ W)) :=
  (ωY.restrictAppIso _ _).hom (ψ.inv.app _ ((ωX.restrictAppIso _ _).inv
    (ωX.presheaf.map (homOfLE ((f ∣_ U ≫ U.ι).image_preimage_le W)).op s)))

/-- The pull-back of a restriction is the restriction of the pull-back. -/
theorem pullbackSection_restrict {U : X.Opens} [IsIso (f ∣_ U)] {ωX : X.Modules}
    {ωY : Y.Modules} (ψ : ωY.restrict (f ⁻¹ᵁ U).ι ≅ ωX.restrict (f ∣_ U ≫ U.ι))
    {W W₀ : X.Opens} (h : W₀ ≤ W) (s : Γ(ωX, W)) :
    pullbackSection f ψ (ωX.presheaf.map (homOfLE h).op s) =
      ωY.presheaf.map (homOfLE (Scheme.Hom.image_mono _ (Scheme.Hom.preimage_mono _ h))).op
        (pullbackSection f ψ s) := by
  have key := modulesHom_app_map ψ.inv (Scheme.Hom.preimage_mono (f ∣_ U ≫ U.ι) h)
    (ωX.presheaf.map (homOfLE ((f ∣_ U ≫ U.ι).image_preimage_le W)).op s)
  have key' : ψ.inv.app _ (ωX.presheaf.map (homOfLE (Scheme.Hom.image_mono _
      (Scheme.Hom.preimage_mono (f ∣_ U ≫ U.ι) h))).op
      (ωX.presheaf.map (homOfLE ((f ∣_ U ≫ U.ι).image_preimage_le W)).op s)) = _ := key
  rw [Intersection.modules_map_map] at key'
  unfold pullbackSection
  rwa [Intersection.modules_map_map]

/-- If `f` restricts to an isomorphism `f⁻¹(U) ⟶ U`, it maps a generic point of `Y` lying in
`f⁻¹(U)` to a generic point of `X`. -/
theorem closure_singleton_map_mem_irreducibleComponents {U : X.Opens} [IsIso (f ∣_ U)] {y : Y}
    (hy : y ∈ f ⁻¹ᵁ U) (hgen : closure {y} ∈ irreducibleComponents Y) :
    closure {f y} ∈ irreducibleComponents X := by
  rw [← isMax_iff_closure_mem_irreducibleComponents] at hgen ⊢
  have h2 := isMax_base (f ∣_ U ≫ U.ι) (η := ⟨y, hy⟩) fun c hc =>
    (le_iff_base_le_base (f ⁻¹ᵁ U).ι).mpr (hgen ((le_iff_base_le_base (f ⁻¹ᵁ U).ι).mp hc))
  rwa [morphismRestrict_ι] at h2

/-- A point `y ∈ f⁻¹(U)` with `f(y) ∈ W` lies in `f⁻¹(W ∩ U)`. -/
theorem mem_image_preimage_morphismRestrict {U : X.Opens} [IsIso (f ∣_ U)] {W : X.Opens}
    {y : Y} (hy : y ∈ f ⁻¹ᵁ U) (hW : f y ∈ W) : y ∈ (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U ≫ U.ι) ⁻¹ᵁ W) := by
  refine ⟨⟨y, hy⟩, ?_, rfl⟩
  change (f ∣_ U ≫ U.ι).base ⟨y, hy⟩ ∈ W
  rwa [morphismRestrict_ι]

end Pullback

/-! ### The discrepancy -/

section Discrepancy

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- **The discrepancy over a scheme satisfying (2.6.1), computed with choices** (FA Remark 2.6).
Let `X` satisfy (2.6.1), of pure dimension `n` over `k` with dualizing sheaf `ω_X`, and let `X°`
be an open set containing every point of codimension `≤ 1` on which `ω_X` is invertible. Let
`s ∈ Γ(W, ω_X)`, `W ⊆ X°`, be a rational section generating `ω_X` at every generic point, `K_X`
the divisor whose coefficient at each prime divisor `Γ` is the order of `s` at the generic point
of `Γ` (which lies in `X°`), `D_X` an `ℝ`-divisor no component of which lies in the singular
locus, and `K_X + D_X = ∑ⱼ rⱼ [Lⱼ]` for Cartier divisors `Lⱼ` with Weil divisors `[Lⱼ]`. Let
`f : Y ⟶ X` be proper and birational in the sense of (2.6.2), `ω_Y` a dualizing sheaf of `Y`
(structure map `f ≫ s_X`), and `E` a prime divisor of `Y` with `codim_X f(E) ≥ 2`. The real number
`a` is the *discrepancy* `a(E, D_X)` computed with these choices if, for an open `U ⊆ X`
containing every point of codimension `≤ 1`, with `f⁻¹(U)` containing the generic points of `Y`
and `f⁻¹(U) ⟶ U` an isomorphism, an isomorphism `ψ : ω_Y|_{f⁻¹U} ≅ ω_X|_U`, and pull-backs
`f^*Lⱼ`, `a = ord_E(f^*s) - ∑ⱼ rⱼ coeff_E(f^*Lⱼ)`: the coefficient of `E` in
`div(f^*s) - ∑ⱼ rⱼ f^*Lⱼ`. -/
@[mmp "def_fa2_discrepancy_nonnormal"]
def IsNonnormalDiscrepancyWith (n : ℕ) (ωX : X.Modules) (Xo : X.Opens) {W : X.Opens}
    (s : Γ(ωX, W)) (K : Divisor X) (D_X : RDivisor X) {m : ℕ} (r : Fin m → ℝ)
    (L : Fin m → X.CartierDivisor) (f : Y ⟶ X) (ωY : Y.Modules) (E : Mori.PrimeDivisor Y)
    (a : ℝ) : Prop :=
  SatisfiesFA261 sX ∧ IsDualizingSheaf sX n ωX ∧ IsInvertibleBigOpen ωX Xo ∧ W ≤ Xo ∧
    (∀ η : X, closure {η} ∈ irreducibleComponents X →
      ∃ (V : X.Opens) (_ : η ∈ V) (hVW : V ≤ W),
        IsLocalGenerator ωX (ωX.presheaf.map (homOfLE hVW).op s)) ∧
    (∀ Γ : Mori.PrimeDivisor X, IsOrderOfSectionAt ωX s Γ.genericPoint (K.coeff Γ)) ∧
    (∀ Γ : Mori.PrimeDivisor X, D_X.coeff Γ ≠ 0 →
      IsRegularLocalRing (X.presheaf.stalk Γ.genericPoint)) ∧
    (∃ wL : Fin m → Divisor X, (∀ j, Intersection.IsWeilDivisorOfCartier (L j) (wL j)) ∧
      Divisor.toRDivisor K + D_X = ∑ j, r j • Divisor.toRDivisor (wL j)) ∧
    IsBirationalFA262 sX (f ≫ sX) f ∧ IsProper f ∧ IsDualizingSheaf (f ≫ sX) n ωY ∧
    2 ≤ closedsCodimension (⟨closure (f.base '' E.support), isClosed_closure⟩ : Closeds X) ∧
    ∃ (U : X.Opens) (_ : ∀ x : X, Order.coheight x ≤ 1 → x ∈ U)
      (_ : ∀ y : Y, closure {y} ∈ irreducibleComponents Y → y ∈ f ⁻¹ᵁ U)
      (hU : IsIso (f ∣_ U)),
      haveI := hU
      ∃ (ψ : ωY.restrict (f ⁻¹ᵁ U).ι ≅ ωX.restrict (f ∣_ U ≫ U.ι)) (c : ℤ)
        (L' : Fin m → Y.CartierDivisor) (c' : Fin m → ℤ),
        IsOrderOfSectionAt ωY (pullbackSection f ψ s) E.genericPoint c ∧
        (∀ j, Intersection.IsPullback f (L j) (L' j)) ∧
        (∀ j, Intersection.IsOrderAlong (L' j) (Intersection.primeDivisorSubvariety E) (c' j)) ∧
        a = c - ∑ j, r j * c' j

/-- **The discrepancy over a scheme satisfying (2.6.1)** (FA Remark 2.6). The real number `a` is
the discrepancy `a(E, D_X)` of the prime divisor `E` of `Y`, for `f : Y ⟶ X`, if it is the
discrepancy computed with some choice of dualizing sheaves `ω_X`, `ω_Y`, of `X°`, of a rational
section of `ω_{X°}` with divisor `K_X`, and of a presentation `K_X + D_X = ∑ⱼ rⱼ Lⱼ` with `Lⱼ`
Cartier (`MMP.Flips.IsNonnormalDiscrepancyWith`). -/
@[mmp "def_fa2_discrepancy_nonnormal"]
def IsNonnormalDiscrepancy (n : ℕ) (D_X : RDivisor X) (f : Y ⟶ X) (E : Mori.PrimeDivisor Y)
    (a : ℝ) : Prop :=
  ∃ (ωX : X.Modules) (Xo W : X.Opens) (s : Γ(ωX, W)) (K : Divisor X) (m : ℕ) (r : Fin m → ℝ)
    (L : Fin m → X.CartierDivisor) (ωY : Y.Modules),
    IsNonnormalDiscrepancyWith sX n ωX Xo s K D_X r L f ωY E a

/-- **The discrepancy does not depend on the choice of `X°`** (FA Remark 2.6). Let `X°₁`, `X°₂` be
open sets containing every point of codimension `≤ 1` on which `ω_X` is invertible, and
`s ∈ Γ(W, ω_X)` with `W ⊆ X°₁`. Then `a` is the discrepancy computed on `X°₁` with the rational
section `s` if and only if it is the discrepancy computed on `X°₂` with the same rational section
`s|_{W ∩ X°₂}`, all other choices being the same. -/
@[mmp "def_fa2_discrepancy_nonnormal"]
theorem isNonnormalDiscrepancyWith_iff_of_isInvertibleBigOpen (n : ℕ) {ωX : X.Modules}
    {Xo₁ Xo₂ : X.Opens} (h₁ : IsInvertibleBigOpen ωX Xo₁) (h₂ : IsInvertibleBigOpen ωX Xo₂)
    {W : X.Opens} (s : Γ(ωX, W)) (hW : W ≤ Xo₁) (K : Divisor X) (D_X : RDivisor X) {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → X.CartierDivisor) (f : Y ⟶ X) (ωY : Y.Modules)
    (E : Mori.PrimeDivisor Y) (a : ℝ) :
    IsNonnormalDiscrepancyWith sX n ωX Xo₁ s K D_X r L f ωY E a ↔
      IsNonnormalDiscrepancyWith sX n ωX Xo₂
        (ωX.presheaf.map (homOfLE (inf_le_left : W ⊓ Xo₂ ≤ W)).op s) K D_X r L f ωY E a := by
  have hcoh : ∀ η : X, closure {η} ∈ irreducibleComponents X → Order.coheight η ≤ 1 :=
    fun η hη => (Order.coheight_eq_zero.mpr
      ((isMax_iff_closure_mem_irreducibleComponents η).mpr hη)).trans_le zero_le_one
  have hgenY : ∀ (U : X.Opens) [IsIso (f ∣_ U)] (W' : X.Opens),
      (∀ y : Y, closure {y} ∈ irreducibleComponents Y → y ∈ f ⁻¹ᵁ U) →
      (∀ η : X, closure {η} ∈ irreducibleComponents X → η ∈ W') →
      ∀ y : Y, closure {y} ∈ irreducibleComponents Y → y ⤳ E.genericPoint →
        y ∈ (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U ≫ U.ι) ⁻¹ᵁ W') :=
    fun U _ W' hUY hW' y hy _ => mem_image_preimage_morphismRestrict f (hUY y hy)
      (hW' _ (closure_singleton_map_mem_irreducibleComponents f (hUY y hy) hy))
  constructor
  · rintro ⟨hX, hωX, -, -, hgen, hK, hD, hL, hbir, hprop, hωY, hcod, U, hU₁, hUY, hU, hrest⟩
    have hW₀ : ∀ η : X, closure {η} ∈ irreducibleComponents X → η ∈ W ⊓ Xo₂ := fun η hη => by
      obtain ⟨V, hηV, hVW, -⟩ := hgen η hη
      exact ⟨hVW hηV, h₂.1 η (hcoh η hη)⟩
    refine ⟨hX, hωX, h₂, inf_le_right, fun η hη => ?_,
      fun Γ => (isOrderOfSectionAt_restrict_iff s inf_le_left (fun η hη _ => hW₀ η hη) _).mpr
        (hK Γ), hD, hL, hbir, hprop, hωY, hcod, U, hU₁, hUY, hU, ?_⟩
    · obtain ⟨V, hηV, hVW, hg⟩ := hgen η hη
      refine ⟨V ⊓ Xo₂, ⟨hηV, h₂.1 η (hcoh η hη)⟩, inf_le_inf_right _ hVW, ?_⟩
      have := hg.restrict (inf_le_left : V ⊓ Xo₂ ≤ V)
      rwa [Intersection.modules_map_map] at this ⊢
    · obtain ⟨ψ, c, L', c', hc, hpb, hord, ha⟩ := hrest
      refine ⟨ψ, c, L', c', ?_, hpb, hord, ha⟩
      rw [pullbackSection_restrict]
      exact (isOrderOfSectionAt_restrict_iff _ _ (hgenY U _ hUY hW₀) c).mpr hc
  · rintro ⟨hX, hωX, -, -, hgen, hK, hD, hL, hbir, hprop, hωY, hcod, U, hU₁, hUY, hU, hrest⟩
    have hW₀ : ∀ η : X, closure {η} ∈ irreducibleComponents X → η ∈ W ⊓ Xo₂ := fun η hη => by
      obtain ⟨V, hηV, hVW, -⟩ := hgen η hη
      exact hVW hηV
    refine ⟨hX, hωX, h₁, hW, fun η hη => ?_,
      fun Γ => (isOrderOfSectionAt_restrict_iff s inf_le_left (fun η hη _ => hW₀ η hη) _).mp
        (hK Γ), hD, hL, hbir, hprop, hωY, hcod, U, hU₁, hUY, hU, ?_⟩
    · obtain ⟨V, hηV, hVW, hg⟩ := hgen η hη
      refine ⟨V, hηV, le_trans hVW inf_le_left, ?_⟩
      rwa [Intersection.modules_map_map] at hg
    · obtain ⟨ψ, c, L', c', hc, hpb, hord, ha⟩ := hrest
      refine ⟨ψ, c, L', c', ?_, hpb, hord, ha⟩
      rw [pullbackSection_restrict] at hc
      exact (isOrderOfSectionAt_restrict_iff _ _ (hgenY U _ hUY hW₀) c).mp hc

end Discrepancy

end MMP.Flips
