/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
public import MMP.AlgebraicGeometry.Divisor.LocalSectionDivisor
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.FibreCoordinate

/-!
# Existence and uniqueness of the log discrepancy vector (FA 3.1.0)

Let `(X, P; B)` be a surface germ with boundary and `g : Y ⟶ X` a resolution of `(X, P)` with
exceptional curves `E_1, …, E_n`. There is exactly one log discrepancy vector of `(X, P; B)` on
`g`. Two inputs are needed beyond the linear algebra of
`MMP.Flips.existsUnique_isGermLogDiscrepancyVector_of_posDef`: the negative definiteness of
`((E_i · E_j))`, and a canonical divisor `K_Y` of the smooth surface `Y`.

The canonical divisor comes from a general fact. On an integral, locally Noetherian, normal,
quasi-compact scheme `Y`, an invertible `𝒪_Y`-module `L` is `𝒪_Y(D)` for a divisor `D`: fix
local generators `a_y` of `L` on opens `W_y ∋ y` and a reference generator `a_{y₀}`; the
transition functions `a_y / a_{y₀}` are units of `K(Y)` whose orders along a prime divisor `E`
do not depend on the trivializing open containing the generic point of `E`, and `D` is the
divisor with local equation `(a_y / a_{y₀})⁻¹` on `W_y`. A section `t` of `L` goes to the
rational function `t / a_{y₀}`; this is an isomorphism `L ≅ 𝒪_Y(D)`, injective since `Y` is
integral and surjective by algebraic Hartogs and gluing. For a smooth variety of dimension `n`
the canonical sheaf `⋀ⁿ Ω_{Y/k}` is invertible ([Stacks, Tag 0B8L]), so `Y` has a canonical
divisor.

## Main definitions

* `MMP.Mori.IsLocalGenerator`: a section freely generating a module over every smaller open.
* `MMP.Mori.LocalFrame`: local generators around every point, with a reference generator;
  `MMP.Mori.LocalFrame.divisor` is its divisor.

## Main results

* `MMP.Mori.exists_divisorialSheaf_iso_of_isInvertible`: an invertible module is `𝒪_Y(D)`.
* `MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme`: a smooth normal variety has a canonical
  divisor.
* `MMP.Flips.existsUnique_isGermLogDiscrepancyVector`: FA 3.1.0.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 3.1.0
* [R. Hartshorne, *Algebraic geometry*][Har77], II.6.11, II.6.13
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Mori

section Generator

variable {Y : Scheme.{u}} (L : Y.Modules)

/-- A section `a` of `L` over `W` is a *local generator* if it is a basis of `L` over every open
`V ⊆ W`: `c ↦ c · a|_V` is a bijection `Γ(Y, V) → Γ(L, V)`. -/
def IsLocalGenerator (W : Y.Opens) (a : Γ(L, W)) : Prop :=
  ∀ (V : Y.Opens) (h : V ≤ W), Function.Bijective fun c : Γ(Y, V) =>
    c • L.presheaf.map (homOfLE h).op a

variable {L}

/-- Restricting a section of `L` from `U` to `V` and then to `W` is restricting it from `U` to
`W`. -/
theorem modules_res_res {U V W : Y.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (t : Γ(L, U)) :
    L.presheaf.map (homOfLE h₁).op (L.presheaf.map (homOfLE h₂).op t) =
      L.presheaf.map (homOfLE (h₁.trans h₂)).op t := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restriction of sections of `L` commutes with scalar multiplication:
`(r • t)|_V = r|_V • t|_V`. -/
theorem modules_res_smul {U V : Y.Opens} (i : V ≤ U) (r : Γ(Y, U)) (t : Γ(L, U)) :
    L.presheaf.map (homOfLE i).op (r • t) =
      Y.presheaf.map (homOfLE i).op r • L.presheaf.map (homOfLE i).op t :=
  Stacks.ProjectiveFromSections.resM_smul i r t

namespace IsLocalGenerator

variable {W : Y.Opens} {a : Γ(L, W)} (h : IsLocalGenerator L W a)

/-- The coordinate of a section `t` of `L` over `V ⊆ W` in the basis `a|_V`. -/
def coord {V : Y.Opens} (hV : V ≤ W) (t : Γ(L, V)) : Γ(Y, V) :=
  (Equiv.ofBijective _ (h V hV)).symm t

include h in
/-- A section `t` over `V ⊆ W` is its coordinate times `a|_V`. -/
theorem coord_smul_eq {V : Y.Opens} (hV : V ≤ W) (t : Γ(L, V)) :
    h.coord hV t • L.presheaf.map (homOfLE hV).op a = t :=
  (Equiv.ofBijective _ (h V hV)).apply_symm_apply t

include h in
/-- If `c • a|_V = t`, then the coordinate of `t` is `c`. -/
theorem coord_eq_of_smul_eq {V : Y.Opens} (hV : V ≤ W) {t : Γ(L, V)} {c : Γ(Y, V)}
    (hc : c • L.presheaf.map (homOfLE hV).op a = t) : h.coord hV t = c :=
  (h V hV).1 ((h.coord_smul_eq hV t).trans hc.symm)

include h in
/-- The coordinate of a sum is the sum of the coordinates. -/
theorem coord_add {V : Y.Opens} (hV : V ≤ W) (t t' : Γ(L, V)) :
    h.coord hV (t + t') = h.coord hV t + h.coord hV t' :=
  h.coord_eq_of_smul_eq hV (by rw [add_smul, h.coord_smul_eq, h.coord_smul_eq])

include h in
/-- The coordinate of `r • t` is `r` times the coordinate of `t`. -/
theorem coord_smul {V : Y.Opens} (hV : V ≤ W) (r : Γ(Y, V)) (t : Γ(L, V)) :
    h.coord hV (r • t) = r * h.coord hV t :=
  h.coord_eq_of_smul_eq hV (by rw [mul_smul, h.coord_smul_eq])

include h in
/-- The coordinate of the restriction of `t` to `V' ⊆ V` is the restriction of the coordinate of
`t`. -/
theorem coord_res {V V' : Y.Opens} (hV : V ≤ W) (hV' : V' ≤ V) (t : Γ(L, V)) :
    h.coord (hV'.trans hV) (L.presheaf.map (homOfLE hV').op t) =
      Y.presheaf.map (homOfLE hV').op (h.coord hV t) := by
  refine h.coord_eq_of_smul_eq _ ?_
  conv_rhs => rw [← h.coord_smul_eq hV t]
  rw [modules_res_smul, modules_res_res]

end IsLocalGenerator

/-- A *local frame* of `L`: a local generator `a y` of `L` on an open neighbourhood `W y` of
every point `y`, together with a base point. -/
structure LocalFrame (L : Y.Modules) where
  /-- The trivializing open around `y`. -/
  W : Y → Y.Opens
  /-- Each point lies in its trivializing open. -/
  mem : ∀ y, y ∈ W y
  /-- The generator over `W y`. -/
  a : ∀ y, Γ(L, W y)
  /-- The section `a y` is a local generator of `L` over `W y`. -/
  isLocalGenerator : ∀ y, IsLocalGenerator L (W y) (a y)
  /-- The base point, whose generator is the reference frame. -/
  base : Y

namespace LocalFrame

variable (F : LocalFrame L)

/-- The coordinate of a section `t` of `L` over `U` in the reference frame, over `U ∩ W₀`. -/
def coordOf (U : Y.Opens) (t : Γ(L, U)) : Γ(Y, U ⊓ F.W F.base) :=
  (F.isLocalGenerator F.base).coord inf_le_right (L.presheaf.map (homOfLE inf_le_left).op t)

/-- The transition function `a_y / a_{y₀}` over `W y ∩ W₀`. -/
def transition (y : Y) : Γ(Y, F.W y ⊓ F.W F.base) := F.coordOf (F.W y) (F.a y)

/-- The coordinate formula: on `U ∩ W y ∩ W₀`, the reference coordinate of `t` is its
coordinate in `a_y` times the transition function. -/
theorem germ_coordOf (y : Y) (U : Y.Opens) (t : Γ(L, U)) (x : Y) (hxU : x ∈ U)
    (hxW : x ∈ F.W y) (hxb : x ∈ F.W F.base) :
    Y.presheaf.germ (U ⊓ F.W F.base) x ⟨hxU, hxb⟩ (F.coordOf U t) =
      Y.presheaf.germ (U ⊓ F.W y) x ⟨hxU, hxW⟩ ((F.isLocalGenerator y).coord inf_le_right
        (L.presheaf.map (homOfLE inf_le_left).op t)) *
      Y.presheaf.germ (F.W y ⊓ F.W F.base) x ⟨hxW, hxb⟩ (F.transition y) := by
  set V' : Y.Opens := U ⊓ F.W y ⊓ F.W F.base
  have h1 : V' ≤ U ⊓ F.W F.base := fun z hz => ⟨hz.1.1, hz.2⟩
  have h2 : V' ≤ U ⊓ F.W y := fun z hz => hz.1
  have h3 : V' ≤ F.W y ⊓ F.W F.base := fun z hz => ⟨hz.1.2, hz.2⟩
  have hx : x ∈ V' := ⟨⟨hxU, hxW⟩, hxb⟩
  rw [← TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE h1) x hx,
    ← TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE h2) x hx,
    ← TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE h3) x hx, ← map_mul]
  congr 1
  set b := (F.isLocalGenerator y).coord inf_le_right
    (L.presheaf.map (homOfLE (inf_le_left : U ⊓ F.W y ≤ U)).op t)
  have hb := (F.isLocalGenerator y).coord_smul_eq inf_le_right
    (L.presheaf.map (homOfLE (inf_le_left : U ⊓ F.W y ≤ U)).op t)
  have g := F.isLocalGenerator F.base
  have e1 : Y.presheaf.map (homOfLE h1).op (F.coordOf U t) =
      g.coord (h1.trans inf_le_right) (L.presheaf.map (homOfLE (h1.trans inf_le_left)).op t) := by
    rw [coordOf, ← g.coord_res inf_le_right h1, modules_res_res]
  have e3 : Y.presheaf.map (homOfLE h3).op (F.transition y) =
      g.coord (h3.trans inf_le_right)
        (L.presheaf.map (homOfLE (h3.trans inf_le_left)).op (F.a y)) := by
    rw [transition, coordOf, ← g.coord_res inf_le_right h3, modules_res_res]
  rw [e1, e3, ← g.coord_smul]
  congr 1
  have : L.presheaf.map (homOfLE (h1.trans inf_le_left)).op t =
      L.presheaf.map (homOfLE h2).op (L.presheaf.map (homOfLE inf_le_left).op t) := by
    rw [modules_res_res]
  rw [this, ← hb, modules_res_smul, modules_res_res]

section Integral

variable [IsIntegral Y]

omit [IsIntegral Y] in
/-- On an integral scheme, the generic point of the irreducible component lies in every nonempty
open. -/
theorem componentGenericPoint_mem_of_isIntegral [IsIntegral Y] (Z : irreducibleComponents Y)
    {O : Y.Opens} (hO : (O : Set Y).Nonempty) : componentGenericPoint Y Z ∈ O := by
  have h1 : Z.1 ∈ ({Set.univ} : Set (Set Y)) :=
    (irreducibleComponents_eq_singleton (X := Y)) ▸ Z.2
  rwa [genericPoint_mem_iff, show Z.1 = Set.univ from h1, Set.inter_univ]

/-- The generic point lies in the reference trivializing open `W y₀`. -/
theorem cgp_mem_base (Z : irreducibleComponents Y) : componentGenericPoint Y Z ∈ F.W F.base :=
  componentGenericPoint_mem_of_isIntegral Z ⟨F.base, F.mem F.base⟩

/-- If the generic point lies in `U`, it lies in `U ∩ W y₀`. -/
theorem cgp_mem_inf_base {Z : irreducibleComponents Y} {U : Y.Opens}
    (h : componentGenericPoint Y Z ∈ U) : componentGenericPoint Y Z ∈ U ⊓ F.W F.base :=
  ⟨h, F.cgp_mem_base Z⟩

omit [IsIntegral Y] in
/-- A local generator does not vanish on a nonempty open. -/
theorem isLocalGenerator_res_ne_zero {W V : Y.Opens} {a : Γ(L, W)} (h : IsLocalGenerator L W a)
    (hV : V ≤ W) (hne : (V : Set Y).Nonempty) : L.presheaf.map (homOfLE hV).op a ≠ 0 := by
  intro h0
  have : Nonempty V := hne.to_subtype
  exact one_ne_zero ((h V hV).1 (a₁ := 1) (a₂ := 0) (by simp only [one_smul, zero_smul, h0]))

/-- The germ of the transition function `a_y / a_{y₀}` at the generic point is nonzero. -/
theorem transition_germ_ne_zero (y : Y) (Z : irreducibleComponents Y)
    (hZ : componentGenericPoint Y Z ∈ F.W y ⊓ F.W F.base) :
    (Y.presheaf.germ _ _ hZ).hom (F.transition y) ≠ 0 := by
  intro h0
  have hc : F.transition y = 0 :=
    germ_injective_of_isIntegral Y _ hZ (h0.trans (map_zero _).symm)
  have hs := (F.isLocalGenerator F.base).coord_smul_eq inf_le_right
    (L.presheaf.map (homOfLE (inf_le_left : F.W y ⊓ F.W F.base ≤ F.W y)).op (F.a y))
  change F.transition y • _ = _ at hs
  rw [hc, zero_smul] at hs
  exact isLocalGenerator_res_ne_zero (F.isLocalGenerator y) inf_le_left ⟨_, hZ⟩ hs.symm

/-- The unit of `K(Y)` given by the transition function `a_y / a_{y₀}`. -/
def unit (y : Y) : (RationalFunctions Y)ˣ :=
  Threefold.Resolution.sectionUnit (F.transition y) (F.transition_germ_ne_zero y)

/-- The unit `unit y` is the germ of the transition function at the generic point. -/
theorem unit_apply (y : Y) (Z : irreducibleComponents Y)
    (hZ : componentGenericPoint Y Z ∈ F.W y ⊓ F.W F.base) :
    (F.unit y : RationalFunctions Y) Z = (Y.presheaf.germ _ _ hZ).hom (F.transition y) :=
  Threefold.Resolution.sectionUnit_apply _ _ Z hZ

/-- A section `t` of `L` over `U`, read as a rational function through the reference frame: the
germ of its reference coordinate at the generic point. -/
def chi (U : Y.Opens) (t : Γ(L, U)) : ToType ((rationalFunctionsPresheaf Y).obj (op U)) :=
  fun Z => Y.presheaf.germ (U ⊓ F.W F.base) _ (F.cgp_mem_inf_base Z.2) (F.coordOf U t)

/-- `chi` is additive. -/
theorem chi_add (U : Y.Opens) (t t' : Γ(L, U)) : F.chi U (t + t') = F.chi U t + F.chi U t' := by
  funext Z
  change F.chi U (t + t') Z = F.chi U t Z + F.chi U t' Z
  simp only [chi, coordOf, map_add, (F.isLocalGenerator F.base).coord_add]

/-- `chi` is `Γ(Y, U)`-linear: `chi U (r • t) = r • chi U t`. -/
theorem chi_smul (U : Y.Opens) (r : Γ(Y, U)) (t : Γ(L, U)) :
    F.chi U (r • t) = r • F.chi U t := by
  funext Z
  rw [rationalFunctions_smul_apply]
  simp only [chi, coordOf, modules_res_smul, (F.isLocalGenerator F.base).coord_smul, map_mul]
  rw [TopCat.Presheaf.germ_res_apply]

/-- `chi` commutes with restriction to a smaller open. -/
theorem chi_res {U V : Y.Opens} (i : V ⟶ U) (t : Γ(L, U)) :
    F.chi V (L.presheaf.map i.op t) = (rationalFunctionsPresheaf Y).map i.op (F.chi U t) := by
  funext Z
  rw [rationalFunctionsPresheaf_map_apply]
  have hle : V ⊓ F.W F.base ≤ U ⊓ F.W F.base := inf_le_inf_right _ i.le
  have : F.coordOf V (L.presheaf.map i.op t) =
      Y.presheaf.map (homOfLE hle).op (F.coordOf U t) := by
    rw [coordOf, coordOf, ← (F.isLocalGenerator F.base).coord_res inf_le_right hle,
      modules_res_res]
    change (F.isLocalGenerator F.base).coord _
      (L.presheaf.map (homOfLE _).op (L.presheaf.map (homOfLE i.le).op t)) = _
    rw [modules_res_res]
  simp only [chi]
  rw [this, TopCat.Presheaf.germ_res_apply]

/-- The value of `chi U t` at the generic point, through the generator `a_y`. -/
theorem chi_apply_eq (y : Y) (U : Y.Opens) (t : Γ(L, U))
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ U})
    (hZ : componentGenericPoint Y Z.1 ∈ F.W y) :
    F.chi U t Z = Y.presheaf.germ (U ⊓ F.W y) _ ⟨Z.2, hZ⟩ ((F.isLocalGenerator y).coord
        inf_le_right (L.presheaf.map (homOfLE inf_le_left).op t)) *
      (F.unit y : RationalFunctions Y) Z.1 := by
  rw [F.unit_apply y Z.1 ⟨hZ, F.cgp_mem_base Z.1⟩]
  exact F.germ_coordOf y U t _ Z.2 hZ (F.cgp_mem_base Z.1)

/-- The value of `chi` on a multiple of a generator. -/
theorem chi_smul_generator (y : Y) {V : Y.Opens} (hV : V ≤ F.W y) (b : Γ(Y, V))
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ V}) :
    F.chi V (b • L.presheaf.map (homOfLE hV).op (F.a y)) Z =
      Y.presheaf.germ V _ Z.2 b * (F.unit y : RationalFunctions Y) Z.1 := by
  rw [F.chi_apply_eq y V _ Z (hV Z.2)]
  congr 1
  have hle : V ⊓ F.W y ≤ V := inf_le_left
  rw [← TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hle) _ (show
    componentGenericPoint Y Z.1 ∈ V ⊓ F.W y from ⟨Z.2, hV Z.2⟩) b]
  congr 1
  refine (F.isLocalGenerator y).coord_eq_of_smul_eq _ ?_
  rw [modules_res_smul, modules_res_res]

/-- `chi` is injective: a section of `L` whose reference coordinate vanishes generically
vanishes. -/
theorem chi_injective (U : Y.Opens) (t : Γ(L, U)) (h : F.chi U t = 0) : t = 0 := by
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨L.presheaf, L.isSheaf⟩ : TopCat.Sheaf Ab Y)
    (fun x : U => U ⊓ F.W x.1) U (fun x => homOfLE inf_le_left)
    (fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hx, F.mem x⟩) t 0 fun x => ?_
  change L.presheaf.map _ t = L.presheaf.map _ 0
  rw [map_zero]
  obtain ⟨Z₀, -⟩ := exists_mem_irreducibleComponents (x : Y)
  have hZU : componentGenericPoint Y Z₀ ∈ U := componentGenericPoint_mem_of_isIntegral Z₀ ⟨x, x.2⟩
  have hZW : componentGenericPoint Y Z₀ ∈ F.W x.1 :=
    componentGenericPoint_mem_of_isIntegral Z₀ ⟨x, F.mem x⟩
  have e := F.chi_apply_eq x.1 U t ⟨Z₀, hZU⟩ hZW
  rw [h] at e
  have hu := (Pi.isUnit_iff.mp (F.unit x.1).isUnit) Z₀
  have hb : (F.isLocalGenerator x.1).coord inf_le_right
      (L.presheaf.map (homOfLE (inf_le_left : U ⊓ F.W x.1 ≤ U)).op t) = 0 := by
    refine germ_injective_of_isIntegral Y _ (show componentGenericPoint Y Z₀ ∈ U ⊓ F.W x.1
      from ⟨hZU, hZW⟩) ?_
    rw [map_zero]
    exact (mul_eq_zero.mp e.symm).resolve_right hu.ne_zero
  rw [← (F.isLocalGenerator x.1).coord_smul_eq inf_le_right
    (L.presheaf.map (homOfLE (inf_le_left : U ⊓ F.W x.1 ≤ U)).op t), hb, zero_smul]

/-- Two sections of `L` with the same image under `chi` are equal. -/
theorem chi_inj (U : Y.Opens) {t t' : Γ(L, U)} (h : F.chi U t = F.chi U t') : t = t' := by
  have e := F.chi_add U (t - t') t'
  rw [sub_add_cancel, h] at e
  exact sub_eq_zero.mp (F.chi_injective U _ (by simpa using e))

variable [IsLocallyNoetherian Y] [IsNormal Y]

/-- The orders of the transition functions along a prime divisor do not depend on the chosen
trivializing open containing its generic point. -/
theorem ord_unit_eq (E : Mori.PrimeDivisor Y) {y y' : Y} (hy : E.genericPoint ∈ F.W y)
    (hy' : E.genericPoint ∈ F.W y') : E.ord (F.unit y') = E.ord (F.unit y) := by
  set V : Y.Opens := F.W y' ⊓ F.W y
  have gy := F.isLocalGenerator y
  have gy' := F.isLocalGenerator y'
  set u := gy.coord (inf_le_right : V ≤ F.W y)
    (L.presheaf.map (homOfLE (inf_le_left : V ≤ F.W y')).op (F.a y'))
  set v := gy'.coord (inf_le_left : V ≤ F.W y')
    (L.presheaf.map (homOfLE (inf_le_right : V ≤ F.W y)).op (F.a y))
  have hvu : v * u = 1 := by
    have h1 : gy.coord (inf_le_right : V ≤ F.W y)
        (L.presheaf.map (homOfLE (inf_le_right : V ≤ F.W y)).op (F.a y)) = 1 :=
      gy.coord_eq_of_smul_eq _ (one_smul _ _)
    rw [← h1]
    symm
    refine gy.coord_eq_of_smul_eq _ ?_
    rw [mul_smul, gy.coord_smul_eq, gy'.coord_smul_eq]
  have hu : IsUnit u := IsUnit.of_mul_eq_one_right v hvu
  have hug : ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ V),
      (Y.presheaf.germ V _ hZ).hom u ≠ 0 := fun Z hZ => ((hu.map _).ne_zero)
  have key : F.unit y' = Threefold.Resolution.sectionUnit u hug * F.unit y := by
    ext Z
    have hZ' : componentGenericPoint Y Z ∈ F.W y' := componentGenericPoint_mem_of_isIntegral Z
      ⟨_, F.mem y'⟩
    have hZ : componentGenericPoint Y Z ∈ F.W y := componentGenericPoint_mem_of_isIntegral Z
      ⟨_, F.mem y⟩
    have hb := F.cgp_mem_base Z
    rw [Units.val_mul, Pi.mul_apply, F.unit_apply y' Z ⟨hZ', hb⟩, F.unit_apply y Z ⟨hZ, hb⟩,
      Threefold.Resolution.sectionUnit_apply u hug Z ⟨hZ', hZ⟩]
    exact F.germ_coordOf y (F.W y') (F.a y') _ hZ' hZ hb
  have hE : E.genericPoint ∈ V := ⟨hy', hy⟩
  rw [key, PrimeDivisor.ord_mul,
    Threefold.Resolution.ord_sectionUnit_eq_zero u hug E hE (hu.map _), zero_add]

variable [CompactSpace Y]

/-- Only finitely many prime divisors `E` have `-ord_E (unit (generic point of E)) ≠ 0`. -/
theorem finite_divisorCoeff_ne_zero :
    {E : Mori.PrimeDivisor Y | -E.ord (F.unit E.genericPoint) ≠ 0}.Finite := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (F.W y : Set Y))
    (fun y => (F.W y).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, F.mem x⟩)
  refine (Set.finite_iUnion fun y : t => finite_ord_ne_zero (F.unit y.1)).subset ?_
  intro E hE
  obtain ⟨y, hy, hEy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ E.genericPoint))
  refine Set.mem_iUnion.2 ⟨⟨y, hy⟩, ?_⟩
  change E.ord _ ≠ 0
  rw [F.ord_unit_eq E (F.mem E.genericPoint) hEy]
  exact fun h => hE (by rw [h, neg_zero])

/-- The divisor of the frame: along `E`, minus the order of the transition function on a
trivializing open containing the generic point of `E`. -/
def divisor : Divisor Y :=
  Finsupp.ofSupportFinite (fun E => -E.ord (F.unit E.genericPoint))
    F.finite_divisorCoeff_ne_zero

/-- The coefficient of the frame's divisor along `E`. -/
theorem divisor_coeff (E : Mori.PrimeDivisor Y) :
    F.divisor.coeff E = -E.ord (F.unit E.genericPoint) := rfl

/-- On `W y`, the frame's divisor has local equation `(a_y / a_{y₀})⁻¹`. -/
theorem isLocalEquation_divisor (y : Y) : F.divisor.IsLocalEquation (F.W y) (F.unit y)⁻¹ := by
  intro E hE
  rw [divisor_coeff, PrimeDivisor.ord_inv,
    F.ord_unit_eq E (F.mem E.genericPoint) (E.genericPoint_mem_of_nonempty hE)]

/-- The image under `chi` of a section of `L` over `U` is a section of `𝒪_Y(D)` over `U`. -/
theorem chi_mem (U : Y.Opens) (t : Γ(L, U)) :
    F.divisor.IsDivisorialSection U (F.chi U t) := by
  intro E hE
  set y := E.genericPoint
  have hEW : E.genericPoint ∈ F.W y := F.mem y
  have hcW : componentGenericPoint Y E.component ∈ F.W y :=
    E.specializes_genericPoint.mem_open (F.W y).isOpen hEW
  rw [F.chi_apply_eq y U t _ hcW, divisor_coeff, neg_neg]
  have hEU : E.genericPoint ∈ U ⊓ F.W y := ⟨E.genericPoint_mem_of_nonempty hE, hEW⟩
  rw [← TopCat.Presheaf.germ_stalkSpecializes_apply Y.presheaf hEU E.specializes_genericPoint]
  refine PrimeDivisor.OrdGE.toComponent_mul (Or.inr ?_) _
  rw [PrimeDivisor.valuation_component]

/-- `chi` is surjective onto the sections of `𝒪_Y(D)`. -/
theorem chi_surjective (U : Y.Opens) (f : F.divisor.divisorialSubmodule U) :
    ∃ t : Γ(L, U), F.chi U t = f.1 := by
  set V : U → Y.Opens := fun x => U ⊓ F.W x.1
  have hg : ∀ x : U, (0 : Divisor Y).IsDivisorialSection (V x) fun Z =>
      f.1 ⟨Z.1, (inf_le_left : V x ≤ U) Z.2⟩ *
        (((F.unit x.1)⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z.1 := by
    intro x E hE
    have hEU : (E.support ∩ U).Nonempty := hE.mono (Set.inter_subset_inter_right _ inf_le_left)
    have hEW : (E.support ∩ F.W x.1).Nonempty :=
      hE.mono (Set.inter_subset_inter_right _ inf_le_right)
    have h1 := f.2 E hEU
    have h2 : E.OrdGE (E.ord (F.unit x.1)⁻¹)
        ((((F.unit x.1)⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) E.component) :=
      Or.inr (by rw [PrimeDivisor.valuation_component])
    refine (h1.mul h2).mono (le_of_eq ?_)
    rw [F.isLocalEquation_divisor x.1 E hEW, DivisorWithCoeffs.coeff_zero]
    ring
  choose b hb using fun x => (hg x).exists_eq
  set tx : ∀ x : U, Γ(L, V x) := fun x =>
    b x • L.presheaf.map (homOfLE (inf_le_right : V x ≤ F.W x.1)).op (F.a x.1)
  have hchi : ∀ x : U, F.chi (V x) (tx x) =
      (rationalFunctionsPresheaf Y).map (homOfLE (inf_le_left : V x ≤ U)).op f.1 := by
    intro x
    funext Z
    rw [F.chi_smul_generator x.1 inf_le_right (b x) Z, rationalFunctionsPresheaf_map_apply]
    have := congrFun (hb x) Z
    rw [toRationalFunctionsPresheaf_app_apply] at this
    rw [this, mul_assoc, ← Pi.mul_apply (f := ((F.unit x.1)⁻¹ : (RationalFunctions Y)ˣ).val),
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Pi.one_apply, mul_one]
  have hcompat : TopCat.Presheaf.IsCompatible L.presheaf V tx := by
    intro x x'
    apply F.chi_inj
    rw [F.chi_res, F.chi_res, hchi, hchi]
    funext Z
    rfl
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨L.presheaf, L.isSheaf⟩ : TopCat.Sheaf Ab Y) V U (fun x => homOfLE inf_le_left)
    (fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hx, F.mem x⟩) tx hcompat
  refine ⟨t, funext fun Z => ?_⟩
  set x : U := ⟨componentGenericPoint Y Z.1, Z.2⟩
  have e1 := F.chi_res (homOfLE (inf_le_left : V x ≤ U)) t
  have e2 : L.presheaf.map (homOfLE (inf_le_left : V x ≤ U)).op t = tx x := ht x
  rw [e2, hchi] at e1
  exact (congrFun e1 ⟨Z.1, Z.2, F.mem x.1⟩).symm

/-- `chi` as a linear map into the sections of `𝒪_Y(D)`. -/
def chiLinear (U : Y.Opens) :
    Γ(L, U) →ₗ[Γ(Y, U)] F.divisor.divisorialSubmodule U where
  toFun t := ⟨F.chi U t, F.chi_mem U t⟩
  map_add' t t' := Subtype.ext (F.chi_add U t t')
  map_smul' r t := Subtype.ext (F.chi_smul U r t)

/-- The morphism `L ⟶ 𝒪_Y(D)` of the frame. -/
def toDivisorialSheaf : L ⟶ F.divisor.divisorialSheaf :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (F.chiLinear U.unop).toAddMonoidHom
      naturality U V i := by
        ext t
        exact Subtype.ext (F.chi_res i.unop t) }
    fun U r t => (F.chiLinear U.unop).map_smul r t⟩

/-- The morphism `L ⟶ 𝒪_Y(D)` of the frame is an isomorphism. -/
theorem isIso_toDivisorialSheaf : IsIso F.toDivisorialSheaf := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun t t' h => F.chi_inj U (congrArg Subtype.val h), fun f => ?_⟩
  obtain ⟨t, ht⟩ := F.chi_surjective U f
  exact ⟨t, Subtype.ext ht⟩

end Integral

end LocalFrame

/-- **A locally free sheaf of rank one is divisorial.** On an integral, locally Noetherian,
normal, quasi-compact scheme, an `𝒪_Y`-module with a local frame is `𝒪_Y(D)` for a divisor `D`. -/
theorem LocalFrame.exists_divisorialSheaf_iso [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] (F : LocalFrame L) :
    ∃ D : Divisor Y, Nonempty (D.divisorialSheaf ≅ L) :=
  ⟨F.divisor, ⟨(@asIso _ _ _ _ F.toDivisorialSheaf F.isIso_toDivisorialSheaf).symm⟩⟩

/-- **An invertible module is divisorial** (Hartshorne II.6.13, 6.15). On an integral, locally
Noetherian, normal, quasi-compact scheme `Y`, every invertible `𝒪_Y`-module `L` is isomorphic to
`𝒪_Y(D)` for a divisor `D`. -/
theorem exists_divisorialSheaf_iso_of_isInvertible [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] :
    ∃ D : Divisor Y, Nonempty (D.divisorialSheaf ≅ L) := by
  have := Stacks.SheafOfModules.isInvertible_of_tensorInvertible (X := Y.toRingedSpace) L
  have : ∀ z : Y.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y.toRingedSpace z) :=
    Y.isLocalRing
  choose W hW a ha using fun y : Y =>
    Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible (X := Y.toRingedSpace) L y
  obtain ⟨y₀⟩ : Nonempty Y := inferInstance
  exact LocalFrame.exists_divisorialSheaf_iso
    { W := W, mem := hW, a := a, isLocalGenerator := ha, base := y₀ }

end Generator

end MMP.Mori

namespace MMP.Mori

section Canonical

variable {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

/-- An invertible module on the open subscheme `U = Y` is the restriction of `𝒪_Y(D)` for a
divisor `D` of `Y`. -/
theorem exists_divisorialSheaf_restrict_iso (U : Y.Opens) (hU : U = ⊤) (M : U.toScheme.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible U.toScheme.presheaf U.toScheme.ringCatSheaf.2 M) :
    ∃ D : Divisor Y, Nonempty (D.divisorialSheaf.restrict U.ι ≅ M) := by
  subst hU
  let j := Y.topIso.inv
  have hj : (⊤ : Y.Opens).ι ≫ j = 𝟙 _ := Y.topIso.hom_inv_id
  let L' := M.restrict j
  let e : L'.restrict (⊤ : Y.Opens).ι ≅ M :=
    ((Scheme.Modules.restrictFunctorComp (⊤ : Y.Opens).ι j).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr hj).app M ≪≫ Scheme.Modules.restrictFunctorId.app M
  have hL' : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L' :=
    Stacks.Modules.isInvertible_of_isInvertible_restrict_of_iSup_eq_top L'
      (fun _ : Unit => (⊤ : Y.Opens)) (by simp)
      fun _ => have := hM; Stacks.SheafOfModules.isInvertible_of_iso _ _ e.symm
  have := hL'.toAlgebraicGeometry
  obtain ⟨D, ⟨φ⟩⟩ := exists_divisorialSheaf_iso_of_isInvertible L'
  exact ⟨D, ⟨(Scheme.Modules.restrictFunctor (⊤ : Y.Opens).ι).mapIso φ ≪≫ e⟩⟩

/-- **A smooth variety has a canonical divisor.** If `Y` is a smooth normal variety of dimension
`n` over `k`, the canonical sheaf `ω_Y = ⋀ⁿ Ω_{Y/k}` is invertible, hence `𝒪_Y(K)` for a
divisor `K`. -/
theorem exists_isCanonicalDivisor_of_isSmoothScheme {k : Type u} [Field k]
    (f : Y ⟶ Spec (.of k)) [IsVariety k f] (hsm : IsSmoothScheme f) {n : ℕ}
    (hn : topologicalKrullDim Y = n) : ∃ K : Divisor Y, K.IsCanonicalDivisor f n := by
  have hsmooth : Smooth f := by
    have hc : iSup (fun U : {U : Y.Opens // Smooth (U.ι ≫ f)} => (U.1 : Y.Opens)) = ⊤ := by
      rw [IsSmoothScheme, smoothLocus] at hsm
      rw [← hsm, sSup_eq_iSup']
      exact le_antisymm (iSup_le fun _ => le_iSup _ _) (iSup_le fun _ => le_iSup _ _)
    have : IsZariskiLocalAtSource @Smooth.{u} :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth)
    rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @Smooth) _ hc]
    exact fun U => U.2
  have : SmoothOfRelativeDimension n f :=
    MMP.Intersection.smoothOfRelativeDimension_of_isVariety f n hn
  have : SmoothOfRelativeDimension n ((smoothLocus f).ι ≫ f) := by
    have h := (inferInstance : SmoothOfRelativeDimension (0 + n) ((smoothLocus f).ι ≫ f))
    rwa [zero_add] at h
  have hinv := Stacks.Discriminant.isInvertible_relativeDifferentialForms
    ((smoothLocus f).ι ≫ f) n
  have hM := Stacks.SheafOfModules.isInvertible_of_tensorInvertible
    (X := (smoothLocus f).toScheme.toRingedSpace) (canonicalSheaf f n) (h := hinv)
  obtain ⟨K, hK⟩ := exists_divisorialSheaf_restrict_iso (smoothLocus f) hsm
    (canonicalSheaf f n) hM
  exact ⟨K, hn, hK⟩

end Canonical

end MMP.Mori

namespace MMP.Flips

open MMP.Mori

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X}
  {B : QDivisor X} {g : Y ⟶ X} [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
  {n : ℕ} {E : Fin n → Mori.PrimeDivisor Y}

/-- **Existence and uniqueness of the log discrepancy vector** (FA 3.1.0). For a surface germ
with boundary `(X, P; B)` and every resolution `g` of `(X, P)` with exceptional curves
`E_1, …, E_n`, there is exactly one log discrepancy vector of `(X, P; B)` on `g`: `Y` has a
canonical divisor (`MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme`), and the intersection
matrix `((E_i · E_j))` is negative definite. -/
@[mmp "lem_fa3_log_discrepancy_vector_exists_unique"]
theorem existsUnique_isGermLogDiscrepancyVector
    (hB : IsSurfaceGermWithBoundary sX P B) (hg : IsGermResolution sX P g)
    (hE : IsExceptionalCurveEnumeration g P E) :
    ∃! a : Fin n → ℚ, IsGermLogDiscrepancyVector sX P B g E a := by
  have hX := hB.1.1
  have := hX.1.toQuasiCompact
  have := hX.2
  have := hg.isSmoothResolution.isProper
  have := hg.isIntegral sX
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  have hYv := hg.isVariety
  have hdim : topologicalKrullDim Y = ((2 : ℕ) : WithBot ℕ∞) := hg.topologicalKrullDim_eq
  obtain ⟨K₀, hK₀⟩ := @exists_isCanonicalDivisor_of_isSmoothScheme Y _ _ _ _ k _ (g ≫ sX) hYv
    hg.isSmoothResolution.isSmoothScheme 2 hdim
  choose C hC hCc using fun i => (hE.isGermExceptionalCurve i).exists_properCurve hg
  refine existsUnique_isGermLogDiscrepancyVector_of_posDef hB hg hE hK₀ C hC ?_
  exact MMP.Threefold.Resolution.posDef_neg_intersectionMatrix_of_isBirationalMorphism
    hg.isVariety hg.isSmoothResolution.isSmoothScheme hg.topologicalKrullDim_eq hX.1 rfl
    hg.isSmoothResolution.isBirationalMorphism E hE.injective C hC hCc

end MMP.Flips
