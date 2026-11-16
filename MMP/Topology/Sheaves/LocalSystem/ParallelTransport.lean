module

public import MMP.AlgebraicTopology.FundamentalClass.ComplexOrientation
public import MMP.Topology.Sheaves.CompactSupport.LongExactSequences
public import MMP.Topology.Sheaves.CompactSupport.OrientedPlaneTrace

/-!
# Parallel transport of a local system, and top compactly supported cohomology of a surface

Let `𝓛` be a local system of finite-dimensional `ℚ`-vector spaces (`MMP.Fourfold.IsLocalSystem`)
on a locally path-connected space `M`. For a path `γ` from `x` to `y` the inverse image
`γ⁻¹ 𝓛` on `[0, 1]` is constant, and the germs at `0` and `1` of its global sections give an
isomorphism `T_γ : 𝓛_x ≅ 𝓛_y`, the *parallel transport* along `γ`. It depends only on the
homotopy class of `γ` rel endpoints and is compatible with concatenation:
`T_{γ δ} = T_δ ∘ T_γ`. On a simply connected open `V ⊆ M` containing `x`, the restriction
`𝓛|_V` is isomorphic to the constant sheaf with fibre `𝓛_x`, by an isomorphism whose stalk at
`y ∈ V` is `T_γ⁻¹` for any path `γ` in `V` from `x` to `y`.

The transport is built from *flat families*: along a continuous map `f : A → M`, a family of
germs `Y a ∈ 𝓛_{f a}` which is locally given by sections of `𝓛`. On a preconnected `A` a flat
family is determined by one of its values (the support of a section of a local system is open),
and along a path every germ at an end point extends to a flat family (a Lebesgue number
subdivides the interval into pieces mapped into trivializing opens). Homotopy invariance is
proved strip by strip on the square of a homotopy.

Let `S` be a Hausdorff surface with an oriented atlas and a finite open cover `(U i)_{i ∈ ι}`
such that every nonempty finite intersection `U_I = ⋂_{i ∈ I} U i` is homeomorphic to `ℝ²`, and
let `L` be a local system of finite-dimensional `ℚ`-vector spaces on `S`. Then
`H^q_c(S, L) = 0` for `q > 2`, and `H²_c(S, L)` is the cokernel of
`⨁_{i<j} H²_c(U_i ∩ U_j, L) → ⨁_i H²_c(U_i, L)`, `x ↦ (e x, -e x)`, the map out of the cokernel
being the sum of the extension maps. On a member of the cover the local system is constant (by
the trivialisation above), so its compactly supported cohomology is concentrated in degree `2`;
the result follows by induction over finite subfamilies of the cover from the Mayer–Vietoris
sequence, applied to `W = A ∪ B` with `A ∩ B` covered by the good family `(U i ∩ B)`.

## Main results

* `MMP.Fourfold.isIso_stalkToPullbackStalk`: the canonical map `F_{f(x)} ⟶ (f⁻¹F)_x` from a
  stalk to the stalk of an inverse image is an isomorphism.
* `MMP.Fourfold.IsLocalSystem.parallelTransport`: the parallel transport, on homotopy classes
  of paths.
* `MMP.Fourfold.IsLocalSystem.exists_parallelTransport`: the inverse image along a path is
  constant, and the parallel transport is characterised by end germs of sections of the inverse
  image along a path, is compatible with concatenation, and trivialises the local system over a
  simply connected open subset (`IsLocalSystem.nonempty_pullback_path_iso_constantSheaf`,
  `IsLocalSystem.parallelTransport_germ`,
  `IsLocalSystem.parallelTransport_trans`,
  `IsLocalSystem.exists_iso_constantSheaf_parallelTransport`).
* `MMP.Fourfold.compactSupportCohomology_two_of_goodCover`: vanishing of `H^q_c(S, L)` for
  `q > 2` and the cokernel presentation of `H²_c(S, L)` from a good cover.

## Implementation notes

The transport is a family of isomorphisms indexed by `Path.Homotopic.Quotient x y`, so homotopy
invariance is built into its type. The stalk `𝓛_y` is compared with the stalk of an inverse
image through `MMP.Fourfold.stalkToPullbackStalk`, and the fibre `E` of a constant sheaf is
mapped to its global sections by the unit of sheafification.

The orientation of `S` is an oriented atlas, `MMP.IsOrientedAtlas`, modelled on
a real normed plane `H` (for instance `ℂ`, so that a complex curve is covered by
`MMP.isOrientedAtlas_of_isManifold_complex`).
`H^q_c(U, L|_U)` is written as `H^q_c(S, j_! j^* L)`, with `j : U → S` the inclusion. The two
agree by `MMP.Fourfold.compactSupportCohomology_extendByZero`, which also identifies the
extension map `H^q_c(V, L|_V) → H^q_c(U, L|_U)` for `V ≤ U` as the map induced by the unique
morphism `j_{V!} j_V^* L ⟶ j_{U!} j_U^* L` over `L`. Here the edge maps are the maps induced by
such morphisms, and the map to `H²_c(S, L)` is the one induced by the counit
`j_{U!} j_U^* L ⟶ L`. The direct sums are finite products, and the cokernel presentation is
stated as exactness of `⨁_{i<j} → ⨁_i → H²_c(S, L) → 0`. The cohomology of an open `W ⊆ S` is
compared with that of `S` through `j_{W!} j_{A'!} (F|_{A'}) ≅ j_{A!}(F|_A)` for an open `A' ⊆ W`
with image `A`, built by adjunction from the invertibility of the counit `j_{A!}(F|_A) ⟶ F` on
every open contained in `A`.

## References

* [Iversen, *Cohomology of sheaves*], III.7 and IV.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite Limits

namespace MMP.Fourfold

section ParallelTransport

open unitInterval

/-! ### Stalks of inverse images -/

section Pullback

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Y)

/-- The section of `f^* F` over `f⁻¹(W)` attached to a section of `F` over `W`. -/
private def unitSec {W : Opens Y} (r : ToType (((TopCat.Sheaf.forget _ Y).obj F).obj (op W))) :
    ToType (((TopCat.Sheaf.forget _ X).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj F)).obj
      (op ((Opens.map f).obj W))) :=
  (((TopCat.Sheaf.forget _ Y).map
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app F)).app
      (op W)).hom r

private theorem stalkToPullbackStalk_germ {W : Opens Y}
    (r : ToType (((TopCat.Sheaf.forget _ Y).obj F).obj (op W))) (x : X) (hx : f x ∈ W) :
    (stalkToPullbackStalk f F x).hom (((TopCat.Sheaf.forget _ Y).obj F).germ W (f x) hx r) =
      ((TopCat.Sheaf.forget _ X).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj F)).germ
        ((Opens.map f).obj W) x hx (unitSec f F r) := by
  have h : ((TopCat.Sheaf.forget _ Y).obj F).germ W (f x) hx ≫ stalkToPullbackStalk f F x =
      ((TopCat.Sheaf.forget _ Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app F)).app
          (op W) ≫ ((TopCat.Sheaf.forget _ X).obj
            ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj F)).germ ((Opens.map f).obj W) x
              hx := by
    unfold stalkToPullbackStalk
    erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc, TopCat.Presheaf.stalkPushforward_germ]
    rfl
  exact congrArg (fun φ => φ.hom r) h

/-- The canonical map `F_{f(x)} ⟶ (f⁻¹F)_x` is an isomorphism: it is the inverse of
`Stacks.SheafifyStalk.stalkSheafPullbackIso`. -/
lemma isIso_stalkToPullbackStalk (x : X) : IsIso (stalkToPullbackStalk f F x) := by
  have e : stalkToPullbackStalk f F x =
      (Stacks.SheafifyStalk.stalkSheafPullbackIso _ f F x).inv :=
    (Stacks.SheafifyStalk.stalkSheafPullbackIso_inv_eq _ f F x).symm
  rw [e]
  exact (Stacks.SheafifyStalk.stalkSheafPullbackIso _ f F x).isIso_inv

private theorem bijective_stalkToPullbackStalk (x : X) :
    Function.Bijective (stalkToPullbackStalk f F x).hom := by
  have := isIso_stalkToPullbackStalk f F x
  exact ConcreteCategory.bijective_of_isIso (stalkToPullbackStalk f F x)

/-- Every section of `f^* F` is, near each point, the image of a section of `F`. -/
private theorem exists_local_germ {U : Opens X}
    (s : ToType (((TopCat.Sheaf.forget _ X).obj
      ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj F)).obj (op U))) (x₀ : X) (hx₀ : x₀ ∈ U) :
    ∃ (W : Opens Y) (r : ToType (((TopCat.Sheaf.forget _ Y).obj F).obj (op W))) (N : Opens X)
      (_ : x₀ ∈ N) (hNU : N ≤ U) (hNW : N ≤ (Opens.map f).obj W),
      ∀ x (hx : x ∈ N), ((TopCat.Sheaf.forget _ X).obj
        ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj F)).germ U x (hNU hx) s =
        (stalkToPullbackStalk f F x).hom
          (((TopCat.Sheaf.forget _ Y).obj F).germ W (f x) (hNW hx) r) := by
  obtain ⟨y, hy⟩ := (bijective_stalkToPullbackStalk f F x₀).2
    (((TopCat.Sheaf.forget _ X).obj
      ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj F)).germ U x₀ hx₀ s)
  obtain ⟨W, hW, r, rfl⟩ := ((TopCat.Sheaf.forget _ Y).obj F).exists_germ_eq y
  rw [stalkToPullbackStalk_germ] at hy
  obtain ⟨N, hN, iW, iU, e⟩ := ((TopCat.Sheaf.forget _ X).obj
    ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj F)).germ_eq x₀ _ _ _ _ hy
  refine ⟨W, r, N, hN, iU.le, iW.le, fun x hx => ?_⟩
  rw [← TopCat.Presheaf.germ_res_apply _ iU x hx, ← e, TopCat.Presheaf.germ_res_apply]
  exact (stalkToPullbackStalk_germ f F r x _).symm

end Pullback

/-! ### Germs of constant sheaves -/

section ConstantSheafGerms

variable {V : TopCat.{0}} (E : ModuleCat.{0} ℚ)

/-- The constant section `e` of the constant sheaf with value `E`. -/
private def constSection (e : E) :
    ToType (((TopCat.Sheaf.forget _ V).obj
      ((constantSheaf (Opens.grothendieckTopology V) (ModuleCat.{0} ℚ)).obj E)).obj (op ⊤)) :=
  ((CategoryTheory.toSheafify (Opens.grothendieckTopology V)
    ((Functor.const (Opens V)ᵒᵖ).obj E)).app (op ⊤)).hom e

private theorem constSection_zero : constSection (V := V) E 0 = 0 :=
  map_zero _

/-- Every germ of a constant sheaf is the germ of a constant section. -/
private theorem constantSheaf_exists_constSection_germ (p : V)
    (c : ToType (((TopCat.Sheaf.forget _ V).obj
      ((constantSheaf (Opens.grothendieckTopology V) (ModuleCat.{0} ℚ)).obj E)).stalk p)) :
    ∃ e : E, ((TopCat.Sheaf.forget _ V).obj
      ((constantSheaf (Opens.grothendieckTopology V) (ModuleCat.{0} ℚ)).obj E)).germ
          ⊤ p (Opens.mem_top p) (constSection E e) = c := by
  let K : TopCat.Presheaf (ModuleCat.{0} ℚ) V := (Functor.const (Opens V)ᵒᵖ).obj E
  have hiso := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso p (ModuleCat.{0} ℚ) K
  obtain ⟨c', hc'⟩ := (ConcreteCategory.bijective_of_isIso
    ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) p).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology V) K))).2 c
  obtain ⟨U, hU, e, rfl⟩ := K.exists_germ_eq c'
  refine ⟨e, ?_⟩
  have this : K.germ U p hU e = K.germ ⊤ p (Opens.mem_top p) e :=
    TopCat.Presheaf.germ_res_apply K (homOfLE (le_top : U ≤ ⊤)) p hU e
  rw [← hc', this]
  exact (TopCat.Presheaf.stalkFunctor_map_germ_apply (F := K) ⊤ p (Opens.mem_top p)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology V) K) e).symm

/-- A constant section with vanishing germ is zero. -/
private theorem eq_zero_of_germ_constSection {e : E} (p : V)
    (h : ((TopCat.Sheaf.forget _ V).obj
      ((constantSheaf (Opens.grothendieckTopology V) (ModuleCat.{0} ℚ)).obj E)).germ
        ⊤ p (Opens.mem_top p) (constSection E e) = 0) : e = 0 := by
  let K : TopCat.Presheaf (ModuleCat.{0} ℚ) V := (Functor.const (Opens V)ᵒᵖ).obj E
  have hiso := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso p (ModuleCat.{0} ℚ) K
  have e1 := TopCat.Presheaf.stalkFunctor_map_germ_apply (F := K) ⊤ p (Opens.mem_top p)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology V) K) e
  have h2 : K.germ ⊤ p (Opens.mem_top p) e = K.germ ⊤ p (Opens.mem_top p) 0 := by
    apply (ConcreteCategory.bijective_of_isIso ((TopCat.Presheaf.stalkFunctor
      (ModuleCat.{0} ℚ) p).map (CategoryTheory.toSheafify (Opens.grothendieckTopology V) K))).1
    refine e1.trans (h.trans ?_)
    exact ((congrArg _ (map_zero _)).trans (map_zero _)).symm
  obtain ⟨W, -, i₁, i₂, he⟩ := K.germ_eq p (Opens.mem_top p) (Opens.mem_top p) e 0 h2
  exact he

/-- Near every point, a section of a constant sheaf has the germs of a constant section. -/
private theorem constantSheaf_exists_constSection {U : Opens V}
    (sec : ToType (((TopCat.Sheaf.forget _ V).obj
      ((constantSheaf (Opens.grothendieckTopology V) (ModuleCat.{0} ℚ)).obj E)).obj (op U)))
    (p : V) (hp : p ∈ U) :
    ∃ (e : E) (N : Opens V) (_ : p ∈ N) (hNU : N ≤ U), ∀ v (hv : v ∈ N),
      ((TopCat.Sheaf.forget _ V).obj
        ((constantSheaf (Opens.grothendieckTopology V) (ModuleCat.{0} ℚ)).obj E)).germ U v
          (hNU hv) sec =
        ((TopCat.Sheaf.forget _ V).obj
          ((constantSheaf (Opens.grothendieckTopology V) (ModuleCat.{0} ℚ)).obj E)).germ ⊤ v
            (Opens.mem_top v) (constSection E e) := by
  obtain ⟨e, he⟩ := constantSheaf_exists_constSection_germ E p
    (((TopCat.Sheaf.forget _ V).obj
      ((constantSheaf (Opens.grothendieckTopology V) (ModuleCat.{0} ℚ)).obj E)).germ U p hp sec)
  obtain ⟨W, hW, iU, iT, hWe⟩ := TopCat.Presheaf.germ_eq _ p hp (Opens.mem_top p) sec
    (constSection E e) he.symm
  refine ⟨e, W, hW, iU.le, fun v hv => ?_⟩
  exact (TopCat.Presheaf.germ_res_apply _ iU v hv sec).symm.trans
    ((congrArg _ hWe).trans (TopCat.Presheaf.germ_res_apply _ iT v hv _))

end ConstantSheafGerms

/-! ### Flat families of germs -/

section Flat

variable {Z : TopCat.{0}} (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Z)

/-- The identification of stalks at equal points. -/
private def castStalk {z z' : Z} (h : z = z') :
    ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk z) ≃ₗ[ℚ]
      ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk z') :=
  h ▸ LinearEquiv.refl ℚ _

private theorem castStalk_eq_cast {z z' : Z} (h : z = z')
    (hT : ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk z) =
      ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk z'))
    (v : ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk z)) :
    castStalk F h v = cast hT v := by
  subst h; rfl

private theorem castStalk_self {z : Z} (h : z = z)
    (v : ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk z)) : castStalk F h v = v := rfl

private theorem castStalk_castStalk {z z' z'' : Z} (h : z = z') (h' : z' = z'')
    (v : ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk z)) :
    castStalk F h' (castStalk F h v) = castStalk F (h.trans h') v := by
  subst h h'; rfl

private theorem castStalk_germ {z z' : Z} (h : z = z') {W : Opens Z} (hz : z ∈ W)
    (r : ToType (((TopCat.Sheaf.forget _ Z).obj F).obj (op W))) :
    castStalk F h (((TopCat.Sheaf.forget _ Z).obj F).germ W z hz r) =
      ((TopCat.Sheaf.forget _ Z).obj F).germ W z' (h ▸ hz) r := by
  subst h; rfl

private theorem castStalk_dep {A : Type} (f : A → Z)
    (Y : ∀ a, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (f a))) {a b : A} (h : a = b) :
    castStalk F (congrArg f h) (Y a) = Y b := by
  subst h; rfl

/-- The family of germs `Y` along `f` is given near `a₀` by a section of `F`. -/
private def IsFlatAt {A : Type} [TopologicalSpace A] (f : A → Z)
    (Y : ∀ a, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (f a))) (a₀ : A) : Prop :=
  ∃ (W : Opens Z) (r : ToType (((TopCat.Sheaf.forget _ Z).obj F).obj (op W))) (N : Set A)
    (_ : IsOpen N) (_ : a₀ ∈ N) (hNW : ∀ a ∈ N, f a ∈ W),
    ∀ a (ha : a ∈ N), Y a = ((TopCat.Sheaf.forget _ Z).obj F).germ W (f a) (hNW a ha) r

/-- A *flat family* along `f`: a family of germs which is locally given by sections. -/
private def IsFlat {A : Type} [TopologicalSpace A] (f : A → Z)
    (Y : ∀ a, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (f a))) : Prop :=
  ∀ a₀, IsFlatAt F f Y a₀

variable {F}

private theorem IsFlatAt.congr {A : Type} [TopologicalSpace A] {f : A → Z}
    {Y Y' : ∀ a, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (f a))} {a₀ : A}
    (h : IsFlatAt F f Y a₀) {S : Set A} (hS : IsOpen S) (ha₀ : a₀ ∈ S)
    (hYY : ∀ a ∈ S, Y' a = Y a) : IsFlatAt F f Y' a₀ := by
  obtain ⟨W, r, N, hN, haN, hNW, hloc⟩ := h
  refine ⟨W, r, N ∩ S, hN.inter hS, ⟨haN, ha₀⟩, fun a ha => hNW a ha.1, fun a ha => ?_⟩
  rw [hYY a ha.2]
  exact hloc a ha.1

private theorem IsFlatAt.comp {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    {f : A → Z} {Y : ∀ a, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (f a))}
    {g : B → A} (hg : Continuous g) {b₀ : B} (h : IsFlatAt F f Y (g b₀)) :
    IsFlatAt F (fun b => f (g b)) (fun b => Y (g b)) b₀ := by
  obtain ⟨W, r, N, hN, haN, hNW, hloc⟩ := h
  exact ⟨W, r, g ⁻¹' N, hN.preimage hg, haN, fun b hb => hNW _ hb, fun b hb => hloc _ hb⟩

private theorem IsFlat.comp {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    {f : A → Z} {Y : ∀ a, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (f a))}
    (h : IsFlat F f Y) {g : B → A} (hg : Continuous g) :
    IsFlat F (fun b => f (g b)) (fun b => Y (g b)) := fun b₀ => (h (g b₀)).comp hg

private theorem IsFlat.cast {A : Type} [TopologicalSpace A] {f f' : A → Z}
    (hf : ∀ a, f a = f' a)
    {Y : ∀ a, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (f a))} (h : IsFlat F f Y) :
    IsFlat F f' (fun a => castStalk F (hf a) (Y a)) := fun a₀ => by
  obtain ⟨W, r, N, hN, haN, hNW, hloc⟩ := h a₀
  refine ⟨W, r, N, hN, haN, fun a ha => hf a ▸ hNW a ha, fun a ha => ?_⟩
  change castStalk F (hf a) (Y a) = _
  rw [hloc a ha, castStalk_germ]

/-- A constant family along a constant map is flat. -/
private theorem isFlat_const {A : Type} [TopologicalSpace A] (z : Z)
    (w : ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk z)) :
    IsFlat F (fun _ : A => z) (fun _ => w) := by
  intro a₀
  obtain ⟨W, hW, r, rfl⟩ := ((TopCat.Sheaf.forget _ Z).obj F).exists_germ_eq w
  exact ⟨W, r, Set.univ, isOpen_univ, trivial, fun _ _ => hW, fun _ _ => rfl⟩

variable (F) in
/-- The flat families along `f`, as a submodule of all families of germs. -/
private def flatSub {A : Type} [TopologicalSpace A] (f : A → Z) :
    Submodule ℚ (∀ a, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (f a))) where
  carrier := {Y | IsFlat F f Y}
  zero_mem' := by
    intro a₀
    refine ⟨⊤, 0, Set.univ, isOpen_univ, trivial, fun _ _ => trivial, fun a _ => ?_⟩
    rw [map_zero]
    rfl
  add_mem' := by
    intro Y₁ Y₂ h₁ h₂ a₀
    obtain ⟨W₁, r₁, N₁, hN₁, ha₁, hNW₁, hloc₁⟩ := h₁ a₀
    obtain ⟨W₂, r₂, N₂, hN₂, ha₂, hNW₂, hloc₂⟩ := h₂ a₀
    let P := (TopCat.Sheaf.forget _ Z).obj F
    refine ⟨W₁ ⊓ W₂, P.map (homOfLE inf_le_left).op r₁ + P.map (homOfLE inf_le_right).op r₂,
      N₁ ∩ N₂, hN₁.inter hN₂, ⟨ha₁, ha₂⟩, fun a ha => ⟨hNW₁ a ha.1, hNW₂ a ha.2⟩,
      fun a ha => ?_⟩
    have e1 := TopCat.Presheaf.germ_res_apply P (homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁)) (f a)
      ⟨hNW₁ a ha.1, hNW₂ a ha.2⟩ r₁
    have e2 := TopCat.Presheaf.germ_res_apply P (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)) (f a)
      ⟨hNW₁ a ha.1, hNW₂ a ha.2⟩ r₂
    rw [map_add, e1, e2]
    exact congrArg₂ (· + ·) (hloc₁ a ha.1) (hloc₂ a ha.2)
  smul_mem' := by
    intro c Y h a₀
    obtain ⟨W, r, N, hN, ha, hNW, hloc⟩ := h a₀
    refine ⟨W, c • r, N, hN, ha, hNW, fun a ha => ?_⟩
    rw [map_smul, Pi.smul_apply, hloc a ha]

end Flat

/-! ### Uniqueness of flat families -/

section LocalSystem

variable {Z : TopCat.{0}} {F : TopCat.Sheaf (ModuleCat.{0} ℚ) Z}

/-- **The support of a section of a local system is open.** -/
private theorem exists_germ_ne_zero (hF : IsLocalSystem F) {W : Opens Z}
    (r : ToType (((TopCat.Sheaf.forget _ Z).obj F).obj (op W))) (z₀ : Z) (hz₀ : z₀ ∈ W)
    (h : ((TopCat.Sheaf.forget _ Z).obj F).germ W z₀ hz₀ r ≠ 0) :
    ∃ (N : Opens Z) (_ : z₀ ∈ N) (hNW : N ≤ W), ∀ z (hz : z ∈ N),
      ((TopCat.Sheaf.forget _ Z).obj F).germ W z (hNW hz) r ≠ 0 := by
  obtain ⟨V, hz₀V, E, -, ⟨φ⟩⟩ := hF z₀
  let ι := V.inclusion'
  let C := (TopCat.Sheaf.forget _ _).obj
    ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat Z).obj V))
      (ModuleCat.{0} ℚ)).obj E)
  let ρ := unitSec ι F r
  let sec : ToType (C.obj (op ((Opens.map ι).obj W))) :=
    (((TopCat.Sheaf.forget _ _).map φ.hom).app (op ((Opens.map ι).obj W))).hom ρ
  let M := fun v : (Opens.toTopCat Z).obj V =>
    ((TopCat.Presheaf.stalkFunctor _ v).mapIso ((TopCat.Sheaf.forget _ _).mapIso φ)).hom.hom
  have hg : ∀ (v : (Opens.toTopCat Z).obj V) (hv : ι v ∈ W),
      C.germ _ v hv sec = M v ((stalkToPullbackStalk ι F v).hom
        (((TopCat.Sheaf.forget _ Z).obj F).germ W (ι v) hv r)) := by
    intro v hv
    rw [stalkToPullbackStalk_germ]
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply _ v hv _ ρ).symm
  have hinj : ∀ v : (Opens.toTopCat Z).obj V,
      Function.Injective (M v ∘ (stalkToPullbackStalk ι F v).hom) := fun v =>
    ((TopCat.Presheaf.stalkFunctor _ v).mapIso
      ((TopCat.Sheaf.forget _ _).mapIso φ)).toLinearEquiv.injective.comp
      (bijective_stalkToPullbackStalk ι F v).1
  let v₀ : (Opens.toTopCat Z).obj V := ⟨z₀, hz₀V⟩
  obtain ⟨e, N, hv₀N, hNU, hloc⟩ := constantSheaf_exists_constSection E sec v₀ hz₀
  have he : e ≠ 0 := by
    rintro rfl
    apply h
    apply hinj v₀
    have h1 := (hg v₀ hz₀).symm.trans (hloc v₀ hv₀N)
    rw [constSection_zero, map_zero] at h1
    exact h1.trans ((congrArg (M v₀) (map_zero _)).trans (map_zero _)).symm
  refine ⟨⟨Subtype.val '' (N : Set ((Opens.toTopCat Z).obj V)),
    V.isOpen.isOpenMap_subtype_val _ N.isOpen⟩, ⟨v₀, hv₀N, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact hNU hv
  · rintro _ ⟨v, hv, rfl⟩ h0
    apply he
    apply eq_zero_of_germ_constSection (V := (Opens.toTopCat Z).obj V) E v
    have h1 := (hloc v hv).symm.trans (hg v (hNU hv))
    have h0' : ((TopCat.Sheaf.forget _ Z).obj F).germ W (ι v) (hNU hv) r = 0 := h0
    exact h1.trans ((congrArg (fun y => M v ((stalkToPullbackStalk ι F v).hom y)) h0').trans
      ((congrArg (M v) (map_zero _)).trans (map_zero _)))

/-- **Uniqueness of flat families.** On a preconnected space, a flat family of germs of a local
system vanishing at one point vanishes everywhere. -/
private theorem IsFlat.eq_zero (hF : IsLocalSystem F) {A : Type} [TopologicalSpace A]
    [PreconnectedSpace A] {f : A → Z} (hf : Continuous f)
    {Y : ∀ a, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (f a))} (hY : IsFlat F f Y)
    {a₀ : A} (h0 : Y a₀ = 0) (a : A) : Y a = 0 := by
  let P := (TopCat.Sheaf.forget _ Z).obj F
  have hA : IsClopen {a | Y a = 0} := by
    constructor
    · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
      intro a ha
      obtain ⟨W, r, N, hN, haN, hNW, hloc⟩ := hY a
      have hne : P.germ W (f a) (hNW a haN) r ≠ 0 := by
        rw [← hloc a haN]
        exact ha
      obtain ⟨N', hN', hN'W, hne'⟩ := exists_germ_ne_zero hF r (f a) (hNW a haN) hne
      refine ⟨N ∩ f ⁻¹' N', fun a' ha' => ?_, hN.inter (N'.isOpen.preimage hf), ⟨haN, hN'⟩⟩
      change Y a' ≠ 0
      rw [hloc a' ha'.1]
      exact hne' _ ha'.2
    · rw [isOpen_iff_forall_mem_open]
      intro a ha
      obtain ⟨W, r, N, hN, haN, hNW, hloc⟩ := hY a
      have h0' : P.germ W (f a) (hNW a haN) r = P.germ W (f a) (hNW a haN) 0 := by
        rw [← hloc a haN, map_zero]
        exact ha
      obtain ⟨W', hW', iU, iV, he⟩ := P.germ_eq (f a) (hNW a haN) (hNW a haN) r 0 h0'
      refine ⟨N ∩ f ⁻¹' W', fun a' ha' => ?_, hN.inter (W'.isOpen.preimage hf), ⟨haN, hW'⟩⟩
      change Y a' = 0
      rw [hloc a' ha'.1, ← TopCat.Presheaf.germ_res_apply P iU (f a') ha'.2 r, he, map_zero,
        map_zero]
  exact Set.eq_univ_iff_forall.mp (hA.eq_univ ⟨a₀, h0⟩) a

/-- Two flat families on a preconnected space which agree at one point agree everywhere. -/
private theorem IsFlat.ext (hF : IsLocalSystem F) {A : Type} [TopologicalSpace A]
    [PreconnectedSpace A] {f : A → Z} (hf : Continuous f)
    {Y₁ Y₂ : ∀ a, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (f a))} (h₁ : IsFlat F f Y₁)
    (h₂ : IsFlat F f Y₂) {a₀ : A} (h0 : Y₁ a₀ = Y₂ a₀) (a : A) : Y₁ a = Y₂ a := by
  have hsub : IsFlat F f (Y₁ - Y₂) := (flatSub F f).sub_mem h₁ h₂
  simpa [sub_eq_zero] using hsub.eq_zero hF hf (a₀ := a₀) (by simp [h0]) a

end LocalSystem

/-! ### Trivializing opens -/

section Good

variable {Z : TopCat.{0}} (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Z)

/-- An open `V` is *good* when every germ at a point of `V` extends to a family of germs which is
flat at every point of `V`. -/
private def IsGood (V : Opens Z) : Prop :=
  ∀ z' ∈ V, ∀ y' : ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk z'),
    ∃ Zf : ∀ z : Z, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk z), Zf z' = y' ∧
      ∀ z₀ ∈ V, IsFlatAt F (fun z => z) Zf z₀

variable {F} in
/-- Every point of a local system has a good neighbourhood. -/
private theorem exists_isGood (hF : IsLocalSystem F) (z : Z) :
    ∃ V : Opens Z, z ∈ V ∧ IsGood F V := by
  obtain ⟨V, hz, E, -, ⟨φ⟩⟩ := hF z
  classical
  refine ⟨V, hz, fun z' hz' y' => ?_⟩
  let ι := V.inclusion'
  let P := (TopCat.Sheaf.forget _ Z).obj F
  let Q := (TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) ι).obj F)
  let pt : (Opens.toTopCat Z).obj V := ⟨z', hz'⟩
  let y'' := (stalkToPullbackStalk ι F pt).hom y'
  obtain ⟨e₀, hσc⟩ := constantSheaf_exists_constSection_germ E pt
    (((TopCat.Presheaf.stalkFunctor _ pt).map ((TopCat.Sheaf.forget _ _).map φ.hom)).hom y'')
  let s : ToType (Q.obj (op ⊤)) :=
    (((TopCat.Sheaf.forget _ _).map φ.inv).app (op ⊤)).hom (constSection E e₀)
  have hs : Q.germ ⊤ pt trivial s = y'' := by
    have e1 := TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ pt trivial
      ((TopCat.Sheaf.forget _ _).map φ.inv) (constSection E e₀)
    refine e1.symm.trans ?_
    erw [hσc, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp,
      φ.hom_inv_id, CategoryTheory.Functor.map_id]
    rfl
  have hbij := fun (v : (Opens.toTopCat Z).obj V) => bijective_stalkToPullbackStalk ι F v
  let Y : ∀ z : Z, ToType (P.stalk z) := fun z => if h : z ∈ V then
    (Equiv.ofBijective _ (hbij ⟨z, h⟩)).symm (Q.germ ⊤ ⟨z, h⟩ trivial s) else 0
  have hY : ∀ z (h : z ∈ V), (stalkToPullbackStalk ι F ⟨z, h⟩).hom (Y z) =
      Q.germ ⊤ ⟨z, h⟩ trivial s := by
    intro z h
    have e : Y z = (Equiv.ofBijective _ (hbij ⟨z, h⟩)).symm (Q.germ ⊤ ⟨z, h⟩ trivial s) := by
      simp [Y, h]; rfl
    rw [e]
    exact (Equiv.ofBijective _ (hbij ⟨z, h⟩)).apply_symm_apply _
  refine ⟨Y, (hbij pt).1 ((hY z' hz').trans hs), fun z₀ hz₀ => ?_⟩
  obtain ⟨W, r, N, hN, _hNU, hNW, hloc⟩ := exists_local_germ ι F s ⟨z₀, hz₀⟩ trivial
  have hNopen : IsOpen (Subtype.val '' (SetLike.coe N : Set V)) :=
    V.isOpen.isOpenMap_subtype_val (SetLike.coe N : Set V) N.isOpen
  refine ⟨W, r, _, hNopen, ⟨_, hN, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact hNW hv
  · rintro _ ⟨v, hv, rfl⟩
    exact (hbij v).1 ((hY v.1 v.2).trans ((hloc v hv).trans rfl))

end Good

/-! ### Flat families along paths -/

section Interval

variable {Z : TopCat.{0}} {F : TopCat.Sheaf (ModuleCat.{0} ℚ) Z}

variable (F) in
/-- Every germ at `γ q` extends to a family along `γ` which is flat at every point up to `q`. -/
private def Reach (γ : I → Z) (q : I) : Prop :=
  ∀ y : ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (γ q)),
    ∃ Y : ∀ x : I, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (γ x)),
      Y q = y ∧ ∀ x₀ ≤ q, IsFlatAt F γ Y x₀

private theorem IsFlatAt.glue {γ : I → Z} (hγ : Continuous γ)
    {Y₁ Y₂ : ∀ x : I, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (γ x))} {q : I}
    (h₁ : IsFlatAt F γ Y₁ q) (h₂ : IsFlatAt F γ Y₂ q) (h : Y₁ q = Y₂ q) :
    IsFlatAt F γ (fun x => if x ≤ q then Y₁ x else Y₂ x) q := by
  classical
  obtain ⟨W₁, r₁, N₁, hN₁, hq₁, hNW₁, hloc₁⟩ := h₁
  obtain ⟨W₂, r₂, N₂, hN₂, hq₂, hNW₂, hloc₂⟩ := h₂
  let P := (TopCat.Sheaf.forget _ Z).obj F
  have e := (hloc₁ q hq₁).symm.trans (h.trans (hloc₂ q hq₂))
  obtain ⟨W, hW, iU, iV, he⟩ := P.germ_eq (γ q) (hNW₁ q hq₁) (hNW₂ q hq₂) r₁ r₂ e
  refine ⟨W, P.map iU.op r₁, N₁ ∩ N₂ ∩ γ ⁻¹' W, (hN₁.inter hN₂).inter (W.isOpen.preimage hγ),
    ⟨⟨hq₁, hq₂⟩, hW⟩, fun x hx => hx.2, fun x hx => ?_⟩
  beta_reduce
  split_ifs
  · rw [hloc₁ x hx.1.1]
    exact (TopCat.Presheaf.germ_res_apply P iU (γ x) hx.2 r₁).symm
  · rw [hloc₂ x hx.1.2, he]
    exact (TopCat.Presheaf.germ_res_apply P iV (γ x) hx.2 r₂).symm

private theorem reach_zero {γ : I → Z} (hγ : Continuous γ) {V : Opens Z} (hV : IsGood F V)
    (h0 : γ 0 ∈ V) : Reach F γ 0 := by
  intro y
  obtain ⟨Zf, hZf, hloc⟩ := hV (γ 0) h0 y
  refine ⟨fun x => Zf (γ x), hZf, fun x₀ hx₀ => ?_⟩
  obtain rfl : x₀ = 0 := le_antisymm hx₀ (unitInterval.nonneg x₀)
  exact (hloc _ h0).comp hγ

private theorem Reach.propagate {γ : I → Z} (hγ : Continuous γ) {q q' : I} (hq : Reach F γ q)
    (hqq' : q ≤ q') {V : Opens Z} (hV : IsGood F V) (hγV : ∀ x, q ≤ x → x ≤ q' → γ x ∈ V) :
    Reach F γ q' := by
  classical
  intro y'
  obtain ⟨Zf, hZf, hloc⟩ := hV (γ q') (hγV q' hqq' le_rfl) y'
  obtain ⟨Y₁, hY₁, hl₁⟩ := hq (Zf (γ q))
  refine ⟨fun x => if x ≤ q then Y₁ x else Zf (γ x), ?_, fun x₀ hx₀ => ?_⟩
  · beta_reduce
    split_ifs with h
    · obtain rfl : q' = q := le_antisymm h hqq'
      exact hY₁.trans hZf
    · exact hZf
  · rcases lt_trichotomy x₀ q with h | rfl | h
    · refine (hl₁ x₀ h.le).congr (isOpen_lt continuous_id continuous_const) h ?_
      intro x hx
      simp [le_of_lt (show x < q from hx)]
    · exact IsFlatAt.glue hγ (hl₁ x₀ le_rfl) ((hloc _ (hγV x₀ le_rfl hqq')).comp hγ) hY₁
    · refine ((hloc _ (hγV x₀ h.le hx₀)).comp hγ).congr
        (isOpen_lt continuous_const continuous_id) h ?_
      intro x hx
      simp [not_le.2 (show q < x from hx)]

private theorem reach (hF : IsLocalSystem F) {γ : I → Z} (hγ : Continuous γ) (q : I) :
    Reach F γ q := by
  choose V hV hext using fun z => exists_isGood hF z
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (s := Set.univ)
    (c := fun z => γ ⁻¹' (V z : Set Z)) isCompact_univ
    (fun z => (V z).isOpen.preimage hγ)
    (fun x _ => Set.mem_iUnion.2 ⟨γ x, hV (γ x)⟩)
  let qs : ℕ → I := fun n => ⟨min (q : ℝ) (n * (δ / 2)), le_min q.2.1 (by positivity),
    (min_le_left _ _).trans q.2.2⟩
  have hq : ∀ n, Reach F γ (qs n) := by
    intro n
    induction n with
    | zero =>
      obtain ⟨z, hz⟩ := hball 0 trivial
      have h0 : qs 0 = 0 := by ext; simp [qs, q.2.1]
      rw [h0]
      exact reach_zero hγ (hext z) (hz (Metric.mem_ball_self hδ))
    | succ n ih =>
      obtain ⟨z, hz⟩ := hball (qs n) trivial
      refine ih.propagate hγ ?_ (hext z) fun x hx hx' => hz ?_
      · change min (q : ℝ) (n * (δ / 2)) ≤ min (q : ℝ) ((n + 1 : ℕ) * (δ / 2))
        gcongr
        exact_mod_cast Nat.le_succ n
      · rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_lt]
        have h1 : ((x : I) : ℝ) ≤ min (q : ℝ) ((n + 1 : ℕ) * (δ / 2)) := hx'
        have h2 : min (q : ℝ) (n * (δ / 2)) ≤ ((x : I) : ℝ) := hx
        have h3 : min (q : ℝ) ((n + 1 : ℕ) * (δ / 2)) ≤ min (q : ℝ) (n * (δ / 2)) + δ / 2 := by
          push_cast
          rcases le_total (q : ℝ) (n * (δ / 2)) with h | h
          · rw [min_eq_left h, min_eq_left (by nlinarith)]
            linarith
          · rw [min_eq_right h]
            exact (min_le_right _ _).trans (by nlinarith)
        change -δ < (x : ℝ) - min (q : ℝ) (n * (δ / 2)) ∧ (x : ℝ) - min (q : ℝ) (n * (δ / 2)) < δ
        constructor <;> linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / δ)
  have : qs n = q := by
    ext
    change min (q : ℝ) (n * (δ / 2)) = q
    refine min_eq_left ?_
    rw [div_lt_iff₀ hδ] at hn
    nlinarith [q.2.2]
  rw [← this]
  exact hq n

/-- **Existence of flat families along a path**, with a prescribed value at `0`. -/
private theorem exists_isFlat_zero (hF : IsLocalSystem F) {γ : I → Z} (hγ : Continuous γ)
    (y : ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (γ 0))) :
    ∃ Y, IsFlat F γ Y ∧ Y 0 = y := by
  have hs : Continuous (fun x => γ (σ x)) := hγ.comp continuous_symm
  have e1 : γ 0 = γ (σ 1) := by rw [symm_one]
  obtain ⟨Y', hY'1, hY'⟩ := reach hF hs 1 (castStalk F e1 y)
  have hY'f : IsFlat F (fun x => γ (σ x)) Y' := fun x₀ => hY' x₀ (le_one x₀)
  have hss : ∀ x, γ (σ (σ x)) = γ x := fun x => by rw [symm_symm]
  refine ⟨fun x => castStalk F (hss x) (Y' (σ x)), (hY'f.comp continuous_symm).cast hss, ?_⟩
  have h01 : (1 : I) = σ 0 := symm_zero.symm
  change castStalk F (hss 0) (Y' (σ 0)) = y
  rw [← castStalk_dep F (fun x => γ (σ x)) Y' h01, hY'1, castStalk_castStalk,
    castStalk_castStalk, castStalk_self]

/-- **Existence of flat families along a path**, with a prescribed value anywhere. -/
private theorem exists_isFlat (hF : IsLocalSystem F) {γ : I → Z} (hγ : Continuous γ) (a : I)
    (y : ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (γ a))) :
    ∃ Y, IsFlat F γ Y ∧ Y a = y := by
  obtain ⟨Y₁, hY₁a, hY₁⟩ := reach hF hγ a y
  obtain ⟨Y, hY, hY0⟩ := exists_isFlat_zero hF hγ (Y₁ 0)
  refine ⟨Y, hY, ?_⟩
  have : PreconnectedSpace (Set.Iic a) :=
    Subtype.preconnectedSpace Set.ordConnected_Iic.isPreconnected
  exact (IsFlat.ext hF (f := fun x : Set.Iic a => γ x.1) (hγ.comp continuous_subtype_val)
    (Y₁ := fun x => Y x.1) (Y₂ := fun x => Y₁ x.1) (hY.comp continuous_subtype_val)
    (fun x => (hY₁ x.1 x.2).comp continuous_subtype_val) (a₀ := ⟨0, Set.mem_Iic.2 (nonneg a)⟩)
    hY0 ⟨a, Set.mem_Iic.2 le_rfl⟩).trans hY₁a

end Interval

/-! ### Parallel transport along paths -/

section Transport

variable {Z : TopCat.{0}} {F : TopCat.Sheaf (ModuleCat.{0} ℚ) Z}

variable (F) in
/-- Evaluation of flat families at a point. -/
private def evalFlat (γ : I → Z) (a : I) :
    flatSub F γ →ₗ[ℚ] ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (γ a)) :=
  (LinearMap.proj a).comp (flatSub F γ).subtype

private theorem bijective_evalFlat (hF : IsLocalSystem F) {γ : I → Z} (hγ : Continuous γ)
    (a : I) : Function.Bijective (evalFlat F γ a) := by
  refine ⟨fun Y₁ Y₂ h => Subtype.ext (funext fun b => IsFlat.ext hF hγ Y₁.2 Y₂.2 h b), ?_⟩
  intro y
  obtain ⟨Y, hY, hYa⟩ := exists_isFlat hF hγ a y
  exact ⟨⟨Y, hY⟩, hYa⟩

/-- Flat families along a path are determined by their value at any point. -/
private def flatEquiv (hF : IsLocalSystem F) {γ : I → Z} (hγ : Continuous γ) (a : I) :
    flatSub F γ ≃ₗ[ℚ] ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (γ a)) :=
  LinearEquiv.ofBijective _ (bijective_evalFlat hF hγ a)

/-- Transport along `γ` from `γ a` to `γ b`. -/
private def transport (hF : IsLocalSystem F) {γ : I → Z} (hγ : Continuous γ) (a b : I) :
    ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (γ a)) ≃ₗ[ℚ]
      ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (γ b)) :=
  (flatEquiv hF hγ a).symm.trans (flatEquiv hF hγ b)

private theorem transport_apply (hF : IsLocalSystem F) {γ : I → Z} (hγ : Continuous γ)
    {a b : I} {Y : ∀ x : I, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (γ x))}
    (hY : IsFlat F γ Y) {y : ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (γ a))}
    (h : Y a = y) : transport hF hγ a b y = Y b := by
  have : (flatEquiv hF hγ a).symm y = ⟨Y, hY⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    exact h.symm
  change flatEquiv hF hγ b ((flatEquiv hF hγ a).symm y) = Y b
  rw [this]
  rfl

/-- The parallel transport `T_γ : F_x ≃ F_y` along a path `γ` from `x` to `y`. -/
private def pathTransport (hF : IsLocalSystem F) {x y : Z} (γ : Path x y) :
    ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk x) ≃ₗ[ℚ]
      ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk y) :=
  (castStalk F γ.source.symm).trans ((transport hF γ.continuous 0 1).trans
    (castStalk F γ.target))

/-- The parallel transport carries the value at `0` of a flat family to its value at `1`. -/
private theorem pathTransport_apply (hF : IsLocalSystem F) {x y : Z} (γ : Path x y)
    {Y : ∀ t : I, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (γ t))} (hY : IsFlat F γ Y)
    {w : ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk x)}
    (h0 : Y 0 = castStalk F γ.source.symm w) :
    pathTransport hF γ w = castStalk F γ.target (Y 1) := by
  change castStalk F γ.target (transport hF γ.continuous 0 1 (castStalk F γ.source.symm w)) = _
  rw [transport_apply hF γ.continuous hY h0]

private theorem half_mem (x : I) : (x : ℝ) / 2 ∈ I := by
  constructor <;> linarith [x.2.1, x.2.2]

private theorem half_add_mem (x : I) : ((x : ℝ) + 1) / 2 ∈ I := by
  constructor <;> linarith [x.2.1, x.2.2]

/-- The first half `x ↦ x / 2` of the unit interval. -/
private def halfLeft : C(I, I) :=
  ⟨fun x => ⟨(x : ℝ) / 2, half_mem x⟩,
    (continuous_subtype_val.div_const 2).subtype_mk half_mem⟩

/-- The second half `x ↦ (x + 1) / 2` of the unit interval. -/
private def halfRight : C(I, I) :=
  ⟨fun x => ⟨((x : ℝ) + 1) / 2, half_add_mem x⟩,
    ((continuous_subtype_val.add continuous_const).div_const 2).subtype_mk half_add_mem⟩

private theorem coe_halfLeft (x : I) : (halfLeft x : ℝ) = x / 2 := rfl

private theorem coe_halfRight (x : I) : (halfRight x : ℝ) = (x + 1) / 2 := rfl

private theorem trans_halfLeft {x y z : Z} (γ₁ : Path x y) (γ₂ : Path y z) (t : I) :
    (γ₁.trans γ₂) (halfLeft t) = γ₁ t := by
  rw [Path.trans_apply, dite_eq_left (by rw [coe_halfLeft]; linarith [t.2.2])]
  congr 1
  ext
  simp only [coe_halfLeft]
  ring

private theorem trans_halfRight {x y z : Z} (γ₁ : Path x y) (γ₂ : Path y z) (t : I) :
    (γ₁.trans γ₂) (halfRight t) = γ₂ t := by
  rw [Path.trans_apply]
  split_ifs with h
  · rw [coe_halfRight] at h
    have ht : t = 0 := Subtype.ext (by
      change (t : ℝ) = 0
      linarith [t.2.1])
    subst ht
    rw [γ₂.source]
    convert γ₁.target using 2
    ext
    simp only [coe_halfRight]
    norm_num
  · congr 1
    ext
    simp only [coe_halfRight]
    ring

private theorem halfLeft_one : halfLeft 1 = halfRight 0 := by
  ext
  rw [coe_halfLeft, coe_halfRight]
  norm_num

private theorem halfLeft_zero : halfLeft 0 = 0 := by
  ext
  rw [coe_halfLeft]
  norm_num

private theorem halfRight_one : halfRight 1 = 1 := by
  ext
  rw [coe_halfRight]
  norm_num

/-- **Transport along a concatenation.** -/
private theorem pathTransport_trans (hF : IsLocalSystem F) {x y z : Z} (γ : Path x y)
    (δ : Path y z) :
    pathTransport hF (γ.trans δ) = (pathTransport hF γ).trans (pathTransport hF δ) := by
  ext w
  obtain ⟨Y, hY, hY0⟩ := exists_isFlat_zero hF (γ.trans δ).continuous
    (castStalk F (γ.trans δ).source.symm w)
  have hYγ := (hY.comp halfLeft.continuous).cast (trans_halfLeft γ δ)
  have hYδ := (hY.comp halfRight.continuous).cast (trans_halfRight γ δ)
  rw [pathTransport_apply hF _ hY hY0, LinearEquiv.trans_apply]
  have e1 : Y (halfLeft 0) = castStalk F (congrArg (γ.trans δ) halfLeft_zero.symm) (Y 0) :=
    (castStalk_dep F (γ.trans δ) Y halfLeft_zero.symm).symm
  rw [pathTransport_apply hF γ hYγ (by
    rw [e1, hY0, castStalk_castStalk, castStalk_castStalk])]
  have e2 : Y (halfRight 0) = castStalk F (congrArg (γ.trans δ) halfLeft_one) (Y (halfLeft 1)) :=
    (castStalk_dep F (γ.trans δ) Y halfLeft_one).symm
  rw [pathTransport_apply hF δ hYδ (by
    rw [e2, castStalk_castStalk, castStalk_castStalk, castStalk_castStalk])]
  have e3 : Y (halfRight 1) = castStalk F (congrArg (γ.trans δ) halfRight_one.symm) (Y 1) :=
    (castStalk_dep F (γ.trans δ) Y halfRight_one.symm).symm
  change _ = castStalk F _ (castStalk F _ (Y (halfRight 1)))
  rw [e3, castStalk_castStalk, castStalk_castStalk]

/-- **Flat families on a square.** If every horizontal strip `I × O` of the square is mapped by
`G` into a good open, the vertical transports of a flat family along the left edge form a flat
family on the whole square. -/
private theorem exists_isFlat_square (hF : IsLocalSystem F) {G : I × I → Z} (hG : Continuous G)
    (hgood : ∀ t₀ : I, ∃ V : Opens Z, IsGood F V ∧ ∃ O : Set I, IsOpen O ∧
      _root_.IsPreconnected O ∧ t₀ ∈ O ∧ ∀ u, ∀ t ∈ O, G (u, t) ∈ V)
    (y₀ : ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (G (0, 0)))) :
    ∃ Y : ∀ p, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (G p)), IsFlat F G Y ∧
      Y (0, 0) = y₀ := by
  have hl : Continuous fun t : I => G (0, t) := by fun_prop
  have hv : ∀ t : I, Continuous fun u : I => G (u, t) := fun t => by fun_prop
  obtain ⟨Y₀, hY₀, hY₀0⟩ := exists_isFlat_zero hF hl y₀
  choose W hW hW0 using fun t => exists_isFlat_zero hF (hv t) (Y₀ t)
  refine ⟨fun p => W p.2 p.1, fun p₀ => ?_, (hW0 0).trans hY₀0⟩
  obtain ⟨V, hV, O, hO, hOc, ht₀, hGV⟩ := hgood p₀.2
  obtain ⟨Zf, hZf, hZfl⟩ := hV (G (0, p₀.2)) (hGV 0 _ ht₀) (Y₀ p₀.2)
  have stepa : ∀ t ∈ O, Y₀ t = Zf (G (0, t)) := by
    intro t ht
    haveI : PreconnectedSpace O := Subtype.preconnectedSpace hOc
    have hc : Continuous fun t : O => G (0, t.1) := hl.comp continuous_subtype_val
    exact IsFlat.ext hF (f := fun t : O => G (0, t.1)) hc (Y₁ := fun t => Y₀ t.1)
      (Y₂ := fun t => Zf (G (0, t.1))) (hY₀.comp continuous_subtype_val)
      (fun t => (hZfl _ (hGV 0 t.1 t.2)).comp (g := fun t : O => G (0, t.1)) hc)
      (a₀ := ⟨p₀.2, ht₀⟩) hZf.symm ⟨t, ht⟩
  have stepb : ∀ t ∈ O, ∀ u, W t u = Zf (G (u, t)) := by
    intro t ht u
    exact IsFlat.ext hF (hv t) (hW t)
      (fun u => (hZfl _ (hGV u t ht)).comp (g := fun u : I => G (u, t)) (hv t)) (a₀ := 0)
      ((hW0 t).trans (stepa t ht)) u
  exact ((hZfl _ (hGV p₀.1 p₀.2 ht₀)).comp (g := G) hG).congr (S := Set.univ ×ˢ O)
    (isOpen_univ.prod hO) ⟨trivial, ht₀⟩ (fun p hp => stepb p.2 hp.2 p.1)

/-- Two paths joined by a square whose horizontal strips lie in good opens have the same
transport. -/
private theorem pathTransport_eq_of_square (hF : IsLocalSystem F) {x y : Z} (p q : Path x y)
    {G : I × I → Z} (hG : Continuous G) (h0 : ∀ t, G (0, t) = p t) (h1 : ∀ t, G (1, t) = q t)
    (hb : ∀ u, G (u, 0) = x) (ht : ∀ u, G (u, 1) = y)
    (hgood : ∀ t₀ : I, ∃ V : Opens Z, IsGood F V ∧ ∃ O : Set I, IsOpen O ∧
      _root_.IsPreconnected O ∧ t₀ ∈ O ∧ ∀ u, ∀ t ∈ O, G (u, t) ∈ V) :
    pathTransport hF p = pathTransport hF q := by
  ext w
  obtain ⟨Y, hY, hY0⟩ := exists_isFlat_square hF hG hgood (castStalk F (hb 0).symm w)
  have hp := (hY.comp (g := fun t : I => ((0 : I), t)) (by fun_prop)).cast h0
  have hq := (hY.comp (g := fun t : I => ((1 : I), t)) (by fun_prop)).cast h1
  have hbot := (hY.comp (g := fun u : I => (u, (0 : I))) (by fun_prop)).cast hb
  have htop := (hY.comp (g := fun u : I => (u, (1 : I))) (by fun_prop)).cast ht
  have ebot : ∀ u, castStalk F (hb u) (Y (u, 0)) = w := fun u =>
    IsFlat.ext hF continuous_const hbot (isFlat_const x w) (a₀ := 0)
      (by change castStalk F _ (Y (0, 0)) = w; rw [hY0, castStalk_castStalk]; rfl) u
  have etop : ∀ u, castStalk F (ht u) (Y (u, 1)) = castStalk F (ht 0) (Y (0, 1)) := fun u =>
    IsFlat.ext hF continuous_const htop (isFlat_const y _) (a₀ := 0) rfl u
  rw [pathTransport_apply hF p hp (by
      change castStalk F _ (Y (0, 0)) = _
      rw [hY0, castStalk_castStalk]),
    pathTransport_apply hF q hq (by
      change castStalk F _ (Y (1, 0)) = _
      rw [← ebot 1, castStalk_castStalk])]
  change castStalk F _ (castStalk F _ (Y (0, 1))) = castStalk F _ (castStalk F _ (Y (1, 1)))
  have e : Y (1, 1) = castStalk F (ht 1).symm (castStalk F (ht 0) (Y (0, 1))) := by
    rw [← etop 1, castStalk_castStalk, castStalk_self]
  rw [e, castStalk_castStalk, castStalk_castStalk, castStalk_castStalk, castStalk_castStalk]

private theorem lerp_mem (a b u : I) : (a : ℝ) + u * ((b : ℝ) - a) ∈ I := by
  have ha := a.2
  have hb := b.2
  have hu := u.2
  simp only [Set.mem_Icc] at *
  constructor <;> nlinarith

/-- The affine path `u ↦ a + u (b - a)` in the unit interval. -/
private def lerp (a b : I) : C(I, I) :=
  ⟨fun u => ⟨(a : ℝ) + u * ((b : ℝ) - a), lerp_mem a b u⟩, by fun_prop⟩

private theorem isPreconnected_ball (t : I) (d : ℝ) : _root_.IsPreconnected (Metric.ball t d) := by
  apply Set.OrdConnected.isPreconnected
  constructor
  intro a ha b hb c hc
  simp only [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] at *
  rw [abs_lt] at *
  have h1 : (a : ℝ) ≤ c := hc.1
  have h2 : (c : ℝ) ≤ b := hc.2
  constructor <;> linarith [ha.1, hb.2]

/-- **Homotopy invariance of parallel transport.** -/
private theorem pathTransport_eq_of_homotopic (hF : IsLocalSystem F) {x y : Z} {p q : Path x y}
    (h : p.Homotopic q) : pathTransport hF p = pathTransport hF q := by
  obtain ⟨H⟩ := h
  choose V hV hgood using fun z => exists_isGood hF z
  have hH : Continuous fun st : I × I => H st := by fun_prop
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (s := Set.univ)
    (c := fun z => (fun st : I × I => H st) ⁻¹' (V z : Set Z)) isCompact_univ
    (fun z => (V z).isOpen.preimage hH)
    (fun st _ => Set.mem_iUnion.2 ⟨H st, hV (H st)⟩)
  have key : ∀ s₀ s : I, dist s s₀ < δ →
      pathTransport hF (H.eval s₀) = pathTransport hF (H.eval s) := by
    intro s₀ s hs
    refine pathTransport_eq_of_square hF (H.eval s₀) (H.eval s)
      (G := fun ut => H (lerp s₀ s ut.1, ut.2)) (by fun_prop) (fun t => ?_) (fun t => ?_) (fun u => H.source _) (fun u => H.target _)
      (fun t₀ => ?_)
    · change H (lerp s₀ s 0, t) = H (s₀, t)
      congr 2
      ext
      simp [lerp]
    · change H (lerp s₀ s 1, t) = H (s, t)
      congr 2
      ext
      simp [lerp]
    · obtain ⟨z, hz⟩ := hball (s₀, t₀) trivial
      refine ⟨V z, hgood z, Metric.ball t₀ δ, Metric.isOpen_ball, isPreconnected_ball t₀ δ,
        Metric.mem_ball_self hδ, fun u t ht => hz ?_⟩
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      refine ⟨?_, ht⟩
      rw [Subtype.dist_eq, Real.dist_eq] at hs ⊢
      change |((s₀ : ℝ) + u * ((s : ℝ) - s₀)) - s₀| < δ
      rw [add_sub_cancel_left, abs_mul, abs_of_nonneg u.2.1]
      exact (mul_le_of_le_one_left (abs_nonneg _) u.2.2).trans_lt hs
  have hS : IsClopen {s : I | pathTransport hF (H.eval s) = pathTransport hF p} := by
    constructor
    · rw [← isOpen_compl_iff, Metric.isOpen_iff]
      exact fun s hs => ⟨δ, hδ, fun s' hs' h => hs ((key s s' hs').trans h)⟩
    · rw [Metric.isOpen_iff]
      exact fun s hs => ⟨δ, hδ, fun s' hs' => (key s s' hs').symm.trans hs⟩
  simpa [H.eval_one] using
    (Set.eq_univ_iff_forall.mp (hS.eq_univ ⟨0, by simp [H.eval_zero]⟩) 1).symm

end Transport

/-! ### Trivializations from flat families -/

section Trivialization

variable {Z : TopCat.{0}} {F : TopCat.Sheaf (ModuleCat.{0} ℚ) Z}

/-- A flat family along `f` is the family of germs of a global section of `f^* F`. -/
private theorem exists_section_of_isFlat {A : TopCat.{0}} (f : A ⟶ Z)
    {Y : ∀ a : A, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (f a))} (hY : IsFlat F f Y) :
    ∃ s : ToType (((TopCat.Sheaf.forget _ A).obj
        ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj F)).obj (op ⊤)), ∀ a,
      ((TopCat.Sheaf.forget _ A).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj F)).germ
        ⊤ a trivial s = (stalkToPullbackStalk f F a).hom (Y a) := by
  choose W r N hNo hN hNW hloc using hY
  let G := (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj F
  let P := (TopCat.Sheaf.forget _ A).obj G
  let NO : A → Opens A := fun i => ⟨N i, hNo i⟩
  have hNW' : ∀ i, NO i ≤ (Opens.map f).obj (W i) := fun i a ha => hNW i a ha
  let sf : ∀ i : A, ToType (P.obj (op (NO i))) := fun i =>
    P.map (homOfLE (hNW' i)).op (unitSec f F (r i))
  have hgerm : ∀ i a (ha : a ∈ NO i), P.germ (NO i) a ha (sf i) =
      (stalkToPullbackStalk f F a).hom (Y a) := by
    intro i a ha
    rw [TopCat.Presheaf.germ_res_apply, hloc i a ha]
    exact (stalkToPullbackStalk_germ f F (r i) a _).symm
  have hcompat : TopCat.Presheaf.IsCompatible P NO sf := by
    intro i j
    refine TopCat.Presheaf.section_ext G _ _ _ fun a ha => ?_
    change P.germ _ a ha _ = P.germ _ a ha _
    have h1 := TopCat.Presheaf.germ_res_apply P ((NO i).infLELeft (NO j)) a ha (sf i)
    have h2 := TopCat.Presheaf.germ_res_apply P ((NO i).infLERight (NO j)) a ha (sf j)
    rw [h1, h2, hgerm, hgerm]
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' G NO ⊤ (fun i => homOfLE le_top)
    (fun a _ => Opens.mem_iSup.2 ⟨a, hN a⟩) sf hcompat
  refine ⟨s, fun a => ?_⟩
  rw [← hgerm a a (hN a), ← hs a]
  exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm

omit F in
/-- The unit of the constant sheaf adjunction is the sheafification map on global sections. -/
private theorem constantSheafAdj_unit_app {A : TopCat.{0}} (E : ModuleCat.{0} ℚ) :
    (constantSheafAdj (Opens.grothendieckTopology A) (ModuleCat.{0} ℚ) isTerminalTop).unit.app E =
      (toSheafify (Opens.grothendieckTopology A) ((Functor.const (Opens A)ᵒᵖ).obj E)).app
        (op ⊤) := by
  simp [constantSheafAdj, Adjunction.comp_unit_app]
  rfl

/-- **Trivialization by flat families.** A linear family `Φ` of flat families along `f` whose
evaluations are bijective at every point identifies `f^* F` with the constant sheaf. -/
private theorem exists_iso_constantSheaf {A : TopCat.{0}} (f : A ⟶ Z) (E : ModuleCat.{0} ℚ)
    (Φ : E →ₗ[ℚ] ∀ a : A, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (f a)))
    (hΦ : ∀ v, IsFlat F f (Φ v)) (hbij : ∀ a, Function.Bijective fun v => Φ v a) :
    ∃ φ : (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj F ≅
        (constantSheaf (Opens.grothendieckTopology A) (ModuleCat.{0} ℚ)).obj E,
      ∀ (a : A) (v : E),
        (TopCat.Presheaf.stalkFunctor _ a).map ((TopCat.Sheaf.forget _ _).map φ.hom)
          (stalkToPullbackStalk f F a (Φ v a)) =
        ((TopCat.Sheaf.forget _ _).obj ((constantSheaf (Opens.grothendieckTopology A)
          (ModuleCat.{0} ℚ)).obj E)).germ ⊤ a (Opens.mem_top _)
            ((toSheafify (Opens.grothendieckTopology A) ((Functor.const _).obj E)).app (op ⊤)
              v) := by
  let G := (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj F
  let Q := (TopCat.Sheaf.forget _ A).obj G
  let C := (constantSheaf (Opens.grothendieckTopology A) (ModuleCat.{0} ℚ)).obj E
  let CP := (TopCat.Sheaf.forget _ A).obj C
  choose s hs using fun v => exists_section_of_isFlat f (hΦ v)
  have hext : ∀ v (t : ToType (Q.obj (op ⊤))),
      (∀ a, Q.germ ⊤ a trivial t = (stalkToPullbackStalk f F a).hom (Φ v a)) → t = s v :=
    fun v t ht => TopCat.Presheaf.section_ext G ⊤ t (s v) (fun a _ => (ht a).trans (hs v a).symm)
  let S : E →ₗ[ℚ] ToType (Q.obj (op ⊤)) :=
    { toFun := s
      map_add' := fun v w => (hext (v + w) (s v + s w) fun a => by
        rw [map_add, hs v a, hs w a, map_add, Pi.add_apply, map_add]).symm
      map_smul' := fun c v => (hext (c • v) (c • s v) fun a => by
        rw [map_smul, hs v a, map_smul, Pi.smul_apply, map_smul]).symm }
  let adj := constantSheafAdj (Opens.grothendieckTopology A) (ModuleCat.{0} ℚ) isTerminalTop
  let θ : E ⟶ ((sheafSections _ _).obj (op ⊤)).obj G := ModuleCat.ofHom S
  let φhom : C ⟶ G := (adj.homEquiv E G).symm θ
  have hφθ : adj.unit.app E ≫ ((sheafSections _ _).obj (op ⊤)).map φhom = θ :=
    (adj.homEquiv_unit E G φhom).symm.trans ((adj.homEquiv E G).apply_symm_apply θ)
  have hval : ∀ v, ((TopCat.Sheaf.forget _ A).map φhom).app (op ⊤) (constSection E v) = s v := by
    intro v
    have := ConcreteCategory.congr_hom hφθ v
    rwa [ConcreteCategory.comp_apply, constantSheafAdj_unit_app] at this
  have hstalk : ∀ a v, (TopCat.Presheaf.stalkFunctor _ a).map ((TopCat.Sheaf.forget _ A).map φhom)
      (CP.germ ⊤ a trivial (constSection E v)) = (stalkToPullbackStalk f F a).hom (Φ v a) := by
    intro a v
    refine (TopCat.Presheaf.stalkFunctor_map_germ_apply (F := CP) ⊤ a trivial
      ((TopCat.Sheaf.forget _ A).map φhom) _).trans ?_
    exact (congrArg _ (hval v)).trans (hs v a)
  have hiso : ∀ a, IsIso ((TopCat.Presheaf.stalkFunctor _ a).map
      ((TopCat.Sheaf.forget _ A).map φhom)) := by
    intro a
    have hb := bijective_stalkToPullbackStalk f F a
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · rw [injective_iff_map_eq_zero]
      intro c hc
      obtain ⟨v, rfl⟩ := constantSheaf_exists_constSection_germ E a c
      rw [hstalk] at hc
      have h1 : Φ v a = 0 := hb.1 (hc.trans (map_zero _).symm)
      have h2 : v = 0 := (hbij a).1 (h1.trans (congrFun (map_zero Φ) a).symm)
      rw [h2, constSection_zero]
      exact map_zero _
    · intro z
      obtain ⟨y, rfl⟩ := hb.2 z
      obtain ⟨v, rfl⟩ := (hbij a).2 y
      exact ⟨_, hstalk a v⟩
  haveI : ∀ a, IsIso ((TopCat.Presheaf.stalkFunctor _ a).map φhom.hom) := hiso
  have hφ : IsIso φhom := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso φhom
  let e : C ≅ G := @asIso _ _ _ _ φhom hφ
  refine ⟨e.symm, fun a v => ?_⟩
  have key : (TopCat.Presheaf.stalkFunctor _ a).map ((TopCat.Sheaf.forget _ A).map φhom) ≫
      (TopCat.Presheaf.stalkFunctor _ a).map ((TopCat.Sheaf.forget _ A).map e.symm.hom) =
        𝟙 _ :=
    ((TopCat.Presheaf.stalkFunctor _ a).mapIso ((TopCat.Sheaf.forget _ A).mapIso e)).hom_inv_id
  rw [← hstalk]
  exact (ConcreteCategory.comp_apply _ _ _).symm.trans
    ((ConcreteCategory.congr_hom key _).trans (ConcreteCategory.id_apply _))

end Trivialization

/-! ### Flat families from sections and from paths -/

section Main

variable {Z : TopCat.{0}} {F : TopCat.Sheaf (ModuleCat.{0} ℚ) Z}

/-- The germs of a global section of `f^* F` form a flat family along `f`. -/
private theorem exists_isFlat_of_section {A : TopCat.{0}} (f : A ⟶ Z)
    (s : ToType (((TopCat.Sheaf.forget _ A).obj
        ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj F)).obj (op ⊤))) :
    ∃ Y : ∀ a : A, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (f a)), IsFlat F f Y ∧
      ∀ a, (stalkToPullbackStalk f F a).hom (Y a) =
        ((TopCat.Sheaf.forget _ A).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj F)).germ
          ⊤ a trivial s := by
  have hb := fun a => bijective_stalkToPullbackStalk f F a
  refine ⟨fun a => (Equiv.ofBijective _ (hb a)).symm (((TopCat.Sheaf.forget _ A).obj
    ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj F)).germ ⊤ a trivial s), fun a₀ => ?_,
    fun a => (Equiv.ofBijective _ (hb a)).apply_symm_apply _⟩
  obtain ⟨W, r, N, hN, _hNU, hNW, hloc⟩ := exists_local_germ f F s a₀ trivial
  refine ⟨W, r, N, N.isOpen, hN, fun a ha => hNW ha, fun a ha => (hb a).1 ?_⟩
  exact ((Equiv.ofBijective _ (hb a)).apply_symm_apply _).trans (hloc a ha)

/-- The flat family along a path `γ` from `x` with a prescribed value in `F_x` at `0`. -/
private def flatOfPath (hF : IsLocalSystem F) {x y : Z} (γ : Path x y) :
    ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk x) →ₗ[ℚ]
      ∀ t : I, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (γ t)) :=
  (flatSub F γ).subtype ∘ₗ ((flatEquiv hF γ.continuous 0).symm.toLinearMap ∘ₗ
    (castStalk F γ.source.symm).toLinearMap)

private theorem isFlat_flatOfPath (hF : IsLocalSystem F) {x y : Z} (γ : Path x y)
    (v : ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk x)) :
    IsFlat F γ (flatOfPath hF γ v) :=
  ((flatEquiv hF γ.continuous 0).symm (castStalk F γ.source.symm v)).2

private theorem bijective_flatOfPath (hF : IsLocalSystem F) {x y : Z} (γ : Path x y) (t : I) :
    Function.Bijective fun v => flatOfPath hF γ v t :=
  (flatEquiv hF γ.continuous t).bijective.comp
    ((flatEquiv hF γ.continuous 0).symm.bijective.comp (castStalk F γ.source.symm).bijective)

/-- On a simply connected open `V`, transport depends only on the end points of a path in `V`. -/
private theorem pathTransport_map_subtype_eq (hF : IsLocalSystem F) {V : Opens Z}
    [SimplyConnectedSpace V] {a b : V} (γ γ' : Path a b) :
    pathTransport hF (γ.map continuous_subtype_val) =
      pathTransport hF (γ'.map continuous_subtype_val) :=
  pathTransport_eq_of_homotopic hF
    ((SimplyConnectedSpace.paths_homotopic γ γ').map ⟨Subtype.val, continuous_subtype_val⟩)

/-- **Transports from a base point are flat.** On a simply connected open `V` of a locally
path-connected space, transporting a germ at `x ∈ V` along paths in `V` gives a flat family
along the inclusion of `V`. -/
private theorem isFlat_transport_somePath [LocallyPathConnectedSpace Z] (hF : IsLocalSystem F)
    (V : Opens Z) [SimplyConnectedSpace V] {x : Z} (hx : x ∈ V)
    (v : ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk x)) :
    IsFlat F V.inclusion' fun y : V =>
      pathTransport hF
        ((PathConnectedSpace.somePath (⟨x, hx⟩ : V) y).map continuous_subtype_val) v := by
  haveI : LocallyPathConnectedSpace V := V.isOpen.locallyPathConnectedSpace
  intro (y₀ : V)
  obtain ⟨U, hy₀U, hU⟩ := exists_isGood hF y₀.1
  obtain ⟨Zf, hZf, hZfl⟩ := hU y₀.1 hy₀U
    (pathTransport hF ((PathConnectedSpace.somePath (⟨x, hx⟩ : V) y₀).map continuous_subtype_val) v)
  refine (IsFlatAt.comp (f := fun z => z) (Y := Zf) continuous_subtype_val (b₀ := y₀)
    (hZfl _ hy₀U)).congr ((U.isOpen.preimage continuous_subtype_val).pathComponentIn y₀)
    (mem_pathComponentIn_self hy₀U) fun y hy => ?_
  let q : Path y₀ y := (hy : JoinedIn _ y₀ y).somePath
  let q' : Path y₀.1 y.1 := q.map continuous_subtype_val
  have hflat : IsFlat F q' (fun t => Zf (q' t)) := fun t =>
    IsFlatAt.comp (f := fun z => z) (Y := Zf) q'.continuous
      (hZfl _ ((hy : JoinedIn _ y₀ y).somePath_mem t))
  change pathTransport hF _ v = Zf y.1
  rw [pathTransport_map_subtype_eq hF _ ((PathConnectedSpace.somePath _ y₀).trans q),
    Path.map_trans, pathTransport_trans, LinearEquiv.trans_apply, ← hZf,
    pathTransport_apply hF _ hflat (castStalk_dep F (fun z => z) Zf q'.source.symm).symm]
  exact castStalk_dep F (fun z => z) Zf q'.target

end Main

/-- The parallel transport `T_γ : 𝓛_x ≅ 𝓛_y` of a local system `𝓛` along a homotopy class `γ`
of paths from `x` to `y` rel endpoints: on a representative path, the value at `1` of the flat
family of germs along the path with the given value at `0`. It is well defined on homotopy
classes by homotopy invariance of the transport along paths. -/
@[no_expose] public def IsLocalSystem.parallelTransport {M : TopCat.{0}}
    {𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) M} (h𝓛 : IsLocalSystem 𝓛) {x y : M}
    (γ : Path.Homotopic.Quotient x y) :
    ((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x ≅ ((TopCat.Sheaf.forget _ M).obj 𝓛).stalk y :=
  Quotient.lift (s := Path.Homotopic.setoid x y)
    (fun γ : Path x y => (pathTransport h𝓛 γ).toModuleIso)
    (fun _ _ h => by rw [pathTransport_eq_of_homotopic h𝓛 h]) γ

private theorem IsLocalSystem.parallelTransport_mk_hom_apply {M : TopCat.{0}}
    {𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) M} (h𝓛 : IsLocalSystem 𝓛) {x y : M} (γ : Path x y)
    (v : ToType (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x)) :
    (h𝓛.parallelTransport (Path.Homotopic.Quotient.mk γ)).hom v = pathTransport h𝓛 γ v :=
  rfl

/-- The inverse image `γ⁻¹ 𝓛` of a local system along a path `γ` from `x` is constant, with
fibre the stalk `𝓛_x`. -/
public theorem IsLocalSystem.nonempty_pullback_path_iso_constantSheaf {M : TopCat.{0}}
    {𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) M} (h𝓛 : IsLocalSystem 𝓛) {x y : M} (γ : Path x y) :
    Nonempty ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (TopCat.ofHom (γ : C(unitInterval, M)) : TopCat.of unitInterval ⟶ M)).obj 𝓛 ≅
      (constantSheaf (Opens.grothendieckTopology (TopCat.of unitInterval))
        (ModuleCat.{0} ℚ)).obj (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x)) :=
  let ⟨φ, _⟩ := exists_iso_constantSheaf (F := 𝓛) (TopCat.ofHom (γ : C(I, M)))
    (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x) (flatOfPath h𝓛 γ)
    (isFlat_flatOfPath h𝓛 γ) (bijective_flatOfPath h𝓛 γ)
  ⟨φ⟩

/-- **End germs.** The parallel transport along `γ` carries the germ at `0` of a global section
of `γ⁻¹ 𝓛` to its germ at `1`. -/
public theorem IsLocalSystem.parallelTransport_germ {M : TopCat.{0}}
    {𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) M} (h𝓛 : IsLocalSystem 𝓛) {x y : M} (γ : Path x y)
    (s : ((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (TopCat.ofHom (γ : C(unitInterval, M)) : TopCat.of unitInterval ⟶ M)).obj 𝓛)).obj
          (op ⊤))
    (v : ((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x)
    (hv : stalkToPullbackStalk (TopCat.ofHom (γ : C(unitInterval, M))) 𝓛 (0 : unitInterval)
        (cast (by simp) v) =
      ((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (TopCat.ofHom (γ : C(unitInterval, M)))).obj 𝓛)).germ ⊤ (0 : unitInterval)
          (Opens.mem_top _) s) :
    stalkToPullbackStalk (TopCat.ofHom (γ : C(unitInterval, M))) 𝓛 (1 : unitInterval)
        (cast (by simp) ((h𝓛.parallelTransport (Path.Homotopic.Quotient.mk γ)).hom v)) =
      ((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (TopCat.ofHom (γ : C(unitInterval, M)))).obj 𝓛)).germ ⊤ (1 : unitInterval)
          (Opens.mem_top _) s := by
  obtain ⟨Y, hY, hYs⟩ := exists_isFlat_of_section (F := 𝓛) (TopCat.ofHom (γ : C(I, M))) s
  have hb := fun a => bijective_stalkToPullbackStalk (TopCat.ofHom (γ : C(I, M))) 𝓛 a
  have h0 : x = (TopCat.ofHom (γ : C(I, M))) 0 := γ.source.symm
  have h1 : y = (TopCat.ofHom (γ : C(I, M))) 1 := γ.target.symm
  rw [← castStalk_eq_cast 𝓛 h0] at hv
  rw [← castStalk_eq_cast 𝓛 h1, IsLocalSystem.parallelTransport_mk_hom_apply,
    pathTransport_apply h𝓛 γ hY ((hb 0).1 ((hYs 0).trans hv.symm)), castStalk_castStalk,
    castStalk_self]
  exact hYs 1

/-- **Concatenation.** `T_{γ δ} = T_δ ∘ T_γ`. -/
@[simp]
public theorem IsLocalSystem.parallelTransport_trans {M : TopCat.{0}}
    {𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) M} (h𝓛 : IsLocalSystem 𝓛) {x y z : M}
    (γ : Path.Homotopic.Quotient x y) (δ : Path.Homotopic.Quotient y z) :
    h𝓛.parallelTransport (γ.trans δ) = h𝓛.parallelTransport γ ≪≫ h𝓛.parallelTransport δ := by
  induction γ using Path.Homotopic.Quotient.ind with | mk γ => ?_
  induction δ using Path.Homotopic.Quotient.ind with | mk δ => ?_
  rw [← Path.Homotopic.Quotient.mk_trans]
  ext v
  change pathTransport h𝓛 (γ.trans δ) v = pathTransport h𝓛 δ (pathTransport h𝓛 γ v)
  rw [pathTransport_trans]
  rfl

/-- **Trivialisation over a simply connected open.** On a simply connected open `V` of a locally
path-connected space, `𝓛|_V` is isomorphic to the constant sheaf with fibre `𝓛_x`, `x ∈ V`, by
an isomorphism whose stalk at `y` is `T_γ⁻¹` for every path `γ` in `V` from `x` to `y`. -/
public theorem IsLocalSystem.exists_iso_constantSheaf_parallelTransport {M : TopCat.{0}}
    [LocallyPathConnectedSpace M] {𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) M}
    (h𝓛 : IsLocalSystem 𝓛) (V : Opens M) [SimplyConnectedSpace V] (x : M) (hx : x ∈ V) :
    ∃ φ : (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) V.inclusion').obj 𝓛 ≅
        (constantSheaf (Opens.grothendieckTopology (TopCat.of V)) (ModuleCat.{0} ℚ)).obj
          (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x),
      ∀ (y : V) (γ : Path (⟨x, hx⟩ : V) y) (v : ((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x),
        (TopCat.Presheaf.stalkFunctor _ y).map ((TopCat.Sheaf.forget _ _).map φ.hom)
            (stalkToPullbackStalk V.inclusion' 𝓛 y
              ((h𝓛.parallelTransport
                (Path.Homotopic.Quotient.mk (γ.map continuous_subtype_val))).hom v)) =
          ((TopCat.Sheaf.forget _ _).obj ((constantSheaf
              (Opens.grothendieckTopology (TopCat.of V)) (ModuleCat.{0} ℚ)).obj
                (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x))).germ ⊤ y (Opens.mem_top _)
            ((toSheafify (Opens.grothendieckTopology (TopCat.of V))
              ((Functor.const _).obj (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x))).app
                (op ⊤) v) := by
  let P : ∀ y : V, Path x y.1 := fun y =>
    (PathConnectedSpace.somePath ⟨x, hx⟩ y).map continuous_subtype_val
  obtain ⟨φ, hφ⟩ := exists_iso_constantSheaf V.inclusion'
    (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x)
    (LinearMap.pi fun y => (pathTransport h𝓛 (P y)).toLinearMap)
    (isFlat_transport_somePath h𝓛 V hx) fun y => (pathTransport h𝓛 (P y)).bijective
  refine ⟨φ, fun y γ v => ?_⟩
  rw [IsLocalSystem.parallelTransport_mk_hom_apply,
    pathTransport_map_subtype_eq h𝓛 γ (PathConnectedSpace.somePath ⟨x, hx⟩ y)]
  exact hφ y v

/-- Parallel transport in a local system of finite-dimensional `ℚ`-vector spaces on a locally
path-connected space `M`: the inverse image of `𝓛` along a path is constant; the isomorphisms
`T_γ = IsLocalSystem.parallelTransport h𝓛 γ : 𝓛_x ≅ 𝓛_y` on homotopy classes of paths are
characterised by the end germs of sections of `γ⁻¹ 𝓛`, compatible with concatenation, and
trivialise `𝓛` over every simply connected open subset. -/
@[mmp "lem_mmp_local_system_transport"]
public theorem IsLocalSystem.exists_parallelTransport {M : TopCat.{0}}
    [LocallyPathConnectedSpace M] {𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) M}
    (h𝓛 : IsLocalSystem 𝓛) :
      -- the inverse image along a path is constant, with fibre the stalk at the source
      (∀ {x y : M} (γ : Path x y),
        Nonempty ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
            (TopCat.ofHom (γ : C(unitInterval, M)) : TopCat.of unitInterval ⟶ M)).obj 𝓛 ≅
          (constantSheaf (Opens.grothendieckTopology (TopCat.of unitInterval))
            (ModuleCat.{0} ℚ)).obj (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x))) ∧
      -- `T_γ` carries the germ at `0` of a global section of `γ⁻¹ 𝓛` to its germ at `1`
      (∀ {x y : M} (γ : Path x y)
        (s : ((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
            (TopCat.ofHom (γ : C(unitInterval, M)) : TopCat.of unitInterval ⟶ M)).obj 𝓛)).obj
              (op ⊤))
        (v : ((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x),
        stalkToPullbackStalk (TopCat.ofHom (γ : C(unitInterval, M))) 𝓛 (0 : unitInterval)
            (cast (by simp) v) =
          ((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
            (TopCat.ofHom (γ : C(unitInterval, M)))).obj 𝓛)).germ ⊤ (0 : unitInterval)
              (Opens.mem_top _) s →
        stalkToPullbackStalk (TopCat.ofHom (γ : C(unitInterval, M))) 𝓛 (1 : unitInterval)
            (cast (by simp) ((h𝓛.parallelTransport (Path.Homotopic.Quotient.mk γ)).hom v)) =
          ((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
            (TopCat.ofHom (γ : C(unitInterval, M)))).obj 𝓛)).germ ⊤ (1 : unitInterval)
              (Opens.mem_top _) s) ∧
      -- `T_{γ δ} = T_δ ∘ T_γ`
      (∀ {x y z : M} (γ : Path.Homotopic.Quotient x y) (δ : Path.Homotopic.Quotient y z),
        h𝓛.parallelTransport (γ.trans δ) =
          h𝓛.parallelTransport γ ≪≫ h𝓛.parallelTransport δ) ∧
      -- trivialisation over a simply connected open subset, with stalks `T_γ⁻¹`
      (∀ (V : Opens M) [SimplyConnectedSpace V] (x : M) (hx : x ∈ V),
        ∃ φ : (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) V.inclusion').obj 𝓛 ≅
            (constantSheaf (Opens.grothendieckTopology (TopCat.of V)) (ModuleCat.{0} ℚ)).obj
              (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x),
          ∀ (y : V) (γ : Path (⟨x, hx⟩ : V) y) (v : ((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x),
            (TopCat.Presheaf.stalkFunctor _ y).map ((TopCat.Sheaf.forget _ _).map φ.hom)
                (stalkToPullbackStalk V.inclusion' 𝓛 y
                  ((h𝓛.parallelTransport
                    (Path.Homotopic.Quotient.mk (γ.map continuous_subtype_val))).hom v)) =
              ((TopCat.Sheaf.forget _ _).obj ((constantSheaf
                  (Opens.grothendieckTopology (TopCat.of V)) (ModuleCat.{0} ℚ)).obj
                    (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x))).germ ⊤ y (Opens.mem_top _)
                ((toSheafify (Opens.grothendieckTopology (TopCat.of V))
                  ((Functor.const _).obj (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x))).app
                    (op ⊤) v)) :=
  ⟨h𝓛.nonempty_pullback_path_iso_constantSheaf, h𝓛.parallelTransport_germ,
    h𝓛.parallelTransport_trans, h𝓛.exists_iso_constantSheaf_parallelTransport⟩

end ParallelTransport

section GoodCover

open Topology ZeroObject

attribute [local instance] HasDerivedCategory.standard

/-! ### Restriction and extension by zero -/

section Open

variable {X : TopCat.{0}}

/-- The stalk functor at `y` on sheaves of `ℚ`-vector spaces. -/
private abbrev st {Y : TopCat.{0}} (y : Y) :
    TopCat.Sheaf (ModuleCat.{0} ℚ) Y ⥤ ModuleCat.{0} ℚ :=
  TopCat.Sheaf.forget _ Y ⋙ TopCat.Presheaf.stalkFunctor _ y

/-- Restriction `j^*` to an open subset. -/
private abbrev resF (U : Opens X) :
    TopCat.Sheaf (ModuleCat.{0} ℚ) X ⥤ TopCat.Sheaf (ModuleCat.{0} ℚ) ((Opens.toTopCat X).obj U) :=
  haveI := U.isOpenEmbedding.functor_isContinuous
  U.isOpenEmbedding.functor.sheafPushforwardContinuous _ _ _

/-- Extension by zero `j_!`. -/
private abbrev extF (U : Opens X) :
    TopCat.Sheaf (ModuleCat.{0} ℚ) ((Opens.toTopCat X).obj U) ⥤ TopCat.Sheaf (ModuleCat.{0} ℚ) X :=
  haveI := U.isOpenEmbedding.functor_isContinuous
  U.isOpenEmbedding.functor.sheafPullback _ _ _

/-- The adjunction `j_! ⊣ j^*`. -/
private abbrev adjF (U : Opens X) : extF U ⊣ resF U :=
  haveI := U.isOpenEmbedding.functor_isContinuous
  U.isOpenEmbedding.functor.sheafAdjunctionContinuous _ _ _

/-- Compactly supported cohomology as a functor. -/
private abbrev HcF (Y : TopCat.{0}) (q : ℤ) :
    TopCat.Sheaf (ModuleCat.{0} ℚ) Y ⥤ ModuleCat.{0} ℚ :=
  DerivedCategory.Plus.singleFunctor _ 0 ⋙
    (compactSupportSectionsFunctor ℚ (X := Y)).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor _ q

/-- `F_U = j_{U!} j_U^* F`. -/
private abbrev LU (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X) (U : Opens X) :
    TopCat.Sheaf (ModuleCat.{0} ℚ) X :=
  (extF U).obj ((resF U).obj F)

/-- The counit `F_U ⟶ F`. -/
private abbrev cU (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X) (U : Opens X) :
    LU F U ⟶ F :=
  (adjF U).counit.app F

/-- The stalk of `j^* A` at `x ∈ U` is the stalk of `A` at `x`, naturally in `A`. -/
private lemma stalk_resF_naturality {U : Opens X} {A B : TopCat.Sheaf (ModuleCat.{0} ℚ) X}
    (f : A ⟶ B) (x : (Opens.toTopCat X).obj U) :
    (st x).map ((resF U).map f) ≫
        (AlgebraicGeometry.PresheafedSpace.restrictStalkIso ⟨X, B.presheaf⟩
          U.isOpenEmbedding x).hom =
      (AlgebraicGeometry.PresheafedSpace.restrictStalkIso ⟨X, A.presheaf⟩
          U.isOpenEmbedding x).hom ≫ (st x.1).map f := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun V hV => ?_
  ext s
  have e1 := AlgebraicGeometry.PresheafedSpace.restrictStalkIso_hom_eq_germ_apply ⟨X, A.presheaf⟩
    U.isOpenEmbedding V x hV s
  have e2 := AlgebraicGeometry.PresheafedSpace.restrictStalkIso_hom_eq_germ_apply ⟨X, B.presheaf⟩
    U.isOpenEmbedding V x hV (((TopCat.Sheaf.forget _ X).map f).app _ s)
  have e3 := TopCat.Presheaf.stalkFunctor_map_germ_apply V x hV ((TopCat.Sheaf.forget _ _).map
    ((resF U).map f)) s
  have e4 := TopCat.Presheaf.stalkFunctor_map_germ_apply
    (U.isOpenEmbedding.functor.obj V) x.1 ⟨x, hV, rfl⟩ ((TopCat.Sheaf.forget _ X).map f) s
  exact (congrArg (AlgebraicGeometry.PresheafedSpace.restrictStalkIso ⟨X, B.presheaf⟩
    U.isOpenEmbedding x).hom e3).trans (e2.trans (e4.symm.trans (congrArg
      ((TopCat.Presheaf.stalkFunctor _ x.1).map ((TopCat.Sheaf.forget _ X).map f)) e1.symm)))

/-- The facts about extension by zero from `MMP.Fourfold.compactSupportCohomology_extendByZero`
used below. -/
private structure ExtHyp {X : TopCat.{0}} (U : Opens X) : Prop where
  unit : ∀ G, IsIso ((adjF U).unit.app G)
  zero : ∀ G, ∀ x ∉ U, IsZero (((extF U).obj G).presheaf.stalk x)
  exact : PreservesFiniteLimits (extF U) ∧ PreservesFiniteColimits (extF U)

private lemma extHyp [LocallyCompactSpace X] [T2Space X] (U : Opens X) : ExtHyp U := by
  obtain ⟨h, -⟩ := compactSupportCohomology_extendByZero ℚ X
  obtain ⟨hex, hu, -, hz, -, -⟩ := h U
  exact ⟨hu, hz, hex⟩

/-- `j^*` of the counit is invertible. -/
private lemma isIso_resF_counit {U : Opens X} (h : ExtHyp U)
    (G : TopCat.Sheaf (ModuleCat.{0} ℚ) X) :
    IsIso ((resF U).map ((adjF U).counit.app G)) := by
  haveI := h.unit ((resF U).obj G)
  haveI : IsIso ((adjF U).unit.app ((resF U).obj G) ≫ (resF U).map ((adjF U).counit.app G)) := by
    rw [(adjF U).right_triangle_components G]; exact IsIso.id _
  exact IsIso.of_isIso_comp_left ((adjF U).unit.app ((resF U).obj G)) _

private lemma isIso_stalk_counit {U : Opens X} (h : ExtHyp U) (G : TopCat.Sheaf (ModuleCat.{0} ℚ) X)
    (x : (Opens.toTopCat X).obj U) : IsIso ((st x.1).map ((adjF U).counit.app G)) := by
  haveI := isIso_resF_counit h G
  rw [← (Iso.inv_comp_eq _).mpr (stalk_resF_naturality ((adjF U).counit.app G) x)]
  exact IsIso.comp_isIso' (Iso.isIso_inv _) (IsIso.comp_isIso' inferInstance (Iso.isIso_hom _))

/-- The counit `j_! j^* G ⟶ G` is a monomorphism. -/
private lemma mono_counit {U : Opens X} (h : ExtHyp U) (G : TopCat.Sheaf (ModuleCat.{0} ℚ) X) :
    Mono ((adjF U).counit.app G) := by
  have hS : (ShortComplex.mk (0 : 0 ⟶ (extF U).obj ((resF U).obj G)) ((adjF U).counit.app G)
      zero_comp).Exact := by
    rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
    intro x
    rw [ShortComplex.exact_iff_mono _ (((st x).map_isZero (isZero_zero _)).eq_of_src _ _)]
    by_cases hx : x ∈ U
    · exact @IsIso.mono_of_iso _ _ _ _ _ (isIso_stalk_counit h G ⟨x, hx⟩)
    · exact mono_of_source_iso_zero _ (h.zero _ x hx).isoZero
  exact (ShortComplex.exact_iff_mono _ rfl).mp hS

private lemma functor_obj_map_obj_of_le {W V : Opens X} (h : V ≤ W) :
    W.isOpenEmbedding.functor.obj ((Opens.map W.inclusion').obj V) = V := by
  rw [Opens.functor_map_eq_inf]
  exact inf_eq_left.mpr h

/-- A morphism of sheaves is invertible on every open contained in `U`. -/
private def IsoBelow {F G : TopCat.Sheaf (ModuleCat.{0} ℚ) X} (f : F ⟶ G) (U : Opens X) : Prop :=
  ∀ V : Opens X, V ≤ U → IsIso (f.hom.app (op V))

private lemma isIso_resF_iff {F G : TopCat.Sheaf (ModuleCat.{0} ℚ) X} (f : F ⟶ G) (U : Opens X) :
    IsIso ((resF U).map f) ↔ IsoBelow f U := by
  constructor
  · intro h V hV
    have h1 : IsIso ((resF U).map f).hom :=
      Iso.isIso_hom ((sheafToPresheaf _ _).mapIso (@asIso _ _ _ _ ((resF U).map f) h))
    have h2 := NatIso.isIso_app_of_isIso ((resF U).map f).hom
      (op ((Opens.map U.inclusion').obj V))
    rw [← functor_obj_map_obj_of_le hV]
    exact h2
  · intro h
    haveI : IsIso ((resF U).map f).hom := by
      haveI : ∀ V, IsIso (((resF U).map f).hom.app V) := fun V =>
        h _ (fun _ ⟨y, _, hy⟩ => hy ▸ y.2)
      exact NatIso.isIso_of_isIso_app _
    haveI : IsIso ((sheafToPresheaf _ _).map ((resF U).map f)) := this
    exact (fullyFaithfulSheafToPresheaf _ _).isIso_of_isIso_map _

private lemma isIso_of_isoBelow_top {F G : TopCat.Sheaf (ModuleCat.{0} ℚ) X} (f : F ⟶ G)
    (h : IsoBelow f ⊤) : IsIso f := by
  haveI : IsIso f.hom := by
    haveI : ∀ V, IsIso (f.hom.app V) := fun V => h V.unop le_top
    exact NatIso.isIso_of_isIso_app _
  haveI : IsIso ((sheafToPresheaf _ _).map f) := this
  exact (fullyFaithfulSheafToPresheaf _ _).isIso_of_isIso_map _

/-- Restriction to `W` and then to an open `A'` of `W` is invertible exactly when the morphism is
invertible on every open below the image of `A'`. -/
private lemma isIso_resF_resF_iff {F G : TopCat.Sheaf (ModuleCat.{0} ℚ) X} (f : F ⟶ G)
    (W : Opens X) (A' : Opens ((Opens.toTopCat X).obj W)) :
    IsIso ((resF A').map ((resF W).map f)) ↔ IsoBelow f (W.isOpenEmbedding.functor.obj A') := by
  rw [isIso_resF_iff]
  constructor
  · intro h V hV
    have hVW : V ≤ W := hV.trans (fun _ ⟨y, _, hy⟩ => hy ▸ y.2)
    have hle : (Opens.map W.inclusion').obj V ≤ A' := by
      intro y hy
      obtain ⟨z, hz, hzy⟩ := hV hy
      exact Subtype.ext hzy ▸ hz
    have h2 := h _ hle
    rw [← functor_obj_map_obj_of_le hVW]
    exact h2
  · intro h V hV
    exact h _ (W.isOpenEmbedding.functor.map (homOfLE hV)).le

private lemma isoBelow_cU {A : Opens X} (hA : ExtHyp A) (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X) :
    IsoBelow (cU F A) A :=
  (isIso_resF_iff _ _).mp (isIso_resF_counit hA F)

variable (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X) (W : Opens X)
  (A' : Opens ((Opens.toTopCat X).obj W))

/-- `j_{W!} j_{A'!} (F|_W)|_{A'}` for an open `A'` of `W`. -/
private abbrev K1 : TopCat.Sheaf (ModuleCat.{0} ℚ) X :=
  (extF W).obj (LU ((resF W).obj F) A')

/-- The composite of the counits `j_{W!} j_{A'!} (F|_W)|_{A'} ⟶ j_{W!} F|_W ⟶ F`. -/
private abbrev c1 : K1 F W A' ⟶ F :=
  (extF W).map (cU ((resF W).obj F) A') ≫ cU F W

variable {F W A'}

private lemma isoBelow_c1 (hW : ExtHyp W) (hA' : ExtHyp A') :
    IsoBelow (c1 F W A') (W.isOpenEmbedding.functor.obj A') := by
  rw [← isIso_resF_resF_iff]
  set G := (resF W).obj F
  set x := cU G A'
  haveI := hW.unit (LU G A')
  haveI := hW.unit G
  have e : (resF W).map ((extF W).map x) =
      inv ((adjF W).unit.app (LU G A')) ≫ x ≫ (adjF W).unit.app G := by
    rw [IsIso.eq_inv_comp]
    simpa using ((adjF W).unit.naturality x).symm
  haveI := isIso_resF_counit hA' G
  haveI := isIso_resF_counit hW F
  rw [Functor.map_comp, Functor.map_comp, e, Functor.map_comp, Functor.map_comp]
  infer_instance

private lemma mono_c1 (hW : ExtHyp W) (hA' : ExtHyp A') : Mono (c1 F W A') := by
  haveI := mono_counit hA' ((resF W).obj F)
  haveI := mono_counit hW F
  haveI : PreservesFiniteLimits (extF W) := hW.exact.1
  infer_instance

/-- **Extension by zero in stages.** For an open `A'` of `W` with image `A`,
`j_{W!} j_{A'!} (F|_{A'}) ≅ j_{A!}(F|_A)` over `F`. -/
private lemma exists_iso_LU {A : Opens X} (hW : ExtHyp W) (hA' : ExtHyp A') (hA : ExtHyp A)
    (hAA : W.isOpenEmbedding.functor.obj A' = A) :
    ∃ ψ : K1 F W A' ≅ LU F A, ψ.hom ≫ cU F A = c1 F W A' := by
  have h1 : IsIso ((resF A).map (c1 F W A')) := by
    rw [isIso_resF_iff, ← hAA]; exact isoBelow_c1 hW hA'
  have h2 : IsIso ((resF A').map ((resF W).map (cU F A))) := by
    rw [isIso_resF_resF_iff, hAA]; exact isoBelow_cU hA F
  let φ : LU F A ⟶ K1 F W A' := ((adjF A).homEquiv _ _).symm (inv ((resF A).map (c1 F W A')))
  let ψ : K1 F W A' ⟶ LU F A := ((adjF W).homEquiv _ _).symm (((adjF A').homEquiv _ _).symm
    (inv ((resF A').map ((resF W).map (cU F A)))))
  have hφ : φ ≫ c1 F W A' = cU F A := by
    simp only [φ]
    rw [← Adjunction.homEquiv_naturality_right_symm, IsIso.inv_hom_id,
      Adjunction.homEquiv_counit, CategoryTheory.Functor.map_id, Category.id_comp]
  have hψ : ψ ≫ cU F A = c1 F W A' := by
    simp only [ψ]
    rw [← Adjunction.homEquiv_naturality_right_symm, ← Adjunction.homEquiv_naturality_right_symm,
      IsIso.inv_hom_id, Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
      CategoryTheory.Functor.map_id, Category.id_comp]
  haveI := mono_c1 (F := F) hW hA'
  haveI := mono_counit hA F
  refine ⟨⟨ψ, φ, ?_, ?_⟩, hψ⟩
  · exact (cancel_mono (c1 F W A')).mp (by simp [hφ, hψ])
  · exact (cancel_mono (cU F A)).mp (by simp [hφ, hψ])

end Open

/-! ### Elements of `ℚ`-modules -/

private lemma hom_comp_apply {A B C : ModuleCat.{0} ℚ} (f : A ⟶ B) (g : B ⟶ C) (x : A) :
    g.hom (f.hom x) = (f ≫ g).hom x := rfl

section Biprod

variable {M N P : ModuleCat.{0} ℚ}

private lemma biprod_fst_lift_apply (f : P ⟶ M) (g : P ⟶ N) (x : P) :
    (biprod.fst : M ⊞ N ⟶ M).hom ((biprod.lift f g).hom x) = f.hom x := by
  rw [hom_comp_apply, biprod.lift_fst]

private lemma biprod_snd_lift_apply (f : P ⟶ M) (g : P ⟶ N) (x : P) :
    (biprod.snd : M ⊞ N ⟶ N).hom ((biprod.lift f g).hom x) = g.hom x := by
  rw [hom_comp_apply, biprod.lift_snd]

private lemma biprod_fst_inl_add (a : M) (b : N) :
    (biprod.fst : M ⊞ N ⟶ M).hom ((biprod.inl : M ⟶ M ⊞ N).hom a +
      (biprod.inr : N ⟶ M ⊞ N).hom b) = a := by
  rw [map_add, hom_comp_apply, hom_comp_apply, biprod.inl_fst, biprod.inr_fst]
  simp

private lemma biprod_snd_inl_add (a : M) (b : N) :
    (biprod.snd : M ⊞ N ⟶ N).hom ((biprod.inl : M ⟶ M ⊞ N).hom a +
      (biprod.inr : N ⟶ M ⊞ N).hom b) = b := by
  rw [map_add, hom_comp_apply, hom_comp_apply, biprod.inl_snd, biprod.inr_snd]
  simp

private lemma biprod_desc_apply (f : M ⟶ P) (g : N ⟶ P) (u : ↑(M ⊞ N)) :
    (biprod.desc f g).hom u = f.hom ((biprod.fst : M ⊞ N ⟶ M).hom u) +
      g.hom ((biprod.snd : M ⊞ N ⟶ N).hom u) := by
  rw [biprod.desc_eq, ModuleCat.hom_add, LinearMap.add_apply, hom_comp_apply, hom_comp_apply]

end Biprod

/-! ### The morphisms `F_V ⟶ F_U` over `F` -/

section Mor

private lemma t2Space_toTopCat {X : TopCat.{0}} [T2Space X] (W : Opens X) :
    T2Space ((Opens.toTopCat X).obj W) :=
  inferInstanceAs (T2Space W)

private lemma locallyCompactSpace_toTopCat {X : TopCat.{0}} [LocallyCompactSpace X] (W : Opens X) :
    LocallyCompactSpace ((Opens.toTopCat X).obj W) :=
  W.isOpen.locallyCompactSpace

attribute [local instance] t2Space_toTopCat locallyCompactSpace_toTopCat

variable {X : TopCat.{0}} [LocallyCompactSpace X] [T2Space X]
  (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X)

/-- The morphism `F_V ⟶ F_U` over `F`, for opens `V ≤ U`. -/
private def morL {V U : Opens X} (h : V ≤ U) : LU F V ⟶ LU F U :=
  ((compactSupportCohomology_extendByZero ℚ X).2.1 F V U h).exists.choose

private lemma morL_spec {V U : Opens X} (h : V ≤ U) : morL F h ≫ cU F U = cU F V :=
  ((compactSupportCohomology_extendByZero ℚ X).2.1 F V U h).exists.choose_spec

private lemma morL_eq {V U : Opens X} (h : V ≤ U) {m : LU F V ⟶ LU F U}
    (hm : m ≫ cU F U = cU F V) : m = morL F h := by
  haveI := mono_counit (extHyp U) F
  exact (cancel_mono (cU F U)).mp (hm.trans (morL_spec F h).symm)

private lemma morL_comp {V W U : Opens X} (h₁ : V ≤ W) (h₂ : W ≤ U) :
    morL F h₁ ≫ morL F h₂ = morL F (h₁.trans h₂) :=
  morL_eq F _ (by rw [Category.assoc, morL_spec, morL_spec])

/-- `E^q(V) = H^q_c(X, F_V)`. -/
private abbrev EH (q : ℤ) (V : Opens X) : ModuleCat.{0} ℚ :=
  (HcF X q).obj (LU F V)

/-- The extension map `E^q(V) ⟶ E^q(U)`. -/
private def morE (q : ℤ) {V U : Opens X} (h : V ≤ U) : EH F q V →ₗ[ℚ] EH F q U :=
  ((HcF X q).map (morL F h)).hom

private lemma morE_comp (q : ℤ) {V W U : Opens X} (h₁ : V ≤ W) (h₂ : W ≤ U) (v : EH F q V) :
    morE F q h₂ (morE F q h₁ v) = morE F q (h₁.trans h₂) v := by
  simp only [morE, ← morL_comp F h₁ h₂, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

variable {F}

private lemma extF_morL_comp {W : Opens X} {A' C' : Opens ((Opens.toTopCat X).obj W)}
    {A C : Opens X} (hA : ExtHyp A)
    (h' : C' ≤ A') (h : C ≤ A) (ψA : K1 F W A' ≅ LU F A) (hψA : ψA.hom ≫ cU F A = c1 F W A')
    (ψC : K1 F W C' ≅ LU F C) (hψC : ψC.hom ≫ cU F C = c1 F W C') :
    (extF W).map (morL ((resF W).obj F) h') ≫ ψA.hom = ψC.hom ≫ morL F h := by
  haveI := mono_counit hA F
  refine (cancel_mono (cU F A)).mp ?_
  rw [Category.assoc, hψA, Category.assoc, morL_spec, hψC, c1, c1, ← Category.assoc,
    ← Functor.map_comp, morL_spec]

private lemma extF_cU_eq {W A : Opens X} {A' : Opens ((Opens.toTopCat X).obj W)} (hAW : A ≤ W)
    (ψA : K1 F W A' ≅ LU F A) (hψA : ψA.hom ≫ cU F A = c1 F W A') :
    (extF W).map (cU ((resF W).obj F) A') = ψA.hom ≫ morL F hAW := by
  haveI := mono_counit (extHyp W) F
  refine (cancel_mono (cU F W)).mp ?_
  rw [Category.assoc, morL_spec, hψA]

end Mor

/-! ### Mayer–Vietoris on `S` -/

section MV

attribute [local instance] t2Space_toTopCat locallyCompactSpace_toTopCat

variable {X : TopCat.{0}} [LocallyCompactSpace X] [T2Space X]
  (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X)

/-- The comparison isomorphisms of `MMP.Fourfold.compactSupportCohomology_extendByZero`, in this
file's notation. -/
private lemma exists_comparison (Y : TopCat.{0}) [LocallyCompactSpace Y] [T2Space Y] :
    Nonempty (∀ (U : Opens Y) (q : ℤ),
      HcF ((Opens.toTopCat Y).obj U) q ≅ extF U ⋙ HcF Y q) := by
  obtain ⟨-, -, ι, -⟩ := compactSupportCohomology_extendByZero ℚ Y
  exact ⟨ι⟩

/-- `MMP.Fourfold.compactSupportCohomology_mayerVietoris_exact`, in this file's notation: the
comparison isomorphisms and extension maps it provides, with exactness at the middle terms. -/
private lemma exists_mayerVietoris_exact (Y : TopCat.{0}) [LocallyCompactSpace Y] [T2Space Y]
    (U V : Opens Y) (hUV : U ⊔ V = ⊤) :
    ∃ (ι : ∀ (W : Opens Y) (q : ℤ), HcF ((Opens.toTopCat Y).obj W) q ≅ extF W ⋙ HcF Y q)
      (e : ∀ (q : ℤ) {W' W : Opens Y}, W' ≤ W →
        (resF W' ⋙ HcF ((Opens.toTopCat Y).obj W') q ⟶ resF W ⋙ HcF ((Opens.toTopCat Y).obj W) q)),
      (∀ (q : ℤ) (W' W : Opens Y) (h : W' ≤ W) (G : TopCat.Sheaf (ModuleCat.{0} ℚ) Y)
        (m : LU G W' ⟶ LU G W), m ≫ cU G W = cU G W' →
          (e q h).app G = (ι W' q).hom.app _ ≫ (HcF Y q).map m ≫ (ι W q).inv.app _) ∧
      ∀ (q : ℤ) (G : TopCat.Sheaf (ModuleCat.{0} ℚ) Y),
        Function.Exact (biprod.lift ((e q (inf_le_left : U ⊓ V ≤ U)).app G)
            (-(e q (inf_le_right : U ⊓ V ≤ V)).app G)).hom
          (biprod.desc ((ι U q).hom.app ((resF U).obj G) ≫ (HcF Y q).map (cU G U))
            ((ι V q).hom.app ((resF V).obj G) ≫ (HcF Y q).map (cU G V))).hom ∧
        ∃ δ : (HcF Y q).obj G ⟶
          (HcF ((Opens.toTopCat Y).obj (U ⊓ V)) (q + 1)).obj ((resF (U ⊓ V)).obj G), Function.Exact
          (biprod.desc ((ι U q).hom.app ((resF U).obj G) ≫ (HcF Y q).map (cU G U))
            ((ι V q).hom.app ((resF V).obj G) ≫ (HcF Y q).map (cU G V))).hom δ.hom := by
  obtain ⟨ι, e, δ, -, -, he, hδ⟩ := compactSupportCohomology_mayerVietoris_exact ℚ Y U V hUV
  exact ⟨ι, e, he, fun q G => ⟨(hδ q G).1, (δ q).app G, (hδ q G).2.1⟩⟩

section Transport

variable {F} {W : Opens X}

/-- `H^q_c(A', F|_{A'}) ≅ E^q(A)` for an open `A'` of `W` with image `A`. -/
private def compIso {A' : Opens ((Opens.toTopCat X).obj W)} {A : Opens X}
    (ιY : ∀ (U : Opens ((Opens.toTopCat X).obj W)) (q : ℤ),
      HcF ((Opens.toTopCat ((Opens.toTopCat X).obj W)).obj U) q ≅
        extF U ⋙ HcF ((Opens.toTopCat X).obj W) q)
    (ιX : ∀ (U : Opens X) (q : ℤ), HcF ((Opens.toTopCat X).obj U) q ≅ extF U ⋙ HcF X q)
    (ψ : K1 F W A' ≅ LU F A) (q : ℤ) :
    (HcF ((Opens.toTopCat ((Opens.toTopCat X).obj W)).obj A') q).obj
      ((resF A').obj ((resF W).obj F)) ≅ EH F q A :=
  (ιY A' q).app _ ≪≫ (ιX W q).app (LU ((resF W).obj F) A') ≪≫ (HcF X q).mapIso ψ

/-- `compIso` carries the extension maps inside `W` to the extension maps `morE` on `X`. -/
private lemma compIso_morL {A' C' : Opens ((Opens.toTopCat X).obj W)} {A C : Opens X}
    (ιY : ∀ (U : Opens ((Opens.toTopCat X).obj W)) (q : ℤ),
      HcF ((Opens.toTopCat ((Opens.toTopCat X).obj W)).obj U) q ≅
        extF U ⋙ HcF ((Opens.toTopCat X).obj W) q)
    (ιX : ∀ (U : Opens X) (q : ℤ), HcF ((Opens.toTopCat X).obj U) q ≅ extF U ⋙ HcF X q)
    (hA : ExtHyp A) (h' : C' ≤ A') (h : C ≤ A) {ψA : K1 F W A' ≅ LU F A}
    (hψA : ψA.hom ≫ cU F A = c1 F W A')
    {ψC : K1 F W C' ≅ LU F C} (hψC : ψC.hom ≫ cU F C = c1 F W C') (q : ℤ) (z) :
    (compIso ιY ιX ψA q).hom.hom (((ιY C' q).hom.app _ ≫
      (HcF ((Opens.toTopCat X).obj W) q).map (morL ((resF W).obj F) h') ≫
        (ιY A' q).inv.app _).hom z) = morE F q h ((compIso ιY ιX ψC q).hom.hom z) := by
  have key : ((ιY C' q).hom.app _ ≫
      (HcF ((Opens.toTopCat X).obj W) q).map (morL ((resF W).obj F) h') ≫
        (ιY A' q).inv.app _) ≫ (compIso ιY ιX ψA q).hom =
      (compIso ιY ιX ψC q).hom ≫ (HcF X q).map (morL F h) := by
    simp only [compIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc,
      Iso.inv_hom_id_app_assoc]
    rw [(ιX W q).hom.naturality_assoc, Functor.comp_map, ← Functor.map_comp, ← Functor.map_comp,
      extF_morL_comp hA h' h ψA hψA ψC hψC]
  rw [hom_comp_apply, key]; rfl

/-- `compIso` carries the counit inside `W` to the extension map `E^q(A) → E^q(W)`. -/
private lemma compIso_cU {A' : Opens ((Opens.toTopCat X).obj W)} {A : Opens X}
    (ιY : ∀ (U : Opens ((Opens.toTopCat X).obj W)) (q : ℤ),
      HcF ((Opens.toTopCat ((Opens.toTopCat X).obj W)).obj U) q ≅
        extF U ⋙ HcF ((Opens.toTopCat X).obj W) q)
    (ιX : ∀ (U : Opens X) (q : ℤ), HcF ((Opens.toTopCat X).obj U) q ≅ extF U ⋙ HcF X q)
    (hAW : A ≤ W) {ψA : K1 F W A' ≅ LU F A} (hψA : ψA.hom ≫ cU F A = c1 F W A') (q : ℤ) (z) :
    ((ιX W q).hom.app ((resF W).obj F)).hom (((ιY A' q).hom.app _ ≫
      (HcF ((Opens.toTopCat X).obj W) q).map (cU ((resF W).obj F) A')).hom z) =
      morE F q hAW ((compIso ιY ιX ψA q).hom.hom z) := by
  have key : ((ιY A' q).hom.app _ ≫
      (HcF ((Opens.toTopCat X).obj W) q).map (cU ((resF W).obj F) A')) ≫
        (ιX W q).hom.app ((resF W).obj F) =
      (compIso ιY ιX ψA q).hom ≫ (HcF X q).map (morL F hAW) := by
    simp only [compIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
    rw [(ιX W q).hom.naturality, Functor.comp_map, ← Functor.map_comp, extF_cU_eq hAW ψA hψA]
  rw [hom_comp_apply, key]; rfl

end Transport

/-- **Mayer–Vietoris for `W = A ∪ B`, in terms of `E^q(-) = H^q_c(X, F_-)`.** The sequence
`E^q(A ∩ B) → E^q(A) ⊕ E^q(B) → E^q(W)` is exact, and the second map is onto when
`E^{q+1}(A ∩ B) = 0`. -/
private lemma mv_transfer (W A B : Opens X) (hAB : A ⊔ B = W) (q : ℤ) :
    (∀ (a : EH F q A) (b : EH F q B),
      morE F q (hAB ▸ le_sup_left : A ≤ W) a + morE F q (hAB ▸ le_sup_right : B ≤ W) b = 0 →
        ∃ z : EH F q (A ⊓ B), morE F q inf_le_left z = a ∧ -(morE F q inf_le_right z) = b) ∧
    (IsZero (EH F (q + 1) (A ⊓ B)) → ∀ w : EH F q W, ∃ (a : EH F q A) (b : EH F q B),
      morE F q (hAB ▸ le_sup_left : A ≤ W) a + morE F q (hAB ▸ le_sup_right : B ≤ W) b = w) := by
  have hAW : A ≤ W := hAB ▸ le_sup_left
  have hBW : B ≤ W := hAB ▸ le_sup_right
  let A' : Opens ((Opens.toTopCat X).obj W) := (Opens.map W.inclusion').obj A
  let B' : Opens ((Opens.toTopCat X).obj W) := (Opens.map W.inclusion').obj B
  have hA'B' : A' ⊔ B' = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    have hy : y.1 ∈ A ⊔ B := hAB ▸ y.2
    exact Opens.mem_sup.mpr (Opens.mem_sup.mp hy)
  obtain ⟨ιY, eY, heY, hmv⟩ := exists_mayerVietoris_exact _ A' B' hA'B'
  obtain ⟨ιX⟩ := exists_comparison X
  obtain ⟨ψA, hψA⟩ := exists_iso_LU (F := F) (extHyp W) (extHyp A') (extHyp A)
    (functor_obj_map_obj_of_le hAW)
  obtain ⟨ψB, hψB⟩ := exists_iso_LU (F := F) (extHyp W) (extHyp B') (extHyp B)
    (functor_obj_map_obj_of_le hBW)
  obtain ⟨ψC, hψC⟩ := exists_iso_LU (F := F) (extHyp W) (extHyp (A' ⊓ B')) (extHyp (A ⊓ B))
    (functor_obj_map_obj_of_le (inf_le_left.trans hAW))
  obtain ⟨ex1, δ, ex2⟩ := hmv q ((resF W).obj F)
  let MA := (HcF ((Opens.toTopCat ((Opens.toTopCat X).obj W)).obj A') q).obj
    ((resF A').obj ((resF W).obj F))
  let MB := (HcF ((Opens.toTopCat ((Opens.toTopCat X).obj W)).obj B') q).obj
    ((resF B').obj ((resF W).obj F))
  refine ⟨fun a b hab => ?_, fun hz w => ?_⟩
  · obtain ⟨z', hz'⟩ := (ex1 ((biprod.inl : MA ⟶ MA ⊞ MB).hom ((compIso ιY ιX ψA q).inv.hom a) +
      (biprod.inr : MB ⟶ MA ⊞ MB).hom ((compIso ιY ιX ψB q).inv.hom b))).mp (by
        apply ((ιX W q).app ((resF W).obj F)).toLinearEquiv.injective
        change ((ιX W q).hom.app _).hom _ = ((ιX W q).hom.app _).hom 0
        rw [biprod_desc_apply, biprod_fst_inl_add, biprod_snd_inl_add, map_add, map_zero,
          compIso_cU ιY ιX hAW hψA, compIso_cU ιY ιX hBW hψB, Iso.inv_hom_id_apply,
          Iso.inv_hom_id_apply]
        exact hab)
    have h1 := (biprod_fst_lift_apply _ _ z').symm.trans
      ((congrArg (biprod.fst : MA ⊞ MB ⟶ MA).hom hz').trans (biprod_fst_inl_add _ _))
    have h2 := (biprod_snd_lift_apply _ _ z').symm.trans
      ((congrArg (biprod.snd : MA ⊞ MB ⟶ MB).hom hz').trans (biprod_snd_inl_add _ _))
    refine ⟨(compIso ιY ιX ψC q).hom.hom z', ?_, ?_⟩
    · rw [← compIso_morL ιY ιX (extHyp A) inf_le_left inf_le_left hψA hψC,
        ← heY q _ _ inf_le_left _ _ (morL_spec _ inf_le_left), h1, Iso.inv_hom_id_apply]
    · rw [← compIso_morL ιY ιX (extHyp B) inf_le_right inf_le_right hψB hψC,
        ← heY q _ _ inf_le_right _ _ (morL_spec _ inf_le_right), ← map_neg,
        ← LinearMap.neg_apply, ← ModuleCat.hom_neg, h2, Iso.inv_hom_id_apply]
  · haveI : Subsingleton ((HcF ((Opens.toTopCat ((Opens.toTopCat X).obj W)).obj (A' ⊓ B'))
        (q + 1)).obj ((resF (A' ⊓ B')).obj ((resF W).obj F))) :=
      ModuleCat.isZero_iff_subsingleton.mp (hz.of_iso (compIso ιY ιX ψC (q + 1)))
    obtain ⟨u, hu⟩ := (ex2 (((ιX W q).inv.app ((resF W).obj F)).hom w)).mp (Subsingleton.elim _ _)
    refine ⟨(compIso ιY ιX ψA q).hom.hom ((biprod.fst : MA ⊞ MB ⟶ MA).hom u),
      (compIso ιY ιX ψB q).hom.hom ((biprod.snd : MA ⊞ MB ⟶ MB).hom u), ?_⟩
    rw [← compIso_cU ιY ιX hAW hψA, ← compIso_cU ιY ιX hBW hψB, ← map_add, ← biprod_desc_apply, hu,
      hom_comp_apply, Iso.inv_hom_id_app]
    rfl

end MV

/-! ### Vanishing over the empty set -/

section Empty

variable {X : TopCat.{0}} [LocallyCompactSpace X] [T2Space X]
  (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X)

/-- `H^q_c(X, F_V) = 0` for `q > 0` when `V` is empty: `F_V` is c-soft. -/
private lemma isZero_EH_of_eq_empty {V : Opens X} (hV : (V : Set X) = ∅) (q : ℤ) (hq : 0 < q) :
    IsZero (EH F q V) := by
  have hres : ∀ (K : Set ((Opens.toTopCat X).obj V)), IsCompact K →
      ∀ W : Opens ((Opens.toTopCat X).obj V), K ⊆ W →
        ∀ s : ((TopCat.Sheaf.forget _ _).obj ((resF V).obj F)).obj (op W),
          ∃ t : ((TopCat.Sheaf.forget _ _).obj ((resF V).obj F)).obj (op ⊤),
            ∃ (W' : Opens _) (h : W' ≤ W), K ⊆ W' ∧
              ((TopCat.Sheaf.forget _ _).obj ((resF V).obj F)).map (homOfLE h).op s =
                ((TopCat.Sheaf.forget _ _).obj ((resF V).obj F)).map (homOfLE le_top).op t := by
    intro K _ W _ s
    haveI : Subsingleton (((TopCat.Sheaf.forget _ _).obj ((resF V).obj F)).obj (op ⊥)) :=
      ModuleCat.isZero_iff_subsingleton.mp
        (TopCat.Sheaf.isTerminalOfEmpty ((resF V).obj F)).isZero
    exact ⟨0, ⊥, bot_le, fun x _ => (show x.1 ∈ (∅ : Set X) from hV ▸ x.2).elim,
      Subsingleton.elim _ _⟩
  obtain ⟨h, -⟩ := compactSupportCohomology_extendByZero ℚ X
  have hext := (h V).2.2.2.2.1 ((resF V).obj F) hres
  obtain ⟨-, -, hc, -⟩ := compactSupportCohomology_of_isCSoft ℚ X
  refine hc (LU F V) ?_ q hq
  intro K hK W hKW s
  obtain ⟨t, W', hW', hK', heq⟩ := hext K hK W hKW s
  exact ⟨t, W', hK', hW', heq.symm⟩

end Empty

/-! ### The induction over finite subfamilies -/

section Induction

open scoped Classical

variable {X : TopCat.{0}} [LocallyCompactSpace X] [T2Space X]
  (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X) {ι : Type} [LinearOrder ι]

/-- A family of opens all of whose nonempty finite intersections are planes. -/
private def Good (V : ι → Opens X) : Prop :=
  ∀ I : Finset ι, I.Nonempty → (⋂ i ∈ I, (V i : Set X)).Nonempty →
    Nonempty ((⋂ i ∈ I, (V i : Set X)) ≃ₜ EuclideanSpace ℝ (Fin 2))

private lemma Good.inf {V : ι → Opens X} (hV : Good V) (k : ι) : Good (fun i => V i ⊓ V k) := by
  intro I hI hne
  have e : (⋂ i ∈ I, ((V i ⊓ V k : Opens X) : Set X)) = ⋂ i ∈ insert k I, (V i : Set X) := by
    ext x
    simp only [Opens.coe_inf, Set.mem_iInter, Set.mem_inter_iff, Finset.mem_insert,
      forall_eq_or_imp]
    constructor
    · intro h
      obtain ⟨i₀, hi₀⟩ := hI
      exact ⟨(h i₀ hi₀).2, fun i hi => (h i hi).1⟩
    · intro h i hi
      exact ⟨h.2 i hi, h.1⟩
  obtain ⟨φ⟩ := hV (insert k I) (Finset.insert_nonempty k I) (e ▸ hne)
  exact ⟨(Homeomorph.setCongr e).trans φ⟩

private lemma Good.homeomorph {V : ι → Opens X} (hV : Good V) (k : ι)
    (hk : (V k : Set X).Nonempty) : Nonempty (V k ≃ₜ EuclideanSpace ℝ (Fin 2)) := by
  have e := Finset.set_biInter_singleton k (fun i => (V i : Set X))
  obtain ⟨φ⟩ := hV {k} (Finset.singleton_nonempty k) (e ▸ hk)
  exact ⟨(Homeomorph.setCongr e.symm).trans φ⟩

/-- The sum of the extension maps `⨁_{i ∈ s} E²(V i) → E²(W)`. -/
private def σ (s : Finset ι) (V : ι → Opens X) (W : Opens X) :
    (∀ i, EH F 2 (V i)) →ₗ[ℚ] EH F 2 W :=
  ∑ i ∈ s, (if h : V i ≤ W then morE F 2 h else 0) ∘ₗ LinearMap.proj i

private lemma σ_apply (s : Finset ι) (V : ι → Opens X) (W : Opens X) (x : ∀ i, EH F 2 (V i)) :
    σ F s V W x = ∑ i ∈ s, if h : V i ≤ W then morE F 2 h (x i) else 0 := by
  simp only [σ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> rfl

private lemma σ_congr (s : Finset ι) (V : ι → Opens X) (W : Opens X) {x y : ∀ i, EH F 2 (V i)}
    (hxy : ∀ i ∈ s, x i = y i) : σ F s V W x = σ F s V W y := by
  rw [σ_apply, σ_apply]
  exact Finset.sum_congr rfl fun i hi => by rw [hxy i hi]

private lemma morE_σ (s : Finset ι) (V : ι → Opens X) {W U : Opens X} (hle : ∀ i ∈ s, V i ≤ W)
    (hWU : W ≤ U) (x : ∀ i, EH F 2 (V i)) : morE F 2 hWU (σ F s V W x) = σ F s V U x := by
  rw [σ_apply, σ_apply, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [dite_eq_left (hle i hi), dite_eq_left ((hle i hi).trans hWU), morE_comp]

private lemma σ_insert {s : Finset ι} {k : ι} (hk : k ∉ s) (V : ι → Opens X) {A W : Opens X}
    (hle : ∀ i ∈ s, V i ≤ A) (hAW : A ≤ W) (hkW : V k ≤ W) (x : ∀ i, EH F 2 (V i)) :
    σ F (insert k s) V W x = morE F 2 hAW (σ F s V A x) + morE F 2 hkW (x k) := by
  rw [morE_σ F s V hle hAW, σ_apply, σ_apply, Finset.sum_insert hk, dite_eq_left hkW, add_comm]

/-- `(e, -e)` on the generator `y ∈ E²(V i ∩ V j)` of the pair `p = (i, j)`. -/
private def dPair (V : ι → Opens X) (p : {p : ι × ι // p.1 < p.2})
    (y : EH F 2 (V p.1.1 ⊓ V p.1.2)) : ∀ i, EH F 2 (V i) :=
  Pi.single p.1.1 (morE F 2 inf_le_left y) - Pi.single p.1.2 (morE F 2 inf_le_right y)

/-- The relations coming from pairs inside `s`. -/
private def pairRelSpan (s : Finset ι) (V : ι → Opens X) : Submodule ℚ (∀ i, EH F 2 (V i)) :=
  Submodule.span ℚ {x | ∃ (p : {p : ι × ι // p.1 < p.2}) (y : EH F 2 (V p.1.1 ⊓ V p.1.2)),
    p.1.1 ∈ s ∧ p.1.2 ∈ s ∧ x = dPair F V p y}

private lemma pairRelSpan_mono {s t : Finset ι} (hst : s ⊆ t) (V : ι → Opens X) :
    pairRelSpan F s V ≤ pairRelSpan F t V :=
  Submodule.span_mono fun _ ⟨p, y, h1, h2, h⟩ => ⟨p, y, hst h1, hst h2, h⟩

/-- **The induction.** For a good family `V` and a finite `s`, with `W = ⋃_{i ∈ s} V i`:
`E^q(W) = 0` for `q > 2`, and `⨁_{i ∈ s} E²(V i) → E²(W)` is onto with kernel spanned by the
relations of the pairs in `s`. -/
private theorem induction_step
    (hP : ∀ V : Opens X, Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2)) → ∀ q : ℤ, q ≠ 2 →
      IsZero (EH F q V)) (s : Finset ι) :
    ∀ V : ι → Opens X, Good V → ∀ W : Opens X, W = ⨆ i ∈ s, V i →
      (∀ q : ℤ, 2 < q → IsZero (EH F q W)) ∧
      (∀ z : EH F 2 W, ∃ x : ∀ i, EH F 2 (V i), (∀ i ∉ s, x i = 0) ∧ σ F s V W x = z) ∧
      (∀ x : ∀ i, EH F 2 (V i), (∀ i ∉ s, x i = 0) → σ F s V W x = 0 → x ∈ pairRelSpan F s V) := by
  induction s using Finset.induction_on_max with
  | empty =>
    intro V _ W hW
    have hWe : (W : Set X) = ∅ := by rw [hW]; simp
    refine ⟨fun q hq => isZero_EH_of_eq_empty F hWe q (by omega),
      fun z => ⟨0, fun _ _ => rfl, ?_⟩, fun x hx _ => ?_⟩
    · haveI := ModuleCat.isZero_iff_subsingleton.mp (isZero_EH_of_eq_empty F hWe 2 (by norm_num))
      exact Subsingleton.elim _ _
    · have : x = 0 := funext fun i => hx i (Finset.notMem_empty i)
      rw [this]; exact Submodule.zero_mem _
  | insert k s hlt IH =>
    intro V hV W hW
    have hk : k ∉ s := fun h => lt_irrefl k (hlt k h)
    obtain ⟨A, hA⟩ : ∃ A : Opens X, A = ⨆ i ∈ s, V i := ⟨_, rfl⟩
    have hAB : A ⊔ V k = W := by rw [hW, Finset.iSup_insert, sup_comm, hA]
    have hle : ∀ i ∈ s, V i ≤ A := fun i hi => hA ▸ le_iSup₂ (f := fun i (_ : i ∈ s) => V i) i hi
    have hAW : A ≤ W := hAB ▸ le_sup_left
    have hkW : V k ≤ W := hAB ▸ le_sup_right
    obtain ⟨IH1a, IH1b, IH1c⟩ := IH V hV A hA
    have hC : A ⊓ V k = ⨆ i ∈ s, (V i ⊓ V k) := by rw [hA, iSup₂_inf_eq]
    obtain ⟨IH2a, IH2b, -⟩ := IH (fun i => V i ⊓ V k) (hV.inf k) (A ⊓ V k) hC
    have hle' : ∀ i ∈ s, V i ⊓ V k ≤ A ⊓ V k := fun i hi => inf_le_inf_right _ (hle i hi)
    have hB : ∀ q : ℤ, 2 < q → IsZero (EH F q (V k)) := by
      intro q hq
      rcases (V k : Set X).eq_empty_or_nonempty with he | hne
      · exact isZero_EH_of_eq_empty F he q (by omega)
      · exact hP _ (hV.homeomorph k hne) q (by omega)
    have hMV := fun q => mv_transfer F W A (V k) hAB q
    refine ⟨fun q hq => ?_, fun z => ?_, fun x hx hσ => ?_⟩
    · have h0 : ∀ w : EH F q W, w = 0 := fun w => by
        obtain ⟨a, b, hab⟩ := (hMV q).2 (IH2a (q + 1) (by omega)) w
        haveI := ModuleCat.isZero_iff_subsingleton.mp (IH1a q hq)
        haveI := ModuleCat.isZero_iff_subsingleton.mp (hB q hq)
        rw [← hab, Subsingleton.elim a 0, Subsingleton.elim b 0, map_zero, map_zero, add_zero]
      exact ModuleCat.isZero_iff_subsingleton.mpr ⟨fun w₁ w₂ => by rw [h0 w₁, h0 w₂]⟩
    · obtain ⟨a, b, hab⟩ := (hMV 2).2 (IH2a 3 (by norm_num)) z
      obtain ⟨x', hx's, hx'⟩ := IH1b a
      refine ⟨x' + Pi.single k b, fun i hi => ?_, ?_⟩
      · rw [Finset.mem_insert, not_or] at hi
        rw [Pi.add_apply, hx's i hi.2, Pi.single_eq_of_ne hi.1, add_zero]
      · have hσx : σ F s V A (x' + Pi.single k b) = σ F s V A x' :=
          σ_congr F s V A fun i hi => by
            rw [Pi.add_apply, Pi.single_eq_of_ne (fun e : i = k => hk (e ▸ hi)), add_zero]
        rw [σ_insert F hk V hle hAW hkW, hσx, hx', Pi.add_apply, hx's k hk, Pi.single_eq_same,
          zero_add]
        exact hab
    · have hsum := σ_insert F hk V hle hAW hkW x
      rw [hσ] at hsum
      obtain ⟨z, hz1, hz2⟩ := (hMV 2).1 (σ F s V A x) (x k) hsum.symm
      obtain ⟨y₀, -, hy₀⟩ := IH2b z
      let e₁ : ∀ i, EH F 2 (V i) := fun i => morE F 2 (inf_le_left : V i ⊓ V k ≤ V i) (y₀ i)
      let e₂ : ι → EH F 2 (V k) := fun i => morE F 2 (inf_le_right : V i ⊓ V k ≤ V k) (y₀ i)
      let u : ∀ i, EH F 2 (V i) := (∑ i ∈ s, Pi.single i (e₁ i)) - Pi.single k (∑ i ∈ s, e₂ i)
      have hu : u ∈ pairRelSpan F (insert k s) V := by
        have : u = ∑ i ∈ s, (Pi.single i (e₁ i) - Pi.single k (e₂ i)) := by
          simp only [u]
          rw [Finset.sum_sub_distrib]
          congr 1
          exact map_sum (AddMonoidHom.single (fun i => EH F 2 (V i)) k) e₂ s
        rw [this]
        exact Submodule.sum_mem _ fun i hi => Submodule.subset_span
          ⟨⟨(i, k), hlt i hi⟩, y₀ i, Finset.mem_insert_of_mem hi, Finset.mem_insert_self k s, rfl⟩
      have hS : ∑ i ∈ s, e₂ i = morE F 2 inf_le_right z := by
        rw [← hy₀, morE_σ F s _ hle' inf_le_right, σ_apply]
        exact Finset.sum_congr rfl fun i _ => by rw [dite_eq_left inf_le_right]
      have hus : ∀ j ∈ s, u j = e₁ j := fun j hj => by
        simp only [u, Pi.sub_apply, Finset.sum_apply, Finset.sum_pi_single, if_pos hj,
          Pi.single_eq_of_ne (fun e : j = k => hk (e ▸ hj)), sub_zero]
      have hxu : x - u ∈ pairRelSpan F s V := by
        apply IH1c
        · intro j hj
          by_cases hjk : j = k
          · subst hjk
            simp only [u, Pi.sub_apply, Finset.sum_apply, Finset.sum_pi_single, if_neg hj,
              Pi.single_eq_same, hS, ← hz2]
            abel
          · have hj' : j ∉ insert k s := by
              rw [Finset.mem_insert, not_or]; exact ⟨hjk, hj⟩
            simp only [u, Pi.sub_apply, Finset.sum_apply, Finset.sum_pi_single, if_neg hj,
              Pi.single_eq_of_ne hjk, hx j hj']
            simp
        · rw [map_sub, σ_congr F s V A hus, ← hz1, ← hy₀, morE_σ F s _ hle' inf_le_left,
            σ_apply, σ_apply, sub_eq_zero]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [dite_eq_left (hle i hi), dite_eq_left (inf_le_left.trans (hle i hi))]
          exact (morE_comp F 2 _ _ _).symm
      have : x = (x - u) + u := by abel
      rw [this]
      exact Submodule.add_mem _ (pairRelSpan_mono F (Finset.subset_insert k s) V hxu) hu

end Induction

/-! ### Planes -/

section Plane

section ConstantSheaf

variable {Y : TopCat.{0}} (E : ModuleCat.{0} ℚ)

/-- `e ↦` the germ at `p` of the constant section `e`. -/
private def germConst (p : Y) :
    E →ₗ[ℚ] ((TopCat.Sheaf.forget _ Y).obj
      ((constantSheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ)).obj E)).stalk p :=
  (((TopCat.Sheaf.forget _ Y).obj
      ((constantSheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ)).obj E)).germ
        ⊤ p (Opens.mem_top p)).hom ∘ₗ
    ((CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
      ((Functor.const (Opens Y)ᵒᵖ).obj E)).app (op ⊤)).hom

/-- The stalk of the constant sheaf with value `E` is `E`. -/
private def stalkConstIso (p : Y) :
    E ≅ ((TopCat.Sheaf.forget _ Y).obj
      ((constantSheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ)).obj E)).stalk p :=
  (LinearEquiv.ofBijective (germConst E p)
    ⟨(injective_iff_map_eq_zero _).mpr fun _ h => eq_zero_of_germ_constSection E p h,
      constantSheaf_exists_constSection_germ E p⟩).toModuleIso

/-- The inverse image of a constant sheaf is constant. -/
private def pullbackConstIso {X Y : TopCat.{0}} (f : X ⟶ Y) :
    constantSheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ) ⋙
      TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f ≅
      constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ) :=
  (((constantSheafAdj (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ) isTerminalTop).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f)).ofNatIsoRight
      (Iso.refl _)).leftAdjointUniq
    (constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ) isTerminalTop)

end ConstantSheaf

/-- On a simply connected open `V`, a local system is the restriction of a constant sheaf with
finite-dimensional value. -/
private lemma exists_iso_resF_constantSheaf {S : TopCat.{0}} [LocallyPathConnectedSpace S]
    (L : TopCat.Sheaf (ModuleCat.{0} ℚ) S) (hL : IsLocalSystem L) (V : Opens S)
    [SimplyConnectedSpace V] (x : S) (hx : x ∈ V) :
    ∃ E : FGModuleCat.{0} ℚ, Nonempty ((resF V).obj L ≅ (resF V).obj
      (((ModuleCat.isFG.{0} ℚ).ι ⋙
        constantSheaf (Opens.grothendieckTopology S) (ModuleCat.{0} ℚ)).obj E)) := by
  obtain ⟨V₀, hx₀, E₀, hfin, ⟨ψ₀⟩⟩ := hL x
  let p₀ : (Opens.toTopCat S).obj V₀ := ⟨x, hx₀⟩
  let iso1 : E₀ ≅ ((TopCat.Sheaf.forget _ S).obj L).stalk x :=
    stalkConstIso E₀ p₀ ≪≫ (st p₀).mapIso ψ₀.symm ≪≫
      (st p₀).mapIso ((V₀.isOpenEmbedding.sheafPullbackIso (ModuleCat.{0} ℚ)).app L) ≪≫
      AlgebraicGeometry.PresheafedSpace.restrictStalkIso ⟨S, L.presheaf⟩ V₀.isOpenEmbedding p₀
  obtain ⟨φ, -⟩ := hL.exists_iso_constantSheaf_parallelTransport V x hx
  exact ⟨⟨E₀, hfin⟩, ⟨((V.isOpenEmbedding.sheafPullbackIso (ModuleCat.{0} ℚ)).app L).symm ≪≫ φ ≪≫
    (constantSheaf _ _).mapIso iso1.symm ≪≫ ((pullbackConstIso V.inclusion').app E₀).symm ≪≫
    (V.isOpenEmbedding.sheafPullbackIso (ModuleCat.{0} ℚ)).app _⟩⟩

/-- On an open `V ⊆ S` homeomorphic to `ℝ²`, `H^q_c(S, L_V) = 0` for `q ≠ 2`. -/
private lemma isZero_EH_plane (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] (hH : Module.finrank ℝ H = 2) (S : TopCat.{0}) [T2Space S]
    [ChartedSpace H S] (hS : MMP.IsOrientedAtlas H S)
    [LocallyCompactSpace S] (L : TopCat.Sheaf (ModuleCat.{0} ℚ) S) (hL : IsLocalSystem L)
    (V : Opens S) (hV : Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2))) (q : ℤ) (hq : q ≠ 2) :
    IsZero (EH L q V) := by
  obtain ⟨e⟩ := hV
  haveI : ContractibleSpace V := e.contractibleSpace
  haveI : LocallyPathConnectedSpace S := ChartedSpace.locallyPathConnectedSpace H S
  obtain ⟨E, ⟨χ⟩⟩ := exists_iso_resF_constantSheaf L hL V (e.symm 0).1 (e.symm 0).2
  obtain ⟨hvan, -⟩ := compactSupportCohomology_orientedPlane_trace H hH S hS
  obtain ⟨ι₀⟩ := exists_comparison S
  exact ((hvan V ⟨e⟩ q hq E).of_iso ((HcF _ q).mapIso χ)).of_iso
    ((ι₀ V q).app ((resF V).obj L)).symm

end Plane

/-! ### The theorem -/

open scoped Classical in
/-- **Top compactly supported cohomology from a good cover.** Let `S` be a Hausdorff surface
with an oriented atlas modelled on a real normed plane `H`, with a finite cover by opens `U i`,
indexed by a finite linearly ordered type `ι`, such that every nonempty intersection
`⋂_{i ∈ I} U i` over a nonempty finite `I` is homeomorphic to `ℝ²`, and let `L` be a local system
of finite-dimensional `ℚ`-vector spaces on `S`. Write `j_!` for extension by zero and `j^*` for
restriction along an open `U ⊆ S`, and `Hc 2` for `H²_c(S, -)`. Then
`H^q_c(S, L) = 0` for `q > 2`; and for any morphisms
`m₁ p : j_! j^* L|_{U i ∩ U j} ⟶ j_! j^* L|_{U i}` and `m₂ p : … ⟶ j_! j^* L|_{U j}` over `L`
(for `p = (i, j)`, `i < j`), the sequence
`∏_{i<j} H²_c(S, j_! j^* L|_{U i ∩ U j}) → ∏_i H²_c(S, j_! j^* L|_{U i}) → H²_c(S, L) → 0`
is exact, where the first map is `x ↦ (m₁ x, -m₂ x)` on each pair and the second is the sum of the
maps induced by the counits `j_! j^* L ⟶ L`. -/
@[mmp "lem_mmp_surface_good_cover_top_compact_support"]
public theorem compactSupportCohomology_two_of_goodCover
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    (hH : Module.finrank ℝ H = 2) (S : TopCat.{0}) [T2Space S] [ChartedSpace H S]
    (hS : MMP.IsOrientedAtlas H S) {ι : Type} [Fintype ι] [LinearOrder ι]
    (U : ι → Opens S)
    (hU : ⨆ i, U i = ⊤)
    (hgood : ∀ I : Finset ι, I.Nonempty → (⋂ i ∈ I, (U i : Set S)).Nonempty →
      Nonempty ((⋂ i ∈ I, (U i : Set S)) ≃ₜ EuclideanSpace ℝ (Fin 2)))
    (L : TopCat.Sheaf (ModuleCat.{0} ℚ) S) (hL : IsLocalSystem L) :
    let res : ∀ V : Opens S, TopCat.Sheaf (ModuleCat.{0} ℚ) S ⥤
        TopCat.Sheaf (ModuleCat.{0} ℚ) ((Opens.toTopCat S).obj V) := fun V =>
      haveI := V.isOpenEmbedding.functor_isContinuous
      V.isOpenEmbedding.functor.sheafPushforwardContinuous _ _ _
    let ext : ∀ V : Opens S, TopCat.Sheaf (ModuleCat.{0} ℚ) ((Opens.toTopCat S).obj V) ⥤
        TopCat.Sheaf (ModuleCat.{0} ℚ) S := fun V =>
      haveI := V.isOpenEmbedding.functor_isContinuous
      V.isOpenEmbedding.functor.sheafPullback _ _ _
    let adj : ∀ V : Opens S, ext V ⊣ res V := fun V =>
      haveI := V.isOpenEmbedding.functor_isContinuous
      V.isOpenEmbedding.functor.sheafAdjunctionContinuous _ _ _
    let Hc : ℤ → (TopCat.Sheaf (ModuleCat.{0} ℚ) S ⥤ ModuleCat.{0} ℚ) := fun q =>
      DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (compactSupportSectionsFunctor ℚ (X := S)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor _ q
    let E : Opens S → ModuleCat.{0} ℚ := fun V => (Hc 2).obj ((ext V).obj ((res V).obj L))
    (∀ q : ℤ, 2 < q → IsZero (compactSupportCohomology ℚ q L)) ∧
    ∀ (m₁ : ∀ p : {p : ι × ι // p.1 < p.2},
        (ext (U p.1.1 ⊓ U p.1.2)).obj ((res (U p.1.1 ⊓ U p.1.2)).obj L) ⟶
          (ext (U p.1.1)).obj ((res (U p.1.1)).obj L))
      (m₂ : ∀ p : {p : ι × ι // p.1 < p.2},
        (ext (U p.1.1 ⊓ U p.1.2)).obj ((res (U p.1.1 ⊓ U p.1.2)).obj L) ⟶
          (ext (U p.1.2)).obj ((res (U p.1.2)).obj L)),
      (∀ p, m₁ p ≫ (adj (U p.1.1)).counit.app L = (adj (U p.1.1 ⊓ U p.1.2)).counit.app L) →
      (∀ p, m₂ p ≫ (adj (U p.1.2)).counit.app L = (adj (U p.1.1 ⊓ U p.1.2)).counit.app L) →
      let e₁ : ∀ p : {p : ι × ι // p.1 < p.2},
          (E (U p.1.1 ⊓ U p.1.2)).carrier →ₗ[ℚ] (E (U p.1.1)).carrier :=
        fun p => ((Hc 2).map (m₁ p)).hom
      let e₂ : ∀ p : {p : ι × ι // p.1 < p.2},
          (E (U p.1.1 ⊓ U p.1.2)).carrier →ₗ[ℚ] (E (U p.1.2)).carrier :=
        fun p => ((Hc 2).map (m₂ p)).hom
      let c : ∀ i, (E (U i)).carrier →ₗ[ℚ] ((Hc 2).obj L).carrier :=
        fun i => ((Hc 2).map ((adj (U i)).counit.app L)).hom
      let d : (∀ p : {p : ι × ι // p.1 < p.2}, (E (U p.1.1 ⊓ U p.1.2)).carrier) →ₗ[ℚ]
          (∀ i, (E (U i)).carrier) :=
        ∑ p : {p : ι × ι // p.1 < p.2},
          (LinearMap.single ℚ (fun i => (E (U i)).carrier) p.1.1 ∘ₗ e₁ p -
          LinearMap.single ℚ (fun i => (E (U i)).carrier) p.1.2 ∘ₗ e₂ p) ∘ₗ
            LinearMap.proj (R := ℚ) (φ := fun p : {p : ι × ι // p.1 < p.2} =>
              (E (U p.1.1 ⊓ U p.1.2)).carrier) p
      let σ : (∀ i, (E (U i)).carrier) →ₗ[ℚ] ((Hc 2).obj L).carrier :=
        ∑ i : ι, c i ∘ₗ LinearMap.proj (R := ℚ) (φ := fun i => (E (U i)).carrier) i
      LinearMap.range d = LinearMap.ker σ ∧ Function.Surjective σ := by
  intro res ext adj Hc E
  haveI : LocallyCompactSpace S := ChartedSpace.locallyCompactSpace H S
  have hP := fun V hV q hq => isZero_EH_plane H hH S hS L hL V hV q hq
  obtain ⟨hA, hB, hC⟩ := induction_step L hP Finset.univ U hgood ⊤ (by rw [← hU]; simp)
  haveI : IsIso (cU L ⊤) := isIso_of_isoBelow_top _ (isoBelow_cU (extHyp ⊤) L)
  let Θ : ∀ q : ℤ, EH L q ⊤ ≅ (HcF S q).obj L := fun q => (HcF S q).mapIso (asIso (cU L ⊤))
  refine ⟨fun q hq => (hA q hq).of_iso (Θ q).symm, fun m₁ m₂ h₁ h₂ => ?_⟩
  intro e₁ e₂ c d σ'
  have hm₁ : ∀ p, m₁ p = morL L (inf_le_left : U p.1.1 ⊓ U p.1.2 ≤ U p.1.1) :=
    fun p => morL_eq L _ (h₁ p)
  have hm₂ : ∀ p, m₂ p = morL L (inf_le_right : U p.1.1 ⊓ U p.1.2 ≤ U p.1.2) :=
    fun p => morL_eq L _ (h₂ p)
  have he₁ : ∀ p y, e₁ p y = morE L 2 inf_le_left y := fun p y => by
    simp only [e₁, hm₁]; rfl
  have he₂ : ∀ p y, e₂ p y = morE L 2 inf_le_right y := fun p y => by
    simp only [e₂, hm₂]; rfl
  have hc : ∀ i v, c i v = (Θ 2).hom.hom (morE L 2 (le_top : U i ≤ ⊤) v) := fun i v => by
    simp only [c, Θ, Functor.mapIso_hom, asIso_hom, morE]
    rw [hom_comp_apply, ← Functor.map_comp, morL_spec]
  have hσ' : ∀ x, σ' x = (Θ 2).hom.hom (σ L Finset.univ U ⊤ x) := fun x => by
    simp only [σ', LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, σ_apply,
      map_sum, hc]
    exact Finset.sum_congr rfl fun i _ => by rw [dite_eq_left le_top]
  have hσs : ∀ i v, σ' (Pi.single i v) = c i v := fun i v => by
    simp only [σ', LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero])
      (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]
  have hd : ∀ p y, d (Pi.single p y) = dPair L U p y := fun p y => by
    simp only [d, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single p (fun b _ hb => by rw [Pi.single_eq_of_ne hb, map_zero])
      (fun h => absurd (Finset.mem_univ p) h), Pi.single_eq_same]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.single_apply, he₁, he₂, dPair]
  refine ⟨le_antisymm ?_ ?_, fun z => ?_⟩
  · rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, ← Finset.univ_sum_single y, map_sum, map_sum]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [hd, dPair, map_sub, hσs, hσs, hc, hc, morE_comp, morE_comp, sub_self]
  · intro x hx
    rw [LinearMap.mem_ker, hσ'] at hx
    have h0 : σ L Finset.univ U ⊤ x = 0 := by
      have := congrArg (Θ 2).inv.hom hx
      rwa [Iso.hom_inv_id_apply, map_zero] at this
    refine Submodule.span_le.mpr ?_ (hC x (fun i hi => absurd (Finset.mem_univ i) hi) h0)
    rintro _ ⟨p, y, -, -, rfl⟩
    exact ⟨Pi.single p y, hd p y⟩
  · obtain ⟨x, -, hx⟩ := hB ((Θ 2).inv.hom z)
    exact ⟨x, by rw [hσ', hx, Iso.inv_hom_id_apply]⟩

end GoodCover

end MMP.Fourfold
