module

public import MMP.AlgebraicGeometry.Analytic.Curve.FiniteGoodCover
public import MMP.Topology.Sheaves.LocalSystem.ParallelTransport
public import StacksFrontier.Algebra.Homology.DerivedCategory.InjectiveResolutionDerived

/-!
# Top compactly supported cohomology of a local system on a complex curve

Let `T` be a smooth complex algebraic curve whose analytic realization `T^an` is connected,
let `𝓛` be a local system of finite-dimensional `ℚ`-vector spaces on `T^an`, and let `t ∈ T^an`.
Then `H²_c(T^an, 𝓛)` is the space of coinvariants of the monodromy action of `π₁(T^an, t)` on
the fibre `𝓛_t`, that is, the quotient of `𝓛_t` by the span of the vectors `w - γ·w`.

Take a finite good cover `(U_i)` of `T^an`: every nonempty finite intersection is homeomorphic
to `ℝ²`. Then `H²_c(T^an, 𝓛)` is the cokernel of
`⨁_{i<j} H²_c(U_i ∩ U_j, 𝓛) → ⨁_i H²_c(U_i, 𝓛)`. Over a disc `V ∋ x` the local system is
isomorphic to the constant sheaf with fibre `𝓛_x`, the isomorphism being parallel transport
to `x` inside `V` on stalks; composed with the trace of the oriented disc this identifies
`H²_c(V, 𝓛)` with `𝓛_x`. Under these identifications the extension map from a smaller disc
`V' ≤ V` is transport inside `V`. Hence the cokernel is the colimit of the fibres `𝓛_{x_i}`
glued along transport, and transporting to `t` identifies it with `𝓛_t` modulo `w - g w`, `g`
running over the transports along loops at `t`: the class of `(y, v)` with `v ∈ 𝓛_y` is
constant along every path, by the local constancy of flat families over the unit interval.

## Main results

* `MMP.Fourfold.nonempty_compactSupportCohomology_two_linearEquiv_coinvariants`

## Implementation notes

The action of a loop `γ` at `t` on `𝓛_t` is parallel transport: `γ·w = v` exactly when some
global section of the inverse image `γ^* 𝓛` on `[0, 1]` has germ `w` at `0` and germ `v` at `1`
(fibres of `γ^* 𝓛` being identified with those of `𝓛` by
`MMP.Fourfold.stalkToPullbackStalk`). The relation submodule is therefore spanned by the
differences `w - v` of the two end germs of such sections, over all loops at `t`.

A complex algebraic curve is a separated scheme of finite type over `ℂ`; smoothness of
relative dimension one makes it a smooth curve.

The restriction `j^*` to an open `V` and the extension by zero `j_!` are those of the open
embedding `V → T^an` (`Functor.sheafPushforwardContinuous` and `Functor.sheafPullback` along
`IsOpenMap.functor`). Morphisms of restricted sheaves are built from, and compared by, their
action on germs. The compatibility of the extension maps with the trivializations is reduced,
through the adjunction `j_! ⊣ j^*`, to a statement on stalks.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][kollarmori1998]
* [B. Iversen, *Cohomology of sheaves*][iversen1986], III and V.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Limits Topology
open MMP.Analytic.ComplexPoints

attribute [local instance] HasDerivedCategory.standard

namespace MMP.Fourfold

noncomputable section

/-! ### Constant sheaves and sections along paths -/

section ConstantSheafGerms

/-- The constant sheaf with value `E`, as a sheaf on the space `V`. -/
@[expose]
public def cSh (V : TopCat.{0}) (E : ModuleCat.{0} ℚ) : TopCat.Sheaf (ModuleCat.{0} ℚ) V :=
  (constantSheaf (Opens.grothendieckTopology V) (ModuleCat.{0} ℚ)).obj E

variable {V : TopCat.{0}} (E : ModuleCat.{0} ℚ)

/-- The constant section `e` of the constant sheaf with value `E`. -/
@[expose]
public def constSection (e : E) :
    ToType (((TopCat.Sheaf.forget _ V).obj (cSh V E)).obj (op ⊤)) :=
  ((CategoryTheory.toSheafify (Opens.grothendieckTopology V)
    ((Functor.const (Opens V)ᵒᵖ).obj E)).app (op ⊤)).hom e

/-- Every germ of a constant sheaf is the germ of a constant section. -/
public theorem constantSheaf_exists_constSection_germ (p : V)
    (c : ToType (((TopCat.Sheaf.forget _ V).obj (cSh V E)).stalk p)) :
    ∃ e : E, ((TopCat.Sheaf.forget _ V).obj (cSh V E)).germ
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
public theorem eq_zero_of_germ_constSection {e : E} (p : V)
    (h : ((TopCat.Sheaf.forget _ V).obj (cSh V E)).germ ⊤ p (Opens.mem_top p)
        (constSection E e) = 0) : e = 0 := by
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
    (σ : ToType (((TopCat.Sheaf.forget _ V).obj (cSh V E)).obj (op U)))
    (p : V) (hp : p ∈ U) :
    ∃ (e : E) (N : Opens V) (_ : p ∈ N) (hNU : N ≤ U), ∀ v (hv : v ∈ N),
      ((TopCat.Sheaf.forget _ V).obj (cSh V E)).germ U v (hNU hv) σ =
        ((TopCat.Sheaf.forget _ V).obj (cSh V E)).germ ⊤ v (Opens.mem_top v)
          (constSection E e) := by
  obtain ⟨e, he⟩ := constantSheaf_exists_constSection_germ E p
    (((TopCat.Sheaf.forget _ V).obj (cSh V E)).germ U p hp σ)
  obtain ⟨W, hW, iU, iT, hWe⟩ := TopCat.Presheaf.germ_eq _ p hp (Opens.mem_top p) σ
    (constSection E e) he.symm
  refine ⟨e, W, hW, iU.le, fun v hv => ?_⟩
  exact (TopCat.Presheaf.germ_res_apply _ iU v hv σ).symm.trans
    ((congrArg _ hWe).trans (TopCat.Presheaf.germ_res_apply _ iT v hv _))

end ConstantSheafGerms

/-! ### Gluing germs -/

section Gluing

variable {X : TopCat.{0}}

/-- **Gluing germs.** A family of germs of a sheaf which is, near every point of `O`, the family
of germs of a section is the family of germs of a section over `O`. -/
private theorem exists_section_of_locally (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X) (O : Opens X)
    (b : ∀ x : X, ToType (((TopCat.Sheaf.forget _ X).obj F).stalk x))
    (hb : ∀ x₀ ∈ O, ∃ (W : Opens X) (r : ToType (((TopCat.Sheaf.forget _ X).obj F).obj (op W)))
      (N : Opens X) (_ : x₀ ∈ N) (hNW : N ≤ W) (_ : N ≤ O), ∀ x (hx : x ∈ N),
        b x = ((TopCat.Sheaf.forget _ X).obj F).germ W x (hNW hx) r) :
    ∃ t : ToType (((TopCat.Sheaf.forget _ X).obj F).obj (op O)), ∀ x (hx : x ∈ O),
      ((TopCat.Sheaf.forget _ X).obj F).germ O x hx t = b x := by
  choose W r N hN hNW hNO hloc using fun p : O => hb p.1 p.2
  let sf : ∀ p : O, ToType (((TopCat.Sheaf.forget _ X).obj F).obj (op (N p))) := fun p =>
    ((TopCat.Sheaf.forget _ X).obj F).map (homOfLE (hNW p)).op (r p)
  have hgerm : ∀ p x (hx : x ∈ N p), ((TopCat.Sheaf.forget _ X).obj F).germ (N p) x hx (sf p) =
      b x := by
    intro p x hx
    rw [TopCat.Presheaf.germ_res_apply, hloc p x hx]
  have hcompat : TopCat.Presheaf.IsCompatible ((TopCat.Sheaf.forget _ X).obj F) N sf := by
    intro i j
    refine TopCat.Presheaf.section_ext F _ _ _ fun x hx => ?_
    change ((TopCat.Sheaf.forget _ X).obj F).germ _ x hx _ =
      ((TopCat.Sheaf.forget _ X).obj F).germ _ x hx _
    exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).trans ((hgerm i x hx.1).trans
      ((hgerm j x hx.2).symm.trans (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm))
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' F N O (fun p => homOfLE (hNO p))
    (fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hN _⟩) sf hcompat
  refine ⟨s, fun x hx => ?_⟩
  rw [← hgerm ⟨x, hx⟩ x (hN _), ← hs ⟨x, hx⟩]
  exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm

end Gluing

/-! ### Germs of inverse images, and parallel transport -/

section Transport

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Y)

/-- The inverse image `f^* F` of the sheaf `F` along `f`. -/
public abbrev Pb : TopCat.Sheaf (ModuleCat.{0} ℚ) X :=
  (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj F

/-- The section of `f^* F` over `f⁻¹(W)` attached to a section of `F` over `W`. -/
@[expose]
public def unitSec {W : Opens Y} (r : ToType (((TopCat.Sheaf.forget _ Y).obj F).obj (op W))) :
    ToType (((TopCat.Sheaf.forget _ X).obj (Pb f F)).obj (op ((Opens.map f).obj W))) :=
  (((TopCat.Sheaf.forget _ Y).map
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app F)).app
      (op W)).hom r

/-- `stalkToPullbackStalk` sends the germ of `r` at `f x` to the germ of `unitSec f F r` at `x`. -/
public theorem stalkToPullbackStalk_germ {W : Opens Y}
    (r : ToType (((TopCat.Sheaf.forget _ Y).obj F).obj (op W))) (x : X) (hx : f x ∈ W) :
    (stalkToPullbackStalk f F x).hom (((TopCat.Sheaf.forget _ Y).obj F).germ W (f x) hx r) =
      ((TopCat.Sheaf.forget _ X).obj (Pb f F)).germ ((Opens.map f).obj W) x hx (unitSec f F r) := by
  have h : ((TopCat.Sheaf.forget _ Y).obj F).germ W (f x) hx ≫ stalkToPullbackStalk f F x =
      ((TopCat.Sheaf.forget _ Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app F)).app
          (op W) ≫ ((TopCat.Sheaf.forget _ X).obj (Pb f F)).germ ((Opens.map f).obj W) x hx := by
    unfold stalkToPullbackStalk
    erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc, TopCat.Presheaf.stalkPushforward_germ]
    rfl
  exact congrArg (fun φ => φ.hom r) h

private theorem bijective_stalkToPullbackStalk (x : X) :
    Function.Bijective (stalkToPullbackStalk f F x).hom := by
  rw [show stalkToPullbackStalk f F x = (Stacks.SheafifyStalk.stalkSheafPullbackIso _ f F x).inv
    from (Stacks.SheafifyStalk.stalkSheafPullbackIso_inv_eq _ f F x).symm]
  exact (Stacks.SheafifyStalk.stalkSheafPullbackIso _ f F x).symm.toLinearEquiv.bijective

/-- Every section of `f^* F` is, near each point, the image of a section of `F`. -/
public theorem exists_local_germ {U : Opens X}
    (s : ToType (((TopCat.Sheaf.forget _ X).obj (Pb f F)).obj (op U))) (x₀ : X) (hx₀ : x₀ ∈ U) :
    ∃ (W : Opens Y) (r : ToType (((TopCat.Sheaf.forget _ Y).obj F).obj (op W))) (N : Opens X)
      (_ : x₀ ∈ N) (hNU : N ≤ U) (hNW : N ≤ (Opens.map f).obj W),
      ∀ x (hx : x ∈ N), ((TopCat.Sheaf.forget _ X).obj (Pb f F)).germ U x (hNU hx) s =
        (stalkToPullbackStalk f F x).hom
          (((TopCat.Sheaf.forget _ Y).obj F).germ W (f x) (hNW hx) r) := by
  obtain ⟨y, hy⟩ := (bijective_stalkToPullbackStalk f F x₀).2
    (((TopCat.Sheaf.forget _ X).obj (Pb f F)).germ U x₀ hx₀ s)
  obtain ⟨W, hW, r, rfl⟩ := ((TopCat.Sheaf.forget _ Y).obj F).exists_germ_eq y
  rw [stalkToPullbackStalk_germ] at hy
  obtain ⟨N, hN, iW, iU, e⟩ := ((TopCat.Sheaf.forget _ X).obj (Pb f F)).germ_eq x₀ _ _ _ _ hy
  refine ⟨W, r, N, hN, iU.le, iW.le, fun x hx => ?_⟩
  rw [← TopCat.Presheaf.germ_res_apply _ iU x hx, ← e, TopCat.Presheaf.germ_res_apply]
  exact (stalkToPullbackStalk_germ f F r x _).symm

/-- A family of germs of `F` along `f` which is locally given by sections of `F` is the family
of germs of a global section of `f^* F`. -/
private theorem exists_section_of_local
    (y : ∀ x : X, ToType (((TopCat.Sheaf.forget _ Y).obj F).stalk (f x)))
    (hy : ∀ x₀ : X, ∃ (W : Opens Y) (r : ToType (((TopCat.Sheaf.forget _ Y).obj F).obj (op W)))
      (N : Opens X) (_ : x₀ ∈ N) (hNW : N ≤ (Opens.map f).obj W),
      ∀ x (hx : x ∈ N), y x = ((TopCat.Sheaf.forget _ Y).obj F).germ W (f x) (hNW hx) r) :
    ∃ s : ToType (((TopCat.Sheaf.forget _ X).obj (Pb f F)).obj (op ⊤)), ∀ x,
      ((TopCat.Sheaf.forget _ X).obj (Pb f F)).germ ⊤ x trivial s =
        (stalkToPullbackStalk f F x).hom (y x) := by
  refine (exists_section_of_locally (Pb f F) ⊤ (fun x => (stalkToPullbackStalk f F x).hom (y x))
    fun x₀ _ => ?_).imp fun s hs x => hs x trivial
  obtain ⟨W, r, N, hN, hNW, hloc⟩ := hy x₀
  exact ⟨_, unitSec f F r, N, hN, hNW, le_top, fun x hx => by
    rw [hloc x hx]; exact stalkToPullbackStalk_germ f F r x _⟩

/-- **Reparametrization.** For `γ' = γ ∘ a`, a section of `γ^* F` induces a section of `γ'^* F`
with the transported germs. -/
private theorem exists_section_reparam {X' : TopCat.{0}} (γ : X ⟶ Y) (γ' : X' ⟶ Y) (a : C(X', X))
    (h : ∀ x, γ (a x) = γ' x)
    (s : ToType (((TopCat.Sheaf.forget _ X).obj (Pb γ F)).obj (op ⊤))) :
    ∃ s' : ToType (((TopCat.Sheaf.forget _ X').obj (Pb γ' F)).obj (op ⊤)),
      ∀ x p (hp : a x = p) (y : ToType (((TopCat.Sheaf.forget _ Y).obj F).stalk (γ p))),
        (stalkToPullbackStalk γ F p).hom y =
            ((TopCat.Sheaf.forget _ X).obj (Pb γ F)).germ ⊤ p trivial s →
          (stalkToPullbackStalk γ' F x).hom
              ((((TopCat.Sheaf.forget _ Y).obj F).stalkCongr
                (Inseparable.of_eq (hp ▸ h x))).hom.hom y) =
            ((TopCat.Sheaf.forget _ X').obj (Pb γ' F)).germ ⊤ x trivial s' := by
  set P := (TopCat.Sheaf.forget _ Y).obj F
  have hsurj := fun p => (bijective_stalkToPullbackStalk γ F p).2
  choose yy hyy using fun p => hsurj p (((TopCat.Sheaf.forget _ X).obj (Pb γ F)).germ ⊤ p trivial s)
  let z : ∀ x : X', ToType (P.stalk (γ' x)) := fun x =>
    (P.stalkCongr (Inseparable.of_eq (h x))).hom.hom (yy (a x))
  obtain ⟨s', hs'⟩ := exists_section_of_local γ' F z (fun x₀ => by
    obtain ⟨W, r, N, hN, _hNU, hNW, hloc⟩ := exists_local_germ γ F s (a x₀) trivial
    refine ⟨W, r, ⟨a ⁻¹' N, N.isOpen.preimage a.continuous⟩, hN, fun x hx => ?_, fun x hx => ?_⟩
    · change γ' x ∈ W
      rw [← h x]
      exact hNW hx
    · have e : yy (a x) = P.germ W (γ (a x)) (hNW hx) r :=
        (bijective_stalkToPullbackStalk γ F (a x)).1 ((hyy (a x)).trans (hloc (a x) hx))
      change (P.stalkCongr _).hom.hom (yy (a x)) = _
      rw [e]
      exact TopCat.Presheaf.germ_stalkSpecializes_apply P _ (Inseparable.of_eq (h x)).ge r)
  refine ⟨s', fun x p hp y hy => ?_⟩
  subst hp
  have e : y = yy (a x) := (bijective_stalkToPullbackStalk γ F (a x)).1 (hy.trans (hyy _).symm)
  subst e
  exact (hs' x).symm

section LocalSystem

variable {Z : TopCat.{0}} (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Z)

/-- Every germ at a point of `V` extends to a family of germs over `V` which is locally given by
sections of `F`. -/
@[expose]
public def GermExtendable (V : Opens Z) : Prop :=
  ∀ z' ∈ V, ∀ y' : ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk z'),
    ∃ Y : ∀ z : Z, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk z), Y z' = y' ∧
      ∀ z₀ ∈ V, ∃ (W : Opens Z) (r : ToType (((TopCat.Sheaf.forget _ Z).obj F).obj (op W)))
        (N : Opens Z) (_ : z₀ ∈ N) (hNW : N ≤ W), ∀ z (hz : z ∈ N),
          Y z = ((TopCat.Sheaf.forget _ Z).obj F).germ W z (hNW hz) r

/-- A local system is germ-extendable near every point. -/
public theorem exists_germExtendable (hF : IsLocalSystem F) (z : Z) :
    ∃ V : Opens Z, z ∈ V ∧ GermExtendable F V := by
  obtain ⟨V, hz, E, -, ⟨φ⟩⟩ := hF z
  classical
  refine ⟨V, hz, fun z' hz' y' => ?_⟩
  let ι := V.inclusion'
  let P := (TopCat.Sheaf.forget _ Z).obj F
  let Q := (TopCat.Sheaf.forget _ _).obj (Pb ι F)
  let pt : (Opens.toTopCat Z).obj V := ⟨z', hz'⟩
  let y'' := (stalkToPullbackStalk ι F pt).hom y'
  obtain ⟨e, hσc⟩ := constantSheaf_exists_constSection_germ E pt
    (((TopCat.Presheaf.stalkFunctor _ pt).map ((TopCat.Sheaf.forget _ _).map φ.hom)).hom y'')
  let σ : ToType (Q.obj (op ⊤)) :=
    (((TopCat.Sheaf.forget _ _).map φ.inv).app (op ⊤)).hom (constSection E e)
  have hσ : Q.germ ⊤ pt trivial σ = y'' := by
    have e1 := TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ pt trivial
      ((TopCat.Sheaf.forget _ _).map φ.inv) (constSection E e)
    refine e1.symm.trans ?_
    erw [hσc, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp,
      φ.hom_inv_id, CategoryTheory.Functor.map_id]
    rfl
  have hbij := fun (v : (Opens.toTopCat Z).obj V) => bijective_stalkToPullbackStalk ι F v
  let Y : ∀ z : Z, ToType (P.stalk z) := fun z => if h : z ∈ V then
    (Equiv.ofBijective _ (hbij ⟨z, h⟩)).symm (Q.germ ⊤ ⟨z, h⟩ trivial σ) else 0
  have hY : ∀ z (h : z ∈ V), (stalkToPullbackStalk ι F ⟨z, h⟩).hom (Y z) =
      Q.germ ⊤ ⟨z, h⟩ trivial σ := by
    intro z h
    rw [show Y z = _ from dif_pos h]
    exact (Equiv.ofBijective _ (hbij ⟨z, h⟩)).apply_symm_apply _
  refine ⟨Y, (hbij pt).1 ((hY z' hz').trans hσ), fun z₀ hz₀ => ?_⟩
  obtain ⟨W, r, N, hN, _hNU, hNW, hloc⟩ := exists_local_germ ι F σ ⟨z₀, hz₀⟩ trivial
  have hNopen : IsOpen (Subtype.val '' (SetLike.coe N : Set V)) :=
    V.isOpen.isOpenMap_subtype_val (SetLike.coe N : Set V) N.isOpen
  refine ⟨W, r, ⟨_, hNopen⟩, ⟨_, hN, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact hNW hv
  · rintro _ ⟨v, hv, rfl⟩
    exact (hbij v).1 ((hY v.1 v.2).trans ((hloc v hv).trans rfl))

end LocalSystem

section Interval

variable {Z : TopCat.{0}} (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Z) (γ : TopCat.of unitInterval ⟶ Z)

/-- A family of germs along `γ` is given near `x₀` by a section of `F`. -/
private def LocGerm (Y : ∀ x : unitInterval, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (γ x)))
    (x₀ : unitInterval) : Prop :=
  ∃ (W : Opens Z) (r : ToType (((TopCat.Sheaf.forget _ Z).obj F).obj (op W)))
    (N : Opens (TopCat.of unitInterval)) (_ : x₀ ∈ N) (hNW : N ≤ (Opens.map γ).obj W),
    ∀ x (hx : x ∈ N), Y x = ((TopCat.Sheaf.forget _ Z).obj F).germ W (γ x) (hNW hx) r

/-- Every germ at `γ q` extends to a family along `γ` given locally by sections up to `q`. -/
private def Reach (q : unitInterval) : Prop :=
  ∀ y : ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (γ q)),
    ∃ Y : ∀ x : unitInterval, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (γ x)),
      Y q = y ∧ ∀ x₀ ≤ q, LocGerm F γ Y x₀

variable {F γ}

private theorem LocGerm.congr {Y Y' : ∀ x : unitInterval,
    ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (γ x))} {x₀ : unitInterval}
    (h : LocGerm F γ Y x₀) (S : Set unitInterval) (hS : IsOpen S) (hx₀ : x₀ ∈ S)
    (hYY : ∀ x ∈ S, Y' x = Y x) : LocGerm F γ Y' x₀ := by
  obtain ⟨W, r, N, hN, hNW, hloc⟩ := h
  refine ⟨W, r, N ⊓ ⟨S, hS⟩, ⟨hN, hx₀⟩, fun x hx => hNW hx.1, fun x hx => ?_⟩
  exact (hYY x hx.2).trans (hloc x hx.1)

private theorem LocGerm.of_germExtendable {V : Opens Z} {Zf : ∀ z : Z,
    ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk z)}
    (hZ : ∀ z₀ ∈ V, ∃ (W : Opens Z) (r : ToType (((TopCat.Sheaf.forget _ Z).obj F).obj (op W)))
        (N : Opens Z) (_ : z₀ ∈ N) (hNW : N ≤ W), ∀ z (hz : z ∈ N),
          Zf z = ((TopCat.Sheaf.forget _ Z).obj F).germ W z (hNW hz) r)
    {x₀ : unitInterval} (hx₀ : γ x₀ ∈ V) : LocGerm F γ (fun x => Zf (γ x)) x₀ := by
  obtain ⟨W, r, N, hN, hNW, hloc⟩ := hZ (γ x₀) hx₀
  exact ⟨W, r, (Opens.map γ).obj N, hN, fun x hx => hNW hx, fun x hx => hloc (γ x) hx⟩

private theorem LocGerm.glue {Y₁ Y₂ : ∀ x : unitInterval,
    ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (γ x))} {q : unitInterval}
    (h₁ : LocGerm F γ Y₁ q) (h₂ : LocGerm F γ Y₂ q) (h : Y₁ q = Y₂ q) :
    LocGerm F γ (fun x => if x ≤ q then Y₁ x else Y₂ x) q := by
  classical
  obtain ⟨W₁, r₁, N₁, hN₁, hNW₁, hloc₁⟩ := h₁
  obtain ⟨W₂, r₂, N₂, hN₂, hNW₂, hloc₂⟩ := h₂
  let P := (TopCat.Sheaf.forget _ Z).obj F
  have e := (hloc₁ q hN₁).symm.trans (h.trans (hloc₂ q hN₂))
  obtain ⟨W, hW, iU, iV, he⟩ := P.germ_eq (γ q) (hNW₁ hN₁) (hNW₂ hN₂) r₁ r₂ e
  refine ⟨W, P.map iU.op r₁, N₁ ⊓ N₂ ⊓ (Opens.map γ).obj W, ⟨⟨hN₁, hN₂⟩, hW⟩,
    fun x hx => hx.2, fun x hx => ?_⟩
  beta_reduce
  split_ifs
  · rw [hloc₁ x hx.1.1]
    exact (TopCat.Presheaf.germ_res_apply P iU (γ x) hx.2 r₁).symm
  · rw [hloc₂ x hx.1.2, he]
    exact (TopCat.Presheaf.germ_res_apply P iV (γ x) hx.2 r₂).symm

private theorem reach_zero {V : Opens Z} (hV : GermExtendable F V) (h0 : γ 0 ∈ V) :
    Reach F γ 0 := by
  intro y
  obtain ⟨Zf, hZf, hloc⟩ := hV (γ 0) h0 y
  refine ⟨fun x => Zf (γ x), hZf, fun x₀ hx₀ => ?_⟩
  obtain rfl : x₀ = 0 := le_antisymm hx₀ (unitInterval.nonneg x₀)
  exact LocGerm.of_germExtendable hloc h0

private theorem Reach.propagate {q q' : unitInterval} (hq : Reach F γ q) (hqq' : q ≤ q')
    {V : Opens Z}
    (hV : GermExtendable F V) (hγ : ∀ x, q ≤ x → x ≤ q' → γ x ∈ V) : Reach F γ q' := by
  classical
  intro y'
  obtain ⟨Zf, hZf, hloc⟩ := hV (γ q') (hγ q' hqq' le_rfl) y'
  obtain ⟨Y₁, hY₁, hl₁⟩ := hq (Zf (γ q))
  refine ⟨fun x => if x ≤ q then Y₁ x else Zf (γ x), ?_, fun x₀ hx₀ => ?_⟩
  · beta_reduce
    split_ifs with h
    · obtain rfl : q' = q := le_antisymm h hqq'
      exact hY₁.trans hZf
    · exact hZf
  · rcases lt_trichotomy x₀ q with h | rfl | h
    · refine (hl₁ x₀ h.le).congr {x | x < q} (isOpen_lt continuous_id continuous_const) h
        fun x hx => if_pos (le_of_lt hx)
    · exact LocGerm.glue (hl₁ x₀ le_rfl) (LocGerm.of_germExtendable hloc (hγ x₀ le_rfl hqq'))
        hY₁
    · refine (LocGerm.of_germExtendable hloc (hγ x₀ h.le hx₀)).congr {x | q < x}
        (isOpen_lt continuous_const continuous_id) h ?_
      intro x hx
      simp only [if_neg (not_le.2 (show q < x from hx))]

private theorem reach_one (hF : IsLocalSystem F) : Reach F γ 1 := by
  choose V hV hext using fun z => exists_germExtendable F hF z
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (s := Set.univ)
    (c := fun z => γ ⁻¹' (V z : Set Z)) isCompact_univ
    (fun z => (V z).isOpen.preimage γ.hom.continuous)
    (fun x _ => Set.mem_iUnion.2 ⟨γ x, hV (γ x)⟩)
  let q : ℕ → unitInterval := fun n => ⟨min 1 (n * (δ / 2)), le_min zero_le_one
    (by positivity), min_le_left _ _⟩
  have hq : ∀ n, Reach F γ (q n) := by
    intro n
    induction n with
    | zero =>
      obtain ⟨z, hz⟩ := hball 0 trivial
      have h0 : q 0 = 0 := by ext; simp [q]
      rw [h0]
      exact reach_zero (hext z) (hz (Metric.mem_ball_self hδ))
    | succ n ih =>
      obtain ⟨z, hz⟩ := hball (q n) trivial
      refine ih.propagate ?_ (hext z) fun x hx hx' => hz ?_
      · change min 1 (n * (δ / 2)) ≤ min 1 ((n + 1 : ℕ) * (δ / 2))
        gcongr
        exact_mod_cast Nat.le_succ n
      · rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_lt]
        have h1 : ((x : unitInterval) : ℝ) ≤ min 1 ((n + 1 : ℕ) * (δ / 2)) := hx'
        have h2 : min 1 (n * (δ / 2)) ≤ ((x : unitInterval) : ℝ) := hx
        have h3 : min 1 ((n + 1 : ℕ) * (δ / 2)) ≤ min 1 (n * (δ / 2)) + δ / 2 := by
          push_cast
          rcases le_total 1 (n * (δ / 2)) with h | h
          · rw [min_eq_left h, min_eq_left (by nlinarith)]
            linarith
          · rw [min_eq_right h]
            exact (min_le_right _ _).trans (by nlinarith)
        change -δ < (x : ℝ) - min 1 (n * (δ / 2)) ∧ (x : ℝ) - min 1 (n * (δ / 2)) < δ
        constructor <;> linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / δ)
  have : q n = 1 := by
    ext
    change min 1 (n * (δ / 2)) = 1
    refine min_eq_left ?_
    rw [div_lt_iff₀ hδ] at hn
    nlinarith
  rw [← this]
  exact hq n

end Interval

end Transport

section TransportExistence

variable {Z : TopCat.{0}} (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Z)

/-- **Germs at the start of a path extend.** Every germ of a local system at the start of a
path `γ` is the germ at `0` of a global section of `γ^* F`. -/
private theorem exists_section_germ_zero (hF : IsLocalSystem F) {t t' : Z} (γ : Path t t')
    (y₀ : ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk
      ((TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap) 0))) :
    ∃ s : ToType (((TopCat.Sheaf.forget _ _).obj
        (Pb (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap) F)).obj (op ⊤)),
      (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
          F 0).hom y₀ =
        ((TopCat.Sheaf.forget _ _).obj
          (Pb (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap) F)).germ
            ⊤ 0 trivial s := by
  let Γ := TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap
  let PF := (TopCat.Sheaf.forget _ Z).obj F
  let Γs := TopCat.ofHom (X := TopCat.of unitInterval) γ.symm.toContinuousMap
  have hs1 : Γ 0 = Γs 1 := by
    change γ 0 = γ (unitInterval.symm 1)
    rw [unitInterval.symm_one]
  obtain ⟨Y', hY'1, hloc'⟩ := reach_one (F := F) (γ := Γs) hF
    ((PF.stalkCongr (.of_eq hs1)).hom.hom y₀)
  obtain ⟨s', hs'⟩ := exists_section_of_local Γs F Y' (fun x₀ => hloc' x₀
    (unitInterval.le_one x₀))
  obtain ⟨s, hs⟩ := exists_section_reparam F Γs Γ
    ⟨unitInterval.symm, unitInterval.continuous_symm⟩ (fun x => by
    change γ (unitInterval.symm (unitInterval.symm x)) = γ x
    rw [unitInterval.symm_symm]) s'
  refine ⟨s, ?_⟩
  have := hs 0 1 unitInterval.symm_zero (Y' 1) (hs' 1).symm
  have hback : ∀ {a b : Z} (e : Inseparable a b) (e' : Inseparable b a) y,
      (PF.stalkCongr e').hom.hom ((PF.stalkCongr e).hom.hom y) = y :=
    fun e _ y => (PF.stalkCongr e).hom_inv_id_apply y
  rwa [hY'1, hback] at this

end TransportExistence

/-! ### Compactly supported cohomology through injective resolutions -/

section CompactSupport

/-- `H^q_c(X, F) ≅ H^q(Γ_c(X, J^•))` for an injective resolution `J^•` of `F`, the resolution
being read as a `ℤ`-indexed complex. -/
private noncomputable def compactSupportCohomologyIso {X : TopCat.{0}}
    (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X) (J : InjectiveResolution F) (q : ℤ) :
    compactSupportCohomology ℚ q F ≅
      (((compactSupportSectionsFunctor ℚ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J.cochainComplex).homology q :=
  (DerivedCategory.homologyFunctor _ q).mapIso (J.toRightDerivedIso _).symm ≪≫
    (DerivedCategory.homologyFunctorFactors _ q).app _

/-- `H^n_c(X, F)` is the `n`-th right derived functor of `Γ_c`, in the sense of injective
resolutions in the abelian category of sheaves. -/
private noncomputable def compactSupportCohomologyIsoRightDerived {X : TopCat.{0}}
    (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X) (n : ℕ) :
    compactSupportCohomology ℚ n F ≅ ((compactSupportSectionsFunctor ℚ).rightDerived n).obj F :=
  compactSupportCohomologyIso F (injectiveResolution F) n ≪≫
    HomologicalComplex.homologyMapIso
      (Stacks.DerivedIndexing.mapExtendIso (compactSupportSectionsFunctor ℚ)
        ComplexShape.embeddingUpNat (injectiveResolution F).cocomplex).symm (n : ℤ) ≪≫
    HomologicalComplex.extendHomologyIso _ _ rfl ≪≫
    ((injectiveResolution F).isoRightDerivedObj _ n).symm

end CompactSupport

/-! ### Morphisms of restricted sheaves described by germs -/

section RestrictGerms

variable {X : TopCat.{0}}

/-- Restriction `F ↦ F|_V` of sheaves to an open `V`. -/
private abbrev resV (V : Opens X) :
    TopCat.Sheaf (ModuleCat.{0} ℚ) X ⥤ TopCat.Sheaf (ModuleCat.{0} ℚ) ((Opens.toTopCat X).obj V) :=
  haveI := V.isOpenEmbedding.functor_isContinuous
  V.isOpenEmbedding.functor.sheafPushforwardContinuous _ _ _

/-- Extension by zero `j_!` along the inclusion of an open `V`. -/
private abbrev extV (V : Opens X) :
    TopCat.Sheaf (ModuleCat.{0} ℚ) ((Opens.toTopCat X).obj V) ⥤ TopCat.Sheaf (ModuleCat.{0} ℚ) X :=
  haveI := V.isOpenEmbedding.functor_isContinuous
  V.isOpenEmbedding.functor.sheafPullback _ _ _

/-- The adjunction `j_! ⊣ j^*`. -/
private abbrev adjV (V : Opens X) : extV V ⊣ resV V :=
  haveI := V.isOpenEmbedding.functor_isContinuous
  V.isOpenEmbedding.functor.sheafAdjunctionContinuous _ _ _

/-- The image in `X` of an open subset of the open `V`. -/
private abbrev img (V : Opens X) (W : Opens ((Opens.toTopCat X).obj V)) : Opens X :=
  V.isOpenEmbedding.functor.obj W

private theorem mem_of_mem_img {V : Opens X} {W : Opens ((Opens.toTopCat X).obj V)} {x : X}
    (hx : x ∈ img V W) : x ∈ V := by
  obtain ⟨z, -, rfl⟩ := hx
  exact z.2

variable (V : Opens X) {A B : TopCat.Sheaf (ModuleCat.{0} ℚ) X}

/-- The morphism `A|_V ⟶ B|_V` with prescribed action on germs. -/
private def homOfGerms
    (f : ∀ x : X, ((TopCat.Sheaf.forget _ X).obj A).stalk x ⟶
      ((TopCat.Sheaf.forget _ X).obj B).stalk x)
    (hf : ∀ (W : Opens ((Opens.toTopCat X).obj V))
      (s : ToType (((TopCat.Sheaf.forget _ X).obj A).obj (op (img V W)))),
      ∃ t : ToType (((TopCat.Sheaf.forget _ X).obj B).obj (op (img V W))), ∀ x (hx : x ∈ img V W),
        ((TopCat.Sheaf.forget _ X).obj B).germ _ x hx t =
          (f x).hom (((TopCat.Sheaf.forget _ X).obj A).germ _ x hx s)) :
    (resV V).obj A ⟶ (resV V).obj B :=
  (TopCat.Sheaf.forget _ _).preimage
    { app := fun W => ModuleCat.ofHom
        { toFun := fun (s : ToType (((TopCat.Sheaf.forget _ X).obj A).obj
              (op (img V W.unop)))) => (hf W.unop s).choose
          map_add' := fun (s s' : ToType (((TopCat.Sheaf.forget _ X).obj A).obj
              (op (img V W.unop)))) => by
            refine TopCat.Presheaf.section_ext B _ _ _ fun x hx => ?_
            have e1 := (hf W.unop (s + s')).choose_spec x hx
            have e2 := (hf W.unop s).choose_spec x hx
            have e3 := (hf W.unop s').choose_spec x hx
            refine e1.trans ?_
            change _ = ((TopCat.Sheaf.forget _ X).obj B).germ _ x hx
              ((hf W.unop s).choose + (hf W.unop s').choose)
            simp only [map_add, e2, e3]
          map_smul' := fun c (s : ToType (((TopCat.Sheaf.forget _ X).obj A).obj
              (op (img V W.unop)))) => by
            refine TopCat.Presheaf.section_ext B _ _ _ fun x hx => ?_
            have e1 := (hf W.unop (c • s)).choose_spec x hx
            have e2 := (hf W.unop s).choose_spec x hx
            refine e1.trans ?_
            change _ = ((TopCat.Sheaf.forget _ X).obj B).germ _ x hx (c • (hf W.unop s).choose)
            simp only [map_smul, e2] }
      naturality := fun W₁ W₂ i => by
        ext s
        refine TopCat.Presheaf.section_ext B _ _ _ fun x hx => ?_
        change ((TopCat.Sheaf.forget _ X).obj B).germ _ x hx (hf W₂.unop
            (((TopCat.Sheaf.forget _ X).obj A).map (V.isOpenEmbedding.functor.map i.unop).op
              s)).choose =
          ((TopCat.Sheaf.forget _ X).obj B).germ _ x hx
            (((TopCat.Sheaf.forget _ X).obj B).map (V.isOpenEmbedding.functor.map i.unop).op
              (hf W₁.unop s).choose)
        refine ((hf W₂.unop _).choose_spec x hx).trans
          (Eq.trans ?_ (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm)
        exact (congrArg (f x).hom (TopCat.Presheaf.germ_res_apply _ _ _ _ _)).trans
          ((hf W₁.unop s).choose_spec _ _).symm }

private theorem germ_homOfGerms (f) (hf)
    (W : Opens ((Opens.toTopCat X).obj V))
    (s : ToType (((TopCat.Sheaf.forget _ X).obj A).obj (op (img V W)))) (x : X) (hx : x ∈ img V W) :
    ((TopCat.Sheaf.forget _ X).obj B).germ (img V W) x hx
        ((((TopCat.Sheaf.forget _ _).map (homOfGerms V f hf)).app (op W)).hom s) =
      (f x).hom (((TopCat.Sheaf.forget _ X).obj A).germ _ x hx s) := by
  rw [homOfGerms, Functor.map_preimage]
  exact (hf W s).choose_spec x hx

private theorem resV_comp_app {C : TopCat.Sheaf (ModuleCat.{0} ℚ) X}
    (α : (resV V).obj A ⟶ (resV V).obj B) (β : (resV V).obj B ⟶ (resV V).obj C)
    (W : Opens ((Opens.toTopCat X).obj V))
    (s : ToType (((TopCat.Sheaf.forget _ X).obj A).obj (op (img V W)))) :
    (((TopCat.Sheaf.forget _ _).map (α ≫ β)).app (op W)).hom s =
      (((TopCat.Sheaf.forget _ _).map β).app (op W)).hom
        ((((TopCat.Sheaf.forget _ _).map α).app (op W)).hom s) :=
  rfl

private theorem resV_id_app (W : Opens ((Opens.toTopCat X).obj V))
    (s : ToType (((TopCat.Sheaf.forget _ X).obj A).obj (op (img V W)))) :
    (((TopCat.Sheaf.forget _ _).map (𝟙 ((resV V).obj A))).app (op W)).hom s = s :=
  rfl

/-- Morphisms `A|_V ⟶ B|_V` with the same action on germs agree. -/
private theorem resV_hom_ext {α β : (resV V).obj A ⟶ (resV V).obj B}
    (h : ∀ (W : Opens ((Opens.toTopCat X).obj V))
      (s : ToType (((TopCat.Sheaf.forget _ X).obj A).obj (op (img V W)))) (x : X)
      (hx : x ∈ img V W),
      ((TopCat.Sheaf.forget _ X).obj B).germ (img V W) x hx
          ((((TopCat.Sheaf.forget _ _).map α).app (op W)).hom s) =
        ((TopCat.Sheaf.forget _ X).obj B).germ (img V W) x hx
          ((((TopCat.Sheaf.forget _ _).map β).app (op W)).hom s)) : α = β := by
  apply (TopCat.Sheaf.forget _ _).map_injective
  ext W s
  exact TopCat.Presheaf.section_ext B _ _ _ fun x hx => h W s x hx

/-- If a global morphism `b` restricts over `V` to `a|_V ≫ θ`, then on stalks at points of `V` it
is `a` followed by the germ action of `θ`. -/
private theorem stalk_map_eq_of_resV_map_eq {K : TopCat.Sheaf (ModuleCat.{0} ℚ) X} (a : K ⟶ A)
    (b : K ⟶ B) {θ : (resV V).obj A ⟶ (resV V).obj B}
    (f : ∀ x : X, ((TopCat.Sheaf.forget _ X).obj A).stalk x ⟶
      ((TopCat.Sheaf.forget _ X).obj B).stalk x)
    (hθ : ∀ (W : Opens ((Opens.toTopCat X).obj V))
      (s : ToType (((TopCat.Sheaf.forget _ X).obj A).obj (op (img V W)))) (x : X)
      (hx : x ∈ img V W),
      ((TopCat.Sheaf.forget _ X).obj B).germ (img V W) x hx
          ((((TopCat.Sheaf.forget _ _).map θ).app (op W)).hom s) =
        (f x).hom (((TopCat.Sheaf.forget _ X).obj A).germ _ x hx s))
    (h : (resV V).map b = (resV V).map a ≫ θ) (x : X) (hx : x ∈ V)
    (z : ToType (((TopCat.Sheaf.forget _ X).obj K).stalk x)) :
    ((TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ X).map b)).hom z =
      (f x).hom (((TopCat.Presheaf.stalkFunctor _ x).map
        ((TopCat.Sheaf.forget _ X).map a)).hom z) := by
  obtain ⟨O, hxO, u, rfl⟩ := ((TopCat.Sheaf.forget _ X).obj K).exists_germ_eq z
  let W : Opens ((Opens.toTopCat X).obj V) := (Opens.map V.inclusion').obj O
  have hle : img V W ≤ O := by
    rintro _ ⟨y, hy, rfl⟩
    exact hy
  have hxW : x ∈ img V W := ⟨⟨x, hx⟩, hxO, rfl⟩
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hle) x hxW u,
    TopCat.Presheaf.stalkFunctor_map_germ_apply, TopCat.Presheaf.stalkFunctor_map_germ_apply]
  have h' := congrArg (fun φ : (resV V).obj K ⟶ (resV V).obj B =>
    (((TopCat.Sheaf.forget _ _).map φ).app (op W)).hom
    (((TopCat.Sheaf.forget _ X).obj K).map (homOfLE hle).op u)) h
  simp only [Functor.map_comp, NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at h'
  exact (congrArg _ h').trans (hθ W _ x hxW)

/-- If the unit of `j_{V!} ⊣ j_V^*` is invertible, then the counit `j_{V!} j_V^* K ⟶ K` becomes
invertible on restriction to any open `V' ≤ V`. -/
private theorem isIso_resV_map_counit {V' : Opens X} (hV : V' ≤ V)
    (hη : ∀ G, IsIso ((adjV V).unit.app G)) (K : TopCat.Sheaf (ModuleCat.{0} ℚ) X) :
    IsIso ((resV V').map ((adjV V).counit.app K)) := by
  have h1 : IsIso ((resV V).map ((adjV V).counit.app K)) := by
    have e := (adjV V).right_triangle_components K
    haveI := hη ((resV V).obj K)
    rw [IsIso.eq_inv_of_hom_inv_id e]
    infer_instance
  have h2 : ∀ O : Opens X, O ≤ V →
      IsIso (((TopCat.Sheaf.forget _ X).map ((adjV V).counit.app K)).app (op O)) := by
    intro O hO
    let W : Opens ((Opens.toTopCat X).obj V) := (Opens.map V.inclusion').obj O
    have hW : img V W = O := by
      ext y
      refine ⟨?_, fun hy => ⟨⟨y, hO hy⟩, hy, rfl⟩⟩
      rintro ⟨z, hz, rfl⟩
      exact hz
    have : IsIso (((TopCat.Sheaf.forget _ _).map ((resV V).map
        ((adjV V).counit.app K))).app (op W)) := inferInstance
    rw [← hW]
    exact this
  haveI : IsIso ((TopCat.Sheaf.forget _ _).map ((resV V').map ((adjV V).counit.app K))) := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun W => ?_
    exact h2 (img V' W.unop) fun y hy => hV (mem_of_mem_img hy)
  exact isIso_of_reflects_iso _ (TopCat.Sheaf.forget _ _)

/-- Over `V`, the morphism `j_{V!}θ` followed by the counit is the counit followed by `θ`. -/
private theorem resV_map_extV_map_comp_counit (hη : ∀ G, IsIso ((adjV V).unit.app G))
    (θ : (resV V).obj A ⟶ (resV V).obj B) :
    (resV V).map ((extV V).map θ ≫ (adjV V).counit.app B) =
      (resV V).map ((adjV V).counit.app A) ≫ θ := by
  haveI := hη ((resV V).obj A)
  haveI : Epi ((adjV V).unit.app ((resV V).obj A)) := IsIso.epi_of_iso _
  rw [← cancel_epi ((adjV V).unit.app ((resV V).obj A)), Functor.map_comp]
  have h1 := (adjV V).unit.naturality θ
  simp only [Functor.id_map, Functor.comp_map] at h1
  rw [← Category.assoc, ← h1, Category.assoc, (adjV V).right_triangle_components,
    ← Category.assoc, (adjV V).right_triangle_components]
  simp

/-- **Extension maps commute with local isomorphisms.** For opens `V' ≤ V`, maps
`m : j_{V'!} j_{V'}^* F ⟶ j_{V!} j_V^* F` over the counits, and `θ : A|_V ⟶ B|_V` whose
restriction to `V'` is `β`, the square `m_A ≫ j_{V!} θ = j_{V'!} β ≫ m_B` commutes. -/
private theorem comp_extV_map_eq {V' : Opens X} (hV : V' ≤ V)
    (hη : ∀ G, IsIso ((adjV V).unit.app G))
    (θ : (resV V).obj A ⟶ (resV V).obj B) (β : (resV V').obj A ⟶ (resV V').obj B)
    (mA : (extV V').obj ((resV V').obj A) ⟶ (extV V).obj ((resV V).obj A))
    (hmA : mA ≫ (adjV V).counit.app A = (adjV V').counit.app A)
    (mB : (extV V').obj ((resV V').obj B) ⟶ (extV V).obj ((resV V).obj B))
    (hmB : mB ≫ (adjV V).counit.app B = (adjV V').counit.app B)
    (hβ : (resV V').map ((extV V).map θ ≫ (adjV V).counit.app B) =
      (resV V').map ((adjV V).counit.app A) ≫ β) :
    mA ≫ (extV V).map θ = (extV V').map β ≫ mB := by
  apply ((adjV V').homEquiv _ _).injective
  haveI := isIso_resV_map_counit V hV hη B
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    ← cancel_mono ((resV V').map ((adjV V).counit.app B))]
  have hL : ((adjV V').unit.app ((resV V').obj A) ≫ (resV V').map (mA ≫ (extV V).map θ)) ≫
      (resV V').map ((adjV V).counit.app B) = β := by
    rw [Functor.map_comp, Category.assoc, Category.assoc, ← Functor.map_comp (resV V')
      ((extV V).map θ), hβ, ← Category.assoc ((resV V').map mA), ← Functor.map_comp, hmA,
      ← Category.assoc, (adjV V').right_triangle_components]
    simp
  have hR : ((adjV V').unit.app ((resV V').obj A) ≫ (resV V').map ((extV V').map β ≫ mB)) ≫
      (resV V').map ((adjV V).counit.app B) = β := by
    have h1 := (adjV V').unit.naturality β
    simp only [Functor.id_map, Functor.comp_map] at h1
    rw [Functor.map_comp, Category.assoc, Category.assoc, ← Functor.map_comp (resV V') mB, hmB,
      ← Category.assoc, ← h1, Category.assoc, (adjV V').right_triangle_components]
    simp
  rw [hL, hR]

/-- `comp_extV_map_eq`, with the compatibility of `θ` and `β` read off their actions on germs. -/
private theorem comp_extV_map_eq_of_germs {V' : Opens X} (hV : V' ≤ V)
    (hη : ∀ G, IsIso ((adjV V).unit.app G))
    (θ : (resV V).obj A ⟶ (resV V).obj B) (β : (resV V').obj A ⟶ (resV V').obj B)
    (f : ∀ x : X, ((TopCat.Sheaf.forget _ X).obj A).stalk x ⟶
      ((TopCat.Sheaf.forget _ X).obj B).stalk x)
    (hθ : ∀ (W : Opens ((Opens.toTopCat X).obj V))
      (s : ToType (((TopCat.Sheaf.forget _ X).obj A).obj (op (img V W)))) (x : X)
      (hx : x ∈ img V W),
      ((TopCat.Sheaf.forget _ X).obj B).germ (img V W) x hx
          ((((TopCat.Sheaf.forget _ _).map θ).app (op W)).hom s) =
        (f x).hom (((TopCat.Sheaf.forget _ X).obj A).germ _ x hx s))
    (hβ : ∀ (W : Opens ((Opens.toTopCat X).obj V'))
      (s : ToType (((TopCat.Sheaf.forget _ X).obj A).obj (op (img V' W)))) (x : X)
      (hx : x ∈ img V' W),
      ((TopCat.Sheaf.forget _ X).obj B).germ (img V' W) x hx
          ((((TopCat.Sheaf.forget _ _).map β).app (op W)).hom s) =
        (f x).hom (((TopCat.Sheaf.forget _ X).obj A).germ _ x hx s))
    (mA : (extV V').obj ((resV V').obj A) ⟶ (extV V).obj ((resV V).obj A))
    (hmA : mA ≫ (adjV V).counit.app A = (adjV V').counit.app A)
    (mB : (extV V').obj ((resV V').obj B) ⟶ (extV V).obj ((resV V).obj B))
    (hmB : mB ≫ (adjV V).counit.app B = (adjV V').counit.app B) :
    mA ≫ (extV V).map θ = (extV V').map β ≫ mB := by
  refine comp_extV_map_eq V hV hη θ β mA hmA mB hmB ?_
  refine resV_hom_ext V' fun W s x hx => ?_
  have hxV : x ∈ V := hV (mem_of_mem_img hx)
  change ((TopCat.Sheaf.forget _ X).obj B).germ (img V' W) x hx
      ((((TopCat.Sheaf.forget _ X).map ((extV V).map θ ≫ (adjV V).counit.app B)).app
        (op (img V' W))).hom s) =
    ((TopCat.Sheaf.forget _ X).obj B).germ (img V' W) x hx
      ((((TopCat.Sheaf.forget _ _).map β).app (op W)).hom
        ((((TopCat.Sheaf.forget _ X).map ((adjV V).counit.app A)).app (op (img V' W))).hom s))
  rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply,
    stalk_map_eq_of_resV_map_eq V _ _ f hθ (resV_map_extV_map_comp_counit V hη θ) x hxV, hβ,
    TopCat.Presheaf.stalkFunctor_map_germ_apply]

end RestrictGerms

/-! ### Parallel transport and trivializations over discs -/

section Discs

variable {M : TopCat.{0}} {𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) M}

/-- An open subset homeomorphic to `ℝ²` is simply connected. -/
private theorem simplyConnectedSpace_of_homeomorph {V : Type*} [TopologicalSpace V]
    (e : V ≃ₜ EuclideanSpace ℝ (Fin 2)) : SimplyConnectedSpace V := by
  haveI : ContractibleSpace V := e.contractibleSpace
  exact SimplyConnectedSpace.ofContractible V

variable (𝓛) in
/-- Parallel transport in `𝓛`: isomorphisms of stalks along homotopy classes of paths,
characterised by the end germs of sections of inverse images along paths, compatible with
concatenation, and trivialising `𝓛` over simply connected opens. -/
private structure Transport where
  /-- The transport along a homotopy class of paths. -/
  T : ∀ {x y : M}, Path.Homotopic.Quotient x y →
    (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x ≅ ((TopCat.Sheaf.forget _ M).obj 𝓛).stalk y)
  germ : ∀ {x y : M} (γ : Path x y)
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
          (cast (by simp) ((T (Path.Homotopic.Quotient.mk γ)).hom v)) =
        ((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
          (TopCat.ofHom (γ : C(unitInterval, M)))).obj 𝓛)).germ ⊤ (1 : unitInterval)
            (Opens.mem_top _) s
  trans : ∀ {x y z : M} (γ : Path.Homotopic.Quotient x y) (δ : Path.Homotopic.Quotient y z),
    T (γ.trans δ) = T γ ≪≫ T δ
  triv : ∀ (V : Opens M) [SimplyConnectedSpace V] (x : M) (hx : x ∈ V),
    ∃ φ : (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) V.inclusion').obj 𝓛 ≅
        (constantSheaf (Opens.grothendieckTopology (TopCat.of V)) (ModuleCat.{0} ℚ)).obj
          (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x),
      ∀ (y : V) (γ : Path (⟨x, hx⟩ : V) y) (v : ((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x),
        (TopCat.Presheaf.stalkFunctor _ y).map ((TopCat.Sheaf.forget _ _).map φ.hom)
            (stalkToPullbackStalk V.inclusion' 𝓛 y
              ((T (Path.Homotopic.Quotient.mk (γ.map continuous_subtype_val))).hom v)) =
          ((TopCat.Sheaf.forget _ _).obj ((constantSheaf
              (Opens.grothendieckTopology (TopCat.of V)) (ModuleCat.{0} ℚ)).obj
                (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x))).germ ⊤ y (Opens.mem_top _)
            ((toSheafify (Opens.grothendieckTopology (TopCat.of V))
              ((Functor.const _).obj (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x))).app
                (op ⊤) v)

/-- The parallel transport of a local system on a locally path-connected space. -/
private noncomputable def Transport.ofIsLocalSystem [LocallyPathConnectedSpace M]
    (h𝓛 : IsLocalSystem 𝓛) : Transport 𝓛 :=
  ⟨h𝓛.parallelTransport, h𝓛.parallelTransport_germ, h𝓛.parallelTransport_trans,
    h𝓛.exists_iso_constantSheaf_parallelTransport⟩

namespace Transport

variable (D : Transport 𝓛)

private theorem T_refl (x : M) : D.T (Path.Homotopic.Quotient.refl x) = Iso.refl _ := by
  have h := D.trans (Path.Homotopic.Quotient.refl x) (Path.Homotopic.Quotient.refl x)
  rw [Path.Homotopic.Quotient.trans_refl] at h
  ext : 1
  have h' := congrArg Iso.hom h
  rw [Iso.trans_hom] at h'
  rw [← cancel_epi (D.T (Path.Homotopic.Quotient.refl x)).hom, ← h']
  simp

private theorem T_trans_symm {x y : M} (γ : Path.Homotopic.Quotient x y) :
    D.T γ ≪≫ D.T γ.symm = Iso.refl _ := by
  rw [← D.trans, Path.Homotopic.Quotient.trans_symm, T_refl]

private theorem T_hom_T_hom {a b c : M} (c₁ : Path.Homotopic.Quotient a b)
    (c₂ : Path.Homotopic.Quotient b c)
    (u : ToType (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk a)) :
    (D.T c₂).hom.hom ((D.T c₁).hom.hom u) = (D.T (c₁.trans c₂)).hom.hom u := by
  rw [D.trans]
  rfl

/-- Transport inside an open disc `V`, along any path of `V`. -/
private noncomputable def P (V : Opens M) (hV : Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2)))
    (a b : V) : ((TopCat.Sheaf.forget _ M).obj 𝓛).stalk a.1 ≅
      ((TopCat.Sheaf.forget _ M).obj 𝓛).stalk b.1 :=
  haveI := simplyConnectedSpace_of_homeomorph hV.some
  D.T (Path.Homotopic.Quotient.mk ((PathConnectedSpace.somePath a b).map continuous_subtype_val))

private theorem T_mk_map_eq (V : Opens M) (hV : Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2)))
    {a b : V} (γ : Path a b) :
    D.T (Path.Homotopic.Quotient.mk (γ.map continuous_subtype_val)) = D.P V hV a b := by
  haveI := simplyConnectedSpace_of_homeomorph hV.some
  exact congrArg D.T (Path.Homotopic.Quotient.eq.2
    ((SimplyConnectedSpace.paths_homotopic γ _).map ⟨Subtype.val, continuous_subtype_val⟩))

private theorem P_trans (V : Opens M) (hV : Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2)))
    (a b c : V) : D.P V hV a b ≪≫ D.P V hV b c = D.P V hV a c := by
  haveI := simplyConnectedSpace_of_homeomorph hV.some
  rw [← D.T_mk_map_eq V hV ((PathConnectedSpace.somePath a b).trans
    (PathConnectedSpace.somePath b c)), Path.map_trans, Path.Homotopic.Quotient.mk_trans,
    D.trans]
  rfl

private theorem P_self (V : Opens M) (hV : Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2))) (a : V) :
    D.P V hV a a = Iso.refl _ := by
  rw [← D.T_mk_map_eq V hV (Path.refl a)]
  exact D.T_refl a.1

private theorem P_hom_P_hom (V : Opens M) (hV : Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2)))
    (a b c : V) (v : ToType (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk a.1)) :
    (D.P V hV b c).hom.hom ((D.P V hV a b).hom.hom v) = (D.P V hV a c).hom.hom v := by
  rw [← D.P_trans V hV a b c]
  rfl

private theorem P_mono {V' V : Opens M} (h : V' ≤ V)
    (hV' : Nonempty (V' ≃ₜ EuclideanSpace ℝ (Fin 2)))
    (hV : Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2))) (a b : V') :
    D.P V' hV' a b = D.P V hV ⟨a.1, h a.2⟩ ⟨b.1, h b.2⟩ := by
  haveI := simplyConnectedSpace_of_homeomorph hV'.some
  exact D.T_mk_map_eq V hV ((PathConnectedSpace.somePath a b).map
    (f := fun z : V' => (⟨z.1, h z.2⟩ : V)) (by fun_prop))

/-- **Flatness of transport.** Transporting a fixed vector from `x` to the points of a disc `V`
gives a family of germs which is, near every point of `V`, the family of germs of a section. -/
private theorem flat (V : Opens M) (hV : Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2))) (x : V)
    (v : ToType (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x.1)) (y₀ : M) (hy₀ : y₀ ∈ V) :
    ∃ (W : Opens M) (r : ToType (((TopCat.Sheaf.forget _ M).obj 𝓛).obj (op W))) (N : Opens M)
      (_ : y₀ ∈ N) (hNW : N ≤ W) (hNV : N ≤ V), ∀ y (hy : y ∈ N),
        (D.P V hV x ⟨y, hNV hy⟩).hom.hom v =
          ((TopCat.Sheaf.forget _ M).obj 𝓛).germ W y (hNW hy) r := by
  haveI := simplyConnectedSpace_of_homeomorph hV.some
  obtain ⟨φ, hφ⟩ := D.triv V x.1 x.2
  let c := ((toSheafify (Opens.grothendieckTopology (TopCat.of V))
    ((Functor.const _).obj (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x.1))).app (op ⊤)).hom v
  let σ := (((TopCat.Sheaf.forget _ _).map φ.inv).app (op ⊤)).hom c
  have hσ : ∀ y : V, ((TopCat.Sheaf.forget _ _).obj (Pb V.inclusion' 𝓛)).germ ⊤ y trivial σ =
      (stalkToPullbackStalk V.inclusion' 𝓛 y).hom ((D.P V hV x y).hom.hom v) := by
    intro y
    have e := hφ y (PathConnectedSpace.somePath _ y) v
    have e2 := TopCat.Presheaf.stalkFunctor_map_germ_apply (⊤ : Opens (TopCat.of V)) y trivial
      ((TopCat.Sheaf.forget _ _).map φ.inv) c
    refine e2.symm.trans ?_
    erw [← e, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp,
      φ.hom_inv_id]
    erw [CategoryTheory.Functor.map_id]
    rfl
  obtain ⟨W, r, N, hN, _hNU, hNW, hloc⟩ := exists_local_germ V.inclusion' 𝓛 σ ⟨y₀, hy₀⟩ trivial
  refine ⟨W, r, img V N, ⟨⟨y₀, hy₀⟩, hN, rfl⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hNW hz
  · rintro _ ⟨z, -, rfl⟩
    exact z.2
  · rintro _ ⟨z, hz, rfl⟩
    exact (bijective_stalkToPullbackStalk _ _ z).1 (((hσ z).symm.trans (hloc z hz)))

end Transport

end Discs

/-! ### Trivializations of a local system over discs -/

section Trivialization

/-- The germ at `y` of the constant section with value `e`. -/
private noncomputable def constGerm {Y : TopCat.{0}} (E : ModuleCat.{0} ℚ) (y : Y) :
    E →ₗ[ℚ] ToType (((TopCat.Sheaf.forget _ Y).obj (cSh Y E)).stalk y) :=
  (((TopCat.Sheaf.forget _ Y).obj (cSh Y E)).germ ⊤ y (Opens.mem_top y)).hom ∘ₗ
    ((CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
      ((Functor.const (Opens Y)ᵒᵖ).obj E)).app (op ⊤)).hom

private theorem constGerm_apply {Y : TopCat.{0}} (E : ModuleCat.{0} ℚ) (y : Y) (e : E) :
    constGerm E y e =
      ((TopCat.Sheaf.forget _ Y).obj (cSh Y E)).germ ⊤ y (Opens.mem_top y) (constSection E e) :=
  rfl

private theorem constGerm_bijective {Y : TopCat.{0}} (E : ModuleCat.{0} ℚ) (y : Y) :
    Function.Bijective (constGerm E y) := by
  refine ⟨?_, fun c => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro e he
    exact eq_zero_of_germ_constSection E y he
  · exact constantSheaf_exists_constSection_germ E y c

/-- `constGerm` as a linear equivalence. -/
private noncomputable def constGermEquiv {Y : TopCat.{0}} (E : ModuleCat.{0} ℚ) (y : Y) :
    E ≃ₗ[ℚ] ToType (((TopCat.Sheaf.forget _ Y).obj (cSh Y E)).stalk y) :=
  LinearEquiv.ofBijective _ (constGerm_bijective E y)

/-- Morphisms of constant sheaves act on constant germs by their value. -/
private theorem constGerm_map {Y : TopCat.{0}} {E E' : ModuleCat.{0} ℚ} (g : E ⟶ E') (y : Y)
    (e : E) :
    ((TopCat.Presheaf.stalkFunctor _ y).map ((TopCat.Sheaf.forget _ Y).map
      ((constantSheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ)).map g))).hom
        (constGerm E y e) = constGerm E' y (g e) := by
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _).trans ?_
  rw [constGerm_apply]
  congr 1
  exact (congrArg (fun φ => (φ.app (op ⊤)).hom e) (toSheafify_naturality
    (Opens.grothendieckTopology Y) ((Functor.const (Opens Y)ᵒᵖ).map g))).symm

variable {M : TopCat.{0}} {𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) M}

namespace Transport

variable (D : Transport 𝓛) (V : Opens M) (hV : Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2))) (x : V)

open Classical in
/-- The stalk maps of the trivialization of `𝓛` over the disc `V` with fibre `𝓛_x`. -/
private noncomputable def trivGerm (y : M) :
    ((TopCat.Sheaf.forget _ M).obj 𝓛).stalk y ⟶
      ((TopCat.Sheaf.forget _ M).obj (cSh M (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x.1))).stalk
        y :=
  if hy : y ∈ V then ModuleCat.ofHom (constGerm _ y ∘ₗ (D.P V hV ⟨y, hy⟩ x).hom.hom) else 0

open Classical in
/-- The stalk maps of the inverse trivialization. -/
private noncomputable def trivGermInv (y : M) :
    ((TopCat.Sheaf.forget _ M).obj (cSh M (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x.1))).stalk
        y ⟶ ((TopCat.Sheaf.forget _ M).obj 𝓛).stalk y :=
  if hy : y ∈ V then
    ModuleCat.ofHom ((D.P V hV x ⟨y, hy⟩).hom.hom ∘ₗ (constGermEquiv _ y).symm.toLinearMap)
  else 0

private theorem trivGerm_apply (y : M) (hy : y ∈ V)
    (g : ToType (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk y)) :
    (D.trivGerm V hV x y).hom g = constGerm _ y ((D.P V hV ⟨y, hy⟩ x).hom.hom g) := by
  rw [show D.trivGerm V hV x y = ModuleCat.ofHom (constGerm _ y ∘ₗ (D.P V hV ⟨y, hy⟩ x).hom.hom)
    from dif_pos hy]
  rfl

private theorem trivGermInv_apply (y : M) (hy : y ∈ V)
    (e : ToType (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x.1)) :
    (D.trivGermInv V hV x y).hom (constGerm _ y e) = (D.P V hV x ⟨y, hy⟩).hom.hom e := by
  rw [show D.trivGermInv V hV x y = ModuleCat.ofHom ((D.P V hV x ⟨y, hy⟩).hom.hom ∘ₗ
    (constGermEquiv _ y).symm.toLinearMap) from dif_pos hy]
  change (D.P V hV x ⟨y, hy⟩).hom.hom ((constGermEquiv _ y).symm (constGermEquiv _ y e)) = _
  rw [LinearEquiv.symm_apply_apply]

private theorem exists_trivGerm (W : Opens ((Opens.toTopCat M).obj V))
    (s : ToType (((TopCat.Sheaf.forget _ M).obj 𝓛).obj (op (img V W)))) :
    ∃ t : ToType (((TopCat.Sheaf.forget _ M).obj
        (cSh M (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x.1))).obj (op (img V W))),
      ∀ y (hy : y ∈ img V W),
        ((TopCat.Sheaf.forget _ M).obj (cSh M (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x.1))).germ
            _ y hy t =
          (D.trivGerm V hV x y).hom (((TopCat.Sheaf.forget _ M).obj 𝓛).germ _ y hy s) := by
  classical
  refine (exists_section_of_locally (cSh M (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x.1))
    (img V W) (fun y => if hy : y ∈ img V W then
      (D.trivGerm V hV x y).hom (((TopCat.Sheaf.forget _ M).obj 𝓛).germ _ y hy s) else 0)
        ?_).imp fun t ht y hy => (ht y hy).trans (dif_pos hy)
  intro y₀ hy₀
  have hy₀V : y₀ ∈ V := mem_of_mem_img hy₀
  let e := (D.P V hV ⟨y₀, hy₀V⟩ x).hom.hom (((TopCat.Sheaf.forget _ M).obj 𝓛).germ _ y₀ hy₀ s)
  obtain ⟨W₁, r, N, hN, hNW, hNV, hloc⟩ := D.flat V hV x e y₀ hy₀V
  have h0 : ((TopCat.Sheaf.forget _ M).obj 𝓛).germ W₁ y₀ (hNW hN) r =
      ((TopCat.Sheaf.forget _ M).obj 𝓛).germ (img V W) y₀ hy₀ s := by
    rw [← hloc y₀ hN, P_hom_P_hom, P_self]
    rfl
  obtain ⟨N', hN', i₁, i₂, he⟩ := TopCat.Presheaf.germ_eq _ y₀ (hNW hN) hy₀ r s h0
  refine ⟨⊤, constSection _ e, N ⊓ N', ⟨hN, hN'⟩, le_top, fun y hy => i₂.le hy.2,
    fun y hy => ?_⟩
  rw [dif_pos (i₂.le hy.2), D.trivGerm_apply V hV x y (hNV hy.1)]
  have h1 : ((TopCat.Sheaf.forget _ M).obj 𝓛).germ (img V W) y (i₂.le hy.2) s =
      (D.P V hV x ⟨y, hNV hy.1⟩).hom.hom e := by
    rw [← TopCat.Presheaf.germ_res_apply _ i₂ y hy.2 s, ← he, TopCat.Presheaf.germ_res_apply,
      ← hloc y hy.1]
  rw [h1, P_hom_P_hom, P_self]
  rfl

private theorem exists_trivGermInv (W : Opens ((Opens.toTopCat M).obj V))
    (σ : ToType (((TopCat.Sheaf.forget _ M).obj
        (cSh M (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x.1))).obj (op (img V W)))) :
    ∃ t : ToType (((TopCat.Sheaf.forget _ M).obj 𝓛).obj (op (img V W))),
      ∀ y (hy : y ∈ img V W),
        ((TopCat.Sheaf.forget _ M).obj 𝓛).germ _ y hy t =
          (D.trivGermInv V hV x y).hom (((TopCat.Sheaf.forget _ M).obj
            (cSh M (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x.1))).germ _ y hy σ) := by
  classical
  refine (exists_section_of_locally 𝓛 (img V W) (fun y => if hy : y ∈ img V W then
      (D.trivGermInv V hV x y).hom (((TopCat.Sheaf.forget _ M).obj
        (cSh M (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x.1))).germ _ y hy σ) else 0)
          ?_).imp fun t ht y hy => (ht y hy).trans (dif_pos hy)
  intro y₀ hy₀
  have hy₀V : y₀ ∈ V := mem_of_mem_img hy₀
  obtain ⟨e, N, hN, hNU, hloc⟩ := constantSheaf_exists_constSection _ σ y₀ hy₀
  obtain ⟨W₁, r, N₁, hN₁, hNW, hNV, hloc₁⟩ := D.flat V hV x e y₀ hy₀V
  refine ⟨W₁, r, N ⊓ N₁, ⟨hN, hN₁⟩, fun y hy => hNW hy.2, fun y hy => hNU hy.1, fun y hy => ?_⟩
  rw [dif_pos (hNU hy.1), hloc y hy.1, ← constGerm_apply,
    D.trivGermInv_apply V hV x y (hNV hy.2), hloc₁ y hy.2]

/-- **The trivialization of a local system over a disc.** Over an open disc `V` and for `x ∈ V`,
`𝓛|_V` is isomorphic to the constant sheaf with fibre `𝓛_x`; on stalks at `y ∈ V` the
isomorphism is transport from `y` to `x` inside `V`. -/
private noncomputable def trivIso : (resV V).obj 𝓛 ≅
    (resV V).obj (cSh M (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x.1)) where
  hom := homOfGerms V (D.trivGerm V hV x) (D.exists_trivGerm V hV x)
  inv := homOfGerms V (D.trivGermInv V hV x) (D.exists_trivGermInv V hV x)
  hom_inv_id := by
    refine resV_hom_ext V fun W s y hy => ?_
    have hyV : y ∈ V := mem_of_mem_img hy
    rw [resV_comp_app, resV_id_app]
    refine (germ_homOfGerms V (D.trivGermInv V hV x) (D.exists_trivGermInv V hV x) W _ y hy).trans
      ?_
    erw [germ_homOfGerms V (D.trivGerm V hV x) (D.exists_trivGerm V hV x) W s y hy]
    rw [D.trivGerm_apply V hV x y hyV, D.trivGermInv_apply V hV x y hyV, P_hom_P_hom, P_self]
    rfl
  inv_hom_id := by
    refine resV_hom_ext V fun W σ y hy => ?_
    have hyV : y ∈ V := mem_of_mem_img hy
    rw [resV_comp_app, resV_id_app]
    refine (germ_homOfGerms V (D.trivGerm V hV x) (D.exists_trivGerm V hV x) W _ y hy).trans ?_
    erw [germ_homOfGerms V (D.trivGermInv V hV x) (D.exists_trivGermInv V hV x) W σ y hy]
    obtain ⟨e, he⟩ := (constGerm_bijective _ y).2
      (((TopCat.Sheaf.forget _ M).obj (cSh M (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x.1))).germ
        _ y hy σ)
    rw [← he, D.trivGermInv_apply V hV x y hyV, D.trivGerm_apply V hV x y hyV, P_hom_P_hom,
      P_self]
    rfl

private theorem germ_triv_hom (W : Opens ((Opens.toTopCat M).obj V))
    (s : ToType (((TopCat.Sheaf.forget _ M).obj 𝓛).obj (op (img V W)))) (y : M)
    (hy : y ∈ img V W) :
    ((TopCat.Sheaf.forget _ M).obj (cSh M (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x.1))).germ
        (img V W) y hy ((((TopCat.Sheaf.forget _ _).map (D.trivIso V hV x).hom).app (op W)).hom s) =
      (D.trivGerm V hV x y).hom (((TopCat.Sheaf.forget _ M).obj 𝓛).germ _ y hy s) :=
  germ_homOfGerms V (D.trivGerm V hV x) (D.exists_trivGerm V hV x) W s y hy

end Transport

end Trivialization

/-! ### Traces of discs and transport -/

section TraceTransport

/-- `H^q_c(Y, -)`. -/
private abbrev hcF (Y : TopCat.{0}) (q : ℤ) : TopCat.Sheaf (ModuleCat.{0} ℚ) Y ⥤ ModuleCat.{0} ℚ :=
  DerivedCategory.Plus.singleFunctor _ 0 ⋙
    (compactSupportSectionsFunctor ℚ (X := Y)).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor _ q

/-- The constant sheaf functor on finite-dimensional spaces. -/
private abbrev constFG (S : TopCat.{0}) :
    FGModuleCat.{0} ℚ ⥤ TopCat.Sheaf (ModuleCat.{0} ℚ) S :=
  (ModuleCat.isFG.{0} ℚ).ι ⋙ constantSheaf (Opens.grothendieckTopology S) (ModuleCat.{0} ℚ)

variable {S : TopCat.{0}} {L : TopCat.Sheaf (ModuleCat.{0} ℚ) S} (D : Transport L)
  (hfin : ∀ y : S, Module.Finite ℚ (((TopCat.Sheaf.forget _ S).obj L).stalk y))
  (ι : ∀ U : Opens S, hcF ((Opens.toTopCat S).obj U) 2 ≅ extV U ⋙ hcF S 2)
  (tr : ∀ V : Opens S, Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2)) →
    (constFG S ⋙ resV V ⋙ hcF _ 2 ≅ (ModuleCat.isFG.{0} ℚ).ι))

/-- The fibre `𝓛_y` as a finite-dimensional space. -/
private abbrev fibreFG (y : S) : FGModuleCat.{0} ℚ :=
  ⟨((TopCat.Sheaf.forget _ S).obj L).stalk y, hfin y⟩

/-- The trivialization of `𝓛` over a disc `V ∋ x`, with fibre `𝓛_x` read in `FGModuleCat`. -/
private noncomputable def trivFG (V : Opens S) (hV : Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2)))
    (x : V) : (resV V).obj L ≅ (resV V).obj ((constFG S).obj (fibreFG hfin x.1)) :=
  D.trivIso V hV x

/-- The stalk maps of `trivFG`. -/
private noncomputable def trivGermFG (V : Opens S)
    (hV : Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2))) (x : V) (y : S) :
    ((TopCat.Sheaf.forget _ S).obj L).stalk y ⟶
      ((TopCat.Sheaf.forget _ S).obj ((constFG S).obj (fibreFG hfin x.1))).stalk y :=
  D.trivGerm V hV x y

private theorem germ_trivFG (V : Opens S) (hV : Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2)))
    (x : V) (W : Opens ((Opens.toTopCat S).obj V))
    (s : ToType (((TopCat.Sheaf.forget _ S).obj L).obj (op (img V W)))) (y : S)
    (hy : y ∈ img V W) :
    ((TopCat.Sheaf.forget _ S).obj ((constFG S).obj (fibreFG hfin x.1))).germ (img V W) y hy
        ((((TopCat.Sheaf.forget _ _).map (trivFG D hfin V hV x).hom).app (op W)).hom s) =
      (trivGermFG D hfin V hV x y).hom (((TopCat.Sheaf.forget _ S).obj L).germ _ y hy s) :=
  D.germ_triv_hom V hV x W s y hy

private theorem trivGermFG_apply (V : Opens S) (hV : Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2)))
    (x : V) (y : S) (hy : y ∈ V) (g : ToType (((TopCat.Sheaf.forget _ S).obj L).stalk y)) :
    (trivGermFG D hfin V hV x y).hom g =
      constGerm (((TopCat.Sheaf.forget _ S).obj L).stalk x.1) y ((D.P V hV ⟨y, hy⟩ x).hom.hom g) :=
  D.trivGerm_apply V hV x y hy g

/-- The trace `H²_c(S, j_!(𝓛|_V)) ≅ 𝓛_x` of a disc `V ∋ x`. -/
private noncomputable def discTrace (V : Opens S) (hV : Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2)))
    (x : V) :
    (hcF S 2).obj ((extV V).obj ((resV V).obj L)) ≅ ((TopCat.Sheaf.forget _ S).obj L).stalk x.1 :=
  (hcF S 2).mapIso ((extV V).mapIso (trivFG D hfin V hV x)) ≪≫
    ((ι V).app ((resV V).obj ((constFG S).obj (fibreFG hfin x.1)))).symm ≪≫
      (tr V hV).app (fibreFG hfin x.1)

/-- **Extension maps between discs are parallel transport.** Under the traces of discs
`V' ≤ V`, the extension map `H²_c(V', 𝓛) ⟶ H²_c(V, 𝓛)` is transport inside `V`. -/
private theorem discTrace_comp
    (htr : ∀ (V' V : Opens S) (_ : V' ≤ V) (hV' : Nonempty (V' ≃ₜ EuclideanSpace ℝ (Fin 2)))
      (hV : Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2))) (E : FGModuleCat.{0} ℚ)
      (m : (extV V').obj ((resV V').obj ((constFG S).obj E)) ⟶
        (extV V).obj ((resV V).obj ((constFG S).obj E))),
      m ≫ (adjV V).counit.app ((constFG S).obj E) = (adjV V').counit.app ((constFG S).obj E) →
        (ι V').hom.app _ ≫ (hcF S 2).map m ≫ (ι V).inv.app _ ≫ (tr V hV).hom.app E =
          (tr V' hV').hom.app E)
    (hη : ∀ (V : Opens S) G, IsIso ((adjV V).unit.app G))
    (hm : ∀ (F : TopCat.Sheaf (ModuleCat.{0} ℚ) S) (V U : Opens S), V ≤ U →
      ∃ m : (extV V).obj ((resV V).obj F) ⟶ (extV U).obj ((resV U).obj F),
        m ≫ (adjV U).counit.app F = (adjV V).counit.app F)
    {V' V : Opens S} (h : V' ≤ V) (hV' : Nonempty (V' ≃ₜ EuclideanSpace ℝ (Fin 2)))
    (hV : Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2))) (x' : V') (x : V)
    (mL : (extV V').obj ((resV V').obj L) ⟶ (extV V).obj ((resV V).obj L))
    (hmL : mL ≫ (adjV V).counit.app L = (adjV V').counit.app L) :
    (hcF S 2).map mL ≫ (discTrace D hfin ι tr V hV x).hom =
      (discTrace D hfin ι tr V' hV' x').hom ≫ (D.P V hV ⟨x'.1, h x'.2⟩ x).hom := by
  obtain ⟨mC, hmC⟩ := hm ((constFG S).obj (fibreFG hfin x.1)) V' V h
  let g : fibreFG hfin x'.1 ⟶ fibreFG hfin x.1 :=
    ObjectProperty.homMk (D.P V hV ⟨x'.1, h x'.2⟩ x).hom
  let β : (resV V').obj L ⟶ (resV V').obj ((constFG S).obj (fibreFG hfin x.1)) :=
    (trivFG D hfin V' hV' x').hom ≫ (resV V').map ((constFG S).map g)
  have key : mL ≫ (extV V).map (trivFG D hfin V hV x).hom = (extV V').map β ≫ mC := by
    refine comp_extV_map_eq_of_germs V h (hη V) _ β (trivGermFG D hfin V hV x)
      (fun W s y hy => germ_trivFG D hfin V hV x W s y hy) ?_ mL hmL mC hmC
    intro W s y hy
    have hyV' : y ∈ V' := mem_of_mem_img hy
    rw [resV_comp_app]
    refine (TopCat.Presheaf.stalkFunctor_map_germ_apply (img V' W) y hy
      ((TopCat.Sheaf.forget _ S).map ((constFG S).map g)) _).symm.trans ?_
    rw [germ_trivFG D hfin V' hV' x' W s y hy, trivGermFG_apply D hfin V' hV' x' y hyV',
      trivGermFG_apply D hfin V hV x y (h hyV')]
    erw [constGerm_map]
    congr 1
    change (D.P V hV ⟨x'.1, h x'.2⟩ x).hom.hom ((D.P V' hV' ⟨y, hyV'⟩ x').hom.hom _) = _
    rw [D.P_mono h hV' hV, Transport.P_hom_P_hom]
  have key2 : (hcF S 2).map mC ≫ (ι V).inv.app _ ≫ (tr V hV).hom.app (fibreFG hfin x.1) =
      (ι V').inv.app _ ≫ (tr V' hV').hom.app (fibreFG hfin x.1) := by
    rw [← htr V' V h hV' hV _ mC hmC]
    simp
  have nat1 : (hcF S 2).map ((extV V').map ((resV V').map ((constFG S).map g))) ≫
      (ι V').inv.app _ = (ι V').inv.app _ ≫ (hcF _ 2).map ((resV V').map ((constFG S).map g)) :=
    (ι V').inv.naturality ((resV V').map ((constFG S).map g))
  have nat2 : (hcF _ 2).map ((resV V').map ((constFG S).map g)) ≫
      (tr V' hV').hom.app (fibreFG hfin x.1) =
        (tr V' hV').hom.app (fibreFG hfin x'.1) ≫ (ModuleCat.isFG.{0} ℚ).ι.map g :=
    (tr V' hV').hom.naturality g
  change (hcF S 2).map mL ≫ (hcF S 2).map ((extV V).map (trivFG D hfin V hV x).hom) ≫
      (ι V).inv.app ((resV V).obj ((constFG S).obj (fibreFG hfin x.1))) ≫
        (tr V hV).hom.app (fibreFG hfin x.1) =
    ((hcF S 2).map ((extV V').map (trivFG D hfin V' hV' x').hom) ≫
      (ι V').inv.app ((resV V').obj ((constFG S).obj (fibreFG hfin x'.1))) ≫
        (tr V' hV').hom.app (fibreFG hfin x'.1)) ≫ (D.P V hV ⟨x'.1, h x'.2⟩ x).hom
  rw [← Category.assoc, ← Functor.map_comp, key]
  simp only [β, Functor.map_comp, Category.assoc]
  rw [key2, ← Category.assoc ((hcF S 2).map ((extV V').map ((resV V').map ((constFG S).map g)))),
    nat1, Category.assoc, nat2]
  rfl

end TraceTransport

/-! ### The monodromy relations -/

section Relations

variable {S : TopCat.{0}} {L : TopCat.Sheaf (ModuleCat.{0} ℚ) S}

variable (L) in
/-- The relations `w - v` of the statement: `w` and `v` are the germs at `0` and `1` of a global
section of the inverse image of `L` along a loop at `t`. -/
private def relSet (t : S) : Set (((TopCat.Sheaf.forget _ _).obj L).stalk t) :=
  {u | ∃ (γ : Path t t)
      (s : ToType (((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj L).obj.obj
          (op ⊤)))
      (w v : ((TopCat.Sheaf.forget _ _).obj L).stalk t),
      (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
          L 0).hom
        ((((TopCat.Sheaf.forget _ _).obj L).stalkCongr (.of_eq γ.source.symm)).hom.hom w) =
        (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
          (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj L)).germ
            ⊤ 0 trivial).hom s ∧
      (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
          L 1).hom
        ((((TopCat.Sheaf.forget _ _).obj L).stalkCongr (.of_eq γ.target.symm)).hom.hom v) =
        (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
          (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj L)).germ
            ⊤ 1 trivial).hom s ∧
      u = w - v}

/-- Transport between stalks along an equality of points is the cast. -/
public theorem stalkCongr_eq_cast {a b : S} (h : a = b)
    (h' : ToType (((TopCat.Sheaf.forget _ S).obj L).stalk a) =
      ToType (((TopCat.Sheaf.forget _ S).obj L).stalk b))
    (v : ToType (((TopCat.Sheaf.forget _ S).obj L).stalk a)) :
    (((TopCat.Sheaf.forget _ S).obj L).stalkCongr (.of_eq h)).hom.hom v = cast h' v := by
  subst h
  change (((TopCat.Sheaf.forget _ S).obj L).stalkSpecializes (specializes_refl a)).hom v = _
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- Every vector `a - T_c a`, for `c` a loop class at `t`, is a relation. -/
private theorem sub_mem_span_relSet (hL : IsLocalSystem L) (D : Transport L) {t : S}
    (c : Path.Homotopic.Quotient t t) (a : ToType (((TopCat.Sheaf.forget _ S).obj L).stalk t)) :
    a - (D.T c).hom.hom a ∈ Submodule.span ℚ (relSet L t) := by
  induction c using Path.Homotopic.Quotient.ind with
  | _ γ =>
  refine Submodule.subset_span ?_
  obtain ⟨s, hs⟩ := exists_section_germ_zero L hL γ
    ((((TopCat.Sheaf.forget _ _).obj L).stalkCongr (.of_eq γ.source.symm)).hom.hom a)
  refine ⟨γ, s, a, (D.T (Path.Homotopic.Quotient.mk γ)).hom.hom a, hs, ?_, rfl⟩
  have h1 := D.germ γ s a (by rw [← hs, stalkCongr_eq_cast γ.source.symm (by simp)])
  rw [stalkCongr_eq_cast γ.target.symm (by simp)]
  exact h1

/-- A linear map invariant under transport along loops kills the relations. -/
private theorem span_relSet_le_ker (D : Transport L) {t : S} {N : Type*} [AddCommGroup N]
    [Module ℚ N] (Ψ : ToType (((TopCat.Sheaf.forget _ S).obj L).stalk t) →ₗ[ℚ] N)
    (hΨ : ∀ (γ : Path t t) (w : ToType (((TopCat.Sheaf.forget _ S).obj L).stalk t)),
      Ψ ((D.T (Path.Homotopic.Quotient.mk γ)).hom.hom w) = Ψ w) :
    Submodule.span ℚ (relSet L t) ≤ LinearMap.ker Ψ := by
  rw [Submodule.span_le]
  rintro _ ⟨γ, s, w, v, hw, hv, rfl⟩
  have h1 := D.germ γ s w (by rw [← hw, stalkCongr_eq_cast γ.source.symm (by simp)])
  have h2 : (D.T (Path.Homotopic.Quotient.mk γ)).hom.hom w = v := by
    rw [stalkCongr_eq_cast γ.target.symm (by simp)] at hv
    exact (cast_inj _).1 ((bijective_stalkToPullbackStalk _ L 1).1 (h1.trans hv.symm))
  change Ψ (w - v) = 0
  rw [map_sub, ← h2, hΨ, sub_self]

/-- Modulo the relations, transport to `t` does not depend on the path class. -/
private theorem mkQ_T_eq_mkQ_T (hL : IsLocalSystem L) (D : Transport L) {y t : S}
    (δ δ' : Path.Homotopic.Quotient y t)
    (u : ToType (((TopCat.Sheaf.forget _ S).obj L).stalk y)) :
    (Submodule.span ℚ (relSet L t)).mkQ ((D.T δ).hom.hom u) =
      (Submodule.span ℚ (relSet L t)).mkQ ((D.T δ').hom.hom u) := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  have h := sub_mem_span_relSet hL D (δ.symm.trans δ') ((D.T δ).hom.hom u)
  rwa [D.trans, Iso.trans_hom, ModuleCat.hom_comp, LinearMap.comp_apply,
    ← LinearMap.comp_apply (D.T δ.symm).hom.hom, ← ModuleCat.hom_comp, ← Iso.trans_hom,
    Transport.T_trans_symm, Iso.refl_hom, ModuleCat.hom_id, LinearMap.id_apply] at h

end Relations

/-! ### Assembly over a good cover -/

section Assembly

variable {S : TopCat.{0}} {L : TopCat.Sheaf (ModuleCat.{0} ℚ) S}

variable (L) in
/-- `H²_c(V, L) = H²_c(S, j_! j^* L)`. -/
private abbrev hcV (V : Opens S) : ModuleCat.{0} ℚ := (hcF S 2).obj ((extV V).obj ((resV V).obj L))

variable (L) in
/-- The sum of the extension maps `⨁_i H²_c(U_i, L) ⟶ H²_c(S, L)`. -/
private abbrev sigmaMap {κ : Type} [Fintype κ] (U : κ → Opens S) :
    (∀ i, (hcV L (U i)).carrier) →ₗ[ℚ] ((hcF S 2).obj L).carrier :=
  ∑ i : κ, ((hcF S 2).map ((adjV (U i)).counit.app L)).hom ∘ₗ
    LinearMap.proj (R := ℚ) (φ := fun i => (hcV L (U i)).carrier) i

variable (L) in
/-- The Mayer–Vietoris differential `⨁_{i<j} H²_c(U_i ∩ U_j, L) ⟶ ⨁_i H²_c(U_i, L)`. -/
private abbrev dMap {κ : Type} [Fintype κ] [LinearOrder κ] (U : κ → Opens S)
    (m₁ : ∀ p : {p : κ × κ // p.1 < p.2},
      (extV (U p.1.1 ⊓ U p.1.2)).obj ((resV (U p.1.1 ⊓ U p.1.2)).obj L) ⟶
        (extV (U p.1.1)).obj ((resV (U p.1.1)).obj L))
    (m₂ : ∀ p : {p : κ × κ // p.1 < p.2},
      (extV (U p.1.1 ⊓ U p.1.2)).obj ((resV (U p.1.1 ⊓ U p.1.2)).obj L) ⟶
        (extV (U p.1.2)).obj ((resV (U p.1.2)).obj L)) :
    (∀ p : {p : κ × κ // p.1 < p.2}, (hcV L (U p.1.1 ⊓ U p.1.2)).carrier) →ₗ[ℚ]
      (∀ i, (hcV L (U i)).carrier) :=
  ∑ p : {p : κ × κ // p.1 < p.2},
    (LinearMap.single ℚ (fun i => (hcV L (U i)).carrier) p.1.1 ∘ₗ ((hcF S 2).map (m₁ p)).hom -
      LinearMap.single ℚ (fun i => (hcV L (U i)).carrier) p.1.2 ∘ₗ ((hcF S 2).map (m₂ p)).hom) ∘ₗ
      LinearMap.proj (R := ℚ) (φ := fun p : {p : κ × κ // p.1 < p.2} =>
        (hcV L (U p.1.1 ⊓ U p.1.2)).carrier) p

private theorem dMap_single {κ : Type} [Fintype κ] [LinearOrder κ] (U : κ → Opens S)
    (m₁ : ∀ p : {p : κ × κ // p.1 < p.2},
      (extV (U p.1.1 ⊓ U p.1.2)).obj ((resV (U p.1.1 ⊓ U p.1.2)).obj L) ⟶
        (extV (U p.1.1)).obj ((resV (U p.1.1)).obj L))
    (m₂ : ∀ p : {p : κ × κ // p.1 < p.2},
      (extV (U p.1.1 ⊓ U p.1.2)).obj ((resV (U p.1.1 ⊓ U p.1.2)).obj L) ⟶
        (extV (U p.1.2)).obj ((resV (U p.1.2)).obj L))
    (p : {p : κ × κ // p.1 < p.2}) (w : (hcV L (U p.1.1 ⊓ U p.1.2)).carrier) :
    dMap L U m₁ m₂ (Pi.single p w) =
      Pi.single p.1.1 (((hcF S 2).map (m₁ p)).hom w) -
        Pi.single p.1.2 (((hcF S 2).map (m₂ p)).hom w) := by
  classical
  rw [LinearMap.sum_apply, Finset.sum_eq_single p]
  · simp
  · intro q _ hq
    simp [Pi.single_apply, hq]
  · simp

/-- **Invariance under transport along paths.** A family of maps on the stalks of a local system
which is invariant under transport inside each disc of a cover is invariant under transport along
every path: along a path the class of the transported vector is locally constant on the unit
interval, hence constant. -/
private theorem eq_apply_T_of_forall_P (hL : IsLocalSystem L) (D : Transport L) {κ : Type}
    (U : κ → Opens S) (hcov : ∀ y, ∃ i, y ∈ U i)
    (hd1 : ∀ i, (U i : Set S).Nonempty → Nonempty (U i ≃ₜ EuclideanSpace ℝ (Fin 2)))
    {N : Type*} (c : ∀ y : S, ToType (((TopCat.Sheaf.forget _ S).obj L).stalk y) → N)
    (hc : ∀ i (y z : S) (hy : y ∈ U i) (hz : z ∈ U i) v,
      c y v = c z ((D.P (U i) (hd1 i ⟨y, hy⟩) ⟨y, hy⟩ ⟨z, hz⟩).hom.hom v))
    {y z : S} (γ : Path y z) (v : ToType (((TopCat.Sheaf.forget _ S).obj L).stalk y)) :
    c y v = c z ((D.T (Path.Homotopic.Quotient.mk γ)).hom.hom v) := by
  have hcast : ∀ {a b : S} (_ : a = b)
      (h' : ToType (((TopCat.Sheaf.forget _ S).obj L).stalk a) =
        ToType (((TopCat.Sheaf.forget _ S).obj L).stalk b)) v, c b (cast h' v) = c a v := by
    rintro a _ rfl h' v
    rfl
  let Γ := TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap
  have h0 : ToType (((TopCat.Sheaf.forget _ S).obj L).stalk y) =
      ToType (((TopCat.Sheaf.forget _ S).obj L).stalk (Γ 0)) := by
    simp [Γ]
  obtain ⟨s, hs⟩ := exists_section_germ_zero L hL γ (cast h0 v)
  have hbij := fun u => bijective_stalkToPullbackStalk Γ L u
  let Y : ∀ u : unitInterval, ToType (((TopCat.Sheaf.forget _ S).obj L).stalk (Γ u)) :=
    fun u => (Equiv.ofBijective _ (hbij u)).symm
      (((TopCat.Sheaf.forget _ _).obj (Pb Γ L)).germ ⊤ u trivial s)
  have hY : ∀ u, (stalkToPullbackStalk Γ L u).hom (Y u) =
      ((TopCat.Sheaf.forget _ _).obj (Pb Γ L)).germ ⊤ u trivial s :=
    fun u => (Equiv.ofBijective _ (hbij u)).apply_symm_apply _
  have hf : IsLocallyConstant fun u => c (Γ u) (Y u) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro u₀
    obtain ⟨i, hi⟩ := hcov (Γ u₀)
    obtain ⟨W₂, r₂, N₂, hN₂, hNW₂, hNV₂, hloc₂⟩ :=
      D.flat (U i) (hd1 i ⟨_, hi⟩) ⟨Γ u₀, hi⟩ (Y u₀) (Γ u₀) hi
    obtain ⟨W, r, N, hN, _hNU, hNW, hloc⟩ := exists_local_germ Γ L s u₀ trivial
    have hYr : ∀ u (hu : u ∈ N),
        Y u = ((TopCat.Sheaf.forget _ S).obj L).germ W (Γ u) (hNW hu) r :=
      fun u hu => (hbij u).1 ((hY u).trans (hloc u hu))
    have e0 : ((TopCat.Sheaf.forget _ S).obj L).germ W₂ (Γ u₀) (hNW₂ hN₂) r₂ =
        ((TopCat.Sheaf.forget _ S).obj L).germ W (Γ u₀) (hNW hN) r := by
      rw [← hloc₂ _ hN₂, ← hYr u₀ hN, Transport.P_self]
      rfl
    obtain ⟨N₃, hN₃, i₂, i₁, he⟩ :=
      TopCat.Presheaf.germ_eq _ (Γ u₀) (hNW₂ hN₂) (hNW hN) r₂ r e0
    refine ⟨N ⊓ (Opens.map Γ).obj (N₂ ⊓ N₃), (N ⊓ (Opens.map Γ).obj (N₂ ⊓ N₃)).isOpen,
      ⟨hN, hN₂, hN₃⟩, fun u hu => ?_⟩
    have hYu : Y u = (D.P (U i) (hd1 i ⟨_, hi⟩) ⟨Γ u₀, hi⟩ ⟨Γ u, hNV₂ hu.2.1⟩).hom.hom (Y u₀) := by
      rw [hYr u hu.1, hloc₂ _ hu.2.1, ← TopCat.Presheaf.germ_res_apply _ i₁ _ hu.2.2 r, ← he,
        TopCat.Presheaf.germ_res_apply]
    simp only [hYu]
    exact (hc i _ _ hi _ _).symm
  have h01 := hf.apply_eq_of_isPreconnected isPreconnected_univ
    (Set.mem_univ (0 : unitInterval)) (Set.mem_univ 1)
  have hY0 : Y 0 = cast h0 v := (hbij 0).1 ((hY 0).trans hs.symm)
  have hY1 : Y 1 = cast (by simp [Γ]) ((D.T (Path.Homotopic.Quotient.mk γ)).hom.hom v) :=
    (hbij 1).1 ((hY 1).trans (D.germ γ s v hs).symm)
  simp only at h01
  rw [hY0, hY1] at h01
  exact (hcast γ.source.symm h0 v).symm.trans (h01.trans (hcast γ.target.symm _ _))

/-- **The coequalizer of a good cover is the space of monodromy coinvariants.** -/
private theorem nonempty_linearEquiv_of_goodCover [PathConnectedSpace S]
    (hL : IsLocalSystem L) (D : Transport L)
    (hfin : ∀ y : S, Module.Finite ℚ (((TopCat.Sheaf.forget _ S).obj L).stalk y))
    (ι : ∀ U : Opens S, hcF ((Opens.toTopCat S).obj U) 2 ≅ extV U ⋙ hcF S 2)
    (tr : ∀ V : Opens S, Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2)) →
      (constFG S ⋙ resV V ⋙ hcF _ 2 ≅ (ModuleCat.isFG.{0} ℚ).ι))
    (htr : ∀ (V' V : Opens S) (_ : V' ≤ V) (hV' : Nonempty (V' ≃ₜ EuclideanSpace ℝ (Fin 2)))
      (hV : Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin 2))) (E : FGModuleCat.{0} ℚ)
      (m : (extV V').obj ((resV V').obj ((constFG S).obj E)) ⟶
        (extV V).obj ((resV V).obj ((constFG S).obj E))),
      m ≫ (adjV V).counit.app ((constFG S).obj E) = (adjV V').counit.app ((constFG S).obj E) →
        (ι V').hom.app _ ≫ (hcF S 2).map m ≫ (ι V).inv.app _ ≫ (tr V hV).hom.app E =
          (tr V' hV').hom.app E)
    (hη : ∀ (V : Opens S) G, IsIso ((adjV V).unit.app G))
    (hm : ∀ (F : TopCat.Sheaf (ModuleCat.{0} ℚ) S) (V U : Opens S), V ≤ U →
      ∃ m : (extV V).obj ((resV V).obj F) ⟶ (extV U).obj ((resV U).obj F),
        m ≫ (adjV U).counit.app F = (adjV V).counit.app F)
    {κ : Type} [Fintype κ] [LinearOrder κ] (U : κ → Opens S) (hcov : ∀ y, ∃ i, y ∈ U i)
    (hd1 : ∀ i, (U i : Set S).Nonempty → Nonempty (U i ≃ₜ EuclideanSpace ℝ (Fin 2)))
    (hd2 : ∀ i j, ((U i ⊓ U j : Opens S) : Set S).Nonempty →
      Nonempty ((U i ⊓ U j : Opens S) ≃ₜ EuclideanSpace ℝ (Fin 2)))
    (hzero : ∀ V : Opens S, (V : Set S) = ∅ → Subsingleton (hcV L V))
    (m₁ : ∀ p : {p : κ × κ // p.1 < p.2},
      (extV (U p.1.1 ⊓ U p.1.2)).obj ((resV (U p.1.1 ⊓ U p.1.2)).obj L) ⟶
        (extV (U p.1.1)).obj ((resV (U p.1.1)).obj L))
    (m₂ : ∀ p : {p : κ × κ // p.1 < p.2},
      (extV (U p.1.1 ⊓ U p.1.2)).obj ((resV (U p.1.1 ⊓ U p.1.2)).obj L) ⟶
        (extV (U p.1.2)).obj ((resV (U p.1.2)).obj L))
    (hm₁ : ∀ p, m₁ p ≫ (adjV (U p.1.1)).counit.app L = (adjV (U p.1.1 ⊓ U p.1.2)).counit.app L)
    (hm₂ : ∀ p, m₂ p ≫ (adjV (U p.1.2)).counit.app L = (adjV (U p.1.1 ⊓ U p.1.2)).counit.app L)
    (hexact : LinearMap.range (dMap L U m₁ m₂) = LinearMap.ker (sigmaMap L U))
    (hsurj : Function.Surjective (sigmaMap L U)) (t : S) :
    Nonempty (((hcF S 2).obj L).carrier ≃ₗ[ℚ]
      (((TopCat.Sheaf.forget _ S).obj L).stalk t ⧸ Submodule.span ℚ (relSet L t))) := by
  classical
  -- traces of the members of the cover
  let pt : ∀ i, (U i : Set S).Nonempty → U i := fun i h => ⟨h.some, h.some_mem⟩
  let τ : ∀ i (h : (U i : Set S).Nonempty),
      hcV L (U i) ≅ ((TopCat.Sheaf.forget _ S).obj L).stalk (pt i h).1 :=
    fun i h => discTrace D hfin ι tr (U i) (hd1 i h) (pt i h)
  -- the class `c_i(y, v)` of a vector at a point of `U i`
  let cL : ∀ i (y : S) (hy : y ∈ U i),
      ToType (((TopCat.Sheaf.forget _ S).obj L).stalk y) →ₗ[ℚ] ((hcF S 2).obj L).carrier :=
    fun i y hy => sigmaMap L U ∘ₗ LinearMap.single ℚ (fun i => (hcV L (U i)).carrier) i ∘ₗ
      (τ i ⟨y, hy⟩).inv.hom ∘ₗ (D.P (U i) (hd1 i ⟨y, hy⟩) ⟨y, hy⟩ (pt i ⟨y, hy⟩)).hom.hom
  have hedge : ∀ p w, sigmaMap L U (Pi.single p.1.1 (((hcF S 2).map (m₁ p)).hom w)) =
      sigmaMap L U (Pi.single p.1.2 (((hcF S 2).map (m₂ p)).hom w)) := by
    intro p w
    have h : dMap L U m₁ m₂ (Pi.single p w) ∈ LinearMap.ker (sigmaMap L U) :=
      hexact ▸ LinearMap.mem_range_self _ _
    rwa [LinearMap.mem_ker, dMap_single, map_sub, sub_eq_zero] at h
  have hA2 : ∀ (i j : κ) (hij : i < j) (y : S) (hi : y ∈ U i) (hj : y ∈ U j) v,
      cL i y hi v = cL j y hj v := by
    intro i j hij y hi hj v
    let p : {p : κ × κ // p.1 < p.2} := ⟨(i, j), hij⟩
    have hy' : y ∈ U i ⊓ U j := ⟨hi, hj⟩
    have hD' := hd2 i j ⟨y, hy'⟩
    let x' : (U i ⊓ U j : Opens S) := ⟨y, hy'⟩
    let w := (discTrace D hfin ι tr (U i ⊓ U j) hD' x').inv.hom v
    have e1 := congrArg (fun φ => φ.hom w) (discTrace_comp D hfin ι tr htr hη hm
      (inf_le_left : U i ⊓ U j ≤ U i) hD' (hd1 i ⟨y, hi⟩) x' (pt i ⟨y, hi⟩) (m₁ p) (hm₁ p))
    have e2 := congrArg (fun φ => φ.hom w) (discTrace_comp D hfin ι tr htr hη hm
      (inf_le_right : U i ⊓ U j ≤ U j) hD' (hd1 j ⟨y, hj⟩) x' (pt j ⟨y, hj⟩) (m₂ p) (hm₂ p))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, w, Iso.inv_hom_id_apply] at e1 e2
    have h1 : ((hcF S 2).map (m₁ p)).hom w = (τ i ⟨y, hi⟩).inv.hom
        ((D.P (U i) (hd1 i ⟨y, hi⟩) ⟨y, hi⟩ (pt i ⟨y, hi⟩)).hom.hom v) := by
      rw [← e1, Iso.hom_inv_id_apply]
    have h2 : ((hcF S 2).map (m₂ p)).hom w = (τ j ⟨y, hj⟩).inv.hom
        ((D.P (U j) (hd1 j ⟨y, hj⟩) ⟨y, hj⟩ (pt j ⟨y, hj⟩)).hom.hom v) := by
      rw [← e2, Iso.hom_inv_id_apply]
    simp only [cL, LinearMap.comp_apply, LinearMap.single_apply]
    rw [← h1, ← h2]
    exact hedge p w
  have hA : ∀ (i j : κ) (y : S) (hi : y ∈ U i) (hj : y ∈ U j) v, cL i y hi v = cL j y hj v := by
    intro i j y hi hj v
    rcases lt_trichotomy i j with h | rfl | h
    · exact hA2 i j h y hi hj v
    · rfl
    · exact (hA2 j i h y hj hi v).symm
  let cAt : ∀ y : S, ToType (((TopCat.Sheaf.forget _ S).obj L).stalk y) →ₗ[ℚ]
      ((hcF S 2).obj L).carrier := fun y => cL (hcov y).choose y (hcov y).choose_spec
  have hA' : ∀ i y (hy : y ∈ U i) v, cAt y v = cL i y hy v := fun i y hy v =>
    hA _ i y _ hy v
  have hc : ∀ i (y z : S) (hy : y ∈ U i) (hz : z ∈ U i) v,
      cAt y v = cAt z ((D.P (U i) (hd1 i ⟨y, hy⟩) ⟨y, hy⟩ ⟨z, hz⟩).hom.hom v) := by
    intro i y z hy hz v
    rw [hA' i y hy, hA' i z hz]
    simp only [cL, LinearMap.comp_apply, LinearMap.single_apply]
    rw [Transport.P_hom_P_hom]
  have hC : ∀ (y z : S) (γ : Path y z) v,
      cAt y v = cAt z ((D.T (Path.Homotopic.Quotient.mk γ)).hom.hom v) :=
    fun _ _ γ v => eq_apply_T_of_forall_P hL D U hcov hd1 (fun y => cAt y) hc γ v
  -- the map to the coinvariants
  let β : ∀ i (h : (U i : Set S).Nonempty), Path (pt i h).1 t := fun i h =>
    PathConnectedSpace.somePath _ _
  let R := Submodule.span ℚ (relSet L t)
  let φ : ∀ i, (hcV L (U i)).carrier →ₗ[ℚ] (((TopCat.Sheaf.forget _ S).obj L).stalk t ⧸ R) :=
    fun i => if h : (U i : Set S).Nonempty then
      R.mkQ ∘ₗ (D.T (Path.Homotopic.Quotient.mk (β i h))).hom.hom ∘ₗ (τ i h).hom.hom else 0
  let Φ₀ : (∀ i, (hcV L (U i)).carrier) →ₗ[ℚ] (((TopCat.Sheaf.forget _ S).obj L).stalk t ⧸ R) :=
    ∑ i, φ i ∘ₗ LinearMap.proj (R := ℚ) (φ := fun i => (hcV L (U i)).carrier) i
  have hΦ₀ : ∀ i a, Φ₀ (Pi.single i a) = φ i a := by
    intro i a
    simp only [Φ₀]
    rw [LinearMap.sum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_apply, hj]
    · simp
  have hφ : ∀ i (h : (U i : Set S).Nonempty) a,
      φ i a = R.mkQ ((D.T (Path.Homotopic.Quotient.mk (β i h))).hom.hom ((τ i h).hom.hom a)) := by
    intro i h a
    simp only [φ, dif_pos h]
    rfl
  have hΦd : LinearMap.ker (sigmaMap L U) ≤ LinearMap.ker Φ₀ := by
    rw [← hexact]
    rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker, ← Finset.univ_sum_single z, map_sum, map_sum]
    refine Finset.sum_eq_zero fun p _ => ?_
    rcases p with ⟨⟨i, j⟩, hij⟩
    rw [dMap_single, map_sub, hΦ₀, hΦ₀, sub_eq_zero]
    by_cases hne : ((U i ⊓ U j : Opens S) : Set S).Nonempty
    · obtain ⟨y, hy⟩ := hne
      have hi : (U i : Set S).Nonempty := ⟨y, hy.1⟩
      have hj : (U j : Set S).Nonempty := ⟨y, hy.2⟩
      have hD' := hd2 i j ⟨y, hy⟩
      let x' : (U i ⊓ U j : Opens S) := ⟨y, hy⟩
      have e1 := congrArg (fun φ => φ.hom (z ⟨(i, j), hij⟩)) (discTrace_comp D hfin ι tr htr hη hm
        (inf_le_left : U i ⊓ U j ≤ U i) hD' (hd1 i hi) x' (pt i hi) (m₁ ⟨(i, j), hij⟩)
          (hm₁ ⟨(i, j), hij⟩))
      have e2 := congrArg (fun φ => φ.hom (z ⟨(i, j), hij⟩)) (discTrace_comp D hfin ι tr htr hη hm
        (inf_le_right : U i ⊓ U j ≤ U j) hD' (hd1 j hj) x' (pt j hj) (m₂ ⟨(i, j), hij⟩)
          (hm₂ ⟨(i, j), hij⟩))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e1 e2
      rw [hφ i hi, hφ j hj]
      change R.mkQ ((D.T (Path.Homotopic.Quotient.mk (β i hi))).hom.hom
          ((τ i hi).hom.hom (((hcF S 2).map (m₁ ⟨(i, j), hij⟩)).hom (z ⟨(i, j), hij⟩)))) =
        R.mkQ ((D.T (Path.Homotopic.Quotient.mk (β j hj))).hom.hom
          ((τ j hj).hom.hom (((hcF S 2).map (m₂ ⟨(i, j), hij⟩)).hom (z ⟨(i, j), hij⟩))))
      rw [e1, e2]
      obtain ⟨ci, hci⟩ : ∃ c, D.P (U i) (hd1 i hi) ⟨x'.1, inf_le_left (a := U i) x'.2⟩ (pt i hi) =
        D.T c := ⟨_, rfl⟩
      obtain ⟨cj, hcj⟩ : ∃ c, D.P (U j) (hd1 j hj) ⟨x'.1, inf_le_right (a := U i) x'.2⟩ (pt j hj) =
        D.T c := ⟨_, rfl⟩
      rw [hci, hcj, D.T_hom_T_hom, D.T_hom_T_hom]
      exact mkQ_T_eq_mkQ_T hL D _ _ _
    · haveI := hzero (U i ⊓ U j) (Set.not_nonempty_iff_eq_empty.1 hne)
      rw [Subsingleton.elim (z ⟨(i, j), hij⟩) 0, map_zero, map_zero, map_zero, map_zero]
  let Φ : ((hcF S 2).obj L).carrier →ₗ[ℚ] (((TopCat.Sheaf.forget _ S).obj L).stalk t ⧸ R) :=
    (LinearMap.ker (sigmaMap L U)).liftQ Φ₀ hΦd ∘ₗ
      ((sigmaMap L U).quotKerEquivOfSurjective hsurj).symm.toLinearMap
  have hΦσ : ∀ z, Φ (sigmaMap L U z) = Φ₀ z := by
    intro z
    simp only [Φ, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [show ((sigmaMap L U).quotKerEquivOfSurjective hsurj).symm (sigmaMap L U z) =
      Submodule.Quotient.mk z from (LinearEquiv.symm_apply_eq _).2
        (LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _).symm]
    exact Submodule.liftQ_apply _ _ _
  let Ψ : (((TopCat.Sheaf.forget _ S).obj L).stalk t ⧸ R) →ₗ[ℚ] ((hcF S 2).obj L).carrier :=
    R.liftQ (cAt t) (span_relSet_le_ker D (cAt t) fun γ w => (hC t t γ w).symm)
  have hΨ : ∀ x, Ψ (Submodule.Quotient.mk x) = cAt t x := fun x => Submodule.liftQ_apply _ _ _
  refine ⟨LinearEquiv.ofLinear Φ Ψ ?_ ?_⟩
  · refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    change Φ (Ψ (Submodule.Quotient.mk v)) = Submodule.Quotient.mk v
    have hi := (hcov t).choose_spec
    have hne : (U (hcov t).choose : Set S).Nonempty := ⟨t, hi⟩
    rw [hΨ]
    change Φ (sigmaMap L U (Pi.single (hcov t).choose ((τ _ ⟨t, hi⟩).inv.hom
      ((D.P (U _) (hd1 _ ⟨t, hi⟩) ⟨t, hi⟩ (pt _ ⟨t, hi⟩)).hom.hom v)))) = _
    rw [hΦσ, hΦ₀, hφ _ hne, Iso.inv_hom_id_apply]
    obtain ⟨c, hc⟩ : ∃ c, D.P (U _) (hd1 _ ⟨t, hi⟩) ⟨t, hi⟩ (pt _ ⟨t, hi⟩) = D.T c := ⟨_, rfl⟩
    rw [hc, D.T_hom_T_hom]
    have := mkQ_T_eq_mkQ_T hL D (c.trans (Path.Homotopic.Quotient.mk (β _ hne)))
      (Path.Homotopic.Quotient.refl t) v
    rwa [Transport.T_refl] at this
  · refine LinearMap.ext fun h => ?_
    obtain ⟨z, rfl⟩ := hsurj h
    change Ψ (Φ (sigmaMap L U z)) = sigmaMap L U z
    rw [hΦσ]
    conv_rhs => rw [← Finset.univ_sum_single z]
    conv_lhs => rw [← Finset.univ_sum_single z]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΦ₀]
    by_cases hne : (U i : Set S).Nonempty
    · rw [hφ i hne, Submodule.mkQ_apply, hΨ, ← hC _ t (β i hne), hA' i _ (pt i hne).2]
      change sigmaMap L U (Pi.single i ((τ i hne).inv.hom
        ((D.P (U i) (hd1 i hne) (pt i hne) (pt i hne)).hom.hom ((τ i hne).hom.hom (z i))))) = _
      rw [Transport.P_self, Iso.refl_hom, ModuleCat.hom_id, LinearMap.id_apply,
        Iso.hom_inv_id_apply]
    · haveI := hzero (U i) (Set.not_nonempty_iff_eq_empty.1 hne)
      rw [Subsingleton.elim (z i) 0, map_zero, map_zero, Pi.single_zero, map_zero]

end Assembly

/-! ### The complex curve -/

section Curve

/-- The fibres of a local system are finite-dimensional. -/
private theorem finite_stalk_of_isLocalSystem {X : TopCat.{0}}
    {L : TopCat.Sheaf (ModuleCat.{0} ℚ) X} (hL : IsLocalSystem L) (x : X) :
    Module.Finite ℚ (((TopCat.Sheaf.forget _ X).obj L).stalk x) := by
  obtain ⟨V, hx, E, hE, ⟨φ⟩⟩ := hL x
  let y : (Opens.toTopCat X).obj V := ⟨x, hx⟩
  let e1 := LinearEquiv.ofBijective (stalkToPullbackStalk V.inclusion' L y).hom
    (bijective_stalkToPullbackStalk _ _ y)
  let e2 := ((TopCat.Presheaf.stalkFunctor _ y).mapIso
    ((TopCat.Sheaf.forget _ _).mapIso φ)).toLinearEquiv
  let e3 := (constGermEquiv E y).symm
  exact Module.Finite.equiv (e1.trans (e2.trans e3)).symm

/-- `H²_c(S, j_! j^* L)` vanishes when all stalks of `j_! j^* L` vanish. -/
private theorem subsingleton_hcV_of_isZero_stalk {S : TopCat.{0}}
    {L : TopCat.Sheaf (ModuleCat.{0} ℚ) S} (V : Opens S)
    (h : ∀ x, IsZero (((TopCat.Sheaf.forget _ S).obj ((extV V).obj ((resV V).obj L))).stalk x)) :
    Subsingleton (hcV L V) := by
  have hK : IsZero ((extV V).obj ((resV V).obj L)) := by
    rw [IsZero.iff_id_eq_zero]
    apply (TopCat.Sheaf.forget _ S).map_injective
    ext U s
    refine TopCat.Presheaf.section_ext _ _ _ _ fun x hx => ?_
    exact @Subsingleton.elim _ (ModuleCat.isZero_iff_subsingleton.1 (h x)) _ _
  have hz : IsZero (((compactSupportSectionsFunctor ℚ).rightDerived 2).obj
      ((extV V).obj ((resV V).obj L))) := Functor.map_isZero _ hK
  exact ModuleCat.isZero_iff_subsingleton.1
    (hz.of_iso (compactSupportCohomologyIsoRightDerived ((extV V).obj ((resV V).obj L)) 2))

/-- A scheme locally of finite type over `ℂ` with connected complex realization is connected:
its closed points, which are the complex points, are dense. -/
private theorem connectedSpace_of_connectedSpace_analyticSpace {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] [ConnectedSpace (analyticSpace sX)] :
    ConnectedSpace X := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  haveI : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := ‹LocallyOfFiniteType sX›
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  haveI : ConnectedSpace (MMP.Analytic.ComplexPoints (X ↘ Spec (.of ℂ))) :=
    ‹ConnectedSpace (analyticSpace sX)›
  haveI : ConnectedSpace (MMP.UnderlyingSpace ℂ X) :=
    (homeomorphUnderlyingSpace (X := X)).surjective.connectedSpace
      (homeomorphUnderlyingSpace (X := X)).continuous
  let f : MMP.UnderlyingSpace ℂ X → X := fun p =>
    (MMP.UnderlyingSpace.equivClosedPoints X p : X)
  have hf : Continuous f := by
    refine continuous_def.2 fun s hs => ?_
    have : f ⁻¹' s = {p : MMP.UnderlyingSpace ℂ X | ⊤ ≤ p.toHom ⁻¹ᵁ ⟨s, hs⟩} := by
      ext p
      simp only [Set.mem_preimage, Set.mem_setOf_eq, f,
        MMP.UnderlyingSpace.equivClosedPoints_apply]
      refine ⟨fun h q _ => ?_, fun h => h (Set.mem_univ _)⟩
      rw [Subsingleton.elim q (IsLocalRing.closedPoint ℂ)]
      exact h
    rw [this]
    exact MMP.UnderlyingSpace.isOpen_setOf_le_preimage _
  have hrange : Set.range f = closedPoints X := by
    ext x
    refine ⟨?_, fun hx => ⟨(MMP.UnderlyingSpace.equivClosedPoints X).symm ⟨x, hx⟩, by simp [f]⟩⟩
    rintro ⟨p, rfl⟩
    exact (MMP.UnderlyingSpace.equivClosedPoints X p).2
  have h := (isConnected_range hf).closure
  rw [hrange, closure_closedPoints] at h
  exact connectedSpace_iff_univ.2 h

/-- The complex realization of a scheme locally of finite type over `ℂ` is locally path
connected: its points have bases of contractible open neighbourhoods. -/
private theorem locallyPathConnectedSpace_analyticSpace' {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] :
    LocallyPathConnectedSpace (analyticSpace sX) := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  haveI : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := ‹LocallyOfFiniteType sX›
  have hb := MMP.UnderlyingSpace.hasOpenContractibleBasis X
  haveI : LocallyPathConnectedSpace (MMP.UnderlyingSpace ℂ X) :=
    LocallyPathConnectedSpace.of_bases hb fun x V hV => by
      change IsPathConnected V
      haveI : ContractibleSpace V := hV.2.2
      exact isPathConnected_iff_pathConnectedSpace.2 inferInstance
  exact (homeomorphUnderlyingSpace (X := X)).isOpenEmbedding.locallyPathConnectedSpace

private theorem finrank_euclideanSpace_complex_one :
    Module.finrank ℝ (EuclideanSpace ℂ (Fin 1)) = 2 := by
  rw [finrank_real_of_complex, finrank_euclideanSpace_fin]

end Curve

end

@[expose] public section

/-- **Top compactly supported cohomology of a local system on a curve is the monodromy
coinvariant space.** For a smooth separated complex curve `T` of finite type with connected
analytic realization, a local system `L` of finite-dimensional `ℚ`-vector spaces on `T^an` and a
point `t`, `H²_c(T^an, L)` is isomorphic to the quotient of the fibre `L_t` by the span of all
`w - v`, where `v` is the parallel transport of `w` along a loop at `t`. -/
@[mmp "lem_mmp_curve_top_compact_cohomology_coinvariants"]
public theorem nonempty_compactSupportCohomology_two_linearEquiv_coinvariants
    {T : Scheme.{0}} (sT : T ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 sT]
    [QuasiCompact sT] [IsSeparated sT]
    [ConnectedSpace (analyticSpace sT)]
    (L : TopCat.Sheaf (ModuleCat.{0} ℚ) (analyticSpace sT)) (hL : IsLocalSystem L)
    (t : analyticSpace sT) :
    Nonempty (compactSupportCohomology ℚ 2 L ≃ₗ[ℚ]
      (((TopCat.Sheaf.forget _ _).obj L).stalk t ⧸ Submodule.span ℚ
        {u | ∃ (γ : Path t t)
            (s : ToType (((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
              (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj L).obj.obj
                (op ⊤)))
            (w v : ((TopCat.Sheaf.forget _ _).obj L).stalk t),
            (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
                L 0).hom
              ((((TopCat.Sheaf.forget _ _).obj L).stalkCongr (.of_eq γ.source.symm)).hom.hom w) =
              (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
                (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj L)).germ
                  ⊤ 0 trivial).hom s ∧
            (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
                L 1).hom
              ((((TopCat.Sheaf.forget _ _).obj L).stalkCongr (.of_eq γ.target.symm)).hom.hom v) =
              (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
                (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj L)).germ
                  ⊤ 1 trivial).hom s ∧
            u = w - v})) := by
  haveI : Smooth sT := SmoothOfRelativeDimension.smooth 1 sT
  haveI : T2Space (analyticSpace sT) := MMP.Analytic.ComplexPoints.t2Space
  letI : ChartedSpace (EuclideanSpace ℂ (Fin 1)) (analyticSpace sT) :=
    MMP.Analytic.ComplexPoints.instChartedSpaceEuclideanSpace
  haveI : IsManifold (modelWithCornersSelf ℂ (EuclideanSpace ℂ (Fin 1))) 1 (analyticSpace sT) :=
    MMP.Analytic.ComplexPoints.instIsManifoldEuclideanSpace
  have hS : MMP.IsOrientedAtlas (EuclideanSpace ℂ (Fin 1)) (analyticSpace sT) :=
    MMP.isOrientedAtlas_of_isManifold_complex _
  haveI : LocallyCompactSpace (analyticSpace sT) :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℂ (Fin 1)) _
  haveI : LocallyPathConnectedSpace (analyticSpace sT) :=
    locallyPathConnectedSpace_analyticSpace' sT
  haveI : PathConnectedSpace (analyticSpace sT) := pathConnectedSpace_iff_connectedSpace.2 ‹_›
  haveI : ConnectedSpace T := connectedSpace_of_connectedSpace_analyticSpace sT
  obtain ⟨κ, _, U, hUo, hUcov, hgood, -⟩ := MMP.Fourfold.exists_finite_goodCover_analyticSpace sT
  letI : LinearOrder κ := LinearOrder.lift' (Fintype.equivFin κ) (Fintype.equivFin κ).injective
  let U' : κ → Opens (analyticSpace sT) := fun i => ⟨U i, hUo i⟩
  have hcov : ∀ y, ∃ i, y ∈ U' i := by
    intro y
    have : y ∈ ⋃ i, U i := hUcov ▸ Set.mem_univ y
    exact Set.mem_iUnion.1 this
  have hU' : ⨆ i, U' i = ⊤ := by
    ext y
    simp only [Opens.coe_iSup, Set.mem_iUnion, Opens.coe_top, Set.mem_univ, iff_true]
    exact hcov y
  have hgood' : ∀ I : Finset κ, I.Nonempty → (⋂ i ∈ I, (U' i : Set (analyticSpace sT))).Nonempty →
      Nonempty (↥(⋂ i ∈ I, (U' i : Set (analyticSpace sT))) ≃ₜ EuclideanSpace ℝ (Fin 2)) := by
    intro I hI hne
    have e : (⋂ i ∈ I, (U' i : Set (analyticSpace sT))) = MMP.Topology.coverInter U I := by
      ext y
      simp [MMP.Topology.mem_coverInter, U']
    rw [e] at hne ⊢
    exact hgood I hI hne
  have hdisc : ∀ (I : Finset κ) {A : Set (analyticSpace sT)}, I.Nonempty →
      ⋂ i ∈ I, (U' i : Set (analyticSpace sT)) = A → A.Nonempty →
        Nonempty (A ≃ₜ EuclideanSpace ℝ (Fin 2)) := by
    rintro I A hI rfl
    exact hgood' I hI
  have hd1 : ∀ i, (U' i : Set (analyticSpace sT)).Nonempty →
      Nonempty (U' i ≃ₜ EuclideanSpace ℝ (Fin 2)) :=
    fun i => hdisc {i} (Finset.singleton_nonempty i) (by simp)
  have hd2 : ∀ i j, ((U' i ⊓ U' j : Opens (analyticSpace sT)) : Set (analyticSpace sT)).Nonempty →
      Nonempty ((U' i ⊓ U' j : Opens (analyticSpace sT)) ≃ₜ EuclideanSpace ℝ (Fin 2)) :=
    fun i j => hdisc {i, j} (Finset.insert_nonempty _ _) (by ext; simp)
  obtain ⟨hOE1, hOE2, ιq, -, -, -, -⟩ :=
    MMP.Fourfold.compactSupportCohomology_extendByZero ℚ (analyticSpace sT)
  have hη : ∀ (V : Opens (analyticSpace sT)) G, IsIso ((adjV V).unit.app G) :=
    fun V G => (hOE1 V).2.1 G
  have hm : ∀ (F : TopCat.Sheaf (ModuleCat.{0} ℚ) (analyticSpace sT))
      (V U : Opens (analyticSpace sT)), V ≤ U →
      ∃ m : (extV V).obj ((resV V).obj F) ⟶ (extV U).obj ((resV U).obj F),
        m ≫ (adjV U).counit.app F = (adjV V).counit.app F :=
    fun F V U h => (hOE2 F V U h).exists
  have hzero : ∀ V : Opens (analyticSpace sT), (V : Set (analyticSpace sT)) = ∅ →
      Subsingleton (hcV L V) := by
    intro V hV
    refine subsingleton_hcV_of_isZero_stalk V fun x => (hOE1 V).2.2.2.1 _ x ?_
    intro hx
    have : x ∈ (V : Set (analyticSpace sT)) := hx
    rw [hV] at this
    exact this
  let ι : ∀ V : Opens (analyticSpace sT),
      hcF ((Opens.toTopCat (analyticSpace sT)).obj V) 2 ≅ extV V ⋙ hcF (analyticSpace sT) 2 :=
    fun V => ιq V 2
  obtain ⟨-, hPT⟩ := MMP.Fourfold.compactSupportCohomology_orientedPlane_trace
    (EuclideanSpace ℂ (Fin 1)) finrank_euclideanSpace_complex_one (analyticSpace sT) hS
  obtain ⟨tr, htr⟩ := hPT ι
  obtain ⟨-, hGC⟩ := MMP.Fourfold.compactSupportCohomology_two_of_goodCover
    (EuclideanSpace ℂ (Fin 1)) finrank_euclideanSpace_complex_one (analyticSpace sT) hS U' hU'
      hgood' L hL
  choose m₁ hm₁ using fun p : {p : κ × κ // p.1 < p.2} =>
    hm L (U' p.1.1 ⊓ U' p.1.2) (U' p.1.1) inf_le_left
  choose m₂ hm₂ using fun p : {p : κ × κ // p.1 < p.2} =>
    hm L (U' p.1.1 ⊓ U' p.1.2) (U' p.1.2) inf_le_right
  obtain ⟨hexact, hsurj⟩ := hGC m₁ m₂ hm₁ hm₂
  exact nonempty_linearEquiv_of_goodCover hL (Transport.ofIsLocalSystem hL)
    (finite_stalk_of_isLocalSystem hL) ι tr htr hη hm U' hcov hd1 hd2 hzero m₁ m₂ hm₁ hm₂
    hexact hsurj t

end

end MMP.Fourfold
