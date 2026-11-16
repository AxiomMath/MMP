module

public import MMP.AlgebraicGeometry.Singularities.CyclicCover.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.UngradedFunctorial
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.PairComposition
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# The action of the roots of unity on a cyclic cover

For a global unit `ζ` of `X`, multiplication by `ζⁱ` on `Symⁱ(N)` is a graded `𝒪_X`-algebra
automorphism `σ_ζ` of `Sym(N)`, and it induces an `X`-automorphism `α_ζ` of `Spec_X Sym(N)`. When
`ζᵐ = 1`, `σ_ζ` maps each generator `u - ⟨u, s⟩` of `I_s` to `ζᵐ u - ⟨u, s⟩ = u - ⟨u, s⟩`, so `α_ζ`
restricts to an `X`-automorphism of the cyclic cover `Z = Spec_X 𝒜(L, m, s)`, with `α_ζ^* = σ_ζ`.

## Main definitions

* `MMP.Mori.symSpecScaling`: the scaling automorphism `α_ζ` of `Spec_X Sym(N)`.
* `MMP.Mori.cyclicCoverScaling`, `MMP.Mori.cyclicCoverScalingIso`: the automorphism `α_ζ` of the
  cyclic cover, for an `m`-th root of unity `ζ`.

## Main results

* `MMP.Mori.cyclicCoverScaling_cyclicCoverAlgebraIncl`: `α_ζ^*` is multiplication by `ζⁱ` on the
  image of `L⁻ⁱ` in `𝒜(L, m, s)`.
* `MMP.Mori.cyclicCoverScaling_comp`, `MMP.Mori.cyclicCoverScaling_one`: `ζ ↦ α_ζ` is an action.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.47.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace MMP.Mori

section Scaling

variable {X : Scheme.{u}} (N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]

/-- The ring of sections of `𝒪_X` over an open `U` is commutative. -/
instance ringCatSheaf_isMulCommutative (U : (X.Opens)ᵒᵖ) :
    IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (IsMulCommutative (X.presheaf.obj U))

/-- The restriction to an open `U` of a global function `c` of `X`, as a scalar acting on the
sections over `U` of a sheaf of `𝒪_X`-modules. -/
abbrev globalScalar (c : Γ(X, ⊤)) (U : (X.Opens)ᵒᵖ) : X.ringCatSheaf.obj.obj U :=
  X.ringCatSheaf.obj.map (isTerminalTop.from U.unop).op c

/-- Restricting global functions to `U` is multiplicative. -/
lemma globalScalar_mul (c d : Γ(X, ⊤)) (U : (X.Opens)ᵒᵖ) :
    globalScalar (c * d) U = globalScalar c U * globalScalar d U :=
  map_mul (X.ringCatSheaf.obj.map (isTerminalTop.from U.unop).op).hom c d

/-- The restriction to `U` of the global function `1` is `1`. -/
lemma globalScalar_one (U : (X.Opens)ᵒᵖ) : globalScalar (1 : Γ(X, ⊤)) U = 1 :=
  map_one (X.ringCatSheaf.obj.map (isTerminalTop.from U.unop).op).hom

/-- Multiplication by `ζⁿ` on `Symⁿ(N)`, for a global unit `ζ` of `X`. -/
def symScalingPiece (ζ : Γ(X, ⊤)ˣ) (n : ℤ) :
    (cyclicCoverSituation N).symmetricAlgebra.piece n ⟶
      (cyclicCoverSituation N).symmetricAlgebra.piece n :=
  (Stacks.SheafOfModules.terminalSectionToEnd X.ringCatSheaf ⊤ isTerminalTop
    (((ζ ^ n : Γ(X, ⊤)ˣ) : Γ(X, ⊤)))).asHom.app _

/-- On sections over `U`, `symScalingPiece N ζ n` is multiplication by the restriction of `ζⁿ`. -/
lemma symScalingPiece_apply (ζ : Γ(X, ⊤)ˣ) (n : ℤ) (U : (X.Opens)ᵒᵖ)
    (x : ((cyclicCoverSituation N).symmetricAlgebra.piece n).val.obj U) :
    (symScalingPiece N ζ n).val.app U x = globalScalar ((ζ ^ n : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) U • x :=
  rfl

/-- The graded `𝒪_X`-algebra automorphism `σ_ζ` of `Sym(N)` which is multiplication by `ζⁱ` on
`Symⁱ(N)`, for a global unit `ζ` of `X`. -/
def symScaling (ζ : Γ(X, ⊤)ˣ) :
    SheafOfModules.GradedAlgebra.UnitalHom (cyclicCoverSituation N).symmetricAlgebra
      (cyclicCoverSituation N).symmetricAlgebra where
  app n := symScalingPiece N ζ n
  map_mul i j U x y := by
    change globalScalar ((ζ ^ (i + j) : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) U •
        ((cyclicCoverSituation N).symmetricAlgebra.mul i j).app U x y =
      ((cyclicCoverSituation N).symmetricAlgebra.mul i j).app U
        (globalScalar ((ζ ^ i : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) U • x)
        (globalScalar ((ζ ^ j : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) U • y)
    rw [(((cyclicCoverSituation N).symmetricAlgebra.mul i j)).map_smul_left,
      (((cyclicCoverSituation N).symmetricAlgebra.mul i j)).map_smul_right, ← mul_smul,
      ← globalScalar_mul, ← Units.val_mul, ← zpow_add]
  map_one U := by
    change globalScalar ((ζ ^ (0 : ℤ) : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) U •
      (cyclicCoverSituation N).symmetricAlgebra.one.eval U = _
    rw [zpow_zero, Units.val_one, globalScalar_one, one_smul]

/-- Multiplication by `ηⁿ` followed by multiplication by `ζⁿ` is multiplication by `(ζη)ⁿ`. -/
@[reassoc (attr := simp)]
lemma symScalingPiece_comp (ζ η : Γ(X, ⊤)ˣ) (n : ℤ) :
    symScalingPiece N η n ≫ symScalingPiece N ζ n = symScalingPiece N (ζ * η) n := by
  ext U x
  change globalScalar ((ζ ^ n : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) U •
      globalScalar ((η ^ n : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) U • x =
    globalScalar (((ζ * η) ^ n : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) U • x
  rw [← mul_smul, ← globalScalar_mul, ← Units.val_mul, mul_zpow]

/-- Multiplication by `1ⁿ` on `Symⁿ(N)` is the identity. -/
@[simp]
lemma symScalingPiece_one (n : ℤ) : symScalingPiece N 1 n = 𝟙 _ := by
  ext U x
  change globalScalar (((1 : Γ(X, ⊤)ˣ) ^ n : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) U • x = x
  rw [one_zpow, Units.val_one, globalScalar_one, one_smul]

/-- The composite of `σ_η` and `σ_ζ` is `σ_{ζη}`. -/
lemma symScaling_comp (ζ η : Γ(X, ⊤)ˣ) :
    (symScaling N η).comp (symScaling N ζ) = symScaling N (ζ * η) :=
  SheafOfModules.GradedAlgebra.UnitalHom.ext fun n => symScalingPiece_comp N ζ η n

/-- The scaling `σ_1` of `Sym(N)` is the identity. -/
@[simp]
lemma symScaling_one : symScaling N 1 = SheafOfModules.GradedAlgebra.UnitalHom.id _ :=
  SheafOfModules.GradedAlgebra.UnitalHom.ext fun n => symScalingPiece_one N n

end Scaling

/-! ### The scaling automorphisms of `Spec_X Sym(N)` -/

section SymSpec

variable {X : Scheme.{u}} (N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]

/-- The relative-spectrum datum `(X, Sym(N))` whose relative spectrum is `Spec_X Sym(N)`. -/
abbrev symSpecSituation : Stacks.RelativeSpec.RelativeSpecSituation.{u} :=
  (cyclicCoverSituation N).relativeSpecSituation

/-- The scaling `σ_ζ` of `Sym(N)` on the ungraded algebra sheaf of `Sym(N)`, as a morphism of
presheaves of `𝒪_X`-algebras. -/
def algebraScaling (ζ : Γ(X, ⊤)ˣ) :
    Under.mk (symSpecSituation N).algebra.hom.hom ⟶ Under.mk (symSpecSituation N).algebra.hom.hom :=
  Under.homMk
    (Stacks.RelativeSpec.ungradedAlgebraSheafMap X (cyclicCoverSituation N).symmetricAlgebra
      (cyclicCoverSituation N).symmetricAlgebra (cyclicCoverSituation N).symmetricAlgebra_mul_comm
      (cyclicCoverSituation N).symmetricAlgebra_mul_comm (symScaling N ζ)).right.hom
    (congrArg (fun k => k.hom)
      (Under.w (Stacks.RelativeSpec.ungradedAlgebraSheafMap X
        (cyclicCoverSituation N).symmetricAlgebra (cyclicCoverSituation N).symmetricAlgebra
        (cyclicCoverSituation N).symmetricAlgebra_mul_comm
        (cyclicCoverSituation N).symmetricAlgebra_mul_comm (symScaling N ζ))))

/-- On the image of a local section `x` of `Symⁿ(N)` over `W`, `algebraScaling N ζ` is the image
of `ζⁿ x`. -/
lemma algebraScaling_incl (ζ : Γ(X, ⊤)ˣ) (n : ℤ) (W : X.Opens)
    (x : ((cyclicCoverSituation N).symmetricAlgebra.piece n).val.obj (op W)) :
    ((algebraScaling N ζ).right.app (op W)).hom ((cyclicCoverSituation N).algebraSheafIncl n W x) =
      (cyclicCoverSituation N).algebraSheafIncl n W
        (globalScalar ((ζ ^ n : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) (op W) • x) :=
  Stacks.RelativeSpec.ungradedAlgebraSheafMap_incl X _ _ _ _ (symScaling N ζ) n W x

/-- Over each open `W`, the scaling by `η` followed by the scaling by `ζ` is the scaling by
`ζη`. -/
lemma algebraScaling_comp (ζ η : Γ(X, ⊤)ˣ) (W : X.Opens) :
    (algebraScaling N η).right.app (op W) ≫ (algebraScaling N ζ).right.app (op W) =
      (algebraScaling N (ζ * η)).right.app (op W) := by
  have h := Stacks.RelativeSpec.ungradedAlgebraSheafMap_comp X
    (cyclicCoverSituation N).symmetricAlgebra (cyclicCoverSituation N).symmetricAlgebra
    (cyclicCoverSituation N).symmetricAlgebra_mul_comm
    (cyclicCoverSituation N).symmetricAlgebra_mul_comm
    (cyclicCoverSituation N).symmetricAlgebra
    (cyclicCoverSituation N).symmetricAlgebra_mul_comm (symScaling N η) (symScaling N ζ)
  rw [symScaling_comp] at h
  exact (congrArg (fun k => NatTrans.app k.right.hom (op W)) h).symm

/-- Over each open `W`, the scaling by `1` is the identity. -/
lemma algebraScaling_one (W : X.Opens) :
    (algebraScaling N 1).right.app (op W) = 𝟙 _ := by
  have h := Stacks.RelativeSpec.ungradedAlgebraSheafMap_id X
    (cyclicCoverSituation N).symmetricAlgebra (cyclicCoverSituation N).symmetricAlgebra_mul_comm
  rw [← symScaling_one] at h
  exact congrArg (fun k => NatTrans.app k.right.hom (op W)) h

/-- The relative-spectrum pair `(π, σ_ζ ≫ ψ)` over `Spec_X Sym(N)`, where `π` is the structure
morphism and `ψ : Sym(N) ⟶ π_* 𝒪` the universal algebra map. -/
def symSpecPair (ζ : Γ(X, ⊤)ˣ) :
    Stacks.RelativeSpec.RelativeSpecPair (symSpecSituation N) (symSpec N) :=
  ⟨symSpecToBase N, algebraScaling N ζ ≫
    Stacks.RelativeSpec.universalAlgebraMap (symSpecSituation N)⟩

/-- The scaling automorphism of `Spec_X Sym(N)` attached to a global unit `ζ` of `X`: the
`X`-morphism whose pull-back on functions is `σ_ζ`, multiplication by `ζⁱ` on `Symⁱ(N)`. -/
def symSpecScaling (ζ : Γ(X, ⊤)ˣ) : symSpec N ⟶ symSpec N :=
  Stacks.RelativeSpec.pairToHom (symSpecPair N ζ)

/-- The scaling automorphism `α_ζ` of `Spec_X Sym(N)` is a morphism over `X`. -/
@[reassoc (attr := simp)]
lemma symSpecScaling_toBase (ζ : Γ(X, ⊤)ˣ) :
    symSpecScaling N ζ ≫ symSpecToBase N = symSpecToBase N :=
  Stacks.RelativeSpec.pairToHom_toBase (symSpecPair N ζ)

/-- A morphism into a relative spectrum pulling the universal pair back to `q` acts on sections
over the preimage of any open of the base by the algebra map of `q`. -/
private lemma appLE_of_pullback_universal {s : Stacks.RelativeSpec.RelativeSpecSituation.{u}}
    {T : Scheme.{u}} (f : T ⟶ (Stacks.RelativeSpec.gluedSpectrum s).scheme)
    (q : Stacks.RelativeSpec.RelativeSpecPair s T)
    (hq : Stacks.RelativeSpec.RelativeSpecPair.pullback f
      (Stacks.RelativeSpec.universalRelativeSpecPair s) = q) (U : s.base.Opens)
    (h : q.1 ⁻¹ᵁ U ≤ f ⁻¹ᵁ ((Stacks.RelativeSpec.gluedSpectrum s).toBase ⁻¹ᵁ U)) :
    (Stacks.RelativeSpec.universalAlgebraMap s).right.app (op U) ≫
        f.appLE ((Stacks.RelativeSpec.gluedSpectrum s).toBase ⁻¹ᵁ U) (q.1 ⁻¹ᵁ U) h =
      q.2.right.app (op U) := by
  subst hq
  exact congrArg (fun k => (Stacks.RelativeSpec.universalAlgebraMap s).right.app (op U) ≫ k)
    f.appLE_eq_app

/-- On sections over the preimage of an open `W ⊆ X`, the scaling automorphism acts by `σ_ζ`. -/
lemma symSpecScaling_appLE (ζ : Γ(X, ⊤)ˣ) (W : X.Opens)
    (h : symSpecToBase N ⁻¹ᵁ W ≤ symSpecScaling N ζ ⁻¹ᵁ (symSpecToBase N ⁻¹ᵁ W)) :
    (Stacks.RelativeSpec.universalAlgebraMap (symSpecSituation N)).right.app (op W) ≫
        (symSpecScaling N ζ).appLE (symSpecToBase N ⁻¹ᵁ W) (symSpecToBase N ⁻¹ᵁ W) h =
      (algebraScaling N ζ).right.app (op W) ≫
        (Stacks.RelativeSpec.universalAlgebraMap (symSpecSituation N)).right.app (op W) :=
  appLE_of_pullback_universal (symSpecScaling N ζ) (symSpecPair N ζ)
    (Stacks.RelativeSpec.pullback_universalRelativeSpecPair_pairToHom (symSpecPair N ζ)) W h

/-- **The scaling automorphism pulls a homogeneous function of degree `k` back to `ζᵏ` times
itself.** -/
lemma symSpecScaling_symSpecFunction (ζ : Γ(X, ⊤)ˣ) (k : ℕ) (W : X.Opens)
    (x : ((cyclicCoverSituation N).symmetricAlgebra.piece (k : ℤ)).val.obj (op W))
    (h : symSpecToBase N ⁻¹ᵁ W ≤ symSpecScaling N ζ ⁻¹ᵁ (symSpecToBase N ⁻¹ᵁ W)) :
    ((symSpecScaling N ζ).appLE _ _ h).hom (symSpecFunction N k W x) =
      symSpecFunction N k W (globalScalar ((ζ ^ (k : ℤ) : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) (op W) • x) := by
  have e := congrArg (fun φ => φ.hom ((cyclicCoverSituation N).algebraSheafIncl k W x))
    (symSpecScaling_appLE N ζ W h)
  refine e.trans ?_
  exact congrArg
    ((Stacks.RelativeSpec.universalAlgebraMap (symSpecSituation N)).right.app (op W)).hom
    (algebraScaling_incl N ζ k W x)

/-- The scaling automorphism `α_ζ` maps the preimage of each open `W ⊆ X` onto itself. -/
lemma symSpecScaling_preimage (ζ : Γ(X, ⊤)ˣ) (W : X.Opens) :
    symSpecScaling N ζ ⁻¹ᵁ (symSpecToBase N ⁻¹ᵁ W) = symSpecToBase N ⁻¹ᵁ W := by
  rw [← Scheme.Hom.comp_preimage, symSpecScaling_toBase]

/-- A morphism `f` of `Spec_X Sym(N)` over `X` acting by `σ_ζ` on the sections over the preimages
of the affine opens of `X` is the scaling automorphism `α_ζ`. -/
lemma eq_symSpecScaling (ζ : Γ(X, ⊤)ˣ) (f : symSpec N ⟶ symSpec N)
    (hb : f ≫ symSpecToBase N = symSpecToBase N)
    (hm : ∀ (U : X.affineOpens) (h : symSpecToBase N ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ (symSpecToBase N ⁻¹ᵁ U.1)),
      (Stacks.RelativeSpec.universalAlgebraMap (symSpecSituation N)).right.app (op U.1) ≫
          f.appLE (symSpecToBase N ⁻¹ᵁ U.1) (symSpecToBase N ⁻¹ᵁ U.1) h =
        (algebraScaling N ζ).right.app (op U.1) ≫
          (Stacks.RelativeSpec.universalAlgebraMap (symSpecSituation N)).right.app (op U.1)) :
    f = symSpecScaling N ζ :=
  (Stacks.RelativeSpec.pairToHom_pullback_universalRelativeSpecPair f).symm.trans
    (congrArg Stacks.RelativeSpec.pairToHom
      (Stacks.RelativeSpec.pullback_universalRelativeSpecPair_eq (symSpecPair N ζ) f hb hm))

/-- If `u` intertwines `s₁` with `f` and `s₂` with `g`, it intertwines `s₁ ≫ s₂` with `f ≫ g`. -/
private lemma comp_comp_eq_of_comp_eq {C : Type*} [Category C] {a b : C} (u : a ⟶ b)
    (s₁ s₂ s : a ⟶ a) (f g : b ⟶ b) (e₁ : u ≫ f = s₁ ≫ u) (e₂ : u ≫ g = s₂ ≫ u)
    (e : s₁ ≫ s₂ = s) : u ≫ f ≫ g = s ≫ u := by
  rw [← Category.assoc, e₁, Category.assoc, e₂, ← Category.assoc, e]

/-- `Scheme.Hom.appLE_comp_appLE` with the inclusion for the composite given as an argument, so
that instantiating it at concrete morphisms needs no unfolding of their composite. -/
private lemma appLE_comp_appLE' {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (U : C.Opens)
    (V : B.Opens) (W : A.Opens) (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V)
    (e : W ≤ (f ≫ g) ⁻¹ᵁ U) :
    g.appLE U V e₁ ≫ f.appLE V W e₂ = (f ≫ g).appLE U W e :=
  Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂

/-- The composite of two scaling automorphisms acts by the composite of the two scalings. -/
lemma symSpecScaling_comp_appLE (ζ η : Γ(X, ⊤)ˣ) (W : X.Opens)
    (h : symSpecToBase N ⁻¹ᵁ W ≤
      (symSpecScaling N ζ ≫ symSpecScaling N η) ⁻¹ᵁ (symSpecToBase N ⁻¹ᵁ W)) :
    (Stacks.RelativeSpec.universalAlgebraMap (symSpecSituation N)).right.app (op W) ≫
        (symSpecScaling N ζ ≫ symSpecScaling N η).appLE (symSpecToBase N ⁻¹ᵁ W)
          (symSpecToBase N ⁻¹ᵁ W) h =
      (algebraScaling N (ζ * η)).right.app (op W) ≫
        (Stacks.RelativeSpec.universalAlgebraMap (symSpecSituation N)).right.app (op W) := by
  have h₁ : symSpecToBase N ⁻¹ᵁ W ≤ symSpecScaling N η ⁻¹ᵁ (symSpecToBase N ⁻¹ᵁ W) :=
    (symSpecScaling_preimage N η W).ge
  have h₂ : symSpecToBase N ⁻¹ᵁ W ≤ symSpecScaling N ζ ⁻¹ᵁ (symSpecToBase N ⁻¹ᵁ W) :=
    (symSpecScaling_preimage N ζ W).ge
  rw [← appLE_comp_appLE' _ _ _ _ _ h₁ h₂ h]
  exact comp_comp_eq_of_comp_eq _ _ _ _ _ _ (symSpecScaling_appLE N η W h₁)
    (symSpecScaling_appLE N ζ W h₂) (algebraScaling_comp N ζ η W)

/-- **The scaling automorphisms compose as the units do**: `α_ζ ≫ α_η = α_{ζη}`. -/
@[reassoc (attr := simp)]
lemma symSpecScaling_comp (ζ η : Γ(X, ⊤)ˣ) :
    symSpecScaling N ζ ≫ symSpecScaling N η = symSpecScaling N (ζ * η) :=
  eq_symSpecScaling N (ζ * η) _
    (by rw [Category.assoc, symSpecScaling_toBase, symSpecScaling_toBase])
    (fun U h => symSpecScaling_comp_appLE N ζ η U.1 h)

/-- The scaling automorphism attached to `ζ = 1` is the identity. -/
@[simp]
lemma symSpecScaling_one : symSpecScaling N 1 = 𝟙 _ := by
  refine (eq_symSpecScaling N 1 (𝟙 _) (Category.id_comp _) fun U h => ?_).symm
  have hid : Scheme.Hom.appLE (𝟙 (symSpec N)) (symSpecToBase N ⁻¹ᵁ U.1)
      (symSpecToBase N ⁻¹ᵁ U.1) h = 𝟙 _ :=
    (Category.id_comp _).trans ((symSpec N).presheaf.map_id _)
  exact ((congrArg (fun k => _ ≫ k) hid).trans (Category.comp_id _)).trans
    (((congrArg (fun k => k ≫
      (Stacks.RelativeSpec.universalAlgebraMap (symSpecSituation N)).right.app (op U.1))
      (algebraScaling_one N U.1)).trans (Category.id_comp _)).symm)

/-- The scaling automorphism `α_ζ` of `Spec_X Sym(N)`, as an isomorphism with inverse
`α_{ζ⁻¹}`. -/
def symSpecScalingIso (ζ : Γ(X, ⊤)ˣ) : symSpec N ≅ symSpec N where
  hom := symSpecScaling N ζ
  inv := symSpecScaling N ζ⁻¹
  hom_inv_id := by rw [symSpecScaling_comp, mul_inv_cancel, symSpecScaling_one]
  inv_hom_id := by rw [symSpecScaling_comp, inv_mul_cancel, symSpecScaling_one]

/-- The scaling automorphism `α_ζ` of `Spec_X Sym(N)` is an isomorphism. -/
instance (ζ : Γ(X, ⊤)ˣ) : IsIso (symSpecScaling N ζ) :=
  (symSpecScalingIso N ζ).isIso_hom

end SymSpec

/-! ### Descent to the cyclic cover -/

section Descent

variable {X : Scheme.{u}} (N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
  (m : ℕ) (σ : (cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ) ⟶
    SheafOfModules.unit X.ringCatSheaf)

private lemma appLE_congr_hom {A B : Scheme.{u}} {f g : A ⟶ B} (hfg : f = g) (U : B.Opens)
    (V : A.Opens) (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst hfg
  rfl

/-- **An automorphism of `Spec_X Sym(N)` over `X` fixing the generators `u - ⟨u, s⟩` preserves
the ideal sheaf `I_s` they generate.** -/
theorem cyclicCoverIdeal_le_map (α : symSpec N ⟶ symSpec N) [IsIso α]
    (hα : α ≫ symSpecToBase N = symSpecToBase N)
    (hgen : ∀ (W : X.Opens)
      (u : ((cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ)).val.obj (op W))
      (h : symSpecToBase N ⁻¹ᵁ W ≤ α ⁻¹ᵁ (symSpecToBase N ⁻¹ᵁ W)),
      (α.appLE _ _ h).hom (cyclicCoverGenerator N m σ W u) = cyclicCoverGenerator N m σ W u) :
    cyclicCoverIdeal N m σ ≤ (cyclicCoverIdeal N m σ).map α := by
  rw [Scheme.IdealSheafData.le_map_iff_comap_le]
  change _ ≤ Scheme.IdealSheafData.ofIdeals _
  refine Scheme.IdealSheafData.le_ofIdeals_iff.mpr fun U g hg => ?_
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Ideal.mem_comap] at hg
  have hg' := Scheme.IdealSheafData.ideal_ofIdeals_le _ _ hg
  have hgg : g = (α.appLE (α ''ᵁ U.1) U.1 (α.preimage_image_eq U.1).ge).hom
      ((α.appIso U.1).inv.hom g) := by
    rw [← Scheme.Hom.appIso_hom']
    exact (congrArg (fun k => k.hom g) (α.appIso U.1).inv_hom_id).symm
  rw [hgg]
  suffices hS : Ideal.span {f | IsLocallyInCyclicCoverIdeal N m σ (α ''ᵁ U.1) f} ≤
      (Ideal.span {f | IsLocallyInCyclicCoverIdeal N m σ U.1 f}).comap
        (α.appLE (α ''ᵁ U.1) U.1 (α.preimage_image_eq U.1).ge).hom from hS hg'
  rw [Ideal.span_le]
  intro f hf
  refine Ideal.subset_span ?_
  intro y hy
  obtain ⟨W, V', h₁, h₂, hyV', hV'⟩ := hf (α y) ⟨y, hy, rfl⟩
  have hV''U : α ⁻¹ᵁ V'.1 ≤ U.1 := (α.preimage_mono h₁).trans (α.preimage_image_eq U.1).le
  have hW : α ⁻¹ᵁ (symSpecToBase N ⁻¹ᵁ W) = symSpecToBase N ⁻¹ᵁ W := by
    rw [← Scheme.Hom.comp_preimage, hα]
  have hV''W : α ⁻¹ᵁ V'.1 ≤ symSpecToBase N ⁻¹ᵁ W := (α.preimage_mono h₂).trans hW.le
  refine ⟨W, ⟨α ⁻¹ᵁ V'.1, V'.2.preimage α⟩, hV''U, hV''W, hyV', ?_⟩
  have hres : (symSpec N).presheaf.map (homOfLE hV''U).op
      ((α.appLE (α ''ᵁ U.1) U.1 (α.preimage_image_eq U.1).ge).hom f) =
      (α.appLE V'.1 (α ⁻¹ᵁ V'.1) le_rfl).hom ((symSpec N).presheaf.map (homOfLE h₁).op f) := by
    change ((α.appLE _ _ _) ≫ (symSpec N).presheaf.map (homOfLE hV''U).op).hom f =
      ((symSpec N).presheaf.map (homOfLE h₁).op ≫ α.appLE V'.1 (α ⁻¹ᵁ V'.1) le_rfl).hom f
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  rw [hres]
  suffices hS : Ideal.span (Set.range fun u =>
        (symSpec N).presheaf.map (homOfLE h₂).op (cyclicCoverGenerator N m σ W u)) ≤
      (Ideal.span (Set.range fun u =>
        (symSpec N).presheaf.map (homOfLE hV''W).op (cyclicCoverGenerator N m σ W u))).comap
        (α.appLE V'.1 (α ⁻¹ᵁ V'.1) le_rfl).hom from hS hV'
  rw [Ideal.span_le]
  rintro _ ⟨u, rfl⟩
  refine Ideal.subset_span ⟨u, ?_⟩
  have hW' : symSpecToBase N ⁻¹ᵁ W ≤ α ⁻¹ᵁ (symSpecToBase N ⁻¹ᵁ W) := hW.ge
  change ((symSpec N).presheaf.map (homOfLE hV''W).op).hom
      (cyclicCoverGenerator N m σ W u) =
    ((symSpec N).presheaf.map (homOfLE h₂).op ≫ α.appLE V'.1 (α ⁻¹ᵁ V'.1) le_rfl).hom
      (cyclicCoverGenerator N m σ W u)
  rw [Scheme.Hom.map_appLE, ← Scheme.Hom.appLE_map α hW' (homOfLE hV''W).op]
  change _ = ((symSpec N).presheaf.map (homOfLE hV''W).op).hom ((α.appLE _ _ hW').hom _)
  rw [hgen W u hW']

/-- An `X`-endomorphism of `Spec_X Sym(N)` fixing the degree-`m` functions `u` fixes the
generators `u - ⟨u, s⟩`, since it fixes the functions pulled back from `X`. -/
lemma appLE_cyclicCoverGenerator (α : symSpec N ⟶ symSpec N)
    (hα : α ≫ symSpecToBase N = symSpecToBase N) (W : X.Opens)
    (u : ((cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ)).val.obj (op W))
    (h : symSpecToBase N ⁻¹ᵁ W ≤ α ⁻¹ᵁ (symSpecToBase N ⁻¹ᵁ W))
    (hu : (α.appLE _ _ h).hom (symSpecFunction N m W u) = symSpecFunction N m W u) :
    (α.appLE _ _ h).hom (cyclicCoverGenerator N m σ W u) = cyclicCoverGenerator N m σ W u := by
  have hbase : (symSpecToBase N).app W ≫ α.appLE _ _ h = (symSpecToBase N).app W := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_congr_hom hα _ _ _ _
  rw [cyclicCoverGenerator, map_sub, hu]
  exact congrArg (fun k => symSpecFunction N m W u - k.hom (σ.val.app (op W) u)) hbase

/-- For an `m`-th root of unity `ζ`, the scaling automorphism `α_ζ` fixes each generator
`u - ⟨u, s⟩` of `I_s`: it maps `u` to `ζᵐ u = u`. -/
lemma symSpecScaling_cyclicCoverGenerator (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ m = 1) (W : X.Opens)
    (u : ((cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ)).val.obj (op W))
    (h : symSpecToBase N ⁻¹ᵁ W ≤ symSpecScaling N ζ ⁻¹ᵁ (symSpecToBase N ⁻¹ᵁ W)) :
    ((symSpecScaling N ζ).appLE _ _ h).hom (cyclicCoverGenerator N m σ W u) =
      cyclicCoverGenerator N m σ W u := by
  refine appLE_cyclicCoverGenerator N m σ _ (symSpecScaling_toBase N ζ) W u h ?_
  rw [symSpecScaling_symSpecFunction, zpow_natCast, hζ, Units.val_one, globalScalar_one,
    one_smul]

/-- For an `m`-th root of unity `ζ`, the scaling automorphism `α_ζ` preserves `I_s`. -/
theorem cyclicCoverIdeal_le_map_symSpecScaling (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ m = 1) :
    cyclicCoverIdeal N m σ ≤ (cyclicCoverIdeal N m σ).map (symSpecScaling N ζ) :=
  cyclicCoverIdeal_le_map N m σ _ (symSpecScaling_toBase N ζ)
    (symSpecScaling_cyclicCoverGenerator N m σ ζ hζ)

/-- **The action of `μ_m` on the cyclic cover.** For an `m`-th root of unity `ζ` among the global
units of `X`, the `X`-endomorphism `α_ζ` of `Z = Spec_X 𝒜(L, m, s)` induced by the scaling
automorphism of `Spec_X Sym(L⁻¹)`, which preserves `I_s`. -/
@[mmp "def_km2c_cyclic_group_action"]
def cyclicCoverScaling (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ m = 1) : cyclicCover N m σ ⟶ cyclicCover N m σ :=
  Scheme.IdealSheafData.subschemeMap _ _ (symSpecScaling N ζ)
    (cyclicCoverIdeal_le_map_symSpecScaling N m σ ζ hζ)

/-- The endomorphism `α_ζ` of the cyclic cover is the restriction of the scaling automorphism of
`Spec_X Sym(N)` along the closed immersion of the cyclic cover. -/
@[reassoc (attr := simp)]
lemma cyclicCoverScaling_subschemeι (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ m = 1) :
    cyclicCoverScaling N m σ ζ hζ ≫ (cyclicCoverIdeal N m σ).subschemeι =
      (cyclicCoverIdeal N m σ).subschemeι ≫ symSpecScaling N ζ :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The endomorphism `α_ζ` of the cyclic cover is a morphism over `X`. -/
@[reassoc (attr := simp)]
lemma cyclicCoverScaling_toBase (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ m = 1) :
    cyclicCoverScaling N m σ ζ hζ ≫ cyclicCoverToBase N m σ = cyclicCoverToBase N m σ := by
  rw [cyclicCoverToBase, cyclicCoverScaling_subschemeι_assoc, symSpecScaling_toBase]

/-- On the cyclic cover, `α_ζ ≫ α_η = α_{ζη}` for `m`-th roots of unity `ζ` and `η`. -/
@[reassoc (attr := simp)]
lemma cyclicCoverScaling_comp (ζ η : Γ(X, ⊤)ˣ) (hζ : ζ ^ m = 1) (hη : η ^ m = 1) :
    cyclicCoverScaling N m σ ζ hζ ≫ cyclicCoverScaling N m σ η hη =
      cyclicCoverScaling N m σ (ζ * η) (by rw [mul_pow, hζ, hη, one_mul]) := by
  rw [← cancel_mono (cyclicCoverIdeal N m σ).subschemeι]
  simp only [Category.assoc, cyclicCoverScaling_subschemeι, cyclicCoverScaling_subschemeι_assoc,
    symSpecScaling_comp]

/-- The endomorphism `α_1` of the cyclic cover is the identity. -/
@[simp]
lemma cyclicCoverScaling_one : cyclicCoverScaling N m σ 1 (one_pow m) = 𝟙 _ := by
  rw [← cancel_mono (cyclicCoverIdeal N m σ).subschemeι, cyclicCoverScaling_subschemeι,
    symSpecScaling_one, Category.comp_id, Category.id_comp]

/-- **The action of `μ_m` on the cyclic cover**, as the `X`-automorphism `α_ζ` of
`Z = Spec_X 𝒜(L, m, s)` with inverse `α_{ζ⁻¹}`, for an `m`-th root of unity `ζ`. -/
@[mmp "def_km2c_cyclic_group_action"]
def cyclicCoverScalingIso (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ m = 1) :
    cyclicCover N m σ ≅ cyclicCover N m σ where
  hom := cyclicCoverScaling N m σ ζ hζ
  inv := cyclicCoverScaling N m σ ζ⁻¹ (by rw [inv_pow, hζ, inv_one])
  hom_inv_id := by
    rw [cyclicCoverScaling_comp]
    simp only [mul_inv_cancel]
    exact cyclicCoverScaling_one N m σ
  inv_hom_id := by
    rw [cyclicCoverScaling_comp]
    simp only [inv_mul_cancel]
    exact cyclicCoverScaling_one N m σ

/-- The endomorphism `α_ζ` of the cyclic cover is an isomorphism. -/
instance (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ m = 1) : IsIso (cyclicCoverScaling N m σ ζ hζ) :=
  (cyclicCoverScalingIso N m σ ζ hζ).isIso_hom

private lemma app_comp_appLE_of_comp_eq {Z S : Scheme.{u}} (i : Z ⟶ S) (a : Z ⟶ Z) (b : S ⟶ S)
    (hab : a ≫ i = i ≫ b) (U : S.Opens) (ha : i ⁻¹ᵁ U ≤ a ⁻¹ᵁ (i ⁻¹ᵁ U)) (hb : U ≤ b ⁻¹ᵁ U) :
    i.app U ≫ a.appLE (i ⁻¹ᵁ U) (i ⁻¹ᵁ U) ha = b.appLE U U hb ≫ i.app U := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  exact appLE_congr_hom hab _ _ _ _

/-- **`α_ζ^* = σ_ζ` on functions**: the automorphism `α_ζ` of the cyclic cover pulls the image in
`𝒜(L, m, s)` of a local section `x` of `L⁻ⁱ` back to the image of `ζⁱ x`. -/
@[mmp "def_km2c_cyclic_group_action"]
theorem cyclicCoverScaling_cyclicCoverAlgebraIncl (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ m = 1) (i : ℕ)
    (W : X.Opens) (x : ((cyclicCoverSituation N).symmetricAlgebra.piece (i : ℤ)).val.obj (op W))
    (h : cyclicCoverToBase N m σ ⁻¹ᵁ W ≤
      cyclicCoverScaling N m σ ζ hζ ⁻¹ᵁ (cyclicCoverToBase N m σ ⁻¹ᵁ W)) :
    ((cyclicCoverScaling N m σ ζ hζ).appLE _ _ h).hom (cyclicCoverAlgebraIncl N m σ i W x) =
      cyclicCoverAlgebraIncl N m σ i W
        (globalScalar ((ζ ^ (i : ℤ) : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) (op W) • x) := by
  have hb : symSpecToBase N ⁻¹ᵁ W ≤ symSpecScaling N ζ ⁻¹ᵁ (symSpecToBase N ⁻¹ᵁ W) :=
    (symSpecScaling_preimage N ζ W).ge
  have e := app_comp_appLE_of_comp_eq (cyclicCoverIdeal N m σ).subschemeι
    (cyclicCoverScaling N m σ ζ hζ) (symSpecScaling N ζ)
    (cyclicCoverScaling_subschemeι N m σ ζ hζ) (symSpecToBase N ⁻¹ᵁ W) h hb
  refine (congrArg (fun k => k.hom (symSpecFunction N i W x)) e).trans ?_
  exact congrArg ((cyclicCoverIdeal N m σ).subschemeι.app (symSpecToBase N ⁻¹ᵁ W)).hom
    (symSpecScaling_symSpecFunction N ζ i W x hb)

end Descent

end MMP.Mori

end
