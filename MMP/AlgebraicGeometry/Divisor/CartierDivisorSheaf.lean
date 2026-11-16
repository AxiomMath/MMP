module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import MMP.Attr
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import MMP.AlgebraicGeometry.Divisor.LocalEquation
public import StacksFrontier.AlgebraicGeometry.Coherent.SheafHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Divisors.RankLocalGenerators

/-!
# The invertible sheaf `𝒪_X(D)` of a Cartier divisor

Let `D` be a Cartier divisor on a scheme `X`, an element of the Stacks project's group
`X.CartierDivisor` of global sections of `𝒦*/𝒪*`, with local equations `f_i ∈ 𝒦*(U_i)` on an
open cover `{U_i}`. The sheaf `𝒪_X(D)` is the sub-`𝒪_X`-module of the sheaf of total quotient
rings `𝒦_X` generated on `U_i` by `f_i⁻¹`. It is well defined because two local equations on the
same open differ by a unit of `𝒪_X`.

The Stacks project defines `𝒪_X(D)` only for effective Cartier divisors, as the dual
`Stacks.Divisors.invertibleSheaf'` of the ideal sheaf, so the sheaf of an arbitrary Cartier
divisor is defined here.

## Main definitions

* `MMP.CartierDivisor.sheaf D`: the sheaf `𝒪_X(D)`, an object of `X.Modules`.
* `MMP.CartierDivisor.sheafSubmodule D`: `𝒪_X(D)` as a sub-`𝒪_X`-module of `𝒦_X`.
* `MMP.CartierDivisorSheaf.Mem D V s`: the section `s` of `𝒦_X` over `V` lies in `𝒪_X(D)`.
* `MMP.CartierDivisorSheaf.frameIso`: the trivialisation `𝒪_U ≅ 𝒪_X(D)|_U`, `a ↦ a f⁻¹`, given
  by a local equation `f` of `D` on `U`.

## Main results

* `MMP.CartierDivisorSheaf.mem_iff`: over an open where `D` has the local equation `f`, the
  sections of `𝒪_X(D)` are the multiples of `f⁻¹`.
* `MMP.CartierDivisorSheaf.exists_units_eq_mul_inv`: two local equations of a Cartier divisor on
  the same open differ by a unit of `𝒪_X`.
* `MMP.CartierDivisor.isFiniteLocallyFreeOfRank_sheaf`: `𝒪_X(D)` is finite locally free of rank
  one.
* `MMP.CartierDivisor.exists_transition`: the local generators satisfy `g⁻¹ = (f / g) · f⁻¹`.

## Implementation notes

`𝒦_X` is an `𝒪_X`-module by restriction of scalars along `𝒪_X ⟶ 𝒦_X`, and `𝒪_X(D)` is a
`SheafOfModules.Submodule` of it. A section `s` of `𝒦_X` over `V` belongs to `𝒪_X(D)` when
`s · f` is a section of `𝒪_X` for every local equation `f` of `D` on every open `W ⊆ V`. Asking
this of every local equation, rather than of one chosen cover, makes the definition independent
of choices and the membership condition visibly local.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Appendix B.4.4 and §1.5.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open MMP.Intersection

universe u

namespace MMP

variable {X : Scheme.{u}}

namespace CartierDivisorSheaf

/-- The sheaf of total quotient rings `𝒦_X` as a sheaf of (not necessarily commutative) rings. -/
abbrev totalQuotientRingCatSheaf (X : Scheme.{u}) :
    Sheaf (Opens.grothendieckTopology X) RingCat.{u} :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).obj
    X.totalQuotientSheaf

/-- The inclusion `𝒪_X ⟶ 𝒦_X` as a morphism of sheaves of rings. -/
abbrev toTotalQuotientRingCatSheaf (X : Scheme.{u}) :
    X.ringCatSheaf ⟶ totalQuotientRingCatSheaf X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
    X.toTotalQuotientSheaf

/-- The sheaf of total quotient rings `𝒦_X` as an `𝒪_X`-module. -/
def totalQuotientModule (X : Scheme.{u}) : X.Modules :=
  (SheafOfModules.restrictScalars (toTotalQuotientRingCatSheaf X)).obj (SheafOfModules.unit _)

/-- The inclusion `Γ(X, W) → 𝒦_X(W)` of sections of `𝒪_X` into sections of `𝒦_X`. -/
abbrev toK (W : X.Opens) : Γ(X, W) →+* X.totalQuotientSheaf.obj.obj (op W) :=
  (X.toTotalQuotientSheaf.hom.app (op W)).hom

/-- Restriction of sections of `𝒦_X`. -/
abbrev resK {V W : X.Opens} (h : W ≤ V) :
    X.totalQuotientSheaf.obj.obj (op V) →+* X.totalQuotientSheaf.obj.obj (op W) :=
  (X.totalQuotientSheaf.obj.map (homOfLE h).op).hom

/-- Restricting the image of a section of `𝒪_X` in `𝒦_X` is the image of its restriction. -/
theorem resK_toK {V W : X.Opens} (h : W ≤ V) (a : Γ(X, V)) :
    resK h (toK V a) = toK W (X.presheaf.map (homOfLE h).op a) := by
  simp only [resK, toK]
  exact (NatTrans.naturality_apply X.toTotalQuotientSheaf.hom (homOfLE h).op a).symm

/-- Restriction of sections of `𝒦_X` is transitive. -/
theorem resK_resK {U V W : X.Opens} (h : W ≤ V) (h' : V ≤ U)
    (s : X.totalQuotientSheaf.obj.obj (op U)) :
    resK h (resK h' s) = resK (h.trans h') s := by
  simp only [resK, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- Restriction of sections of `𝒦_X` to the same open is the identity. -/
theorem resK_id {V : X.Opens} (s : X.totalQuotientSheaf.obj.obj (op V)) :
    resK (le_refl V) s = s := by
  simp [resK, show homOfLE (le_refl V) = 𝟙 V from rfl]

/-- Sections of `𝒪_X` embed into sections of `𝒦_X`. -/
theorem toK_injective (W : X.Opens) : Function.Injective (toK (X := X) W) := by
  have : Mono X.toTotalQuotientSheaf := X.mono_toTotalQuotientSheaf
  have : Mono (X.toTotalQuotientSheaf.hom.app (op W)) :=
    (NatTrans.mono_iff_mono_app _).mp
      (Functor.map_mono (TopCat.Sheaf.forget CommRingCat.{u} X) X.toTotalQuotientSheaf) (op W)
  exact ConcreteCategory.injective_of_mono_of_preservesPullback
    (X.toTotalQuotientSheaf.hom.app (op W))

/-- Being a section of `𝒪_X` inside `𝒦_X` is a local property. -/
theorem mem_range_toK_of_locally {W : X.Opens} (t : X.totalQuotientSheaf.obj.obj (op W))
    (ht : ∀ x ∈ W, ∃ (W' : X.Opens) (h : W' ≤ W), x ∈ W' ∧ ∃ a, toK W' a = resK h t) :
    ∃ a, toK W a = t := by
  choose W' hW' hxW a ha using ht
  let V : W → X.Opens := fun x ↦ W' x.1 x.2
  have hcover : W ≤ iSup V := fun x hx ↦ Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW _ _⟩
  have hc : TopCat.Presheaf.IsCompatible X.sheaf.obj V (fun x ↦ a x.1 x.2) := by
    intro x y
    apply toK_injective
    erw [← resK_toK (inf_le_left : V x ⊓ V y ≤ V x), ← resK_toK (inf_le_right : V x ⊓ V y ≤ V y)]
    rw [ha, ha, resK_resK, resK_resK]
  obtain ⟨b, hb, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf V W
    (fun x ↦ homOfLE (hW' x.1 x.2)) hcover _ hc
  refine ⟨b, TopCat.Sheaf.eq_of_locally_eq' X.totalQuotientSheaf V W
    (fun x ↦ homOfLE (hW' x.1 x.2)) hcover _ _ fun x ↦ ?_⟩
  change resK (hW' x.1 x.2) (toK W b) = resK (hW' x.1 x.2) t
  erw [resK_toK (hW' x.1 x.2) b, hb x]
  exact ha _ _

/-- Two local equations of a Cartier divisor on the same open differ by a unit of `𝒪_X`. -/
theorem exists_units_eq_mul_inv {D : X.CartierDivisor} {W : X.Opens}
    {f g : (X.totalQuotientSheaf.obj.obj (op W))ˣ}
    (hf : IsLocalEquationOn D W f) (hg : IsLocalEquationOn D W g) :
    ∃ u : Γ(X, W)ˣ, Units.map (toK W).toMonoidHom u = f * g⁻¹ := by
  have key : ∀ {f g : (X.totalQuotientSheaf.obj.obj (op W))ˣ}, IsLocalEquationOn D W f →
      IsLocalEquationOn D W g → ∃ a : Γ(X, W), toK W a = ↑(f * g⁻¹) := by
    intro f g hf hg
    refine mem_range_toK_of_locally _ fun x hx ↦ ?_
    obtain ⟨W', h, hxW', u, hu⟩ := hg.exists_unit_mul_eq hf hx
    refine ⟨W', h, hxW', u, ?_⟩
    change toTotalQuotient W' (u : Γ(X, W')) =
      X.totalQuotientSheaf.obj.map (homOfLE h).op (↑f * ↑g⁻¹)
    rw [map_mul, ← hu, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  obtain ⟨a, ha⟩ := key hf hg
  obtain ⟨b, hb⟩ := key hg hf
  have hab : a * b = 1 := toK_injective W (by
    rw [map_mul, ha, hb, map_one, ← Units.val_mul]
    simp [mul_assoc])
  exact ⟨⟨a, b, hab, mul_comm b a ▸ hab⟩, Units.ext ha⟩

/-- A local equation of `D` on `V` restricts to a local equation on `W ⊆ V`. -/
theorem isLocalEquation_restrict {D : X.CartierDivisor} {V W : X.Opens} (h : W ≤ V)
    {f : (X.totalQuotientSheaf.obj.obj (op V))ˣ} (hf : IsLocalEquationOn D V f) :
    IsLocalEquationOn D W (Units.map (resK h).toMonoidHom f) :=
  isLocalEquationOn_resUnit (homOfLE h) hf

/-- A section `s` of `𝒦_X` over `V` lies in `𝒪_X(D)` if `s · f` is a section of `𝒪_X` for every
local equation `f` of `D` on every open `W ⊆ V`. -/
def Mem (D : X.CartierDivisor) (V : X.Opens) (s : X.totalQuotientSheaf.obj.obj (op V)) : Prop :=
  ∀ (W : X.Opens) (h : W ≤ V) (f : (X.totalQuotientSheaf.obj.obj (op W))ˣ),
    IsLocalEquationOn D W f → ∃ a : Γ(X, W), toK W a = resK h s * f

/-- The zero section of `𝒦_X` lies in `𝒪_X(D)`. -/
theorem Mem.zero (D : X.CartierDivisor) (V : X.Opens) : Mem D V 0 :=
  fun W _ _ _ ↦ ⟨0, by simp⟩

/-- The sections of `𝒪_X(D)` are closed under addition. -/
theorem Mem.add {D : X.CartierDivisor} {V : X.Opens} {s t : X.totalQuotientSheaf.obj.obj (op V)}
    (hs : Mem D V s) (ht : Mem D V t) : Mem D V (s + t) := by
  intro W h f hf
  obtain ⟨a, ha⟩ := hs W h f hf
  obtain ⟨b, hb⟩ := ht W h f hf
  exact ⟨a + b, by rw [map_add, ha, hb, map_add, add_mul]⟩

/-- The sections of `𝒪_X(D)` are closed under multiplication by sections of `𝒪_X`. -/
theorem Mem.mul_toK {D : X.CartierDivisor} {V : X.Opens} {s : X.totalQuotientSheaf.obj.obj (op V)}
    (hs : Mem D V s) (c : Γ(X, V)) : Mem D V (toK V c * s) := by
  intro W h f hf
  obtain ⟨a, ha⟩ := hs W h f hf
  exact ⟨X.presheaf.map (homOfLE h).op c * a, by rw [map_mul, ha, map_mul, resK_toK, mul_assoc]⟩

/-- The restriction of a section of `𝒪_X(D)` to a smaller open lies in `𝒪_X(D)`. -/
theorem Mem.res {D : X.CartierDivisor} {V V' : X.Opens} (h : V' ≤ V)
    {s : X.totalQuotientSheaf.obj.obj (op V)} (hs : Mem D V s) : Mem D V' (resK h s) := by
  intro W h' f hf
  obtain ⟨a, ha⟩ := hs W (h'.trans h) f hf
  exact ⟨a, by rw [ha, resK_resK]⟩

/-- A section of `𝒦_X` that lies in `𝒪_X(D)` locally around every point lies in `𝒪_X(D)`. -/
theorem Mem.of_locally {D : X.CartierDivisor} {V : X.Opens}
    {s : X.totalQuotientSheaf.obj.obj (op V)}
    (hs : ∀ x ∈ V, ∃ (V' : X.Opens) (h : V' ≤ V), x ∈ V' ∧ Mem D V' (resK h s)) : Mem D V s := by
  intro W h f hf
  apply mem_range_toK_of_locally
  intro x hx
  obtain ⟨V', hV', hxV', hs'⟩ := hs x (h hx)
  refine ⟨W ⊓ V', inf_le_left, ⟨hx, hxV'⟩, ?_⟩
  obtain ⟨a, ha⟩ := hs' (W ⊓ V') inf_le_right _ (isLocalEquation_restrict inf_le_left hf)
  refine ⟨a, ?_⟩
  rw [ha, map_mul, resK_resK, resK_resK]
  rfl

/-- If `f` is a local equation of `D` on `U`, then `f⁻¹` lies in `𝒪_X(D)` over `U`. -/
theorem mem_inv {D : X.CartierDivisor} {U : X.Opens} {f : (X.totalQuotientSheaf.obj.obj (op U))ˣ}
    (hf : IsLocalEquationOn D U f) :
    Mem D U ((f⁻¹ : (X.totalQuotientSheaf.obj.obj (op U))ˣ) :
      X.totalQuotientSheaf.obj.obj (op U)) := by
  intro W h g hg
  obtain ⟨u, hu⟩ := exists_units_eq_mul_inv hg (isLocalEquation_restrict h hf)
  refine ⟨u, ?_⟩
  have := congrArg Units.val hu
  simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_mul, Units.coe_map_inv] at this
  exact this.trans (mul_comm _ _)

/-- On an open `V ⊆ U`, where `f` is a local equation of `D` on `U`, the sections of `𝒪_X(D)` are
the multiples of `f⁻¹`. -/
theorem mem_iff {D : X.CartierDivisor} {U V : X.Opens} {f : (X.totalQuotientSheaf.obj.obj (op U))ˣ}
    (hf : IsLocalEquationOn D U f) (h : V ≤ U)
    (s : X.totalQuotientSheaf.obj.obj (op V)) :
    Mem D V s ↔ ∃ a : Γ(X, V), toK V a * resK h ↑f⁻¹ = s := by
  constructor
  · intro hs
    obtain ⟨a, ha⟩ := hs V le_rfl _ (isLocalEquation_restrict h hf)
    refine ⟨a, ?_⟩
    rw [ha, resK_id, mul_assoc]
    have : (resK h) (f : X.totalQuotientSheaf.obj.obj (op U)) * resK h ↑f⁻¹ = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    exact (congrArg (s * ·) this).trans (mul_one s)
  · rintro ⟨a, rfl⟩
    exact ((mem_inv hf).res h).mul_toK a

end CartierDivisorSheaf

namespace CartierDivisor

open CartierDivisorSheaf

/-- The sub-`𝒪_X`-module `𝒪_X(D)` of `𝒦_X`, as a submodule of the sheaf of modules `𝒦_X`. -/
@[mmp "def_p01a_line_bundle_of_divisor"]
def sheafSubmodule (D : X.CartierDivisor) : (totalQuotientModule X).Submodule where
  obj V :=
    { carrier := {s | Mem D V.unop s}
      add_mem' := Mem.add
      zero_mem' := Mem.zero D V.unop
      smul_mem' := fun c _ hs ↦ hs.mul_toK c }
  map {V V'} g := fun _ hs ↦ hs.res (leOfHom g.unop)
  isSheaf {V} s hs := by
    refine Mem.of_locally fun x hx ↦ ?_
    obtain ⟨V', g, hg, hxV'⟩ := hs x hx
    exact ⟨V', leOfHom g, hxV', hg⟩

/-- **The sheaf `𝒪_X(D)`**: the sub-`𝒪_X`-module of `𝒦_X` generated, on an open `U` where `D`
has a local equation `f`, by `f⁻¹`. -/
@[mmp "def_p01a_line_bundle_of_divisor"]
def sheaf (D : X.CartierDivisor) : X.Modules :=
  (sheafSubmodule D).toSheafOfModules

end CartierDivisor

namespace CartierDivisorSheaf

section Frame

variable {D : X.CartierDivisor} {U V : X.Opens} {f : (X.totalQuotientSheaf.obj.obj (op U))ˣ}
  {g : (X.totalQuotientSheaf.obj.obj (op V))ˣ}

/-- The local generator `f⁻¹` of `𝒪_X(D)` over an open `V ⊆ U`, as a section of the restriction
of `𝒪_X(D)` to `U`. -/
def frame (hf : IsLocalEquationOn D U f) (Y : (Over U)ᵒᵖ) :
    ((CartierDivisor.sheaf D).over U).val.obj Y :=
  ⟨resK (leOfHom Y.unop.hom) ↑f⁻¹, (mem_inv hf).res _⟩

/-- Multiplication by the local generator `f⁻¹`, from `𝒪_X` to `𝒪_X(D)` over an open `V ⊆ U`. -/
def frameMap (hf : IsLocalEquationOn D U f) (Y : (Over U)ᵒᵖ) :
    (X.ringCatSheaf.over U).obj.obj Y →ₗ[(X.ringCatSheaf.over U).obj.obj Y]
      ((CartierDivisor.sheaf D).over U).val.obj Y :=
  LinearMap.toSpanSingleton _ _ (frame hf Y)

/-- Multiplication by the local generator `f⁻¹` is a bijection from `𝒪_X` to `𝒪_X(D)` over every
open `V ⊆ U`. -/
theorem frameMap_bijective (hf : IsLocalEquationOn D U f) (Y : (Over U)ᵒᵖ) :
    Function.Bijective (frameMap hf Y) := by
  refine ⟨fun a b hab ↦ toK_injective Y.unop.left ?_, ?_⟩
  · exact ((Units.isUnit f⁻¹).map (resK (leOfHom Y.unop.hom))).mul_right_cancel
      (congrArg Subtype.val hab)
  · rintro ⟨s, hs⟩
    obtain ⟨a, ha⟩ := (mem_iff hf (leOfHom Y.unop.hom) s).mp hs
    exact ⟨a, Subtype.ext ha⟩

/-- The trivialisation `𝒪_U ≅ 𝒪_X(D)|_U`, `a ↦ a f⁻¹`, given by a local equation `f` of `D` on
`U`. -/
@[mmp "lem_p01a_line_bundle_of_divisor_invertible"]
def frameIso (hf : IsLocalEquationOn D U f) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ≅ (CartierDivisor.sheaf D).over U :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun Y ↦ (LinearEquiv.ofBijective (frameMap hf Y) (frameMap_bijective hf Y)).toModuleIso)
      (by
        intro Y Y' g
        refine ModuleCat.hom_ext (LinearMap.ext fun a ↦ Subtype.ext ?_)
        change toK Y'.unop.left (X.presheaf.map (homOfLE (leOfHom g.unop.left)).op a) *
            resK (leOfHom Y'.unop.hom) ↑f⁻¹ =
          resK (leOfHom g.unop.left) (toK Y.unop.left a * resK (leOfHom Y.unop.hom) ↑f⁻¹)
        rw [map_mul, resK_resK]
        exact congrArg (· * _) (resK_toK _ a).symm))

/-- If `u = f / g` in `𝒦(U ∩ V)`, then `g⁻¹ = u f⁻¹`. -/
theorem resK_inv_eq_of_toK_eq (u : Γ(X, U ⊓ V))
    (hu : toK (U ⊓ V) u = resK inf_le_left (f : X.totalQuotientSheaf.obj.obj (op U)) *
      resK inf_le_right ↑g⁻¹) :
    resK inf_le_right ↑g⁻¹ = toK (U ⊓ V) u * resK inf_le_left ↑f⁻¹ := by
  rw [hu, mul_comm (resK _ _) (resK _ _), mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]

end Frame

end CartierDivisorSheaf

namespace CartierDivisor

open CartierDivisorSheaf

/-- `𝒪_X(D)` is an invertible sheaf: it is finite locally free of rank one. -/
@[mmp "lem_p01a_line_bundle_of_divisor_invertible"]
instance isFiniteLocallyFreeOfRank_sheaf (D : X.CartierDivisor) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (CartierDivisor.sheaf D) 1 := by
  choose U hxU f hf using exists_isLocalEquationOn D
  refine Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_of_free_iso 1 U ?_ fun x ↦
    coproductUniqueIso _ ≪≫ frameIso (hf x)
  exact (Opens.coversTop_iff X U).2 (top_unique fun x _ ↦ Opens.mem_iSup.2 ⟨x, hxU x⟩)

/-- `𝒪_X(D)` is of finite presentation. -/
theorem isFinitePresentation_sheaf (D : X.CartierDivisor) :
    (CartierDivisor.sheaf D).IsFinitePresentation := by
  haveI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (CartierDivisor.sheaf D) 1
  haveI : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (CartierDivisor.sheaf D) :=
    ⟨AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.exists_isFiniteLocallyFreeData
      (M := (CartierDivisor.sheaf D))⟩
  exact Stacks.FiniteLocallyFree.isFinitePresentation (CartierDivisor.sheaf D)

/-- The dual of `𝒪_X(D)` is quasi-coherent. -/
instance isQuasicoherent_dualSheaf_sheaf (D : X.CartierDivisor) :
    (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
      (CartierDivisor.sheaf D)).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.InternalHomModules.isQuasicoherent_dualSheaf _
    (isFinitePresentation_sheaf D)

/-- On an open `V` contained in an open `U` on which `f` is a local equation of `D`, the sections
of `𝒪_X(D)` are exactly the multiples `a f⁻¹`, `a ∈ Γ(X, V)`. -/
@[mmp "lem_p01a_line_bundle_of_divisor_invertible"]
theorem mem_sheafSubmodule_iff {U V : X.Opens} (D : X.CartierDivisor)
    {f : (X.totalQuotientSheaf.obj.obj (op U))ˣ} (hf : IsLocalEquationOn D U f) (h : V ≤ U)
    (s : (totalQuotientModule X).val.obj (op V)) :
    s ∈ (CartierDivisor.sheafSubmodule D).obj (op V) ↔
      ∃ a : Γ(X, V), toK V a * resK h ↑f⁻¹ = (show X.totalQuotientSheaf.obj.obj (op V) from s) :=
  mem_iff hf h s

/-- **Transition functions.** If `f` and `g` are local equations of `D` on `U` and `V`, then on
`U ∩ V` the quotient `f / g` is a unit `u` of `𝒪_X`, and the local generators of `𝒪_X(D)` are
related by `g⁻¹ = u · f⁻¹`: the transition function from the trivialisation by `g⁻¹` to the
trivialisation by `f⁻¹` is `f / g`. -/
theorem exists_transition (D : X.CartierDivisor) {U V : X.Opens}
    {f : (X.totalQuotientSheaf.obj.obj (op U))ˣ} {g : (X.totalQuotientSheaf.obj.obj (op V))ˣ}
    (hf : IsLocalEquationOn D U f) (hg : IsLocalEquationOn D V g) :
    ∃ u : Γ(X, U ⊓ V)ˣ,
      toK (U ⊓ V) u = resK inf_le_left (f : X.totalQuotientSheaf.obj.obj (op U)) *
          resK inf_le_right ↑g⁻¹ ∧
        resK inf_le_right ↑g⁻¹ = toK (U ⊓ V) u * resK inf_le_left ↑f⁻¹ := by
  obtain ⟨u, hu⟩ := exists_units_eq_mul_inv (isLocalEquation_restrict (inf_le_left : U ⊓ V ≤ U) hf)
    (isLocalEquation_restrict (inf_le_right : U ⊓ V ≤ V) hg)
  have hu' := congrArg Units.val hu
  simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_mul, Units.coe_map_inv] at hu'
  exact ⟨u, hu', resK_inv_eq_of_toK_eq _ hu'⟩

end CartierDivisor

end MMP
