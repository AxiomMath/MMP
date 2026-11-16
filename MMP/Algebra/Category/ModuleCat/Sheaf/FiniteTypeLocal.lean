module

public import MMP.Algebra.Category.ModuleCat.Sheaf.FiniteTypePushforward
public import MMP.CategoryTheory.Sites.OverPost
public import Mathlib.CategoryTheory.Sites.CoversTop.Over
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits

/-!
# Being of finite type is a local property

Let `M` be a sheaf of modules over a sheaf of rings `R` on a small site `C`. For `Y : C` and
`Z : Over Y`, the iterated restriction `(M|_Y)|_Z` is a sheaf on `(C/Y)/Z`, which is equivalent
to `C/Z.left` (`CategoryTheory.Over.iteratedSliceEquiv`); along this equivalence it is the
restriction `M|_{Z.left}`. Generating sections of `(M|_Y)|_Z` therefore give generating sections
of `M|_{Z.left}`. Consequently, if `M|_{Yᵢ}` is of finite type for a family `Yᵢ` covering the
terminal object, then `M` is of finite type: the local generators of the `M|_{Yᵢ}` assemble.

## Main definitions

* `MMP.GeneratingSections.ofOverOver`: generating sections of `M|_{Z.left}` from generating
  sections of `(M|_Y)|_Z`.
* `MMP.freeGeneratingSections`: the basis sections of a free module.

## Main results

* `MMP.isFiniteType_free`: a free module of finite rank is of finite type.
* `MMP.isFiniteType_of_coversTop`: `M` is of finite type if its restrictions to a covering
  family of the terminal object are.
-/

@[expose] public section

open CategoryTheory Limits SheafOfModules

namespace MMP

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{0}}
  [HasPullbacks C]

section

variable {Y : C} (Z : Over Y)

/-- The functor `Over Z.left ⥤ Over Z` of the iterated slice equivalence. -/
abbrev sliceBack : Over Z.left ⥤ Over Z := Z.iteratedSliceBackward

/-- The identification of the ring sheaf `R|_{Z.left}` with the pushforward of `(R|_Y)|_Z`. -/
noncomputable def overOverRingHom : R.over Z.left ⟶
    ((sliceBack Z).sheafPushforwardContinuous RingCat.{0} (J.over Z.left)
      ((J.over Y).over Z)).obj ((R.over Y).over Z) := 𝟙 _

set_option backward.isDefEq.respectTransparency false in
/-- Pushforward of sheaves of modules along `overOverRingHom Z` is a left adjoint. -/
instance isLeftAdjoint_pushforward_overOverRingHom :
    (SheafOfModules.pushforward.{0} (overOverRingHom (R := R) Z)).IsLeftAdjoint := by
  haveI : (sliceBack Z).IsLeftAdjoint := ⟨_, ⟨Z.iteratedSliceEquiv.symm.toAdjunction⟩⟩
  haveI : IsIso (overOverRingHom (R := R) Z) := inferInstanceAs (IsIso (𝟙 _))
  exact isLeftAdjoint_pushforward_of_isIso _

/-- The pushforward of `(M|_Y)|_Z` along the iterated slice equivalence is `M|_{Z.left}`. -/
noncomputable def overOverIso (M : SheafOfModules.{0} R) :
    (SheafOfModules.pushforward.{0} (overOverRingHom (R := R) Z)).obj ((M.over Y).over Z) ≅
      M.over Z.left :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk (fun _ ↦ Iso.refl _)

/-- Generating sections of `(M|_Y)|_Z` give generating sections of `M|_{Z.left}`. -/
noncomputable def GeneratingSections.ofOverOver {M : SheafOfModules.{0} R}
    (G : ((M.over Y).over Z).GeneratingSections) : (M.over Z.left).GeneratingSections :=
  (G.map (SheafOfModules.pushforward.{0} (overOverRingHom (R := R) Z)) (Iso.refl _)).ofEpi
    (overOverIso Z M).hom

/-- Finitely many generating sections of `(M|_Y)|_Z` give finitely many generating sections of
`M|_{Z.left}`. -/
instance {M : SheafOfModules.{0} R} (G : ((M.over Y).over Z).GeneratingSections)
    [G.IsFiniteType] : (GeneratingSections.ofOverOver Z G).IsFiniteType where
  finite := inferInstanceAs (Finite G.I)

end

/-- **Finite type is local.** A sheaf of modules whose restrictions to the members of a family
covering the terminal object are of finite type is of finite type. -/
theorem isFiniteType_of_coversTop (M : SheafOfModules.{0} R) {I : Type} {Y : I → C}
    (hY : J.CoversTop Y) (hM : ∀ i, SheafOfModules.IsFiniteType.{0} (M.over (Y i))) :
    SheafOfModules.IsFiniteType.{0} M := by
  choose P hP using fun i => (hM i).exists_localGeneratorsData
  let Q : M.LocalGeneratorsData :=
    { I := Σ i, (P i).I
      X := fun j => ((P j.1).X j.2).left
      coversTop := hY.over fun i => (P i).coversTop
      generators := fun j => GeneratingSections.ofOverOver _ ((P j.1).generators j.2) }
  haveI : Q.IsFiniteType := ⟨fun j => by
    haveI := LocalGeneratorsData.IsFiniteType.isFiniteType (p := P j.1) j.2
    exact inferInstanceAs (GeneratingSections.ofOverOver _ ((P j.1).generators j.2)).IsFiniteType⟩
  exact ⟨⟨Q.shrink, ⟨fun j => LocalGeneratorsData.IsFiniteType.isFiniteType (p := Q) _⟩⟩⟩

/-- The basis sections of a free sheaf of modules generate it. -/
noncomputable def freeGeneratingSections (I : Type) :
    (SheafOfModules.free (R := R) I).GeneratingSections where
  I := I
  s := (SheafOfModules.free I).freeHomEquiv (𝟙 _)
  epi := by rw [Equiv.symm_apply_apply]; infer_instance

/-- A free sheaf of modules of finite rank is of finite type. -/
theorem isFiniteType_free [HasBinaryProducts C] (I : Type) [Finite I] :
    SheafOfModules.IsFiniteType.{0} (SheafOfModules.free (R := R) I) :=
  haveI : (freeGeneratingSections (R := R) I).IsFiniteType := ⟨inferInstanceAs (Finite I)⟩
  ⟨⟨(freeGeneratingSections (R := R) I).localGeneratorsData, ⟨fun _ => ⟨inferInstanceAs (Finite I)⟩⟩⟩⟩

end MMP
