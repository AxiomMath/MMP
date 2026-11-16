module

public import MMP.AlgebraicTopology.CapProduct.RestrictionNbhd
public import MMP.AlgebraicTopology.CapProduct.SupportRetraction
public import MMP.AlgebraicTopology.PoincareDuality.DualClassSupport
public import MMP.AlgebraicTopology.FundamentalClass.Restriction
/-!
# The cap product with supports and restriction to an open subset

Let `X` be closed in a space `Y`, `U ⊆ Y` open with inclusion `j`, `c ∈ H^j(Y, Y - X)` and
`a ∈ H_k Y`. Then `(c ∩ a)|_{X ∩ U} = j^* c ∩ a|_U` in `H_{k-j}(X ∩ U)` (Fulton §19.1; [BT] 2.2).

For a proper retraction `r : N → X` of a closed neighbourhood, the restriction of `r_* (c ∩_N a)`
to `X ∩ U` is the push-forward of the restriction of `c ∩_N a` to `V = r⁻¹(X ∩ U)`, an open
subset of `N` which need not lie in `U`, but lies in `U' = U ∪ (Y - X)`. In `U'`, the set
`X ∩ U` is closed, and (normality) has closed neighbourhoods `L ⊆ int L₂ ⊆ L₂ ⊆ U ∩ V`. The
neighbourhood cap product commutes with restriction to `U'`
(`pushforward_opensInterMap_restrict_capProductNbhd`) and does not change on shrinking the
neighbourhood to `L₂`; then one more restriction (to `U` inside `U'`) and the projection formula
for the homeomorphism of `U` with its copy in `U'` identify it with the cap product of `U`
computed along the retraction `r|_L`.

## Main results

* `MMP.borelMooreHomology.restrict_capProductNbhd_eq_pushforward`: the
  restriction of `c ∩_N a` to an open `V ⊆ N ∩ U'` is the push-forward of `c|_{U'} ∩_L a|_{U'}`
  for a closed neighbourhood `L ⊆ V` of `X ∩ U'` in `U'`.
* `MMP.borelMooreHomology.pushforward_opensInterMap_restrict_capProductSupport`:
  `(c ∩ a)|_{X ∩ U} = j^* c ∩ a|_U`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* W. Fulton, R. MacPherson, *Categorical framework for the study of singular spaces*, 2.2.
-/

@[expose] public noncomputable section

open CategoryTheory Set Topology

universe u

namespace MMP

open MMP

namespace borelMooreHomology

open MMP.borelMooreHomology

variable (R : Type u) [CommRing R]

/-- Restriction to an open subset that is the whole space, pushed back, is the identity. -/
lemma pushforward_inclHom_restrict_of_eq_top {Z : TopCat.{u}} [T2Space Z]
    {O : TopologicalSpace.Opens Z} (hO : O = ⊤) (hp : IsProperMap (inclHom O)) (i : ℤ)
    (a : borelMooreHomology R (ModuleCat.of R R) Z i) :
    (pushforward R (ModuleCat.of R R) (inclHom O) hp i).hom
      ((restrict R (ModuleCat.of R R) O i).hom a) = a := by
  subst hO
  exact pushforward_inclHom_top_restrict R i a

/-- Push-forward along `f ≫ g` is push-forward along `f` followed by push-forward along `g`. -/
lemma pushforward_comp_apply {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsProperMap f)
    (hg : IsProperMap g) (hfg : IsProperMap (f ≫ g)) (i : ℤ)
    (a : borelMooreHomology R (ModuleCat.of R R) X i) :
    (pushforward R (ModuleCat.of R R) g hg i).hom
        ((pushforward R (ModuleCat.of R R) f hf i).hom a) =
      (pushforward R (ModuleCat.of R R) (f ≫ g) hfg i).hom a := by
  rw [pushforward_comp R (ModuleCat.of R R) f g hf hg i]
  rfl

/-- Push-forwards along equal proper maps agree. -/
lemma pushforward_apply_congr {X Y : TopCat.{u}} {f g : X ⟶ Y} (hfg : f = g) (hf : IsProperMap f)
    (hg : IsProperMap g) (i : ℤ) (a : borelMooreHomology R (ModuleCat.of R R) X i) :
    (pushforward R (ModuleCat.of R R) f hf i).hom a =
      (pushforward R (ModuleCat.of R R) g hg i).hom a := by
  subst hfg
  rfl

/-- Push-forward along a proper map equal to the identity is the identity. -/
lemma pushforward_id_apply' {X : TopCat.{u}} (f : X ⟶ X) (hf : IsProperMap f) (h : f = 𝟙 X)
    (i : ℤ) (a : borelMooreHomology R (ModuleCat.of R R) X i) :
    (pushforward R (ModuleCat.of R R) f hf i).hom a = a := by
  subst h
  rw [pushforward_id]
  rfl

/-- If `f` is the identity after a homeomorphism `e` (`e ≫ f = 𝟙`), `f_* (e_* x) = x`; so a
class `b` with `e_* b = y` is `f_* y`. -/
lemma eq_pushforward_of_pushforward_eq {X Y : TopCat.{u}} (e : X ⟶ Y) (f : Y ⟶ X)
    (he : IsProperMap e) (hf : IsProperMap f) (hef : e ≫ f = 𝟙 X) (i : ℤ)
    {b : borelMooreHomology R (ModuleCat.of R R) X i}
    {y : borelMooreHomology R (ModuleCat.of R R) Y i}
    (h : (pushforward R (ModuleCat.of R R) e he i).hom b = y) :
    b = (pushforward R (ModuleCat.of R R) f hf i).hom y := by
  rw [← h, pushforward_comp_apply R e f he hf (hef ▸ (by simp [isProperMap_id])),
    pushforward_id_apply' R _ _ hef]

section opensInter

variable {Y : TopCat.{u}} (U : TopologicalSpace.Opens Y) (N : Set Y)

/-- The inverse of `opensInterMap`. -/
def opensInterInv : TopCat.of (setInter U N) ⟶ TopCat.of (opensInter U N) :=
  TopCat.ofHom ((opensInterHomeo U N).symm : C(setInter U N, opensInter U N))

/-- The map `opensInterInv U N` is proper. -/
lemma isProperMap_opensInterInv : IsProperMap (opensInterInv U N) :=
  (opensInterHomeo U N).symm.isProperMap

/-- `opensInterInv U N` is a left inverse of `opensInterMap U N`. -/
lemma opensInterMap_opensInterInv : opensInterMap U N ≫ opensInterInv U N = 𝟙 _ := rfl

end opensInter

section nbhd

variable {Y : TopCat.{u}} [T2Space Y] (U' : TopologicalSpace.Opens Y) {N : Set Y}
  (V : TopologicalSpace.Opens (TopCat.of N)) (hV : V ≤ opensInter U' N)
  {L : Set (TopCat.of U')} (hL : IsClosed L) (hLN : L ⊆ setInter U' N)
  (hLV : ∀ l : L, (⟨l.1.1, hLN l.2⟩ : N) ∈ V)

/-- A set `L ⊆ N ∩ U'`, closed in `U'`, mapping into an open `V ⊆ N ∩ U'` of `N`. -/
def nbhdToOpens : TopCat.of L ⟶ TopCat.of V :=
  TopCat.ofHom ⟨fun l ↦ ⟨⟨l.1.1, hLN l.2⟩, hLV l⟩,
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _⟩

omit [T2Space Y] in
include hV hL in
/-- The inclusion `nbhdToOpens` of a set `L` closed in `U'` into `V` is proper. -/
lemma isProperMap_nbhdToOpens : IsProperMap (nbhdToOpens U' V hLN hLV) := by
  let φ : V → U' := fun v ↦ ⟨v.1.1, hV v.2⟩
  refine isProperMap_of_comp_of_inj (g := φ) (nbhdToOpens U' V hLN hLV).hom.continuous
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) ?_
    fun v w h ↦ Subtype.ext (Subtype.ext (congrArg Subtype.val h :))
  exact hL.isClosedEmbedding_subtypeVal.isProperMap

include hV hL in
/-- **The restriction of a neighbourhood cap product to an open subset away from `X`.** Let `N`
be a closed neighbourhood of `X ⊆ Y`, `U' ⊆ Y` open, `V ⊆ N ∩ U'` open in `N`, and `L ⊆ V` closed
in `U'` with `X ∩ U' ⊆ int L`. Then `(c ∩_N a)|_V` is the push-forward of
`c|_{U'} ∩_L a|_{U'}` along `L ⊆ V`. -/
theorem restrict_capProductNbhd_eq_pushforward {X : Set Y} (hX : IsClosed X) (hN : IsClosed N)
    (hXN : X ⊆ interior N) (hXL : (inclHom U').hom ⁻¹' X ⊆ interior L) (j k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    (restrict R (ModuleCat.of R R) V (k - j)).hom (capProductNbhd R Y hX hN hXN j k c a) =
      (pushforward R (ModuleCat.of R R) (nbhdToOpens U' V hLN hLV)
        (isProperMap_nbhdToOpens U' V hV hL hLN hLV) (k - j)).hom
        (capProductNbhd R (TopCat.of U') (hX.preimage (inclHom U').hom.continuous) hL hXL j k
          ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (inclHom U') X j).hom c)
          ((restrict R (ModuleCat.of R R) U' k).hom a)) := by
  have hT : (restrict R (ModuleCat.of R R) (opensInter U' N) (k - j)).hom
      (capProductNbhd R Y hX hN hXN j k c a) =
      (pushforward R (ModuleCat.of R R) (subsetInclusionOfSubset hLN ≫ opensInterInv U' N)
        ((isProperMap_opensInterInv U' N).comp (isProperMap_subsetInclusionOfSubset hL hLN))
          (k - j)).hom
        (capProductNbhd R (TopCat.of U') (hX.preimage (inclHom U').hom.continuous) hL hXL j k
          ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (inclHom U') X j).hom c)
          ((restrict R (ModuleCat.of R R) U' k).hom a)) := by
    rw [← pushforward_comp_apply R _ _ (isProperMap_subsetInclusionOfSubset hL hLN)
      (isProperMap_opensInterInv U' N),
      pushforward_subsetInclusionOfSubset_capProductNbhd R (TopCat.of U') _
        (isClosed_setInter hN) (preimage_subset_interior_preimage (inclHom U') hXN)]
    exact eq_pushforward_of_pushforward_eq R _ _ (isProperMap_opensInterMap U' N)
      (isProperMap_opensInterInv U' N) rfl _
      (pushforward_opensInterMap_restrict_capProductNbhd R Y U' hX hN hXN j k c a)
  rw [FundamentalClass.restrict_eq_pushforward_subOpensInv hV, hT, restrict_pushforward_apply]
  set O := TopologicalSpace.Opens.comap (subsetInclusionOfSubset hLN ≫ opensInterInv U' N).hom
    (subOpens (opensInter U' N) V) with hOdef
  have hO : O = ⊤ := by
    ext l
    exact ⟨fun _ ↦ trivial, fun _ ↦ hLV l⟩
  have hOp : IsProperMap (inclHom O) :=
    (show IsClosed (O : Set (TopCat.of L)) by rw [hO]; exact isClosed_univ)
      |>.isClosedEmbedding_subtypeVal.isProperMap
  let g : TopCat.of L ⟶ TopCat.of (subOpens (opensInter U' N) V) :=
    TopCat.ofHom ⟨fun l ↦ ⟨(subsetInclusionOfSubset hLN ≫ opensInterInv U' N) l, hLV l⟩,
      (subsetInclusionOfSubset hLN ≫ opensInterInv U' N).hom.continuous.subtype_mk _⟩
  have hg : IsProperMap g := by
    let φ : subOpens (opensInter U' N) V → U' := fun v ↦ ⟨v.1.1.1, v.1.2⟩
    refine isProperMap_of_comp_of_inj (g := φ) g.hom.continuous
      ((continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _) ?_
      fun v w h ↦ Subtype.ext (Subtype.ext (Subtype.ext (congrArg Subtype.val h :)))
    exact hL.isClosedEmbedding_subtypeVal.isProperMap
  have hrP : restrictPreimage (subsetInclusionOfSubset hLN ≫ opensInterInv U' N)
      (subOpens (opensInter U' N) V) = inclHom O ≫ g := rfl
  rw [pushforward_apply_congr R hrP _ (hg.comp hOp), ← pushforward_comp_apply R _ _ hOp hg,
    pushforward_inclHom_restrict_of_eq_top R hO, pushforward_comp_apply R _ _ hg
      (FundamentalClass.isProperMap_subOpensInv hV)
      ((FundamentalClass.isProperMap_subOpensInv hV).comp hg)]
  exact pushforward_apply_congr R rfl _ _ _ _

end nbhd

section ambient

variable {Y : TopCat.{u}} [T2Space Y] {U U' : TopologicalSpace.Opens Y} (h : U ≤ U')

/-- A subset of `U'`, read in the open subset `U ⊆ U'`. -/
abbrev setInOpens (L : Set (TopCat.of U')) : Set (TopCat.of U) :=
  (subOpensMap U' h).hom ⁻¹' setInter (subOpens U' U) L

variable {L L₂ : Set (TopCat.of U')} (hL : IsClosed L) (hL₂ : IsClosed L₂)
  (hLL₂ : L ⊆ interior L₂) (hL₂U : L₂ ⊆ subOpens U' U)

/-- The inclusion of `L`, read in `U`, into `L₂ ⊆ U'`. -/
def setInOpensMap : TopCat.of (setInOpens h L) ⟶ TopCat.of L₂ :=
  TopCat.ofHom ⟨fun x ↦ ⟨⟨x.1.1, h x.1.2⟩, interior_subset (hLL₂ x.2)⟩,
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _⟩

omit [T2Space Y] in
include hL in
/-- A closed subset of `U'`, read in `U`, is closed in `U`. -/
lemma isClosed_setInOpens : IsClosed (setInOpens h L) :=
  (isClosed_setInter hL).preimage (subOpensMap U' h).hom.continuous

omit [T2Space Y] in
include hL₂U in
/-- If `L₂ ⊆ U`, then `U ∩ L₂` is all of `L₂`. -/
lemma opensInter_subOpens_eq_top : opensInter (subOpens U' U) L₂ = ⊤ := by
  ext l
  exact ⟨fun _ ↦ trivial, fun _ ↦ hL₂U l.2⟩

omit [T2Space Y] in
include hL₂U in
/-- If `L₂ ⊆ U`, the inclusion of `U ∩ L₂` into `L₂` is proper. -/
lemma isProperMap_inclHom_opensInter_subOpens :
    IsProperMap (inclHom (opensInter (subOpens U' U) L₂)) :=
  (show IsClosed ((opensInter (subOpens U' U) L₂ : TopologicalSpace.Opens (TopCat.of L₂)) :
      Set (TopCat.of L₂)) by
    rw [opensInter_subOpens_eq_top hL₂U]; exact isClosed_univ)
    |>.isClosedEmbedding_subtypeVal.isProperMap

omit [T2Space Y] in
include hL hL₂U in
/-- The inclusion `setInOpensMap` of `L`, read in `U`, into `L₂` is proper. -/
lemma isProperMap_setInOpensMap : IsProperMap (setInOpensMap h hLL₂) :=
  ((isProperMap_inclHom_opensInter_subOpens hL₂U).comp
    (isProperMap_opensInterInv (subOpens U' U) L₂)).comp
    (isProperMap_preimageRestrict (subOpensMap U' h) (isProperMap_subOpensMap U' h)
      (isClosed_setInter hL)
      ((preimage_subset_interior_preimage (inclHom (subOpens U' U)) hLL₂).trans interior_subset))

include hL hL₂ hL₂U in
/-- **Changing the ambient space from `U'` to an open `U ⊆ U'`.** For closed neighbourhoods
`L ⊆ int L₂` of `X ∩ U'` in `U'` with `L₂ ⊆ U`, the cap product of `U` with values in `L ∩ U`
pushes forward to the cap product of `U'` with values in `L₂`. -/
theorem pushforward_setInOpensMap_capProductNbhd {X : Set Y} (hX : IsClosed X)
    (hXL : (inclHom U').hom ⁻¹' X ⊆ interior L) (j k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    (pushforward R (ModuleCat.of R R) (setInOpensMap h hLL₂)
        (isProperMap_setInOpensMap h hL hLL₂ hL₂U) (k - j)).hom
      (capProductNbhd R (TopCat.of U) (hX.preimage (inclHom U).hom.continuous)
        (isClosed_setInOpens h hL)
        (preimage_subset_interior_preimage (subOpensMap U' h)
          (preimage_subset_interior_preimage (inclHom (subOpens U' U)) hXL)) j k
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (inclHom U) X j).hom c)
        ((restrict R (ModuleCat.of R R) U k).hom a)) =
      capProductNbhd R (TopCat.of U') (hX.preimage (inclHom U').hom.continuous) hL₂
        (hXL.trans (interior_subset.trans hLL₂)) j k
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (inclHom U') X j).hom c)
        ((restrict R (ModuleCat.of R R) U' k).hom a) := by
  have hLo : IsClosed (setInter (subOpens U' U) L) := isClosed_setInter hL
  have hL₂o : IsClosed (setInter (subOpens U' U) L₂) := isClosed_setInter hL₂
  have hLLo : setInter (subOpens U' U) L ⊆ interior (setInter (subOpens U' U) L₂) :=
    preimage_subset_interior_preimage (inclHom (subOpens U' U)) hLL₂
  have h1 := pushforward_opensInterMap_restrict_capProductNbhd R (TopCat.of U') (subOpens U' U)
    (hX.preimage (inclHom U').hom.continuous) hL₂ (hXL.trans (interior_subset.trans hLL₂)) j k
    ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (inclHom U') X j).hom c)
    ((restrict R (ModuleCat.of R R) U' k).hom a)
  have h2 := eq_pushforward_of_pushforward_eq R _ _ (isProperMap_opensInterMap _ _)
    (isProperMap_opensInterInv (subOpens U' U) L₂) rfl _ h1
  have h3 := pushforward_inclHom_restrict_of_eq_top R (opensInter_subOpens_eq_top hL₂U)
    (isProperMap_inclHom_opensInter_subOpens hL₂U) (k - j)
    (capProductNbhd R (TopCat.of U') (hX.preimage (inclHom U').hom.continuous) hL₂
        (hXL.trans (interior_subset.trans hLL₂)) j k
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (inclHom U') X j).hom c)
        ((restrict R (ModuleCat.of R R) U' k).hom a))
  rw [h2, pushforward_comp_apply R _ _ (isProperMap_opensInterInv _ _)
    (isProperMap_inclHom_opensInter_subOpens hL₂U)
    ((isProperMap_inclHom_opensInter_subOpens hL₂U).comp
      (isProperMap_opensInterInv (subOpens U' U) L₂))] at h3
  have key := pushforward_preimageRestrict_capProductNbhd R (subOpensMap U' h)
    (isProperMap_subOpensMap U' h) (hX.preimage (inclHom U').hom.continuous |>.preimage
      (inclHom (subOpens U' U)).hom.continuous) hLo hL₂o
    (preimage_subset_interior_preimage (inclHom (subOpens U' U)) hXL) hLLo j k
    ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (inclHom (subOpens U' U)) _ j).hom
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (inclHom U') X j).hom c))
    ((restrict R (ModuleCat.of R R) U k).hom a)
  have hb := restrict_restrict_apply R (ModuleCat.of R R) U' h k a
  have hc : (cohomologyWithSupports.pullback R (ModuleCat.of R R) (subOpensMap U' h) _ j).hom
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (inclHom (subOpens U' U)) _ j).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (inclHom U') X j).hom c)) =
      (cohomologyWithSupports.pullback R (ModuleCat.of R R) (inclHom U) X j).hom c := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← LinearMap.comp_apply,
      ← ModuleCat.hom_comp, ← cohomologyWithSupports.pullback_comp,
      ← cohomologyWithSupports.pullback_comp]
    rfl
  erw [← hb, hc] at key
  rw [← h3, ← key, pushforward_comp_apply R _ _ (isProperMap_preimageRestrict _
    (isProperMap_subOpensMap U' h) hLo _) _ (isProperMap_setInOpensMap h hL hLL₂ hL₂U)]
  rfl

end ambient

section main

/-- **The cap product commutes with restriction to an open subset** (Fulton §19.1; [BT] 2.2). Let
`X` be closed in a space `Y`, `U ⊆ Y` open with inclusion `j`, `c ∈ H^j(Y, Y - X)` and
`a ∈ H_k Y`. Then `(c ∩ a)|_{X ∩ U} = j^* c ∩ a|_U` in `H_{k-j}(X ∩ U)`; here `X ∩ U` is the open
subset `opensInter U X` of `X`, identified with the closed subset `j⁻¹ X` of `U` by
`opensInterMap`. The spaces are those of Fulton §19.1 (closed subspaces of some `ℝᴺ`, so
hereditarily normal: `T5Space`), and `X ⊆ Y`, `j⁻¹ X ⊆ U` have arbitrarily small proper
neighbourhood deformations, the setting in which the two cap products are defined. -/
theorem pushforward_opensInterMap_restrict_capProductSupport (Y : TopCat.{u}) [T5Space Y]
    (U : TopologicalSpace.Opens Y) {X : Set Y} (hX : IsClosed X)
    (hXd : HasProperNeighbourhoodDeformations X)
    (hXUd : HasProperNeighbourhoodDeformations ((inclHom U).hom ⁻¹' X)) (j k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    (pushforward R (ModuleCat.of R R) (opensInterMap U X) (isProperMap_opensInterMap U X)
        (k - j)).hom ((restrict R (ModuleCat.of R R) (opensInter U X) (k - j)).hom
          (capProductSupport R Y hX hXd j k c a)) =
      capProductSupportPullback R (inclHom U) hX hXUd j k c
        ((restrict R (ModuleCat.of R R) U k).hom a) := by
  obtain ⟨N, hN, hXN, r, hr, hrX⟩ := hXd.exists_retraction
  rw [capProductSupport_eq_capProductAlong R Y hX hXd hN hXN r hr hrX]
  simp only [capProductAlong, LinearMap.compr₂_apply]
  rw [restrict_pushforward_apply]
  set W := opensInter U X
  set V : TopologicalSpace.Opens (TopCat.of N) :=
    TopologicalSpace.Opens.comap (TopCat.ofHom r).hom W with hVdef
  have hmemV : ∀ y : N, y ∈ V ↔ ((r y : X) : Y) ∈ U := fun _ ↦ Iff.rfl
  let U' : TopologicalSpace.Opens Y := ⟨(U : Set Y) ∪ Xᶜ, U.isOpen.union hX.isOpen_compl⟩
  have hUU' : U ≤ U' := fun _ hy ↦ Or.inl hy
  have hV : V ≤ opensInter U' N := by
    intro y hy
    by_cases hyX : (y : Y) ∈ X
    · have := (hmemV y).1 hy
      rw [hrX y hyX] at this
      exact Or.inl this
    · exact Or.inr hyX
  obtain ⟨S, hS, hSV⟩ := isOpen_induced_iff.1 V.isOpen
  have hXUO : X ∩ U ⊆ U ∩ interior N ∩ S := by
    rintro x ⟨hxX, hxU⟩
    refine ⟨⟨hxU, hXN hxX⟩, ?_⟩
    have : (⟨x, interior_subset (hXN hxX)⟩ : N) ∈ (V : Set (TopCat.of N)) := by
      rwa [SetLike.mem_coe, hmemV, hrX _ hxX]
    rwa [← hSV] at this
  have hO₂ : IsOpen (U ∩ interior N ∩ S) := (U.isOpen.inter isOpen_interior).inter hS
  have hK : IsClosed (Subtype.val ⁻¹' (X ∩ U) : Set (U' : Set Y)) := by
    have e : (Subtype.val ⁻¹' (X ∩ U) : Set (U' : Set Y)) = Subtype.val ⁻¹' X := by
      ext x
      exact ⟨fun hx ↦ hx.1, fun hx ↦ ⟨hx, x.2.resolve_right (fun h ↦ h hx)⟩⟩
    rw [e]
    exact hX.preimage continuous_subtype_val
  have hKU' : X ∩ U ⊆ (U' : Set Y) := fun x hx ↦ Or.inl hx.2
  obtain ⟨L₂, hL₂, -, hL₂O, hKL₂⟩ :=
    exists_isClosed_preimage_subset_nhds U'.isOpen hK hKU' hO₂ hXUO
  obtain ⟨L, hL, -, hLL₂, hKL⟩ :=
    exists_isClosed_preimage_subset_nhds U'.isOpen hK hKU' isOpen_interior hKL₂
  set L₂' : Set (TopCat.of U') := Subtype.val ⁻¹' L₂
  set L' : Set (TopCat.of U') := Subtype.val ⁻¹' L
  have hint : ∀ {A B : Set Y}, A ⊆ interior B →
      (Subtype.val ⁻¹' A : Set (TopCat.of U')) ⊆ interior (Subtype.val ⁻¹' B) := fun h ↦
    (preimage_mono h).trans (preimage_interior_subset_interior_preimage continuous_subtype_val)
  have hXU' : ∀ x : TopCat.of U', (x : Y) ∈ X → (x : Y) ∈ X ∩ U := fun x hx ↦
    ⟨hx, x.2.resolve_right (fun h ↦ h hx)⟩
  have hXL₂' : (inclHom U').hom ⁻¹' X ⊆ interior L₂' := fun x hx ↦ hint hKL₂ (hXU' x hx)
  have hXL' : (inclHom U').hom ⁻¹' X ⊆ interior L' := fun x hx ↦ hint hKL (hXU' x hx)
  have hLL₂' : L' ⊆ interior L₂' := hint hLL₂
  have hL₂N : L₂' ⊆ setInter U' N := fun x hx ↦ (interior_subset (hL₂O hx).1.2 : (x : Y) ∈ N)
  have hL₂V : ∀ l : L₂', (⟨l.1.1, hL₂N l.2⟩ : N) ∈ V := by
    intro l
    have : (⟨l.1.1, hL₂N l.2⟩ : N) ∈ (Subtype.val ⁻¹' S : Set N) := (hL₂O l.2).2
    rwa [hSV] at this
  have hL₂U : L₂' ⊆ subOpens U' U := fun x hx ↦ (hL₂O hx).1.1
  rw [restrict_capProductNbhd_eq_pushforward R U' V hV hL₂ hL₂N hL₂V hX hN hXN hXL₂' j k c a,
    ← pushforward_setInOpensMap_capProductNbhd R hUU' hL hL₂ hLL₂' hL₂U hX hXL' j k c a]
  set F := setInOpensMap hUU' hLL₂' ≫ nbhdToOpens U' V hL₂N hL₂V ≫
    restrictPreimage (TopCat.ofHom r) W ≫ opensInterMap U X with hFdef
  have hF : IsProperMap F :=
    (((isProperMap_opensInterMap U X).comp (isProperMap_restrictPreimage _ W hr)).comp
      (isProperMap_nbhdToOpens U' V hV hL₂ hL₂N hL₂V)).comp
      (isProperMap_setInOpensMap hUU' hL hLL₂' hL₂U)
  have hFX : ∀ y : setInOpens hUU' L', (y : TopCat.of U) ∈ (inclHom U).hom ⁻¹' X →
      ((F.hom y : (inclHom U).hom ⁻¹' X) : TopCat.of U) = y :=
    fun y hy ↦ Subtype.ext (hrX _ hy)
  rw [capProductSupportPullback_apply, capProductSupport_eq_capProductAlong R (TopCat.of U)
    (hX.preimage (inclHom U).hom.continuous) hXUd (isClosed_setInOpens hUU' hL)
    (preimage_subset_interior_preimage (subOpensMap U' hUU')
      (preimage_subset_interior_preimage (inclHom (subOpens U' U)) hXL')) F.hom hF hFX]
  simp only [capProductAlong, LinearMap.compr₂_apply]
  have p1 : IsProperMap (setInOpensMap hUU' hLL₂' ≫ nbhdToOpens U' V hL₂N hL₂V) :=
    (isProperMap_nbhdToOpens U' V hV hL₂ hL₂N hL₂V).comp
      (isProperMap_setInOpensMap hUU' hL hLL₂' hL₂U)
  have p2 : IsProperMap ((setInOpensMap hUU' hLL₂' ≫ nbhdToOpens U' V hL₂N hL₂V) ≫
      restrictPreimage (TopCat.ofHom r) W) := (isProperMap_restrictPreimage _ W hr).comp p1
  have p3 : IsProperMap (((setInOpensMap hUU' hLL₂' ≫ nbhdToOpens U' V hL₂N hL₂V) ≫
      restrictPreimage (TopCat.ofHom r) W) ≫ opensInterMap U X) :=
    (isProperMap_opensInterMap U X).comp p2
  rw [pushforward_comp_apply R _ _ (isProperMap_setInOpensMap hUU' hL hLL₂' hL₂U)
      (isProperMap_nbhdToOpens U' V hV hL₂ hL₂N hL₂V) p1,
    pushforward_comp_apply R _ _ p1 (isProperMap_restrictPreimage _ W hr) p2,
    pushforward_comp_apply R _ _ p2 (isProperMap_opensInterMap U X) p3]
  exact pushforward_apply_congr R rfl _ _ _ _

end main

end borelMooreHomology

end MMP
