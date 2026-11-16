module
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupEmbedded
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceBlowupGlobal

/-!
# Weak embedded resolution sequences are bounded by the tree of infinitely near singularities

Let `S₀` be a two-dimensional regular Noetherian scheme and `C₀ ⊆ S₀` a reduced curve. If the
infinitely near singular points of `C₀`, over all singular points of `C₀`, form a finite tree with
`T` vertices, then every weak embedded resolution sequence for `(S₀, C₀)` has length at most `T`,
and every maximal one stops: it has finite length `n` and `C_n` is regular at each of its closed
points.

## Main results

* `MMP.Resolution.PointBlowupSequence.length_le_ncard_and_stops_of_finite`.

## Implementation notes

A vertex of the tree of infinitely near singular points is recorded by its chain of ancestors: a
list `[t₀, t₁, …, t_k]` of pointed subschemes with `t₀ = (S₀, C₀, p)` for a closed singular point
`p` of `C₀` and `t_{j+1} ∈ firstInfinitelyNearSingularities t_j`. Counting chains rather than
their end triples makes distinct blow-up paths distinct vertices: two such chains first diverge at
two different points of one and the same scheme. A weak embedded resolution sequence `s` is
*maximal* when no weak embedded resolution sequence of greater length extends it, i.e. has the
same schemes `S_i` (`i ≤ n`), the same identification `S_0 ≅ S₀`, the same centres `p_i` and the
same isomorphisms `S_{i+1} ≅ B_{p_i}S_i` (`i < n`).

A centre `p_i` lives on `S_i`, while the chains are built from the iterated blow-ups of `S₀`
itself, so a point of `S_i` is compared with the last vertex of a chain through an isomorphism of
germs: a scheme embedded openly into both, carrying one curve to the other. Such a germ transports
membership in the curve and regularity of its local ring. Blowing up commutes with restriction to
an open subscheme (Stacks, Tag 0805), and so does the birational transform, since it is the kernel
of a morphism; hence a germ at the centres lifts to a germ along the whole exceptional fibres.
Away from the exceptional curve the blow-up is an isomorphism carrying the birational transform to
the curve. By induction on `i`, every singular closed point of `C_i` is recorded by a chain whose
last vertex has the germ of `C_i` at it; the chains of distinct singular points are
prefix-incomparable and are never prefixes of the chains of the earlier centres, which makes the
centres' chains distinct. A maximal sequence has finite length by the bound, and if `C_n` had a
singular closed point, blowing it up would extend the sequence.

## References

* [Kollár, *Lectures on resolution of singularities*, §1.4–1.5][kollar2007]
-/

universe u

namespace MMP.Resolution

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/-! ### Regularity along the sequence -/

/-- `X` is Noetherian and regular of topological Krull dimension two: the form of
`IsRegularSurface` that is stable under isomorphism and under blowing up a closed point. -/
private def IsRegSurf (X : Scheme.{u}) : Prop :=
  IsNoetherian X ∧ IsRegular X ∧ topologicalKrullDim X = 2

private theorem isNoetherian_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) [h : IsNoetherian Y] :
    IsNoetherian X := by
  have : IsLocallyNoetherian Y := h.toIsLocallyNoetherian
  have := isLocallyNoetherian_of_isOpenImmersion e.hom
  have : CompactSpace X := (Scheme.homeoOfIso e).symm.compactSpace
  exact ⟨⟩

private theorem isRegSurf_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) (h : IsRegSurf Y) :
    IsRegSurf X := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  exact ⟨isNoetherian_of_iso e, ObjectProperty.prop_of_iso (fun X : Scheme.{u} => IsRegular X)
    e.symm h₂, h₃ ▸ (Scheme.homeoOfIso e).isHomeomorph.topologicalKrullDim_eq⟩

private theorem isRegSurf_blowUp {X : Scheme.{u}} (h : IsRegSurf X) (x : X)
    (hx : IsClosed ({x} : Set X)) :
    IsRegSurf (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)) := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  exact ⟨Stacks.ResolutionOfSurfaces.isNoetherian_blowUp _,
    isRegular_and_topologicalKrullDim_blowUp_vanishingIdeal_singleton X h₂ h₃ x hx⟩

private theorem isRegSurf_of_isRegularSurface {S : Scheme.{u}} (hS : IsRegularSurface S)
    [Nonempty S] : IsRegSurf S := by
  obtain ⟨h₁, h₂, h₃⟩ := hS
  have : IsLocallyNoetherian S := h₁.toIsLocallyNoetherian
  refine ⟨h₁, (isRegular_iff_regular_stalks S).2 ⟨inferInstance, h₂⟩, ?_⟩
  rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
  obtain ⟨y, -, hy⟩ := (isClosed_univ (X := S)).exists_closed_singleton Set.univ_nonempty
  refine le_antisymm (iSup_le fun x => ?_) ((h₃ y hy).symm.le.trans
    (le_iSup (fun x : S => ringKrullDim (S.presheaf.stalk x)) y))
  obtain ⟨z, hz, hzc⟩ := (isClosed_closure (s := ({x} : Set S))).exists_closed_singleton
    ⟨x, subset_closure rfl⟩
  calc ringKrullDim (S.presheaf.stalk x) ≤ ringKrullDim (S.presheaf.stalk z) := by
          rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight]
          exact_mod_cast Order.coheight_anti
            (show z ≤ x from specializes_iff_mem_closure.2 hz)
    _ = 2 := h₃ z hzc

private theorem nonempty_blowUp {X : Scheme.{u}} (h : IsRegSurf X) (x : X)
    (hx : IsClosed ({x} : Set X)) :
    Nonempty (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : TopologicalSpace.Closeds X)
  obtain ⟨y, hy⟩ : ∃ y : X, y ≠ x := by
    by_contra! hall
    have : Subsingleton X := ⟨fun a b => (hall a).trans (hall b).symm⟩
    have : DiscreteTopology X := ⟨Subsingleton.elim _ _⟩
    have := topologicalKrullDim_zero_of_discreteTopology X
    rw [h.2.2] at this
    exact absurd this (by decide)
  have hyU : y ∈ (I.support.compl : X.Opens) := by
    change y ∉ (I.support : Set X)
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hy
  have := isIso_blowUp_restrict_compl_support I
  exact ⟨((inv (blowUpToBase I ∣_ (I.support.compl : X.Opens))).base ⟨y, hyU⟩).1⟩

private theorem isRegSurf_S {S₀ : Scheme.{u}} (h : IsRegSurf S₀) (s : PointBlowupSequence S₀) :
    ∀ i : ℕ, (i : ℕ∞) ≤ s.length → IsRegSurf (s.S i)
  | 0, _ => isRegSurf_of_iso s.zeroIso h
  | i + 1, hi =>
    have hlt := PointBlowupSequence.coe_lt_of_succ_le hi
    isRegSurf_of_iso (s.blowupIso i hlt)
      (isRegSurf_blowUp (isRegSurf_S h s i hlt.le) _ (s.isClosed_p i hlt))

/-! ### Extending a sequence by one blow-up -/

/-- `s'` agrees with `s` on all the data of `s`: the same schemes `S_i` (`i ≤ s.length`), the same
identification `S_0 ≅ S₀`, the same centres `p_i` and the same isomorphisms `S_{i+1} ≅ B_{p_i}S_i`
(`i < s.length`). -/
private abbrev Agrees {S₀ : Scheme.{u}} (s s' : PointBlowupSequence S₀) : Prop :=
  (∀ i : ℕ, (i : ℕ∞) ≤ s.length → s'.S i = s.S i) ∧ HEq s'.zeroIso s.zeroIso ∧
    (∀ i : ℕ, (i : ℕ∞) < s.length → HEq (s'.p i) (s.p i)) ∧
    ∀ (i : ℕ) (hi : (i : ℕ∞) < s.length) (hi' : (i : ℕ∞) < s'.length),
      HEq (s'.blowupIso i hi') (s.blowupIso i hi)

section Extension

private noncomputable def castPt {X Y : Scheme.{u}} (e : X = Y) (x : X) : Y :=
  cast (congrArg (fun Z : Scheme.{u} => (Z : Type u)) e) x

private theorem castPt_heq {X Y : Scheme.{u}} (e : X = Y) (x : X) : HEq (castPt e x) x :=
  cast_heq _ _

private theorem blowUp_congr {X Y : Scheme.{u}} (h : X = Y) {x : X} {y : Y} (hxy : HEq x y)
    (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({y} : Set Y)) :
    blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩) =
      blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) := by
  subst h; cases hxy; rfl

private theorem isClosed_congr {X Y : Scheme.{u}} (h : X = Y) {x : X} {y : Y} (hxy : HEq x y)
    (hy : IsClosed ({y} : Set Y)) : IsClosed ({x} : Set X) := by
  subst h; cases hxy; exact hy

private theorem heq_eqToIso_trans {A A' B B' : Scheme.{u}} (e₁ : A' = A) (f : A ≅ B)
    (e₂ : B = B') : HEq (eqToIso e₁ ≪≫ f ≪≫ eqToIso e₂) f := by
  subst e₁ e₂; simp

private theorem heq_eqToIso_trans' {A A' B : Scheme.{u}} (e₁ : A' = A) (f : A ≅ B) :
    HEq (eqToIso e₁ ≪≫ f) f := by
  subst e₁; simp

private theorem heq_comap {X Y Z : Scheme.{u}} (e : X = Y) {f : X ≅ Z} {g : Y ≅ Z}
    (hfg : HEq f g) (C : Z.IdealSheafData) : HEq (C.comap f.hom) (C.comap g.hom) := by
  subst e; cases hfg; rfl

private theorem heq_comap_birationalTransform {X Y X' Y' : Scheme.{u}} (e : X = Y)
    {x : X} {y : Y} (hxy : HEq x y) (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({y} : Set Y))
    {Cx : X.IdealSheafData} {Cy : Y.IdealSheafData} (hC : HEq Cx Cy) (e' : X' = Y')
    (φ : X' ≅ blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩))
    (ψ : Y' ≅ blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) (hφψ : HEq φ ψ) :
    HEq ((birationalTransform x hx Cx).comap φ.hom)
      ((birationalTransform y hy Cy).comap ψ.hom) := by
  subst e; cases hxy; cases hC; subst e'; cases hφψ; rfl

private theorem weak_congr {X Y : Scheme.{u}} (e : X = Y) {x : X} {y : Y} (hxy : HEq x y)
    {Cx : X.IdealSheafData} {Cy : Y.IdealSheafData} (hC : HEq Cx Cy)
    (h : y ∈ Cy.support ∧ ¬ IsRegularLocalRing (Y.presheaf.stalk y ⧸ IdealSheafData.stalk Cy y)) :
    x ∈ Cx.support ∧ ¬ IsRegularLocalRing (X.presheaf.stalk x ⧸ IdealSheafData.stalk Cx x) := by
  subst e; cases hxy; cases hC; exact h

variable {S₀ : Scheme.{u}} (s : PointBlowupSequence S₀) (n : ℕ) {q : s.S n}
  (hq : IsClosed ({q} : Set (s.S n)))

/-- The schemes of the extension. -/
private noncomputable def extS (i : ℕ) : Scheme.{u} :=
  if i ≤ n then s.S i else blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{q}, hq⟩)

private theorem extS_le {i : ℕ} (h : i ≤ n) : extS s n hq i = s.S i := ite_eq_left h

private theorem extS_gt {i : ℕ} (h : ¬ i ≤ n) :
    extS s n hq i = blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{q}, hq⟩) := ite_eq_right h

/-- The centres of the extension. -/
private noncomputable def extP (b : blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{q}, hq⟩))
    (i : ℕ) : extS s n hq i :=
  if h : i < n then castPt (extS_le s n hq h.le).symm (s.p i)
  else if h' : i = n then castPt (extS_le s n hq h'.le).symm (castPt (congrArg s.S h'.symm) q)
  else castPt (extS_gt s n hq (by omega)).symm b

private theorem extP_heq_lt (b) {i : ℕ} (h : i < n) : HEq (extP s n hq b i) (s.p i) := by
  rw [extP, dite_eq_left h]; exact castPt_heq _ _

private theorem extP_heq_eq (b) : HEq (extP s n hq b n) q := by
  rw [extP, dite_eq_right (lt_irrefl n), dite_eq_left rfl]
  exact (castPt_heq _ _).trans (castPt_heq _ _)

variable {s n} (hn : s.length = n)

include hn

private theorem lt_of_lt_ext {i : ℕ} (h : i < n) : (i : ℕ∞) < s.length := by
  rw [hn]; exact_mod_cast h

private theorem extP_isClosed (b) (i : ℕ) (hi : (i : ℕ∞) < ((n + 1 : ℕ) : ℕ∞)) :
    IsClosed ({extP s n hq b i} : Set (extS s n hq i)) := by
  have hi' : i ≤ n := by have := ENat.natCast_lt_natCast.mp hi; omega
  rcases hi'.lt_or_eq with h | rfl
  · exact isClosed_congr (extS_le s n hq h.le) (extP_heq_lt s n hq b h)
      (s.isClosed_p i (lt_of_lt_ext hn h))
  · exact isClosed_congr (extS_le s i hq le_rfl) (extP_heq_eq s i hq b) hq

/-- The extension of `s`, of length `n`, by the blow-up of `q`; the point `b` fills the unused
slot `p (n + 1)`. -/
private noncomputable def ext (b : blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{q}, hq⟩)) :
    PointBlowupSequence S₀ where
  length := (n + 1 : ℕ)
  S := extS s n hq
  zeroIso := eqToIso (extS_le s n hq (Nat.zero_le n)) ≪≫ s.zeroIso
  p := extP s n hq b
  isClosed_p := extP_isClosed hq hn b
  blowupIso i hi :=
    if h : i < n then
      eqToIso (extS_le s n hq (Nat.succ_le_of_lt h)) ≪≫ s.blowupIso i (lt_of_lt_ext hn h) ≪≫
        eqToIso (blowUp_congr (extS_le s n hq h.le).symm (extP_heq_lt s n hq b h).symm _ _)
    else
      have hin : i = n := by have := ENat.natCast_lt_natCast.mp hi; omega
      eqToIso (extS_gt s n hq (by omega)) ≪≫
        eqToIso (blowUp_congr (by subst hin; exact (extS_le s i hq le_rfl).symm)
          (by subst hin; exact (extP_heq_eq s i hq b).symm) _ _)

private theorem ext_blowupIso_heq (b) {i : ℕ} (h : i < n) (hi' : (i : ℕ∞) < (ext hq hn b).length) :
    HEq ((ext hq hn b).blowupIso i hi') (s.blowupIso i (lt_of_lt_ext hn h)) := by
  dsimp only [ext]
  split
  · exact heq_eqToIso_trans _ _ _
  · contradiction

private theorem ext_transformedSubscheme_heq (b) (C₀ : S₀.IdealSheafData) :
    ∀ i : ℕ, i ≤ n →
      HEq ((ext hq hn b).transformedSubscheme C₀ i) (s.transformedSubscheme C₀ i)
  | 0, _ => heq_comap (extS_le s n hq (Nat.zero_le n)) (heq_eqToIso_trans' _ _) C₀
  | i + 1, h => by
    have hi : i < n := h
    have hi₁ : (i : ℕ∞) < (ext hq hn b).length := by
      change (i : ℕ∞) < ((n + 1 : ℕ) : ℕ∞); exact_mod_cast (by omega : i < n + 1)
    rw [PointBlowupSequence.transformedSubscheme, PointBlowupSequence.transformedSubscheme,
      dite_eq_left hi₁, dite_eq_left (lt_of_lt_ext hn hi)]
    exact heq_comap_birationalTransform (extS_le s n hq hi.le) (extP_heq_lt s n hq b hi) _ _
      (ext_transformedSubscheme_heq b C₀ i hi.le) (extS_le s n hq h) _ _
      (ext_blowupIso_heq hq hn b hi hi₁)

private theorem exists_extension_of_point (C₀ : S₀.IdealSheafData)
    (hs : s.IsWeakEmbeddedResolution C₀)
    (hqC : q ∈ (s.transformedSubscheme C₀ n).support)
    (hqreg : ¬ IsRegularLocalRing ((s.S n).presheaf.stalk q ⧸
        IdealSheafData.stalk (s.transformedSubscheme C₀ n) q))
    (b : blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{q}, hq⟩)) :
    ∃ s' : PointBlowupSequence S₀, s'.IsWeakEmbeddedResolution C₀ ∧ s.length < s'.length ∧
      Agrees s s' := by
  have hlt : ∀ {i : ℕ}, (i : ℕ∞) < s.length → i < n := fun h => by
    rw [hn] at h; exact_mod_cast h
  refine ⟨ext hq hn b, fun i hi => ?_, ?_, fun i hi => extS_le s n hq ?_,
    heq_eqToIso_trans' _ _, fun i hi => extP_heq_lt s n hq b (hlt hi),
    fun i hi hi' => ext_blowupIso_heq hq hn b (hlt hi) hi'⟩
  · have hi' : i ≤ n := by have := ENat.natCast_lt_natCast.mp hi; omega
    rcases hi'.lt_or_eq with h | rfl
    · exact weak_congr (extS_le s n hq h.le) (extP_heq_lt s n hq b h)
        (ext_transformedSubscheme_heq hq hn b C₀ i h.le) (hs i (lt_of_lt_ext hn h))
    · exact weak_congr (extS_le s i hq le_rfl) (extP_heq_eq s i hq b)
        (ext_transformedSubscheme_heq hq hn b C₀ i le_rfl) ⟨hqC, hqreg⟩
  · rw [hn]; change ((n : ℕ) : ℕ∞) < ((n + 1 : ℕ) : ℕ∞); exact_mod_cast Nat.lt_succ_self n
  · rw [hn] at hi; exact_mod_cast hi

end Extension

/-! ### Germs of curves on schemes and blow-ups of closed points -/

section Germs

/-- `(X, C, x)` and `(Y, D, y)` have isomorphic germs: some scheme `W` with a point `w` embeds
openly into both, sending `w` to `x` and `y`, with the same inverse image of `C` and `D`. -/
private def Germ {X Y : Scheme.{u}} (C : X.IdealSheafData) (D : Y.IdealSheafData) (x : X)
    (y : Y) : Prop :=
  ∃ (W : Scheme.{u}) (a : W ⟶ X) (b : W ⟶ Y) (_ : IsOpenImmersion a) (_ : IsOpenImmersion b)
    (w : W), a w = x ∧ b w = y ∧ C.comap a = D.comap b

private theorem Germ.trans {X Y Z : Scheme.{u}} {C : X.IdealSheafData} {D : Y.IdealSheafData}
    {E : Z.IdealSheafData} {x : X} {y : Y} {z : Z} (h₁ : Germ C D x y) (h₂ : Germ D E y z) :
    Germ C E x z := by
  obtain ⟨W₁, a₁, b₁, ha₁, hb₁, w₁, hx₁, hy₁, hC₁⟩ := h₁
  obtain ⟨W₂, a₂, b₂, ha₂, hb₂, w₂, hy₂, hz₂, hC₂⟩ := h₂
  obtain ⟨t, ht₁, ht₂⟩ := Scheme.Pullback.exists_preimage_pullback w₁ w₂ (hy₁.trans hy₂.symm)
  refine ⟨pullback b₁ a₂, pullback.fst b₁ a₂ ≫ a₁, pullback.snd b₁ a₂ ≫ b₂, inferInstance,
    inferInstance, t, ?_, ?_, ?_⟩
  · rw [Scheme.Hom.comp_apply, ht₁, hx₁]
  · rw [Scheme.Hom.comp_apply, ht₂, hz₂]
  · rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, hC₁,
      ← Scheme.IdealSheafData.comap_comp, pullback.condition, Scheme.IdealSheafData.comap_comp,
      hC₂, ← Scheme.IdealSheafData.comap_comp]

private theorem Germ.of_iso {X Y : Scheme.{u}} (e : X ≅ Y) (D : Y.IdealSheafData) (x : X) :
    Germ (D.comap e.hom) D x (e.hom x) :=
  ⟨X, 𝟙 X, e.hom, inferInstance, inferInstance, x, rfl, rfl, by
    rw [Scheme.IdealSheafData.comap_id]⟩

private theorem Germ.mem_support_iff {X Y : Scheme.{u}} {C : X.IdealSheafData}
    {D : Y.IdealSheafData} {x : X} {y : Y} (h : Germ C D x y) :
    x ∈ C.support ↔ y ∈ D.support := by
  obtain ⟨W, a, b, ha, hb, w, rfl, rfl, hC⟩ := h
  have h1 : w ∈ (C.comap a).support ↔ a w ∈ C.support := by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.support_comap]; rfl
  have h2 : w ∈ (D.comap b).support ↔ b w ∈ D.support := by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.support_comap]; rfl
  rw [← h1, ← h2, hC]

private theorem isRegularLocalRing_quotient_comap_iff {X W : Scheme.{u}} (a : W ⟶ X)
    [IsOpenImmersion a] (C : X.IdealSheafData) (w : W) :
    IsRegularLocalRing (W.presheaf.stalk w ⧸ IdealSheafData.stalk (C.comap a) w) ↔
      IsRegularLocalRing (X.presheaf.stalk (a w) ⧸ IdealSheafData.stalk C (a w)) := by
  have := IsOpenImmersion.instIsIsoCommRingCatStalkMap a w
  let e : X.presheaf.stalk (a w) ≃+* W.presheaf.stalk w :=
    (asIso (a.stalkMap w)).commRingCatIsoToRingEquiv
  have he : IdealSheafData.stalk (C.comap a) w = (IdealSheafData.stalk C (a w)).map e := by
    rw [IdealSheafData.stalk_comap]; rfl
  let q := Ideal.quotientEquiv _ _ e he
  exact ⟨fun _ => IsRegularLocalRing.of_ringEquiv q.symm,
    fun _ => IsRegularLocalRing.of_ringEquiv q⟩

private theorem Germ.isRegularLocalRing_iff {X Y : Scheme.{u}} {C : X.IdealSheafData}
    {D : Y.IdealSheafData} {x : X} {y : Y} (h : Germ C D x y) :
    IsRegularLocalRing (X.presheaf.stalk x ⧸ IdealSheafData.stalk C x) ↔
      IsRegularLocalRing (Y.presheaf.stalk y ⧸ IdealSheafData.stalk D y) := by
  obtain ⟨W, a, b, ha, hb, w, rfl, rfl, hC⟩ := h
  rw [← isRegularLocalRing_quotient_comap_iff a, ← isRegularLocalRing_quotient_comap_iff b, hC]

/-- Kernels commute with base change along an open immersion. -/
private theorem ker_comap_of_isPullback {T T' B B' : Scheme.{u}} {g : T ⟶ B} {g' : T' ⟶ B'}
    {r : T' ⟶ T} {h : B' ⟶ B} [IsOpenImmersion h] [QuasiCompact g]
    (H : IsPullback g' r h g) : g.ker.comap h = g'.ker := by
  ext W
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.ker_ideal_of_isPullback_of_isOpenImmersion g g' r h H]

/-- Kernels of the restriction to an open commute with base change along an open immersion. -/
private theorem ker_restrict_comap_of_isPullback {P P' B B' : Scheme.{u}} {q : P ⟶ B}
    {q' : P' ⟶ B'} {r : P' ⟶ P} {h : B' ⟶ B} [IsOpenImmersion h] (U : B.Opens)
    [QuasiCompact ((q ⁻¹ᵁ U).ι ≫ q)] (H : IsPullback q' r h q) :
    ((q ⁻¹ᵁ U).ι ≫ q).ker.comap h = ((q' ⁻¹ᵁ (h ⁻¹ᵁ U)).ι ≫ q').ker := by
  rw [ker_comap_of_isPullback ((isPullback_morphismRestrict r (q ⁻¹ᵁ U)).flip.paste_horiz H),
    show r ⁻¹ᵁ (q ⁻¹ᵁ U) = q' ⁻¹ᵁ (h ⁻¹ᵁ U) by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, H.w]]

/-- The birational transform of `C` in the blow-up of `I`, for an arbitrary centre `I`. -/
private noncomputable def btGen {X : Scheme.{u}} (I C : X.IdealSheafData) :
    (blowUp I).IdealSheafData :=
  (((pullback.snd C.subschemeι (blowUpToBase I)) ⁻¹ᵁ
      (exceptionalIdeal I).support.compl).ι ≫ pullback.snd C.subschemeι (blowUpToBase I)).ker

private theorem birationalTransform_eq_btGen {X : Scheme.{u}} (p : X) (hp : IsClosed ({p} : Set X))
    (C : X.IdealSheafData) :
    birationalTransform p hp C =
      btGen (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) C := rfl

private theorem ker_pullback_snd_subschemeι {X B : Scheme.{u}} (C : X.IdealSheafData)
    (σ : B ⟶ X) : (pullback.snd C.subschemeι σ).ker = C.comap σ := by
  rw [← pullbackSymmetry_hom_comp_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, Scheme.IdealSheafData.ker_subschemeι]

private theorem quasiCompact_restrict_comp {P B : Scheme.{u}} [IsLocallyNoetherian B]
    (q : P ⟶ B) [IsClosedImmersion q] (U : B.Opens) : QuasiCompact ((q ⁻¹ᵁ U).ι ≫ q) := by
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
  infer_instance

/-- The birational transform computed from any closed immersion with the right kernel. -/
private theorem btGen_eq_of_ker {X P : Scheme.{u}} (I C : X.IdealSheafData)
    [IsLocallyNoetherian (blowUp I)]
    (q : P ⟶ blowUp I) [IsClosedImmersion q] (hq : q.ker = C.comap (blowUpToBase I)) :
    btGen I C = ((q ⁻¹ᵁ (exceptionalIdeal I).support.compl).ι ≫ q).ker := by
  set q₀ := pullback.snd C.subschemeι (blowUpToBase I)
  have hq₀ : q₀.ker = C.comap (blowUpToBase I) := ker_pullback_snd_subschemeι C _
  let e : P ⟶ pullback C.subschemeι (blowUpToBase I) :=
    IsClosedImmersion.lift q₀ q (by rw [hq₀, hq])
  have he : e ≫ q₀ = q := IsClosedImmersion.lift_fac _ _ _
  have : IsIso e := IsClosedImmersion.isIso_of_ker_eq q q₀ e he (by rw [hq, hq₀])
  have H : IsPullback q e (𝟙 _) q₀ :=
    IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, he]⟩
  have : QuasiCompact ((q₀ ⁻¹ᵁ (exceptionalIdeal I).support.compl).ι ≫ q₀) :=
    quasiCompact_restrict_comp q₀ _
  have h := ker_restrict_comap_of_isPullback (exceptionalIdeal I).support.compl H
  rwa [Scheme.IdealSheafData.comap_id] at h

private theorem isIso_top_ι (P : Scheme.{u}) : IsIso (⊤ : P.Opens).ι :=
  ⟨⟨P.topIso.inv, P.ι_toIso_inv, P.toIso_inv_ι⟩⟩

private theorem compl_support_comap {X Y : Scheme.{u}} (J : Y.IdealSheafData) (f : X ⟶ Y) :
    (J.comap f).support.compl = f ⁻¹ᵁ J.support.compl := by
  ext z
  change z ∉ ((J.comap f).support : Set X) ↔ f z ∉ (J.support : Set Y)
  rw [Scheme.IdealSheafData.support_comap]; rfl

private theorem mem_support_exceptionalIdeal_iff {X : Scheme.{u}} (p : X)
    (hp : IsClosed ({p} : Set X))
    (z : blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) :
    z ∈ (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).support ↔
      blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) z = p := by
  rw [← SetLike.mem_coe, exceptionalIdeal, Scheme.IdealSheafData.support_comap]
  change blowUpToBase _ z ∈
    ((Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).support : Set X) ↔ _
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

private theorem isOpenImmersion_compl_exceptional {X : Scheme.{u}} (I : X.IdealSheafData) :
    IsOpenImmersion (Scheme.Opens.ι (X := blowUp I) (exceptionalIdeal I).support.compl ≫
      blowUpToBase I) := by
  have hO : ((exceptionalIdeal I).support.compl : (blowUp I).Opens) =
      blowUpToBase I ⁻¹ᵁ (I.support.compl : X.Opens) :=
    compl_support_comap I (blowUpToBase I)
  have hiso := isIso_blowUp_restrict_compl_support I
  rw [hO, ← morphismRestrict_ι]
  infer_instance

private theorem eq_of_blowUpToBase_eq {X : Scheme.{u}} (I : X.IdealSheafData) {x x' : blowUp I}
    (hx : x ∉ (exceptionalIdeal I).support) (hx' : x' ∉ (exceptionalIdeal I).support)
    (h : blowUpToBase I x = blowUpToBase I x') : x = x' := by
  let O : (blowUp I).Opens := (exceptionalIdeal I).support.compl
  have : IsOpenImmersion (O.ι ≫ blowUpToBase I) := isOpenImmersion_compl_exceptional I
  exact congrArg Subtype.val <|
    (O.ι ≫ blowUpToBase I).isOpenEmbedding.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨x', hx'⟩) h

/-- Away from the exceptional locus, the birational transform is the curve itself. -/
private theorem germ_of_notMem {X : Scheme.{u}} [IsNoetherian X] (I C : X.IdealSheafData)
    (x : blowUp I) (hx : x ∉ (exceptionalIdeal I).support) :
    Germ (btGen I C) C x (blowUpToBase I x) := by
  have : IsLocallyNoetherian (blowUp I) :=
    (Stacks.ResolutionOfSurfaces.isNoetherian_blowUp I).toIsLocallyNoetherian
  let O : (blowUp I).Opens := (exceptionalIdeal I).support.compl
  have hxO : x ∈ O := hx
  have hb : IsOpenImmersion (O.ι ≫ blowUpToBase I) := isOpenImmersion_compl_exceptional I
  refine ⟨O, O.ι, O.ι ≫ blowUpToBase I, inferInstance, hb, ⟨x, hxO⟩, rfl, rfl, ?_⟩
  have : QuasiCompact ((pullback.snd C.subschemeι (blowUpToBase I) ⁻¹ᵁ O).ι ≫
      pullback.snd C.subschemeι (blowUpToBase I)) := quasiCompact_restrict_comp _ _
  rw [btGen, ker_restrict_comap_of_isPullback O
      (IsPullback.of_hasPullback O.ι (pullback.snd C.subschemeι (blowUpToBase I))),
    Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]
  have := isIso_top_ι (pullback O.ι (pullback.snd C.subschemeι (blowUpToBase I)))
  rw [Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ker_pullback_snd_subschemeι, ← Scheme.IdealSheafData.comap_comp]

/-- The birational transform commutes with base change along an open immersion. -/
private theorem btGen_comap_of_isPullback {X W : Scheme.{u}} [IsNoetherian X] (a : W ⟶ X)
    [IsOpenImmersion a] (I C : X.IdealSheafData) (K : W.IdealSheafData) (hK : K = I.comap a)
    (h : blowUp K ⟶ blowUp I) (sq : IsPullback (blowUpToBase K) h a (blowUpToBase I)) :
    (btGen I C).comap h = btGen K (C.comap a) := by
  subst hK
  have : IsLocallyNoetherian (blowUp I) :=
    (Stacks.ResolutionOfSurfaces.isNoetherian_blowUp I).toIsLocallyNoetherian
  have : IsOpenImmersion h := MorphismProperty.of_isPullback sq inferInstance
  have : IsLocallyNoetherian (blowUp (I.comap a)) := isLocallyNoetherian_of_isOpenImmersion h
  set q₀ := pullback.snd C.subschemeι (blowUpToBase I)
  have : QuasiCompact ((q₀ ⁻¹ᵁ (exceptionalIdeal I).support.compl).ι ≫ q₀) :=
    quasiCompact_restrict_comp q₀ _
  rw [btGen_eq_of_ker (I.comap a) (C.comap a) (pullback.fst h q₀)]
  · rw [btGen, ker_restrict_comap_of_isPullback _ (IsPullback.of_hasPullback h q₀)]
    have hE : h ⁻¹ᵁ (exceptionalIdeal I).support.compl =
        (exceptionalIdeal (I.comap a)).support.compl := by
      rw [← compl_support_comap, exceptionalIdeal, exceptionalIdeal,
        ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, sq.w]
    rw [hE]
  · rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ker_pullback_snd_subschemeι,
      ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, sq.w]

private theorem comap_vanishingIdeal_of_isOpenImmersion {V Y : Scheme.{u}} (j : V ⟶ Y)
    [IsOpenImmersion j] (Z : TopologicalSpace.Closeds Y) :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap j =
      Scheme.IdealSheafData.vanishingIdeal (Z.preimage j.continuous) := by
  set I := Scheme.IdealSheafData.vanishingIdeal Z
  have : IsReduced (I.comap j).subscheme :=
    isReduced_of_isOpenImmersion ((I.comapIso j).hom ≫ Limits.pullback.snd j I.subschemeι)
  refine Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ ?_
  rw [Scheme.IdealSheafData.support_comap]
  apply TopologicalSpace.Closeds.ext
  rw [TopologicalSpace.Closeds.coe_preimage, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    TopologicalSpace.Closeds.coe_preimage]

private theorem apply_comp_of_isPullback {P X Y Z : Scheme.{u}} {f' : P ⟶ X} {h : P ⟶ Y}
    {a : X ⟶ Z} {f : Y ⟶ Z} (sq : IsPullback f' h a f) (t : P) : f (h t) = a (f' t) := by
  rw [← Scheme.Hom.comp_apply, ← sq.w, Scheme.Hom.comp_apply]

private theorem mem_range_of_isPullback {P X Y Z : Scheme.{u}} {f' : P ⟶ X} {h : P ⟶ Y}
    {a : X ⟶ Z} {f : Y ⟶ Z} (sq : IsPullback f' h a f) (z : Y) (hz : f z ∈ Set.range a) :
    z ∈ Set.range h := by
  obtain ⟨x, hx⟩ := hz
  obtain ⟨t, -, ht⟩ := Scheme.Pullback.exists_preimage_pullback x z hx
  refine ⟨sq.isoPullback.inv t, ?_⟩
  rw [← Scheme.Hom.comp_apply, sq.isoPullback_inv_snd, ht]

/-- A closed point of a fibre carried by open immersions to another fibre stays closed. -/
private theorem isClosed_singleton_of_fibre {W A B : Scheme.{u}} (a : W ⟶ A) (b : W ⟶ B)
    [IsOpenImmersion a] [IsOpenImmersion b] (FA : Set A) (FB : Set B) (hFB : IsClosed FB)
    (hFBr : FB ⊆ Set.range b) (hfib : ∀ t, a t ∈ FA ↔ b t ∈ FB) (t : W)
    (ht : IsClosed ({a t} : Set A)) (htF : a t ∈ FA) : IsClosed ({b t} : Set B) := by
  rw [← closure_subset_iff_isClosed]
  intro s hs
  have hsF : s ∈ FB := closure_minimal (Set.singleton_subset_iff.2 ((hfib t).1 htF)) hFB hs
  obtain ⟨r, rfl⟩ := hFBr hsF
  have hr : r ∈ closure ({t} : Set W) := by
    rw [b.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_singleton]
    exact hs
  have hr' : a r ∈ closure ({a t} : Set A) := by
    rw [a.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_singleton] at hr
    exact hr
  rw [ht.closure_eq, Set.mem_singleton_iff] at hr'
  rw [a.isOpenEmbedding.injective hr']
  exact Set.mem_singleton _

/-- Blowing up the two centres of a germ gives a germ along the whole exceptional fibres. -/
private theorem exists_blowUp_germ {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {C : X.IdealSheafData} {D : Y.IdealSheafData} {x : X} {y : Y}
    (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({y} : Set Y)) (h : Germ C D x y) :
    ∃ (W : Scheme.{u}) (a : W ⟶ blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩))
      (b : W ⟶ blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)),
      IsOpenImmersion a ∧ IsOpenImmersion b ∧
      (birationalTransform x hx C).comap a = (birationalTransform y hy D).comap b ∧
      (∀ z, blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩) z = x →
        z ∈ Set.range a) ∧
      (∀ z, blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) z = y →
        z ∈ Set.range b) ∧
      ∀ t, blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩) (a t) = x ↔
        blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) (b t) = y := by
  obtain ⟨W, a, b, ha, hb, w, rfl, rfl, hC⟩ := h
  have hIJ : (Scheme.IdealSheafData.vanishingIdeal ⟨{a w}, hx⟩).comap a =
      (Scheme.IdealSheafData.vanishingIdeal ⟨{b w}, hy⟩).comap b := by
    rw [comap_vanishingIdeal_of_isOpenImmersion, comap_vanishingIdeal_of_isOpenImmersion]
    congr 1
    apply TopologicalSpace.Closeds.ext
    ext t
    change a t ∈ ({a w} : Set X) ↔ b t ∈ ({b w} : Set Y)
    rw [Set.mem_singleton_iff, Set.mem_singleton_iff, a.isOpenEmbedding.injective.eq_iff,
      b.isOpenEmbedding.injective.eq_iff]
  obtain ⟨ha', sqa⟩ := exists_isPullback_blowUpToBase_comap a
    (Scheme.IdealSheafData.vanishingIdeal ⟨{a w}, hx⟩)
  obtain ⟨hb', sqb⟩ : ∃ hb' : blowUp ((Scheme.IdealSheafData.vanishingIdeal ⟨{a w}, hx⟩).comap a) ⟶
      blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{b w}, hy⟩),
      IsPullback (blowUpToBase ((Scheme.IdealSheafData.vanishingIdeal ⟨{a w}, hx⟩).comap a))
        hb' b (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{b w}, hy⟩)) := by
    rw [hIJ]
    exact exists_isPullback_blowUpToBase_comap b _
  have hfa : ∀ t, blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{a w}, hx⟩) (ha' t) = a w ↔
      blowUpToBase _ t = w := fun t => by
    rw [apply_comp_of_isPullback sqa, a.isOpenEmbedding.injective.eq_iff]
  have hfb : ∀ t, blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{b w}, hy⟩) (hb' t) = b w ↔
      blowUpToBase _ t = w := fun t => by
    rw [apply_comp_of_isPullback sqb, b.isOpenEmbedding.injective.eq_iff]
  refine ⟨_, ha', hb', MorphismProperty.of_isPullback sqa inferInstance,
    MorphismProperty.of_isPullback sqb inferInstance, ?_,
    fun z hz => mem_range_of_isPullback sqa z ⟨w, hz.symm⟩,
    fun z hz => mem_range_of_isPullback sqb z ⟨w, hz.symm⟩,
    fun t => (hfa t).trans (hfb t).symm⟩
  rw [birationalTransform_eq_btGen, birationalTransform_eq_btGen,
    btGen_comap_of_isPullback a _ C _ rfl ha' sqa,
    btGen_comap_of_isPullback b _ D _ hIJ hb' sqb, hC]

/-! ### Recording singular points by ancestor chains -/

/-- A closed point of `C` at which `C` is not regular. -/
private def SingPt {X : Scheme.{u}} (C : X.IdealSheafData) (x : X) : Prop :=
  IsClosed ({x} : Set X) ∧ x ∈ C.support ∧
    ¬ IsRegularLocalRing (X.presheaf.stalk x ⧸ IdealSheafData.stalk C x)

private theorem Germ.support_and_iff {X Y : Scheme.{u}} {C : X.IdealSheafData}
    {D : Y.IdealSheafData} {x : X} {y : Y} (h : Germ C D x y) :
    (x ∈ C.support ∧ ¬ IsRegularLocalRing (X.presheaf.stalk x ⧸ IdealSheafData.stalk C x)) ↔
      (y ∈ D.support ∧ ¬ IsRegularLocalRing (Y.presheaf.stalk y ⧸ IdealSheafData.stalk D y)) := by
  rw [h.mem_support_iff, h.isRegularLocalRing_iff]

/-- The last vertex of `l` is a closed point of a Noetherian scheme, with the germ of `C` at
`x`. -/
private def Tip {X : Scheme.{u}} (C : X.IdealSheafData) (x : X)
    (l : List PointedSubscheme.{u}) : Prop :=
  ∃ t : PointedSubscheme.{u}, l.getLast? = some t ∧ IsClosed ({t.q} : Set t.S) ∧
    IsNoetherian t.S ∧ Germ C t.C x t.q

/-- The invariant of the induction at a stage with `n` centres already blown up: `F` records the
singular points of `C`, `G` the centres; the recorded chains of singular points are pairwise
prefix-incomparable, and none of them is a prefix of the chain of a centre. -/
private def InvAt (N : Set (List PointedSubscheme.{u})) {X : Scheme.{u}} (C : X.IdealSheafData)
    (n : ℕ) (F : X → List PointedSubscheme.{u}) (G : ℕ → List PointedSubscheme.{u}) : Prop :=
  (∀ x, SingPt C x → F x ∈ N ∧ Tip C x (F x)) ∧
  (∀ x x', SingPt C x → SingPt C x' → F x <+: F x' → x = x') ∧
  (∀ j < n, G j ∈ N) ∧
  (∀ j j', j < n → j' < n → G j = G j' → j = j') ∧
  (∀ x, SingPt C x → ∀ j < n, ¬ F x <+: G j)

private theorem isClosed_singleton_iso {X Y : Scheme.{u}} (e : X ≅ Y) {x : X}
    (hx : IsClosed ({x} : Set X)) : IsClosed ({e.hom x} : Set Y) := by
  simpa only [Set.image_singleton] using e.hom.isClosedMap _ hx

private theorem invAt_zero (N : Set (List PointedSubscheme.{u})) {X S₀ : Scheme.{u}}
    [IsNoetherian S₀] (e : X ≅ S₀) (C₀ : S₀.IdealSheafData)
    (hN : ∀ q, SingPt C₀ q → [(⟨S₀, C₀, q⟩ : PointedSubscheme.{u})] ∈ N) :
    ∃ F G, InvAt N (C₀.comap e.hom) 0 F G := by
  refine ⟨fun x => [⟨S₀, C₀, e.hom x⟩], fun _ => [], ?_, ?_,
    fun j hj => absurd hj (Nat.not_lt_zero _), fun j _ hj => absurd hj (Nat.not_lt_zero _),
    fun _ _ j hj => absurd hj (Nat.not_lt_zero _)⟩
  · intro x hx
    have hg := Germ.of_iso e C₀ x
    have hs : SingPt C₀ (e.hom x) :=
      ⟨isClosed_singleton_iso e hx.1, hg.support_and_iff.1 hx.2⟩
    exact ⟨hN _ hs, ⟨S₀, C₀, e.hom x⟩, rfl, hs.1, inferInstance, hg⟩
  · intro x x' _ _ hpre
    have h1 := List.IsPrefix.eq_of_length hpre rfl
    simp only [List.cons.injEq, and_true, PointedSubscheme.mk.injEq, heq_eq_eq, true_and] at h1
    exact e.hom.isOpenEmbedding.injective h1

/-- On the exceptional fibre: given a germ `(a, b)` of the blow-ups of `p` and `y` along their
exceptional fibres, a singular closed point `z` of the transform `C'` of `C` over `p`, with
`a r = e z`, gives the singular closed point `b r` of the transform of `D` over `y`, at which the
transform of `D` has the germ of `C'` at `z`. -/
private theorem singPt_and_germ_of_mem_fibre {X X' Y W : Scheme.{u}} {C : X.IdealSheafData}
    {D : Y.IdealSheafData} {p : X} {y : Y} (hp : IsClosed ({p} : Set X))
    (hy : IsClosed ({y} : Set Y))
    (e : X' ≅ blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))
    (a : W ⟶ blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))
    (b : W ⟶ blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
    [IsOpenImmersion a] [IsOpenImmersion b]
    (hbt : (birationalTransform p hp C).comap a = (birationalTransform y hy D).comap b)
    (hrb : ∀ z, blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) z = y →
      z ∈ Set.range b)
    (hfib : ∀ t, blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) (a t) = p ↔
      blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) (b t) = y)
    {z : X'} {r : W} (hr : a r = e.hom z)
    (hz : (e.hom ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) z = p)
    (hzS : SingPt ((birationalTransform p hp C).comap e.hom) z) :
    SingPt (birationalTransform y hy D) (b r) ∧
      blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) (b r) = y ∧
      Germ ((birationalTransform p hp C).comap e.hom) (birationalTransform y hy D) z (b r) := by
  have hzp : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) (a r) = p := by
    rw [hr]; exact hz
  have g := (Germ.of_iso e (birationalTransform p hp C) z).trans
    (⟨W, a, b, inferInstance, inferInstance, r, hr, rfl, hbt⟩ : Germ _ _ (e.hom z) (b r))
  refine ⟨⟨isClosed_singleton_of_fibre a b
    {z | blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) z = p}
    {z | blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) z = y}
    (hy.preimage (blowUpToBase _).continuous) hrb hfib r
    (by rw [hr]; exact isClosed_singleton_iso e hzS.1) hzp, g.support_and_iff.1 hzS.2⟩,
    (hfib r).1 hzp, g⟩

/-- Off the exceptional fibre: a singular closed point `z` of the transform `C'` of `C` over `p`
lies over the singular closed point `σ z` of `C`, at which `C` has the germ of `C'` at `z`. -/
private theorem singPt_and_germ_of_notMem_fibre {X X' : Scheme.{u}} [IsNoetherian X]
    (C : X.IdealSheafData) {p : X} (hp : IsClosed ({p} : Set X))
    (e : X' ≅ blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) {z : X'}
    (hz : (e.hom ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) z ≠ p)
    (hzS : SingPt ((birationalTransform p hp C).comap e.hom) z) :
    SingPt C ((e.hom ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) z) ∧
      Germ ((birationalTransform p hp C).comap e.hom) C z
        ((e.hom ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) z) := by
  have hnot :
      e.hom z ∉ (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).support :=
    fun hm => hz ((mem_support_exceptionalIdeal_iff p hp _).1 hm)
  have g := (Germ.of_iso e (birationalTransform p hp C) z).trans (germ_of_notMem _ C _ hnot)
  have : IsLocallyNoetherian X := ‹IsNoetherian X›.toIsLocallyNoetherian
  have hcl := (blowUpToBase _).isClosedMap _ (isClosed_singleton_iso e hzS.1)
  rw [Set.image_singleton] at hcl
  exact ⟨⟨hcl, g.support_and_iff.1 hzS.2⟩, g⟩

/-- Prefix-incomparability of recorded chains survives one blow-up. The new chain `F' z` of a
point `z` over the centre `p` is `F p` extended by a vertex `g z`, injective in `z`; the chain of a
point off the centre is that of `σ z`, and `σ` is injective there. -/
private theorem prefix_injOn_extend {α X X' : Type*} {S : X → Prop} {S' : X' → Prop}
    {F : X → List α} {σ : X' → X} {p : X} (g : ∀ z, σ z = p → α) (F' : X' → List α)
    (hF'on : ∀ z hz, F' z = F p ++ [g z hz]) (hF'off : ∀ z, ¬ σ z = p → F' z = F (σ z))
    (hp : S p) (hF : ∀ x x', S x → S x' → F x <+: F x' → x = x')
    (hoff : ∀ z, ¬ σ z = p → S' z → S (σ z))
    (hg : ∀ z₁ z₂ h₁ h₂, g z₁ h₁ = g z₂ h₂ → z₁ = z₂)
    (hσ : ∀ z₁ z₂, ¬ σ z₁ = p → ¬ σ z₂ = p → σ z₁ = σ z₂ → z₁ = z₂)
    (z₁ z₂ : X') (hz₁ : S' z₁) (hz₂ : S' z₂) (hpre : F' z₁ <+: F' z₂) : z₁ = z₂ := by
  by_cases h₁ : σ z₁ = p <;> by_cases h₂ : σ z₂ = p
  · rw [hF'on z₁ h₁, hF'on z₂ h₂] at hpre
    exact hg z₁ z₂ h₁ h₂ (by simpa using hpre.eq_of_length (by simp))
  · rw [hF'on z₁ h₁, hF'off z₂ h₂] at hpre
    exact absurd (hF p _ hp (hoff z₂ h₂ hz₂) ((List.prefix_append _ _).trans hpre)).symm h₂
  · rw [hF'off z₁ h₁, hF'on z₂ h₂] at hpre
    rcases List.prefix_concat_iff.1 hpre with heq | hpre'
    · exact absurd (hF p _ hp (hoff z₁ h₁ hz₁) (heq ▸ List.prefix_append _ _)).symm h₁
    · exact absurd (hF _ p (hoff z₁ h₁ hz₁) hp hpre') h₁
  · rw [hF'off z₁ h₁, hF'off z₂ h₂] at hpre
    exact hσ z₁ z₂ h₁ h₂ (hF _ _ (hoff z₁ h₁ hz₁) (hoff z₂ h₂ hz₂) hpre)

/-- Appending the chain `c` as the `n`-th centre keeps the centre chains injective, provided `c`
is a prefix of none of the earlier ones. -/
private theorem injOn_extend_centre {α : Type*} {n : ℕ} {G G' : ℕ → List α} {c : List α}
    (hlt : ∀ j, j < n → G' j = G j) (hge : ∀ j, ¬ j < n → G' j = c)
    (hG : ∀ j j', j < n → j' < n → G j = G j' → j = j') (hc : ∀ j < n, ¬ c <+: G j)
    (j j' : ℕ) (hj : j < n + 1) (hj' : j' < n + 1) (heq : G' j = G' j') : j = j' := by
  by_cases hjn : j < n <;> by_cases hjn' : j' < n
  · rw [hlt j hjn, hlt j' hjn'] at heq
    exact hG j j' hjn hjn' heq
  · rw [hlt j hjn, hge j' hjn'] at heq
    exact absurd (heq ▸ List.prefix_refl _) (hc j hjn)
  · rw [hge j hjn, hlt j' hjn'] at heq
    exact absurd (heq ▸ List.prefix_refl _) (hc j' hjn')
  · omega

/-- After one blow-up, no recorded chain is a prefix of a centre chain, the new centre chain
being that of the blown-up point `p`. -/
private theorem not_prefix_extend {α X X' : Type*} {S : X → Prop} {S' : X' → Prop}
    {F : X → List α} {σ : X' → X} {p : X} (g : ∀ z, σ z = p → α) (F' : X' → List α)
    (hF'on : ∀ z hz, F' z = F p ++ [g z hz]) (hF'off : ∀ z, ¬ σ z = p → F' z = F (σ z))
    {n : ℕ} {G G' : ℕ → List α} (hlt : ∀ j, j < n → G' j = G j)
    (hge : ∀ j, ¬ j < n → G' j = F p) (hp : S p)
    (hF : ∀ x x', S x → S x' → F x <+: F x' → x = x')
    (hoff : ∀ z, ¬ σ z = p → S' z → S (σ z)) (hFG : ∀ x, S x → ∀ j < n, ¬ F x <+: G j) :
    ∀ z, S' z → ∀ j < n + 1, ¬ F' z <+: G' j := by
  intro z hzS j _ hpre
  by_cases hz : σ z = p <;> by_cases hjn : j < n
  · rw [hF'on z hz, hlt j hjn] at hpre
    exact hFG p hp j hjn ((List.prefix_append _ _).trans hpre)
  · rw [hF'on z hz, hge j hjn] at hpre
    have := hpre.length_le
    simp only [List.length_append, List.length_singleton] at this
    omega
  · rw [hF'off z hz, hlt j hjn] at hpre
    exact hFG _ (hoff z hz hzS) j hjn hpre
  · rw [hF'off z hz, hge j hjn] at hpre
    exact hz (hF _ _ (hoff z hz hzS) hp hpre)

/-- The invariant survives blowing up the next centre `p`, a singular point of `C`: a singular
point of the transform over `p` is recorded by the chain of `p` extended by its point of the
blow-up of the tip, one off `p` by the chain of its image, and `p` becomes the new centre. -/
private theorem invAt_succ (N : Set (List PointedSubscheme.{u}))
    (hN : ∀ l ∈ N, ∀ t, l.getLast? = some t → ∀ t' ∈ firstInfinitelyNearSingularities t,
      l ++ [t'] ∈ N)
    {X X' : Scheme.{u}} [IsNoetherian X] (C : X.IdealSheafData) (p : X)
    (hp : IsClosed ({p} : Set X))
    (hpS : p ∈ C.support ∧ ¬ IsRegularLocalRing (X.presheaf.stalk p ⧸ IdealSheafData.stalk C p))
    (e : X' ≅ blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) (n : ℕ)
    (F : X → List PointedSubscheme.{u}) (G : ℕ → List PointedSubscheme.{u})
    (h : InvAt N C n F G) :
    ∃ F' G', InvAt N ((birationalTransform p hp C).comap e.hom) (n + 1) F' G' := by
  classical
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hpSing : SingPt C p := ⟨hp, hpS⟩
  obtain ⟨hFpN, t, htl, htc, htn, hgerm⟩ := h1 p hpSing
  obtain ⟨W, a, b, ha, hb, hbt, hra, hrb, hfib⟩ := exists_blowUp_germ hp htc hgerm
  let σ := e.hom ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
  choose R hR using fun z (hz : σ z = p) => hra (e.hom z) hz
  have hon := fun z hz => singPt_and_germ_of_mem_fibre hp htc e a b hbt hrb hfib (hR z hz) hz
  have hoff := fun z hz => singPt_and_germ_of_notMem_fibre C hp e (z := z) hz
  let g : ∀ z, σ z = p → PointedSubscheme.{u} := fun z hz =>
    ⟨blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{t.q}, htc⟩), birationalTransform t.q htc t.C,
      b (R z hz)⟩
  let F' : X' → List PointedSubscheme.{u} := fun z =>
    if hz : σ z = p then F p ++ [g z hz] else F (σ z)
  have hF'on : ∀ z hz, F' z = F p ++ [g z hz] := fun z hz => dite_eq_left hz
  have hF'off : ∀ z, ¬ σ z = p → F' z = F (σ z) := fun z hz => dite_eq_right hz
  let G' : ℕ → List PointedSubscheme.{u} := fun j => if j < n then G j else F p
  have hG'lt : ∀ j, j < n → G' j = G j := fun j hj => ite_eq_left hj
  have hG'ge : ∀ j, ¬ j < n → G' j = F p := fun j hj => ite_eq_right hj
  have hoffS := fun z hz hzS => (hoff z hz hzS).1
  refine ⟨F', G', fun z hzS => ?_, prefix_injOn_extend g F' hF'on hF'off hpSing h2 hoffS
    (fun z₁ z₂ h₁ h₂ hg => ?_) (fun z₁ z₂ h₁ h₂ h' => ?_), fun j hj => ?_,
    injOn_extend_centre hG'lt hG'ge h4 (h5 p hpSing),
    not_prefix_extend g F' hF'on hF'off hG'lt hG'ge hpSing h2 hoffS h5⟩
  · by_cases hz : σ z = p
    · obtain ⟨hs, hy, g⟩ := hon z hz hzS
      rw [hF'on z hz]
      refine ⟨hN _ hFpN t htl _ ?_, _, List.getLast?_concat, hs.1,
        Stacks.ResolutionOfSurfaces.isNoetherian_blowUp _, g⟩
      rw [firstInfinitelyNearSingularities, dite_eq_left htc]
      exact ⟨_, hs.1, hs.2.1, (mem_support_exceptionalIdeal_iff _ _ _).2 hy, hs.2.2, rfl⟩
    · obtain ⟨hs, g⟩ := hoff z hz hzS
      obtain ⟨hN', t', ht'l, ht'c, ht'n, g'⟩ := h1 _ hs
      rw [hF'off z hz]
      exact ⟨hN', t', ht'l, ht'c, ht'n, g.trans g'⟩
  · simp only [g, PointedSubscheme.mk.injEq, heq_eq_eq, true_and] at hg
    exact e.hom.isOpenEmbedding.injective
      (by rw [← hR z₁ h₁, ← hR z₂ h₂, b.isOpenEmbedding.injective hg])
  · have hnot : ∀ z, ¬ σ z = p → e.hom z ∉
        (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).support :=
      fun z hz hm => hz ((mem_support_exceptionalIdeal_iff p hp _).1 hm)
    exact e.hom.isOpenEmbedding.injective
      (eq_of_blowUpToBase_eq _ (hnot z₁ h₁) (hnot z₂ h₂) h')
  · by_cases hjn : j < n
    · rw [hG'lt j hjn]; exact h3 j hjn
    · rw [hG'ge j hjn]; exact hFpN

end Germs

/-! ### The two parts -/

/-- The ancestor chains of infinitely near singular points of `C₀ ⊆ S₀`. -/
private abbrev chains {S₀ : Scheme.{u}} (C₀ : S₀.IdealSheafData) :
    Set (List PointedSubscheme.{u}) :=
  {l : List PointedSubscheme.{u} | ∃ p : S₀,
        IsClosed ({p} : Set S₀) ∧ p ∈ C₀.support ∧
        ¬ IsRegularLocalRing (S₀.presheaf.stalk p ⧸ AlgebraicGeometry.IdealSheafData.stalk C₀ p) ∧
        l.head? = some ⟨S₀, C₀, p⟩ ∧
        List.IsChain (fun t t' => t' ∈ firstInfinitelyNearSingularities t) l}

private theorem chains_append {S₀ : Scheme.{u}} (C₀ : S₀.IdealSheafData) :
    ∀ l ∈ chains C₀, ∀ t, l.getLast? = some t → ∀ t' ∈ firstInfinitelyNearSingularities t,
      l ++ [t'] ∈ chains C₀ := by
  rintro l ⟨p, hp, hpC, hpr, hhead, hchain⟩ t ht t' ht'
  refine ⟨p, hp, hpC, hpr, ?_, ?_⟩
  · rw [List.head?_append, hhead]; rfl
  · rw [List.isChain_append]
    refine ⟨hchain, List.isChain_singleton _, fun x hx y hy => ?_⟩
    rw [ht, Option.mem_some_iff] at hx
    obtain rfl := Option.mem_some_iff.1 hy
    subst hx
    exact ht'

private theorem isNoetherian_S {S₀ : Scheme.{u}} [IsNoetherian S₀] (s : PointBlowupSequence S₀) :
    ∀ i : ℕ, (i : ℕ∞) ≤ s.length → IsNoetherian (s.S i)
  | 0, _ => isNoetherian_of_iso s.zeroIso
  | i + 1, hi =>
    have hlt := PointBlowupSequence.coe_lt_of_succ_le hi
    have := isNoetherian_S s i hlt.le
    have := Stacks.ResolutionOfSurfaces.isNoetherian_blowUp
      (Scheme.IdealSheafData.vanishingIdeal ⟨{s.p i}, s.isClosed_p i hlt⟩)
    isNoetherian_of_iso (s.blowupIso i hlt)

/-- The invariant holds after the first `k` blow-ups of a weak embedded resolution sequence. -/
private theorem exists_invAt {S₀ : Scheme.{u}} [IsNoetherian S₀] (C₀ : S₀.IdealSheafData)
    (s : PointBlowupSequence S₀) (hs : s.IsWeakEmbeddedResolution C₀) :
    ∀ k : ℕ, (k : ℕ∞) ≤ s.length →
      ∃ F G, InvAt (chains C₀) (s.transformedSubscheme C₀ k) k F G
  | 0, _ => invAt_zero (chains C₀) s.zeroIso C₀
      (fun q hq => ⟨q, hq.1, hq.2.1, hq.2.2, rfl, List.isChain_singleton _⟩)
  | k + 1, hk => by
    have hlt := PointBlowupSequence.coe_lt_of_succ_le hk
    have := isNoetherian_S s k hlt.le
    obtain ⟨F, G, h⟩ := exists_invAt C₀ s hs k hlt.le
    rw [PointBlowupSequence.transformedSubscheme, dite_eq_left hlt]
    exact invAt_succ (chains C₀) (chains_append C₀) _ (s.p k) (s.isClosed_p k hlt) (hs k hlt)
      (s.blowupIso k hlt) k F G h

/-- Every weak embedded resolution sequence has length at most the number of ancestor chains:
its centres inject into them (Kollár 1.42). -/
private theorem length_le_ncard {S₀ : Scheme.{u}} (hS : IsRegularSurface S₀)
    (C₀ : S₀.IdealSheafData) (hfin : (chains C₀).Finite)
    (s : PointBlowupSequence S₀) (hs : s.IsWeakEmbeddedResolution C₀) :
    s.length ≤ ((chains C₀).ncard : ℕ∞) := by
  have key : ∀ k : ℕ, (k : ℕ∞) ≤ s.length → k ≤ (chains C₀).ncard := fun k hk => by
    have : IsNoetherian S₀ := hS.1
    obtain ⟨-, G, -, -, h3, h4, -⟩ := exists_invAt C₀ s hs k hk
    have := Set.ncard_le_ncard_of_injOn (s := Set.Iio k) G (fun j hj => h3 j hj)
      (fun j hj j' hj' heq => h4 j j' hj hj' heq) hfin
    rwa [← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range] at this
  cases h : s.length with
  | top =>
    exfalso
    have := key ((chains C₀).ncard + 1) (by rw [h]; exact le_top)
    omega
  | coe n =>
    exact_mod_cast key n (by rw [h])

/-- A scheme carrying a closed subscheme of dimension one is nonempty. -/
private theorem nonempty_of_topologicalKrullDim_subscheme_eq_one {S₀ : Scheme.{u}}
    (C₀ : S₀.IdealSheafData) (hcurve : topologicalKrullDim C₀.subscheme = 1) : Nonempty S₀ := by
  have hne : Nonempty C₀.subscheme := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : IsEmpty (TopologicalSpace.IrreducibleCloseds C₀.subscheme) :=
      ⟨fun Z => h.elim Z.isIrreducible.nonempty.some⟩
    rw [topologicalKrullDim, Order.krullDim_eq_bot] at hcurve
    exact absurd hcurve (by decide)
  exact ⟨C₀.subschemeι.base hne.some⟩

end MMP.Resolution

/-- If the ancestor chains of infinitely near singular points of a reduced curve `C₀` on a regular
surface `S₀` form a finite set `N`, then every weak embedded resolution sequence for `(S₀, C₀)` has
length at most `N.ncard`, and every maximal weak embedded resolution sequence stops. The
finiteness of `N` implies that `C₀` has finitely many singular points, since each of them gives
the one-element chain `[(S₀, C₀, p)]` at a singular point `p`. -/
@[mmp "lem_kr1c_weak_sequence_length_le_tree"]
public theorem MMP.Resolution.PointBlowupSequence.length_le_ncard_and_stops_of_finite
    {S₀ : AlgebraicGeometry.Scheme.{u}} (hS : MMP.Resolution.IsRegularSurface S₀)
    (C₀ : S₀.IdealSheafData) (hred : AlgebraicGeometry.IsReduced C₀.subscheme)
    (hcurve : topologicalKrullDim C₀.subscheme = 1)
    (hfin : {l : List MMP.Resolution.PointedSubscheme.{u} | ∃ p : S₀,
        IsClosed ({p} : Set S₀) ∧ p ∈ C₀.support ∧
        ¬ IsRegularLocalRing (S₀.presheaf.stalk p ⧸ AlgebraicGeometry.IdealSheafData.stalk C₀ p) ∧
        l.head? = some ⟨S₀, C₀, p⟩ ∧
        List.IsChain (fun t t' => t' ∈ MMP.Resolution.firstInfinitelyNearSingularities t)
          l}.Finite) :
    (∀ s : MMP.Resolution.PointBlowupSequence S₀, s.IsWeakEmbeddedResolution C₀ →
      s.length ≤ ({l : List MMP.Resolution.PointedSubscheme.{u} | ∃ p : S₀,
        IsClosed ({p} : Set S₀) ∧ p ∈ C₀.support ∧
        ¬ IsRegularLocalRing (S₀.presheaf.stalk p ⧸ AlgebraicGeometry.IdealSheafData.stalk C₀ p) ∧
        l.head? = some ⟨S₀, C₀, p⟩ ∧
        List.IsChain (fun t t' => t' ∈ MMP.Resolution.firstInfinitelyNearSingularities t) l}.ncard :
        ℕ∞)) ∧
    ∀ s : MMP.Resolution.PointBlowupSequence S₀, s.IsWeakEmbeddedResolution C₀ →
      (∀ s' : MMP.Resolution.PointBlowupSequence S₀, s'.IsWeakEmbeddedResolution C₀ →
        s.length < s'.length →
        ¬ ((∀ i : ℕ, (i : ℕ∞) ≤ s.length → s'.S i = s.S i) ∧ HEq s'.zeroIso s.zeroIso ∧
          (∀ i : ℕ, (i : ℕ∞) < s.length → HEq (s'.p i) (s.p i)) ∧
          ∀ (i : ℕ) (hi : (i : ℕ∞) < s.length) (hi' : (i : ℕ∞) < s'.length),
            HEq (s'.blowupIso i hi') (s.blowupIso i hi))) →
      s.WeakEmbeddedResolutionStops C₀ := by
  refine ⟨length_le_ncard hS C₀ hfin, fun s hs hmax => ?_⟩
  have hle := length_le_ncard hS C₀ hfin s hs
  obtain ⟨n, hn⟩ : ∃ n : ℕ, s.length = n :=
    ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle) |>.imp
      fun n h => h.symm
  refine ⟨n, hn, fun q hq hqC => ?_⟩
  by_contra hqreg
  have := nonempty_of_topologicalKrullDim_subscheme_eq_one C₀ hcurve
  obtain ⟨s', hs', hlt, hagree⟩ := exists_extension_of_point hq hn C₀ hs hqC hqreg
    (nonempty_blowUp (isRegSurf_S (isRegSurf_of_isRegularSurface hS) s n hn.ge) q hq).some
  exact hmax s' hs' hlt hagree
