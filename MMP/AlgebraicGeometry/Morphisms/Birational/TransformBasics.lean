module

public import MMP.AlgebraicGeometry.Morphisms.Birational.Transform
public import MMP.AlgebraicGeometry.Divisor.Principal

/-!
# Elementary facts on maps, birational transforms and `ℚ`-Cartier divisors (KM Notation 0.4)

* The birational transform `f_*(Z)` of a closed subset may be computed on any representative
  `(U, f_U)` of `f` with `Z ∩ U` dense in `Z`.
* The inverse of a birational map is unique.
* A prime divisor `E` of `X` is exceptional for a birational morphism `f : X → X'` if and only if
  `f(E)` has closure of codimension at least two.
* If `mD` is Cartier for a `ℚ`-Cartier `ℚ`-divisor `D`, the Cartier index `m_D` divides `m`.

## Main results

* `MMP.Positivity.closure_image_eq_transform`
* `MMP.Positivity.IsBirational.existsUnique_isInverse`
* `MMP.Positivity.isExceptional_toRationalMap_iff`
* `MMP.Mori.QDivisor.cartierIndex_dvd`
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Positivity

open MMP.Mori

variable {X Y : Scheme.{u}}

/-- Two partial maps from a reduced scheme to a separated scheme representing the same rational
map agree at every point of the intersection of their domains. -/
theorem PartialMap.hom_apply_eq_of_toRationalMap_eq [IsReduced X] [IsSeparated (Y ↘ ⊤_ Scheme)]
    {g g' : X.PartialMap Y} (h : g.toRationalMap = g'.toRationalMap) {x : X}
    (hx : x ∈ g.domain) (hx' : x ∈ g'.domain) : g.hom ⟨x, hx⟩ = g'.hom ⟨x, hx'⟩ := by
  have e : X.homOfLE (inf_le_left : g.domain ⊓ g'.domain ≤ g.domain) ≫ g.hom =
      X.homOfLE (inf_le_right : g.domain ⊓ g'.domain ≤ g'.domain) ≫ g'.hom :=
    (Scheme.PartialMap.equiv_iff_of_isSeparated (S := ⊤_ Scheme)).mp
      (Scheme.PartialMap.toRationalMap_eq_iff.mp h)
  let p : (g.domain ⊓ g'.domain).toScheme :=
    ⟨x, show x ∈ g.domain ⊓ g'.domain from ⟨hx, hx'⟩⟩
  have h1 : (X.homOfLE (inf_le_left : g.domain ⊓ g'.domain ≤ g.domain)) p = ⟨x, hx⟩ :=
    Subtype.ext (Scheme.homOfLE_apply _ _)
  have h2 : (X.homOfLE (inf_le_right : g.domain ⊓ g'.domain ≤ g'.domain)) p =
    ⟨x, hx'⟩ := Subtype.ext (Scheme.homOfLE_apply _ _)
  rw [← h1, ← h2, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, e]

/-- Let `g, g'` be partial maps from a reduced scheme to a separated scheme representing the same
rational map, and `Z ⊆ X` with `Z ∩ dom g` dense in `Z`. Then `g'(Z ∩ dom g')` lies in the closure
of `g(Z ∩ dom g)`. -/
theorem PartialMap.image_subset_closure_image [IsReduced X] [IsSeparated (Y ↘ ⊤_ Scheme)]
    {g g' : X.PartialMap Y} (h : g.toRationalMap = g'.toRationalMap) {Z : Set X}
    (hZ : Z ⊆ closure (Z ∩ g.domain)) :
    g'.hom '' (g'.domain.ι ⁻¹' Z) ⊆ closure (g.hom '' (g.domain.ι ⁻¹' Z)) := by
  rintro _ ⟨p, hp, rfl⟩
  have hpA : p ∈ closure {q : g'.domain.toScheme | q.1 ∈ Z ∧ q.1 ∈ g.domain} := by
    rw [g'.domain.ι.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image]
    have hι : g'.domain.ι p = p.1 := Scheme.Opens.ι_apply _ _
    have hp' : g'.domain.ι p ∈ (g'.domain : Set X) ∩ closure (Z ∩ g.domain) := by
      rw [hι]
      exact ⟨p.2, hZ (hι ▸ hp)⟩
    refine closure_mono ?_ (g'.domain.isOpen.inter_closure hp')
    rintro y ⟨hy', hyZ, hyg⟩
    exact ⟨⟨y, hy'⟩, ⟨hyZ, hyg⟩, Scheme.Opens.ι_apply _ _⟩
  refine closure_mono ?_ (image_closure_subset_closure_image g'.hom.continuous ⟨p, hpA, rfl⟩)
  rintro _ ⟨q, ⟨hqZ, hqg⟩, rfl⟩
  refine ⟨⟨q.1, hqg⟩, ?_, hom_apply_eq_of_toRationalMap_eq h hqg q.2⟩
  change g.domain.ι ⟨q.1, hqg⟩ ∈ Z
  rwa [Scheme.Opens.ι_apply]

/-- The image of `Z` under the partial map `f : ⊤ ⟶ Y` of a morphism is `f(Z)`. -/
theorem image_toPartialMap_hom (f : X ⟶ Y) (Z : Set X) :
    f.toPartialMap.hom '' (f.toPartialMap.domain.ι ⁻¹' Z) = f '' Z := by
  change (X.topIso.hom ≫ f) '' ((⊤ : X.Opens).ι ⁻¹' Z) = f '' Z
  rw [Scheme.topIso_hom, Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp,
    Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι, TopologicalSpace.Opens.coe_top,
    Set.inter_univ]

/-- **KM Notation 0.4(11), independence of the dense open.** Let `X` be a reduced scheme, `Y` a
separated scheme, `f : X ⤏ Y` a map, `Z ⊆ X` a closed subset and `(U, f_U)` a representative of
`f` such that `Z⁰ = Z ∩ U` is dense in `Z`. Then `f_*(Z)` is the closure of `f_U(Z⁰)`. -/
@[mmp "lem_km0_birational_transform_independent_of_open"]
theorem closure_image_eq_transform [IsReduced X] [IsSeparated (Y ↘ ⊤_ Scheme)]
    {f : Scheme.RationalMap X Y} (g : X.PartialMap Y) (hg : g.toRationalMap = f) (Z : Closeds X)
    (hZ : closure ((Z : Set X) ∩ g.domain) = Z) :
    Closeds.closure (g.hom '' (g.domain.ι ⁻¹' Z)) = RationalMap.transform f Z := by
  refine le_antisymm (Closeds.closure_le.mpr (RationalMap.image_subset_transform g hg Z)) ?_
  refine RationalMap.transform_le_iff.mpr fun g' hg' ↦ ?_
  exact PartialMap.image_subset_closure_image (hg.trans hg'.symm) hZ.symm.subset

/-- If `i : W ⟶ V` lifts `e ∣_ W` through `V ≤ target e` (for an open `W ≤ source e`), then
`i ≫ e⁻¹ ∣_ V` is the inclusion of `W`. -/
theorem PartialIso.comp_homOfLE_iso_inv_ι (e : X.PartialIso Y) {W : X.Opens} (h1 : W ≤ e.source)
    {V : Y.Opens} (hV : V ≤ e.target) (i : W.toScheme ⟶ V.toScheme)
    (hi : i ≫ V.ι = X.homOfLE h1 ≫ e.iso.hom ≫ e.target.ι) :
    i ≫ Y.homOfLE hV ≫ e.iso.inv ≫ e.source.ι = W.ι := by
  have : i ≫ Y.homOfLE hV = X.homOfLE h1 ≫ e.iso.hom := by
    rw [← cancel_mono e.target.ι]
    simp [hi]
  rw [← Category.assoc, this]
  simp

/-- The range of an open immersion factoring through `U.ι` lies in `U`. -/
theorem opensRange_comp_comp_ι_le {Z : Scheme.{u}} (a : X ⟶ Z) (U : Y.Opens)
    (b : Z ⟶ U.toScheme) [IsOpenImmersion (a ≫ b ≫ U.ι)] : (a ≫ b ≫ U.ι).opensRange ≤ U := by
  change ((a ≫ b ≫ U.ι).opensRange : Set Y) ⊆ U
  rw [Scheme.Hom.coe_opensRange, ← Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp]
  exact (Set.range_comp_subset_range _ _).trans (Scheme.Opens.range_ι _).le

/-- Two partial isomorphisms with the same rational map have inverses with the same rational
map. -/
theorem PartialIso.symm_toRationalMap_eq {e e' : X.PartialIso Y}
    (h : e.toRationalMap = e'.toRationalMap) : e.symm.toRationalMap = e'.symm.toRationalMap := by
  obtain ⟨W, hW, h1, h2, hWe⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp h
  replace h1 : W ≤ e.source := h1
  replace h2 : W ≤ e'.source := h2
  have hWe' : X.homOfLE h1 ≫ e.iso.hom ≫ e.target.ι = X.homOfLE h2 ≫ e'.iso.hom ≫ e'.target.ι :=
    hWe
  have : IsDominant (X.homOfLE h1) := Opens.isDominant_homOfLE hW h1
  have : IsDominant e.target.ι := Opens.isDominant_ι e.dense_target
  have hV1 := opensRange_comp_comp_ι_le (X.homOfLE h1) e.target e.iso.hom
  have hV2 : (X.homOfLE h1 ≫ e.iso.hom ≫ e.target.ι).opensRange ≤ e'.target := by
    simpa only [← hWe'] using opensRange_comp_comp_ι_le (X.homOfLE h2) e'.target e'.iso.hom
  have hVd : Dense ((X.homOfLE h1 ≫ e.iso.hom ≫ e.target.ι).opensRange : Set Y) := by
    rw [Scheme.Hom.coe_opensRange]
    exact (X.homOfLE h1 ≫ e.iso.hom ≫ e.target.ι).denseRange
  rw [Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨_, hVd, hV1, hV2, ?_⟩
  change Y.homOfLE hV1 ≫ e.iso.inv ≫ e.source.ι = Y.homOfLE hV2 ≫ e'.iso.inv ≫ e'.source.ι
  rw [← cancel_epi (X.homOfLE h1 ≫ e.iso.hom ≫ e.target.ι).isoOpensRange.hom,
    comp_homOfLE_iso_inv_ι e h1 hV1 _ (by simp),
    comp_homOfLE_iso_inv_ι e' h2 hV2 _ (by simp [hWe'])]

/-- **KM 0.4, the inverse of a birational map.** Every birational map `f : X ⤏ Y` has exactly one
inverse. -/
@[mmp "lem_km0_inverse_birational_map_exists_unique"]
theorem IsBirational.existsUnique_isInverse {f : Scheme.RationalMap X Y}
    (hf : RationalMap.IsBirational f) :
    ∃! h : Scheme.RationalMap Y X, RationalMap.IsInverse f h := by
  obtain ⟨h, H⟩ := hf.exists_isInverse
  refine ⟨h, H, fun h' ⟨e', he', hh'⟩ ↦ ?_⟩
  obtain ⟨e, he, rfl⟩ := H
  rw [← hh']
  exact PartialIso.symm_toRationalMap_eq (he'.trans he.symm)

/-- **The exceptional divisors of a morphism.** Let `f : X → Y` be a morphism of locally Noetherian
normal schemes with `Y` separated, and `E ⊆ X` a prime divisor. Then `E` is `f`-exceptional if and
only if `codim_Y \overline{f(E)} ≥ 2`. Birationality of `f` is not needed: a morphism is defined
everywhere, so only the transform of `E` enters. -/
@[mmp "lem_km0_exceptional_divisor_of_morphism"]
theorem isExceptional_toRationalMap_iff [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsSeparated (Y ↘ ⊤_ Scheme)] {f : X ⟶ Y}
    (E : MMP.Mori.PrimeDivisor X) :
    RationalMap.IsExceptional (X := X) f.toRationalMap E ↔
      2 ≤ closedsCodimension (Closeds.closure (f '' (E.idealSheaf.support : Set X))) := by
  have hdef : RationalMap.DefinedAt (X := X) f.toRationalMap E.genericPoint := by
    rw [RationalMap.DefinedAt, RationalMap.dom_toRationalMap_hom]
    trivial
  have htr := closure_image_eq_transform f.toPartialMap rfl E.idealSheaf.support (by
    change closure ((E.idealSheaf.support : Set X) ∩ ((⊤ : X.Opens) : Set X)) = _
    rw [TopologicalSpace.Opens.coe_top, Set.inter_univ, E.idealSheaf.support.isClosed.closure_eq])
  rw [RationalMap.isExceptional_iff, ← htr, image_toPartialMap_hom]
  exact ⟨fun h ↦ h hdef, fun h _ ↦ h⟩

/-- **KM Notation 0.4(1).** Let `D` be a `ℚ`-Cartier `ℚ`-divisor on a normal scheme `X` and
`m ∈ ℤ` such that `mD` is a divisor and is Cartier. Then the Cartier index `m_D` divides `m`. -/
@[mmp "lem_km0_q_cartier_multiples"]
theorem _root_.MMP.Mori.QDivisor.cartierIndex_dvd [IsLocallyNoetherian X] [IsNormal X]
    {D : QDivisor X} (h : D.IsQCartier) {m : ℤ} (hm : (m • D).IsCartierDivisor) :
    (D.cartierIndex h : ℤ) ∣ m := by
  set n := D.cartierIndex h
  have hn : 0 < n := QDivisor.cartierIndex_pos h
  obtain ⟨A, hA, hAc⟩ := hm
  obtain ⟨B, hB, hBc⟩ := QDivisor.isCartierDivisor_cartierIndex_smul h
  have key : (m % (n : ℤ)) • D = Divisor.toQDivisor (A - (m / (n : ℤ)) • B) := by
    rw [map_sub, map_zsmul, hA, hB, smul_smul, ← sub_smul, Int.emod_def, mul_comm]
  by_contra hd
  have hne : m % (n : ℤ) ≠ 0 := fun h0 ↦ hd (Int.dvd_of_emod_eq_zero h0)
  have hnn : 0 ≤ m % (n : ℤ) := Int.emod_nonneg m (by omega)
  have hlt : m % (n : ℤ) < n := Int.emod_lt_of_pos m (by omega)
  have hle := QDivisor.cartierIndex_le h (m := (m % (n : ℤ)).toNat) (by omega) (by
    rw [Int.toNat_of_nonneg hnn]
    exact ⟨_, key.symm, hAc.sub (hBc.zsmul _)⟩)
  omega

end MMP.Positivity
