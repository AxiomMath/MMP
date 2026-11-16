module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.IndexBound.ClosedFibreLineBundles
public import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.FibreCurveCount
public import MMP.AlgebraicGeometry.Singularities.EtaleNeighbourhoodTerminal

/-!
# Enough exceptional curves over a singular point

Let `(Y, π, y)` be a threefold point setting (`MMP.Fourfold.IsThreefoldPointSetting`), let
`T_y = {y} × ℙ¹ ⊆ Y × ℙ¹` (`MMP.Fourfold.pointSettingCurve`) and let `b = b_{T_y}` be the rank of
its punctured local system (`MMP.Fourfold.curveLocalSystemRank`). Let `M_1, …, M_b` be line
bundles on the scheme fibre `F_y = Ỹ ×_Y Spec κ(y)` whose pullbacks to
`F_{η_{T_y}} = F_y ×_ℂ Spec K_{T_y}` are punctured-independent
(`MMP.Fourfold.IsPuncturedIndependent`) for `π × id : Ỹ × ℙ¹ ⟶ Y × ℙ¹`. Let `q_U : U ⟶ Y` be an
étale morphism from a normal integral quasi-projective complex threefold, `u ∈ U` a closed point
over `y`, and `M̃_i` line bundles on `Ũ = Ỹ ×_Y U` restricting to `M_i` on the scheme fibre
`Ũ ×_U Spec κ(u) = F_y`, where `Ũ` is smooth and integral and `π_U : Ũ ⟶ U` is projective,
birational and an isomorphism over `q_U⁻¹(Y_reg)`. Then for every projective small birational
morphism `g₃ : U' ⟶ U` with `U'` `ℚ`-factorial, the fibre `g₃⁻¹(u)` has at least `b`
irreducible components of dimension one.

The proof takes the chart `A = 𝔸¹ ⊆ ℙ¹` and the generic point `η'` of `{u} × A ⊆ U × A`.
The product `(U × A, q_U × j, η', L̃_i)` is a local étale datum for the pullbacks `L_i` in the
local setting `(Y × ℙ¹, 0, T_y, π × id)`, and `g = g₃ × id` is a projective small birational
morphism with `ℚ`-factorial source. By the degree independence of the transferred divisors, the
scheme fibre `g⁻¹(η')` contains at least `b` proper curves. This fibre is `G ×_ℂ Spec κ(η')`
with `G = g₃⁻¹(u)`, whose irreducible components are the preimages of those of `G`, of the same
dimension. Since `g₃` is small, `G` has dimension at most one: if `g₃` is an isomorphism over a
neighbourhood of `u` the fibre is a closed point, and otherwise it lies in the exceptional set,
of codimension at least two in the threefold `U'`. So each proper curve of `g⁻¹(η')` is a whole
component, and distinct curves give distinct one-dimensional components of `G`.

## Main results

* `MMP.Fourfold.IsThreefoldPointSetting.le_encard_irreducibleComponents_preimage`: the fibre
  `g₃⁻¹(u)` has at least `b_{T_y}` one-dimensional irreducible components.

## Implementation notes

* `Y × ℙ¹`, `π × id`, `T_y` and the map `F_{η_{T_y}} ⟶ F_y` are formed exactly as in
  `MMP.Fourfold.IsThreefoldPointSetting.exists_isPuncturedIndependent_pullback`, and `b_{T_y}` is
  `curveLocalSystemRank T°` for an arbitrary local-system open `T°` of `T_y`.
* The pair `(U, u)` with `q_U` étale and `q_U(u) = y` is an elementary étale neighbourhood
  (`AlgebraicGeometry.ElementaryEtaleNeighborhood`) of `(Y, y)`: the residue field extension
  `κ(y) → κ(u)` is an isomorphism, as both are `ℂ` for closed points of complex varieties. This
  isomorphism identifies `Ũ ×_U Spec κ(u)` with `F_y`; the composite `F_y ⟶ Ũ` is
  `MMP.Fourfold.localEtaleFibreMap`. `U` is a complex scheme through `q_U ≫ s_Y`.
* The reduced structure does not change the underlying space, and the underlying space of the
  scheme fibre `U' ×_U Spec κ(u)` is the preimage `g₃⁻¹(u) ⊆ U'`; the components are counted on
  the subspace `g₃⁻¹(u)`, with `Set.encard`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-! ### Irreducible components and dimension under homeomorphisms -/

/-- Pulling back along a homeomorphism is a bijection on irreducible components. -/
private theorem bijOn_preimage_irreducibleComponents {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) :
    Set.BijOn (fun Z : Set B => e ⁻¹' Z) (irreducibleComponents B) (irreducibleComponents A) := by
  refine ⟨fun Z hZ => preimage_mem_irreducibleComponents hZ e.isOpenEmbedding ?_,
    fun Z _ Z' _ hZZ' => (Set.preimage_injective.mpr e.surjective) hZZ', fun W hW =>
      ⟨e.symm ⁻¹' W, preimage_mem_irreducibleComponents hW e.symm.isOpenEmbedding ?_, ?_⟩⟩
  · rw [e.surjective.range_eq, Set.inter_univ]
    exact hZ.1.1
  · rw [e.symm.surjective.range_eq, Set.inter_univ]
    exact hW.1.1
  · ext x
    simp

/-- Pulling back along a homeomorphism preserves the dimension of a subset. -/
private theorem topologicalKrullDim_preimage_homeomorph {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) (Z : Set B) :
    topologicalKrullDim (e ⁻¹' Z) = topologicalKrullDim Z :=
  IsHomeomorph.topologicalKrullDim_eq _
    (e.subtype (p := (· ∈ e ⁻¹' Z)) (q := (· ∈ Z)) fun _ => Iff.rfl).isHomeomorph

/-! ### Base change to a field extension of `ℂ` -/

/-- For a scheme `X` locally of finite type over `ℂ` and any field `K` over `ℂ`, the irreducible
components of `X_K` are the preimages of those of `X`, and preimages of locally closed subsets
keep their dimension. -/
private theorem bijOn_and_topologicalKrullDim_baseChange {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType f] {K : Type} [Field K]
    (h' : Spec (.of K) ⟶ Spec (.of ℂ)) :
    Set.BijOn (fun Z : Set X => (pullback.fst f h').base ⁻¹' Z) (irreducibleComponents X)
        (irreducibleComponents (pullback f h' : Scheme.{0})) ∧
      ∀ Z : Set X, IsLocallyClosed Z →
        topologicalKrullDim ((pullback.fst f h').base ⁻¹' Z) = topologicalKrullDim Z := by
  rw [← Spec.map_preimage h']
  generalize Spec.preimage h' = φ
  letI : Algebra ℂ K := φ.hom.toAlgebra
  obtain ⟨-, -, -, h1, h2⟩ :=
    MMP.isReduced_isIntegral_isNormal_dim_baseChange_of_isAlgClosed (K := K) f
  exact ⟨h1, h2⟩

/-! ### The fibre of a small morphism over a closed point -/

/-- Let `g₃ : U' ⟶ U` be a morphism from an integral threefold over `ℂ` whose exceptional set has
codimension at least two. Every point `z` of the fibre over a closed point `u` has height at most
one: either `g₃` is an isomorphism over a neighbourhood of `u`, and then `z` is a closed point, or
`z` lies in the exceptional set and has coheight at least two. -/
private theorem height_le_one_of_map_eq {U U' : Scheme.{0}} [IsIntegral U']
    (sU' : U' ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sU'] (hdim : topologicalKrullDim U' = 3)
    (g₃ : U' ⟶ U) (hsmall : 2 ≤ closedsCodimension (exceptionalSet g₃)) {u : U}
    (hu : IsClosed ({u} : Set U)) {z : U'} (hz : g₃.base z = u) : Order.height z ≤ 1 := by
  by_cases hV : u ∈ biregularLocus g₃
  · haveI : IsIso (g₃ ∣_ biregularLocus g₃) := isBiregular_biregularLocus g₃
    have hinj : ∀ a b : U', g₃.base a ∈ biregularLocus g₃ → g₃.base b ∈ biregularLocus g₃ →
        g₃.base a = g₃.base b → a = b := by
      intro a b ha hb hab
      have := (g₃ ∣_ biregularLocus g₃).homeomorph.injective
        (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) (Subtype.ext ?_)
      · exact congrArg Subtype.val this
      · exact (morphismRestrict_base_coe g₃ (biregularLocus g₃) ⟨a, ha⟩).trans
          (hab.trans (morphismRestrict_base_coe g₃ (biregularLocus g₃) ⟨b, hb⟩).symm)
    have hmin : IsMin z := by
      intro w hw
      have hgw : g₃.base w = u := ((show z ⤳ w from hw).map g₃.continuous).mem_closed hu hz
      rw [hinj w z (hgw ▸ hV) (hz ▸ hV) (hgw.trans hz.symm)]
    exact (Order.height_eq_zero.mpr hmin).trans_le zero_le_one
  · have hc : 2 ≤ Order.coheight z :=
      MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hsmall z (by rwa [← hz] at hV)
    have hsum := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sU' z
    rw [topologicalKrullDim_closure_singleton_eq_height, hdim] at hsum
    have h3 : Order.height z + Order.coheight z = 3 := WithBot.coe_injective hsum
    by_contra! hlt
    have h4 := add_le_add (Order.add_one_le_of_lt hlt) hc
    rw [h3] at h4
    norm_num at h4

/-- If every point of `X` over `y` has height at most one, the scheme fibre `f⁻¹(y)` has
dimension at most one. -/
private theorem topologicalKrullDim_fiber_le_one {X Y : Scheme.{0}} (f : X ⟶ Y) (y : Y)
    (h : ∀ x : X, f.base x = y → Order.height x ≤ 1) :
    topologicalKrullDim (f.fiber y) ≤ 1 := by
  have hinj : Function.Injective (f.fiberι y).base := fun a b hab =>
    (f.fiberHomeo y).injective (Subtype.ext (by
      rwa [Scheme.Hom.fiberHomeo_apply, Scheme.Hom.fiberHomeo_apply]))
  have hmono : StrictMono (f.fiberι y).base := by
    intro a b hab
    have hle : (f.fiberι y).base a ≤ (f.fiberι y).base b :=
      (show b ⤳ a from hab.le).map (f.fiberι y).continuous
    exact lt_of_le_not_ge hle fun hba => hab.ne (hinj (Specializes.antisymm hba hle).eq)
  change Order.krullDim (IrreducibleCloseds _) ≤ 1
  rw [Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints, Order.krullDim_eq_iSup_height]
  refine iSup_le fun a => ?_
  have hy : f.base ((f.fiberι y).base a) = y := by
    rw [← Scheme.Hom.fiberHomeo_apply]
    exact (f.fiberHomeo y a).2
  exact_mod_cast (Order.height_le_height_apply_of_strictMono _ hmono a).trans (h _ hy)

/-! ### Counting curves -/

/-- Let `F` be a scheme of dimension at most one and `φ : F → Y` a map such that `Z ↦ φ⁻¹(Z)` is
a bijection from the irreducible components of `Y` onto those of `F`, preserving dimension. Then
distinct points of `F` whose closures are curves give distinct one-dimensional components of
`Y`. -/
private theorem card_le_encard_of_bijOn {F : Scheme.{0}} {Y : Type*} [TopologicalSpace Y] (φ : F → Y)
    (hdim : topologicalKrullDim F ≤ 1)
    (hbij : Set.BijOn (fun Z : Set Y => φ ⁻¹' Z) (irreducibleComponents Y)
      (irreducibleComponents F))
    (hd : ∀ Z ∈ irreducibleComponents Y, topologicalKrullDim (φ ⁻¹' Z) = topologicalKrullDim Z)
    {ι : Type*} (pt : ι → F) (hpt : Function.Injective pt)
    (h1 : ∀ i, topologicalKrullDim (closure {pt i}) = 1) :
    ENat.card ι ≤ {Z ∈ irreducibleComponents Y | topologicalKrullDim Z = 1}.encard := by
  have hheight : ∀ i, Order.height (pt i) = 1 := fun i => by
    have := h1 i
    rw [topologicalKrullDim_closure_singleton_eq_height] at this
    exact_mod_cast this
  have hle : ∀ w : F, Order.height w ≤ 1 := fun w => by
    have := (topologicalKrullDim_subspace_le F (closure {w})).trans hdim
    rw [topologicalKrullDim_closure_singleton_eq_height] at this
    exact_mod_cast this
  have hcomp : ∀ i, closure {pt i} ∈ irreducibleComponents F := fun i => by
    rw [← isMax_iff_closure_mem_irreducibleComponents]
    intro w hw
    by_contra hne
    have := Order.height_strictMono (lt_of_le_not_ge hw hne) (by rw [hheight i]; simp)
    rw [hheight i] at this
    exact absurd (hle w) (not_le.mpr this)
  choose Z hZ hZeq using fun i => hbij.surjOn (hcomp i)
  have hZ1 : ∀ i, topologicalKrullDim (Z i) = 1 := fun i => by
    rw [← hd _ (hZ i)]
    exact (congrArg (fun S : Set F => topologicalKrullDim S) (hZeq i)).trans (h1 i)
  let f : ι → {Z ∈ irreducibleComponents Y | topologicalKrullDim Z = 1} :=
    fun i => ⟨Z i, hZ i, hZ1 i⟩
  exact ENat.card_le_card_of_injective (f := f) fun i j hij => hpt
    (inseparable_iff_closure_eq.mpr (by
      rw [← hZeq i, ← hZeq j, show Z i = Z j from congrArg Subtype.val hij])).eq

/-- The curves of a scheme fibre `g⁻¹(η)` which is identified with `G ×_ℂ Spec κ(η)`, for
`G = g₃⁻¹(u)` the fibre of a small morphism `g₃` of threefolds over a closed point `u`, give
distinct one-dimensional irreducible components of `g₃⁻¹(u)`. -/
private theorem card_properCurve_le_encard {U U' : Scheme.{0}} [IsIntegral U']
    (sU : U ⟶ Spec (.of ℂ)) (g₃ : U' ⟶ U) [LocallyOfFiniteType g₃] [LocallyOfFiniteType sU]
    (hdim : topologicalKrullDim U' = 3) (hsmall : 2 ≤ closedsCodimension (exceptionalSet g₃))
    {u : U} (hu : IsClosed ({u} : Set U)) [IsIso (U.fromSpecResidueField u ≫ sU)]
    {Y' V : Scheme.{0}} (g : Y' ⟶ V) (η : V) (h' : Spec (V.residueField η) ⟶ Spec (.of ℂ))
    (ψ : g.fiber η ⟶ pullback
      (pullback.snd g₃ (U.fromSpecResidueField u) ≫ U.fromSpecResidueField u ≫ sU) h')
    (hψ : IsIso ψ) :
    ENat.card (ProperCurve (g.fiberToSpecResidueField η)) ≤
      {Z ∈ irreducibleComponents ↥(g₃.base ⁻¹' {u}) | topologicalKrullDim Z = 1}.encard := by
  obtain ⟨hbij, hd⟩ := bijOn_and_topologicalKrullDim_baseChange (K := V.residueField η)
    (pullback.snd g₃ (U.fromSpecResidueField u) ≫ U.fromSpecResidueField u ≫ sU) h'
  let p := (pullback.fst
    (pullback.snd g₃ (U.fromSpecResidueField u) ≫ U.fromSpecResidueField u ≫ sU) h').base
  let e := ψ.homeomorph
  let e₂ := g₃.fiberHomeo u
  have hbijφ : Set.BijOn (fun Z => (e₂ ∘ p ∘ e) ⁻¹' Z) (irreducibleComponents ↥(g₃.base ⁻¹' {u}))
      (irreducibleComponents (g.fiber η)) :=
    (bijOn_preimage_irreducibleComponents e).comp
      (hbij.comp (bijOn_preimage_irreducibleComponents e₂))
  have hdφ : ∀ Z ∈ irreducibleComponents ↥(g₃.base ⁻¹' {u}),
      topologicalKrullDim ((e₂ ∘ p ∘ e) ⁻¹' Z) = topologicalKrullDim Z := fun Z hZ => by
    have hlc : IsLocallyClosed (e₂ ⁻¹' Z) := (isClosed_of_mem_irreducibleComponents _
      ((bijOn_preimage_irreducibleComponents e₂).mapsTo hZ)).isLocallyClosed
    exact (topologicalKrullDim_preimage_homeomorph e _).trans
      ((hd _ hlc).trans (topologicalKrullDim_preimage_homeomorph e₂ Z))
  have hdimF : topologicalKrullDim (g.fiber η) ≤ 1 := by
    rw [IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph]
    have := hd Set.univ isClosed_univ.isLocallyClosed
    rw [Set.preimage_univ,
      IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph,
      IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph] at this
    rw [this]
    exact topologicalKrullDim_fiber_le_one g₃ u fun z hz =>
      height_le_one_of_map_eq (g₃ ≫ sU) hdim g₃ hsmall hu hz
  refine card_le_encard_of_bijOn (e₂ ∘ p ∘ e) hdimF hbijφ hdφ (fun C => C.point)
    (fun C C' h => ProperCurve.ext h) fun C => ?_
  rw [← MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq]
  exact C.dim_eq

/-- In a fibre product `X ×_S L` with `L` irreducible, the fibre of the first projection over a
closed point `x ∈ X` with `Spec κ(x) ⟶ S` an isomorphism has a generic point: it is the image of
`Spec κ(x) ×_S L ≅ L`. -/
private theorem exists_isGenericPoint_preimage_fst {S X L : Scheme.{0}} (sX : X ⟶ S) (sL : L ⟶ S)
    [IrreducibleSpace L] {x : X} (hx : IsClosed ({x} : Set X))
    [IsIso (X.fromSpecResidueField x ≫ sX)] :
    ∃ η, IsGenericPoint η ((pullback.fst sX sL).base ⁻¹' {x}) := by
  have hrange : Set.range (pullback.snd (X.fromSpecResidueField x) (pullback.fst sX sL)).base =
      (pullback.fst sX sL).base ⁻¹' {x} := by
    rw [Scheme.Pullback.range_snd, Scheme.range_fromSpecResidueField]
  let φ : L ⟶ pullback (X.fromSpecResidueField x) (pullback.fst sX sL) :=
    inv (pullback.snd (X.fromSpecResidueField x ≫ sX) sL) ≫
      (pullbackRightPullbackFstIso sX sL (X.fromSpecResidueField x)).inv
  have hirr : IsIrreducible ((pullback.fst sX sL).base ⁻¹' {x}) := by
    have h2 : Set.range (pullback.snd (X.fromSpecResidueField x) (pullback.fst sX sL)).base =
        Set.range (φ ≫ pullback.snd (X.fromSpecResidueField x) (pullback.fst sX sL)).base := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, φ.surjective.range_comp]
    rw [← hrange, h2, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ L).image _ (φ ≫ _).continuous.continuousOn
  have hcl : IsClosed ((pullback.fst sX sL).base ⁻¹' {x}) :=
    hx.preimage (pullback.fst sX sL).base.hom.continuous
  refine ⟨hirr.genericPoint, ?_⟩
  simpa [hcl.closure_eq] using hirr.isGenericPoint_genericPoint_closure

/-- **Enough exceptional curves over the point.** Let `(Y, π, y)` be a threefold point setting,
`b = b_{T_y}` and `M_1, …, M_b` line bundles on `F_y` with punctured-independent pullbacks to
`F_{η_{T_y}}`. Let `(U, u)` be an elementary étale neighbourhood of `(Y, y)` with `U` a normal
integral quasi-projective complex threefold and `u` closed, and `M̃_i` line bundles on
`Ũ = Ỹ ×_Y U` restricting to `M_i` on `F_y`, with `Ũ` smooth and integral and `π_U : Ũ ⟶ U`
projective, birational and an isomorphism over `q_U⁻¹(Y_reg)`. Then for every projective small
birational `g₃ : U' ⟶ U` with `U'` `ℚ`-factorial, `g₃⁻¹(u)` has at least `b` irreducible
components of dimension one. -/
@[mmp "lem_mmp_indexb_enough_curves"]
public theorem IsThreefoldPointSetting.le_encard_irreducibleComponents_preimage
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {π : Yt ⟶ Y} {y : Y} (h : IsThreefoldPointSetting sY π y)
    (T : IrreducibleCloseds ↥(pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))))
    (hT : (T : Set ↥(pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ)))) = pointSettingCurve sY y)
    (To : (curveScheme T).Opens)
    (hTo : IsLocalSystemOpen (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) To)
    (M : Fin (curveLocalSystemRank
        (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) To) →
        (pointSettingFibre π y).Modules)
    (hMinv : ∀ i, SheafOfModules.IsInvertible (pointSettingFibre π y).presheaf
      (pointSettingFibre π y).ringCatSheaf.2 (M i))
    (hM : ∃ hπ : IsBiregular
          (pullback.map (π ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) sY
            (projectiveLine ℂ ↘ Spec (.of ℂ)) π (𝟙 _) (𝟙 _) (by simp) (by simp))
          (smoothLocus (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY)),
        IsPuncturedIndependent (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) hπ
          (T := T) fun i ↦ (Scheme.Modules.pullback
            (pullback.map _ _ π (Y.fromSpecResidueField y)
              (pullback.fst (π ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)))
              (Spec.map ((pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ))).residueFieldMap
                  (localSettingGenericPoint T)) ≫
                Spec.map (Y.residueFieldCongr (show y =
                  (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ))).base
                    (localSettingGenericPoint T) from
                  ((Set.ext_iff.1 hT _).1
                    (isGenericPoint_localSettingGenericPoint T).mem).symm)).hom)
              (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ))) (by simp)
              (by
                rw [Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField,
                  Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]) :
              genericFibre _ T ⟶ pointSettingFibre π y)).obj (M i))
    (U : ElementaryEtaleNeighborhood Y y)
    [IsIntegral U.obj.scheme] [IsLocallyNoetherian U.obj.scheme] [IsNormal U.obj.scheme]
    (hU : IsQuasiProjectiveVariety ℂ (U.obj.toBase ≫ sY))
    (hUn : IsNormalVariety ℂ (U.obj.toBase ≫ sY))
    (hUdim : topologicalKrullDim U.obj.scheme = 3)
    (hu : IsClosed ({U.obj.point} : Set U.obj.scheme))
    (Mt : Fin (curveLocalSystemRank
        (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) To) →
        (pullback π U.obj.toBase).Modules)
    (hMt : ∀ i, SheafOfModules.IsInvertible (pullback π U.obj.toBase).presheaf
      (pullback π U.obj.toBase).ringCatSheaf.2 (Mt i))
    (hMtr : ∀ i, Nonempty
      ((Scheme.Modules.pullback (localEtaleFibreMap π U)).obj (Mt i) ≅ M i))
    (hUt : IsIntegral (pullback π U.obj.toBase))
    (hUts : Smooth (pullback.snd π U.obj.toBase ≫ U.obj.toBase ≫ sY))
    (hπUp : IsProjectiveMorphism (pullback.snd π U.obj.toBase))
    (hπUb : IsBirationalMorphism (pullback.snd π U.obj.toBase))
    (hπUi : IsBiregular (pullback.snd π U.obj.toBase) (U.obj.toBase ⁻¹ᵁ smoothLocus sY))
    {U' : Scheme.{0}} [IsIntegral U'] [IsLocallyNoetherian U'] [IsNormal U']
    {sU' : U' ⟶ Spec (.of ℂ)} {g₃ : U' ⟶ U.obj.scheme}
    (hg : IsProjectiveMorphism g₃) (hgs : IsSmallMorphism sU' (U.obj.toBase ≫ sY) g₃)
    (hU' : IsQFactorial sU') :
    (curveLocalSystemRank (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) To : ℕ∞) ≤
      {Z ∈ irreducibleComponents ↥(g₃.base ⁻¹' {U.obj.point}) |
        topologicalKrullDim Z = 1}.encard := by
  obtain rfl := hgs.comp_eq
  obtain ⟨hπ, hL⟩ := hM
  obtain ⟨⟨hI, hLN, hN, T', hT', hLS⟩, -, -, -, -⟩ := h.isLocalSetting_pullback_projectiveLine
  obtain rfl : T = T' := SetLike.coe_injective (hT.trans hT'.symm)
  haveI : LocallyOfFiniteType (U.obj.toBase ≫ sY) := hUn.1.toLocallyOfFiniteType
  haveI : IsIso (U.obj.scheme.fromSpecResidueField U.obj.point ≫ U.obj.toBase ≫ sY) := by
    rw [← SpecMap_residueFieldIsoBase_inv (U.obj.toBase ≫ sY) U.obj.point hu]
    infer_instance
  obtain ⟨η', hη'⟩ := exists_isGenericPoint_preimage_fst (U.obj.toBase ≫ sY)
    (projectiveLineXChart ℂ ≫ projectiveLine ℂ ↘ Spec (.of ℂ)) hu
  obtain ⟨hq, hmap, hel, hqp, hnorm, hinv, hres, hprod⟩ :=
    h.exists_localEtaleDatum_prod T hT M hMinv U hU hUn hUdim hu Mt hMt hMtr hUt hUts hπUp hπUb
      hπUi (projectiveLineXChart ℂ) η' hη'
  obtain ⟨hgp, hgsm, ⟨hLN', hN', hQ⟩, hiso⟩ := hprod g₃ hg hgs hU'
  have hb := LocalEtaleDatum.le_card_properCurve_fiber hLS hL
    (⟨⟨_, hel⟩, hqp, hnorm, _, hinv, hres⟩ : LocalEtaleDatum _ T _ _) _ hgsm hgp hQ
  haveI := hgs.isProper
  have hU'dim : topologicalKrullDim U' = 3 := by
    haveI := hUn.1
    haveI := hgs.isNormalVariety_source.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism
      (U.obj.toBase ≫ sY) (g₃ ≫ U.obj.toBase ≫ sY) hgs.isBirationalMorphism]
    exact hUdim
  exact hb.trans (card_properCurve_le_encard (U.obj.toBase ≫ sY) g₃ hU'dim hgs.two_le_codimension hu
    _ _ _ _ hiso)

end MMP.Fourfold

end
