module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.StacksPresentation

/-!
# The normal fibre in two charts, for Stacks vector bundles

Let `σ : Y ⟶ 𝐕(ℰ)` be a section of the vector bundle of a quasi-coherent `𝒪_Y`-module `ℰ`,
finite locally free of rank `r`, on a complex scheme `Y`, and `x ∈ Y(ℂ)` a point of the opens
`V`, `V'` of two charts `c = (V, b)`, `c' = (V', b')` of `ℰ`. The coordinates of the two charts at
`x` differ by the transition matrix `g(x) = transition c c' x`, and so do the normal fibres
(`MMP.Modules.normalFibre`): `g(x) N_{c,x} ⊆ N_{c',x}`. Indeed on a basic open `D(a) ⊆ V ∩ V'`
around `x` the local coordinates of `σ` satisfy `σ^♯b'ⱼ = ∑ᵢ gⱼᵢ σ^♯bᵢ`, `g` the change-of-basis
matrix (`MMP.Modules.sectionCoord_eq_sum_transitionSection`), so a relation
`∑ⱼ hⱼ σ^♯b'ⱼ = 0` gives the relation `∑ᵢ (∑ⱼ hⱼ gⱼᵢ) σ^♯bᵢ = 0`.

## Main results

* `MMP.Modules.map_totalSections`, `MMP.Modules.totalSections_structureMap`: the identification
  `Γ(V, Sym ℰ) ≅ Γ(π⁻¹V, 𝒪)` commutes with restriction and sends `a ∈ Γ(Y, V)` to `π^♯a`.
* `MMP.Modules.sectionCoord_eq_sum_transitionSection`: `σ^♯b'ⱼ = ∑ᵢ gⱼᵢ σ^♯bᵢ` on `D(a)`.
* `MMP.Modules.coord_chartInv_of_mem`: `x⁽ᶜ'⁾(φ_c⁻¹(x, w)) = g(x) w`.
* `MMP.Modules.injective_transition_mulVec`
* `MMP.Modules.transition_mulVec_mem_normalFibre`
* `MMP.Modules.finrank_normalFibre`: at a point of a regular imbedding of codimension `d` cut out
  by `σ`, the normal fibre has dimension `d`.
* `MMP.Modules.normalFibre_eq_map_transition`: `N_{c',x} = g(x) N_{c,x}` at the points of `X`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

namespace MMP.Modules

open UnderlyingSpace
open Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.RegularIdealSheaf (IsRegularClosedImmersionOfCodim)
open scoped Matrix

variable {Y : Scheme.{0}} {E : Y.Modules} [E.IsQuasicoherent] {r : ℕ}

private lemma preimage_preimage_proj {σ : Y ⟶ totalSpace E} (hσ : σ ≫ proj E = 𝟙 Y)
    (U : Y.Opens) : σ ⁻¹ᵁ (proj E ⁻¹ᵁ U) = U := by
  rw [← Scheme.Hom.comp_preimage, hσ, Scheme.Hom.id_preimage]

/-! ### Sections of `Sym ℰ` as functions on `𝐕(ℰ)` -/

variable (E) in
/-- The preimage of `π⁻¹V` under `Spec Γ(V, Sym ℰ) ⟶ 𝐕(ℰ)` is everything. -/
lemma top_le_preimage_specSectionsι (V : Y.affineOpens) :
    ⊤ ≤ specSectionsι E V ⁻¹ᵁ (proj E ⁻¹ᵁ V.1) := by
  rw [← opensRange_specSectionsι, Scheme.Hom.preimage_opensRange]

variable (E) in
/-- Pulled back to `Spec Γ(V, Sym ℰ)`, the function `totalSections E V s` is `s`. -/
lemma appLE_specSectionsι_totalSections (V : Y.affineOpens) (s : symSections E V.1) :
    (specSectionsι E V).appLE (proj E ⁻¹ᵁ V.1) ⊤ (top_le_preimage_specSectionsι E V)
      (totalSections E V s) = (Scheme.ΓSpecIso _).inv s := by
  set U := proj E ⁻¹ᵁ V.1
  have hι : specSectionsι E V = (specIso E V).inv ≫ U.ι := by
    rw [← specIso_hom_specSectionsι, Iso.inv_hom_id_assoc]
  have key : ∀ (g : Spec (symSections E V.1) ⟶ totalSpace E) (hg : ⊤ ≤ g ⁻¹ᵁ U)
      (t : Γ(U.toScheme, ⊤)), g = (specIso E V).inv ≫ U.ι →
        g.appLE U ⊤ hg (U.topIso.hom t) = (specIso E V).inv.appTop t := by
    rintro _ hg t rfl
    exact appLE_comp_ι_topIso_hom U _ hg t
  simp only [totalSections, CommRingCat.comp_apply]
  rw [key _ _ _ hι, appTop_inv_hom_apply]

variable (E) in
/-- The map `Γ(V, Sym ℰ) ⟶ Γ(π⁻¹V, 𝒪)` is an isomorphism. -/
lemma isIso_totalSections (V : Y.affineOpens) : IsIso (totalSections E V) := by
  have : IsIso ((specIso E V).hom.appTop) := inferInstanceAs (IsIso ((specIso E V).hom.app ⊤))
  unfold totalSections
  infer_instance

variable (E) in
/-- Two sections over `π⁻¹V` with the same pull-back to `Spec Γ(V, Sym ℰ)` are equal. -/
lemma eq_of_appLE_specSectionsι_eq (V : Y.affineOpens) {t t' : Γ(totalSpace E, proj E ⁻¹ᵁ V.1)}
    (h : (specSectionsι E V).appLE (proj E ⁻¹ᵁ V.1) ⊤ (top_le_preimage_specSectionsι E V) t =
      (specSectionsι E V).appLE (proj E ⁻¹ᵁ V.1) ⊤ (top_le_preimage_specSectionsι E V) t') :
    t = t' := by
  have := isIso_totalSections E V
  obtain ⟨s, rfl⟩ := (ConcreteCategory.bijective_of_isIso (totalSections E V)).2 t
  obtain ⟨s', rfl⟩ := (ConcreteCategory.bijective_of_isIso (totalSections E V)).2 t'
  rw [appLE_specSectionsι_totalSections, appLE_specSectionsι_totalSections] at h
  rw [(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (symSections E V.1)).inv).1 h]

variable (E) in
/-- **`Γ(V, Sym ℰ) ≅ Γ(π⁻¹V, 𝒪)` commutes with restriction.** -/
lemma map_totalSections {W V : Y.affineOpens} (hWV : W ≤ V) (s : symSections E V.1) :
    (totalSpace E).presheaf.map (homOfLE (Scheme.Hom.preimage_mono (proj E) hWV)).op
        (totalSections E V s) =
      totalSections E W (secRes (symAlg E) (homOfLE hWV) s) := by
  refine eq_of_appLE_specSectionsι_eq E W ?_
  rw [appLE_specSectionsι_totalSections, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  have key : ∀ (g : Spec (symSections E W.1) ⟶ totalSpace E) (hg : ⊤ ≤ g ⁻¹ᵁ (proj E ⁻¹ᵁ V.1)),
      g = Spec.map (secRes (symAlg E) (homOfLE hWV)) ≫ specSectionsι E V →
        g.appLE (proj E ⁻¹ᵁ V.1) ⊤ hg (totalSections E V s) =
          (Scheme.ΓSpecIso _).inv (secRes (symAlg E) (homOfLE hWV) s) := by
    rintro _ hg rfl
    rw [← Scheme.Hom.appLE_comp_appLE _ _ _ ⊤ ⊤ (top_le_preimage_specSectionsι E V)
      (Scheme.Hom.preimage_top _).ge, CommRingCat.comp_apply,
      appLE_specSectionsι_totalSections, UnderlyingSpace.appLE_top_top,
      specMap_appTop_ΓSpecIso_inv]
  exact key _ _ (specMap_secRes_specSectionsι E (homOfLE hWV)).symm

variable (E) in
/-- **`Γ(V, Sym ℰ) ≅ Γ(π⁻¹V, 𝒪)` sends `a ∈ Γ(Y, V)` to `π^♯a`.** -/
lemma totalSections_structureMap (V : Y.affineOpens) (a : Γ(Y, V.1)) :
    totalSections E V (((symAlg E).hom.hom.app (op V.1)).hom a) =
      (proj E).appLE V.1 (proj E ⁻¹ᵁ V.1) le_rfl a := by
  refine eq_of_appLE_specSectionsι_eq E V ?_
  rw [appLE_specSectionsι_totalSections, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE]
  have key : ∀ (g : Spec (symSections E V.1) ⟶ Y) (hg : ⊤ ≤ g ⁻¹ᵁ V.1),
      g = (Spec.map ((symAlg E).hom.hom.app (op V.1)) ≫
        (isAffineOpen_affineOpens V).isoSpec.inv) ≫ V.1.ι →
        g.appLE V.1 ⊤ hg a =
          (Scheme.ΓSpecIso _).inv (((symAlg E).hom.hom.app (op V.1)).hom a) := by
    rintro _ hg rfl
    conv_lhs => rw [← Iso.inv_hom_id_apply V.1.topIso a]
    rw [appLE_comp_ι_topIso_hom]
    exact appTop_specMap_isoSpec_inv _ _ a
  refine (key _ _ ?_).symm
  rw [specSectionsι_toBase]
  exact (Category.assoc _ _ _).symm

/-! ### Local coordinates of a section in two charts -/

/-- **The local coordinates of `σ` in two charts.** On an open `W` inside a basic open
`D(a) ⊆ V ∩ V'`, `σ^♯b'ⱼ = ∑ᵢ gⱼᵢ σ^♯bᵢ`, `g` the change-of-basis matrix of the two charts. -/
theorem sectionCoord_eq_sum_transitionSection {σ : Y ⟶ totalSpace E} (hσ : σ ≫ proj E = 𝟙 Y)
    (c c' : Chart E r) (a : Γ(Y, c.1.1)) (ha : Y.basicOpen a ≤ c'.1.1) {W : Y.Opens}
    (hW : W ≤ Y.basicOpen a) (j : Fin r) :
    sectionCoord σ c' (W := W) (by rw [preimage_preimage_proj hσ]; exact hW.trans ha) j =
      ∑ i, Y.presheaf.map (homOfLE hW).op (transitionSection c c' a ha j i) *
        sectionCoord σ c (W := W)
          (by rw [preimage_preimage_proj hσ]; exact hW.trans (Y.basicOpen_le a)) i := by
  let D : Y.affineOpens := ⟨Y.basicOpen a, (isAffineOpen_affineOpens c.1).basicOpen a⟩
  have hDV : D ≤ c.1 := Y.basicOpen_le a
  have hDV' : D ≤ c'.1 := ha
  have hWD : W ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ D.1) := hW.trans (preimage_preimage_proj hσ _).ge
  have hres : ∀ (c'' : Chart E r) (hD : D ≤ c''.1) (hW' : W ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c''.1.1))
      (t : Γ(totalSpace E, proj E ⁻¹ᵁ c''.1.1)),
      σ.appLE (proj E ⁻¹ᵁ c''.1.1) W hW' t = σ.appLE (proj E ⁻¹ᵁ D.1) W hWD
        ((totalSpace E).presheaf.map (homOfLE (Scheme.Hom.preimage_mono (proj E) hD)).op t) := by
    intro c'' hD hW' t
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  have hcoord : (totalSpace E).presheaf.map (homOfLE (Scheme.Hom.preimage_mono (proj E) hDV')).op
      (chartCoordSection c' j) = ∑ i, (proj E).appLE D.1 (proj E ⁻¹ᵁ D.1) le_rfl
        (transitionSection c c' a ha j i) *
        (totalSpace E).presheaf.map (homOfLE (Scheme.Hom.preimage_mono (proj E) hDV)).op
          (chartCoordSection c i) := by
    rw [chartCoordSection, map_totalSections E hDV']
    erw [generator_restrict E _ (isAffineOpen_affineOpens D) ha]
    rw [restrict_eq_sum_transitionSection c c' a ha j, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [generator_smul, map_mul, totalSections_structureMap, chartCoordSection,
      map_totalSections E hDV]
    erw [generator_restrict E _ (isAffineOpen_affineOpens D) (Y.basicOpen_le a)]
  have hπ : ∀ t : Γ(Y, D.1), σ.appLE (proj E ⁻¹ᵁ D.1) W hWD
      ((proj E).appLE D.1 (proj E ⁻¹ᵁ D.1) le_rfl t) = Y.presheaf.map (homOfLE hW).op t := by
    intro t
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    have key : ∀ (g : Y ⟶ Y) (hg : W ≤ g ⁻¹ᵁ D.1), g = 𝟙 Y →
        g.appLE D.1 W hg t = Y.presheaf.map (homOfLE hW).op t := by
      rintro _ hg rfl
      rfl
    exact key _ _ hσ
  simp only [sectionCoord]
  rw [hres c' hDV', hcoord, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, hπ, hres c hDV]

/-! ### Points in two charts -/

variable [Y.Over (Spec (.of ℂ))]

/-- In the chart `c'`, the point `φ_c⁻¹(x, w)` has coordinates `g(x) w`. -/
lemma coord_chartInv_of_mem (c c' : Chart E r) {x : UnderlyingSpace ℂ Y}
    (hx : ⊤ ≤ x.toHom ⁻¹ᵁ c.1.1) (hx' : ⊤ ≤ x.toHom ⁻¹ᵁ c'.1.1) (w : Fin r → ℂ) :
    coord c' (chartInv c x hx w) = transition c c' x *ᵥ w := by
  have hp : ⊤ ≤ (chartInv c x hx w).toHom ⁻¹ᵁ (proj E ⁻¹ᵁ (c.1.1 ⊓ c'.1.1)) := by
    intro z hz
    change proj E ((chartInv c x hx w).toHom z) ∈ c.1.1 ⊓ c'.1.1
    rw [← Scheme.Hom.comp_apply, toHom_chartInv_proj]
    exact ⟨hx hz, hx' hz⟩
  rw [coord_eq_transition_mulVec c c' _ hp, coord_chartInv, mapFun_proj_chartInv]

/-- The value `g(x)` of a transition matrix is injective. -/
lemma injective_transition_mulVec (c c' : Chart E r) {x : UnderlyingSpace ℂ Y}
    (hx : ⊤ ≤ x.toHom ⁻¹ᵁ c.1.1) (hx' : ⊤ ≤ x.toHom ⁻¹ᵁ c'.1.1) :
    Function.Injective (transition c c' x *ᵥ ·) := by
  refine (injective_iff_map_eq_zero (Matrix.mulVecLin (transition c c' x))).2 fun w hw ↦ ?_
  change transition c c' x *ᵥ w = 0 at hw
  have key : ∀ (y : UnderlyingSpace ℂ Y) (hy : y = x) (h : ⊤ ≤ y.toHom ⁻¹ᵁ c'.1.1)
      (v : Fin r → ℂ), chartInv c' y h v = chartInv c' x hx' v := by
    rintro _ rfl _ _
    rfl
  have hp : chartInv c x hx w = chartInv c' x hx' 0 := by
    have h1 := chartInv_mapFun_proj_coord c' (chartInv c x hx w) (by
      intro z hz
      change proj E ((chartInv c x hx w).toHom z) ∈ c'.1.1
      rw [← Scheme.Hom.comp_apply, toHom_chartInv_proj]
      exact hx' hz)
    rw [key _ (mapFun_proj_chartInv c x hx w), coord_chartInv_of_mem c c' hx hx', hw] at h1
    exact h1.symm
  have := congrArg (coord c) hp
  rwa [coord_chartInv, coord_chartInv_of_mem c' c hx' hx, Matrix.mulVec_zero] at this

/-! ### The normal fibre in two charts -/

/-- **Change of chart for the normal fibre**: `g(x) N_{c,x} ⊆ N_{c',x}`. -/
theorem transition_mulVec_mem_normalFibre {σ : Y ⟶ totalSpace E} (hσ : σ ≫ proj E = 𝟙 Y)
    (c c' : Chart E r) {x : UnderlyingSpace ℂ Y} (hx : ⊤ ≤ x.toHom ⁻¹ᵁ c.1.1)
    (hx' : ⊤ ≤ x.toHom ⁻¹ᵁ c'.1.1) {w : Fin r → ℂ} (hw : w ∈ normalFibre σ c x) :
    transition c c' x *ᵥ w ∈ normalFibre σ c' x := by
  rw [mem_normalFibre] at hw ⊢
  intro W hW hxW h hrel
  have hz : x.toHom (IsLocalRing.closedPoint ℂ) ∈ c.1.1 ⊓ c'.1.1 :=
    ⟨hx trivial, hx' trivial⟩
  obtain ⟨a, ha, hza⟩ := (isAffineOpen_affineOpens c.1).exists_basicOpen_le ⟨_, hz.2⟩ hz.1
  have hxa : ⊤ ≤ x.toHom ⁻¹ᵁ Y.basicOpen a := (top_le_preimage_iff x _).mpr hza
  set W' : Y.Opens := W ⊓ Y.basicOpen a
  have hW'W : W' ≤ W := inf_le_left
  have hW'a : W' ≤ Y.basicOpen a := inf_le_right
  have hxW' : ⊤ ≤ x.toHom ⁻¹ᵁ W' := by
    rw [Scheme.Hom.preimage_inf]
    exact le_inf hxW hxa
  have hW'c : W' ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1) :=
    (hW'a.trans (Y.basicOpen_le a)).trans (preimage_preimage_proj_of_comp_eq_id hσ _).ge
  let ρ := Y.presheaf.map (homOfLE hW'W).op
  let G : Fin r → Fin r → Γ(Y, W') := fun j i ↦
    Y.presheaf.map (homOfLE hW'a).op (transitionSection c c' a ha j i)
  have hcoord : ∀ j, ρ (sectionCoord σ c' hW j) = ∑ i, G j i * sectionCoord σ c hW'c i := by
    intro j
    rw [map_sectionCoord]
    exact sectionCoord_eq_sum_transitionSection hσ c c' a ha hW'a j
  let g : Fin r → Γ(Y, W') := fun i ↦ ∑ j, ρ (h j) * G j i
  have hrel' : ∑ i, g i * sectionCoord σ c hW'c i = 0 := by
    have h0 := congrArg ρ hrel
    rw [map_sum, map_zero] at h0
    simp only [map_mul, hcoord, Finset.mul_sum] at h0
    rw [Finset.sum_comm] at h0
    simp only [g, Finset.sum_mul]
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have key := hw W' hW'c hxW' g hrel'
  have hG : ∀ j i, eval x hxW' (G j i) = transition c c' x j i := fun j i ↦ by
    rw [eval_restrict, transition_eq_of_basicOpen c c' a ha x hxa, Matrix.of_apply]
  have hρ : ∀ j, eval x hxW' (ρ (h j)) = eval x hxW (h j) := fun j ↦ eval_restrict _ _ _ _
  have key' : ∑ i, w i * ∑ j, eval x hxW (h j) * transition c c' x j i = 0 := by
    rw [← key]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [smul_eq_mul]
    congr 1
    rw [← evalRingHom_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, evalRingHom_apply, evalRingHom_apply, hρ, hG]
  simp only [Matrix.mulVec, dotProduct, smul_eq_mul]
  rw [← key']
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] {d : ℕ}

/-- At a point of a regular imbedding `X` of codimension `d` cut out by `σ`, the normal fibre
`N_x ⊆ ℂʳ` has dimension `d`. -/
theorem finrank_normalFibre (i : X ⟶ Y) [i.IsOver (Spec (.of ℂ))] [IsClosedImmersion i]
    (hi : IsRegularClosedImmersionOfCodim i d)
    {σ : Y ⟶ totalSpace E} (hσ : σ ≫ proj E = 𝟙 Y) (hs : zeroLocus E σ = i.ker)
    (c : Chart E r) (x : UnderlyingSpace ℂ X) (hx : ⊤ ≤ (mapFun i x).toHom ⁻¹ᵁ c.1.1) :
    Module.finrank ℂ (normalFibre σ c (mapFun i x)) = d := by
  obtain ⟨W, hWc, hxW, M, G, f, h⟩ := exists_isLocalRegularPresentation i hi σ hσ hs c x hx
  rw [normalFibre_eq_range h, LinearMap.finrank_range_of_inj, Module.finrank_fin_fun]
  intro v v' hvv'
  funext b
  have hb := congrFun (congrArg (evalMatrix _ hxW G) hvv') b
  simp only [evalMatrix_apply, Finset.mul_sum] at hb
  rw [Finset.sum_comm, Finset.sum_comm (f := fun _ _ ↦ _ * (_ * v' _))] at hb
  simpa only [← mul_assoc, ← Finset.sum_mul, eval_mul_eval_eq_one h, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true] using hb

/-- **The normal fibres in two charts correspond**: `N_{c',x} = g(x) N_{c,x}` at the points of a
regular imbedding cut out by `σ`. -/
theorem normalFibre_eq_map_transition (i : X ⟶ Y) [i.IsOver (Spec (.of ℂ))]
    [IsClosedImmersion i] (hi : IsRegularClosedImmersionOfCodim i d) {σ : Y ⟶ totalSpace E}
    (hσ : σ ≫ proj E = 𝟙 Y)
    (hs : zeroLocus E σ = i.ker) (c c' : Chart E r) (x : UnderlyingSpace ℂ X)
    (hx : ⊤ ≤ (mapFun i x).toHom ⁻¹ᵁ c.1.1) (hx' : ⊤ ≤ (mapFun i x).toHom ⁻¹ᵁ c'.1.1) :
    normalFibre σ c' (mapFun i x) =
      (normalFibre σ c (mapFun i x)).map (Matrix.mulVecLin (transition c c' (mapFun i x))) := by
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact transition_mulVec_mem_normalFibre hσ c c' hx hx' hw
  · rw [← (Submodule.equivMapOfInjective _ (injective_transition_mulVec c c' hx hx')
      _).finrank_eq, finrank_normalFibre i hi hσ hs c x hx, finrank_normalFibre i hi hσ hs c' x hx']

end MMP.Modules
