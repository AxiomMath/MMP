module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksSectionPoints
public import MMP.AlgebraicTopology.ComplexVectorBundle.OfStacksBundle

/-!
# The base change of a Stacks vector bundle in charts

Let `f : X' ⟶ X` be a morphism of schemes and `ℰ` a quasi-coherent `𝒪_X`-module, with vector
bundle `𝐕(ℰ)`. The vector bundle `𝐕(f^*ℰ)` of the pulled-back module is the base change of
`𝐕(ℰ)` along `f` (Stacks' `Scheme.Modules.isPullback_vectorBundleBaseChangeMap`), through the
bundle map `f̃ : 𝐕(f^*ℰ) ⟶ 𝐕(ℰ)`. In charts, `f̃` pulls the coordinate function `m ∈ Γ(ℰ, V)`
of `𝐕(ℰ)` back to the coordinate function `f^*m|_{V'} ∈ Γ(f^*ℰ, V')` of `𝐕(f^*ℰ)`
(`MMP.Modules.appLE_baseChangeMap_generator`); hence on complex points `f̃` is, fibre by fibre,
a linear isomorphism in coordinates (`MMP.Modules.exists_coord_baseChangeMap`).

## References

* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [W. Fulton, *Intersection Theory*][fulton1998], Appendix B.5.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Opposite Matrix

namespace MMP.Modules

variable {X X' : Scheme.{0}} (f : X' ⟶ X) (E : X.Modules) [E.IsQuasicoherent]
  [((Scheme.Modules.pullback f).obj E).IsQuasicoherent]

/-- The bundle map `f̃ : 𝐕(f^*ℰ) ⟶ 𝐕(ℰ)` of the base change. -/
abbrev baseChangeMap :
    totalSpace ((Scheme.Modules.pullback f).obj E) ⟶ totalSpace E :=
  Scheme.Modules.vectorBundleBaseChangeMap f E

/-- The bundle map `f̃` commutes with the projections: `π ∘ f̃ = f ∘ π'`. -/
lemma baseChangeMap_proj :
    baseChangeMap f E ≫ proj E = proj ((Scheme.Modules.pullback f).obj E) ≫ f :=
  (Scheme.Modules.isPullback_vectorBundleBaseChangeMap f E).w

/-- The section `f^*m ∈ Γ(f^*ℰ, f⁻¹V)` of a section `m ∈ Γ(ℰ, V)`: the unit of `f^* ⊣ f_*`. -/
def pullbackSection {V : X.Opens} (m : Γ(E, V)) :
    Γ((Scheme.Modules.pullback f).obj E, f ⁻¹ᵁ V) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E).val.app (op V)).hom m

/-- **The bundle map of a base change, in charts.** On `π'⁻¹(V')` for an affine `V' ⊆ f⁻¹V`,
`f̃` pulls the coordinate function `m ∈ Γ(ℰ, V)` back to the coordinate function `f^*m|_{V'}`. -/
theorem appLE_baseChangeMap_generator (V : X.affineOpens) (V' : X'.affineOpens)
    (hV : V'.1 ≤ f ⁻¹ᵁ V.1) (m : Γ(E, V.1))
    (hle : proj ((Scheme.Modules.pullback f).obj E) ⁻¹ᵁ V'.1 ≤
      baseChangeMap f E ⁻¹ᵁ (proj E ⁻¹ᵁ V.1)) :
    (baseChangeMap f E).appLE (proj E ⁻¹ᵁ V.1)
        (proj ((Scheme.Modules.pullback f).obj E) ⁻¹ᵁ V'.1) hle
        (totalSections E V (generator E V.2 m)) =
      totalSections _ V' (generator _ V'.2
        (((Scheme.Modules.pullback f).obj E).presheaf.map (homOfLE hV).op
          (pullbackSection f E m))) := by
  set E' := (Scheme.Modules.pullback f).obj E
  set W : Over X := (Over.map f).obj (Scheme.Modules.vectorBundleOver X' (F := E'))
  have hW : W.hom ⁻¹ᵁ V.1 ≤ (Scheme.Modules.vectorBundleBaseChangeOver f E).left ⁻¹ᵁ
      (proj E ⁻¹ᵁ V.1) := by
    rw [← Scheme.Modules.vectorBundleBaseChangeMap_eq]
    intro x hx
    change (baseChangeMap f E ≫ proj E).base x ∈ V.1
    rw [baseChangeMap_proj]
    exact hx
  have hle' : proj E' ⁻¹ᵁ V'.1 ≤ W.hom ⁻¹ᵁ V.1 := fun x hx ↦ hV hx
  have h1 := appLE_totalSections_generator E (Scheme.Modules.vectorBundleBaseChangeOver f E) V m
    hW
  have h2 := appLE_totalSections_generator E' (𝟙 _) V' (E'.presheaf.map (homOfLE hV).op
    (pullbackSection f E m)) le_rfl
  have h3 : Scheme.Modules.vectorBundleHomEquiv E W
      (Scheme.Modules.vectorBundleBaseChangeOver f E) =
      Scheme.Modules.transposeEquiv f E _
        (Scheme.Modules.vectorBundleHomEquiv E' _ (𝟙 _)) :=
    Equiv.apply_symm_apply _ _
  have key : ∀ (g : totalSpace E' ⟶ totalSpace E)
      (hg : g = (Scheme.Modules.vectorBundleBaseChangeOver f E).left) (e),
      g.appLE (proj E ⁻¹ᵁ V.1) (proj E' ⁻¹ᵁ V'.1) e =
        (Scheme.Modules.vectorBundleBaseChangeOver f E).left.appLE (proj E ⁻¹ᵁ V.1)
          (W.hom ⁻¹ᵁ V.1) hW ≫ (totalSpace E').presheaf.map (homOfLE hle').op := by
    intro g hg e
    subst hg
    exact (Scheme.Hom.appLE_map _ hW (homOfLE hle').op).symm
  have h4 : ∀ φ : E' ⟶ Scheme.Modules.structurePushforward
        (Scheme.Modules.vectorBundleOver X' (F := E')).hom,
      ((Scheme.Modules.transposeEquiv f E (Scheme.Modules.vectorBundleOver X' (F := E')) φ).val.app
        (op V.1)).hom m = (φ.val.app (op (f ⁻¹ᵁ V.1))).hom (pullbackSection f E m) := by
    intro φ
    rw [Scheme.Modules.transposeEquiv_apply, Adjunction.homEquiv_unit]
    rfl
  rw [key _ (Scheme.Modules.vectorBundleBaseChangeMap_eq f E) hle, CommRingCat.comp_apply, h1, h3]
  erw [h4]
  have h5 := PresheafOfModules.naturality_apply
    (Scheme.Modules.vectorBundleHomEquiv E' (Scheme.Modules.vectorBundleOver X' (F := E'))
      (𝟙 _)).val (homOfLE hV).op (pullbackSection f E m)
  erw [← h5, ← h2]
  simp only [Scheme.Hom.appLE, Over.id_left, Scheme.Hom.id_app]
  erw [Category.id_comp, Subsingleton.elim (homOfLE _) (𝟙 _), op_id, CategoryTheory.Functor.map_id]
  rfl

section Points

open UnderlyingSpace

variable [X.Over (Spec (.of ℂ))] [X'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]

/-- The bundle map `f̃ : 𝐕(f^*ℰ) ⟶ 𝐕(ℰ)` is a morphism over `Spec ℂ`. -/
instance isOver_baseChangeMap : (baseChangeMap f E).IsOver (Spec (.of ℂ)) :=
  ⟨by
    change baseChangeMap f E ≫ proj E ≫ X ↘ Spec (.of ℂ) =
      proj ((Scheme.Modules.pullback f).obj E) ≫ X' ↘ Spec (.of ℂ)
    rw [← Category.assoc, baseChangeMap_proj, Category.assoc, comp_over f (Spec (.of ℂ))]⟩

/-- The projection of `f̃(q)` is `f` of the projection of `q`. -/
lemma mapFun_proj_mapFun_baseChangeMap
    (q : UnderlyingSpace ℂ (totalSpace ((Scheme.Modules.pullback f).obj E))) :
    mapFun (proj E) (mapFun (baseChangeMap f E) q) =
      mapFun f (mapFun (proj ((Scheme.Modules.pullback f).obj E)) q) :=
  UnderlyingSpace.ext (by
    simp only [toHom_mapFun, Category.assoc, baseChangeMap_proj])

variable {r : ℕ}

/-- **The bundle map of a base change is linear on fibres, in coordinates.** For charts
`c = (V, b)` of `ℰ` and `c' = (V', b')` of `f^*ℰ` with `V' ⊆ f⁻¹V`, and a point `x' ∈ V'(ℂ)`, there
is a matrix `M` with `x^c(f̃ q) = M · x^{c'}(q)` for every point `q` of `𝐕(f^*ℰ)(ℂ)` over `x'`. -/
theorem exists_coord_baseChangeMap (c : Chart E r)
    (c' : Chart ((Scheme.Modules.pullback f).obj E) r)
    (hc : c'.1.1 ≤ f ⁻¹ᵁ c.1.1) (x' : UnderlyingSpace ℂ X') (hx' : x' ∈ chartBase c') :
    ∃ M : Matrix (Fin r) (Fin r) ℂ, ∀ q, mapFun (proj ((Scheme.Modules.pullback f).obj E)) q = x' →
      coord c (mapFun (baseChangeMap f E) q) = M *ᵥ coord c' q := by
  set a : Fin r → Fin r → Γ(X', c'.1.1) := fun i j ↦ c'.2.repr
    (((Scheme.Modules.pullback f).obj E).presheaf.map (homOfLE hc).op
      (pullbackSection f E (c.2 i))) j
  have hx : ⊤ ≤ x'.toHom ⁻¹ᵁ c'.1.1 := hx'
  refine ⟨fun i j ↦ eval x' hx (a i j), fun q hq ↦ funext fun i ↦ ?_⟩
  have hq' : ⊤ ≤ q.toHom ⁻¹ᵁ (proj ((Scheme.Modules.pullback f).obj E) ⁻¹ᵁ c'.1.1) := by
    change ⊤ ≤ (q.toHom ≫ proj ((Scheme.Modules.pullback f).obj E)) ⁻¹ᵁ c'.1.1
    rw [← toHom_mapFun, hq]
    exact hx
  have hle : proj ((Scheme.Modules.pullback f).obj E) ⁻¹ᵁ c'.1.1 ≤
      baseChangeMap f E ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1) := by
    intro y hy
    change (baseChangeMap f E ≫ proj E).base y ∈ c.1.1
    rw [baseChangeMap_proj]
    exact hc hy
  have hBq : ⊤ ≤ (mapFun (baseChangeMap f E) q).toHom ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1) :=
    hq'.trans (Scheme.Hom.preimage_mono _ hle)
  rw [coord_apply c hBq, chartCoordSection,
    ← eval_appLE (baseChangeMap f E) hle q hq',
    appLE_baseChangeMap_generator f E c.1 c'.1 hc (c.2 i) hle,
    ← c'.2.sum_repr (((Scheme.Modules.pullback f).obj E).presheaf.map (homOfLE hc).op
      (pullbackSection f E (c.2 i))), map_sum,
    map_sum]
  simp only [generator_smul, map_mul]
  change evalRingHom q hq' _ = _
  rw [map_sum]
  simp only [map_mul, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  erw [generator_smul, map_mul, map_mul]
  change eval q hq' _ * eval q hq' _ = _
  rw [eval_totalSections_structureMap ((Scheme.Modules.pullback f).obj E) c'.1 q hq' (hq ▸ hx),
    coord_apply c' hq' j]
  have hev : ∀ (y : UnderlyingSpace ℂ X') (hy : y = x') (h : ⊤ ≤ y.toHom ⁻¹ᵁ c'.1.1),
      eval y h (a i j) = eval x' hx (a i j) := by
    rintro _ rfl _
    rfl
  rw [hev _ hq]
  rfl

/-- **The bundle map of a base change is injective on fibres**: `𝐕(f^*ℰ)` is the fibre product
`X' ×_X 𝐕(ℰ)`, so a point of it is determined by its projection and its image in `𝐕(ℰ)`. -/
lemma eq_of_mapFun_baseChangeMap_eq
    {q q' : UnderlyingSpace ℂ (totalSpace ((Scheme.Modules.pullback f).obj E))}
    (hπ : mapFun (proj ((Scheme.Modules.pullback f).obj E)) q =
      mapFun (proj ((Scheme.Modules.pullback f).obj E)) q')
    (hB : mapFun (baseChangeMap f E) q = mapFun (baseChangeMap f E) q') : q = q' := by
  refine UnderlyingSpace.ext
    ((Scheme.Modules.isPullback_vectorBundleBaseChangeMap f E).hom_ext ?_ ?_)
  · have := congrArg UnderlyingSpace.toHom hB
    simpa only [toHom_mapFun] using this
  · have := congrArg UnderlyingSpace.toHom hπ
    simpa only [toHom_mapFun] using this

/-- **The bundle map of a base change is a linear isomorphism on fibres, in coordinates.** For
charts `c = (V, b)` of `ℰ` and `c' = (V', b')` of `f^*ℰ` with `V' ⊆ f⁻¹V`, and `x' ∈ V'(ℂ)`, there
is `A ∈ GL(r, ℂ)` with `x^c(f̃ q) = A · x^{c'}(q)` for every point `q` of `𝐕(f^*ℰ)(ℂ)` over
`x'`. -/
theorem exists_gl_coord_baseChangeMap (c : Chart E r)
    (c' : Chart ((Scheme.Modules.pullback f).obj E) r) (hc : c'.1.1 ≤ f ⁻¹ᵁ c.1.1)
    (x' : UnderlyingSpace ℂ X') (hx' : x' ∈ chartBase c') :
    ∃ A : GL (Fin r) ℂ, ∀ q, mapFun (proj ((Scheme.Modules.pullback f).obj E)) q = x' →
      coord c (mapFun (baseChangeMap f E) q) = (A : Matrix (Fin r) (Fin r) ℂ) *ᵥ coord c' q := by
  classical
  obtain ⟨M, hM⟩ := exists_coord_baseChangeMap f E c c' hc x' hx'
  have hfx : mapFun f x' ∈ chartBase c := by
    change ⊤ ≤ (x'.toHom ≫ f) ⁻¹ᵁ c.1.1
    exact fun z hz ↦ hc (hx' hz)
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨w, hw, hMw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hx : ⊤ ≤ x'.toHom ⁻¹ᵁ c'.1.1 := hx'
    have hq := mapFun_proj_chartInv c' x' hx w
    have hq0 := mapFun_proj_chartInv c' x' hx 0
    have hB : mapFun (baseChangeMap f E) (chartInv c' x' hx w) =
        mapFun (baseChangeMap f E) (chartInv c' x' hx 0) := by
      have h := fibre_ext (E := E) (r := r) c hfx
        (y := ⟨mapFun (baseChangeMap f E) (chartInv c' x' hx w),
          (mapFun_proj_mapFun_baseChangeMap f E _).trans (congrArg _ hq)⟩)
        (y' := ⟨mapFun (baseChangeMap f E) (chartInv c' x' hx 0),
          (mapFun_proj_mapFun_baseChangeMap f E _).trans (congrArg _ hq0)⟩)
        (by
          change coord c _ = coord c _
          rw [hM _ hq, hM _ hq0, coord_chartInv, coord_chartInv, hMw, Matrix.mulVec_zero])
      exact congrArg Subtype.val h
    have := eq_of_mapFun_baseChangeMap_eq f E (hq.trans hq0.symm) hB
    apply hw
    rw [← coord_chartInv c' x' hx w, this, coord_chartInv]
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, hM⟩

end Points

end MMP.Modules
