module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksBaseChangeChart
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.ChainBaseChangeGeneric
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksNormalizationThom
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksSectionPullback
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.Unique.StacksGlue

/-!
# Base change of orientation classes, for Stacks vector bundles (Fulton, Lemma 19.2 (a))

Let `X' = X ×_Y Y'` be a fibre square of complex schemes, with `i : X → Y` and `i' : X' → Y'`
regular imbeddings of codimension `d` and `f : Y' → Y`. An orientation datum `(ℰ, σ, V, Q)` of `i`
(`MMP.Modules.RegularImbeddingOrientationDatum`) pulls back to the orientation datum
`(f^*ℰ, f^*σ, f⁻¹V, f^*Q)` of `i'`, and `f^*(u_i) = u_{i'}`.

The bundle map `f̃ : 𝐕(f^*ℰ) → 𝐕(ℰ)` pulls the chart coordinates `bᵢ` of a chart `c = (U, b)` of
`ℰ` back to `∑ⱼ aᵢⱼ b''ⱼ` on a chart `c'' = (U'', b'')` of `f^*ℰ` with `U'' ⊆ f⁻¹U`, `aᵢⱼ` the
coefficients of `f^*bᵢ|_{U''}` in the basis `b''`; so the local coordinates of `f^*σ` are
`∑ⱼ aᵢⱼ (f^*σ)^♯b''ⱼ = f^♯(σ^♯bᵢ)`, and `a(y)` carries the normal fibre of `X' ⊆ Y'` at `y` into
that of `X ⊆ Y` at `f(y)` (`MMP.Modules.mulVec_mem_normalFibre_pullbackSectionMap`).

## Main results

* `MMP.Modules.appLE_baseChangeMap_chartCoordSection`: `f̃^♯ bᵢ = ∑ⱼ aᵢⱼ b''ⱼ`.
* `MMP.Modules.coord_baseChangeMap_eq_mulVec`: `x^c(f̃ q) = a(y) x^{c''}(q)`.
* `MMP.Modules.mulVec_mem_normalFibre_pullbackSectionMap`: `a(y) N_{c'',y} ⊆ N_{c,f(y)}`.
* `MMP.Modules.RegularImbeddingOrientationDatum.pullback`: the pulled-back datum.
* `MMP.Modules.IsRegularImbeddingOrientationClass.pullback_of_isPullback`: `f^* u_i` is an
  orientation class of `i'`.
* `MMP.Modules.IsRegularImbeddingOrientationClass.pullback_eq`: `f^*(u_i) = u_{i'}`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Lemma 19.2 (a).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Bundle Topology Opposite
open Stacks.AlgebraicGeometry.RegularIdealSheaf (IsRegularClosedImmersionOfCodim)
open scoped Matrix

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback

namespace MMP.Modules

open UnderlyingSpace

/-! ### The bundle map of a base change in charts -/

section Chart

variable {Y Y' : Scheme.{0}} (f : Y' ⟶ Y) {E : Y.Modules} [E.IsQuasicoherent] {r : ℕ}

/-- The coefficients `aᵢⱼ ∈ Γ(Y', U'')` of `f^*bᵢ|_{U''}` in the basis `b''`, for charts
`c = (U, b)` of `ℰ` and `c'' = (U'', b'')` of `f^*ℰ` with `U'' ⊆ f⁻¹U`. -/
def baseChangeSection (c : Chart E r) (c'' : Chart ((Scheme.Modules.pullback f).obj E) r)
    (hc : c''.1.1 ≤ f ⁻¹ᵁ c.1.1) (i j : Fin r) : Γ(Y', c''.1.1) :=
  c''.2.repr (((Scheme.Modules.pullback f).obj E).presheaf.map (homOfLE hc).op
    (pullbackSection f E (c.2 i))) j

/-- **The bundle map of a base change on chart coordinates**: `f̃^♯ bᵢ = ∑ⱼ aᵢⱼ b''ⱼ` on
`π'⁻¹U''`. -/
theorem appLE_baseChangeMap_chartCoordSection (c : Chart E r)
    (c'' : Chart ((Scheme.Modules.pullback f).obj E) r) (hc : c''.1.1 ≤ f ⁻¹ᵁ c.1.1)
    (hle : proj ((Scheme.Modules.pullback f).obj E) ⁻¹ᵁ c''.1.1 ≤
      baseChangeMap f E ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)) (i : Fin r) :
    (baseChangeMap f E).appLE (proj E ⁻¹ᵁ c.1.1)
        (proj ((Scheme.Modules.pullback f).obj E) ⁻¹ᵁ c''.1.1) hle (chartCoordSection c i) =
      ∑ j, (proj ((Scheme.Modules.pullback f).obj E)).appLE c''.1.1
          (proj ((Scheme.Modules.pullback f).obj E) ⁻¹ᵁ c''.1.1) le_rfl
          (baseChangeSection f c c'' hc i j) * chartCoordSection c'' j := by
  rw [chartCoordSection, appLE_baseChangeMap_generator f E c.1 c''.1 hc (c.2 i) hle,
    ← c''.2.sum_repr (((Scheme.Modules.pullback f).obj E).presheaf.map (homOfLE hc).op
      (pullbackSection f E (c.2 i))), map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  erw [generator_smul, map_mul, totalSections_structureMap]
  rfl

/-- For a chart `c''` of `f^*ℰ` over an open contained in `f⁻¹` of the base of a chart `c` of `ℰ`,
the preimage of that open in `𝐕(f^*ℰ)` lies in the preimage under `f̃` of the preimage of the base
of `c` in `𝐕(ℰ)`. -/
lemma preimage_proj_le_preimage_baseChangeMap (c : Chart E r)
    (c'' : Chart ((Scheme.Modules.pullback f).obj E) r) (hc : c''.1.1 ≤ f ⁻¹ᵁ c.1.1) :
    proj ((Scheme.Modules.pullback f).obj E) ⁻¹ᵁ c''.1.1 ≤
      baseChangeMap f E ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1) := by
  intro y hy
  change (baseChangeMap f E ≫ proj E).base y ∈ c.1.1
  rw [baseChangeMap_proj]
  exact hc hy

variable {σ : Y ⟶ totalSpace E} (hσ : σ ≫ proj E = 𝟙 Y)

/-- **The local coordinates of a pulled-back section**: `f^♯(σ^♯bᵢ) = ∑ⱼ aᵢⱼ (f^*σ)^♯b''ⱼ`. -/
theorem appLE_sectionCoord_pullbackSectionMap (c : Chart E r)
    (c'' : Chart ((Scheme.Modules.pullback f).obj E) r) (hc : c''.1.1 ≤ f ⁻¹ᵁ c.1.1)
    {W : Y.Opens} (hW : W ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)) {W' : Y'.Opens} (hW' : W' ≤ f ⁻¹ᵁ W)
    (hW'c : W' ≤ c''.1.1)
    (hW'σ : W' ≤ pullbackSectionMap f hσ ⁻¹ᵁ
      (proj ((Scheme.Modules.pullback f).obj E) ⁻¹ᵁ c''.1.1)) (i : Fin r) :
    f.appLE W W' hW' (sectionCoord σ c hW i) =
      ∑ j, Y'.presheaf.map (homOfLE hW'c).op (baseChangeSection f c c'' hc i j) *
        sectionCoord (pullbackSectionMap f hσ) c'' hW'σ j := by
  have hle := preimage_proj_le_preimage_baseChangeMap f c c'' hc
  simp only [sectionCoord]
  rw [MMP.appLE_appLE_eq
      (pullbackSectionMap_baseChangeMap f hσ).symm hW hW' hle hW'σ,
    appLE_baseChangeMap_chartCoordSection f c c'' hc hle, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_mul]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have key : ∀ (g : Y' ⟶ Y') (hg : W' ≤ g ⁻¹ᵁ c''.1.1), g = 𝟙 Y' →
      g.appLE c''.1.1 W' hg (baseChangeSection f c c'' hc i j) =
        Y'.presheaf.map (homOfLE hW'c).op (baseChangeSection f c c'' hc i j) := by
    rintro _ hg rfl
    rfl
  exact key _ _ (pullbackSectionMap_proj f hσ)

variable [Y.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]

/-- **The bundle map of a base change in coordinates**: `x^c(f̃ q) = a(y) x^{c''}(q)` for the
points `q` of `𝐕(f^*ℰ)(ℂ)` over `y ∈ U''(ℂ)`. -/
theorem coord_baseChangeMap_eq_mulVec (c : Chart E r)
    (c'' : Chart ((Scheme.Modules.pullback f).obj E) r) (hc : c''.1.1 ≤ f ⁻¹ᵁ c.1.1)
    {y : UnderlyingSpace ℂ Y'} (hy : ⊤ ≤ y.toHom ⁻¹ᵁ c''.1.1)
    (q : UnderlyingSpace ℂ (totalSpace ((Scheme.Modules.pullback f).obj E)))
    (hq : mapFun (proj ((Scheme.Modules.pullback f).obj E)) q = y) :
    coord c (mapFun (baseChangeMap f E) q) =
      Matrix.of (fun i j ↦ eval y hy (baseChangeSection f c c'' hc i j)) *ᵥ coord c'' q := by
  have hq' : ⊤ ≤ q.toHom ⁻¹ᵁ (proj ((Scheme.Modules.pullback f).obj E) ⁻¹ᵁ c''.1.1) := by
    change ⊤ ≤ (q.toHom ≫ proj ((Scheme.Modules.pullback f).obj E)) ⁻¹ᵁ c''.1.1
    rwa [← toHom_mapFun, hq]
  have hle := preimage_proj_le_preimage_baseChangeMap f c c'' hc
  have hBq : ⊤ ≤ (mapFun (baseChangeMap f E) q).toHom ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1) :=
    hq'.trans (Scheme.Hom.preimage_mono _ hle)
  have hev : ∀ (y' : UnderlyingSpace ℂ Y') (h : y' = y) (hh : ⊤ ≤ y'.toHom ⁻¹ᵁ c''.1.1)
      (a : Γ(Y', c''.1.1)), eval y' hh a = eval y hy a := by
    rintro _ rfl _ _
    rfl
  funext i
  rw [coord_apply c hBq, ← eval_appLE (baseChangeMap f E) hle q hq',
    appLE_baseChangeMap_chartCoordSection f c c'' hc hle, ← evalRingHom_apply, map_sum]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, map_mul, evalRingHom_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [eval_appLE, coord_apply c'' hq' j, hev _ hq]

/-- **The bundle map of a base change on chart points**: if `A` is the matrix of `f̃` from `c''`
to `c` over `y`, and `T` that of the change of chart from `c'` to `c''`, then `f̃` sends the point
of `𝐕(f^*ℰ)` with coordinates `w` in `c'` to the point with coordinates `(A T) w` in `c`. -/
theorem mapFun_baseChangeMap_chartInv (c : Chart E r)
    (c' c'' : Chart ((Scheme.Modules.pullback f).obj E) r) {y : UnderlyingSpace ℂ Y'}
    (hy : ⊤ ≤ y.toHom ⁻¹ᵁ c'.1.1) (hc : ⊤ ≤ (mapFun f y).toHom ⁻¹ᵁ c.1.1)
    (A T : GL (Fin r) ℂ)
    (hA : ∀ q, mapFun (proj ((Scheme.Modules.pullback f).obj E)) q = y →
      coord c (mapFun (baseChangeMap f E) q) = (A : Matrix (Fin r) (Fin r) ℂ) *ᵥ coord c'' q)
    (hT : ∀ q, mapFun (proj ((Scheme.Modules.pullback f).obj E)) q = y →
      coord c'' q = (T : Matrix (Fin r) (Fin r) ℂ) *ᵥ coord c' q) (w : Fin r → ℂ) :
    mapFun (baseChangeMap f E) (chartInv c' y hy w) =
      chartInv c (mapFun f y) hc (((A * T : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ w) := by
  have hq := mapFun_proj_chartInv c' y hy w
  have h1 : mapFun (proj E) (mapFun (baseChangeMap f E) (chartInv c' y hy w)) = mapFun f y := by
    rw [mapFun_proj_mapFun_baseChangeMap, hq]
  have h2 := mapFun_proj_chartInv c (mapFun f y) hc
    (((A * T : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ w)
  have hm1 : mapFun (baseChangeMap f E) (chartInv c' y hy w) ∈ chartTotalOpens c := by
    change mapFun (proj E) _ ∈ chartBase c
    rwa [h1]
  have hm2 : chartInv c (mapFun f y) hc
      (((A * T : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ w) ∈ chartTotalOpens c := by
    change mapFun (proj E) _ ∈ chartBase c
    rwa [h2]
  have := (chartHomeomorph c).injective (a₁ := ⟨_, hm1⟩) (a₂ := ⟨_, hm2⟩)
    (Prod.ext (Subtype.ext (h1.trans h2.symm)) (by
      change coord c _ = coord c _
      rw [hA _ hq, hT _ hq]
      erw [coord_chartInv, coord_chartInv]
      rw [Matrix.mulVec_mulVec, Matrix.GeneralLinearGroup.coe_mul]))
  exact congrArg Subtype.val this

/-- **The normal fibres under base change**: `a(y) N_{c'',y} ⊆ N_{c,f(y)}`, for the normal fibre
of `Z(f^*σ)` at `y` and that of `Z(σ)` at `f(y)`. -/
theorem mulVec_mem_normalFibre_pullbackSectionMap (c : Chart E r)
    (c'' : Chart ((Scheme.Modules.pullback f).obj E) r) (hc : c''.1.1 ≤ f ⁻¹ᵁ c.1.1)
    {y : UnderlyingSpace ℂ Y'} (hy : ⊤ ≤ y.toHom ⁻¹ᵁ c''.1.1) {w : Fin r → ℂ}
    (hw : w ∈ normalFibre (pullbackSectionMap f hσ) c'' y) :
    Matrix.of (fun i j ↦ eval y hy (baseChangeSection f c c'' hc i j)) *ᵥ w ∈
      normalFibre σ c (mapFun f y) := by
  rw [mem_normalFibre] at hw ⊢
  intro W hW hxW g hrel
  set W' : Y'.Opens := f ⁻¹ᵁ W ⊓ c''.1.1
  have hW'f : W' ≤ f ⁻¹ᵁ W := inf_le_left
  have hW'c : W' ≤ c''.1.1 := inf_le_right
  have hyW' : ⊤ ≤ y.toHom ⁻¹ᵁ W' := by
    rw [Scheme.Hom.preimage_inf]
    refine le_inf ?_ hy
    rwa [← Scheme.Hom.comp_preimage, ← toHom_mapFun]
  have hW'σ : W' ≤ pullbackSectionMap f hσ ⁻¹ᵁ
      (proj ((Scheme.Modules.pullback f).obj E) ⁻¹ᵁ c''.1.1) := by
    rwa [preimage_preimage_proj_of_comp_eq_id (pullbackSectionMap_proj f hσ)]
  let ρ := Y'.presheaf.map (homOfLE hW'c).op
  let g' : Fin r → Γ(Y', W') := fun j ↦
    ∑ i, f.appLE W W' hW'f (g i) * ρ (baseChangeSection f c c'' hc i j)
  have hrel' : ∑ j, g' j * sectionCoord (pullbackSectionMap f hσ) c'' hW'σ j = 0 := by
    have h0 := congrArg (f.appLE W W' hW'f) hrel
    rw [map_sum, map_zero] at h0
    simp only [map_mul, appLE_sectionCoord_pullbackSectionMap f hσ c c'' hc hW hW'f hW'c hW'σ,
      Finset.mul_sum] at h0
    rw [Finset.sum_comm] at h0
    simp only [g', Finset.sum_mul]
    rw [← h0]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [ρ]
    ring
  have key := hw W' hW'σ hyW' g' hrel'
  have hg : ∀ i, eval y hyW' (f.appLE W W' hW'f (g i)) = eval (mapFun f y) hxW (g i) :=
    fun i ↦ by rw [eval_appLE]
  have ha : ∀ i j, eval y hyW' (ρ (baseChangeSection f c c'' hc i j)) =
      eval y hy (baseChangeSection f c c'' hc i j) := fun i j ↦ by
    simp only [ρ]
    rw [eval_restrict]
  rw [← key]
  simp only [g', ← evalRingHom_apply, map_sum, map_mul]
  simp only [evalRingHom_apply, hg, ha, Matrix.mulVec, dotProduct, Matrix.of_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  ring

end Chart

/-! ### The pull-back of an orientation datum -/

variable {X Y X' Y' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  [X'.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))]

namespace RegularImbeddingOrientationDatum

open ThomClass

variable {i : X ⟶ Y} {i' : X' ⟶ Y'} {f : Y' ⟶ Y} {g : X' ⟶ X} [i.IsOver (Spec (.of ℂ))]
  [i'.IsOver (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))] [g.IsOver (Spec (.of ℂ))] {d : ℕ}
  (D : RegularImbeddingOrientationDatum i d)

/-- The map `f⁻¹(V) → V` induced by `f`. -/
def nbhdMap : C((mapFun f ⁻¹' D.nbhd : Set (UnderlyingSpace ℂ Y')), D.nbhd) :=
  ⟨fun y ↦ ⟨mapFun f y.1, y.2⟩, ((continuous_mapFun f).comp continuous_subtype_val).subtype_mk _⟩

/-- The quotient map `𝐕(f^*ℰ)(ℂ)|_{f⁻¹V} → f^*Q`. -/
def pullbackQuot
    (p : {p : UnderlyingSpace ℂ (totalSpace ((Scheme.Modules.pullback f).obj D.E)) //
      mapFun (proj ((Scheme.Modules.pullback f).obj D.E)) p ∈
        (mapFun f ⁻¹' D.nbhd : Set (UnderlyingSpace ℂ Y'))}) :
    TotalSpace D.F ((D.nbhdMap (f := f)) *ᵖ D.Q) :=
  pullbackMk D.nbhdMap ⟨mapFun (proj ((Scheme.Modules.pullback f).obj D.E)) p.1, p.2⟩
    (D.quot ⟨mapFun (baseChangeMap f D.E) p.1, by
      rw [mapFun_proj_mapFun_baseChangeMap]; exact p.2⟩)
    (by rw [D.proj_quot]; exact Subtype.ext (mapFun_proj_mapFun_baseChangeMap _ _ _))

/-- The image of `pullbackQuot` in `Q` is the quotient map applied to the image under `f̃`. -/
lemma lift_pullbackQuot (p) : Pullback.lift D.nbhdMap (D.pullbackQuot (f := f) p) =
    D.quot ⟨mapFun (baseChangeMap f D.E) p.1, by
      rw [mapFun_proj_mapFun_baseChangeMap]; exact p.2⟩ :=
  lift_pullbackMk _ _ _ _

/-- The quotient map `𝐕(f^*ℰ)(ℂ)|_{f⁻¹V} → f^*Q` is continuous. -/
lemma continuous_pullbackQuot : Continuous (D.pullbackQuot (f := f)) := by
  change Continuous[_, pullbackTopology D.F D.Q D.nbhdMap] _
  rw [pullbackTopology_def]
  refine continuous_inf_rng.2 ⟨continuous_induced_rng.2
    (((continuous_mapFun _).comp continuous_subtype_val).subtype_mk _),
    continuous_induced_rng.2 ?_⟩
  exact (D.continuous_quot.comp
    (((continuous_mapFun _).comp continuous_subtype_val).subtype_mk _)).congr
      fun p ↦ (D.lift_pullbackQuot p).symm

/-- `f̃ ∘ f^*σ = σ ∘ f` on complex points. -/
lemma mapFun_baseChangeMap_pullbackSectionMap (y : UnderlyingSpace ℂ Y') :
    mapFun (baseChangeMap f D.E) (mapFun (pullbackSectionMap f D.comp_proj) y) =
      mapFun D.σ (mapFun f y) :=
  UnderlyingSpace.ext (by
    change (y.toHom ≫ pullbackSectionMap f D.comp_proj) ≫ baseChangeMap f D.E =
      (y.toHom ≫ f) ≫ D.σ
    rw [Category.assoc, Category.assoc, pullbackSectionMap_baseChangeMap])

include D in
/-- In a fibre square over `Z(σ) = X`, `Z(f^*σ) = X'`. -/
lemma zeroLocus_pullbackSectionMap_eq_ker [IsClosedImmersion i] (sq : IsPullback i' g f i) :
    zeroLocus _ (pullbackSectionMap f D.comp_proj) = i'.ker := by
  rw [zeroLocus_pullbackSectionMap, D.zeroLocus_eq,
    ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← sq.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

/-- The linear isomorphism `w ↦ P w` of `ℂʳ` given by an invertible matrix. -/
def glEquiv {n : ℕ} (P : GL (Fin n) ℂ) : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
  LinearEquiv.ofLinear (P : Matrix (Fin n) (Fin n) ℂ).mulVecLin
    ((P⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).mulVecLin
    (LinearMap.ext fun w ↦ by simp [Matrix.mulVec_mulVec])
    (LinearMap.ext fun w ↦ by simp [Matrix.mulVec_mulVec])

/-- `glEquiv P` sends `w` to the matrix-vector product `P *ᵥ w`. -/
lemma glEquiv_apply {n : ℕ} (P : GL (Fin n) ℂ) (w : Fin n → ℂ) :
    glEquiv P w = (P : Matrix (Fin n) (Fin n) ℂ) *ᵥ w :=
  rfl

/-- **The pull-back of an orientation datum** along `f : Y' → Y`, in a fibre square
`X' = X ×_Y Y'` with `i`, `i'` regular of codimension `d`: `(f^*ℰ, f^*σ, f⁻¹V, f^*Q)`. -/
def pullback [IsClosedImmersion i] (hi : IsRegularClosedImmersionOfCodim i d)
    (hi' : IsRegularClosedImmersionOfCodim i' d) (sq : IsPullback i' g f i) :
    RegularImbeddingOrientationDatum i' d where
  rank := D.rank
  le_rank := D.le_rank
  E := (Scheme.Modules.pullback f).obj D.E
  σ := pullbackSectionMap f D.comp_proj
  comp_proj := pullbackSectionMap_proj f D.comp_proj
  zeroLocus_eq := D.zeroLocus_pullbackSectionMap_eq_ker sq
  nbhd := mapFun f ⁻¹' D.nbhd
  isOpen_nbhd := D.isOpen_nbhd.preimage (continuous_mapFun f)
  range_subset_nbhd := by
    rw [range_map_eq_preimage_of_isPullback sq]
    exact preimage_mono D.range_subset_nbhd
  F := D.F
  finrank_F := D.finrank_F
  Q := D.nbhdMap (f := f) *ᵖ D.Q
  quot := D.pullbackQuot
  continuous_quot := D.continuous_pullbackQuot
  proj_quot _ := rfl
  fibre c' y hy hyV := by
    have : IsClosedImmersion i' := MorphismProperty.of_isPullback sq.flip inferInstance
    set c := chartAt D.E D.rank (mapFun f y)
    have hc : mapFun f y ∈ chartBase c := mem_chartBase_chartAt _ _ _
    have hyW : y.toHom (IsLocalRing.closedPoint ℂ) ∈ f ⁻¹ᵁ c.1.1 := by
      have : ⊤ ≤ y.toHom ⁻¹ᵁ (f ⁻¹ᵁ c.1.1) := by
        rwa [← Scheme.Hom.comp_preimage, ← toHom_mapFun]
      exact (top_le_preimage_iff y _).1 this
    obtain ⟨c'', hyc'', hc''⟩ := exists_chart_mem_le
      (E := (Scheme.Modules.pullback f).obj D.E) (r := D.rank) hyW
    have hy'' : y ∈ chartBase c'' := (top_le_preimage_iff y _).2 hyc''
    have hyc' : y ∈ chartBase c' := hy
    obtain ⟨A, hA⟩ := exists_gl_coord_baseChangeMap f D.E c c'' hc'' y hy''
    obtain ⟨T, hT⟩ := exists_coord_eq_mulVec c' c'' hyc' hy''
    obtain ⟨L₀, hL₀, hsurj₀, hcompl₀⟩ := D.fibre c (mapFun f y) hc hyV
    set e := glEquiv (A * T)
    have hAM : ∀ v, (A : Matrix (Fin D.rank) (Fin D.rank) ℂ) *ᵥ v =
        Matrix.of (fun a b ↦ eval y hy'' (baseChangeSection f c c'' hc'' a b)) *ᵥ v := by
      intro v
      have hq := mapFun_proj_chartInv c'' y hy'' v
      have h1 := hA _ hq
      rw [coord_baseChangeMap_eq_mulVec f c c'' hc'' hy'' _ hq] at h1
      erw [coord_chartInv] at h1
      exact h1.symm
    have hTt : ∀ v, (T : Matrix (Fin D.rank) (Fin D.rank) ℂ) *ᵥ v = transition c' c'' y *ᵥ v := by
      intro v
      have hq := mapFun_proj_chartInv c' y hy v
      have h1 := hT _ hq
      have h2 := coord_eq_transition_mulVec c' c'' (chartInv c' y hy v)
        (top_le_preimage_proj_inf (by rw [hq]; exact ⟨hyc', hy''⟩))
      rw [hq, coord_chartInv] at h2
      rw [coord_chartInv] at h1
      exact h1.symm.trans h2
    refine ⟨L₀ ∘ₗ e.toLinearMap, fun w ↦ ?_, hsurj₀.comp e.surjective, ?_⟩
    · refine pullback_totalSpace_ext D.nbhdMap
        (Subtype.ext (mapFun_proj_chartInv c' y hy w)) ?_
      refine (D.lift_pullbackQuot _).trans (Eq.trans ?_ (hL₀ (e w)))
      congr 2
      exact mapFun_baseChangeMap_chartInv f c c' c'' hy hc A T hA hT w
    · rintro ⟨x', rfl⟩
      have e₀ := MMP.mapFun_comp_of_isPullback sq x'
      have hN : normalFibre (pullbackSectionMap f D.comp_proj) c' (UnderlyingSpace.map i' x') =
          (normalFibre D.σ c (mapFun f (mapFun i' x'))).comap e.toLinearMap := by
        refine Submodule.eq_of_le_of_finrank_eq (fun w hw ↦ ?_) ?_
        · have hw'' := transition_mulVec_mem_normalFibre (pullbackSectionMap_proj f D.comp_proj)
            c' c'' hy hy'' hw
          rw [← hTt] at hw''
          have := mulVec_mem_normalFibre_pullbackSectionMap f D.comp_proj c c'' hc'' hy'' hw''
          rw [← hAM, Matrix.mulVec_mulVec] at this
          change e w ∈ normalFibre D.σ c (mapFun f (mapFun i' x'))
          rwa [glEquiv_apply, Matrix.GeneralLinearGroup.coe_mul]
        · rw [Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
          have h1 := finrank_normalFibre i' hi' (pullbackSectionMap_proj f D.comp_proj)
            (D.zeroLocus_pullbackSectionMap_eq_ker sq) c' x' hy
          have h2 := finrank_normalFibre i hi D.comp_proj D.zeroLocus_eq c (mapFun g x')
            (by rw [← e₀]; exact hc)
          rw [← e₀] at h2
          exact h1.trans h2.symm
      have hmem : mapFun f (mapFun i' x') ∈ range (UnderlyingSpace.map (K := ℂ) i) := by
        rw [e₀]
        exact ⟨_, rfl⟩
      have := (Submodule.orderIsoMapComap e).symm.isCompl (hcompl₀ hmem)
      rw [Submodule.orderIsoMapComap_symm_apply, Submodule.orderIsoMapComap_symm_apply] at this
      rw [hN]
      convert this using 1
      all_goals first | rfl | exact LinearMap.ker_comp _ _
  quot_sec_notMem y hy := by
    rintro ⟨b, hb⟩
    have hy' : (D.nbhdMap (f := f) y).1 ∉ range (UnderlyingSpace.map (K := ℂ) i) :=
      fun h ↦ hy (by rwa [range_map_eq_preimage_of_isPullback sq])
    apply D.quot_sec_notMem (D.nbhdMap y) hy'
    have h1 := congrArg (Pullback.lift D.nbhdMap) hb
    rw [D.lift_pullbackQuot] at h1
    refine ⟨D.nbhdMap b, ?_⟩
    refine (show _ = Pullback.lift D.nbhdMap (Bundle.zeroSection D.F (D.nbhdMap (f := f) *ᵖ D.Q) b)
      from rfl).trans (h1.trans ?_)
    congr 2
    exact D.mapFun_baseChangeMap_pullbackSectionMap y.1

/-- The section of `f^*Q` given by the pulled-back datum maps, in `Q`, to the section of `Q` at the
image point. -/
lemma lift_sectionBar_pullback [IsClosedImmersion i] (hi : IsRegularClosedImmersionOfCodim i d)
    (hi' : IsRegularClosedImmersionOfCodim i' d) (sq : IsPullback i' g f i)
    (y : (D.pullback hi hi' sq).nbhd) :
    Pullback.lift D.nbhdMap ((D.pullback hi hi' sq).sectionBar y) =
      D.sectionBar (D.nbhdMap y) := by
  refine (D.lift_pullbackQuot _).trans ?_
  change D.quot _ = D.quot _
  congr 2
  exact D.mapFun_baseChangeMap_pullbackSectionMap y.1

variable (R : Type) [CommRing R]

/-- `f⁻¹(V) - X' ⊆ f⁻¹(V - X)`. -/
lemma compl_subset_preimage_nbhdMap (sq : IsPullback i' g f i) :
    (Subtype.val ⁻¹' range (UnderlyingSpace.map (K := ℂ) i') :
      Set (mapFun f ⁻¹' D.nbhd : Set (UnderlyingSpace ℂ Y')))ᶜ ⊆
      (TopCat.ofHom D.nbhdMap) ⁻¹' (Subtype.val ⁻¹' range (UnderlyingSpace.map (K := ℂ) i))ᶜ :=
  fun y hy h ↦ hy (by
    change y.1 ∈ range (UnderlyingSpace.map (K := ℂ) i')
    rw [range_map_eq_preimage_of_isPullback sq]
    exact h)

/-- `σ̄^*` commutes with the pull-back along `f⁻¹(V) → V`. -/
lemma thomPullback_comp_map [IsClosedImmersion i] (hi : IsRegularClosedImmersionOfCodim i d)
    (hi' : IsRegularClosedImmersionOfCodim i' d) (sq : IsPullback i' g f i) :
    D.thomPullback R ≫ relativeSingularCohomology.map R (ModuleCat.of R R)
        (TopCat.ofHom D.nbhdMap) (D.compl_subset_preimage_nbhdMap sq) _ =
      relativeSingularCohomology.map R (ModuleCat.of R R) (pullbackBundleMap D.F D.Q D.nbhdMap)
        (pullbackBundleMap_compl_zeroSection D.F D.Q D.nbhdMap) _ ≫
        (D.pullback hi hi' sq).thomPullback R := by
  have core : relativeSingularCohomology.map R (ModuleCat.of R R) D.sectionBarHom
        (fun _ hx ↦ hx) _ ≫
      relativeSingularCohomology.map R (ModuleCat.of R R) (𝟙 _)
        (compl_subset_compl.mpr D.sectionBar_preimage_subset) _ ≫
      relativeSingularCohomology.map R (ModuleCat.of R R) (TopCat.ofHom D.nbhdMap)
        (D.compl_subset_preimage_nbhdMap sq) ((2 * Module.finrank ℂ D.F : ℕ) : ℤ) =
      relativeSingularCohomology.map R (ModuleCat.of R R) (pullbackBundleMap D.F D.Q D.nbhdMap)
        (pullbackBundleMap_compl_zeroSection D.F D.Q D.nbhdMap) _ ≫
      relativeSingularCohomology.map R (ModuleCat.of R R) (D.pullback hi hi' sq).sectionBarHom
        (fun _ hx ↦ hx) _ ≫
      relativeSingularCohomology.map R (ModuleCat.of R R) (𝟙 _)
        (compl_subset_compl.mpr (D.pullback hi hi' sq).sectionBar_preimage_subset) _ := by
    refine (congrArg (_ ≫ ·)
      (relativeSingularCohomology.map_comp_map_eq R _ _ _ _ _ rfl _)).trans ?_
    refine (relativeSingularCohomology.map_comp_map_eq R _ _ _ _ _ rfl _).trans ?_
    refine Eq.trans ?_
      (congrArg (_ ≫ ·) (relativeSingularCohomology.map_comp_map_eq R _ _ _ _ _ rfl _)).symm
    refine Eq.trans ?_ (relativeSingularCohomology.map_comp_map_eq R _ _ _ _ _ rfl _).symm
    refine relativeSingularCohomology.map_congr_hom R _ _ _ ?_ _
    refine ConcreteCategory.hom_ext _ _ fun y ↦ ?_
    exact (D.lift_sectionBar_pullback hi hi' sq y).symm
  change (_ ≫ _ ≫ eqToHom _) ≫ _ = _ ≫ _ ≫ _ ≫ eqToHom _
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans ?_
  refine (congrArg (_ ≫ _ ≫ ·)
    (relativeSingularCohomology.eqToHom_comp_map R _ _ _ D.finrank_F _
      (by rw [D.finrank_F]))).trans ?_
  exact (reassoc_of% core) _

end RegularImbeddingOrientationDatum

variable {i : X ⟶ Y} {i' : X' ⟶ Y'} {f : Y' ⟶ Y} {g : X' ⟶ X} [i.IsOver (Spec (.of ℂ))]
  [i'.IsOver (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))] [g.IsOver (Spec (.of ℂ))] {d : ℕ}
  (R : Type) [CommRing R]

open RegularImbeddingOrientationDatum in
/-- **Orientation classes pull back** along fibre squares (Fulton, Lemma 19.2 (a), existence
half): if `u` is an orientation class of `i`, then `f^* u` is one of `i'`. -/
theorem IsRegularImbeddingOrientationClass.pullback_of_isPullback [IsClosedImmersion i]
    (hi : IsRegularClosedImmersionOfCodim i d) (hi' : IsRegularClosedImmersionOfCodim i' d)
    (sq : IsPullback i' g f i)
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map i)) (2 * d : ℕ)}
    (hu : IsRegularImbeddingOrientationClass R i d u) :
    IsRegularImbeddingOrientationClass R i' d
      ((cohomologyWithSupports.forget R (ModuleCat.of R R) _
        (range_map_eq_preimage_of_isPullback sq).ge _).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f)) _ _).hom u)) := by
  obtain ⟨D, uQ, hQ, hu⟩ := hu
  refine ⟨D.pullback hi hi' sq, (relativeSingularCohomology.map R (ModuleCat.of R R)
    (pullbackBundleMap D.F D.Q D.nbhdMap) (pullbackBundleMap_compl_zeroSection D.F D.Q D.nbhdMap)
    _).hom uQ, hQ.pullback _ _ _, ?_⟩
  have key₁ : (excisionRestrict R _ (D.pullback hi hi' sq).nbhd _).hom
      ((cohomologyWithSupports.forget R (ModuleCat.of R R) _
        (range_map_eq_preimage_of_isPullback sq).ge _).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f)) _ _).hom u)) =
      (relativeSingularCohomology.map R (ModuleCat.of R R) (TopCat.ofHom D.nbhdMap)
        (D.compl_subset_preimage_nbhdMap sq) _).hom ((excisionRestrict R _ D.nbhd _).hom u) := by
    simp only [excisionRestrict, cohomologyWithSupports.pullback, cohomologyWithSupports.forget]
    refine Eq.trans (rfl : _ = ModuleCat.Hom.hom
      (relativeSingularCohomology.map R _ (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f)) _ _ ≫
        relativeSingularCohomology.map R _ (𝟙 _) _ _ ≫
        relativeSingularCohomology.map R _ (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
          _ _) u) (Eq.trans ?_ (rfl : ModuleCat.Hom.hom
      (relativeSingularCohomology.map R _ (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
          _ _ ≫ relativeSingularCohomology.map R _ (TopCat.ofHom D.nbhdMap) _ _) u = _))
    refine congrArg (fun φ ↦ ModuleCat.Hom.hom φ u) ?_
    refine (congrArg (_ ≫ ·)
      (relativeSingularCohomology.map_comp_map_eq R _ _ _ _ _ rfl _)).trans ?_
    refine (relativeSingularCohomology.map_comp_map_eq R _ _ _ _ _ rfl _).trans ?_
    refine Eq.trans ?_ (relativeSingularCohomology.map_comp_map_eq R _ _ _ _ _ rfl _).symm
    exact relativeSingularCohomology.map_congr_hom R _ _ _
      (ConcreteCategory.hom_ext _ _ fun _ ↦ rfl) _
  rw [key₁, hu]
  exact congrArg (fun φ ↦ ModuleCat.Hom.hom φ uQ) (D.thomPullback_comp_map R hi hi' sq)

/-- **Base change of orientation classes** (Fulton, Lemma 19.2 (a)): in a fibre square
`X' = X ×_Y Y'` of complex schemes, with `i : X → Y` and `i' : X' → Y'` regular imbeddings of
codimension `d` and `f : Y' → Y`, `f^*(u_i) = u_{i'}` in `H^{2d}(Y', Y' - X')`. -/
theorem IsRegularImbeddingOrientationClass.pullback_eq [IsComplexScheme Y'] [IsClosedImmersion i]
    (hi : IsRegularClosedImmersionOfCodim i d) (hi' : IsRegularClosedImmersionOfCodim i' d)
    (sq : IsPullback i' g f i)
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map i)) (2 * d : ℕ)}
    {u' : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y'))
      (range (UnderlyingSpace.map i')) (2 * d : ℕ)}
    (hu : IsRegularImbeddingOrientationClass R i d u)
    (hu' : IsRegularImbeddingOrientationClass R i' d u') :
    (cohomologyWithSupports.forget R (ModuleCat.of R R) _
        (range_map_eq_preimage_of_isPullback sq).ge _).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f)) _ _).hom u) = u' :=
  haveI : IsClosedImmersion i' := MorphismProperty.of_isPullback sq.flip inferInstance
  (hu.pullback_of_isPullback R hi hi' sq).eq R hi' hu'

end MMP.Modules
