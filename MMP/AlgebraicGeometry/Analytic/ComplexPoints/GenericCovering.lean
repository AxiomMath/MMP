module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.CoveringPresentationSheets
public import MMP.AlgebraicGeometry.Variety.GenericFiniteness

/-!
# A proper morphism of complex varieties of the same dimension is generically a covering

Let `f : V → W` be a proper surjective morphism of complex varieties with `dim V = dim W = n` and
`d = deg(V/W)`. There is a nonempty Zariski open `W₀ ⊆ W_reg` with `f⁻¹(W₀) ⊆ V_reg` such that
every `w ∈ W₀(ℂ)` has a connected open neighbourhood `U ⊆ W₀(ℂ)`, a coordinate ball of an
algebraic chart of `W_reg(ℂ)`, with `f⁻¹(U) = U₁ ⊔ ⋯ ⊔ U_d`, each `U_i` open and mapped
biholomorphically onto `U` by `f`.

The open `W₀` is the locus `{c δ ≠ 0}` in an affine open `U' ⊆ W` over which `f` is finite and has
a covering presentation `Γ(f⁻¹ U') = Γ(U')[y]`, `f(y) = 0`, of degree `d`
(`MMP.GenericCovering.exists_isAffineOpen_coveringPresentation`). Over a ball `S`
in an algebraic chart `e` of `W_reg(ℂ)` at `w` the roots of `f` are `d` holomorphic functions with
distinct values, and the `ℂ`-points of `V` over `U = e⁻¹(S)` form `d` sheets `U_i`, on which
`e ∘ f` is an algebraic chart of `V_reg(ℂ)`
(`MMP.GenericCovering.CoveringPresentation.SheetData.isAlgebraicChart_chart`).
In the charts `e ∘ f|_{U_i}` of `U_i` and `e` of `U`, the map `f : U_i → U` is the identity, so it
is biholomorphic.

## Main definitions

* `MMP.UnderlyingSpace.regularOpensInter`: an open subset of `X(ℂ)`, as an open
  subset of the complex manifold `X_reg(ℂ)`.

## Main results

* `MMP.UnderlyingSpace.IsAlgebraicChart.restrict_openEmbedding`: algebraic charts
  restrict along open immersions.
* `MMP.GenericCovering.exists_preimage_eq_iUnion_diffeomorph`: the generic
  covering structure of `f`.

## Implementation notes

"Biholomorphic" is a `C^ω` diffeomorphism (`Diffeomorph` of order `ω`) between the open
submanifolds `U_i ⊆ V_reg(ℂ)` and `U ⊆ W_reg(ℂ)`, for the holomorphic atlases
`MMP.UnderlyingSpace.regularChartedSpace` of algebraic charts with values in `ℂⁿ`.
The degree `deg(V/W)` is the residue degree `f.residueDegree (genericPoint V)`, the degree of
the extension of function fields `ℂ(W) ⊆ ℂ(V)`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
open scoped ContDiff

namespace MMP

open MMP.Intersection.Scheme (dimension)

namespace UnderlyingSpace

section Restrict

variable {𝕜 : Type} [RCLike 𝕜] {U X : Scheme.{0}} [U.Over (Spec (.of 𝕜))] [X.Over (Spec (.of 𝕜))]
  (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of 𝕜))] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {e : OpenPartialHomeomorph (UnderlyingSpace 𝕜 X) E}
  [Nonempty (UnderlyingSpace 𝕜 U)]

/-- The restriction of a chart of `X(𝕜)` to `U(𝕜)` along an open immersion `U → X`. -/
abbrev restrictChart (e : OpenPartialHomeomorph (UnderlyingSpace 𝕜 X) E) :
    OpenPartialHomeomorph (UnderlyingSpace 𝕜 U) E :=
  (IsOpenEmbedding.toOpenPartialHomeomorph (map (K := 𝕜) j)
    (isOpenEmbedding_map_of_isOpenImmersion j)).trans e

omit [NormedSpace 𝕜 E] in
/-- The restriction of `e` to `U(𝕜)` sends `q` to the value of `e` at the image of `q` in
`X(𝕜)`. -/
lemma restrictChart_apply (q : UnderlyingSpace 𝕜 U) : restrictChart j e q = e (mapFun j q) :=
  rfl

omit [NormedSpace 𝕜 E] in
/-- On the target of the restricted chart, the image in `X(𝕜)` of its inverse is the inverse of
`e`. -/
lemma mapFun_restrictChart_symm {k : E} (hk : k ∈ (restrictChart j e).target) :
    mapFun j ((restrictChart j e).symm k) = e.symm k := by
  obtain ⟨-, hk⟩ := hk
  simp only [Set.mem_preimage, IsOpenEmbedding.toOpenPartialHomeomorph_target] at hk
  obtain ⟨q, hq⟩ := hk
  simp only [OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply]
  rw [← hq, IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]
  rfl

/-- **Algebraic charts restrict along open immersions.** For an open immersion `j : U → X` over
`𝕜` and an algebraic chart `e` of `X(𝕜)`, the restriction of `e` to `U(𝕜)` is an algebraic chart
of `U(𝕜)`. -/
theorem IsAlgebraicChart.restrict_openEmbedding (he : IsAlgebraicChart e) :
    IsAlgebraicChart (restrictChart j e) where
  contDiffOn_evalExt V a := by
    have hpre : ∀ q' : UnderlyingSpace 𝕜 U, ⊤ ≤ (mapFun j q').toHom ⁻¹ᵁ (j ''ᵁ V) ↔
        ⊤ ≤ q'.toHom ⁻¹ᵁ V := fun q' ↦ by
      rw [toHom_mapFun, Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq]
    have hev : ∀ q' : UnderlyingSpace 𝕜 U,
        evalExt (j ''ᵁ V) ((j.appIso V).inv a) (mapFun j q') = evalExt V a q' := fun q' ↦ by
      rw [evalExt_mapFun, Scheme.Hom.appIso_inv_app_apply, evalExt_eqToHom]
    refine ((he.contDiffOn_evalExt (j ''ᵁ V) ((j.appIso V).inv a)).mono fun k hk ↦ ?_).congr
      fun k hk ↦ ?_
    · refine ⟨hk.1.1, ?_⟩
      have := (hpre _).2 hk.2
      rwa [mapFun_restrictChart_symm j hk.1] at this
    · rw [← hev, mapFun_restrictChart_symm j hk.1]
  exists_eq_evalExt q hq := by
    obtain ⟨V, ι, _, a, L, hV, hL⟩ := he.exists_eq_evalExt (mapFun j q) hq.2
    have hpre : ∀ q' : UnderlyingSpace 𝕜 U, ⊤ ≤ (mapFun j q').toHom ⁻¹ᵁ V ↔
        ⊤ ≤ q'.toHom ⁻¹ᵁ (j ⁻¹ᵁ V) := fun q' ↦ by
      rw [toHom_mapFun, Scheme.Hom.comp_preimage]
    refine ⟨j ⁻¹ᵁ V, ι, inferInstance, fun i ↦ j.app V (a i), L, (hpre q).1 hV, ?_⟩
    intro q' hq' hq'V
    rw [restrictChart_apply]
    erw [hL _ hq'.2 ((hpre q').2 hq'V)]
    exact congrArg L (funext fun i ↦ evalExt_mapFun j V (a i) q')

end Restrict

section OpensRange

variable {𝕜 : Type} [RCLike 𝕜] {X : Scheme.{0}} [X.Over (Spec (.of 𝕜))] {O : X.Opens}
  [O.toScheme.Over (Spec (.of 𝕜))] [O.ι.IsOver (Spec (.of 𝕜))]

/-- A `𝕜`-point of `X` whose closed point lies in the open `O` comes from a `𝕜`-point of `O`. -/
lemma mem_range_mapFun_ι {p : UnderlyingSpace 𝕜 X}
    (hp : p.toHom (IsLocalRing.closedPoint 𝕜) ∈ O) :
    p ∈ Set.range (mapFun (K := 𝕜) O.ι) := by
  rw [range_mapFun_of_isOpenImmersion, Set.mem_ofPred_eq, Scheme.Opens.opensRange_ι,
    top_le_preimage_iff]
  exact hp

/-- The image in `X(𝕜)` of a `𝕜`-point of the open `O` has its closed point in `O`. -/
lemma toHom_mapFun_ι_mem (p : UnderlyingSpace 𝕜 O) :
    (mapFun O.ι p).toHom (IsLocalRing.closedPoint 𝕜) ∈ O := by
  have := Set.mem_range_self (f := ⇑O.ι) (p.toHom (IsLocalRing.closedPoint 𝕜))
  rwa [Scheme.Opens.range_ι] at this

end OpensRange

variable {𝕜 : Type} [RCLike 𝕜] {X : Scheme.{0}} [X.Over (Spec (.of 𝕜))]
  [LocallyOfFiniteType (X ↘ Spec (.of 𝕜))]

/-- An open subset of `X(𝕜)`, as an open subset of `X_reg(𝕜)`: its intersection with `X_reg(𝕜)`. -/
def regularOpensInter (O : Opens (UnderlyingSpace 𝕜 X)) : Opens (regularOpens 𝕜 X) :=
  ⟨Subtype.val ⁻¹' O, O.2.preimage continuous_subtype_val⟩

/-- A point of `X_reg(𝕜)` lies in `regularOpensInter O` if and only if it lies in `O`. -/
@[simp]
lemma mem_regularOpensInter {O : Opens (UnderlyingSpace 𝕜 X)} {p : regularOpens 𝕜 X} :
    p ∈ regularOpensInter O ↔ p.1 ∈ O :=
  Iff.rfl

end UnderlyingSpace

namespace GenericCovering

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {M N : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold (modelWithCornersSelf ℂ E) ω M] [TopologicalSpace N]
  [ChartedSpace E N]
  [IsManifold (modelWithCornersSelf ℂ E) ω N]

/-- A map between open subsets of two complex manifolds which reads as the identity in a chart of
each is holomorphic. -/
theorem contMDiff_of_chart_apply_eq {A : Opens M} {B : Opens N} {Φ : OpenPartialHomeomorph M E}
    {Ψ : OpenPartialHomeomorph N E} (hΦ : Φ ∈ atlas E M) (hΨ : Ψ ∈ atlas E N)
    (hA : (A : Set M) ⊆ Φ.source) (hB : (B : Set N) ⊆ Ψ.source) (F : A → B)
    (hF : ∀ x, Ψ (F x) = Φ x) :
    ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω F := by
  intro x
  have : Nonempty A := ⟨x⟩
  have : Nonempty B := ⟨F x⟩
  set Φ' := Φ.subtypeRestr (s := A) ⟨x⟩
  set Ψ' := Ψ.subtypeRestr (s := B) ⟨F x⟩
  have hΦ' : Φ' ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ E) ω A :=
    StructureGroupoid.subtypeRestr_mem_maximalAtlas hΦ _
  have hΨ' : Ψ' ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ E) ω B :=
    StructureGroupoid.subtypeRestr_mem_maximalAtlas hΨ _
  have hsrc : ∀ y : A, y ∈ Φ'.source := fun y ↦ by
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact hA y.2
  have hsrc' : ∀ y : B, y ∈ Ψ'.source := fun y ↦ by
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact hB y.2
  have hF' : ∀ y, Ψ' (F y) = Φ' y := fun y ↦ hF y
  have hFeq : ∀ y, F y = Ψ'.symm (Φ' y) := fun y ↦ by
    rw [← hF', Ψ'.left_inv (hsrc' _)]
  rw [contMDiffAt_iff_of_mem_maximalAtlas hΦ' hΨ' (hsrc x) (hsrc' (F x))]
  refine ⟨?_, ?_⟩
  · rw [show F = Ψ'.symm ∘ Φ' from funext hFeq]
    refine ContinuousAt.comp (Ψ'.continuousAt_symm ?_) (Φ'.continuousAt (hsrc x))
    rw [← hF']
    exact Ψ'.map_source (hsrc' _)
  · simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id, Function.id_comp,
      Function.comp_id]
    refine (contDiffAt_id.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [Φ'.open_target.mem_nhds (Φ'.map_source (hsrc x))] with k hk
    simp only [Function.comp_apply, id]
    rw [hF', Φ'.right_inv hk]

/-- Mutually inverse maps between open subsets of two complex manifolds which read as the identity
in a chart of each form a holomorphic diffeomorphism. -/
theorem exists_diffeomorph_of_chart_apply_eq {A : Opens M} {B : Opens N}
    {Φ : OpenPartialHomeomorph M E} {Ψ : OpenPartialHomeomorph N E} (hΦ : Φ ∈ atlas E M)
    (hΨ : Ψ ∈ atlas E N) (hA : (A : Set M) ⊆ Φ.source) (hB : (B : Set N) ⊆ Ψ.source)
    (F : A → B) (G : B → A) (hF : ∀ x, Ψ (F x) = Φ x) (hG : ∀ y, Φ (G y) = Ψ y) :
    ∃ φ : Diffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) A B ω,
      ∀ x, φ x = F x :=
  ⟨{ toFun := F
     invFun := G
     left_inv := fun x ↦ Subtype.ext <| Φ.injOn (hA (G (F x)).2) (hA x.2) (by rw [hG, hF])
     right_inv := fun y ↦ Subtype.ext <| Ψ.injOn (hB (F (G y)).2) (hB y.2) (by rw [hF, hG])
     contMDiff_toFun := contMDiff_of_chart_apply_eq hΦ hΨ hA hB F hF
     contMDiff_invFun := contMDiff_of_chart_apply_eq hΨ hΦ hB hA G hG }, fun _ ↦ rfl⟩

end Manifold

open UnderlyingSpace

/-- The dimension of a variety is a natural number. -/
theorem exists_natCast_eq_dimension (K : Type) [Field K] (X : Scheme.{0}) [X.Over (Spec (.of K))]
    [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))] :
    ∃ n : ℕ, (n : WithBot ℕ∞) = dimension X := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of K))
  have h1 : dimension X ≠ ⊤ :=
    topologicalKrullDim_ne_top_of_locallyOfFiniteType K (X ↘ Spec (.of K))
  have h2 : (0 : WithBot ℕ∞) ≤ dimension X := by
    have : Nonempty (TopologicalSpace.IrreducibleCloseds X) :=
      ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩⟩
    exact Order.krullDim_nonneg
  generalize dimension X = d at h1 h2 ⊢
  induction d with
  | bot => exact absurd h2 (by simp)
  | coe d =>
    induction d with
    | top => exact absurd rfl h1
    | coe n => exact ⟨n, rfl⟩

/-- **The local structure over a point of `W₀`.** Let `f : V → W` be a morphism of complex
varieties of the same dimension, `U' ⊆ W` an affine open of regular points with `f⁻¹(U')` affine
and of regular points, and `(y, f, c, δ)` a covering presentation of `Γ(f⁻¹ U')` over `Γ(U')`.
Every `ℂ`-point `w` of `W₀ = {c δ ≠ 0} ⊆ U'` has a connected open neighbourhood `U ⊆ W₀(ℂ)`, a
coordinate ball, with `f⁻¹(U) = U₁ ⊔ ⋯ ⊔ U_d`, `d = deg f`, each `U_i` open and mapped
biholomorphically onto `U` by `f`. -/
theorem exists_local_sheets {V W : Scheme.{0}} [V.Over (Spec (.of ℂ))] [W.Over (Spec (.of ℂ))]
    [IsIntegral V] [LocallyOfFiniteType (V ↘ Spec (.of ℂ))] [QuasiCompact (V ↘ Spec (.of ℂ))]
    [IsIntegral W] [LocallyOfFiniteType (W ↘ Spec (.of ℂ))] [QuasiCompact (W ↘ Spec (.of ℂ))]
    (f : V ⟶ W) [f.IsOver (Spec (.of ℂ))]
    (hdim : dimension V = dimension W) {Ua : W.Opens} (hUa : IsAffineOpen Ua)
    (hUa' : IsAffineOpen (f ⁻¹ᵁ Ua)) (hUreg : (Ua : Set W) ⊆ regularLocus W)
    (hVreg : (f ⁻¹ᵁ Ua : Set V) ⊆ regularLocus V) [Algebra Γ(Ua, ⊤) Γ(f ⁻¹ᵁ Ua, ⊤)]
    (hg : algebraMap Γ(Ua, ⊤) Γ(f ⁻¹ᵁ Ua, ⊤) = (f ∣_ Ua).appTop.hom)
    (P : CoveringPresentation Γ(Ua, ⊤) Γ(f ⁻¹ᵁ Ua, ⊤)) (w : UnderlyingSpace ℂ W)
    (hw : w.toHom (IsLocalRing.closedPoint ℂ) ∈ Ua.ι ''ᵁ Ua.toScheme.basicOpen (P.c * P.δ)) :
    ∃ U : Opens (UnderlyingSpace ℂ W), IsConnected (U : Set (UnderlyingSpace ℂ W)) ∧ w ∈ U ∧
      (∀ p ∈ U, p.toHom (IsLocalRing.closedPoint ℂ) ∈
        Ua.ι ''ᵁ Ua.toScheme.basicOpen (P.c * P.δ)) ∧
      ∃ Ui : Fin P.f.natDegree → Opens (UnderlyingSpace ℂ V),
        Pairwise (fun i j ↦ Disjoint (Ui i : Set (UnderlyingSpace ℂ V)) (Ui j)) ∧
        mapFun f ⁻¹' U = ⋃ i, (Ui i : Set (UnderlyingSpace ℂ V)) ∧
        ∀ (n : ℕ) (hn : (n : WithBot ℕ∞) = dimension W),
          (∃ e : OpenPartialHomeomorph (UnderlyingSpace ℂ W) (EuclideanSpace ℂ (Fin n)),
            IsAlgebraicChart e ∧ ∃ x r, Metric.ball x r ⊆ e.target ∧
              (U : Set (UnderlyingSpace ℂ W)) = e.source ∩ e ⁻¹' Metric.ball x r) ∧
          ∀ i, letI := regularChartedSpace (𝕜 := ℂ) (X := W) hn
            letI := regularChartedSpace (𝕜 := ℂ) (X := V) (hn.trans hdim.symm)
            ∃ φ : Diffeomorph (modelWithCornersSelf ℂ (EuclideanSpace ℂ (Fin n)))
                (modelWithCornersSelf ℂ (EuclideanSpace ℂ (Fin n)))
                (regularOpensInter (Ui i)) (regularOpensInter U) ω,
              ∀ x, ((φ x : regularOpens ℂ W) : UnderlyingSpace ℂ W) =
                mapFun f ((x : regularOpens ℂ V) : UnderlyingSpace ℂ V) := by
  classical
  let : Ua.toScheme.Over (Spec (.of ℂ)) := ⟨Ua.ι ≫ W ↘ Spec (.of ℂ)⟩
  let : (f ⁻¹ᵁ Ua).toScheme.Over (Spec (.of ℂ)) := ⟨(f ⁻¹ᵁ Ua).ι ≫ V ↘ Spec (.of ℂ)⟩
  have : Ua.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  have : (f ⁻¹ᵁ Ua).ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  have : (f ∣_ Ua).IsOver (Spec (.of ℂ)) := ⟨by
    change f ∣_ Ua ≫ Ua.ι ≫ W ↘ Spec (.of ℂ) = (f ⁻¹ᵁ Ua).ι ≫ V ↘ Spec (.of ℂ)
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, comp_over]⟩
  have : IsAffine Ua := hUa
  have : IsAffine (f ⁻¹ᵁ Ua) := hUa'
  set ιW := Ua.ι
  set ιV := (f ⁻¹ᵁ Ua).ι
  set g := f ∣_ Ua
  set B := Ua.toScheme.basicOpen (P.c * P.δ)
  have hcomp : ∀ q : UnderlyingSpace ℂ (f ⁻¹ᵁ Ua),
      mapFun f (mapFun ιV q) = mapFun ιW (mapFun g q) := fun q ↦
    UnderlyingSpace.ext (by
      simp only [toHom_mapFun, Category.assoc, ιV, ιW, g, morphismRestrict_ι])
  have hinjW := mapFun_injective_of_mono (K := ℂ) ιW
  have hinjV := mapFun_injective_of_mono (K := ℂ) ιV
  have hB : ∀ p' : UnderlyingSpace ℂ Ua, (mapFun ιW p').toHom (IsLocalRing.closedPoint ℂ) ∈
      ιW ''ᵁ B ↔ evalTop p' (P.c * P.δ) ≠ 0 := fun p' ↦ by
    change ιW (p'.toHom (IsLocalRing.closedPoint ℂ)) ∈ _ ↔ _
    rw [Scheme.Hom.apply_mem_image_iff, ← top_le_preimage_iff,
      top_le_preimage_basicOpen_iff (U := ⊤) p' (Scheme.Hom.preimage_top _).ge]
    rfl
  -- the point `w` comes from `U'`
  obtain ⟨w', rfl⟩ := mem_range_mapFun_ι ((Scheme.Opens.ι_image_le Ua B) hw)
  have hcδ := (hB w').1 hw
  rw [← evalHom_apply, map_mul] at hcδ
  have hc : evalTop w' P.c ≠ 0 := left_ne_zero_of_mul hcδ
  have hδ : evalTop w' P.δ ≠ 0 := right_ne_zero_of_mul hcδ
  -- an algebraic chart at `w`
  obtain ⟨n₀, hn₀⟩ := exists_natCast_eq_dimension ℂ W
  have hwreg : mapFun ιW w' ∈ regularPart ℂ W :=
    (mem_regularPart_iff _).2 (hUreg (toHom_mapFun_ι_mem w'))
  obtain ⟨eW, hweW, heW⟩ := exists_isAlgebraicChart_of_dimension_eq hn₀ _ hwreg
  have : Nonempty (UnderlyingSpace ℂ Ua) := ⟨w'⟩
  set e' := restrictChart ιW eW
  have he' : IsAlgebraicChart e' := heW.restrict_openEmbedding ιW
  have hw'e' : w' ∈ e'.source := ⟨trivial, hweW⟩
  obtain ⟨D, ⟨r, hr⟩, hD0, hDδ⟩ := P.exists_sheetData he' hw'e' hc hδ
  -- the chart of `W` and the neighbourhood `U`
  set Ψ := e'.lift_openEmbedding (isOpenEmbedding_map_of_isOpenImmersion (K := ℂ) ιW)
  have hΨ : IsAlgebraicChart Ψ := he'.lift_openEmbedding ιW
  have hΨapply : ∀ x, Ψ (mapFun ιW x) = e' x := fun x ↦ e'.lift_openEmbedding_apply _
  have hΨsource : Ψ.source = mapFun ιW '' e'.source := e'.lift_openEmbedding_source _
  have hΨtarget : Ψ.target = e'.target := e'.lift_openEmbedding_target _
  let U : Opens (UnderlyingSpace ℂ W) := ⟨Ψ.source ∩ Ψ ⁻¹' D.S, Ψ.isOpen_inter_preimage D.isOpen⟩
  have hU : (U : Set (UnderlyingSpace ℂ W)) = Ψ.source ∩ Ψ ⁻¹' D.S := rfl
  have hmemU : ∀ x, mapFun ιW x ∈ U ↔ x ∈ e'.source ∧ e' x ∈ D.S := fun x ↦ by
    change mapFun ιW x ∈ Ψ.source ∧ Ψ (mapFun ιW x) ∈ D.S ↔ _
    rw [hΨsource, hΨapply, hinjW.mem_set_image]
  have hUW : ∀ p ∈ U, ∃ x, mapFun ιW x = p := fun p hp ↦ by
    obtain ⟨x, -, rfl⟩ := hΨsource ▸ hp.1
    exact ⟨x, rfl⟩
  have hUB : ∀ p ∈ U, p.toHom (IsLocalRing.closedPoint ℂ) ∈ ιW ''ᵁ B := fun p hp ↦ by
    obtain ⟨x, rfl⟩ := hUW p hp
    obtain ⟨hx1, hx2⟩ := (hmemU x).1 hp
    have h1 := D.ne_zero_c _ hx2
    have h2 := hDδ _ hx2
    rw [e'.left_inv hx1] at h1 h2
    rw [hB, ← evalHom_apply, map_mul]
    exact mul_ne_zero h1 h2
  -- the sheets
  set Φ : Fin P.f.natDegree → OpenPartialHomeomorph (UnderlyingSpace ℂ V)
      (EuclideanSpace ℂ (Fin n₀)) := fun i ↦
    (D.chart hg i).lift_openEmbedding (isOpenEmbedding_map_of_isOpenImmersion (K := ℂ) ιV)
  have hΦ : ∀ i, IsAlgebraicChart (Φ i) := fun i ↦
    (D.isAlgebraicChart_chart hg he' i).lift_openEmbedding ιV
  have hΦapply : ∀ i x, Φ i (mapFun ιV x) = e' (mapFun g x) := fun i x ↦
    (D.chart hg i).lift_openEmbedding_apply _
  have hΦsource : ∀ i, (Φ i).source = mapFun ιV '' D.sheet (g := g) i := fun i ↦
    (D.chart hg i).lift_openEmbedding_source _
  have hΦtarget : ∀ i, (Φ i).target = D.S := fun i ↦ (D.chart hg i).lift_openEmbedding_target _
  let Ui : Fin P.f.natDegree → Opens (UnderlyingSpace ℂ V) := fun i ↦
    ⟨(Φ i).source, (Φ i).open_source⟩
  have hpre : mapFun f ⁻¹' U = ⋃ i, (Ui i : Set (UnderlyingSpace ℂ V)) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_iUnion]
    change _ ↔ ∃ i, p ∈ (Φ i).source
    simp only [hΦsource]
    constructor
    · intro hp
      obtain ⟨x, hx⟩ := hUW _ hp
      have hpU : p.toHom (IsLocalRing.closedPoint ℂ) ∈ f ⁻¹ᵁ Ua := by
        change (mapFun f p).toHom (IsLocalRing.closedPoint ℂ) ∈ Ua
        rw [← hx]
        exact toHom_mapFun_ι_mem x
      obtain ⟨p', rfl⟩ := mem_range_mapFun_ι hpU
      rw [hcomp] at hx hp
      obtain ⟨h1, h2⟩ := (hmemU _).1 hp
      have : p' ∈ mapFun g ⁻¹' (e'.source ∩ e' ⁻¹' D.S) := ⟨h1, h2⟩
      rw [D.preimage_eq_iUnion_sheet hg, Set.mem_iUnion] at this
      obtain ⟨i, hi⟩ := this
      exact ⟨i, p', hi, rfl⟩
    · rintro ⟨i, p', hp', rfl⟩
      rw [hcomp]
      exact (hmemU _).2 ⟨hp'.1, hp'.2.1⟩
  have hwU : mapFun ιW w' ∈ U := (hmemU w').2 ⟨hw'e', hD0⟩
  refine ⟨U, ?_, hwU, hUB, Ui, fun i j hij ↦ ?_, hpre, fun n hn ↦ ?_⟩
  · have hS : D.S ⊆ Ψ.target := hΨtarget ▸ D.subset_target
    change _root_.IsConnected (U : Set (UnderlyingSpace ℂ W))
    rw [hU, ← Ψ.symm_image_eq_source_inter_preimage hS]
    refine IsConnected.image ⟨⟨_, hD0⟩, hr ▸ (convex_ball _ _).isPreconnected⟩ _
      (Ψ.continuousOn_symm.mono hS)
  · change Disjoint (Φ i).source (Φ j).source
    rw [hΦsource, hΦsource]
    exact (Set.disjoint_image_iff hinjV).2 (D.disjoint_sheet hij)
  obtain rfl : n = n₀ := by exact_mod_cast hn.trans hn₀.symm
  refine ⟨⟨Ψ, hΨ, e' w', r, by rw [hΨtarget, ← hr]; exact D.subset_target, by rw [hU, hr]⟩,
    fun i ↦ ?_⟩
  let := regularChartedSpace (𝕜 := ℂ) (X := W) hn
  let := regularChartedSpace (𝕜 := ℂ) (X := V) (hn.trans hdim.symm)
  have := isManifold_regularOpens (𝕜 := ℂ) (X := W) hn
  have := isManifold_regularOpens (𝕜 := ℂ) (X := V) (hn.trans hdim.symm)
  have hregW : ∀ p ∈ U, p ∈ regularPart ℂ W := fun p hp ↦ by
    obtain ⟨x, rfl⟩ := hUW p hp
    exact (mem_regularPart_iff _).2 (hUreg (toHom_mapFun_ι_mem x))
  have hregV : ∀ p ∈ (Φ i).source, p ∈ regularPart ℂ V := fun p hp ↦ by
    rw [hΦsource] at hp
    obtain ⟨p', -, rfl⟩ := hp
    exact (mem_regularPart_iff _).2 (hVreg (toHom_mapFun_ι_mem p'))
  have hkey : ∀ p ∈ (Φ i).source, Ψ (mapFun f p) = Φ i p := fun p hp ↦ by
    rw [hΦsource] at hp
    obtain ⟨p', -, rfl⟩ := hp
    rw [hcomp, hΨapply, hΦapply]
  have hfU : ∀ p ∈ (Φ i).source, mapFun f p ∈ U := fun p hp ↦
    (Set.ext_iff.1 hpre p).2 (Set.mem_iUnion.2 ⟨i, hp⟩)
  have hsymm : ∀ p ∈ U, (Φ i).symm (Ψ p) ∈ (Φ i).source := fun p hp ↦
    (Φ i).map_target (by rw [hΦtarget]; exact hp.2)
  have hneW : Nonempty (regularOpens ℂ W) := ⟨⟨_, hregW _ hwU⟩⟩
  have hneV : Nonempty (regularOpens ℂ V) := ⟨⟨_, hregV _ (hsymm _ hwU)⟩⟩
  have hΦat : (Φ i).subtypeRestr hneV ∈ atlas (EuclideanSpace ℂ (Fin n)) (regularOpens ℂ V) :=
    ⟨Φ i, hneV, hΦ i, rfl⟩
  have hΨat : Ψ.subtypeRestr hneW ∈ atlas (EuclideanSpace ℂ (Fin n)) (regularOpens ℂ W) :=
    ⟨Ψ, hneW, hΨ, rfl⟩
  let F : regularOpensInter (Ui i) → regularOpensInter U := fun x ↦
    ⟨⟨mapFun f x.1.1, hregW _ (hfU _ x.2)⟩, hfU _ x.2⟩
  let G : regularOpensInter U → regularOpensInter (Ui i) := fun y ↦
    ⟨⟨(Φ i).symm (Ψ y.1.1), hregV _ (hsymm _ y.2)⟩, hsymm _ y.2⟩
  have hA : ((regularOpensInter (Ui i) : Opens (regularOpens ℂ V)) : Set (regularOpens ℂ V)) ⊆
      ((Φ i).subtypeRestr hneV).source := by
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact fun x hx ↦ hx
  have hB : ((regularOpensInter U : Opens (regularOpens ℂ W)) : Set (regularOpens ℂ W)) ⊆
      (Ψ.subtypeRestr hneW).source := by
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact fun x hx ↦ (show x.1 ∈ Ψ.source ∩ Ψ ⁻¹' D.S from hx).1
  obtain ⟨φ, hφ⟩ := exists_diffeomorph_of_chart_apply_eq hΦat hΨat hA hB F G
    (fun x ↦ hkey _ x.2) fun y ↦ (Φ i).right_inv (by rw [hΦtarget]; exact y.2.2)
  exact ⟨φ, fun x ↦ congrArg (fun y : regularOpensInter U ↦
    ((y : regularOpens ℂ W) : UnderlyingSpace ℂ W)) (hφ x)⟩

/-- **The generic covering structure of a proper morphism of complex varieties of the same
dimension.** Let `f : V → W` be a proper surjective morphism of complex varieties with
`dim V = dim W`, and `d = deg(V/W)`. There is a nonempty Zariski open `W₀ ⊆ W` of regular points
with `f⁻¹(W₀)` consisting of regular points, such that every `w ∈ W₀(ℂ)` has a connected open
neighbourhood `U ⊆ W₀(ℂ)`, a coordinate ball of an algebraic chart of `W_reg(ℂ)`, with
`f⁻¹(U) = U₁ ⊔ ⋯ ⊔ U_d`, each `U_i` open and mapped biholomorphically onto `U` by `f`. -/
theorem exists_preimage_eq_iUnion_diffeomorph {V W : Scheme.{0}} [V.Over (Spec (.of ℂ))]
    [W.Over (Spec (.of ℂ))] [IsIntegral V] [LocallyOfFiniteType (V ↘ Spec (.of ℂ))]
    [QuasiCompact (V ↘ Spec (.of ℂ))] [IsIntegral W] [LocallyOfFiniteType (W ↘ Spec (.of ℂ))]
    [QuasiCompact (W ↘ Spec (.of ℂ))] (f : V ⟶ W)
    [f.IsOver (Spec (.of ℂ))] [IsProper f] (hf : Function.Surjective f)
    (hdim : dimension V = dimension W) :
    ∃ W₀ : W.Opens, (W₀ : Set W).Nonempty ∧ (W₀ : Set W) ⊆ regularLocus W ∧
      (f ⁻¹ᵁ W₀ : Set V) ⊆ regularLocus V ∧
      ∀ w : UnderlyingSpace ℂ W, w.toHom (IsLocalRing.closedPoint ℂ) ∈ W₀ →
        ∃ U : Opens (UnderlyingSpace ℂ W), IsConnected (U : Set (UnderlyingSpace ℂ W)) ∧
          w ∈ U ∧ (∀ p ∈ U, p.toHom (IsLocalRing.closedPoint ℂ) ∈ W₀) ∧
          (U : Set (UnderlyingSpace ℂ W)) ⊆ regularPart ℂ W ∧
          ∃ Ui : Fin (f.residueDegree (genericPoint V)) →
              Opens (UnderlyingSpace ℂ V),
            Pairwise (fun i j ↦ Disjoint (Ui i : Set (UnderlyingSpace ℂ V)) (Ui j)) ∧
            mapFun f ⁻¹' U = ⋃ i, (Ui i : Set (UnderlyingSpace ℂ V)) ∧
            (∀ i, (Ui i : Set (UnderlyingSpace ℂ V)) ⊆ regularPart ℂ V) ∧
            ∀ (n : ℕ) (hn : (n : WithBot ℕ∞) = dimension W),
              (∃ e : OpenPartialHomeomorph (UnderlyingSpace ℂ W) (EuclideanSpace ℂ (Fin n)),
                IsAlgebraicChart e ∧ ∃ x r, Metric.ball x r ⊆ e.target ∧
                  (U : Set (UnderlyingSpace ℂ W)) = e.source ∩ e ⁻¹' Metric.ball x r) ∧
              ∀ i, letI := regularChartedSpace (𝕜 := ℂ) (X := W) hn
                letI := regularChartedSpace (𝕜 := ℂ) (X := V) (hn.trans hdim.symm)
                ∃ φ : Diffeomorph (modelWithCornersSelf ℂ (EuclideanSpace ℂ (Fin n)))
                (modelWithCornersSelf ℂ (EuclideanSpace ℂ (Fin n)))
                    (regularOpensInter (Ui i)) (regularOpensInter U) ω,
                  ∀ x, ((φ x : regularOpens ℂ W) : UnderlyingSpace ℂ W) =
                    mapFun f ((x : regularOpens ℂ V) : UnderlyingSpace ℂ V) := by
  have : Surjective f := ⟨hf⟩
  obtain ⟨Ua, hUa, hηUa, hUreg, hVreg, hUa', hP⟩ :=
    exists_isAffineOpen_coveringPresentation (K := ℂ) f hdim
  let : Algebra Γ(Ua, ⊤) Γ(f ⁻¹ᵁ Ua, ⊤) := (f ∣_ Ua).appTop.hom.toAlgebra
  obtain ⟨P, hc, hδ, hdeg⟩ := hP
  have hW₀U : ∀ z ∈ (Ua.ι ''ᵁ Ua.toScheme.basicOpen (P.c * P.δ) : Set W), z ∈ (Ua : Set W) :=
    fun z hz ↦ Scheme.Opens.ι_image_le Ua _ hz
  refine ⟨Ua.ι ''ᵁ Ua.toScheme.basicOpen (P.c * P.δ), ?_, fun z hz ↦ hUreg (hW₀U z hz),
    fun z hz ↦ hVreg (hW₀U _ hz), fun w hw ↦ ?_⟩
  · have : Nonempty Ua := ⟨⟨_, hηUa⟩⟩
    have hne : Ua.toScheme.basicOpen (P.c * P.δ) ≠ ⊥ := by
      rw [Ne, basicOpen_eq_bot_iff]
      exact mul_ne_zero hc hδ
    obtain ⟨x, hx⟩ := (Opens.ne_bot_iff_nonempty _).1 hne
    exact ⟨Ua.ι x, (Scheme.Hom.apply_mem_image_iff _).2 hx⟩
  obtain ⟨U, hUc, hwU, hUW₀, Ui, hdisj, hpre, hrest⟩ :=
    exists_local_sheets f hdim hUa hUa' hUreg hVreg rfl P w hw
  have hregU : (U : Set (UnderlyingSpace ℂ W)) ⊆ regularPart ℂ W := fun p hp ↦
    (mem_regularPart_iff _).2 (hUreg (hW₀U _ (hUW₀ p hp)))
  refine ⟨U, hUc, hwU, hUW₀, hregU, fun i ↦ Ui (Fin.cast hdeg.symm i),
    fun i j hij ↦ hdisj fun h ↦ hij (Fin.cast_injective _ h), ?_, fun i p hp ↦ ?_,
    fun n hn ↦ ⟨(hrest n hn).1, fun i ↦ (hrest n hn).2 _⟩⟩
  · rw [hpre]
    exact ((finCongr hdeg.symm).surjective.iUnion_comp
      fun i ↦ (Ui i : Set (UnderlyingSpace ℂ V))).symm
  · have hfp : p ∈ mapFun f ⁻¹' U := (Set.ext_iff.1 hpre p).2 (Set.mem_iUnion.2 ⟨_, hp⟩)
    exact (mem_regularPart_iff _).2 (hVreg (hW₀U _ (hUW₀ _ hfp)))

end GenericCovering

end MMP
