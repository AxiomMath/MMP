module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Analytic.Analytification
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Comparison
import MMP.Analysis.Complex.Coherent.OkaCartanBlocks
import MMP.Analysis.Complex.Coherent.CartanBlocksGluing
import MMP.Analysis.Complex.Coherent.Basic
import MMP.AlgebraicGeometry.Analytic.GAGA.DolbeaultVanishing
import MMP.Analysis.Complex.CauchyTransformRungeMontel
import MMP.AlgebraicGeometry.Analytic.GAGA.TwistsCechComparison
import MMP.Analysis.Complex.Coherent.MatrixMapsSubmanifolds
import MMP.Analysis.Complex.HolomorphicCompactConvergence
import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.FlasqueAlternatingVanishing
import MMP.Topology.Sheaves.GodementFlasqueResolution
import MMP.Analysis.Complex.Coherent.OkaInduction

/-!
# Cartan–Serre finiteness on complex projective space

Let `P = ℙᴺ_ℂ` and `P^an` its analytification. There is an integer `m`, depending only on `N`,
such that for every coherent analytic sheaf `𝒮` on `P^an` every cohomology group
`H^q(P^an, 𝒮)` is a finite-dimensional complex vector space, and `H^q(P^an, 𝒮) = 0` for
`q ≥ m`; one may take `m = N + 1`.

The proof follows Cartan–Serre. The standard charts `U_j ≅ ℂᴺ` of `ℙᴺ` carry concentric boxes
of half-side `r`; the sets `V^{(r)}_j ⊆ U_j` they define cover `P^an` for `r > 1`, and every
finite intersection of them is, in the coordinates of its first chart, an open set `Ω ⊆ ℂᴺ`
which is the projection of a closed complex submanifold of a box (the graph of the coordinate
changes). Cartan's Theorem B on boxes therefore kills the higher cohomology of every coherent
sheaf on these intersections, and Leray's theorem computes `H^q(P^an, 𝒮)` by the ordered Čech
complex of each cover. As the cover has `N + 1` members, the cohomology vanishes in degrees
`≥ N + 1`. Finiteness is Schwartz's theorem applied to Banach spaces of bounded holomorphic
cochains of presentations of `𝒮` on two of the covers: the restriction between them is compact
by Montel's theorem.

## Main results

* `MMP.Analytic.projectiveSpace_finiteDimensional_sheafCohomology`: the theorem above.

## Implementation notes

`H^q(P^an, 𝒮)` is the Godement cohomology `MMP.Analytic.sheafCohomology` of the abelian sheaf
underlying `𝒮`, an abelian group. Its complex structure is the one induced by functoriality from
the scalar multiplications of `𝒮`: a constant `c ∈ ℂ` acts by the endomorphism `φ c` of the
underlying abelian sheaf which on sections over an open `W` multiplies by the restriction to `W`
of the global constant function `c ∈ Γ(P^an, 𝒪)`, the image of `c` under `α_P^#`. Such an
endomorphism is determined by its components, so `φ` is unique; finite dimensionality is stated
as the existence of finitely many classes spanning `H^q(P^an, 𝒮)` under this action.

The covers used are the boxes of half-sides `2, 3, 4, 5` in the `N + 1` standard charts, and
Theorem A near the closed box of half-side `5` gives, for every chart `α`, finitely many sections
`g^α_j` generating `𝒮` near `V^{(5)}_α`. Instead of the quotient Banach spaces `B_{min I}(V_I)`
of the source, a degree-`q` bounded cochain is a family of bounded holomorphic coefficient
vectors, one for the presentation of every index of every ordered tuple `I`; it represents the
Čech cochain `(∑_{k,j} a_{I,k,j} g^{I_k}_j)_I`. With these redundant presentations the Čech
differential is computed by restriction alone, with no transition matrices, and the bounded
cocycles form a closed subspace because relations among the `g^α_j` are closed under uniform
convergence. Schwartz's theorem is applied to the bounded cocycles of `V^{(3)}` and `V^{(4)}` and
the space of pairs `(ξ, c)` with `ξ|_{V^{(2)}} = δ c`.

## References

* [Cartan–Serre, *Un théorème de finitude concernant les variétés analytiques compactes*]
* [Serre, *Géométrie algébrique et géométrie analytique*], §12
-/

namespace MMP.Analytic.ProjectiveFiniteness

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open MMP.Analytic MMP.Analytic.Analytification MMP.Analytic.CoherentAnalytic
open MMP.Analytic.ProjectiveTwists MMP.Analytic.ComplexPoints
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)
open scoped Manifold ContDiff

noncomputable section

attribute [local instance] locallyOfFiniteType_sP MvPolynomial.gradedAlgebra

private lemma opensMap_isContinuous' {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : TopCat.of X ⟶ TopCat.of Y) :
    (Opens.map f).IsContinuous (Opens.grothendieckTopology (TopCat.of Y))
      (Opens.grothendieckTopology (TopCat.of X)) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreserving_opens_map _)
    (coverPreserving_opens_map _)

attribute [local instance] opensMap_isContinuous'

section Transport

/-! A transport datum: a functor `F : Opens T' ⥤ Opens T` along a continuous map `e : T' ⟶ T`
with `e(V) ⊆ F(V)` and `F(e⁻¹ U ∩ V) ⊆ U`, and a morphism of sheaves of rings `A' ⟶ F_* A` which is
bijective on sections. -/

variable {T T' : TopCat.{0}} (e : T' ⟶ T) (F : Opens T' ⥤ Opens T)
  (hF₁ : ∀ (V : Opens T') (x : T'), x ∈ V → e x ∈ F.obj V)
  (hF₂ : ∀ (U : Opens T) (V : Opens T'), F.obj ((Opens.map e).obj U ⊓ V) ≤ U)
  {A : Sheaf (Opens.grothendieckTopology T) RingCat.{0}}
  {A' : Sheaf (Opens.grothendieckTopology T') RingCat.{0}}
  [F.IsContinuous (Opens.grothendieckTopology T') (Opens.grothendieckTopology T)]
  (ψ : A' ⟶ (F.sheafPushforwardContinuous RingCat.{0}
      (Opens.grothendieckTopology T') (Opens.grothendieckTopology T)).obj A)

/-- The ring map `A'(V) → A(F V)` of a transport datum. -/
private noncomputable abbrev ψa (V : Opens T') :
    A'.obj.obj (op V) →+* A.obj.obj (op (F.obj V)) :=
  (ψ.hom.app (op V)).hom

private lemma fmono {V V' : Opens T'} (h : V' ≤ V) : F.obj V' ≤ F.obj V :=
  leOfHom (F.map (homOfLE h))

private lemma ψa_res {V V' : Opens T'} (h : V' ≤ V) (a : A'.obj.obj (op V)) :
    ψa F ψ V' (resA h a) = resA (fmono F h) (ψa F ψ V a) :=
  ConcreteCategory.congr_hom (ψ.hom.naturality (homOfLE h).op) a

include hF₁ hF₂ in
private lemma locallyGenerates_pushforward (hψ : ∀ V, Function.Surjective (ψa F ψ V))
    {M : SheafOfModules.{0} A} {W : Opens T} {m : ℕ} {g : Fin m → M.val.obj (op W)}
    (hg : LocallyGenerates M g) {W' : Opens T'} (hW : F.obj W' ≤ W) :
    LocallyGenerates ((SheafOfModules.pushforward ψ).obj M)
      (fun k => (show ((SheafOfModules.pushforward ψ).obj M).val.obj (op W') from
        resM M hW (g k))) := by
  refine locallyGenerates_of_nhds _ fun U' hU' t y' hy' => ?_
  obtain ⟨t, rfl⟩ : ∃ t₀ : M.val.obj (op (F.obj U')), t₀ = t := ⟨t, rfl⟩
  have hUW : F.obj U' ≤ W := (fmono F hU').trans hW
  obtain ⟨U₁, h₁, hy₁, c, hc⟩ := hg.exists_nhds hUW t (y := e y') (hF₁ U' y' hy')
  let U₁' : Opens T' := (Opens.map e).obj U₁ ⊓ U'
  have hU₁ : F.obj U₁' ≤ U₁ := hF₂ U₁ U'
  refine ⟨U₁', inf_le_right, ⟨hy₁, hy'⟩,
    fun k => Function.surjInv (hψ U₁') (resA hU₁ (c k)), ?_⟩
  show resM M (fmono F (inf_le_right : U₁' ≤ U')) t = ∑ k, ψa F ψ U₁'
    (Function.surjInv (hψ U₁') (resA hU₁ (c k))) •
      resM M (fmono F ((inf_le_right : U₁' ≤ U').trans hU')) (resM M hW (g k))
  simp only [Function.surjInv_eq]
  have e1 : resM M (fmono F (inf_le_right : U₁' ≤ U')) t =
      resM M hU₁ (resM M h₁ t) := by rw [resM_resM]
  rw [e1, hc, resM_sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [resM_resM, resM_resM]

include hF₁ hF₂ in
private lemma finGen_pushforward (hψ : ∀ V, Function.Surjective (ψa F ψ V))
    {M : SheafOfModules.{0} A} (hM : FinGen M) : FinGen ((SheafOfModules.pushforward ψ).obj M) := by
  intro x'
  obtain ⟨W, hxW, m, g, hg⟩ := hM (e x')
  exact ⟨(Opens.map e).obj W ⊓ ⊤, ⟨hxW, trivial⟩, m, _,
    locallyGenerates_pushforward e F hF₁ hF₂ ψ hψ hg (hF₂ W ⊤)⟩

include hF₁ hF₂ in
private lemma relFin_pushforward (hψ : ∀ V, Function.Bijective (ψa F ψ V))
    {M : SheafOfModules.{0} A} (hM : RelFin M) : RelFin ((SheafOfModules.pushforward ψ).obj M) := by
  intro V' p f x' hx'
  obtain ⟨f, rfl⟩ : ∃ f₀ : Fin p → M.val.obj (op (F.obj V')), f₀ = f := ⟨f, rfl⟩
  obtain ⟨W, hWV, hxW, s, r, hr, hgen⟩ := hM (F.obj V') p f (e x') (hF₁ V' x' hx')
  let W' : Opens T' := (Opens.map e).obj W ⊓ V'
  have hW'W : F.obj W' ≤ W := hF₂ W V'
  let r' : Fin s → Fin p → A'.obj.obj (op W') := fun k j =>
    Function.surjInv (hψ W').2 (resA hW'W (r k j))
  have hr' : ∀ k j, ψa F ψ W' (r' k j) = resA hW'W (r k j) := fun k j =>
    Function.surjInv_eq (hψ W').2 _
  refine ⟨W', inf_le_right, ⟨hxW, hx'⟩, s, r', fun k => ?_, ?_⟩
  · show ∑ j, ψa F ψ W' (r' k j) • resM M (fmono F (inf_le_right : W' ≤ V')) (f j) = 0
    simp only [hr']
    have : ∀ j, resM M (fmono F (inf_le_right : W' ≤ V')) (f j) =
        resM M hW'W (resM M hWV (f j)) := fun j => by rw [resM_resM]
    simp only [this, ← resM_sum_smul, hr k, resM_zero]
  · intro U' hUW a ha y' hy'
    have ha' : ∑ j, ψa F ψ U' (a j) • resM M ((fmono F hUW).trans hW'W |>.trans hWV) (f j) = 0 :=
      ha
    obtain ⟨U₁, h₁, hy₁, c, hc⟩ := hgen (F.obj U') ((fmono F hUW).trans hW'W)
      (fun j => ψa F ψ U' (a j)) ha' (e y') (hF₁ U' y' hy')
    let U₁' : Opens T' := (Opens.map e).obj U₁ ⊓ U'
    have hU₁ : F.obj U₁' ≤ U₁ := hF₂ U₁ U'
    let c' : Fin s → A'.obj.obj (op U₁') := fun k => Function.surjInv (hψ U₁').2 (resA hU₁ (c k))
    refine ⟨U₁', inf_le_right, ⟨hy₁, hy'⟩, c', fun j => (hψ U₁').1 ?_⟩
    rw [ψa_res, map_sum]
    simp only [map_mul, ψa_res, c', Function.surjInv_eq, hr']
    have e1 : resA (fmono F (inf_le_right : U₁' ≤ U')) (ψa F ψ U' (a j)) =
        resA hU₁ (resA h₁ (ψa F ψ U' (a j))) := by rw [resA_resA]
    rw [e1, hc j, resA_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [resA_mul, resA_resA, resA_resA]

include hF₁ hF₂ in
/-- **Coherence is transported** along a transport datum. -/
private theorem isCoherentModule_pushforward (hψ : ∀ V, Function.Bijective (ψa F ψ V))
    {M : SheafOfModules.{0} A} (hM : IsCoherentModule M) :
    IsCoherentModule ((SheafOfModules.pushforward ψ).obj M) :=
  isCoherentModule_of_finGen_of_relFin
    (finGen_pushforward e F hF₁ hF₂ ψ (fun V => (hψ V).2) ((isFiniteType_iff_finGen M).1 hM.1))
    (relFin_pushforward e F hF₁ hF₂ ψ hψ (relFin_of_isCoherentModule hM))

end Transport

variable {n r : ℕ}

/-- The first `n` coordinates of a point of `ℂ^{n+r}`. -/
private def prL : EuclideanSpace ℂ (Fin (n + r)) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℂ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => EuclideanSpace.proj (Fin.castAdd r i))

/-- The last `r` coordinates of a point of `ℂ^{n+r}`. -/
private def sndL : EuclideanSpace ℂ (Fin (n + r)) →L[ℂ] EuclideanSpace ℂ (Fin r) :=
  (EuclideanSpace.equiv (Fin r) ℂ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => EuclideanSpace.proj (Fin.natAdd n i))

/-- The point of `ℂ^{n+r}` with coordinates `(w, u)`. -/
private def joinL : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin r) →L[ℂ]
    EuclideanSpace ℂ (Fin (n + r)) :=
  (EuclideanSpace.equiv (Fin (n + r)) ℂ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => Fin.addCases
      (fun k => (EuclideanSpace.proj k).comp (ContinuousLinearMap.fst ℂ _ _))
      (fun k => (EuclideanSpace.proj k).comp (ContinuousLinearMap.snd ℂ _ _)) i)

private abbrev join (w : EuclideanSpace ℂ (Fin n)) (u : EuclideanSpace ℂ (Fin r)) :
    EuclideanSpace ℂ (Fin (n + r)) := joinL (w, u)

private lemma prL_apply (y : EuclideanSpace ℂ (Fin (n + r))) (i : Fin n) :
    prL y i = y (Fin.castAdd r i) := rfl

private lemma sndL_apply (y : EuclideanSpace ℂ (Fin (n + r))) (i : Fin r) :
    sndL y i = y (Fin.natAdd n i) := rfl

private lemma join_castAdd (w : EuclideanSpace ℂ (Fin n)) (u : EuclideanSpace ℂ (Fin r))
    (i : Fin n) : join w u (Fin.castAdd r i) = w i := by
  simp [join, joinL]

private lemma join_natAdd (w : EuclideanSpace ℂ (Fin n)) (u : EuclideanSpace ℂ (Fin r))
    (i : Fin r) : join w u (Fin.natAdd n i) = u i := by
  simp [join, joinL]

private lemma prL_join (w : EuclideanSpace ℂ (Fin n)) (u : EuclideanSpace ℂ (Fin r)) :
    prL (join w u) = w := by ext i; simp [prL_apply, join_castAdd]

private lemma sndL_join (w : EuclideanSpace ℂ (Fin n)) (u : EuclideanSpace ℂ (Fin r)) :
    sndL (join w u) = u := by ext i; simp [sndL_apply, join_natAdd]

private lemma join_prL_sndL (y : EuclideanSpace ℂ (Fin (n + r))) :
    join (prL y) (sndL y) = y := by
  ext i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;>
    simp [join_castAdd, join_natAdd, prL_apply, sndL_apply]

attribute [local simp] prL_apply sndL_apply join_castAdd join_natAdd prL_join sndL_join
  join_prL_sndL

section Graph

variable (Ω : Opens (EuclideanSpace ℂ (Fin n)))
  (g : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin r))

/-- `(w, u) ↦ (w, u - g w)`, flattening the graph of `g`. -/
private def graphFwd (y : EuclideanSpace ℂ (Fin (n + r))) : EuclideanSpace ℂ (Fin (n + r)) :=
  join (prL y) (sndL y - g (prL y))

/-- `(w, v) ↦ (w, v + g w)`, the inverse of `graphFwd`. -/
private def graphBwd (v : EuclideanSpace ℂ (Fin (n + r))) : EuclideanSpace ℂ (Fin (n + r)) :=
  join (prL v) (sndL v + g (prL v))

private lemma prL_graphFwd (y : EuclideanSpace ℂ (Fin (n + r))) : prL (graphFwd g y) = prL y := by
  simp [graphFwd]

private lemma prL_graphBwd (v : EuclideanSpace ℂ (Fin (n + r))) : prL (graphBwd g v) = prL v := by
  simp [graphBwd]

private lemma graphBwd_graphFwd (y : EuclideanSpace ℂ (Fin (n + r))) :
    graphBwd g (graphFwd g y) = y := by
  simp [graphBwd, graphFwd]

private lemma graphFwd_graphBwd (v : EuclideanSpace ℂ (Fin (n + r))) :
    graphFwd g (graphBwd g v) = v := by
  simp [graphBwd, graphFwd]

variable {Ω g}

/-- A map into `ℂʳ` whose coordinates are holomorphic on `Ω` is smooth on `Ω`. -/
private lemma contDiffOn_of_differentiableOn_coord
    (hg : ∀ i, DifferentiableOn ℂ (fun w => g w i) Ω) : ContDiffOn ℂ ∞ g Ω :=
  contDiffOn_piLp' 2 fun i =>
    (analyticOnNhd_of_differentiableOn Ω.isOpen (hg i)).contDiffOn Ω.isOpen.uniqueDiffOn

private lemma contDiffOn_comp_prL (hg : ∀ i, DifferentiableOn ℂ (fun w => g w i) Ω) :
    ContDiffOn ℂ ∞ (fun y : EuclideanSpace ℂ (Fin (n + r)) => g (prL y)) (prL ⁻¹' Ω) :=
  (contDiffOn_of_differentiableOn_coord hg).comp prL.contDiff.contDiffOn fun _ hy => hy

private lemma contDiffOn_graphFwd (hg : ∀ i, DifferentiableOn ℂ (fun w => g w i) Ω) :
    ContDiffOn ℂ ∞ (graphFwd g) (prL ⁻¹' Ω) :=
  joinL.contDiff.comp_contDiffOn (prL.contDiff.contDiffOn.prodMk
    (sndL.contDiff.contDiffOn.sub (contDiffOn_comp_prL hg)))

private lemma contDiffOn_graphBwd (hg : ∀ i, DifferentiableOn ℂ (fun w => g w i) Ω) :
    ContDiffOn ℂ ∞ (graphBwd g) (prL ⁻¹' Ω) :=
  joinL.contDiff.comp_contDiffOn (prL.contDiff.contDiffOn.prodMk
    (sndL.contDiff.contDiffOn.add (contDiffOn_comp_prL hg)))

variable (hg : ∀ i, DifferentiableOn ℂ (fun w => g w i) Ω)
  (D : Opens (EuclideanSpace ℂ (Fin (n + r))))

open Classical

/-- The chart of `D` flattening the graph of `g`. -/
private def flatChart (x₀ : D) : OpenPartialHomeomorph D (EuclideanSpace ℂ (Fin (n + r))) where
  toFun y := graphFwd g y.1
  invFun v := if h : graphBwd g v ∈ D then ⟨graphBwd g v, h⟩ else x₀
  source := {y | prL y.1 ∈ Ω}
  target := {v | prL v ∈ Ω ∧ graphBwd g v ∈ D}
  map_source' y hy := ⟨by show prL (graphFwd g y.1) ∈ Ω; rw [prL_graphFwd]; exact hy,
    by rw [graphBwd_graphFwd]; exact y.2⟩
  map_target' v hv := by
    simp only [Set.mem_setOf_eq, dif_pos hv.2, prL_graphBwd]; exact hv.1
  left_inv' y hy := by
    rw [dif_pos (by rw [graphBwd_graphFwd]; exact y.2)]
    exact Subtype.ext (graphBwd_graphFwd g y.1)
  right_inv' v hv := by
    simp only [dif_pos hv.2, graphFwd_graphBwd]
  open_source := Ω.isOpen.preimage (prL.continuous.comp continuous_subtype_val)
  open_target := (contDiffOn_graphBwd hg).continuousOn.isOpen_inter_preimage
    (Ω.isOpen.preimage prL.continuous) D.isOpen
  continuousOn_toFun := (contDiffOn_graphFwd hg).continuousOn.comp
    continuous_subtype_val.continuousOn (fun _ hy => hy)
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine ((contDiffOn_graphBwd hg).continuousOn.mono fun v hv => hv.1).congr fun v hv => ?_
    simp only [Function.comp_apply, dif_pos hv.2]

private lemma flatChart_symm_coe (x₀ : D) (v : EuclideanSpace ℂ (Fin (n + r)))
    (hv : graphBwd g v ∈ D) :
    (((flatChart hg D x₀).symm v : D) : EuclideanSpace ℂ (Fin (n + r))) = graphBwd g v := by
  show ((if h : graphBwd g v ∈ D then (⟨graphBwd g v, h⟩ : D) else x₀) : D).1 = _
  rw [dif_pos hv]

private lemma flatChart_mem_maximalAtlas (x₀ : D) :
    flatChart hg D x₀ ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin (n + r))) ∞ D := by
  refine OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn _ ?_ ?_
  · exact (contMDiffOn_iff_contDiffOn.2 (contDiffOn_graphFwd hg)).comp
      contMDiff_subtype_val.contMDiffOn (fun _ hy => hy)
  · intro v hv
    rw [← ContMDiffWithinAt.subtypeVal_comp_iff]
    refine (((contMDiffOn_iff_contDiffOn.2 (contDiffOn_graphBwd hg)).mono
      fun v hv => hv.1) v hv).congr (fun v' hv' => ?_) ?_
    · exact flatChart_symm_coe hg D x₀ v' hv'.2
    · exact flatChart_symm_coe hg D x₀ v hv.2

variable (Ω g) in
/-- The graph of `g` over `Ω`, inside `D`. -/
private def graphSet : Set D := {y | prL y.1 ∈ Ω ∧ sndL y.1 = g (prL y.1)}

private lemma forall_ge_eq_zero_iff (v : EuclideanSpace ℂ (Fin (n + r))) :
    (∀ i : Fin (n + r), n ≤ (i : ℕ) → v i = 0) ↔ sndL v = 0 := by
  constructor
  · intro h
    ext k
    rw [sndL_apply]
    exact h _ (by simp)
  · intro h i hi
    induction i using Fin.addCases with
    | left k => exact absurd hi (by simp)
    | right k =>
      simpa [sndL_apply] using congrArg (fun u : EuclideanSpace ℂ (Fin r) => u k) h

private lemma flatChart_image (x₀ : D) :
    flatChart hg D x₀ '' (graphSet Ω g D ∩ (flatChart hg D x₀).source) =
      (flatChart hg D x₀).target ∩ {v | ∀ i : Fin (n + r), n ≤ (i : ℕ) → v i = 0} := by
  ext v
  simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq, forall_ge_eq_zero_iff]
  constructor
  · rintro ⟨y, ⟨⟨hyΩ, hyg⟩, -⟩, rfl⟩
    refine ⟨(flatChart hg D x₀).map_source hyΩ, ?_⟩
    change sndL (graphFwd g y.1) = 0
    simp [graphFwd, hyg]
  · rintro ⟨hv, hv0⟩
    refine ⟨⟨graphBwd g v, hv.2⟩, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [prL_graphBwd]; exact hv.1
    · simp [graphBwd, hv0]
    · change prL (graphBwd g v) ∈ Ω
      rw [prL_graphBwd]; exact hv.1
    · exact graphFwd_graphBwd g v

include hg in
private lemma isClosedComplexSubmanifold_graphSet (hcl : IsClosed (graphSet Ω g D)) :
    IsClosedComplexSubmanifold (n + r) (graphSet Ω g D) :=
  ⟨hcl, fun x hx => ⟨flatChart hg D x, flatChart_mem_maximalAtlas hg D x, hx.1, n,
    flatChart_image hg D x⟩⟩

variable (Ω g) in
/-- The hypotheses on a graph: `g` is holomorphic on `Ω` and its graph lies in `D`. -/
private structure GraphHyp : Type where
  hg : ∀ i, DifferentiableOn ℂ (fun w => g w i) Ω
  hD : ∀ w ∈ Ω, join w (g w) ∈ D

section Proj

variable (H : GraphHyp Ω g D)

/-- The point of the graph over `w ∈ Ω`. -/
private def graphPt (w : Ω) : graphSet Ω g D :=
  ⟨⟨join w.1 (g w.1), H.hD w.1 w.2⟩, by
    show prL (join w.1 (g w.1)) ∈ Ω ∧ sndL (join w.1 (g w.1)) = g (prL (join w.1 (g w.1)))
    rw [prL_join, sndL_join]; exact ⟨w.2, rfl⟩⟩

/-- The projection of the graph onto `Ω`. -/
private def graphProj : TopCat.of (graphSet Ω g D) ⟶ TopCat.of Ω :=
  TopCat.ofHom ⟨fun z => ⟨prL z.1.1, z.2.1⟩,
    (prL.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _⟩

private lemma graphProj_graphPt (w : Ω) : graphProj D (graphPt D H w) = w :=
  Subtype.ext (prL_join _ _)

private lemma graphPt_graphProj (z : graphSet Ω g D) : graphPt D H (graphProj D z) = z := by
  apply Subtype.ext; apply Subtype.ext
  change join (prL z.1.1) (g (prL z.1.1)) = z.1.1
  rw [← z.2.2, join_prL_sndL]

include H in
private lemma continuous_graphPt : Continuous (graphPt D H) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  exact joinL.continuous.comp (continuous_subtype_val.prodMk
    ((contDiffOn_of_differentiableOn_coord H.hg).continuousOn.comp_continuous
      continuous_subtype_val fun w => w.2))

/-- The projection is a homeomorphism of the graph onto `Ω`. -/
private def graphHomeo : graphSet Ω g D ≃ₜ Ω where
  toFun := graphProj D
  invFun := graphPt D H
  left_inv := graphPt_graphProj D H
  right_inv := graphProj_graphPt D H
  continuous_toFun := (graphProj D).hom.continuous
  continuous_invFun := continuous_graphPt D H

/-- The inverse of the projection, as a morphism of spaces. -/
private def graphInv : TopCat.of Ω ⟶ TopCat.of (graphSet Ω g D) :=
  TopCat.ofHom ⟨graphPt D H, continuous_graphPt D H⟩

variable (W : Opens (TopCat.of (graphSet Ω g D)))

private lemma graphPt_mem_of_mem (x : (Opens.map (graphInv D H)).obj W) :
    graphPt D H x.1 ∈ W := x.2

private lemma graphProj_mem_of_mem (z : W) :
    graphProj D z.1 ∈ (Opens.map (graphInv D H)).obj W := by
  change graphPt D H (graphProj D z.1) ∈ W
  rw [graphPt_graphProj]; exact z.2

/-- The graph map `w ↦ (w, g w)`. -/
private abbrev graphMap (w : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin (n + r)) :=
  join w (g w)

include hg in
private lemma differentiableAt_graphMap {w : EuclideanSpace ℂ (Fin n)} (hw : w ∈ Ω) :
    DifferentiableAt ℂ (graphMap (g := g)) w :=
  joinL.differentiableAt.comp w (differentiableAt_id.prodMk
    (((contDiffOn_of_differentiableOn_coord hg).differentiableOn (by simp)).differentiableAt
      (Ω.isOpen.mem_nhds hw)))

/-- A function on the graph, read on `Ω`. -/
private def restrFun (f : restrictedSubring (n + r) (graphSet Ω g D) W) :
    (Opens.map (graphInv D H)).obj W → ℂ :=
  fun x => f.1 ⟨graphPt D H x.1, graphPt_mem_of_mem D H W x⟩

private lemma contMDiff_restrFun (f : restrictedSubring (n + r) (graphSet Ω g D) W) :
    ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ (restrFun D H W f) := by
  rw [MMP.Analytic.contMDiff_iff_differentiableOn_extend]
  rintro _ ⟨x, rfl⟩
  obtain ⟨U, hxU, G, hG⟩ := f.2 ⟨graphPt D H x.1, graphPt_mem_of_mem D H W x⟩
  let Gext := Function.extend (MMP.Analytic.openInclusion (D := D) U) G 0
  have hGd : DifferentiableOn ℂ Gext (Set.range (MMP.Analytic.openInclusion (D := D) U)) :=
    (MMP.Analytic.contMDiff_iff_differentiableOn_extend (D := D) U G).1 G.2
  have hUo : IsOpen (Set.range (MMP.Analytic.openInclusion (D := D) U)) :=
    (MMP.Analytic.isOpenEmbedding_openInclusion (D := D) U).isOpen_range
  have hx0 : graphMap (g := g) (MMP.Analytic.openInclusion _ x) ∈
      Set.range (MMP.Analytic.openInclusion (D := D) U) := ⟨⟨_, hxU⟩, rfl⟩
  have hd : DifferentiableAt ℂ (Gext ∘ graphMap (g := g)) (MMP.Analytic.openInclusion _ x) :=
    (hGd.differentiableAt (hUo.mem_nhds hx0)).comp _
      (differentiableAt_graphMap H.hg (x.1.2))
  refine hd.differentiableWithinAt.congr_of_eventuallyEq ?_ ?_
  · have hev : ∀ᶠ w in nhds (MMP.Analytic.openInclusion _ x),
        graphMap (g := g) w ∈ Set.range (MMP.Analytic.openInclusion (D := D) U) :=
      (differentiableAt_graphMap H.hg x.1.2).continuousAt.preimage_mem_nhds (hUo.mem_nhds hx0)
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with w hw hwr
    obtain ⟨x', rfl⟩ := hwr
    rw [(MMP.Analytic.isOpenEmbedding_openInclusion _).injective.extend_apply]
    obtain ⟨u, hu⟩ := hw
    have hmem : ((⟨graphPt D H x'.1, graphPt_mem_of_mem D H W x'⟩ : W) : graphSet Ω g D).1
        ∈ U := by
      have : (u : D) = (graphPt D H x'.1).1 := Subtype.ext hu
      rw [← this]; exact u.2
    change f.1 ⟨graphPt D H x'.1, graphPt_mem_of_mem D H W x'⟩ = _
    rw [hG _ hmem]
    exact ((MMP.Analytic.isOpenEmbedding_openInclusion (D := D) U).injective.extend_apply
      (G : U → ℂ) 0 ⟨_, hmem⟩).symm
  · rw [(MMP.Analytic.isOpenEmbedding_openInclusion _).injective.extend_apply,
      Function.comp_apply]
    change f.1 ⟨graphPt D H x.1, graphPt_mem_of_mem D H W x⟩ = _
    rw [hG _ hxU]
    exact ((MMP.Analytic.isOpenEmbedding_openInclusion (D := D) U).injective.extend_apply
      (G : U → ℂ) 0 ⟨_, hxU⟩).symm

/-- Functions on the graph which are locally restrictions of holomorphic functions, read on `Ω`. -/
private def restrToHol : restrictedSubring (n + r) (graphSet Ω g D) W →+*
    𝒪[n, Ω].presheaf.obj (op ((Opens.map (graphInv D H)).obj W)) where
  toFun f := ⟨restrFun D H W f, contMDiff_restrFun D H W f⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private lemma restrToHol_bijective : Function.Bijective (restrToHol D H W) := by
  refine ⟨fun f f' h => Subtype.ext (funext fun z => ?_), fun h => ?_⟩
  · have e := congrArg (fun F : 𝒪[n, Ω].presheaf.obj
        (op ((Opens.map (graphInv D H)).obj W)) =>
      (F : _ → ℂ) ⟨graphProj D z.1, graphProj_mem_of_mem D H W z⟩) h
    change f.1 ⟨graphPt D H (graphProj D z.1), _⟩ = f'.1 ⟨graphPt D H (graphProj D z.1), _⟩ at e
    have hz : (⟨graphPt D H (graphProj D z.1), graphPt_mem_of_mem D H W
        ⟨graphProj D z.1, graphProj_mem_of_mem D H W z⟩⟩ : W) = z :=
      Subtype.ext (graphPt_graphProj D H z.1)
    rwa [hz] at e
  · let FW := (Opens.map (graphInv D H)).obj W
    let hext := Function.extend (MMP.Analytic.openInclusion (D := Ω) FW) (h : FW → ℂ) 0
    have hhd : DifferentiableOn ℂ hext (Set.range (MMP.Analytic.openInclusion (D := Ω) FW)) :=
      (MMP.Analytic.contMDiff_iff_differentiableOn_extend (D := Ω) FW h).1 h.2
    have hFo : IsOpen (Set.range (MMP.Analytic.openInclusion (D := Ω) FW)) :=
      (MMP.Analytic.isOpenEmbedding_openInclusion (D := Ω) FW).isOpen_range
    let U : Opens D := ⟨{y : D | prL y.1 ∈ Set.range (MMP.Analytic.openInclusion (D := Ω) FW)},
      hFo.preimage (prL.continuous.comp continuous_subtype_val)⟩
    let G : U → ℂ := fun y => hext (prL y.1.1)
    have hG : ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin (n + r))) 𝓘(ℂ) ∞ G := by
      rw [MMP.Analytic.contMDiff_iff_differentiableOn_extend (D := D) U G]
      refine ((hhd.comp prL.differentiableOn (fun y hy => ?_))).congr fun y hy => ?_
      · obtain ⟨u, rfl⟩ := hy; exact u.2
      · obtain ⟨u, rfl⟩ := hy
        exact (MMP.Analytic.isOpenEmbedding_openInclusion (D := D) U).injective.extend_apply G 0 u
    let f : W → ℂ := fun z => h ⟨graphProj D z.1, graphProj_mem_of_mem D H W z⟩
    have hf : f ∈ restrictedSubring (n + r) (graphSet Ω g D) W := by
      intro w
      refine ⟨U, ⟨⟨graphProj D w.1, graphProj_mem_of_mem D H W w⟩, rfl⟩, ⟨G, hG⟩,
        fun v hv => ?_⟩
      change h ⟨graphProj D v.1, graphProj_mem_of_mem D H W v⟩ = hext (prL v.1.1.1)
      exact ((MMP.Analytic.isOpenEmbedding_openInclusion (D := Ω) FW).injective.extend_apply
        (h : FW → ℂ) 0 ⟨graphProj D v.1, graphProj_mem_of_mem D H W v⟩).symm
    refine ⟨⟨f, hf⟩, ContMDiffMap.ext fun x => ?_⟩
    change h ⟨graphProj D (graphPt D H x.1), _⟩ = h x
    have hx : (⟨graphProj D (graphPt D H x.1), graphProj_mem_of_mem D H W
        ⟨_, graphPt_mem_of_mem D H W x⟩⟩ : FW) = x :=
      Subtype.ext (graphProj_graphPt D H x.1)
    rw [hx]

/-- The functions locally restricted from `D`, read on `Ω`, as a morphism of sheaves of rings. -/
private def restrToHolHom :
    (sheafCompose _ (forget₂ CommRingCat RingCat.{0})).obj
        (restrictedSheaf (n + r) (graphSet Ω g D)) ⟶
      ((Opens.map (graphInv D H)).sheafPushforwardContinuous RingCat.{0}
        (Opens.grothendieckTopology (TopCat.of (graphSet Ω g D)))
        (Opens.grothendieckTopology (TopCat.of Ω))).obj (holomorphicRingCatSheaf n Ω) where
  hom :=
    { app := fun W => RingCat.ofHom (restrToHol D H W.unop)
      naturality := fun _ _ _ => by ext; rfl }

/-- The structure sheaf of the graph, read on `Ω`. -/
private def graphψ :
    (sheafCompose _ (forget₂ CommRingCat RingCat.{0})).obj
        (submanifoldStructureSheaf (n + r) (graphSet Ω g D)) ⟶
      ((Opens.map (graphInv D H)).sheafPushforwardContinuous RingCat.{0}
        (Opens.grothendieckTopology (TopCat.of (graphSet Ω g D)))
        (Opens.grothendieckTopology (TopCat.of Ω))).obj (holomorphicRingCatSheaf n Ω) :=
  (sheafCompose _ (forget₂ CommRingCat RingCat.{0})).map
    (structureSheafToRestricted (n + r) (graphSet Ω g D)) ≫ restrToHolHom D H

private lemma graphψ_bijective (hcl : IsClosed (graphSet Ω g D))
    (W : Opens (TopCat.of (graphSet Ω g D))) :
    Function.Bijective ((graphψ D H).hom.app (op W)).hom := by
  have h0 : IsIso (C := Sheaf (Opens.grothendieckTopology (TopCat.of (graphSet Ω g D)))
      CommRingCat.{0}) (structureSheafToRestricted (n + r) (graphSet Ω g D)) :=
    isIso_structureSheafToRestricted (n := n + r) (graphSet Ω g D) hcl
  have h1 : IsIso ((sheafCompose _ (forget₂ CommRingCat RingCat.{0})).map
      (structureSheafToRestricted (n + r) (graphSet Ω g D))) := Functor.map_isIso _ _
  have h2 : IsIso ((sheafToPresheaf _ _).map ((sheafCompose _ (forget₂ CommRingCat RingCat.{0})).map
      (structureSheafToRestricted (n + r) (graphSet Ω g D)))) := Functor.map_isIso _ _
  have h3 : IsIso (((sheafCompose _ (forget₂ CommRingCat RingCat.{0})).map
      (structureSheafToRestricted (n + r) (graphSet Ω g D))).hom.app (op W)) :=
    NatIso.isIso_app_of_isIso _ _
  have h4 := ConcreteCategory.bijective_of_isIso
    (((sheafCompose _ (forget₂ CommRingCat RingCat.{0})).map
      (structureSheafToRestricted (n + r) (graphSet Ω g D))).hom.app (op W))
  exact (restrToHol_bijective D H W).comp h4

end Proj

/-- **Cartan's Theorem B on a graph domain.** If `Ω ⊆ ℂⁿ` is the projection of the graph of a
holomorphic map `g : Ω → ℂʳ`, closed in a box `D ⊆ ℂ^{n+r}`, every coherent `𝒪_Ω`-module has
vanishing higher cohomology. -/
private theorem isZero_sheafCohomology_of_graph (a b c d : Fin (n + r) → ℝ)
    (D : Opens (EuclideanSpace ℂ (Fin (n + r))))
    (hDbox : (D : Set (EuclideanSpace ℂ (Fin (n + r)))) =
      {z | ∀ i, z i ∈ Set.Ioo (a i) (b i) ×ℂ Set.Ioo (c i) (d i)})
    (hg : ∀ i, DifferentiableOn ℂ (fun w => g w i) Ω) (hD : ∀ w ∈ Ω, join w (g w) ∈ D)
    (hcl : IsClosed (graphSet Ω g D))
    (M : SheafOfModules.{0} (holomorphicRingCatSheaf n Ω)) (hM : IsCoherentModule M)
    (q : ℤ) (hq : 1 ≤ q) :
    IsZero ((sheafCohomology (TopCat.of Ω) q).obj ((SheafOfModules.toSheaf _).obj M)) := by
  let H : GraphHyp Ω g D := ⟨hg, hD⟩
  have hF₁ : ∀ (V : Opens (TopCat.of (graphSet Ω g D))) (x : graphSet Ω g D), x ∈ V →
      graphProj D x ∈ (Opens.map (graphInv D H)).obj V := fun V x hx => by
    change graphPt D H (graphProj D x) ∈ V
    rwa [graphPt_graphProj]
  have hF₂ : ∀ (U : Opens (TopCat.of Ω)) (V : Opens (TopCat.of (graphSet Ω g D))),
      (Opens.map (graphInv D H)).obj ((Opens.map (graphProj D)).obj U ⊓ V) ≤ U := by
    intro U V y hy
    have : graphProj D (graphPt D H y) ∈ U := hy.1
    rwa [graphProj_graphPt] at this
  let M' := (SheafOfModules.pushforward (graphψ D H)).obj M
  have hM' : IsCoherentModule M' :=
    isCoherentModule_pushforward (graphProj D) _ hF₁ hF₂ (graphψ D H)
      (graphψ_bijective D H hcl) hM
  have h0 := cartan_theoremB_box a b c d D hDbox (graphSet Ω g D)
    (isClosedComplexSubmanifold_graphSet hg D hcl) M' hM' q hq
  have hinv : Topology.IsOpenEmbedding (graphInv D H) := (graphHomeo D H).symm.isOpenEmbedding
  have h1 : IsIso (sheafCohomologyPullback (graphInv D H)
      ((SheafOfModules.toSheaf _).obj M') q) :=
    CartanCompactBlocks.isIso_sheafCohomologyPullback _ hinv (graphHomeo D H).symm.surjective _ q
  have h2 := isIso_pullbackPushforwardAdjunction_counit (f := graphInv D H) hinv.isInducing
    ((SheafOfModules.toSheaf _).obj M)
  have e1 : (SheafOfModules.toSheaf _).obj M' ≅
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (graphInv D H)).obj
        ((SheafOfModules.toSheaf _).obj M) := Iso.refl _
  refine ((h0.of_iso (asIso (sheafCohomologyPullback (graphInv D H)
      ((SheafOfModules.toSheaf _).obj M') q)).symm).of_iso
    ((sheafCohomology _ q).mapIso ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (graphInv D H)).mapIso
      e1.symm))).of_iso ((sheafCohomology _ q).mapIso
        (asIso ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0}
          (graphInv D H)).counit.app ((SheafOfModules.toSheaf _).obj M))).symm)

end Graph

/-! ### The standard charts of `(ℙᴺ)^an` -/

variable {N : ℕ}

/-- The chart `U_j` of `(ℙᴺ)^an` is homeomorphic to `ℂᴺ` through its affine coordinates. -/
private noncomputable def coordsHomeo (j : Fin (N + 1)) :
    chart (sX := sP N) (stdChart N j).U ≃ₜ (Fin N → ℂ) :=
  (coordsEquiv j).toHomeomorphOfIsInducing
    (isOpenEmbedding_coords (stdChart N j) (stdChart_ideal N j)).isInducing

private lemma coordsHomeo_apply (j : Fin (N + 1)) (y : chart (sX := sP N) (stdChart N j).U) :
    coordsHomeo j y = (stdChart N j).coords y := rfl

/-- The point of `(ℙᴺ)^an` with affine coordinates `w ∈ ℂᴺ` in the chart `U_j`. -/
private noncomputable def chartPt (j : Fin (N + 1)) (w : EuclideanSpace ℂ (Fin N)) :
    ComplexPoints (sP N) :=
  ((coordsHomeo j).symm (EuclideanSpace.equiv (Fin N) ℂ w)).1

private lemma chartPt_mem (j : Fin (N + 1)) (w : EuclideanSpace ℂ (Fin N)) :
    chartPt j w ∈ chart (sX := sP N) (stdChart N j).U :=
  ((coordsHomeo j).symm (EuclideanSpace.equiv (Fin N) ℂ w)).2

private lemma coords_chartPt (j : Fin (N + 1)) (w : EuclideanSpace ℂ (Fin N)) :
    (stdChart N j).coords ⟨chartPt j w, chartPt_mem j w⟩ = EuclideanSpace.equiv (Fin N) ℂ w :=
  (coordsHomeo j).apply_symm_apply _

private lemma isOpenEmbedding_chartPt (j : Fin (N + 1)) :
    Topology.IsOpenEmbedding (chartPt (N := N) j) :=
  ((stdChart N j).isOpen_chart_and_isEmbedding_coords.1.isOpenEmbedding_subtypeVal.comp
    (coordsHomeo j).symm.isOpenEmbedding).comp
    (EuclideanSpace.equiv (Fin N) ℂ).toHomeomorph.isOpenEmbedding

/-- The inclusion of an open `Y ⊆ ℂᴺ` into `(ℙᴺ)^an` as the chart `U_j`. -/
private noncomputable def chartMap (j : Fin (N + 1)) (Y : Opens (EuclideanSpace ℂ (Fin N))) :
    TopCat.of Y ⟶ space (sP N) :=
  TopCat.ofHom ⟨fun y => chartPt j y.1,
    (isOpenEmbedding_chartPt j).continuous.comp continuous_subtype_val⟩

private lemma isOpenEmbedding_chartMap (j : Fin (N + 1)) (Y : Opens (EuclideanSpace ℂ (Fin N))) :
    Topology.IsOpenEmbedding (chartMap j Y) :=
  (isOpenEmbedding_chartPt j).comp Y.isOpen.isOpenEmbedding_subtypeVal

variable (j : Fin (N + 1)) (Y : Opens (EuclideanSpace ℂ (Fin N)))

private lemma mem_chart_of_mem_functor (V : Opens (TopCat.of Y))
    (x : (isOpenEmbedding_chartMap j Y).functor.obj V) :
    x.1 ∈ chart (sX := sP N) (stdChart N j).U := by
  obtain ⟨v, -, hv⟩ := x.2
  rw [← hv]
  exact chartPt_mem j _

/-- The point of `e(V)` with coordinates `v`. -/
private abbrev ptOf (V : Opens (TopCat.of Y)) (v : V) :
    (isOpenEmbedding_chartMap j Y).functor.obj V :=
  ⟨chartPt j v.1.1, ⟨v.1, v.2, rfl⟩⟩

/-- A section of `𝒪_{(ℙᴺ)^an}` over the image of `V`, as a function on `V`. -/
private noncomputable def valFun (V : Opens (TopCat.of Y))
    (s : sections (sP N) ((isOpenEmbedding_chartMap j Y).functor.obj V)) : V → ℂ :=
  fun v => secVal s (ptOf j Y V v) (stdChart N j) (chartPt_mem j _)

private lemma contMDiff_valFun (V : Opens (TopCat.of Y))
    (s : sections (sP N) ((isOpenEmbedding_chartMap j Y).functor.obj V)) :
    ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin N)) 𝓘(ℂ) ∞ (valFun j Y V s) := by
  rw [MMP.Analytic.contMDiff_iff_differentiableOn_extend]
  have hW := mem_chart_of_mem_functor j Y V
  let G : EuclideanSpace ℂ (Fin N) → ℂ := fun z =>
    holFun (c := stdChart N j) hW s (EuclideanSpace.equiv (Fin N) ℂ z)
  have hG : DifferentiableOn ℂ G (Set.range (MMP.Analytic.openInclusion V)) := by
    rintro _ ⟨v, rfl⟩
    have h1 := differentiableAt_holFun (stdChart_ideal N j) hW s (ptOf j Y V v)
    rw [coords_chartPt] at h1
    exact (h1.comp _ (EuclideanSpace.equiv (Fin N) ℂ).differentiableAt).differentiableWithinAt
  refine hG.congr ?_
  rintro _ ⟨v, rfl⟩
  rw [(MMP.Analytic.isOpenEmbedding_openInclusion V).injective.extend_apply]
  have h2 := holFun_coords (stdChart_ideal N j) hW s (ptOf j Y V v)
  simp only [G, valFun]
  rw [← h2, coords_chartPt]

/-- Reading sections of `𝒪_{(ℙᴺ)^an}` over the image of `V` in the chart `U_j`. -/
private noncomputable def valHom (V : Opens (TopCat.of Y)) :
    sections (sP N) ((isOpenEmbedding_chartMap j Y).functor.obj V) →+*
      𝒪[N, Y].presheaf.obj (op V) where
  toFun s := ⟨valFun j Y V s, contMDiff_valFun j Y V s⟩
  map_one' := ContMDiffMap.ext fun v => by
    change stalkRingValue (stdChart N j) ⟨chartPt j v.1.1, chartPt_mem j _⟩ 1 = 1
    exact map_one _
  map_mul' s t := ContMDiffMap.ext fun v => secVal_mul s t _ _ _
  map_zero' := ContMDiffMap.ext fun v => by
    change stalkRingValue (stdChart N j) ⟨chartPt j v.1.1, chartPt_mem j _⟩ 0 = 0
    exact map_zero _
  map_add' s t := ContMDiffMap.ext fun v => secVal_add s t _ _ _

private lemma valHom_apply (V : Opens (TopCat.of Y))
    (s : sections (sP N) ((isOpenEmbedding_chartMap j Y).functor.obj V)) (v : V) :
    (valHom j Y V s : V → ℂ) v = secVal s (ptOf j Y V v) (stdChart N j) (chartPt_mem j _) := rfl

private lemma valHom_bijective (V : Opens (TopCat.of Y)) : Function.Bijective (valHom j Y V) := by
  have hW := mem_chart_of_mem_functor j Y V
  refine ⟨fun s t h => ?_, fun g => ?_⟩
  · refine eq_of_secVal_eq (stdChart_ideal N j) hW s t fun x => ?_
    rcases x with ⟨_, v, hv, rfl⟩
    exact congrArg (fun f : 𝒪[N, Y].presheaf.obj (op V) => (f : V → ℂ) ⟨v, hv⟩) h
  · let h : (Fin N → ℂ) → ℂ := fun p => Function.extend (MMP.Analytic.openInclusion V) g 0
      ((EuclideanSpace.equiv (Fin N) ℂ).symm p)
    have hT : IsOpen ((EuclideanSpace.equiv (Fin N) ℂ).symm ⁻¹'
        Set.range (MMP.Analytic.openInclusion V)) :=
      (MMP.Analytic.isOpenEmbedding_openInclusion V).isOpen_range.preimage
        (EuclideanSpace.equiv (Fin N) ℂ).symm.continuous
    have hh : DifferentiableOn ℂ h ((EuclideanSpace.equiv (Fin N) ℂ).symm ⁻¹'
        Set.range (MMP.Analytic.openInclusion V)) :=
      ((MMP.Analytic.contMDiff_iff_differentiableOn_extend V g).1 g.2).comp
        (EuclideanSpace.equiv (Fin N) ℂ).symm.differentiableOn (fun _ hp => hp)
    obtain ⟨s, hs⟩ := exists_sections_secVal_eq (c := stdChart N j) hW hT h hh (by
      rintro ⟨_, v, hv, rfl⟩
      change (EuclideanSpace.equiv (Fin N) ℂ).symm ((stdChart N j).coords ⟨chartPt j v.1, _⟩) ∈
        Set.range (MMP.Analytic.openInclusion V)
      rw [coords_chartPt, ContinuousLinearEquiv.symm_apply_apply]
      exact ⟨⟨v, hv⟩, rfl⟩)
    refine ⟨s, ContMDiffMap.ext fun v => ?_⟩
    refine (valHom_apply j Y V s v).trans ((hs _).trans ?_)
    change Function.extend (MMP.Analytic.openInclusion V) g 0
      ((EuclideanSpace.equiv (Fin N) ℂ).symm ((stdChart N j).coords ⟨chartPt j v.1.1, _⟩)) = g v
    rw [coords_chartPt, ContinuousLinearEquiv.symm_apply_apply]
    exact (MMP.Analytic.isOpenEmbedding_openInclusion V).injective.extend_apply g 0 v

private lemma valHom_res {V₁ V₂ : Opens (TopCat.of Y)} (h : V₂ ≤ V₁)
    (s : sections (sP N) ((isOpenEmbedding_chartMap j Y).functor.obj V₁)) :
    valHom j Y V₂ (restrictHom (Set.image_mono h) s) =
      𝒪[N, Y].presheaf.map (homOfLE h).op (valHom j Y V₁ s) :=
  ContMDiffMap.ext fun _ => rfl

private lemma chartMap_functor_isContinuous :
    (isOpenEmbedding_chartMap j Y).functor.IsContinuous
      (Opens.grothendieckTopology (TopCat.of Y)) (Opens.grothendieckTopology (space (sP N))) :=
  (isOpenEmbedding_chartMap j Y).functor_isContinuous

attribute [local instance] chartMap_functor_isContinuous

/-- The structure sheaf of `(ℙᴺ)^an` on the chart `U_j`, read on `Y ⊆ ℂᴺ`, is the sheaf of
holomorphic functions. -/
private noncomputable def chartRingIso :
    ((isOpenEmbedding_chartMap j Y).functor.sheafPushforwardContinuous RingCat.{0}
      (Opens.grothendieckTopology (TopCat.of Y)) (Opens.grothendieckTopology (space (sP N)))).obj
        (ringCatSheaf (sP N)) ≅ holomorphicRingCatSheaf N Y :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (NatIso.ofComponents
    (fun V =>
      (RingEquiv.ofBijective (valHom j Y V.unop) (valHom_bijective j Y V.unop)).toRingCatIso)
    (fun {V₁ V₂} i => by
      ext s
      exact valHom_res j Y (leOfHom i.unop) s))

/-- The transport datum of the chart `U_j` over `Y`. -/
private noncomputable abbrev chartψ :
    holomorphicRingCatSheaf N Y ⟶
      ((isOpenEmbedding_chartMap j Y).functor.sheafPushforwardContinuous RingCat.{0}
        (Opens.grothendieckTopology (TopCat.of Y)) (Opens.grothendieckTopology (space (sP N)))).obj
          (ringCatSheaf (sP N)) :=
  (chartRingIso j Y).inv

private lemma chartψ_bijective (V : Opens (TopCat.of Y)) :
    Function.Bijective ((chartψ j Y).hom.app (op V)).hom :=
  (RingEquiv.ofBijective (valHom j Y V) (valHom_bijective j Y V)).symm.bijective

/-- Coherence of `S` is coherence of `S` read on a chart. -/
private lemma isCoherentModule_chart (S : SheafOfModules.{0} (ringCatSheaf (sP N)))
    (hS : IsCoherentModule S) (α : Fin (N + 1))
    (Ω : Opens (EuclideanSpace ℂ (Fin N))) :
    IsCoherentModule ((SheafOfModules.pushforward (chartψ α Ω)).obj S) :=
  isCoherentModule_pushforward (chartMap α Ω) _ (fun V x hx => Set.mem_image_of_mem _ hx)
    (by rintro U V _ ⟨x, ⟨hxU, -⟩, rfl⟩; exact hxU) (chartψ α Ω) (chartψ_bijective α Ω) hS

/-! ### Coordinate changes between the standard charts -/

section Transitions

variable {N : ℕ}

/-- The homogeneous coordinates `(w, 1)` of the point of `U_α` with affine coordinates `w`. -/
private abbrev hz (α : Fin (N + 1)) (w : EuclideanSpace ℂ (Fin N)) : Fin (N + 1) → ℂ :=
  insertOne α (EuclideanSpace.equiv (Fin N) ℂ w)

private lemma hz_self (α : Fin (N + 1)) (w : EuclideanSpace ℂ (Fin N)) : hz α w α = 1 :=
  Fin.insertNth_apply_same (α := fun _ => ℂ) α 1 _

private lemma hz_succAbove (α : Fin (N + 1)) (w : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    hz α w (α.succAbove i) = w i :=
  Fin.insertNth_apply_succAbove (α := fun _ => ℂ) α 1 _ i

private lemma hcoord_chartPt (α : Fin (N + 1)) (w : EuclideanSpace ℂ (Fin N)) :
    hcoord N α ⟨chartPt α w, chartPt_mem α w⟩ = hz α w := by
  rw [hcoord_eq_insertOne, coords_chartPt]

private lemma chartPt_mem_iff (α β : Fin (N + 1)) (w : EuclideanSpace ℂ (Fin N)) :
    chartPt α w ∈ chart (sX := sP N) (stdChart N β).U ↔ hz α w β ≠ 0 := by
  rw [← hcoord_chartPt, ← toScheme_mem_X_iff]
  exact mem_chart_iff

/-- The coordinate change `U_α → U_β`, `w ↦ (z_{β.succAbove i} / z_β)_i` with `z = (w, 1)`. -/
private def tr (α β : Fin (N + 1)) (w : EuclideanSpace ℂ (Fin N)) : EuclideanSpace ℂ (Fin N) :=
  (EuclideanSpace.equiv (Fin N) ℂ).symm fun i => hz α w (β.succAbove i) / hz α w β

private lemma tr_apply (α β : Fin (N + 1)) (w : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    tr α β w i = hz α w (β.succAbove i) / hz α w β := rfl

private lemma coords_chartPt_of_ne (α β : Fin (N + 1)) (w : EuclideanSpace ℂ (Fin N))
    (h : hz α w β ≠ 0) :
    (stdChart N β).coords ⟨chartPt α w, (chartPt_mem_iff α β w).2 h⟩ =
      EuclideanSpace.equiv (Fin N) ℂ (tr α β w) := by
  refine funext fun (i : Fin N) => ?_
  have hα := chartPt_mem α w
  have hβ := (chartPt_mem_iff α β w).2 h
  have e1 := hcoord_change α β (chartPt α w) hα hβ (β.succAbove i)
  have e2 := hcoord_change α β (chartPt α w) hα hβ β
  rw [hcoord_self, hcoord_chartPt] at e2
  rw [hcoord_chartPt] at e1
  change hcoord N β ⟨chartPt α w, hβ⟩ (β.succAbove i) = hz α w (β.succAbove i) / hz α w β
  rw [e1]
  rw [eq_div_iff h]
  have : hcoord N β ⟨chartPt α w, hβ⟩ α = 1 / hz α w β := by
    rw [eq_div_iff h]; exact e2.symm
  rw [this]
  field_simp

private lemma chartPt_tr (α β : Fin (N + 1)) (w : EuclideanSpace ℂ (Fin N)) (h : hz α w β ≠ 0) :
    chartPt β (tr α β w) = chartPt α w := by
  have := (coordsHomeo β).injective (a₁ := ⟨chartPt β (tr α β w), chartPt_mem β _⟩)
    (a₂ := ⟨chartPt α w, (chartPt_mem_iff α β w).2 h⟩)
    (by rw [coordsHomeo_apply, coordsHomeo_apply, coords_chartPt, coords_chartPt_of_ne α β w h])
  exact congrArg Subtype.val this

private lemma tr_self (α : Fin (N + 1)) (w : EuclideanSpace ℂ (Fin N)) : tr α α w = w := by
  ext i
  rw [tr_apply, hz_self, div_one, hz_succAbove]

private lemma differentiable_hz (α : Fin (N + 1)) (m : Fin (N + 1)) :
    Differentiable ℂ (fun w : EuclideanSpace ℂ (Fin N) => hz α w m) := by
  rcases Fin.eq_self_or_eq_succAbove α m with rfl | ⟨i, rfl⟩
  · simp only [hz_self]; exact differentiable_const _
  · simp only [hz_succAbove]
    exact (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin N) →L[ℂ] ℂ).differentiable

private lemma differentiableOn_tr (α β : Fin (N + 1)) (i : Fin N) :
    DifferentiableOn ℂ (fun w : EuclideanSpace ℂ (Fin N) => tr α β w i) {w | hz α w β ≠ 0} :=
  show DifferentiableOn ℂ (fun w => hz α w (β.succAbove i) / hz α w β) _ from fun w hw => by
    have h1 := (differentiable_hz α (β.succAbove i) w).mul ((differentiable_hz α β w).inv hw)
    simp only [← div_eq_mul_inv] at h1
    exact h1.differentiableWithinAt

private lemma continuous_hz (α m : Fin (N + 1)) :
    Continuous (fun w : EuclideanSpace ℂ (Fin N) => hz α w m) :=
  (differentiable_hz α m).continuous

end Transitions

/-! ### Boxes -/

section Boxes

variable {N : ℕ}

/-- The open box `∏ᵢ (-r, r) × (-r, r)` in `ℂᴺ`. -/
private def box (r : ℝ) : Set (EuclideanSpace ℂ (Fin N)) :=
  {w | ∀ i, w i ∈ Set.Ioo (-r) r ×ℂ Set.Ioo (-r) r}

/-- The closed box `∏ᵢ [-r, r] × [-r, r]` in `ℂᴺ`. -/
private def cbox (r : ℝ) : Set (EuclideanSpace ℂ (Fin N)) :=
  {w | ∀ i, w i ∈ Set.Icc (-r) r ×ℂ Set.Icc (-r) r}

private lemma mem_box_iff {r : ℝ} {w : EuclideanSpace ℂ (Fin N)} :
    w ∈ box r ↔ ∀ i, |(w i).re| < r ∧ |(w i).im| < r := by
  simp only [box, Set.mem_setOf_eq, abs_lt]
  rfl

private lemma mem_cbox_iff {r : ℝ} {w : EuclideanSpace ℂ (Fin N)} :
    w ∈ cbox r ↔ ∀ i, |(w i).re| ≤ r ∧ |(w i).im| ≤ r := by
  simp only [cbox, Set.mem_setOf_eq, abs_le]
  rfl

private lemma isOpen_box (r : ℝ) : IsOpen (box (N := N) r) := by
  have : box (N := N) r = ⋂ i, (fun w : EuclideanSpace ℂ (Fin N) => w i) ⁻¹'
      (Set.Ioo (-r) r ×ℂ Set.Ioo (-r) r) := by
    ext w; simp [box]
  rw [this]
  exact isOpen_iInter_of_finite fun i => (isOpen_Ioo.reProdIm isOpen_Ioo).preimage
    (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin N) →L[ℂ] ℂ).continuous

private lemma isClosed_cbox (r : ℝ) : IsClosed (cbox (N := N) r) := by
  have : cbox (N := N) r = ⋂ i, (fun w : EuclideanSpace ℂ (Fin N) => w i) ⁻¹'
      (Set.Icc (-r) r ×ℂ Set.Icc (-r) r) := by
    ext w; simp [cbox]
  rw [this]
  exact isClosed_iInter fun i => (isClosed_Icc.reProdIm isClosed_Icc).preimage
    (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin N) →L[ℂ] ℂ).continuous

private lemma box_subset_cbox (r : ℝ) : box (N := N) r ⊆ cbox r := fun w hw i =>
  ⟨⟨(hw i).1.1.le, (hw i).1.2.le⟩, ⟨(hw i).2.1.le, (hw i).2.2.le⟩⟩

private lemma cbox_subset_box {r r' : ℝ} (h : r < r') : cbox (N := N) r ⊆ box r' := fun w hw i =>
  ⟨⟨by linarith [(hw i).1.1], by linarith [(hw i).1.2]⟩,
    ⟨by linarith [(hw i).2.1], by linarith [(hw i).2.2]⟩⟩

private lemma box_mono {r r' : ℝ} (h : r ≤ r') : box (N := N) r ⊆ box r' := fun w hw i =>
  ⟨⟨by linarith [(hw i).1.1], by linarith [(hw i).1.2]⟩,
    ⟨by linarith [(hw i).2.1], by linarith [(hw i).2.2]⟩⟩

private lemma closure_box_subset (r : ℝ) : closure (box (N := N) r) ⊆ cbox r :=
  closure_minimal (box_subset_cbox r) (isClosed_cbox r)

private lemma norm_le_of_mem_cbox {r : ℝ} {w : EuclideanSpace ℂ (Fin N)} (hw : w ∈ cbox r) :
    ‖w‖ ≤ √(∑ _i : Fin N, (2 * r) ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  have h := mem_cbox_iff.1 hw i
  have h0 : ‖w i‖ ≤ 2 * r :=
    (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith [h.1, h.2, abs_nonneg (w i).re])
  exact pow_le_pow_left₀ (norm_nonneg _) h0 2

private lemma isCompact_cbox (r : ℝ) : IsCompact (cbox (N := N) r) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_cbox r)
    (isBounded_iff_forall_norm_le.2 ⟨_, fun _ hw => norm_le_of_mem_cbox hw⟩)

private lemma mem_box_of_norm_le {r : ℝ} (hr : 1 < r) {w : EuclideanSpace ℂ (Fin N)}
    (hw : ∀ i, ‖w i‖ ≤ 1) : w ∈ box r := fun i =>
  have h1 := Complex.abs_re_le_norm (w i)
  have h2 := Complex.abs_im_le_norm (w i)
  ⟨abs_lt.1 (by linarith [hw i]), abs_lt.1 (by linarith [hw i])⟩

private lemma norm_lt_of_mem_box {r : ℝ} {w : EuclideanSpace ℂ (Fin N)} (hw : w ∈ box r)
    (i : Fin N) : ‖w i‖ < 2 * r := by
  have h := mem_box_iff.1 hw i
  exact (Complex.norm_le_abs_re_add_abs_im _).trans_lt (by linarith [h.1, h.2])

end Boxes

/-! ### The covers of `(ℙᴺ)^an` by boxes in the standard charts -/

section Cover

variable {N : ℕ}

private lemma chartPt_injective (α : Fin (N + 1)) : Function.Injective (chartPt (N := N) α) :=
  (isOpenEmbedding_chartPt α).injective

/-- Every point of `(ℙᴺ)^an` lies in a standard chart. -/
private lemma exists_chartPt_eq (x : ComplexPoints (sP N)) :
    ∃ (γ : Fin (N + 1)) (w : EuclideanSpace ℂ (Fin N)), chartPt γ w = x := by
  have hx : x.toScheme ∈ ⨆ i, MMP.UnderlyingSpace.projectiveSpaceStdChart ℂ N i := by
    rw [Stacks.AlgebraicGeometry.ProjPolyChart.iSup_basicOpen_X_eq_top ℂ N]; trivial
  obtain ⟨γ, hγ⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have hxc : x ∈ chart (sX := sP N) (stdChart N γ).U := mem_chart_iff.2 hγ
  refine ⟨γ, (EuclideanSpace.equiv (Fin N) ℂ).symm (coordsHomeo γ ⟨x, hxc⟩), ?_⟩
  change ((coordsHomeo γ).symm (EuclideanSpace.equiv (Fin N) ℂ
    ((EuclideanSpace.equiv (Fin N) ℂ).symm (coordsHomeo γ ⟨x, hxc⟩)))).1 = x
  rw [ContinuousLinearEquiv.apply_symm_apply, Homeomorph.symm_apply_apply]

/-- The cover member `V^{(r)}_α`: the box of half-side `r` in the chart `U_α`. -/
private def cov (r : ℝ) (α : Fin (N + 1)) : Opens (space (sP N)) :=
  ⟨chartPt α '' box r, (isOpenEmbedding_chartPt α).isOpenMap _ (isOpen_box r)⟩

private lemma mem_cov_iff (r : ℝ) (α β : Fin (N + 1)) (w : EuclideanSpace ℂ (Fin N)) :
    chartPt α w ∈ cov r β ↔ hz α w β ≠ 0 ∧ tr α β w ∈ box r := by
  constructor
  · rintro ⟨v, hv, he⟩
    have hβ : chartPt α w ∈ chart (sX := sP N) (stdChart N β).U := he ▸ chartPt_mem β v
    have h := (chartPt_mem_iff α β w).1 hβ
    refine ⟨h, ?_⟩
    have : tr α β w = v := chartPt_injective β ((chartPt_tr α β w h).trans he.symm)
    rwa [this]
  · rintro ⟨h1, h2⟩
    exact ⟨tr α β w, h2, chartPt_tr α β w h1⟩

private lemma cov_mono {r r' : ℝ} (h : r ≤ r') (α : Fin (N + 1)) : cov (N := N) r α ≤ cov r' α :=
  Set.image_mono (box_mono h)

private lemma iSup_cov {r : ℝ} (hr : 1 < r) : ⨆ α, cov (N := N) r α = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨γ, w, rfl⟩ := exists_chartPt_eq x
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun m => ‖hz γ w m‖)
    ⟨γ, Finset.mem_univ _⟩
  have hγ : ‖hz γ w γ‖ = 1 := by rw [hz_self, norm_one]
  have hm0 : hz γ w m ≠ 0 := by
    intro h0
    have := hm γ (Finset.mem_univ _)
    rw [hγ, h0, norm_zero] at this
    exact absurd this (by norm_num)
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨m, (mem_cov_iff r γ m w).2 ⟨hm0, ?_⟩⟩
  refine mem_box_of_norm_le hr fun i => ?_
  rw [tr_apply, norm_div, div_le_one (norm_pos_iff.2 hm0)]
  exact hm _ (Finset.mem_univ _)

private lemma continuousOn_tr (α β : Fin (N + 1)) :
    ContinuousOn (tr α β) {w : EuclideanSpace ℂ (Fin N) | hz α w β ≠ 0} :=
  (EuclideanSpace.equiv (Fin N) ℂ).symm.continuous.comp_continuousOn
    (continuousOn_pi.2 fun i => (continuous_hz α (β.succAbove i)).continuousOn.div
      (continuous_hz α β).continuousOn fun _ hw => hw)

private lemma isOpen_hz_ne (α β : Fin (N + 1)) :
    IsOpen {w : EuclideanSpace ℂ (Fin N) | hz α w β ≠ 0} :=
  isOpen_ne_fun (continuous_hz α β) continuous_const

/-- The coordinates, in the chart `U_α`, of the intersection `V^{(r)}_J` of the cover members
indexed by `J`. -/
private def Ωs (r : ℝ) (α : Fin (N + 1)) {p : ℕ} (J : Fin p → Fin (N + 1)) :
    Set (EuclideanSpace ℂ (Fin N)) :=
  {w | ∀ k, hz α w (J k) ≠ 0 ∧ tr α (J k) w ∈ box r}

private lemma isOpen_Ωs (r : ℝ) (α : Fin (N + 1)) {p : ℕ} (J : Fin p → Fin (N + 1)) :
    IsOpen (Ωs r α J) := by
  have : Ωs r α J = ⋂ k, ({w | hz α w (J k) ≠ 0} ∩ tr α (J k) ⁻¹' box r) := by
    ext w; simp [Ωs]
  rw [this]
  exact isOpen_iInter_of_finite fun k =>
    (continuousOn_tr α (J k)).isOpen_inter_preimage (isOpen_hz_ne α (J k)) (isOpen_box r)

/-- `Ωs` as an open set. -/
private def Ωo (r : ℝ) (α : Fin (N + 1)) {p : ℕ} (J : Fin p → Fin (N + 1)) :
    Opens (EuclideanSpace ℂ (Fin N)) :=
  ⟨Ωs r α J, isOpen_Ωs r α J⟩

private lemma mem_inter_iff {ι : Type} {U : ι → Opens (space (sP N))} {p : ℕ} (J : Fin p → ι)
    (x : ComplexPoints (sP N)) : x ∈ CechCochains.inter U J ↔ ∀ k, x ∈ U (J k) := by
  change x ∈ ((⨅ k, U (J k) : Opens (space (sP N))) : Set (ComplexPoints (sP N))) ↔ _
  rw [Opens.coe_iInf]
  simp

private lemma chartPt_mem_inter_iff (r : ℝ) (α : Fin (N + 1)) {p : ℕ} (J : Fin p → Fin (N + 1))
    (w : EuclideanSpace ℂ (Fin N)) :
    chartPt α w ∈ CechCochains.inter (cov r) J ↔ w ∈ Ωs r α J := by
  rw [mem_inter_iff]
  exact forall_congr' fun k => mem_cov_iff r α (J k) w

private lemma Ωs_subset_box {r : ℝ} {α : Fin (N + 1)} {p : ℕ} {J : Fin p → Fin (N + 1)}
    (hα : α ∈ Set.range J) : Ωs r α J ⊆ box r := by
  obtain ⟨k, hk⟩ := hα
  intro w hw
  have := (hw k).2
  rwa [hk, tr_self] at this

private lemma eq_chartPt_of_mem_inter {r : ℝ} {α : Fin (N + 1)} {p : ℕ}
    {J : Fin p → Fin (N + 1)} (hα : α ∈ Set.range J) {x : ComplexPoints (sP N)}
    (hx : x ∈ CechCochains.inter (cov r) J) : ∃ w ∈ Ωs r α J, chartPt α w = x := by
  obtain ⟨k, hk⟩ := hα
  have h1 := (mem_inter_iff J x).1 hx k
  rw [hk] at h1
  obtain ⟨v, -, rfl⟩ := h1
  exact ⟨v, (chartPt_mem_inter_iff r α J v).1 hx, rfl⟩

end Cover

/-! ### Closures of the intersections, and the intersections as graphs -/

section Graphs

variable {N : ℕ}

private lemma norm_hz_ge {r : ℝ} (hr : 1 ≤ r) {α : Fin (N + 1)} {p : ℕ}
    {J : Fin p → Fin (N + 1)} {w : EuclideanSpace ℂ (Fin N)} (hw : w ∈ Ωs r α J) (k : Fin p) :
    1 / (2 * r) ≤ ‖hz α w (J k)‖ := by
  rcases Fin.eq_self_or_eq_succAbove (J k) α with h | ⟨i, h⟩
  · rw [← h, hz_self, norm_one, div_le_one (by positivity)]; linarith
  · have h1 := norm_lt_of_mem_box (hw k).2 i
    rw [tr_apply, ← h, hz_self, norm_div, norm_one] at h1
    have hpos : 0 < ‖hz α w (J k)‖ := norm_pos_iff.2 (hw k).1
    rw [div_lt_iff₀ hpos] at h1
    rw [div_le_iff₀ (by positivity)]; linarith

private lemma closure_Ωs_subset {r r' : ℝ} (hr : 1 ≤ r) (hrr' : r < r') (α : Fin (N + 1))
    {p : ℕ} (J : Fin p → Fin (N + 1)) : closure (Ωs r α J) ⊆ Ωs r' α J := by
  intro w hw k
  have hc : IsClosed {w : EuclideanSpace ℂ (Fin N) | 1 / (2 * r) ≤ ‖hz α w (J k)‖} :=
    isClosed_le continuous_const (continuous_norm.comp (continuous_hz α (J k)))
  have h1 : 1 / (2 * r) ≤ ‖hz α w (J k)‖ :=
    closure_minimal (fun w hw => norm_hz_ge hr hw k) hc hw
  have hne : hz α w (J k) ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le (by positivity) h1)
  refine ⟨hne, ?_⟩
  have hca : ContinuousWithinAt (tr α (J k)) (Ωs r α J) w :=
    ((continuousOn_tr α (J k)).continuousAt
      ((isOpen_hz_ne α (J k)).mem_nhds hne)).continuousWithinAt
  have := hca.mem_closure_image hw
  have hsub : tr α (J k) '' Ωs r α J ⊆ box r := by rintro _ ⟨v, hv, rfl⟩; exact (hv k).2
  exact cbox_subset_box hrr' (closure_box_subset r (closure_mono hsub this))

private lemma isCompact_closure_Ωs {r : ℝ} {α : Fin (N + 1)} {p : ℕ} {J : Fin p → Fin (N + 1)}
    (hα : α ∈ Set.range J) : IsCompact (closure (Ωs r α J)) :=
  (isCompact_cbox r).of_isClosed_subset isClosed_closure
    ((closure_mono (Ωs_subset_box hα)).trans (closure_box_subset r))

variable {p : ℕ} (α : Fin (N + 1)) (J : Fin (p + 1) → Fin (N + 1))

/-- The chart changes `w ↦ (tr α (J k) w)_k`, as a single map `ℂᴺ → ℂ^{(p+1)N}`. -/
private def gtr (w : EuclideanSpace ℂ (Fin N)) : EuclideanSpace ℂ (Fin ((p + 1) * N)) :=
  (EuclideanSpace.equiv _ ℂ).symm fun i =>
    tr α (J (finProdFinEquiv.symm i).1) w (finProdFinEquiv.symm i).2

private lemma gtr_apply (w : EuclideanSpace ℂ (Fin N)) (i : Fin ((p + 1) * N)) :
    gtr α J w i = tr α (J (finProdFinEquiv.symm i).1) w (finProdFinEquiv.symm i).2 := rfl

/-- The box of half-side `r` in `ℂ^{N + (p+1)N}`, containing the graph of `gtr`. -/
private def gbox (r : ℝ) : Opens (EuclideanSpace ℂ (Fin (N + (p + 1) * N))) :=
  ⟨box r, isOpen_box r⟩

private lemma differentiableOn_gtr (r : ℝ) (i : Fin ((p + 1) * N)) :
    DifferentiableOn ℂ (fun w => gtr α J w i) (Ωo r α J) :=
  (differentiableOn_tr α (J (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2).mono
    fun _ hw => (hw _).1

private lemma join_gtr_mem {r : ℝ} (hα : α ∈ Set.range J) (w : EuclideanSpace ℂ (Fin N))
    (hw : w ∈ Ωo r α J) : join w (gtr α J w) ∈ gbox (p := p) (N := N) r := by
  intro i
  induction i using Fin.addCases with
  | left i => rw [join_castAdd]; exact Ωs_subset_box hα hw i
  | right i => rw [join_natAdd, gtr_apply]; exact (hw _).2 _

private lemma graphSet_gtr_eq (r : ℝ) :
    graphSet (Ωo r α J) (gtr α J) (gbox (p := p) (N := N) r) =
      {y | ∀ i : Fin ((p + 1) * N), sndL y.1 i * hz α (prL y.1) (J (finProdFinEquiv.symm i).1) =
        hz α (prL y.1) ((J (finProdFinEquiv.symm i).1).succAbove (finProdFinEquiv.symm i).2)} := by
  ext y
  constructor
  · rintro ⟨hy, hg⟩ i
    rw [hg, gtr_apply, tr_apply]
    exact div_mul_cancel₀ _ (hy _).1
  · intro hy
    set w := prL y.1
    have hne : ∀ k, hz α w (J k) ≠ 0 := by
      intro k h0
      have hall : ∀ m, hz α w m = 0 := by
        intro m
        rcases Fin.eq_self_or_eq_succAbove (J k) m with h | ⟨j, h⟩
        · rwa [h]
        · have := hy (finProdFinEquiv (k, j))
          simp only [Equiv.symm_apply_apply] at this
          rw [h, ← this, h0, mul_zero]
      exact one_ne_zero ((hz_self α w).symm.trans (hall α))
    have hsnd : ∀ i, sndL y.1 i = gtr α J w i := by
      intro i
      rw [gtr_apply, tr_apply, eq_div_iff (hne _)]
      exact hy i
    have hsg : sndL y.1 = gtr α J w := by ext i; exact hsnd i
    refine ⟨fun k => ⟨hne k, fun j => ?_⟩, hsg⟩
    have h1 := y.2 (Fin.natAdd N (finProdFinEquiv (k, j)))
    have h2 : tr α (J k) w j = sndL y.1 (finProdFinEquiv (k, j)) := by
      rw [hsnd, gtr_apply, Equiv.symm_apply_apply]
    rw [h2, sndL_apply]
    exact h1

private lemma isClosed_graphSet_gtr (r : ℝ) :
    IsClosed (graphSet (Ωo r α J) (gtr α J) (gbox (p := p) (N := N) r)) := by
  rw [graphSet_gtr_eq]
  have hc : ∀ m : Fin (N + 1), Continuous fun y : gbox (p := p) (N := N) r =>
      hz α (prL y.1) m :=
    fun m => (continuous_hz α m).comp (prL.continuous.comp continuous_subtype_val)
  have hs : ∀ i, Continuous fun y : gbox (p := p) (N := N) r => sndL y.1 i := fun i =>
    (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin ((p + 1) * N)) →L[ℂ] ℂ).continuous.comp
      (sndL.continuous.comp continuous_subtype_val)
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_eq ((hs i).mul (hc _)) (hc _)

/-- **Cartan's Theorem B on the intersections.** Every coherent module on the chart
coordinates of `V^{(r)}_J` has vanishing higher cohomology. -/
private theorem isZero_sheafCohomology_Ωo {r : ℝ} (hα : α ∈ Set.range J)
    (M : SheafOfModules.{0} (holomorphicRingCatSheaf N (Ωo r α J))) (hM : IsCoherentModule M)
    (q : ℤ) (hq : 1 ≤ q) :
    IsZero ((sheafCohomology (TopCat.of (Ωo r α J)) q).obj ((SheafOfModules.toSheaf _).obj M)) :=
  isZero_sheafCohomology_of_graph (fun _ => -r) (fun _ => r) (fun _ => -r) (fun _ => r)
    (gbox (p := p) (N := N) r) rfl (differentiableOn_gtr α J r) (join_gtr_mem α J hα)
    (isClosed_graphSet_gtr α J r) M hM q hq

end Graphs

/-! ### Acyclicity of coherent sheaves on the intersections of the covers -/

section Acyclic

variable {N : ℕ}

/-- The chart coordinates of `V^{(r)}_J` map homeomorphically onto `V^{(r)}_J`. -/
private def interPt (r : ℝ) (α : Fin (N + 1)) {p : ℕ} (J : Fin p → Fin (N + 1)) :
    TopCat.of (Ωo r α J) ⟶
      (Opens.toTopCat (space (sP N))).obj (CechCochains.inter (cov r) J) :=
  TopCat.ofHom ⟨fun w => ⟨chartPt α w.1, (chartPt_mem_inter_iff r α J w.1).2 w.2⟩,
    ((isOpenEmbedding_chartPt α).continuous.comp continuous_subtype_val).subtype_mk _⟩

private lemma isOpenEmbedding_interPt (r : ℝ) (α : Fin (N + 1)) {p : ℕ}
    (J : Fin p → Fin (N + 1)) : Topology.IsOpenEmbedding (interPt r α J) :=
  Topology.IsOpenEmbedding.of_comp _ (CechCochains.inter (cov r) J).isOpenEmbedding'
    (isOpenEmbedding_chartMap α (Ωo r α J))

private lemma surjective_interPt {r : ℝ} {α : Fin (N + 1)} {p : ℕ} {J : Fin p → Fin (N + 1)}
    (hα : α ∈ Set.range J) : Function.Surjective (interPt r α J) := fun x => by
  obtain ⟨w, hw, h⟩ := eq_chartPt_of_mem_inter hα x.2
  exact ⟨⟨w, hw⟩, Subtype.ext h⟩

variable (S : SheafOfModules.{0} (ringCatSheaf (sP N)))

/-- The underlying abelian sheaf of `S`. -/
private abbrev Ssh : TopCat.Sheaf AddCommGrpCat.{0} (space (sP N)) :=
  (SheafOfModules.toSheaf _).obj S

/-- The restriction of `S` to `V^{(r)}_J`, read on the chart coordinates, is the abelian sheaf
of the transported module. -/
private def interSheafIso (r : ℝ) (α : Fin (N + 1)) {p : ℕ} (J : Fin p → Fin (N + 1)) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} (interPt r α J)).obj
      ((TopCat.Sheaf.pullback AddCommGrpCat.{0}
        (Opens.inclusion' (CechCochains.inter (cov r) J))).obj (Ssh S)) ≅
      (SheafOfModules.toSheaf _).obj
        ((SheafOfModules.pushforward (chartψ α (Ωo r α J))).obj S) := by
  let hh := isOpenEmbedding_interPt r α J
  let hi := Opens.isOpenEmbedding (CechCochains.inter (cov r) J)
  refine ((hh.sheafPullbackIso AddCommGrpCat.{0}).app _) ≪≫
    (hh.sheafPullback AddCommGrpCat.{0}).mapIso
      ((hi.sheafPullbackIso AddCommGrpCat.{0}).app _) ≪≫ ?_
  have e : ∀ V : Opens (TopCat.of (Ωo r α J)), hi.functor.obj (hh.functor.obj V) =
      (isOpenEmbedding_chartMap α (Ωo r α J)).functor.obj V := fun V => by
    ext x; constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩; exact ⟨w, hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩; exact ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  refine (fullyFaithfulSheafToPresheaf _ _).preimageIso (NatIso.ofComponents (fun V =>
    (Ssh S).obj.mapIso (eqToIso (congrArg op (e V.unop)))) ?_)
  intro V V' f
  simp only [Functor.mapIso_hom, eqToIso.hom]
  change (Ssh S).obj.map _ ≫ (Ssh S).obj.map _ = (Ssh S).obj.map _ ≫ (Ssh S).obj.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

private theorem isZero_inter (hS : IsCoherentModule S) (r : ℝ) {p : ℕ}
    (J : CechCochains.OrdIndex (I := Fin (N + 1)) p) (q : ℤ) (hq : 0 < q) :
    IsZero ((sheafCohomology ((Opens.toTopCat (space (sP N))).obj
      (CechCochains.inter (cov r) J.1)) q).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{0}
          (Opens.inclusion' (CechCochains.inter (cov r) J.1))).obj (Ssh S))) := by
  have hα : J.1 0 ∈ Set.range J.1 := ⟨0, rfl⟩
  have h0 := isZero_sheafCohomology_Ωo (J.1 0) J.1 hα _
    (isCoherentModule_chart S hS (J.1 0) (Ωo r (J.1 0) J.1)) q (by omega)
  have h1 := CartanCompactBlocks.isIso_sheafCohomologyPullback (interPt r (J.1 0) J.1)
    (isOpenEmbedding_interPt r (J.1 0) J.1) (surjective_interPt hα)
    ((TopCat.Sheaf.pullback AddCommGrpCat.{0}
      (Opens.inclusion' (CechCochains.inter (cov r) J.1))).obj (Ssh S)) q
  exact (h0.of_iso ((sheafCohomology _ q).mapIso (interSheafIso S r (J.1 0) J.1))).of_iso
    (asIso (sheafCohomologyPullback _ _ q))

end Acyclic

/-! ### Leray's theorem for the covers, and the vanishing -/

section Vanishing

variable {N : ℕ}

private lemma isEmpty_ordIndex {p : ℕ} (hp : N + 1 ≤ p) :
    IsEmpty (CechCochains.OrdIndex (I := Fin (N + 1)) p) :=
  ⟨fun J => by
    have := Fintype.card_le_of_injective _ J.2.injective
    simp only [Fintype.card_fin] at this
    omega⟩

/-- The Leray isomorphisms, from the ordered Čech complexes of acyclic covers to sheaf
cohomology, with their naturality. -/
private abbrev LerayData :=
  exists_orderedCechComplex_homologyIso_sheafCohomology.{0}

variable (S : SheafOfModules.{0} (ringCatSheaf (sP N)))

private theorem isZero_sheafCohomology_of_le (hS : IsCoherentModule S) (q : ℕ)
    (hq : N + 1 ≤ q) : IsZero ((sheafCohomology (space (sP N)) q).obj (Ssh S)) := by
  obtain ⟨e, -, -, -⟩ := LerayData
  have h := e (Fin (N + 1)) (space (sP N)) (cov 2) (Ssh S) (iSup_cov (by norm_num))
    (fun p J q hq => isZero_inter S hS 2 J q hq) q
  refine IsZero.of_iso ?_ h.symm
  refine ShortComplex.isZero_homology_of_isZero_X₂ _ ?_
  have := isEmpty_ordIndex (N := N) hq
  have hsub : Subsingleton (CechCochains.OrdCochain (cov 2) (Ssh S).obj q) :=
    ⟨fun a b => funext fun J => isEmptyElim J⟩
  exact @AddCommGrpCat.isZero_of_subsingleton _ hsub

end Vanishing

/-! ### Values of holomorphic functions on `(ℙᴺ)^an`, and bounded holomorphic functions -/

section Values

variable {N : ℕ}

private lemma exists_mem_chart (x : ComplexPoints (sP N)) :
    ∃ γ : Fin (N + 1), x ∈ chart (sX := sP N) (stdChart N γ).U := by
  obtain ⟨γ, w, rfl⟩ := exists_chartPt_eq x
  exact ⟨γ, chartPt_mem γ w⟩

/-- A standard chart containing `x`. -/
private def pickChart (x : ComplexPoints (sP N)) : Fin (N + 1) := (exists_mem_chart x).choose

private lemma pickChart_mem (x : ComplexPoints (sP N)) :
    x ∈ chart (sX := sP N) (stdChart N (pickChart x)).U :=
  (exists_mem_chart x).choose_spec

/-- The value at `x` of a section of `𝒪_{(ℙᴺ)^an}`. -/
private def ev {V : Opens (space (sP N))} (s : sections (sP N) V) (x : V) : ℂ :=
  secVal s x (stdChart N (pickChart x.1)) (pickChart_mem x.1)

private lemma ev_eq {V : Opens (space (sP N))} (s : sections (sP N) V) (x : V) (α : Fin (N + 1))
    (hx : x.1 ∈ chart (sX := sP N) (stdChart N α).U) : ev s x = secVal s x (stdChart N α) hx :=
  secVal_indep s x _ _ _ _

private lemma ev_add {V : Opens (space (sP N))} (s t : sections (sP N) V) (x : V) :
    ev (s + t) x = ev s x + ev t x := secVal_add s t x _ _

private lemma ev_mul {V : Opens (space (sP N))} (s t : sections (sP N) V) (x : V) :
    ev (s * t) x = ev s x * ev t x := secVal_mul s t x _ _

private lemma ev_zero {V : Opens (space (sP N))} (x : V) : ev (0 : sections (sP N) V) x = 0 := by
  have := ev_add (0 : sections (sP N) V) 0 x
  rw [add_zero] at this
  linear_combination -this

private lemma ev_restrict {V V' : Opens (space (sP N))} (h : V' ≤ V) (s : sections (sP N) V)
    (x : V') : ev (restrictHom h s) x = ev s ⟨x.1, h x.2⟩ := rfl

/-- The constant section `c` over `V`, as in the statement of the theorem. -/
private def constSec (V : Opens (space (sP N))) (c : ℂ) : (ringCatSheaf (sP N)).obj.obj (op V) :=
  (ringCatSheaf (sP N)).obj.map (homOfLE (le_top : V ≤ ⊤)).op
    (show (ringCatSheaf (sP N)).obj.obj (op ⊤) from
      (ringCatSheafHom (sP N)).hom.app (op ⊤) (ComplexPoints.baseRingHom (sP N) ⊤ c))

private lemma ringCatSheafHom_app_eq (V : (AlgebraicGeometry.Proj (polyGrading ℂ N)).Opens)
    (g : Γ(AlgebraicGeometry.Proj (polyGrading ℂ N), V)) :
    (show sections (sP N) ((Opens.map (toSchemeHom (sP N))).obj V) from
      (ringCatSheafHom (sP N)).hom.app (op V) g) = sharpHom V g := rfl

private lemma secVal_sharpHom_top (c : ℂ) (y : (Opens.map (toSchemeHom (sP N))).obj ⊤)
    (d : Chart (sP N)) (hd : y.1 ∈ chart (sX := sP N) d.U) :
    secVal (sharpHom ⊤ (ComplexPoints.baseRingHom (sP N) ⊤ c)) y d hd = c := by
  have key := secVal_sharpHom_res (c := d) (V := d.U) le_rfl
    (ComplexPoints.baseRingHom (sP N) d.U c) ⟨y.1, mem_chart_iff.1 hd⟩ hd
  rw [ComplexPoints.evalHom_baseRingHom] at key
  refine Eq.trans ?_ key
  unfold secVal
  rw [sharpHom_apply, sharpHom_apply]
  congr 2
  have e1 : ∀ (U : (AlgebraicGeometry.Proj (polyGrading ℂ N)).Opens) (p)
      (hp : p ∈ U),
      (AlgebraicGeometry.Proj (polyGrading ℂ N)).presheaf.germ U p hp
        (ComplexPoints.baseRingHom (sP N) U c) =
      (AlgebraicGeometry.Proj (polyGrading ℂ N)).presheaf.germ ⊤ p trivial
        (((sP N).appTop.hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom) c) :=
    fun U p hp => TopCat.Presheaf.germ_res_apply _ (homOfLE le_top) p hp _
  refine (e1 _ _ _).trans ((e1 _ _ (mem_chart_iff.1 hd)).symm.trans ?_)
  exact (TopCat.Presheaf.germ_res_apply _ (homOfLE le_rfl) _ _ _).symm

private lemma ev_constSec (V : Opens (space (sP N))) (c : ℂ) (x : V) :
    ev (show sections (sP N) V from constSec V c) x = c := by
  change ev (restrictHom (le_top : V ≤ ⊤) (show sections (sP N) ⊤ from
    (ringCatSheafHom (sP N)).hom.app (op ⊤) (ComplexPoints.baseRingHom (sP N) ⊤ c))) x = c
  rw [ev_restrict, ringCatSheafHom_app_eq]
  exact secVal_sharpHom_top c _ _ _

private lemma chartPt_coords (α : Fin (N + 1)) (x : ComplexPoints (sP N))
    (hx : x ∈ chart (sX := sP N) (stdChart N α).U) :
    chartPt α ((EuclideanSpace.equiv (Fin N) ℂ).symm ((stdChart N α).coords ⟨x, hx⟩)) = x := by
  change ((coordsHomeo α).symm (EuclideanSpace.equiv (Fin N) ℂ
    ((EuclideanSpace.equiv (Fin N) ℂ).symm (coordsHomeo α ⟨x, hx⟩)))).1 = x
  rw [ContinuousLinearEquiv.apply_symm_apply, Homeomorph.symm_apply_apply]

variable {α : Fin (N + 1)} {V : Opens (space (sP N))}
  (hV : ∀ x : V, x.1 ∈ chart (sX := sP N) (stdChart N α).U)

/-- A section over `V ⊆ U_α`, as a function of the coordinates of `U_α`. -/
private def hol (s : sections (sP N) V) : EuclideanSpace ℂ (Fin N) → ℂ := fun w =>
  holFun (c := stdChart N α) hV s (EuclideanSpace.equiv (Fin N) ℂ w)

include hV in
private lemma hol_chartPt (s : sections (sP N) V) (w : EuclideanSpace ℂ (Fin N))
    (hw : chartPt α w ∈ V) : hol hV s w = ev s ⟨chartPt α w, hw⟩ := by
  have h1 := holFun_coords (stdChart_ideal N α) hV s ⟨chartPt α w, hw⟩
  rw [coords_chartPt] at h1
  rw [hol, h1, ev_eq s _ α]

include hV in
private lemma differentiableOn_hol (s : sections (sP N) V) :
    DifferentiableOn ℂ (hol hV s) (chartPt α ⁻¹' V) := by
  intro w hw
  have h1 := differentiableAt_holFun (stdChart_ideal N α) hV s ⟨chartPt α w, hw⟩
  rw [coords_chartPt] at h1
  exact (h1.comp w (EuclideanSpace.equiv (Fin N) ℂ).differentiableAt).differentiableWithinAt

private lemma isOpen_preimage_chartPt (V : Opens (space (sP N))) :
    IsOpen (chartPt α ⁻¹' (V : Set (ComplexPoints (sP N)))) :=
  V.isOpen.preimage (isOpenEmbedding_chartPt α).continuous

include hV in
private lemma exists_sec_of_hol (G : EuclideanSpace ℂ (Fin N) → ℂ)
    (hG : DifferentiableOn ℂ G (chartPt α ⁻¹' V)) :
    ∃ s : sections (sP N) V, ∀ (w : EuclideanSpace ℂ (Fin N)) (hw : chartPt α w ∈ V),
      ev s ⟨chartPt α w, hw⟩ = G w := by
  let e := EuclideanSpace.equiv (Fin N) ℂ
  have hT : IsOpen (e.symm ⁻¹' (chartPt α ⁻¹' (V : Set (ComplexPoints (sP N))))) :=
    (isOpen_preimage_chartPt V).preimage e.symm.continuous
  obtain ⟨s, hs⟩ := exists_sections_secVal_eq (c := stdChart N α) hV hT (G ∘ e.symm)
    (hG.comp e.symm.differentiableOn fun _ h => h) (fun x => by
      change chartPt α (e.symm ((stdChart N α).coords ⟨x.1, hV x⟩)) ∈ V
      rw [chartPt_coords]; exact x.2)
  refine ⟨s, fun w hw => ?_⟩
  have h1 : e.symm ((stdChart N α).coords ⟨chartPt α w, hV ⟨_, hw⟩⟩) = w := by
    rw [coords_chartPt]; exact e.symm_apply_apply w
  rw [ev_eq s _ α (hV _), hs]
  exact congrArg G h1

include hV in
private lemma eq_of_ev_eq (s t : sections (sP N) V) (h : ∀ x, ev s x = ev t x) : s = t :=
  eq_of_secVal_eq (stdChart_ideal N α) hV s t fun x => by
    rw [← ev_eq, ← ev_eq]; exact h x

include hV in
private lemma continuous_ev (s : sections (sP N) V) : Continuous (fun x : V => ev s x) := by
  let e := EuclideanSpace.equiv (Fin N) ℂ
  let k : V → EuclideanSpace ℂ (Fin N) := fun x => e.symm ((stdChart N α).coords ⟨x.1, hV x⟩)
  have hk : Continuous k := e.symm.continuous.comp
    ((isOpenEmbedding_coords (stdChart N α) (stdChart_ideal N α)).continuous.comp
      (continuous_subtype_val.subtype_mk _))
  have hkm : ∀ x, k x ∈ chartPt α ⁻¹' V := fun x => by
    change chartPt α (k x) ∈ V
    rw [chartPt_coords]; exact x.2
  have h1 : (fun x : V => ev s x) = hol hV s ∘ k := by
    funext x
    rw [Function.comp_apply, hol_chartPt hV s (k x) (hkm x)]
    congr 1
    exact Subtype.ext (chartPt_coords α x.1 (hV x)).symm
  rw [h1]
  exact (differentiableOn_hol hV s).continuousOn.comp_continuous hk hkm

end Values

/-! ### The Banach spaces of bounded holomorphic functions -/

section BoundedHol

variable {N : ℕ}

/-- Bounded holomorphic functions on an open `V` of `(ℙᴺ)^an`, inside the bounded continuous
functions with the sup norm. -/
private def BH (V : Opens (space (sP N))) : Submodule ℂ (BoundedContinuousFunction V ℂ) where
  carrier := {f | ∃ s : sections (sP N) V, ∀ x, ev s x = f x}
  add_mem' := by
    rintro f g ⟨s, hs⟩ ⟨t, ht⟩
    exact ⟨s + t, fun x => by rw [ev_add, hs, ht]; rfl⟩
  zero_mem' := ⟨0, fun x => ev_zero x⟩
  smul_mem' := by
    rintro a f ⟨s, hs⟩
    exact ⟨(show sections (sP N) V from constSec V a) * s, fun x => by
      rw [ev_mul, ev_constSec, hs]; rfl⟩

variable {α : Fin (N + 1)} {V : Opens (space (sP N))}
  (hV : ∀ x : V, x.1 ∈ chart (sX := sP N) (stdChart N α).U)

include hV in
private lemma exists_chartPt_of_mem (x : V) :
    ∃ (w : EuclideanSpace ℂ (Fin N)) (hw : chartPt α w ∈ V), (⟨chartPt α w, hw⟩ : V) = x :=
  ⟨_, by rw [chartPt_coords]; exact x.2, Subtype.ext (chartPt_coords α x.1 (hV x))⟩

include hV in
private lemma isClosed_BH : IsClosed (BH V : Set (BoundedContinuousFunction V ℂ)) := by
  classical
  refine isClosed_of_closure_subset fun f hf => ?_
  obtain ⟨F, hF, hlim⟩ := mem_closure_iff_seq_limit.1 hf
  choose s hs using hF
  let G : EuclideanSpace ℂ (Fin N) → ℂ := fun w =>
    if h : chartPt α w ∈ V then f ⟨_, h⟩ else 0
  have hG : ∀ w (hw : chartPt α w ∈ V), G w = f ⟨_, hw⟩ := fun w hw => dif_pos hw
  have hconv : TendstoUniformlyOn (fun n => hol hV (s n)) G Filter.atTop (chartPt α ⁻¹' V) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1 hlim
    filter_upwards [Metric.tendstoUniformly_iff.1 hu ε hε] with n hn w hw
    rw [hol_chartPt hV (s n) w hw, hs, hG w hw]
    exact hn _
  have hd := differentiableOn_of_tendstoLocallyUniformlyOn (isOpen_preimage_chartPt V)
    (Filter.Eventually.of_forall fun n => differentiableOn_hol hV (s n))
    hconv.tendstoLocallyUniformlyOn
  obtain ⟨t, ht⟩ := exists_sec_of_hol hV G hd
  refine ⟨t, fun x => ?_⟩
  obtain ⟨w, hw, rfl⟩ := exists_chartPt_of_mem hV x
  rw [ht w hw, hG w hw]

include hV in
private lemma completeSpace_BH : CompleteSpace (BH V) := (isClosed_BH hV).completeSpace_coe

/-- The section of `𝒪` with the values of a bounded holomorphic function. -/
private def secOf (f : BH V) : sections (sP N) V := f.2.choose

private lemma ev_secOf (f : BH V) (x : V) : ev (secOf f) x = f.1 x := f.2.choose_spec x

include hV in
private lemma secOf_add (f g : BH V) : secOf (f + g) = secOf f + secOf g :=
  eq_of_ev_eq hV _ _ fun x => by rw [ev_add, ev_secOf, ev_secOf, ev_secOf]; rfl

include hV in
private lemma secOf_smul (a : ℂ) (f : BH V) :
    secOf (a • f) = (show sections (sP N) V from constSec V a) * secOf f :=
  eq_of_ev_eq hV _ _ fun x => by rw [ev_mul, ev_secOf, ev_secOf, ev_constSec]; rfl

include hV in
private lemma secOf_zero : secOf (0 : BH V) = 0 :=
  eq_of_ev_eq hV _ _ fun x => by rw [ev_secOf, ev_zero]; rfl

/-- A bounded section, as an element of `BH V`. -/
private def mkBH (s : sections (sP N) V) (C : ℝ) (hC : ∀ x, ‖ev s x‖ ≤ C) : BH V :=
  ⟨BoundedContinuousFunction.ofNormedAddCommGroup (fun x => ev s x) (continuous_ev hV s) C hC,
    ⟨s, fun _ => rfl⟩⟩

private lemma secOf_mkBH (s : sections (sP N) V) (C : ℝ) (hC : ∀ x, ‖ev s x‖ ≤ C) :
    secOf (mkBH hV s C hC) = s :=
  eq_of_ev_eq hV _ _ fun x => by rw [ev_secOf]; rfl

end BoundedHol

section Restriction

variable {N : ℕ}

/-- Restriction of bounded holomorphic functions to a smaller open. -/
private def resBH {V V' : Opens (space (sP N))} (h : V' ≤ V) : BH V →L[ℂ] BH V' :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨f.1.compContinuous ⟨Set.inclusion h, continuous_inclusion h⟩,
        ⟨restrictHom h (secOf f), fun x => by rw [ev_restrict, ev_secOf]; rfl⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 fun f => by
    rw [one_mul]
    exact BoundedContinuousFunction.norm_compContinuous_le _ _

private lemma secOf_resBH {α : Fin (N + 1)} {V V' : Opens (space (sP N))} (h : V' ≤ V)
    (hV' : ∀ x : V', x.1 ∈ chart (sX := sP N) (stdChart N α).U) (f : BH V) :
    secOf (resBH h f) = restrictHom h (secOf f) :=
  eq_of_ev_eq hV' _ _ fun x => by rw [ev_secOf, ev_restrict, ev_secOf]; rfl

end Restriction

/-! ### Two facts of functional analysis -/

section FunctionalAnalysis

/-- In a complete metric space, a set all of whose sequences have Cauchy subsequences has
compact closure. -/
private lemma isCompact_closure_of_cauchySeq {X : Type*} [MetricSpace X] [CompleteSpace X]
    {A : Set X} (h : ∀ y : ℕ → X, (∀ n, y n ∈ A) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ CauchySeq (y ∘ φ)) :
    IsCompact (closure A) := by
  refine IsSeqCompact.isCompact fun x hx => ?_
  have hy : ∀ n, ∃ b ∈ A, dist (x n) b < 1 / ((n : ℝ) + 1) := fun n =>
    Metric.mem_closure_iff.1 (hx n) _ (by positivity)
  choose y hyA hyx using hy
  obtain ⟨φ, hφ, hc⟩ := h y hyA
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨a, isClosed_closure.mem_of_tendsto ha
    (Filter.Eventually.of_forall fun n => subset_closure (hyA _)), φ, hφ, ?_⟩
  refine tendsto_of_tendsto_of_dist ha ?_
  have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) h0
  rw [dist_comm]
  exact (hyx (φ n)).le

/-- A linear map sending bounded sequences to sequences with Cauchy subsequences, into a
complete space, is a compact operator. -/
private lemma isCompactOperator_of_cauchySeq {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [CompleteSpace F] (T : E → F)
    (h : ∀ y : ℕ → E, (∀ n, ‖y n‖ ≤ 1) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ CauchySeq (T ∘ y ∘ φ)) :
    IsCompactOperator T := by
  refine ⟨closure (T '' Metric.closedBall 0 1), isCompact_closure_of_cauchySeq fun y hy => ?_,
    Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos)
      fun z hz => subset_closure ⟨z, hz, rfl⟩⟩
  choose z hz hzy using hy
  obtain ⟨φ, hφ, hc⟩ := h z fun n => by simpa using hz n
  refine ⟨φ, hφ, ?_⟩
  rwa [show y ∘ φ = T ∘ z ∘ φ from funext fun n => (hzy (φ n)).symm]

/-- **The finiteness criterion.** If `ρ` is compact and `ρ + π` is jointly surjective, then
`E₂` is spanned modulo the range of `π` by finitely many vectors. -/
private lemma exists_finite_span_mod_range {E₃ E₂ Y : Type*}
    [NormedAddCommGroup E₃] [NormedSpace ℂ E₃] [CompleteSpace E₃]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [CompleteSpace E₂]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (ρ : E₃ →L[ℂ] E₂) (hρ : IsCompactOperator ρ) (π : Y →L[ℂ] E₂)
    (hsurj : ∀ ξ, ∃ z y, ρ z + π y = ξ) :
    ∃ (n : ℕ) (ξ : Fin n → E₂), ∀ x, ∃ (a : Fin n → ℂ) (y : Y), x = ∑ i, a i • ξ i + π y := by
  let u : E₃ × Y →L[ℂ] E₂ := ρ.coprod π
  let v : E₃ × Y →L[ℂ] E₂ := -(ρ.comp (ContinuousLinearMap.fst ℂ E₃ Y))
  have hu : Function.Surjective u := fun ξ => by
    obtain ⟨z, y, h⟩ := hsurj ξ; exact ⟨(z, y), h⟩
  have hv : IsCompactOperator v := (hρ.comp_clm (ContinuousLinearMap.fst ℂ E₃ Y)).neg
  have hfd := MMP.finiteDimensional_quotient_range_add_of_surjective_of_isCompactOperator u v hu hv
  have h1 : u + v = π.comp (ContinuousLinearMap.snd ℂ E₃ Y) := by
    ext <;> simp [u, v]
  have huv : LinearMap.range (u + v).toLinearMap = LinearMap.range π.toLinearMap := by
    rw [h1]
    exact LinearMap.range_comp_of_range_eq_top (π : Y →ₗ[ℂ] E₂)
      (LinearMap.range_eq_top.2 fun y => ⟨((0 : E₃), y), rfl⟩)
  rw [huv] at hfd
  let R := LinearMap.range π.toLinearMap
  let b := Module.finBasis ℂ (E₂ ⧸ R)
  choose ξ hξ using fun i => Submodule.Quotient.mk_surjective R (b i)
  refine ⟨Module.finrank ℂ (E₂ ⧸ R), ξ, fun x => ?_⟩
  let a := b.repr (R.mkQ x)
  have hx : R.mkQ (x - ∑ i, a i • ξ i) = 0 := by
    rw [map_sub, map_sum]
    simp only [map_smul, Submodule.mkQ_apply, hξ]
    rw [b.sum_repr, Submodule.mkQ_apply, sub_self]
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨y, hy⟩ := hx
  exact ⟨a, y, by rw [ContinuousLinearMap.coe_coe] at hy; rw [hy]; abel⟩

end FunctionalAnalysis

/-! ### Bounds and compactness on the intersections -/

section Montel

variable {N : ℕ}

private lemma mem_chart_of_mem_inter {r : ℝ} {p : ℕ} (J : Fin (p + 1) → Fin (N + 1))
    (x : CechCochains.inter (cov r) J) : x.1 ∈ chart (sX := sP N) (stdChart N (J 0)).U := by
  obtain ⟨w, -, h⟩ := eq_chartPt_of_mem_inter ⟨0, rfl⟩ x.2
  rw [← h]; exact chartPt_mem _ w

private lemma inter_mono {r r' : ℝ} (h : r ≤ r') {p : ℕ} (J : Fin p → Fin (N + 1)) :
    CechCochains.inter (cov (N := N) r) J ≤ CechCochains.inter (cov r') J := fun x hx =>
  (mem_inter_iff J x).2 fun k => cov_mono h _ ((mem_inter_iff J x).1 hx k)

private lemma preimage_inter (r : ℝ) (α : Fin (N + 1)) {p : ℕ} (J : Fin p → Fin (N + 1)) :
    chartPt α ⁻¹' (CechCochains.inter (cov r) J : Set (ComplexPoints (sP N))) = Ωs r α J :=
  Set.ext fun w => chartPt_mem_inter_iff r α J w

/-- A section over `V^{(r')}_J` is bounded on `V^{(r)}_J` for `1 ≤ r < r'`. -/
private lemma exists_bound_ev {r r' : ℝ} (hr : 1 ≤ r) (hrr' : r < r') {p : ℕ}
    (J : Fin (p + 1) → Fin (N + 1)) (s : sections (sP N) (CechCochains.inter (cov r') J)) :
    ∃ C, ∀ x : CechCochains.inter (cov r) J,
      ‖ev s ⟨x.1, inter_mono hrr'.le J x.2⟩‖ ≤ C := by
  have hV' := mem_chart_of_mem_inter (r := r') J
  have hc : ContinuousOn (hol hV' s) (closure (Ωs r (J 0) J)) :=
    (differentiableOn_hol hV' s).continuousOn.mono (by
      rw [preimage_inter]; exact closure_Ωs_subset hr hrr' (J 0) J)
  obtain ⟨C, hC⟩ := (isCompact_closure_Ωs ⟨0, rfl⟩).exists_bound_of_continuousOn hc
  refine ⟨C, fun x => ?_⟩
  obtain ⟨w, hw, hx⟩ := eq_chartPt_of_mem_inter ⟨0, rfl⟩ x.2
  have hw' : chartPt (J 0) w ∈ CechCochains.inter (cov r') J := hx ▸ inter_mono hrr'.le J x.2
  have h1 := hC w (subset_closure hw)
  rw [hol_chartPt hV' s w hw'] at h1
  have e : (⟨x.1, inter_mono hrr'.le J x.2⟩ : CechCochains.inter (cov r') J) =
      ⟨chartPt (J 0) w, hw'⟩ := Subtype.ext hx.symm
  rwa [e]

/-- The restriction to `V^{(r)}_J` of a section over `V^{(r')}_J`, as a bounded holomorphic
function. -/
private def boundedRes {r r' : ℝ} (hr : 1 ≤ r) (hrr' : r < r') {p : ℕ}
    (J : Fin (p + 1) → Fin (N + 1)) (s : sections (sP N) (CechCochains.inter (cov r') J)) :
    BH (CechCochains.inter (cov r) J) :=
  mkBH (mem_chart_of_mem_inter J) (restrictHom (inter_mono hrr'.le J) s)
    (exists_bound_ev hr hrr' J s).choose fun x => by
      rw [ev_restrict]; exact (exists_bound_ev hr hrr' J s).choose_spec x

private lemma secOf_boundedRes {r r' : ℝ} (hr : 1 ≤ r) (hrr' : r < r') {p : ℕ}
    (J : Fin (p + 1) → Fin (N + 1)) (s : sections (sP N) (CechCochains.inter (cov r') J)) :
    secOf (boundedRes hr hrr' J s) = restrictHom (inter_mono hrr'.le J) s :=
  secOf_mkBH _ _ _ _

/-- **Montel.** Restriction of bounded holomorphic functions from `V^{(r')}_J` to `V^{(r)}_J`
is a compact operator. -/
private lemma isCompactOperator_resBH {r r' : ℝ} (hr : 1 ≤ r) (hrr' : r < r') {p : ℕ}
    (J : Fin (p + 1) → Fin (N + 1)) :
    IsCompactOperator (resBH (inter_mono hrr'.le J) :
      BH (CechCochains.inter (cov (N := N) r') J) →L[ℂ] BH (CechCochains.inter (cov r) J)) := by
  haveI := completeSpace_BH (mem_chart_of_mem_inter (r := r) J)
  refine isCompactOperator_of_cauchySeq _ fun z hz => ?_
  have hV' := mem_chart_of_mem_inter (r := r') J
  let e := EuclideanSpace.equiv (Fin N) ℂ
  let G : ℕ → (Fin N → ℂ) → ℂ := fun n => hol hV' (secOf (z n)) ∘ e.symm
  let Ω' : Set (Fin N → ℂ) := e.symm ⁻¹' Ωs r' (J 0) J
  have hΩ' : IsOpen Ω' := (isOpen_Ωs r' (J 0) J).preimage e.symm.continuous
  have hG : ∀ n, DifferentiableOn ℂ (G n) Ω' := fun n =>
    (differentiableOn_hol hV' _).comp e.symm.differentiableOn fun y hy => by
      rwa [preimage_inter]
  have hb : ∀ n y, y ∈ Ω' → ‖G n y‖ ≤ 1 := by
    intro n y hy
    have hy' : chartPt (J 0) (e.symm y) ∈ CechCochains.inter (cov r') J :=
      (chartPt_mem_inter_iff r' (J 0) J _).2 hy
    simp only [G, Function.comp_apply]
    rw [hol_chartPt hV' _ _ hy', ev_secOf]
    exact (BoundedContinuousFunction.norm_coe_le_norm _ _).trans (hz n)
  obtain ⟨φ, h, hφ, -, hconv⟩ := (MMP.Gaga.cauchyTransform_runge_montel).2.2 N Ω' G hΩ' hG
    fun Q hQ _ => ⟨1, fun n y hy => hb n y (hQ hy)⟩
  let Q : Set (Fin N → ℂ) := e '' closure (Ωs r (J 0) J)
  have hQ : Q ⊆ Ω' := by
    rintro _ ⟨w, hw, rfl⟩
    show e.symm (e w) ∈ Ωs r' (J 0) J
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact closure_Ωs_subset hr hrr' (J 0) J hw
  have hQc : IsCompact Q := (isCompact_closure_Ωs ⟨0, rfl⟩).image e.continuous
  have hcs := (hconv Q hQ hQc).uniformCauchySeqOn
  refine ⟨φ, hφ, Metric.cauchySeq_iff.2 fun ε hε => ?_⟩
  obtain ⟨M, hM⟩ := Metric.uniformCauchySeqOn_iff.1 hcs (ε / 2) (by positivity)
  refine ⟨M, fun m hm n hn => lt_of_le_of_lt ?_ (half_lt_self hε)⟩
  rw [Subtype.dist_eq]
  refine (BoundedContinuousFunction.dist_le (by positivity)).2 fun x => ?_
  obtain ⟨w, hw, hx⟩ := eq_chartPt_of_mem_inter ⟨0, rfl⟩ x.2
  have hw' : chartPt (J 0) w ∈ CechCochains.inter (cov r') J := hx ▸ inter_mono hrr'.le J x.2
  have h1 := hM m hm n hn (e w) ⟨w, subset_closure hw, rfl⟩
  simp only [G, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] at h1
  rw [hol_chartPt hV' _ _ hw', hol_chartPt hV' _ _ hw', ev_secOf, ev_secOf] at h1
  have ex : (⟨x.1, inter_mono hrr'.le J x.2⟩ : CechCochains.inter (cov r') J) =
      ⟨chartPt (J 0) w, hw'⟩ := Subtype.ext hx.symm
  show dist ((z (φ m)).1 ⟨x.1, _⟩) ((z (φ n)).1 ⟨x.1, _⟩) ≤ ε / 2
  rw [ex]; exact h1.le

end Montel

/-! ### Free modules over holomorphic functions are coherent -/

section FreeCoherence

open OkaCoherence

variable {T : TopCat.{0}} {A : TopCat.Sheaf RingCat.{0} T}

/-- **A criterion for coherence of a free module.** If the relations among finitely many vectors
of `A^q` are locally finitely generated, the free module `A^q` is coherent. -/
private theorem isCoherentModule_free_of_relations {q : ℕ} (h : RelationsLocallyFinite A q) :
    IsCoherentModule (SheafOfModules.free (R := A) (Fin q)) := by
  refine ⟨MMP.isFiniteType_free (Fin q), fun V p σ => ?_⟩
  let M := SheafOfModules.free (R := A) (Fin q)
  let g := (M.over V).freeHomEquiv.symm σ
  choose F hF using fun i => MMP.exists_eq_sum_smul_freeSection (R := A) (op V)
    (secAt (σ i) (op (Over.mk (𝟙 V))))
  have hσZ : ∀ (Z : Over V) (i : Fin p), secAt (σ i) (op Z) =
      ∑ j, res Z.hom.le (F i j) • freeElt (R := A) j (op Z.left) := by
    intro Z i
    have h0 := PresheafOfModules.sections_property (σ i)
      (Over.homMk (U := Z) (V := Over.mk (𝟙 V)) Z.hom (by simp)).op
    refine h0.symm.trans ?_
    change M.val.map (homOfLE Z.hom.le).op (secAt (σ i) (op (Over.mk (𝟙 V)))) = _
    rw [hF i]
    exact OkaCoherence.free_map_sum_smul _ _
  have hg : ∀ (Z : Over V) (a : Fin p → A.obj.obj (op Z.left)),
      g.val.app (op Z) (∑ i, toOver Z (a i) • freeElt (R := A.over V) i (op Z)) =
        ∑ j, (∑ i, a i * res Z.hom.le (F i j)) • freeElt (R := A) j (op Z.left) := by
    intro Z a
    rw [OkaCoherence.freeHomEquiv_symm_app_sum]
    refine (Finset.sum_congr rfl fun i _ => congrArg _ (hσZ Z i)).trans ?_
    exact (free_sum_smul_eq_sum_smul _ a _ fun j => rfl).symm
  choose W hWV hxW s r hr hgen using fun x : V => h V p F x.1 x.2
  let Y : V → Over V := fun x => Over.mk (homOfLE (hWV x))
  refine isFiniteType_kernel_of_local g (Y := Y) ?_ (fun x => s x)
    (fun x k => ∑ i, toOver (Y x) (r x k i) •
      freeElt (R := A.over V) i (op (Y x))) (fun x k => ?_) ?_
  · intro U
    rw [GrothendieckTopology.mem_over_iff]
    intro y hy
    let x : V := ⟨y, U.hom.le hy⟩
    refine ⟨U.left ⊓ W x, homOfLE inf_le_left, ?_, ⟨hy, hxW x⟩⟩
    rw [Sieve.overEquiv_iff, Sieve.mem_ofObjects_iff]
    exact ⟨x, ⟨Over.homMk (homOfLE inf_le_right) (Subsingleton.elim _ _)⟩⟩
  · refine (hg (Y x) (r x k)).trans ?_
    exact Finset.sum_eq_zero fun j _ => by rw [hr x k j, zero_smul]; rfl
  · intro x Z z m hm
    obtain ⟨a, rfl⟩ := MMP.exists_eq_sum_smul_freeSection (op Z) m
    have hZW : Z.left ≤ W x := z.left.le
    let a' : Fin p → A.obj.obj (op Z.left) := a
    have hm' : ∀ j, ∑ i, a' i * res (hZW.trans (hWV x)) (F i j) = 0 := by
      have h0 : ∑ j, (∑ i, a' i * res Z.hom.le (F i j)) • freeElt (R := A) j (op Z.left) =
          ∑ j, (0 : A.obj.obj (op Z.left)) • freeElt (R := A) j (op Z.left) :=
        (hg Z a').symm.trans (hm.trans (by simp only [zero_smul, Finset.sum_const_zero]; rfl))
      exact fun j => coeff_eq_of_sum_smul_eq h0 j
    choose U' hU' hyU' c hc using hgen x Z.left hZW a' hm'
    let S : Sieve Z :=
      { arrows := fun W' _ => ∃ y : Z.left, W'.left ≤ U' y.1 y.2
        downward_closed := fun {W' W''} _ ⟨y, hy⟩ g => ⟨y, g.left.le.trans hy⟩ }
    refine ⟨S, ?_, ?_⟩
    · rw [GrothendieckTopology.mem_over_iff]
      intro y hy
      refine ⟨U' y hy, homOfLE (hU' y hy), ?_, hyU' y hy⟩
      rw [Sieve.overEquiv_iff]
      exact ⟨⟨y, hy⟩, le_rfl⟩
    · rintro W' φ ⟨⟨y, hy⟩, hle⟩
      refine ⟨fun k => toOver W' (res hle (c y hy k)),
        (OkaCoherence.free_map_sum_smul φ.op a).trans ?_⟩
      simp only [OkaCoherence.free_map_sum_smul]
      refine free_sum_smul_eq_sum_smul _ _ _ fun i => ?_
      have key := congrArg (res (A := A) hle) (hc y hy i)
      rw [OkaCoherence.res_res, OkaCoherence.res_sum] at key
      simp only [OkaCoherence.res_mul, OkaCoherence.res_res] at key
      exact key

end FreeCoherence

open OkaCoherence in
/-- The free modules `𝒪ᵖ` on an open subset of `ℂⁿ` are coherent (Oka). -/
private theorem isCoherentModule_free_holomorphic {n : ℕ} (U : Opens (EuclideanSpace ℂ (Fin n)))
    (p : ℕ) :
    IsCoherentModule (SheafOfModules.free (R := holomorphicRingCatSheaf n U) (Fin p)) :=
  isCoherentModule_free_of_relations
    (relationsLocallyFinite_of_one (relationsLocallyFinite_holomorphic n U) p)

/-! ### Lifting sections through a presentation -/

section Lifting

variable {X : TopCat.{0}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{0}}

/-- An element of `M` over the whole space, as a section. -/
private def topSection (M : SheafOfModules.{0} R) (x : M.val.obj (op ⊤)) : M.sections :=
  PresheafOfModules.sectionsMk (fun U => M.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op x)
    fun {U U'} f => by
      rw [← PresheafOfModules.map_comp_apply]; rfl

/-- The morphism `R^m ⟶ M` given by finitely many elements of `M` over the whole space. -/
private abbrev freeMap (M : SheafOfModules.{0} R) {m : ℕ} (t : Fin m → M.val.obj (op ⊤)) :
    SheafOfModules.free (R := R) (Fin m) ⟶ M :=
  M.freeHomEquiv.symm fun k => topSection M (t k)

private lemma freeMap_app_sum (M : SheafOfModules.{0} R) {m : ℕ} (t : Fin m → M.val.obj (op ⊤))
    (U : Opens X) (a : Fin m → R.obj.obj (op U)) :
    (freeMap M t).val.app (op U) (∑ k, a k •
      (show (SheafOfModules.free (R := R) (Fin m)).val.obj (op U) from
        (SheafOfModules.freeSection (R := R) k).1 (op U))) =
      ∑ k, a k • M.val.map (homOfLE (le_top : U ≤ ⊤)).op (t k) :=
  freeHomEquiv_symm_app_sum _ _ _

private lemma epi_freeMap (M : SheafOfModules.{0} R) {m : ℕ} (t : Fin m → M.val.obj (op ⊤))
    (ht : LocallyGenerates M t) : Epi (freeMap M t) := by
  refine OkaCoherence.epi_of_locally_surjective _ fun Z q => ?_
  obtain ⟨S, hS, hc⟩ := ht Z (homOfLE le_top) q
  refine ⟨S, hS, fun W f hf => ?_⟩
  obtain ⟨c, hc⟩ := hc W f hf
  exact ⟨_, (freeMap_app_sum M t W c).trans hc.symm⟩

attribute [local instance] globalSections_additive in
/-- **Lifting global sections.** If `t` locally generates `M` and the kernel of `R^m ⟶ M` has
no `H¹`, every global element of `M` is a combination of the `t k`. -/
private lemma exists_sum_eq_of_isZero (M : SheafOfModules.{0} R) {m : ℕ}
    (t : Fin m → M.val.obj (op ⊤)) (ht : LocallyGenerates M t)
    (hK : IsZero ((sheafCohomology X ((1 : ℕ) : ℤ)).obj
      ((SheafOfModules.toSheaf R).obj (kernel (freeMap M t)))))
    (x : M.val.obj (op ⊤)) : ∃ c : Fin m → R.obj.obj (op ⊤), x = ∑ k, c k • t k := by
  haveI := epi_freeMap M t ht
  haveI := CartanCompactBlocks.preservesFiniteColimits_toSheaf R
  have h1 := hK.of_iso ((sheafCohomologyIso X 1).app _).symm
  have h2 := CartanCompactBlocks.subsingleton_H'_of_isZero_rightDerived _ 0 h1
  obtain ⟨y, hy⟩ := CartanCompactBlocks.exists_lift_of_subsingleton_ext (X' := X)
    (SheafOfModules.toSheaf R) (freeMap M t) h2 x
  obtain ⟨c, hc⟩ := exists_eq_sum_smul_freeSection' (R := R) (op ⊤) y
  refine ⟨c, ?_⟩
  have hy' : (freeMap M t).val.app (op ⊤) y = x := hy
  rw [← hy', hc, freeMap_app_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  exact ConcreteCategory.congr_hom (M.val.map_id (op ⊤)) (t k)

end Lifting

/-! ### Presentations on the intersections -/

section ChartPresentations

variable {N : ℕ} (S : SheafOfModules.{0} (ringCatSheaf (sP N)))

private lemma functor_top_eq {r : ℝ} {p : ℕ} (J : Fin (p + 1) → Fin (N + 1)) :
    (isOpenEmbedding_chartMap (J 0) (Ωo r (J 0) J)).functor.obj ⊤ =
      CechCochains.inter (cov r) J := by
  ext x; constructor
  · rintro ⟨w, -, rfl⟩; exact (chartPt_mem_inter_iff r (J 0) J w.1).2 w.2
  · intro hx
    obtain ⟨w, hw, rfl⟩ := eq_chartPt_of_mem_inter ⟨0, rfl⟩ hx
    exact ⟨⟨w, hw⟩, trivial, rfl⟩

/-- **Lifting through a presentation.** If `g` locally generates `S` on `W ⊇ V^{(r)}_J`, every
section of `S` over `V^{(r)}_J` is a holomorphic combination of the `g k`: the kernel of the
presentation is coherent, hence acyclic on the graph domain `V^{(r)}_J`. -/
private theorem exists_lift (hS : IsCoherentModule S) {r : ℝ} {p : ℕ}
    (J : Fin (p + 1) → Fin (N + 1)) {W : Opens (space (sP N))} {m : ℕ}
    (g : Fin m → S.val.obj (op W)) (hg : LocallyGenerates S g)
    (hJW : CechCochains.inter (cov r) J ≤ W)
    (t : S.val.obj (op (CechCochains.inter (cov r) J))) :
    ∃ a : Fin m → (ringCatSheaf (sP N)).obj.obj (op (CechCochains.inter (cov r) J)),
      t = ∑ k, a k • resM S hJW (g k) := by
  have hFeq := functor_top_eq (r := r) J
  let Ω := Ωo r (J 0) J
  let F := (isOpenEmbedding_chartMap (J 0) Ω).functor
  let M := (SheafOfModules.pushforward (chartψ (J 0) Ω)).obj S
  have hM := isCoherentModule_chart S hS (J 0) Ω
  have hFW : F.obj ⊤ ≤ W := hFeq.le.trans hJW
  let t' : Fin m → M.val.obj (op ⊤) := fun k => resM S hFW (g k)
  have hg' : LocallyGenerates M t' :=
    locallyGenerates_pushforward (chartMap (J 0) Ω) F (fun V x hx => Set.mem_image_of_mem _ hx)
      (by rintro U V _ ⟨x, ⟨hxU, -⟩, rfl⟩; exact hxU) (chartψ (J 0) Ω)
      (fun V => (chartψ_bijective (J 0) Ω V).2) hg hFW
  have hker : IsCoherentModule (kernel (freeMap M t')) :=
    ((coherent_analytic_toolkit (n := N) (M := Ω)).1 (freeMap M t')
      (isCoherentModule_free_holomorphic Ω m) hM).1
  have hK := isZero_sheafCohomology_Ωo (J 0) J ⟨0, rfl⟩ _ hker ((1 : ℕ) : ℤ) (by norm_num)
  obtain ⟨c, hc⟩ := exists_sum_eq_of_isZero M t' hg' hK (resM S hFeq.le t)
  have hc' : resM S hFeq.le t = ∑ k, ψa F (chartψ (J 0) Ω) ⊤ (c k) • resM S hFW (g k) := hc
  refine ⟨fun k => resA hFeq.ge (ψa F (chartψ (J 0) Ω) ⊤ (c k)), ?_⟩
  rw [← resM_resM_self S hFeq.le hFeq.ge t, hc', resM_sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [resM_resM]

end ChartPresentations

/-! ### Relations are closed under uniform convergence -/

section Closedness

variable {N : ℕ} (S : SheafOfModules.{0} (ringCatSheaf (sP N)))

private lemma chartψ_valHom (α : Fin (N + 1)) (Y : Opens (EuclideanSpace ℂ (Fin N)))
    (V : Opens (TopCat.of Y))
    (s : sections (sP N) ((isOpenEmbedding_chartMap α Y).functor.obj V)) :
    ψa (isOpenEmbedding_chartMap α Y).functor (chartψ α Y) V (valHom α Y V s) = s :=
  (RingEquiv.ofBijective (valHom α Y V) (valHom_bijective α Y V)).symm_apply_apply s

/-- The scalar action on the pushforward of `S` along a chart, through `valHom`. -/
private lemma valHom_smul_pushforward (α : Fin (N + 1)) (Y : Opens (EuclideanSpace ℂ (Fin N)))
    (c : sections (sP N) ((isOpenEmbedding_chartMap α Y).functor.obj ⊤))
    (t : ((SheafOfModules.pushforward (chartψ α Y)).obj S).val.obj (op ⊤)) :
    (show ((SheafOfModules.pushforward (chartψ α Y)).obj S).val.obj (op ⊤) from
      (show (holomorphicRingCatSheaf N Y).obj.obj (op ⊤) from valHom α Y ⊤ c) • t) =
      (show S.val.obj (op ((isOpenEmbedding_chartMap α Y).functor.obj ⊤)) from
        (show (ringCatSheaf (sP N)).obj.obj
            (op ((isOpenEmbedding_chartMap α Y).functor.obj ⊤)) from c) •
          (show S.val.obj (op ((isOpenEmbedding_chartMap α Y).functor.obj ⊤)) from t)) :=
  congrArg (· • (show S.val.obj (op ((isOpenEmbedding_chartMap α Y).functor.obj ⊤)) from t))
    (chartψ_valHom α Y ⊤ c)

private lemma freeMap_chartψ_sum (α : Fin (N + 1)) (Y : Opens (EuclideanSpace ℂ (Fin N))) {m : ℕ}
    (t' : Fin m → ((SheafOfModules.pushforward (chartψ α Y)).obj S).val.obj (op ⊤))
    (c : Fin m → sections (sP N) ((isOpenEmbedding_chartMap α Y).functor.obj ⊤)) :
    (freeMap ((SheafOfModules.pushforward (chartψ α Y)).obj S) t').val.app (op ⊤)
      (∑ k, (show (holomorphicRingCatSheaf N Y).obj.obj (op ⊤) from valHom α Y ⊤ (c k)) •
          (show (SheafOfModules.free (R := holomorphicRingCatSheaf N Y) (Fin m)).val.obj (op ⊤)
            from (SheafOfModules.freeSection (R := holomorphicRingCatSheaf N Y) k).1 (op ⊤))) =
      (show S.val.obj (op ((isOpenEmbedding_chartMap α Y).functor.obj ⊤)) from
        ∑ k, (show (ringCatSheaf (sP N)).obj.obj
            (op ((isOpenEmbedding_chartMap α Y).functor.obj ⊤)) from c k) •
          (show S.val.obj (op ((isOpenEmbedding_chartMap α Y).functor.obj ⊤)) from t' k)) := by
  rw [freeMap_app_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e1 : ((SheafOfModules.pushforward (chartψ α Y)).obj S).val.map
      (homOfLE (le_top : (⊤ : Opens (TopCat.of Y)) ≤ ⊤)).op (t' k) = t' k :=
    ConcreteCategory.congr_hom
      (((SheafOfModules.pushforward (chartψ α Y)).obj S).val.map_id (op ⊤)) (t' k)
  exact (congrArg (fun u => (show (holomorphicRingCatSheaf N Y).obj.obj (op ⊤) from
    valHom α Y ⊤ (c k)) • u) e1).trans (valHom_smul_pushforward S α Y (c k) (t' k))

private lemma valHom_restrictHom_top {r : ℝ} {p : ℕ} (J : Fin (p + 1) → Fin (N + 1))
    (c : sections (sP N) (CechCochains.inter (cov r) J))
    (y : (⊤ : Opens (TopCat.of (Ωo r (J 0) J)))) :
    (valHom (J 0) (Ωo r (J 0) J) ⊤ (restrictHom (functor_top_eq (r := r) J).le c) : _ → ℂ) y =
      ev c ⟨chartPt (J 0) y.1.1, (chartPt_mem_inter_iff r (J 0) J y.1.1).2 y.1.2⟩ :=
  (valHom_apply _ _ _ _ _).trans ((ev_eq _ _ _ _).symm.trans (ev_restrict _ _ _))

/-- **Closedness of relations.** For finitely many sections `t k` of `S` over `V^{(r)}_J`, the
coefficient vectors `a` with `∑ a k • t k = 0` are closed under uniform convergence on
`V^{(r)}_J`. -/
private theorem sum_smul_eq_zero_of_tendstoUniformly (hS : IsCoherentModule S) {r : ℝ} {p : ℕ}
    (J : Fin (p + 1) → Fin (N + 1)) {m : ℕ}
    (t : Fin m → S.val.obj (op (CechCochains.inter (cov r) J)))
    (a : ℕ → Fin m → sections (sP N) (CechCochains.inter (cov r) J))
    (b : Fin m → sections (sP N) (CechCochains.inter (cov r) J))
    (ha : ∀ n, ∑ k, (show (ringCatSheaf (sP N)).obj.obj (op (CechCochains.inter (cov r) J))
      from a n k) • t k = 0)
    (hconv : ∀ k, TendstoUniformly (fun n x => ev (a n k) x) (fun x => ev (b k) x)
      Filter.atTop) :
    ∑ k, (show (ringCatSheaf (sP N)).obj.obj (op (CechCochains.inter (cov r) J)) from b k) •
      t k = 0 := by
  have hFeq := functor_top_eq (r := r) J
  let Ω := Ωo r (J 0) J
  let F := (isOpenEmbedding_chartMap (J 0) Ω).functor
  let M := (SheafOfModules.pushforward (chartψ (J 0) Ω)).obj S
  have hM := isCoherentModule_chart S hS (J 0) Ω
  let t' : Fin m → M.val.obj (op ⊤) := fun k => resM S hFeq.le (t k)
  let ε := freeMap M t'
  have hR : IsCoherentModule (kernel ε) :=
    ((coherent_analytic_toolkit (n := N) (M := Ω)).1 ε
      (isCoherentModule_free_holomorphic Ω m) hM).1
  have key : ∀ c : Fin m → sections (sP N) (F.obj ⊤),
      ε.val.app (op ⊤) (∑ k, (show (holomorphicRingCatSheaf N Ω).obj.obj (op ⊤) from
        valHom (J 0) Ω ⊤ (c k)) •
          (show (SheafOfModules.free (R := holomorphicRingCatSheaf N Ω) (Fin m)).val.obj (op ⊤)
            from (SheafOfModules.freeSection (R := holomorphicRingCatSheaf N Ω) k).1 (op ⊤))) =
        (show S.val.obj (op (F.obj ⊤)) from
          ∑ k, (show (ringCatSheaf (sP N)).obj.obj (op (F.obj ⊤)) from c k) •
            (show S.val.obj (op (F.obj ⊤)) from t' k)) :=
    freeMap_chartψ_sum S (J 0) Ω t'
  have hres : ∀ c : Fin m → sections (sP N) (CechCochains.inter (cov r) J),
      (show S.val.obj (op (F.obj ⊤)) from ∑ k, (show (ringCatSheaf (sP N)).obj.obj
        (op (F.obj ⊤)) from restrictHom hFeq.le (c k)) •
          (show S.val.obj (op (F.obj ⊤)) from t' k)) =
        resM S hFeq.le (∑ k, (show (ringCatSheaf (sP N)).obj.obj
          (op (CechCochains.inter (cov r) J)) from c k) • t k) :=
    fun c => (resM_sum_smul S hFeq.le (fun k => c k) t).symm
  let pt : (⊤ : Opens (TopCat.of Ω)) → CechCochains.inter (cov r) J := fun y =>
    ⟨chartPt (J 0) y.1.1, (chartPt_mem_inter_iff r (J 0) J y.1.1).2 y.1.2⟩
  have hval : ∀ (c : sections (sP N) (CechCochains.inter (cov r) J))
      (y : (⊤ : Opens (TopCat.of Ω))),
      (valHom (J 0) Ω ⊤ (restrictHom hFeq.le c) : _ → ℂ) y = ev c (pt y) :=
    valHom_restrictHom_top J
  obtain ⟨r', hr'⟩ := (coherent_analytic_toolkit (n := N) (M := Ω)).2.2.2.2.2.2 m (kernel ε)
    (kernel.ι ε) hR ⊤ (fun n k => valHom (J 0) Ω ⊤ (restrictHom hFeq.le (a n k)))
    (fun k => valHom (J 0) Ω ⊤ (restrictHom hFeq.le (b k)))
    (fun n => OkaCoherence.exists_kernel_ι_app_eq ε (op ⊤) _ (by
      rw [key, hres, ha n, resM_zero]; rfl))
    (fun k K _ => by
      have h1 := (hconv k).comp pt
      refine (h1.tendstoUniformlyOn (s := K)).congr_right ?_ |>.congr ?_
      · intro y _; exact (hval (b k) y).symm
      · exact Filter.Eventually.of_forall fun n y _ => (hval (a n k) y).symm)
  have h0 := OkaCoherence.kernel_condition_app ε (op ⊤) r'
  rw [hr', key, hres] at h0
  rw [← resM_resM_self S hFeq.le hFeq.ge (∑ k, _), h0]
  exact map_zero _

end Closedness

/-! ### Classes of cocycles of a cochain complex of abelian groups -/

section CechClasses

variable (K : CochainComplex AddCommGrpCat.{0} ℕ) (q : ℕ)

/-- The cycle with underlying cochain `x`. -/
private def cyc (x : K.X q) (hx : K.d q (q + 1) x = 0) : K.cycles q :=
  (K.sc q).abCyclesIso.inv ⟨x, by
    change (K.d q ((ComplexShape.up ℕ).next q)) x = 0
    rw [CochainComplex.next ℕ q]; exact hx⟩

private lemma iCycles_cyc (x : K.X q) (hx : K.d q (q + 1) x = 0) :
    K.iCycles q (cyc K q x hx) = x :=
  (K.sc q).abCyclesIso_inv_apply_iCycles _

private lemma iCycles_injective : Function.Injective (K.iCycles q) :=
  (AddCommGrpCat.mono_iff_injective _).1 inferInstance

private lemma d_iCycles (z : K.cycles q) : K.d q (q + 1) (K.iCycles q z) = 0 := by
  rw [← ConcreteCategory.comp_apply, K.iCycles_d]; rfl

/-- The cohomology class of a cocycle. -/
private def cls (x : K.X q) (hx : K.d q (q + 1) x = 0) : K.homology q :=
  K.homologyπ q (cyc K q x hx)

private lemma cls_surjective (y : K.homology q) : ∃ x hx, cls K q x hx = y := by
  obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective _).1
    (inferInstance : Epi (K.homologyπ q)) y
  refine ⟨K.iCycles q z, d_iCycles K q z, ?_⟩
  unfold cls; congr 1; exact iCycles_injective K q (iCycles_cyc K q _ _)

private lemma cls_add (x x' : K.X q) (hx : K.d q (q + 1) x = 0) (hx' : K.d q (q + 1) x' = 0)
    (hxx' : K.d q (q + 1) (x + x') = 0) :
    cls K q (x + x') hxx' = cls K q x hx + cls K q x' hx' := by
  unfold cls; rw [← map_add]; congr 1; apply iCycles_injective
  rw [map_add, iCycles_cyc, iCycles_cyc, iCycles_cyc]

private lemma cls_eq_zero_iff (i : ℕ) (hi : (ComplexShape.up ℕ).prev q = i) (x : K.X q)
    (hx : K.d q (q + 1) x = 0) : cls K q x hx = 0 ↔ ∃ c, K.d i q c = x := by
  have hT := (ShortComplex.mk (K.toCycles i q) (K.homologyπ q) (by simp)).exact_of_g_is_cokernel
    (K.homologyIsCokernel i q hi)
  rw [ShortComplex.ab_exact_iff] at hT
  constructor
  · intro h
    obtain ⟨c, hc⟩ := hT _ h
    refine ⟨c, ?_⟩
    have := congrArg (K.iCycles q) hc
    rwa [iCycles_cyc, ← ConcreteCategory.comp_apply, K.toCycles_i] at this
  · rintro ⟨c, rfl⟩
    have : cyc K q (K.d i q c) hx = K.toCycles i q c := by
      apply iCycles_injective
      rw [iCycles_cyc, ← ConcreteCategory.comp_apply, K.toCycles_i]
    unfold cls; rw [this, ← ConcreteCategory.comp_apply, K.toCycles_comp_homologyπ]; rfl

private lemma homologyMap_cls {K L : CochainComplex AddCommGrpCat.{0} ℕ} (χ : K ⟶ L)
    (x : K.X q) (hx : K.d q (q + 1) x = 0) (hx' : L.d q (q + 1) (χ.f q x) = 0) :
    HomologicalComplex.homologyMap χ q (cls K q x hx) = cls L q (χ.f q x) hx' := by
  unfold cls
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply]
  congr 1; apply iCycles_injective
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply,
    iCycles_cyc, iCycles_cyc]

end CechClasses

/-! ### Restriction to a smaller cover, and postcomposition, on ordered Čech complexes -/

section CechMaps

open CechCochains

variable {T : TopCat.{0}} {I : Type} [LinearOrder I]

private lemma inter_mono' {U U' : I → Opens T} (h : ∀ i, U' i ≤ U i) {p : ℕ} (J : Fin p → I) :
    inter U' J ≤ inter U J := iInf_mono fun k => h (J k)

/-- Restriction of ordered Čech cochains to a cover with smaller members and the same indices. -/
private def ordRes (U U' : I → Opens T) (h : ∀ i, U' i ≤ U i)
    (A : TopCat.Presheaf AddCommGrpCat.{0} T) :
    Stacks.Cech.orderedCechComplex U A ⟶ Stacks.Cech.orderedCechComplex U' A where
  f p := AddCommGrpCat.ofHom
    { toFun := fun c J => restr A (inter_mono' h J.1) (c J)
      map_zero' := by funext J; exact map_zero _
      map_add' := fun c d => by funext J; exact map_add _ _ _ }
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [Stacks.Cech.orderedCechComplex_d, Stacks.Cech.orderedCechComplex_d]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro c
    funext J
    change ∑ k : Fin (i + 2), ((-1 : ℤ) ^ (k : ℕ)) • restr A (inter_le_omit U' J.1 k)
        (restr A (inter_mono' h (J.1 ∘ k.succAbove))
          (c ⟨J.1 ∘ k.succAbove, strictMono_omit J.2 k⟩)) =
      restr A (inter_mono' h J.1) (∑ k : Fin (i + 2), ((-1 : ℤ) ^ (k : ℕ)) •
        restr A (inter_le_omit U J.1 k) (c ⟨J.1 ∘ k.succAbove, strictMono_omit J.2 k⟩))
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, restr_restr, restr_restr]

/-- Postcomposition of ordered Čech cochains with a map of presheaves. -/
private def ordPost (U : I → Opens T) {A A' : TopCat.Presheaf AddCommGrpCat.{0} T}
    (φ : A ⟶ A') :
    Stacks.Cech.orderedCechComplex U A ⟶ Stacks.Cech.orderedCechComplex U A' where
  f p := AddCommGrpCat.ofHom
    { toFun := fun c J => (φ.app _).hom (c J)
      map_zero' := by funext J; exact map_zero _
      map_add' := fun c d => by funext J; exact map_add _ _ _ }
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [Stacks.Cech.orderedCechComplex_d, Stacks.Cech.orderedCechComplex_d]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro c
    funext J
    change ∑ k : Fin (i + 2), ((-1 : ℤ) ^ (k : ℕ)) • restr A' (inter_le_omit U J.1 k)
        ((φ.app _).hom (c ⟨J.1 ∘ k.succAbove, strictMono_omit J.2 k⟩)) =
      (φ.app _).hom (∑ k : Fin (i + 2), ((-1 : ℤ) ^ (k : ℕ)) •
        restr A (inter_le_omit U J.1 k) (c ⟨J.1 ∘ k.succAbove, strictMono_omit J.2 k⟩))
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul]
    congr 1
    exact (ConcreteCategory.congr_hom (φ.naturality (homOfLE (inter_le_omit U J.1 k)).op) _).symm

end CechMaps

/-! ### Classes of Čech cocycles of the covers in `H^q((ℙᴺ)^an, 𝒮)` -/

section LerayClasses

variable {N : ℕ} {S : SheafOfModules.{0} (ringCatSheaf (sP N))} (hS : IsCoherentModule S)

variable (S) in
/-- The ordered Čech complex of `S` for the cover `V^{(r)}`. -/
private abbrev KC (r : ℝ) : CochainComplex AddCommGrpCat.{0} ℕ :=
  Stacks.Cech.orderedCechComplex (cov (N := N) r) (Ssh S).obj

/-- The Leray isomorphism of the cover `V^{(r)}`. -/
private def lerayIsoCov {r : ℝ} (hr : 1 < r) (q : ℕ) :
    (KC S r).homology q ≅ (sheafCohomology (space (sP N)) q).obj (Ssh S) :=
  Classical.choose LerayData (Fin (N + 1)) (space (sP N)) (cov r) (Ssh S) (iSup_cov hr)
    (fun _ J q hq => isZero_inter S hS r J q hq) q

/-- The class in `H^q((ℙᴺ)^an, 𝒮)` of a Čech cocycle of `V^{(r)}`. -/
private def cl {r : ℝ} (hr : 1 < r) {q : ℕ} (x : (KC S r).X q)
    (hx : (KC S r).d q (q + 1) x = 0) : (sheafCohomology (space (sP N)) q).obj (Ssh S) :=
  (lerayIsoCov hS hr q).hom (cls (KC S r) q x hx)

private lemma cl_surjective {r : ℝ} (hr : 1 < r) {q : ℕ}
    (y : (sheafCohomology (space (sP N)) q).obj (Ssh S)) : ∃ x hx, cl hS hr x hx = y := by
  obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso (lerayIsoCov hS hr q).hom).2 y
  obtain ⟨x, hx, rfl⟩ := cls_surjective (KC S r) q z
  exact ⟨x, hx, rfl⟩

private lemma cl_add {r : ℝ} (hr : 1 < r) {q : ℕ} (x x' : (KC S r).X q)
    (hx : (KC S r).d q (q + 1) x = 0) (hx' : (KC S r).d q (q + 1) x' = 0)
    (hxx' : (KC S r).d q (q + 1) (x + x') = 0) :
    cl hS hr (x + x') hxx' = cl hS hr x hx + cl hS hr x' hx' := by
  unfold cl; rw [cls_add (KC S r) q x x' hx hx', map_add]

private lemma cl_congr {r : ℝ} (hr : 1 < r) {q : ℕ} {x x' : (KC S r).X q} (h : x = x')
    (hx : (KC S r).d q (q + 1) x = 0) (hx' : (KC S r).d q (q + 1) x' = 0) :
    cl hS hr x hx = cl hS hr x' hx' := by
  subst h; rfl

private lemma cl_eq_zero_iff {r : ℝ} (hr : 1 < r) {q : ℕ} (i : ℕ)
    (hi : (ComplexShape.up ℕ).prev q = i) (x : (KC S r).X q)
    (hx : (KC S r).d q (q + 1) x = 0) : cl hS hr x hx = 0 ↔ ∃ c, (KC S r).d i q c = x := by
  rw [← cls_eq_zero_iff (KC S r) q i hi x hx]
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (lerayIsoCov hS hr q).hom).1

private lemma cl_res {r r' : ℝ} (hr : 1 < r) (hr' : 1 < r') (h : r' ≤ r) {q : ℕ}
    (x : (KC S r).X q) (hx : (KC S r).d q (q + 1) x = 0)
    (hx' : (KC S r').d q (q + 1)
      ((ordRes (cov r) (cov r') (fun α => cov_mono h α) (Ssh S).obj).f q x) = 0) :
    cl hS hr' ((ordRes (cov r) (cov r') (fun α => cov_mono h α) (Ssh S).obj).f q x) hx' =
      cl hS hr x hx := by
  have key := (Classical.choose_spec LerayData).2.1 (Fin (N + 1)) (Fin (N + 1)) (space (sP N))
    (cov r) (cov r') (iSup_cov hr) (iSup_cov hr') id monotone_id (fun α => cov_mono h α)
    (Ssh S) (fun _ J q hq => isZero_inter S hS r J q hq)
    (fun _ J q hq => isZero_inter S hS r' J q hq)
    (ordRes (cov r) (cov r') (fun α => cov_mono h α) (Ssh S).obj)
    (fun _ _ _ _ _ => rfl) (fun _ _ J hJ => absurd J.2 hJ) q
  unfold cl
  rw [← homologyMap_cls q _ x hx hx']
  exact ConcreteCategory.congr_hom key (cls (KC S r) q x hx)

private lemma cl_post {r : ℝ} (hr : 1 < r) {q : ℕ} (φ : Ssh S ⟶ Ssh S) (x : (KC S r).X q)
    (hx : (KC S r).d q (q + 1) x = 0)
    (hx' : (KC S r).d q (q + 1) ((ordPost (cov r) φ.hom).f q x) = 0) :
    cl hS hr ((ordPost (cov r) φ.hom).f q x) hx' =
      (sheafCohomology (space (sP N)) q).map φ (cl hS hr x hx) := by
  have key := (Classical.choose_spec LerayData).1 (Fin (N + 1)) (space (sP N)) (cov r)
    (iSup_cov hr) (Ssh S) (Ssh S) (fun _ J q hq => isZero_inter S hS r J q hq)
    (fun _ J q hq => isZero_inter S hS r J q hq) φ (ordPost (cov r) φ.hom)
    (fun _ _ _ => rfl) q
  unfold cl
  rw [← homologyMap_cls q _ x hx hx']
  exact ConcreteCategory.congr_hom key (cls (KC S r) q x hx)

end LerayClasses

/-! ### Multiplication by constants -/

section Constants

variable {N : ℕ} (S : SheafOfModules.{0} (ringCatSheaf (sP N)))

private lemma resA_constSec {V V' : Opens (space (sP N))} (h : V' ≤ V) (a : ℂ) :
    resA (A := ringCatSheaf (sP N)) h (constSec V a) = constSec V' a := by
  show (ringCatSheaf (sP N)).obj.map (homOfLE h).op
      ((ringCatSheaf (sP N)).obj.map (homOfLE (le_top : V ≤ ⊤)).op _) =
    (ringCatSheaf (sP N)).obj.map (homOfLE (le_top : V' ≤ ⊤)).op _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Multiplication by the constant `a`, on the underlying abelian presheaf of `S`. -/
private def mulC (a : ℂ) : (Ssh S).obj ⟶ (Ssh S).obj where
  app V := AddCommGrpCat.ofHom
    { toFun := fun y : S.val.obj V =>
        (show (ringCatSheaf (sP N)).obj.obj V from constSec V.unop a) • y
      map_zero' := smul_zero _
      map_add' := smul_add _ }
  naturality V V' i := by
    ext y
    change (show (ringCatSheaf (sP N)).obj.obj V' from constSec V'.unop a) • resM S i.unop.le y =
      resM S i.unop.le ((show (ringCatSheaf (sP N)).obj.obj V from constSec V.unop a) •
        (show S.val.obj V from y))
    rw [resM_smul, resA_constSec]

end Constants

/-! ### Presentations of `S` near the closed boxes -/

section Presentations

variable {N : ℕ} (S : SheafOfModules.{0} (ringCatSheaf (sP N)))

/-- Adding zero generators preserves local generation. -/
private lemma locallyGenerates_pad {T : TopCat.{0}}
    {A : Sheaf (Opens.grothendieckTopology T) RingCat.{0}} (M : SheafOfModules.{0} A)
    {W : Opens T} {m P : ℕ} (hmP : m ≤ P) (g : Fin m → M.val.obj (op W))
    (hg : LocallyGenerates M g) :
    LocallyGenerates M (fun j : Fin P => if h : (j : ℕ) < m then g ⟨j, h⟩ else 0) := by
  refine locallyGenerates_of_nhds _ fun U hU t y hy => ?_
  obtain ⟨U', h, hy', c, hc⟩ := hg.exists_nhds hU t hy
  refine ⟨U', h, hy', fun j => if h : (j : ℕ) < m then c ⟨j, h⟩ else 0, ?_⟩
  rw [hc]
  refine Fintype.sum_of_injective (Fin.castLE hmP) (Fin.castLE_injective hmP) _ _
    (fun j hj => ?_) (fun k => ?_)
  · have hj' : ¬ (j : ℕ) < m := fun h' => hj ⟨⟨j, h'⟩, rfl⟩
    simp only [dif_neg hj', zero_smul]
  · have hk : ((Fin.castLE hmP k : Fin P) : ℕ) < m := k.2
    simp only [dif_pos hk]
    rfl

/-- Local generation of the module read on a chart gives local generation of `S`. -/
private lemma locallyGenerates_of_chart (α : Fin (N + 1)) (Y : Opens (EuclideanSpace ℂ (Fin N)))
    {W : Opens (TopCat.of Y)} {m : ℕ}
    (g : Fin m → ((SheafOfModules.pushforward (chartψ α Y)).obj S).val.obj (op W))
    (hg : LocallyGenerates ((SheafOfModules.pushforward (chartψ α Y)).obj S) g) :
    LocallyGenerates S (fun k => (show S.val.obj
      (op ((isOpenEmbedding_chartMap α Y).functor.obj W)) from g k)) := by
  let F := (isOpenEmbedding_chartMap α Y).functor
  let M := (SheafOfModules.pushforward (chartψ α Y)).obj S
  refine locallyGenerates_of_nhds _ fun U hU t y hy => ?_
  obtain ⟨v, -, rfl⟩ := hU hy
  let U' : Opens (TopCat.of Y) := (Opens.map (chartMap α Y)).obj U
  have hU'W : U' ≤ W := fun v' hv' => by
    obtain ⟨w, hw, he⟩ := hU hv'
    rwa [(isOpenEmbedding_chartMap α Y).injective he] at hw
  have hFU : F.obj U' ≤ U := by rintro _ ⟨w, hw, rfl⟩; exact hw
  obtain ⟨U₁', h₁, hv₁, c, hc⟩ := hg.exists_nhds hU'W
    (show M.val.obj (op U') from resM S hFU t) (y := v) hy
  refine ⟨F.obj U₁', (fmono F h₁).trans hFU, ⟨v, hv₁, rfl⟩,
    fun k => ψa F (chartψ α Y) U₁' (c k), ?_⟩
  rw [← resM_resM S hFU (fmono F h₁) t]
  exact hc

/-- **Theorem A near a closed box.** `S` is locally generated by finitely many sections over an
open neighbourhood of `V^{(5)}_α`. -/
private lemma exists_presentation (hS : IsCoherentModule S) (α : Fin (N + 1)) :
    ∃ (W : Opens (space (sP N))) (_ : cov 5 α ≤ W) (m : ℕ) (g : Fin m → S.val.obj (op W)),
      LocallyGenerates S g := by
  let Y : Opens (EuclideanSpace ℂ (Fin N)) := ⊤
  let M := (SheafOfModules.pushforward (chartψ α Y)).obj S
  have hM := isCoherentModule_chart S hS α Y
  obtain ⟨-, ⟨W, hKW, m, f, hf⟩, -⟩ := cartan_compact_blocks Y (fun _ => -5) (fun _ => 5)
    (fun _ => -5) (fun _ => 5) (fun _ _ => trivial) M hM
  let G : (M.over W).GeneratingSections :=
    ⟨Fin m, (M.over W).freeHomEquiv f, by rw [Equiv.symm_apply_apply]; exact hf⟩
  have hG := locallyGenerates_of_generatingSections M G (Equiv.refl _)
  refine ⟨(isOpenEmbedding_chartMap α Y).functor.obj W, ?_, m, _,
    locallyGenerates_of_chart S α Y _ hG⟩
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨⟨w, trivial⟩, hKW (box_subset_cbox 5 hw), rfl⟩

/-- Presentations of `S` near all the closed boxes `V^{(5)}_α`, with the same number of
generators. -/
private structure Pres where
  /-- The number of generators. -/
  P : ℕ
  /-- The open on which the generators of the `α`-th presentation live. -/
  W : Fin (N + 1) → Opens (space (sP N))
  hW : ∀ α, cov 5 α ≤ W α
  /-- The generators of the `α`-th presentation. -/
  g : ∀ α, Fin P → S.val.obj (op (W α))
  hg : ∀ α, LocallyGenerates S (g α)

private lemma nonempty_pres (hS : IsCoherentModule S) : Nonempty (Pres S) := by
  choose W hW m g hg using exists_presentation S hS
  have hmP : ∀ α, m α ≤ Finset.univ.sup m := fun α => Finset.le_sup (Finset.mem_univ α)
  exact ⟨⟨Finset.univ.sup m, W, hW,
    fun α j => if h : (j : ℕ) < m α then g α ⟨j, h⟩ else 0,
    fun α => locallyGenerates_pad S (hmP α) (g α) (hg α)⟩⟩

end Presentations

/-! ### Banach spaces of bounded coefficient cochains -/

section BanachCochains

private lemma le25 : (2 : ℝ) ≤ 5 := by norm_num
private lemma le35 : (3 : ℝ) ≤ 5 := by norm_num
private lemma le45 : (4 : ℝ) ≤ 5 := by norm_num
private lemma le23 : (2 : ℝ) ≤ 3 := by norm_num
private lemma le34 : (3 : ℝ) ≤ 4 := by norm_num
private lemma lt12 : (1 : ℝ) < 2 := by norm_num
private lemma lt13 : (1 : ℝ) < 3 := by norm_num
private lemma lt15 : (1 : ℝ) < 5 := by norm_num

variable {N : ℕ} {S : SheafOfModules.{0} (ringCatSheaf (sP N))} (Q : Pres S)

/-- The ordered tuples of indices form a finite type. -/
@[instance_reducible]
private def fintypeOrdIndex (p : ℕ) : Fintype (CechCochains.OrdIndex (I := Fin (N + 1)) p) :=
  Fintype.ofFinite _

attribute [local instance] fintypeOrdIndex

private lemma completeSpace_BH_inter {r : ℝ} {p : ℕ} (J : Fin (p + 1) → Fin (N + 1)) :
    CompleteSpace (BH (CechCochains.inter (cov (N := N) r) J)) :=
  completeSpace_BH (mem_chart_of_mem_inter J)

attribute [local instance] completeSpace_BH_inter

variable (N) in
/-- Bounded holomorphic coefficient vectors, for the presentations of all the indices of each
tuple, of a degree-`p` cochain of `V^{(r)}`. -/
private abbrev BC (P : ℕ) (r : ℝ) (p : ℕ) : Type :=
  ∀ J : CechCochains.OrdIndex (I := Fin (N + 1)) p,
    Fin (p + 1) × Fin P → BH (CechCochains.inter (cov (N := N) r) J.1)

private lemma resM_fsum {T : TopCat.{0}} {A : Sheaf (Opens.grothendieckTopology T) RingCat.{0}}
    (M : SheafOfModules.{0} A) {U U' : Opens T} (h : U' ≤ U) {ι : Type*} [Fintype ι]
    (t : ι → M.val.obj (op U)) : resM M h (∑ i, t i) = ∑ i, resM M h (t i) :=
  map_sum (M.val.map (homOfLE h).op).hom t _

private lemma inter_le_cov {r : ℝ} {p : ℕ} (J : Fin p → Fin (N + 1)) (k : Fin p) :
    CechCochains.inter (cov (N := N) r) J ≤ cov r (J k) := fun x hx => (mem_inter_iff J x).1 hx k

/-- The `j`-th generator of the presentation of the `k`-th index of `J`, on `V^{(r)}_J`. -/
private def gen {r : ℝ} (hr : r ≤ 5) {p : ℕ} (J : Fin (p + 1) → Fin (N + 1)) (k : Fin (p + 1))
    (j : Fin Q.P) : S.val.obj (op (CechCochains.inter (cov r) J)) :=
  resM S ((inter_le_cov J k).trans ((cov_mono hr _).trans (Q.hW (J k)))) (Q.g (J k) j)

variable (S) in
/-- A bounded holomorphic function times a section of `S`. -/
private abbrev bsmul {V : Opens (space (sP N))} (a : BH V) (t : S.val.obj (op V)) :
    S.val.obj (op V) :=
  (show (ringCatSheaf (sP N)).obj.obj (op V) from secOf a) • t

/-- The Čech cochain represented by bounded coefficient vectors. -/
private def rep {r : ℝ} (hr : r ≤ 5) {p : ℕ} (x : BC N Q.P r p) : (KC S r).X p :=
  fun J => ∑ kj : Fin (p + 1) × Fin Q.P, bsmul S (x J kj) (gen Q hr J.1 kj.1 kj.2)

private lemma rep_add {r : ℝ} (hr : r ≤ 5) {p : ℕ} (x y : BC N Q.P r p) :
    rep Q hr (x + y) = rep Q hr x + rep Q hr y := by
  funext J
  change ∑ kj : Fin (p + 1) × Fin Q.P, bsmul S (x J kj + y J kj) (gen Q hr J.1 kj.1 kj.2) =
    ∑ kj : Fin (p + 1) × Fin Q.P, bsmul S (x J kj) (gen Q hr J.1 kj.1 kj.2) +
      ∑ kj : Fin (p + 1) × Fin Q.P, bsmul S (y J kj) (gen Q hr J.1 kj.1 kj.2)
  refine Eq.trans (Finset.sum_congr rfl fun kj _ => ?_) Finset.sum_add_distrib
  exact (congrArg (fun s : sections (sP N) (CechCochains.inter (cov r) J.1) =>
    (show (ringCatSheaf (sP N)).obj.obj (op (CechCochains.inter (cov r) J.1)) from s) •
      gen Q hr J.1 kj.1 kj.2)
      (secOf_add (mem_chart_of_mem_inter J.1) _ _)).trans
    (add_smul (R := (ringCatSheaf (sP N) : Sheaf (Opens.grothendieckTopology (space (sP N)))
      RingCat.{0}).obj.obj (op (CechCochains.inter (cov r) J.1))) _ _ _)

private lemma rep_zero {r : ℝ} (hr : r ≤ 5) {p : ℕ} : rep Q hr (0 : BC N Q.P r p) = 0 := by
  have h := rep_add Q hr (0 : BC N Q.P r p) 0
  rw [add_zero] at h
  exact add_eq_left.1 h.symm

private lemma rep_smul {r : ℝ} (hr : r ≤ 5) {p : ℕ} (a : ℂ) (x : BC N Q.P r p) :
    rep Q hr (a • x) = (ordPost (cov r) (mulC S a)).f p (rep Q hr x) := by
  funext J
  change ∑ kj : Fin (p + 1) × Fin Q.P, bsmul S (a • x J kj) (gen Q hr J.1 kj.1 kj.2) =
    (show (ringCatSheaf (sP N)).obj.obj (op (CechCochains.inter (cov r) J.1)) from
      constSec (CechCochains.inter (cov r) J.1) a) •
      ∑ kj : Fin (p + 1) × Fin Q.P, bsmul S (x J kj) (gen Q hr J.1 kj.1 kj.2)
  refine Eq.trans (Finset.sum_congr rfl fun kj _ => ?_) Finset.smul_sum.symm
  exact (congrArg (fun s : sections (sP N) (CechCochains.inter (cov r) J.1) =>
    (show (ringCatSheaf (sP N)).obj.obj (op (CechCochains.inter (cov r) J.1)) from s) •
      gen Q hr J.1 kj.1 kj.2)
      (secOf_smul (mem_chart_of_mem_inter J.1) a _)).trans (mul_smul _ _ _)

/-- Restriction of bounded coefficient vectors to a smaller cover. -/
private def resE {r r' : ℝ} (h : r' ≤ r) (p : ℕ) : BC N Q.P r p →L[ℂ] BC N Q.P r' p :=
  ContinuousLinearMap.pi fun J => ContinuousLinearMap.pi fun kj =>
    (resBH (inter_mono h J.1)).comp
      ((ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin (p + 1) × Fin Q.P => BH (CechCochains.inter (cov r) J.1)) kj).comp
        (ContinuousLinearMap.proj (R := ℂ)
          (φ := fun J : CechCochains.OrdIndex (I := Fin (N + 1)) p =>
          Fin (p + 1) × Fin Q.P → BH (CechCochains.inter (cov (N := N) r) J.1)) J))

private lemma rep_resE {r r' : ℝ} (hr : r ≤ 5) (hr' : r' ≤ 5) (h : r' ≤ r) {p : ℕ}
    (x : BC N Q.P r p) :
    rep Q hr' (resE Q h p x) =
      (ordRes (cov r) (cov r') (fun α => cov_mono h α) (Ssh S).obj).f p (rep Q hr x) := by
  funext J
  change ∑ kj : Fin (p + 1) × Fin Q.P, bsmul S (resBH (inter_mono h J.1) (x J kj))
      (gen Q hr' J.1 kj.1 kj.2) =
    resM S (inter_mono h J.1)
      (∑ kj : Fin (p + 1) × Fin Q.P, bsmul S (x J kj) (gen Q hr J.1 kj.1 kj.2))
  refine Eq.symm ((resM_fsum S _ _).trans (Finset.sum_congr rfl fun kj _ => ?_))
  refine (resM_smul S _ _ _).trans ?_
  have e1 := secOf_resBH (inter_mono h J.1) (mem_chart_of_mem_inter (r := r') J.1) (x J kj)
  have e2 : resM S (inter_mono h J.1) (gen Q hr J.1 kj.1 kj.2) =
      gen Q hr' J.1 kj.1 kj.2 := resM_resM _ _ _ _
  exact congrArg₂ (fun (s : sections (sP N) (CechCochains.inter (cov r') J.1))
    (u : S.val.obj (op (CechCochains.inter (cov r') J.1))) =>
      (show (ringCatSheaf (sP N)).obj.obj (op (CechCochains.inter (cov r') J.1)) from s) • u)
        e1.symm e2

/-! #### Sections of `S` depending on bounded coefficients through a presentation -/

variable (S) in
/-- `f` is, uniformly in `x`, a combination of fixed sections of `S` over `V` with bounded
holomorphic coefficients depending continuously and linearly on `x`. -/
private def IsRep {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (V : Opens (space (sP N)))
    (f : E → S.val.obj (op V)) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (t : ι → S.val.obj (op V)) (Λ : E →L[ℂ] (ι → BH V)),
    ∀ x, f x = ∑ i, bsmul S (Λ x i) (t i)

variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] {V : Opens (space (sP N))}

omit Q in
private lemma IsRep.congr {f f' : E → S.val.obj (op V)} (hf : IsRep S V f)
    (h : ∀ x, f x = f' x) : IsRep S V f' := by
  obtain ⟨ι, _, t, Λ, hΛ⟩ := hf
  exact ⟨ι, inferInstance, t, Λ, fun x => (h x).symm.trans (hΛ x)⟩

omit Q in
private lemma isRep_zero : IsRep S V (fun _ : E => 0) :=
  ⟨PEmpty, inferInstance, PEmpty.elim, 0, fun _ => by simp⟩

omit Q in
private lemma IsRep.add {f f' : E → S.val.obj (op V)} (hf : IsRep S V f) (hf' : IsRep S V f') :
    IsRep S V (fun x => f x + f' x) := by
  obtain ⟨ι, _, t, Λ, hΛ⟩ := hf
  obtain ⟨ι', _, t', Λ', hΛ'⟩ := hf'
  let Λ'' : E →L[ℂ] (ι ⊕ ι' → BH V) :=
    ContinuousLinearMap.pi (Sum.elim (fun i => (ContinuousLinearMap.proj i).comp Λ)
      (fun i => (ContinuousLinearMap.proj i).comp Λ'))
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim t t', Λ'', fun x => ?_⟩
  exact (congrArg₂ (· + ·) (hΛ x) (hΛ' x)).trans
    (Fintype.sum_sum_type (fun i => bsmul S (Λ'' x i) (Sum.elim t t' i))).symm

omit Q in
private lemma IsRep.zsmul {f : E → S.val.obj (op V)} (hf : IsRep S V f) (n : ℤ) :
    IsRep S V (fun x => n • f x) := by
  obtain ⟨ι, _, t, Λ, hΛ⟩ := hf
  refine ⟨ι, inferInstance, fun i => n • t i, Λ, fun x => ?_⟩
  exact (congrArg (n • ·) (hΛ x)).trans (Finset.smul_sum.trans
    (Finset.sum_congr rfl fun i _ => (smul_comm _ _ _).symm))

omit Q in
private lemma IsRep.sum {ι : Type} [Fintype ι] {f : ι → E → S.val.obj (op V)}
    (hf : ∀ i, IsRep S V (f i)) : IsRep S V (fun x => ∑ i, f i x) := by
  classical
  have key : ∀ s : Finset ι, IsRep S V (fun x => ∑ i ∈ s, f i x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact isRep_zero.congr fun x => by simp
    | insert a s ha ih =>
      exact ((hf a).add ih).congr fun x => by rw [Finset.sum_insert ha]
  exact key Finset.univ

omit Q in
private lemma IsRep.comp {f : E → S.val.obj (op V)} (hf : IsRep S V f) (L : E' →L[ℂ] E) :
    IsRep S V (fun x => f (L x)) := by
  obtain ⟨ι, _, t, Λ, hΛ⟩ := hf
  exact ⟨ι, inferInstance, t, Λ.comp L, fun x => hΛ (L x)⟩

omit Q in
private lemma IsRep.res {α : Fin (N + 1)} {f : E → S.val.obj (op V)} (hf : IsRep S V f)
    {V' : Opens (space (sP N))} (h : V' ≤ V)
    (hV' : ∀ x : V', x.1 ∈ chart (sX := sP N) (stdChart N α).U) :
    IsRep S V' (fun x => resM S h (f x)) := by
  obtain ⟨ι, _, t, Λ, hΛ⟩ := hf
  refine ⟨ι, inferInstance, fun i => resM S h (t i),
    (ContinuousLinearMap.pi fun i => (resBH h).comp (ContinuousLinearMap.proj i)).comp Λ,
    fun x => ?_⟩
  refine (congrArg (resM S h) (hΛ x)).trans
    ((resM_fsum S _ _).trans (Finset.sum_congr rfl fun i _ => ?_))
  refine (resM_smul S _ _ _).trans ?_
  exact congrArg (fun s : sections (sP N) V' => (show (ringCatSheaf (sP N)).obj.obj (op V') from s)
    • resM S h (t i)) (secOf_resBH h hV' (Λ x i)).symm

private lemma isRep_rep {r : ℝ} (hr : r ≤ 5) {p : ℕ}
    (J : CechCochains.OrdIndex (I := Fin (N + 1)) p) :
    IsRep S (CechCochains.inter (cov r) J.1)
      (fun x : BC N Q.P r p => (rep Q hr x : CechCochains.OrdCochain (cov r) (Ssh S).obj p) J) :=
  ⟨Fin (p + 1) × Fin Q.P, inferInstance, fun kj => gen Q hr J.1 kj.1 kj.2,
    ContinuousLinearMap.proj J, fun _ => rfl⟩

private lemma isRep_d_rep {r : ℝ} (hr : r ≤ 5) (i q : ℕ)
    (L : CechCochains.OrdIndex (I := Fin (N + 1)) q) :
    IsRep S (CechCochains.inter (cov r) L.1) (fun x : BC N Q.P r i =>
      ((KC S r).d i q (rep Q hr x) : CechCochains.OrdCochain (cov r) (Ssh S).obj q) L) := by
  by_cases h : i + 1 = q
  · subst h
    simp only [KC, Stacks.Cech.orderedCechComplex_d]
    refine (IsRep.sum fun k : Fin (i + 2) => ((((isRep_rep Q hr
      ⟨L.1 ∘ k.succAbove, CechCochains.strictMono_omit L.2 k⟩).res
        (CechCochains.inter_le_omit (cov r) L.1 k) (mem_chart_of_mem_inter L.1)).zsmul
          ((-1 : ℤ) ^ (k : ℕ))))).congr fun x => rfl
  · rw [(KC S r).shape i q h]
    exact isRep_zero.congr fun x => rfl

/-- **Closedness.** The vanishing locus of a section of `S` over `V^{(r)}_L` depending on bounded
coefficients through a presentation is closed. -/
private lemma isClosed_isRep (hS : IsCoherentModule S) {r : ℝ} {p : ℕ}
    (L : Fin (p + 1) → Fin (N + 1)) {f : E → S.val.obj (op (CechCochains.inter (cov r) L))}
    (hf : IsRep S _ f) : IsClosed {x | f x = 0} := by
  obtain ⟨ι, _, t, Λ, hΛ⟩ := hf
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨y, hy, hlim⟩ := mem_closure_iff_seq_limit.1 hx
  let e := Fintype.equivFin ι
  have h := sum_smul_eq_zero_of_tendstoUniformly S hS L (fun k => t (e.symm k))
    (fun n k => secOf (Λ (y n) (e.symm k))) (fun k => secOf (Λ x (e.symm k)))
    (fun n => by
      have h0 : f (y n) = 0 := hy n
      rw [hΛ] at h0
      rw [← h0]
      exact e.symm.sum_comp (fun i => bsmul S (Λ (y n) i) (t i)))
    (fun k => by
      simp only [ev_secOf]
      have h1 : Filter.Tendsto (fun n => Λ (y n) (e.symm k)) Filter.atTop
          (nhds (Λ x (e.symm k))) :=
        ((continuous_apply (e.symm k)).comp Λ.continuous).continuousAt.tendsto.comp hlim
      exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1
        ((continuous_subtype_val.tendsto _).comp h1))
  show f x = 0
  rw [hΛ, ← e.symm.sum_comp]
  exact h

private lemma rep_sub {r : ℝ} (hr : r ≤ 5) {p : ℕ} (x y : BC N Q.P r p) :
    rep Q hr (x - y) = rep Q hr x - rep Q hr y :=
  eq_sub_of_add_eq ((rep_add Q hr (x - y) y).symm.trans (congrArg _ (sub_add_cancel x y)))

private lemma ordRes_ordRes {r r' r'' : ℝ} (h : r' ≤ r) (h' : r'' ≤ r') (h'' : r'' ≤ r) {p : ℕ}
    (x : (KC S r).X p) :
    (ordRes (cov r') (cov r'') (fun α => cov_mono h' α) (Ssh S).obj).f p
      ((ordRes (cov r) (cov r') (fun α => cov_mono h α) (Ssh S).obj).f p x) =
    (ordRes (cov r) (cov r'') (fun α => cov_mono h'' α) (Ssh S).obj).f p x := by
  funext J
  exact CechCochains.restr_restr (ℱ := (Ssh S).obj) _ _ _

private lemma d_ordRes {r r' : ℝ} (h : r' ≤ r) {i q : ℕ} (x : (KC S r).X i) :
    (KC S r').d i q ((ordRes (cov r) (cov r') (fun α => cov_mono h α) (Ssh S).obj).f i x) =
      (ordRes (cov r) (cov r') (fun α => cov_mono h α) (Ssh S).obj).f q ((KC S r).d i q x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, HomologicalComplex.Hom.comm]

private lemma d_ordPost {r : ℝ} (a : ℂ) {i q : ℕ} (x : (KC S r).X i) :
    (KC S r).d i q ((ordPost (cov r) (mulC S a)).f i x) =
      (ordPost (cov r) (mulC S a)).f q ((KC S r).d i q x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, HomologicalComplex.Hom.comm]

/-! #### Bounded cocycles -/

/-- Bounded coefficient vectors of the degree `q` cocycles of `V^{(r)}`. -/
private def Zc {r : ℝ} (hr : r ≤ 5) (q : ℕ) : Submodule ℂ (BC N Q.P r q) where
  carrier := {x | (KC S r).d q (q + 1) (rep Q hr x) = 0}
  add_mem' {x y} hx hy := by
    change (KC S r).d q (q + 1) (rep Q hr (x + y)) = 0
    rw [rep_add, map_add, hx, hy, add_zero]
  zero_mem' := by
    change (KC S r).d q (q + 1) (rep Q hr 0) = 0
    rw [rep_zero, map_zero]
  smul_mem' a x hx := by
    change (KC S r).d q (q + 1) (rep Q hr (a • x)) = 0
    rw [rep_smul, d_ordPost]
    change (ordPost (cov r) (mulC S a)).f (q + 1) ((KC S r).d q (q + 1) (rep Q hr x)) = 0
    rw [hx, map_zero]

private lemma mem_Zc {r : ℝ} (hr : r ≤ 5) {q : ℕ} (x : BC N Q.P r q) :
    x ∈ Zc Q hr q ↔ (KC S r).d q (q + 1) (rep Q hr x) = 0 := Iff.rfl

private lemma eq_zero_iff_forall {r : ℝ} {q : ℕ} (c : (KC S r).X q) :
    c = 0 ↔ ∀ L : CechCochains.OrdIndex (I := Fin (N + 1)) q,
      (c : CechCochains.OrdCochain (cov r) (Ssh S).obj q) L = 0 :=
  ⟨fun h L => by rw [h]; rfl, fun h => funext h⟩

private lemma isClosed_Zc (hS : IsCoherentModule S) {r : ℝ} (hr : r ≤ 5) (q : ℕ) :
    IsClosed (Zc Q hr q : Set (BC N Q.P r q)) := by
  have : (Zc Q hr q : Set (BC N Q.P r q)) = ⋂ L : CechCochains.OrdIndex (I := Fin (N + 1)) (q + 1),
      {x | ((KC S r).d q (q + 1) (rep Q hr x) : CechCochains.OrdCochain (cov r) (Ssh S).obj
        (q + 1)) L = 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe]
    exact (mem_Zc Q hr x).trans (eq_zero_iff_forall _)
  rw [this]
  exact isClosed_iInter fun L => isClosed_isRep hS L.1 (isRep_d_rep Q hr q (q + 1) L)

private lemma resE_mem_Zc {r r' : ℝ} (hr : r ≤ 5) (hr' : r' ≤ 5) (h : r' ≤ r) {q : ℕ}
    (x : BC N Q.P r q) (hx : x ∈ Zc Q hr q) : resE Q h q x ∈ Zc Q hr' q := by
  rw [mem_Zc, rep_resE Q hr hr' h, d_ordRes h, (mem_Zc Q hr x).1 hx, map_zero]

/-- The pairs `(ξ, c)` of a bounded cocycle `ξ` of `V^{(3)}` and a bounded cochain `c` of
`V^{(2)}` with `ξ|_{V^{(2)}} = δ c`. -/
private def Ysub (q i : ℕ) :
    Submodule ℂ (Zc Q le35 q × BC N Q.P 2 i) where
  carrier := {y | rep Q le25 (resE Q le23 q y.1.1) =
    (KC S 2).d i q (rep Q le25 y.2)}
  add_mem' {x y} hx hy := by
    change rep Q _ (resE Q _ q (x.1.1 + y.1.1)) = (KC S 2).d i q (rep Q _ (x.2 + y.2))
    rw [map_add, rep_add, rep_add, map_add, hx, hy]
  zero_mem' := by
    change rep Q _ (resE Q _ q 0) = (KC S 2).d i q (rep Q _ 0)
    rw [map_zero, rep_zero, rep_zero, map_zero]
  smul_mem' a x hx := by
    change rep Q _ (resE Q _ q (a • x.1.1)) = (KC S 2).d i q (rep Q _ (a • x.2))
    rw [map_smul, rep_smul, rep_smul, d_ordPost]
    exact congrArg _ hx

private lemma isClosed_Ysub (hS : IsCoherentModule S) (q i : ℕ) :
    IsClosed (Ysub Q q i : Set (Zc Q le35 q × BC N Q.P 2 i)) := by
  let L₁ : Zc Q le35 q × BC N Q.P 2 i →L[ℂ] BC N Q.P 2 q :=
    (resE Q le23 q).comp
      ((Submodule.subtypeL _).comp (ContinuousLinearMap.fst ℂ _ _))
  let L₂ : Zc Q le35 q × BC N Q.P 2 i →L[ℂ] BC N Q.P 2 i :=
    ContinuousLinearMap.snd ℂ _ _
  have : (Ysub Q q i : Set (Zc Q le35 q × BC N Q.P 2 i)) =
      ⋂ L : CechCochains.OrdIndex (I := Fin (N + 1)) q,
        {y | (rep Q le25 (L₁ y) : CechCochains.OrdCochain (cov 2) (Ssh S).obj q) L +
          (-1 : ℤ) • ((KC S 2).d i q (rep Q le25 (L₂ y)) :
            CechCochains.OrdCochain (cov 2) (Ssh S).obj q) L = 0} := by
    ext y
    simp only [Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe, neg_one_zsmul,
      ← sub_eq_add_neg, sub_eq_zero]
    exact ⟨fun h L => by rw [show (rep Q _ (L₁ y)) = _ from h]; rfl, fun h => funext h⟩
  rw [this]
  exact isClosed_iInter fun L => isClosed_isRep hS L.1
    (((isRep_rep Q le25 L).comp L₁).add
      (((isRep_d_rep Q le25 i q L).comp L₂).zsmul (-1)))

/-! #### Compactness of the restriction -/

private lemma isCompactOperator_pi' {ι : Type*} [Fintype ι] {E : Type*} [TopologicalSpace E]
    [Zero E] {F : ι → Type*} [∀ i, TopologicalSpace (F i)] (T : E → ∀ i, F i)
    (h : ∀ i, IsCompactOperator fun x => T x i) : IsCompactOperator T := by
  choose K hK hKT using h
  refine ⟨Set.pi Set.univ K, isCompact_univ_pi hK, ?_⟩
  have : T ⁻¹' Set.pi Set.univ K = ⋂ i, (fun x => T x i) ⁻¹' K i := by
    ext x; simp [Set.mem_pi]
  rw [this]
  exact Filter.iInter_mem.2 hKT

private lemma isCompactOperator_comp_continuous {E E' F : Type*} [TopologicalSpace E]
    [Zero E] [TopologicalSpace E'] [Zero E'] [TopologicalSpace F] {f : E → F}
    (hf : IsCompactOperator f) {g : E' → E} (hg : Continuous g) (h0 : g 0 = 0) :
    IsCompactOperator (f ∘ g) := by
  obtain ⟨K, hK, hKf⟩ := hf
  exact ⟨K, hK, hg.continuousAt.preimage_mem_nhds (by rw [h0]; exact hKf)⟩

private lemma isCompactOperator_resE {r r' : ℝ} (hr' : 1 ≤ r') (h : r' < r) (q : ℕ) :
    IsCompactOperator (resE Q h.le q) :=
  isCompactOperator_pi' _ fun J => isCompactOperator_pi' _ fun kj =>
    isCompactOperator_comp_continuous (isCompactOperator_resBH hr' h J.1)
      (g := fun x : BC N Q.P r q => x J kj)
      ((continuous_apply kj).comp (continuous_apply J)) rfl

/-! #### Lifting cochains through the presentations -/

private lemma bsmul_zero {α : Fin (N + 1)} {V : Opens (space (sP N))}
    (hV : ∀ x : V, x.1 ∈ chart (sX := sP N) (stdChart N α).U) (t : S.val.obj (op V)) :
    bsmul S (0 : BH V) t = 0 :=
  (congrArg (fun s : sections (sP N) V => (show (ringCatSheaf (sP N)).obj.obj (op V) from s) • t)
    (secOf_zero hV)).trans
    (zero_smul ((ringCatSheaf (sP N) : Sheaf (Opens.grothendieckTopology (space (sP N)))
      RingCat.{0}).obj.obj (op V)) _)

/-- **Lifting.** The restriction to `V^{(r)}` of a cochain of `V^{(r')}`, `1 ≤ r < r' ≤ 5`, is
represented by bounded coefficients. -/
private lemma exists_rep_eq_res (hS : IsCoherentModule S) {r r' : ℝ} (hr : 1 ≤ r)
    (hrr' : r < r') (hr' : r' ≤ 5) (hr5 : r ≤ 5) {p : ℕ} (x : (KC S r').X p) :
    ∃ ζ : BC N Q.P r p, rep Q hr5 ζ =
      (ordRes (cov r') (cov r) (fun α => cov_mono hrr'.le α) (Ssh S).obj).f p x := by
  have hlift : ∀ J : CechCochains.OrdIndex (I := Fin (N + 1)) p,
      ∃ a : Fin Q.P → (ringCatSheaf (sP N)).obj.obj (op (CechCochains.inter (cov r') J.1)),
        (x J : S.val.obj (op (CechCochains.inter (cov r') J.1))) = ∑ j, a j • resM S
          ((inter_le_cov J.1 0).trans ((cov_mono hr' _).trans (Q.hW (J.1 0)))) (Q.g (J.1 0) j) :=
    fun J => exists_lift S hS J.1 (Q.g (J.1 0)) (Q.hg _) _ (x J)
  choose a ha using hlift
  refine ⟨fun J kj => if kj.1 = 0 then boundedRes hr hrr' J.1 (a J kj.2) else 0, ?_⟩
  funext J
  have hV := mem_chart_of_mem_inter (r := r) J.1
  change ∑ kj : Fin (p + 1) × Fin Q.P,
      bsmul S (if kj.1 = 0 then boundedRes hr hrr' J.1 (a J kj.2) else 0)
        (gen Q hr5 J.1 kj.1 kj.2) =
    resM S (inter_mono hrr'.le J.1) (x J)
  have e1 : ∀ kj : Fin (p + 1) × Fin Q.P,
      bsmul S (if kj.1 = 0 then boundedRes hr hrr' J.1 (a J kj.2) else 0)
        (gen Q hr5 J.1 kj.1 kj.2) =
      if kj.1 = 0 then bsmul S (boundedRes hr hrr' J.1 (a J kj.2)) (gen Q hr5 J.1 0 kj.2)
        else 0 := by
    rintro ⟨k, j⟩
    by_cases hk : k = 0
    · subst hk; simp only [if_true]
    · simp only [hk, if_false]; exact bsmul_zero hV _
  rw [Fintype.sum_congr _ _ e1, Fintype.sum_prod_type]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Fintype.sum_ite_eq']
  rw [ha J, resM_sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e2 := secOf_boundedRes hr hrr' J.1 (a J j)
  have e3 : resM S (inter_mono hrr'.le J.1) (resM S
      ((inter_le_cov J.1 0).trans ((cov_mono hr' _).trans (Q.hW (J.1 0)))) (Q.g (J.1 0) j)) =
      gen Q hr5 J.1 0 j := resM_resM _ _ _ _
  exact congrArg₂ (fun (s : sections (sP N) (CechCochains.inter (cov r) J.1))
    (u : S.val.obj (op (CechCochains.inter (cov r) J.1))) =>
      (show (ringCatSheaf (sP N)).obj.obj (op (CechCochains.inter (cov r) J.1)) from s) • u)
        e2 e3.symm

/-! #### Finiteness -/

/-- Every bounded cocycle of `V^{(3)}` differs from the restriction of a cocycle of `V^{(5)}`
by a coboundary. -/
private lemma exists_cocycle_sub_eq_d (hS : IsCoherentModule S) (q : ℕ) (ξ : Zc Q le35 q) :
    ∃ (z' : (KC S 5).X q) (_ : (KC S 5).d q (q + 1) z' = 0)
      (c' : (KC S 3).X ((ComplexShape.up ℕ).prev q)),
      (KC S 3).d _ q c' = rep Q le35 ξ.1 -
        (ordRes (cov 5) (cov 3) (fun α => cov_mono le35 α) (Ssh S).obj).f q z' := by
  have hx : (KC S 3).d q (q + 1) (rep Q le35 ξ.1) = 0 := ξ.2
  obtain ⟨z', hz', hz'eq⟩ := cl_surjective hS lt15 (cl hS lt13 _ hx)
  have hw : (KC S 3).d q (q + 1)
      ((ordRes (cov 5) (cov 3) (fun α => cov_mono le35 α) (Ssh S).obj).f q z') = 0 := by
    rw [d_ordRes le35, hz', map_zero]
  have hxw : (KC S 3).d q (q + 1) (rep Q le35 ξ.1 -
      (ordRes (cov 5) (cov 3) (fun α => cov_mono le35 α) (Ssh S).obj).f q z') = 0 := by
    rw [map_sub, hx, hw, sub_zero]
  have hcl : cl hS lt13 _ hxw = 0 := by
    have e := cl_add hS lt13 _ _ hxw hw (by rwa [sub_add_cancel])
    rw [cl_congr hS lt13 (sub_add_cancel _ _) _ hx, cl_res hS lt15 lt13 (by norm_num) z' hz' hw,
      hz'eq] at e
    exact add_eq_right.1 e.symm
  exact ⟨z', hz', (cl_eq_zero_iff hS lt13 _ rfl _ hxw).1 hcl⟩

private lemma rep_sub_resE_eq (q : ℕ) (ξ : Zc Q le35 q) (ζ : BC N Q.P 4 q)
    (z' : (KC S 5).X q)
    (hζ : rep Q le45 ζ = (ordRes (cov 5) (cov 4) (fun α => cov_mono le45 α) (Ssh S).obj).f q z') :
    rep Q le35 (ξ.1 - resE Q le34 q ζ) = rep Q le35 ξ.1 -
      (ordRes (cov 5) (cov 3) (fun α => cov_mono le35 α) (Ssh S).obj).f q z' := by
  rw [rep_sub, rep_resE Q le45 le35 le34, hζ, ordRes_ordRes le45 le34 le35]

private lemma rep_resE_eq_d (q : ℕ) (η : BC N Q.P 3 q) (c : BC N Q.P 2 ((ComplexShape.up ℕ).prev q))
    (c' : (KC S 3).X ((ComplexShape.up ℕ).prev q))
    (hc : rep Q le25 c =
      (ordRes (cov 3) (cov 2) (fun α => cov_mono le23 α) (Ssh S).obj).f _ c')
    (hη : rep Q le35 η = (KC S 3).d _ q c') :
    rep Q le25 (resE Q le23 q η) = (KC S 2).d _ q (rep Q le25 c) := by
  rw [rep_resE Q le35 le25 le23, hc, d_ordRes le23, hη]

private lemma exists_Zc45 (hS : IsCoherentModule S) (q : ℕ) (z' : (KC S 5).X q)
    (hz' : (KC S 5).d q (q + 1) z' = 0) :
    ∃ ζ : BC N Q.P 4 q, ζ ∈ Zc Q le45 q ∧
      rep Q le45 ζ = (ordRes (cov 5) (cov 4) (fun α => cov_mono le45 α) (Ssh S).obj).f q z' := by
  obtain ⟨ζ, hζ⟩ := exists_rep_eq_res Q hS (r := 4) (r' := 5) (by norm_num) (by norm_num) le_rfl
    le45 z'
  refine ⟨ζ, ?_, hζ⟩
  rw [mem_Zc, hζ, d_ordRes le45, hz', map_zero]

/-- The data of `exists_add_eq`: a bounded cocycle `ζ` of `V^{(4)}` and a bounded cochain `c`
of `V^{(2)}` with `(ξ - ζ|_{V^{(3)}})|_{V^{(2)}} = δ c`. -/
private lemma exists_add_eq_data (hS : IsCoherentModule S) (q : ℕ) (ξ : Zc Q le35 q) :
    ∃ (ζ : BC N Q.P 4 q) (c : BC N Q.P 2 ((ComplexShape.up ℕ).prev q)), ζ ∈ Zc Q le45 q ∧
      rep Q le25 (resE Q le23 q (ξ.1 - resE Q le34 q ζ)) = (KC S 2).d _ q (rep Q le25 c) := by
  obtain ⟨z', hz', c', hc'⟩ := exists_cocycle_sub_eq_d Q hS q ξ
  obtain ⟨ζ, hζZ, hζ⟩ := exists_Zc45 Q hS q z' hz'
  obtain ⟨c, hc⟩ := exists_rep_eq_res Q hS (r := 2) (r' := 3) (by norm_num) (by norm_num)
    le35 le25 c'
  exact ⟨ζ, c, hζZ, rep_resE_eq_d Q q _ c c' hc ((rep_sub_resE_eq Q q ξ ζ z' hζ).trans hc'.symm)⟩

private lemma exists_add_eq_of (q : ℕ) (ξ : Zc Q le35 q) (ζ : BC N Q.P 4 q)
    (hζZ : ζ ∈ Zc Q le45 q) (x : BC N Q.P 3 q) (hx : x ∈ Zc Q le35 q)
    (hxe : resE Q le34 q ζ + x = ξ.1) (c : BC N Q.P 2 ((ComplexShape.up ℕ).prev q))
    (hy : (⟨x, hx⟩, c) ∈ Ysub Q q ((ComplexShape.up ℕ).prev q)) :
    ∃ (z : Zc Q le45 q) (y : Ysub Q q ((ComplexShape.up ℕ).prev q)),
      resE Q le34 q z.1 + (y.1.1 : BC N Q.P 3 q) = ξ.1 :=
  ⟨⟨ζ, hζZ⟩, ⟨(⟨x, hx⟩, c), hy⟩, hxe⟩

/-- **Surjectivity.** Every bounded cocycle of `V^{(3)}` is the restriction of a bounded cocycle of
`V^{(4)}` plus the first component of a pair in `Ysub`. -/
private lemma exists_add_eq (hS : IsCoherentModule S) (q : ℕ)
    (ξ : Zc Q le35 q) :
    ∃ (z : Zc Q le45 q) (y : Ysub Q q ((ComplexShape.up ℕ).prev q)),
      resE Q le34 q z.1 +
        (y.1.1 : BC N Q.P 3 q) = ξ.1 :=
  (exists_add_eq_data Q hS q ξ).elim fun ζ h => h.elim fun c h => h.elim fun hζZ hy =>
    exists_add_eq_of Q q ξ ζ hζZ _
      (Submodule.sub_mem _ ξ.2 (resE_mem_Zc Q le45 le35 le34 ζ hζZ)) (add_sub_cancel _ _) c hy

/-- The restriction of bounded cocycles of `V^{(4)}` to `V^{(3)}`. -/
private def ρZ (q : ℕ) : Zc Q le45 q →L[ℂ] Zc Q le35 q :=
  ((resE Q le34 q).comp (Submodule.subtypeL _)).codRestrict _
    (fun x => resE_mem_Zc Q le45 le35 le34 x.1 x.2)

private lemma isCompactOperator_ρZ (hS : IsCoherentModule S) (q : ℕ) :
    IsCompactOperator (ρZ Q q) :=
  (isCompactOperator_comp_continuous
    (isCompactOperator_resE Q (r := 4) (r' := 3) (by norm_num) (by norm_num) q)
    (g := fun x : Zc Q le45 q => (x : BC N Q.P 4 q)) continuous_subtype_val rfl).codRestrict
    (fun x => resE_mem_Zc Q le45 le35 le34 x.1 x.2) (isClosed_Zc Q hS _ q)

/-- The first projection of `Ysub`. -/
private def πY (q : ℕ) : Ysub Q q ((ComplexShape.up ℕ).prev q) →L[ℂ] Zc Q le35 q :=
  (ContinuousLinearMap.fst ℂ _ _).comp (Submodule.subtypeL _)

private lemma ρZ_coe (q : ℕ) (z : Zc Q le45 q) :
    ((ρZ Q q z : Zc Q le35 q) : BC N Q.P 3 q) = resE Q le34 q z.1 := rfl

private lemma πY_coe (q : ℕ) (y : Ysub Q q ((ComplexShape.up ℕ).prev q)) :
    ((πY Q q y : Zc Q le35 q) : BC N Q.P 3 q) = y.1.1.1 := rfl

private lemma exists_ρZ_add_πY (hS : IsCoherentModule S) (q : ℕ) (ξ : Zc Q le35 q) :
    ∃ z y, ρZ Q q z + πY Q q y = ξ :=
  (exists_add_eq Q hS q ξ).elim fun z h => h.elim fun y h =>
    ⟨z, y, Subtype.ext ((Submodule.coe_add _ _).trans
      ((congrArg₂ (· + ·) (ρZ_coe Q q z) (πY_coe Q q y)).trans h))⟩

/-- **Finiteness modulo coboundaries** (Schwartz). Finitely many bounded cocycles of `V^{(3)}` span
all of them modulo the first components of `Ysub`. -/
private theorem exists_span (hS : IsCoherentModule S) (q : ℕ) :
    ∃ (n : ℕ) (ξ : Fin n → Zc Q le35 q),
      ∀ x, ∃ (a : Fin n → ℂ) (y : Ysub Q q ((ComplexShape.up ℕ).prev q)),
        x = ∑ k, a k • ξ k + y.1.1 := by
  haveI : CompleteSpace (Zc Q le35 q) :=
    (isClosed_Zc Q hS _ q).completeSpace_coe
  haveI : CompleteSpace (Zc Q le45 q) :=
    (isClosed_Zc Q hS _ q).completeSpace_coe
  haveI : CompleteSpace (Ysub Q q ((ComplexShape.up ℕ).prev q)) :=
    (isClosed_Ysub Q hS q _).completeSpace_coe
  exact exists_finite_span_mod_range (ρZ Q q) (isCompactOperator_ρZ Q hS q) (πY Q q)
    (exists_ρZ_add_πY Q hS q)

private lemma addMonoidHom_map_add_of_eq_zero {A B : Type*} [AddZeroClass A] [AddZeroClass B]
    (f : A →+ B) (x y : A) (hy : f y = 0) : f (x + y) = f x := by
  rw [map_add, hy, add_zero]

/-- The class in `H^q((ℙᴺ)^an, 𝒮)` of a bounded cocycle of `V^{(3)}`. -/
private def clZ (hS : IsCoherentModule S) (q : ℕ) :
    Zc Q le35 q →+ (sheafCohomology (space (sP N)) q).obj (Ssh S) where
  toFun x := cl hS lt13 (rep Q le35 x.1) x.2
  map_zero' := (cl_eq_zero_iff hS lt13 _ rfl _ _).2 ⟨0, by
    rw [map_zero]; exact (rep_zero Q le35).symm⟩
  map_add' x y := by
    have hxy : (KC S 3).d q (q + 1) (rep Q le35 x.1 + rep Q le35 y.1) = 0 := by
      rw [map_add, (mem_Zc Q _ _).1 x.2, (mem_Zc Q _ _).1 y.2, add_zero]
    exact (cl_congr hS lt13 (rep_add Q le35 x.1 y.1) _ hxy).trans
      (cl_add hS lt13 _ _ x.2 y.2 hxy)

private lemma clZ_apply (hS : IsCoherentModule S) (q : ℕ) (x : Zc Q le35 q) :
    clZ Q hS q x = cl hS lt13 (rep Q le35 x.1) x.2 := rfl

private lemma hom_eq_mulC (φ : ℂ → (Ssh S ⟶ Ssh S))
    (hφ : ∀ (c : ℂ) (W : (Opens (space (sP N)))ᵒᵖ) (x : S.val.obj W),
      (φ c).hom.app W x = (show (ringCatSheaf (sP N)).obj.obj W from constSec W.unop c) • x)
    (a : ℂ) : (φ a).hom = mulC S a :=
  NatTrans.ext (funext fun W => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => hφ a W x))

private lemma clZ_smul (hS : IsCoherentModule S) (q : ℕ) (φ : ℂ → (Ssh S ⟶ Ssh S)) (a : ℂ)
    (hφa : (φ a).hom = mulC S a) (x : Zc Q le35 q) :
    clZ Q hS q (a • x) = ((sheafCohomology (space (sP N)) q).map (φ a)).hom (clZ Q hS q x) := by
  have hx' : (KC S 3).d q (q + 1) ((ordPost (cov 3) (φ a).hom).f q (rep Q le35 x.1)) = 0 := by
    rw [hφa, d_ordPost, x.2, map_zero]
  refine (cl_congr hS lt13 ?_ _ hx').trans (cl_post hS lt13 (φ a) _ x.2 hx')
  rw [hφa]
  exact rep_smul Q le35 a x.1

private lemma clZ_eq_zero_of_mem (hS : IsCoherentModule S) (q : ℕ) (η : Zc Q le35 q)
    (c : BC N Q.P 2 ((ComplexShape.up ℕ).prev q))
    (hy : rep Q le25 (resE Q le23 q η.1) = (KC S 2).d _ q (rep Q le25 c)) :
    clZ Q hS q η = 0 := by
  have hd : (KC S 2).d q (q + 1)
      ((ordRes (cov 3) (cov 2) (fun α => cov_mono le23 α)
        (Ssh S).obj).f q (rep Q le35 η.1)) = 0 := by
    rw [d_ordRes le23, η.2, map_zero]
  rw [clZ_apply, ← cl_res hS lt13 lt12 le23 _ η.2 hd]
  refine (cl_eq_zero_iff hS lt12 _ rfl _ hd).2 ⟨rep Q le25 c, ?_⟩
  rw [← hy, rep_resE Q le35 le25 le23]

private lemma cl_eq_clZ (hS : IsCoherentModule S) (q : ℕ) (z' : (KC S 5).X q)
    (hz' : (KC S 5).d q (q + 1) z' = 0) (ζ : BC N Q.P 3 q)
    (hζ : rep Q le35 ζ = (ordRes (cov 5) (cov 3) (fun α => cov_mono le35 α) (Ssh S).obj).f q z')
    (hζZ : ζ ∈ Zc Q le35 q) :
    cl hS lt15 z' hz' = clZ Q hS q ⟨ζ, hζZ⟩ := by
  rw [clZ_apply]
  have hw : (KC S 3).d q (q + 1) ((ordRes (cov 5) (cov 3)
      (fun α => cov_mono le35 α) (Ssh S).obj).f q z') = 0 := by
    rw [d_ordRes le35, hz', map_zero]
  rw [← cl_res hS lt15 lt13 le35 z' hz' hw]
  exact cl_congr hS lt13 hζ.symm _ _

private lemma mem_Zc_of_rep_eq (q : ℕ) (z' : (KC S 5).X q)
    (hz' : (KC S 5).d q (q + 1) z' = 0) (ζ : BC N Q.P 3 q)
    (hζ : rep Q le35 ζ = (ordRes (cov 5) (cov 3) (fun α => cov_mono le35 α) (Ssh S).obj).f q z') :
    ζ ∈ Zc Q le35 q := by
  rw [mem_Zc, hζ, d_ordRes le35, hz', map_zero]

private lemma cl_eq_sum_clZ (hS : IsCoherentModule S) (q : ℕ) (φ : ℂ → (Ssh S ⟶ Ssh S))
    (hφ : ∀ (c : ℂ) (W : (Opens (space (sP N)))ᵒᵖ) (x : S.val.obj W),
      (φ c).hom.app W x = (show (ringCatSheaf (sP N)).obj.obj W from constSec W.unop c) • x)
    {n : ℕ} (ξ : Fin n → Zc Q le35 q) (z' : (KC S 5).X q)
    (hz' : (KC S 5).d q (q + 1) z' = 0) (ζ : BC N Q.P 3 q)
    (hζ : rep Q le35 ζ = (ordRes (cov 5) (cov 3) (fun α => cov_mono le35 α) (Ssh S).obj).f q z')
    (hζZ : ζ ∈ Zc Q le35 q) (a : Fin n → ℂ) (y' : Ysub Q q ((ComplexShape.up ℕ).prev q))
    (hy' : (⟨ζ, hζZ⟩ : Zc Q le35 q) = ∑ k, a k • ξ k + y'.1.1) :
    cl hS lt15 z' hz' =
      ∑ i, ((sheafCohomology (space (sP N)) (q : ℤ)).map (φ (a i))).hom (clZ Q hS q (ξ i)) := by
  rw [cl_eq_clZ Q hS q z' hz' ζ hζ hζZ, hy',
    addMonoidHom_map_add_of_eq_zero _ _ _ (clZ_eq_zero_of_mem Q hS q y'.1.1 y'.1.2 y'.2),
    map_sum]
  exact Finset.sum_congr rfl fun k _ => clZ_smul Q hS q φ (a k) (hom_eq_mulC φ hφ (a k)) (ξ k)

/-- **Cartan–Serre finiteness.** Finitely many classes span `H^q((ℙᴺ)^an, 𝒮)` under the action of
the constants. -/
private theorem exists_span_sheafCohomology (hS : IsCoherentModule S)
    (φ : ℂ → (Ssh S ⟶ Ssh S))
    (hφ : ∀ (c : ℂ) (W : (Opens (space (sP N)))ᵒᵖ) (x : S.val.obj W),
      (φ c).hom.app W x = (show (ringCatSheaf (sP N)).obj.obj W from constSec W.unop c) • x)
    (q : ℕ) :
    ∃ (n : ℕ) (t : Fin n → (sheafCohomology (space (sP N)) (q : ℤ)).obj (Ssh S)),
      ∀ y, ∃ a : Fin n → ℂ,
        y = ∑ i, ((sheafCohomology (space (sP N)) (q : ℤ)).map (φ (a i))).hom (t i) :=
  (nonempty_pres S hS).elim fun Q => (exists_span Q hS q).elim fun n h => h.elim fun ξ hξ =>
    ⟨n, fun k => clZ Q hS q (ξ k), fun y =>
      (cl_surjective hS lt15 y).elim fun z' h => h.elim fun hz' hy =>
        (exists_rep_eq_res Q hS (r := 3) (r' := 5) (by norm_num) (by norm_num) le_rfl le35
          z').elim fun ζ hζ =>
          (hξ ⟨ζ, mem_Zc_of_rep_eq Q q z' hz' ζ hζ⟩).elim fun a h => h.elim fun y' hy' =>
            ⟨a, hy.symm.trans (cl_eq_sum_clZ Q hS q φ hφ ξ z' hz' ζ hζ _ a y' hy')⟩⟩

end BanachCochains

end

end MMP.Analytic.ProjectiveFiniteness

@[expose] public section

namespace MMP.Analytic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open MMP.Analytic.Analytification
open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff)

/-- **Cartan–Serre finiteness on `ℙᴺ_ℂ`.** There is `m`, depending only on `N`, such that for
every coherent sheaf of modules `𝒮` over the structure sheaf of `(ℙᴺ_ℂ)^an`: `H^q(P^an, 𝒮) = 0`
for `q ≥ m`, and every `H^q(P^an, 𝒮)` is spanned by finitely many classes over `ℂ`, where
`c ∈ ℂ` acts through the endomorphism `φ c` of `𝒮` given by multiplication with the constant
function `c`. Here `ℙᴺ_ℂ = Proj ℂ[x₀, …, x_N]`, a scheme over `ℂ` through `projToSpecCoeff ℂ N`. -/
@[mmp "thm_mmp_gaga_projective_finiteness"]
public theorem projectiveSpace_finiteDimensional_sheafCohomology (N : ℕ) :
    ∃ m : ℕ, ∀ (S : SheafOfModules.{0} (ringCatSheaf (projToSpecCoeff ℂ N))),
      IsCoherentModule S →
      (∀ q : ℕ, m ≤ q →
        IsZero ((sheafCohomology _ (q : ℤ)).obj ((SheafOfModules.toSheaf _).obj S))) ∧
      ∀ φ : ℂ → ((SheafOfModules.toSheaf _).obj S ⟶ (SheafOfModules.toSheaf _).obj S),
        (∀ (c : ℂ) (W : (Opens (space (projToSpecCoeff ℂ N)))ᵒᵖ) (x : S.val.obj W),
          (φ c).hom.app W x =
            ((ringCatSheaf (projToSpecCoeff ℂ N)).obj.map
              (homOfLE (le_top : W.unop ≤ ⊤)).op
              (show (ringCatSheaf (projToSpecCoeff ℂ N)).obj.obj (op ⊤) from
                (ringCatSheafHom (projToSpecCoeff ℂ N)).hom.app (op ⊤)
                  (ComplexPoints.baseRingHom (projToSpecCoeff ℂ N) ⊤ c))) • x) →
        ∀ q : ℕ, ∃ (n : ℕ) (t : Fin n →
            (sheafCohomology _ (q : ℤ)).obj ((SheafOfModules.toSheaf _).obj S)),
          ∀ y, ∃ a : Fin n → ℂ,
            y = ∑ i, ((sheafCohomology _ (q : ℤ)).map (φ (a i))).hom (t i) :=
  ⟨N + 1, fun S hS => ⟨fun q hq => ProjectiveFiniteness.isZero_sheafCohomology_of_le S hS q hq,
    fun φ hφ q => ProjectiveFiniteness.exists_span_sheafCohomology hS φ hφ q⟩⟩

end MMP.Analytic

end
