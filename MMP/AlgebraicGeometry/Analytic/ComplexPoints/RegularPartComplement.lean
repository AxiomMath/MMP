module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.AnalyticSubsetComplement
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPartManifold

/-!
# Removing a Zariski closed subset from the regular part of a complex variety

Let `X` be a complex variety of dimension `n` and `Z ⊆ X` a Zariski closed subset. In an
algebraic chart `e` of `X_reg(ℂ)` around a point `p`, choose an affine open `V ∋ p`; the points of
`Z ∩ V` are the common zeros of the sections `s ∈ Γ(X, V)` with `D(s) ∩ Z = ∅` (basic opens form
a basis of the topology of `V`), and these sections are analytic in the chart. So `Z(ℂ) ∩ X_reg(ℂ)`
is a locally analytic subset of `X_reg(ℂ)`, and if `X_reg(ℂ)` is preconnected, then
`X_reg(ℂ) - Z` is preconnected and, for `Z ≠ X`, dense in `X_reg(ℂ)`.

## Main results

* `MMP.UnderlyingSpace.eval_eq_zero_iff_notMem_basicOpen`: `s(p) = 0` iff the point of `X`
  underlying `p` is not in the basic open `D(s)`.
* `MMP.UnderlyingSpace.isLocallyAnalytic_regularOpens_inter`: `Z(ℂ) ∩ X_reg(ℂ)` is
  a locally analytic subset of `X_reg(ℂ)`.
* `MMP.UnderlyingSpace.isPreconnected_regularPart_diff`,
  `MMP.UnderlyingSpace.regularPart_subset_closure_regularPart_diff`: if `X_reg(ℂ)`
  is preconnected, so is `X_reg(ℂ) - Z`, and it is dense in `X_reg(ℂ)` when `Z ≠ X`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry
open MMP.Intersection.Scheme (dimension)

namespace MMP

namespace UnderlyingSpace

section Eval

variable {K : Type*} [Field K] {X : Scheme} [X.Over (Spec (.of K))]

/-- A section `s ∈ Γ(X, U)` vanishes at `p ∈ U(K)` iff the point of `X` underlying `p` is not in
the basic open `D(s)`. -/
theorem eval_eq_zero_iff_notMem_basicOpen {U : X.Opens} (p : UnderlyingSpace K X)
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ U) (s : Γ(X, U)) :
    eval p hp s = 0 ↔ p.toHom (IsLocalRing.closedPoint K) ∉ X.basicOpen s := by
  rw [← top_le_preimage_iff, top_le_preimage_basicOpen_iff p hp, not_not]

end Eval

/-- In an affine open `V`, a point lies in a closed set `Z` iff it lies outside every basic open
`D(s)`, `s ∈ Γ(X, V)`, disjoint from `Z`. -/
theorem _root_.AlgebraicGeometry.IsAffineOpen.mem_iff_forall_notMem_basicOpen {X : Scheme}
    {V : X.Opens} (hV : IsAffineOpen V) {Z : Set X} (hZ : IsClosed Z) {x : X} (hx : x ∈ V) :
    x ∈ Z ↔ ∀ s : Γ(X, V), (X.basicOpen s : Set X) ∩ Z = ∅ → x ∉ X.basicOpen s := by
  refine ⟨fun hxZ s hs hxs ↦ (Set.eq_empty_iff_forall_notMem.mp hs) x ⟨hxs, hxZ⟩, fun h ↦ ?_⟩
  by_contra hxZ
  obtain ⟨s, hsZ, hxs⟩ := hV.exists_basicOpen_le (V := ⟨Zᶜ, hZ.isOpen_compl⟩) ⟨x, hxZ⟩ hx
  exact h s (Set.eq_empty_iff_forall_notMem.mpr fun y hy ↦ hsZ hy.1 hy.2) hxs

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [QuasiCompact (X ↘ Spec (.of ℂ))]

/-- **`Z(ℂ) ∩ X_reg(ℂ)` is a locally analytic subset of `X_reg(ℂ)`.** For a complex variety `X` of
dimension `n` and a Zariski closed `Z ⊆ X`, the regular `ℂ`-points lying in `Z` form a locally
analytic subset of `X_reg(ℂ)` for the algebraic charts with values in `ℂⁿ`. -/
theorem isLocallyAnalytic_regularOpens_inter {n : ℕ} (hn : (n : WithBot ℕ∞) = dimension X)
    {Z : Set X} (hZ : IsClosed Z) :
    SmoothLocusConnected.IsLocallyAnalytic (EuclideanSpace ℂ (Fin n)) ℂ
      {q : regularOpens ℂ X | q.1.toHom (IsLocalRing.closedPoint ℂ) ∈ Z} := by
  intro p
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := p.1.toHom (IsLocalRing.closedPoint ℂ)) (U := ⊤) trivial
  obtain ⟨e₀, hpe, he⟩ := exists_isAlgebraicChart_of_dimension_eq hn p.1 p.2
  set W : Set (UnderlyingSpace ℂ X) := regularPart ℂ X ∩ {q | ⊤ ≤ q.toHom ⁻¹ᵁ V}
  have hW : IsOpen W := isOpen_regularPart.inter (isOpen_setOf_le_preimage V)
  set e₁ := (e₀.restrOpen W hW).subtypeRestr (s := regularOpens ℂ X) ⟨p⟩
  have he₁ : ∀ q, e₁ q = e₀ q.1 := fun q ↦ rfl
  have hsrc : ∀ q, q ∈ e₁.source ↔ q.1 ∈ e₀.source ∧ q.1 ∈ W := by
    intro q
    rw [OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage,
      OpenPartialHomeomorph.restrOpen_source]
    rfl
  set T := e₀.target ∩ e₀.symm ⁻¹' {q : UnderlyingSpace ℂ X | ⊤ ≤ q.toHom ⁻¹ᵁ V}
  have hT : IsOpen T := e₀.isOpen_inter_preimage_symm (isOpen_setOf_le_preimage V)
  have htgt : e₁.target ⊆ T := by
    intro y hy
    rw [← e₁.image_source_eq_target] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    obtain ⟨hq₀, hqW⟩ := (hsrc q).mp hq
    rw [he₁]
    exact ⟨e₀.map_source hq₀, by
      simpa only [Set.mem_preimage, e₀.left_inv hq₀] using hqW.2⟩
  refine ⟨e₁, {s : Γ(X, V) // (X.basicOpen s : Set X) ∩ Z = ∅},
    fun s k ↦ evalExt V s.1 (e₀.symm k), (hsrc p).mpr ⟨hpe, p.2, ?_⟩, fun s ↦ ?_, fun q hq ↦ ?_⟩
  · exact (top_le_preimage_iff _ _).mpr hxV
  · exact ((hT.analyticOn_iff_analyticOnNhd).mp (he.contDiffOn_evalExt V s.1).analyticOn).mono
      htgt
  · obtain ⟨hq₀, hqW⟩ := (hsrc q).mp hq
    simp only [Set.mem_setOf_eq, he₁, e₀.left_inv hq₀, evalExt_of_le _ hqW.2,
      eval_eq_zero_iff_notMem_basicOpen, Subtype.forall]
    exact hV.mem_iff_forall_notMem_basicOpen hZ ((top_le_preimage_iff _ _).mp hqW.2)

/-- The regular `ℂ`-points off `Z`, as the image of the complement of `Z(ℂ) ∩ X_reg(ℂ)` in
`X_reg(ℂ)`. -/
private lemma image_compl_eq (Z : Set X) :
    Subtype.val '' {q : regularOpens ℂ X | q.1.toHom (IsLocalRing.closedPoint ℂ) ∈ Z}ᶜ =
      regularPart ℂ X \ {p | p.toHom (IsLocalRing.closedPoint ℂ) ∈ Z} :=
  Subtype.image_preimage_coe (regularPart ℂ X) {p | p.toHom (IsLocalRing.closedPoint ℂ) ∈ Z}ᶜ

/-- **Removing a Zariski closed set keeps `X_reg(ℂ)` preconnected.** For a complex variety `X`
with `X_reg(ℂ)` preconnected and a Zariski closed `Z ⊆ X`, `X_reg(ℂ) - Z` is preconnected. -/
theorem isPreconnected_regularPart_diff {Z : Set X} (hZ : IsClosed Z)
    (hconn : IsPreconnected (regularPart ℂ X)) :
    IsPreconnected (regularPart ℂ X \ {p | p.toHom (IsLocalRing.closedPoint ℂ) ∈ Z}) := by
  rcases (regularPart ℂ X).eq_empty_or_nonempty with h | ⟨p, hp⟩
  · rw [h, Set.empty_diff]
    exact isPreconnected_empty
  obtain ⟨n, -, -, -, hn⟩ := exists_isAlgebraicChart p hp
  haveI : PreconnectedSpace (regularOpens ℂ X) := isPreconnected_iff_preconnectedSpace.mp hconn
  set S := {q : regularOpens ℂ X | q.1.toHom (IsLocalRing.closedPoint ℂ) ∈ Z}
  by_cases hS : S = Set.univ
  · rw [← image_compl_eq]
    change IsPreconnected (Subtype.val '' Sᶜ)
    rw [hS, Set.compl_univ, Set.image_empty]
    exact isPreconnected_empty
  rw [← image_compl_eq]
  exact (SmoothLocusConnected.isPreconnected_compl_of_isLocallyAnalytic
    (isLocallyAnalytic_regularOpens_inter hn hZ) hS).image _
    continuous_subtype_val.continuousOn

omit [QuasiCompact (X ↘ Spec (.of ℂ))] in
/-- There is a regular `ℂ`-point off a proper Zariski closed subset of a complex variety. -/
theorem exists_mem_regularPart_notMem {Z : Set X} (hZ : IsClosed Z) (hZne : Z ≠ Set.univ) :
    ∃ p ∈ regularPart ℂ X, p.toHom (IsLocalRing.closedPoint ℂ) ∉ Z := by
  have hgen : genericPoint X ∈ regularLocus X ∩ Zᶜ := by
    refine ⟨genericPoint_mem_regularLocus X, fun hg ↦ hZne ?_⟩
    have := hZ.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hg)
    rw [genericPoint_spec X |>.def] at this
    exact Set.eq_univ_of_univ_subset this
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of ℂ))
  obtain ⟨c, hc, hcl⟩ := nonempty_inter_closedPoints ⟨_, hgen⟩
    ((isOpen_regularLocus_of_isAlgebraicScheme ℂ X).inter hZ.isOpen_compl).isLocallyClosed
  refine ⟨(equivClosedPoints X).symm ⟨c, hcl⟩, ?_, ?_⟩
  · rw [mem_regularPart_iff, ← equivClosedPoints_apply, Equiv.apply_symm_apply]
    exact hc.1
  · rw [← equivClosedPoints_apply, Equiv.apply_symm_apply]
    exact hc.2

/-- **Removing a proper Zariski closed set leaves `X_reg(ℂ)` dense.** For a complex variety `X`
with `X_reg(ℂ)` preconnected and a Zariski closed `Z ⊊ X`, `X_reg(ℂ) - Z` is dense in
`X_reg(ℂ)`. -/
theorem regularPart_subset_closure_regularPart_diff {Z : Set X} (hZ : IsClosed Z)
    (hZne : Z ≠ Set.univ) (hconn : IsPreconnected (regularPart ℂ X)) :
    regularPart ℂ X ⊆
      closure (regularPart ℂ X \ {p | p.toHom (IsLocalRing.closedPoint ℂ) ∈ Z}) := by
  obtain ⟨p₀, hp₀, hp₀Z⟩ := exists_mem_regularPart_notMem hZ hZne
  obtain ⟨n, -, -, -, hn⟩ := exists_isAlgebraicChart p₀ hp₀
  haveI : PreconnectedSpace (regularOpens ℂ X) := isPreconnected_iff_preconnectedSpace.mp hconn
  set S := {q : regularOpens ℂ X | q.1.toHom (IsLocalRing.closedPoint ℂ) ∈ Z}
  have hS : S ≠ Set.univ := fun h ↦ hp₀Z
    (show (⟨p₀, hp₀⟩ : regularOpens ℂ X) ∈ S from h ▸ Set.mem_univ _)
  have hd := SmoothLocusConnected.dense_compl_of_isLocallyAnalytic
    (isLocallyAnalytic_regularOpens_inter hn hZ) hS
  intro p hp
  rw [← image_compl_eq]
  exact image_closure_subset_closure_image continuous_subtype_val
    ⟨⟨p, hp⟩, hd.closure_eq ▸ Set.mem_univ _, rfl⟩

end UnderlyingSpace

end MMP
