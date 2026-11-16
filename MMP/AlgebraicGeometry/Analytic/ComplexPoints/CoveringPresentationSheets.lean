module

public import MMP.RingTheory.Presentation.CoveringPresentation
public import MMP.Analysis.Complex.GenericCoveringSheets
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPartManifold

/-!
# A finite morphism of affine complex schemes with a covering presentation is a covering

Let `g : X → Y` be a morphism of affine schemes over `ℂ` such that `B = Γ(X)` has a covering
presentation `(y, f, c, δ)` over `A = Γ(Y)`
(`MMP.GenericCovering.CoveringPresentation`).
A `ℂ`-point `q` of `X` over a point `w` of `Y` with `c(w) ≠ 0` is determined by `w` and the root
`q(y)` of `f_w`, and every root occurs: the points of `X(ℂ)` over `{c ≠ 0}` correspond to the
points of the hypersurface `{(w, t) | c(w) ≠ 0, f_w(t) = 0}`.

Let `e` be an algebraic chart of `Y(ℂ)` at a point `w₀` with `(c δ)(w₀) ≠ 0`. The coefficients of
`f` are holomorphic in `e`, and `f_{w₀}` is separable, so over a ball `S` around `e(w₀)` the roots
of `f` are the values of `d = deg f` holomorphic functions `ψ_i` with pairwise distinct values
(`MMP.GenericCovering.exists_analytic_sheets`). Hence over `U = e⁻¹(S)` the
`ℂ`-points of `X` are the disjoint union of the `d` sheets `U_i = {q | q(y) = ψ_i(e(g q))}`, and
`e ∘ g : U_i → S` is an algebraic chart of `X(ℂ)`, with inverse `k ↦ (e⁻¹ k, ψ_i k)`.

## Main definitions

* `MMP.GenericCovering.CoveringPresentation.liftPoint`: the `ℂ`-point of `X` over a
  point `w` of `Y` and a root of `f_w`.
* `MMP.GenericCovering.CoveringPresentation.SheetData`: the holomorphic roots
  `ψ_i` over an open set in the target of a chart of `Y(ℂ)`.
* `MMP.GenericCovering.CoveringPresentation.SheetData.sheet`,
  `MMP.GenericCovering.CoveringPresentation.SheetData.chart`: the sheets `U_i` and
  their charts `e ∘ g`.

## Main results

* `MMP.GenericCovering.CoveringPresentation.eq_liftPoint`: a point of `X(ℂ)` over
  `{c ≠ 0}` is the point over its image and its value at `y`.
* `MMP.GenericCovering.CoveringPresentation.exists_sheetData`: sheet data exist
  over a ball around `e(w₀)`.
* `MMP.GenericCovering.CoveringPresentation.SheetData.preimage_eq_iUnion_sheet`,
  `MMP.GenericCovering.CoveringPresentation.SheetData.disjoint_sheet`,
  `MMP.GenericCovering.CoveringPresentation.SheetData.isOpen_sheet`: the points
  over `e⁻¹(S)` are the disjoint union of the open sheets.
* `MMP.GenericCovering.CoveringPresentation.SheetData.isAlgebraicChart_chart`: the
  chart of each sheet is algebraic.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial Topology
open scoped ContDiff

namespace MMP.GenericCovering

open UnderlyingSpace

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] [IsAffine X]
  {g : X ⟶ Y} [g.IsOver (Spec (.of ℂ))] [Algebra Γ(Y, ⊤) Γ(X, ⊤)]

/-- Evaluation of global sections at a `ℂ`-point, as a ring map. -/
abbrev evalHom {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] (q : UnderlyingSpace ℂ Z) :
    Γ(Z, ⊤) →+* ℂ :=
  evalRingHom (U := ⊤) q (Scheme.Hom.preimage_top _).ge

/-- `evalHom q` sends a global section `a` to its value `evalTop q a` at `q`. -/
lemma evalHom_apply {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] (q : UnderlyingSpace ℂ Z)
    (a : Γ(Z, ⊤)) : evalHom q a = evalTop q a :=
  rfl

omit [IsAffine X] [Algebra Γ(Y, ⊤) Γ(X, ⊤)] in
variable (g) in
/-- `a(g(q)) = (g^* a)(q)` for a global section `a` of `Y`. -/
lemma evalTop_appTop (q : UnderlyingSpace ℂ X) (a : Γ(Y, ⊤)) :
    evalTop q (g.appTop.hom a) = evalTop (mapFun g q) a := by
  rw [evalTop_eq, evalTop_eq, toHom_mapFun, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

omit [IsAffine X] in
/-- When the algebra map is `g^*`, evaluating at `q` after `algebraMap` is evaluation at
`g(q)`. -/
lemma evalHom_comp_algebraMap (hg : algebraMap Γ(Y, ⊤) Γ(X, ⊤) = g.appTop.hom)
    (q : UnderlyingSpace ℂ X) :
    (evalHom q).comp (algebraMap Γ(Y, ⊤) Γ(X, ⊤)) = evalHom (mapFun g q) := by
  ext a
  rw [RingHom.comp_apply, hg, evalHom_apply, evalHom_apply, evalTop_appTop]

omit [IsAffine X] [Algebra Γ(Y, ⊤) Γ(X, ⊤)] in
variable (g) in
/-- The constant `c ∈ ℂ` as a global section of `X` is the pullback along `g` of the constant `c`
on `Y`. -/
lemma structureRingHom_eq_appTop (c : ℂ) :
    structureRingHom ℂ X c = g.appTop.hom (structureRingHom ℂ Y c) := by
  have h : X ↘ Spec (.of ℂ) = g ≫ Y ↘ Spec (.of ℂ) := (comp_over g (Spec (.of ℂ))).symm
  simp only [structureRingHom, h, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.coe_comp, Function.comp_apply]

namespace CoveringPresentation

variable (hg : algebraMap Γ(Y, ⊤) Γ(X, ⊤) = g.appTop.hom)
  (P : CoveringPresentation Γ(Y, ⊤) Γ(X, ⊤))

omit [IsAffine X] in
include hg in
/-- The value at `y` of a `ℂ`-point `q` of `X` is a root of `f` over the image of `q`. -/
lemma eval_map_evalTop_y (q : UnderlyingSpace ℂ X) :
    (P.f.map (evalHom (mapFun g q))).eval (evalTop q P.y) = 0 := by
  rw [← evalHom_comp_algebraMap hg]
  exact P.eval_map_apply_y (evalHom q)

variable {w : UnderlyingSpace ℂ Y} {t : ℂ}

omit [IsAffine X] in
include hg in
/-- The ring map `point ht hc : Γ(X) → ℂ` sends the constant `c` to `c`. -/
lemma point_structureRingHom (ht : (P.f.map (evalHom w)).eval t = 0)
    (hc : evalHom w P.c ≠ 0) (c : ℂ) : point ht hc (structureRingHom ℂ X c) = c := by
  rw [structureRingHom_eq_appTop g, ← hg, point_algebraMap, evalHom_apply,
    evalTop_structureRingHom]

/-- The `ℂ`-point of `X` over a point `w` of `Y` with `c(w) ≠ 0` and a root `t` of `f_w`. -/
def liftPoint (ht : (P.f.map (evalHom w)).eval t = 0) (hc : evalHom w P.c ≠ 0) :
    UnderlyingSpace ℂ X :=
  ofRingHom (point ht hc) (P.point_structureRingHom hg ht hc)

/-- The value of a global section `b` of `X` at `liftPoint` is `pointFun (evalHom w) t b`. -/
lemma evalTop_liftPoint (ht : (P.f.map (evalHom w)).eval t = 0) (hc : evalHom w P.c ≠ 0)
    (b : Γ(X, ⊤)) : evalTop (P.liftPoint hg ht hc) b = P.pointFun (evalHom w) t b := by
  rw [liftPoint, evalTop_ofRingHom, point_apply]

/-- The value of `y` at the point over `w` and the root `t` is `t`. -/
@[simp]
lemma evalTop_liftPoint_y (ht : (P.f.map (evalHom w)).eval t = 0) (hc : evalHom w P.c ≠ 0) :
    evalTop (P.liftPoint hg ht hc) P.y = t := by
  rw [liftPoint, evalTop_ofRingHom, point_y]

/-- The point over `w` and a root of `f_w` lies over `w`. -/
@[simp]
lemma mapFun_liftPoint [IsAffine Y] (ht : (P.f.map (evalHom w)).eval t = 0)
    (hc : evalHom w P.c ≠ 0) :
    mapFun g (P.liftPoint hg ht hc) = w := by
  let := (structureRingHom ℂ Y).toAlgebra
  refine eq_of_forall_evalTop_eq fun a ↦ ?_
  rw [← evalTop_appTop, liftPoint, evalTop_ofRingHom, ← hg, point_algebraMap, evalHom_apply]

/-- A `ℂ`-point `q` of `X` with `c(g q) ≠ 0` is the point over `g(q)` and `q(y)`. -/
lemma eq_liftPoint (q : UnderlyingSpace ℂ X) (hc : evalHom (mapFun g q) P.c ≠ 0) :
    q = P.liftPoint hg (P.eval_map_evalTop_y hg q) hc := by
  have hc' : evalHom q (algebraMap _ _ P.c) ≠ 0 := by
    rwa [← RingHom.comp_apply, evalHom_comp_algebraMap hg]
  have h := P.eq_point (evalHom q) hc'
  let := (structureRingHom ℂ X).toAlgebra
  refine eq_of_forall_evalTop_eq fun b ↦ ?_
  rw [evalTop_liftPoint, ← evalHom_apply, h, point_apply, evalHom_comp_algebraMap hg]
  rfl

/-- `liftPoint` depends only on the point `w` and the root `t`, not on the proofs. -/
lemma liftPoint_congr {w' : UnderlyingSpace ℂ Y} {t' : ℂ} (ht : (P.f.map (evalHom w)).eval t = 0)
    (hc : evalHom w P.c ≠ 0) (ht' : (P.f.map (evalHom w')).eval t' = 0)
    (hc' : evalHom w' P.c ≠ 0) (hw : w = w') (htt : t = t') :
    P.liftPoint hg ht hc = P.liftPoint hg ht' hc' := by
  subst hw htt
  rfl

end CoveringPresentation

/-- `x ↦ Q_{ev x}(ψ x)` is `C^n` where the coefficients of `Q` and `ψ` are. -/
lemma contDiffOn_eval₂ {R E : Type*} [CommRing R] [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n : WithTop ℕ∞} (Q : R[X]) (ev : E → R →+* ℂ) (ψ : E → ℂ) {S : Set E}
    (hev : ∀ i, ContDiffOn ℂ n (fun x ↦ ev x (Q.coeff i)) S) (hψ : ContDiffOn ℂ n ψ S) :
    ContDiffOn ℂ n (fun x ↦ Q.eval₂ (ev x) (ψ x)) S := by
  simp only [eval₂_eq_sum_range]
  exact ContDiffOn.sum fun i _ ↦ (hev i).mul (hψ.pow i)

namespace CoveringPresentation

variable (P : CoveringPresentation Γ(Y, ⊤) Γ(X, ⊤)) {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℂ E]

/-- *Sheet data* for a covering presentation over an open set `S` in the target of a chart `e` of
`Y(ℂ)`: holomorphic functions `ψ_i` on `S`, `i < deg f`, whose values at `k ∈ S` are the pairwise
distinct roots of `f` over `e⁻¹(k)`, where the conductor element does not vanish and the global
sections of `Y` are holomorphic. -/
structure SheetData (e : OpenPartialHomeomorph (UnderlyingSpace ℂ Y) E) where
  /-- The open set of the chart's target over which the sheets are defined. -/
  S : Set E
  /-- The sheets. -/
  ψ : Fin P.f.natDegree → E → ℂ
  /-- `S` is open. -/
  isOpen : IsOpen S
  /-- `S` is nonempty. -/
  nonempty : S.Nonempty
  /-- `S` lies in the target of `e`. -/
  subset_target : S ⊆ e.target
  /-- The conductor element `c` does not vanish over `S`. -/
  ne_zero_c : ∀ k ∈ S, evalHom (e.symm k) P.c ≠ 0
  /-- Each `ψ i` is holomorphic on `S`. -/
  contDiffOn_ψ : ∀ i, ContDiffOn ℂ ω (ψ i) S
  /-- Every global section `a` of `Y` gives a holomorphic function `k ↦ a(e⁻¹ k)` on `S`. -/
  contDiffOn_coeff : ∀ a : Γ(Y, ⊤), ContDiffOn ℂ ω (fun k ↦ evalTop (e.symm k) a) S
  /-- Each `ψ i k` is a root of `f` over `e⁻¹(k)`. -/
  isRoot : ∀ i, ∀ k ∈ S, (P.f.map (evalHom (e.symm k))).eval (ψ i k) = 0
  /-- The values `ψ i k` are pairwise distinct. -/
  injective : ∀ k ∈ S, Function.Injective fun i ↦ ψ i k
  /-- Every root of `f` over `e⁻¹(k)` is some `ψ i k`. -/
  exists_eq : ∀ k ∈ S, ∀ t, (P.f.map (evalHom (e.symm k))).eval t = 0 → ∃ i, ψ i k = t

namespace SheetData

variable (hg : algebraMap Γ(Y, ⊤) Γ(X, ⊤) = g.appTop.hom) {P}
  {e : OpenPartialHomeomorph (UnderlyingSpace ℂ Y) E} (D : P.SheetData e)

/-- The `i`-th section `k ↦ (e⁻¹ k, ψ_i k)` over `S` (extended arbitrarily off `S`). -/
def sect (i : Fin P.f.natDegree) (k : E) : UnderlyingSpace ℂ X :=
  open Classical in
  if h : k ∈ D.S then P.liftPoint hg (D.isRoot i k h) (D.ne_zero_c k h)
  else P.liftPoint hg (D.isRoot i _ D.nonempty.some_mem) (D.ne_zero_c _ D.nonempty.some_mem)

/-- On `S`, the `i`-th section is the point over `e⁻¹(k)` and the root `ψ_i k`. -/
lemma sect_of_mem (i : Fin P.f.natDegree) {k : E} (hk : k ∈ D.S) :
    D.sect hg i k = P.liftPoint hg (D.isRoot i k hk) (D.ne_zero_c k hk) :=
  dite_eq_left_of_eq_true (eq_true hk)

/-- On `S`, the `i`-th section at `k` lies over `e⁻¹(k)`. -/
lemma mapFun_sect [IsAffine Y] (i : Fin P.f.natDegree) {k : E} (hk : k ∈ D.S) :
    mapFun g (D.sect hg i k) = e.symm k := by
  rw [D.sect_of_mem hg i hk, mapFun_liftPoint]

/-- On `S`, the value of `y` at the `i`-th section at `k` is `ψ_i k`. -/
lemma evalTop_sect_y (i : Fin P.f.natDegree) {k : E} (hk : k ∈ D.S) :
    evalTop (D.sect hg i k) P.y = D.ψ i k := by
  rw [D.sect_of_mem hg i hk, evalTop_liftPoint_y]

/-- The values of the global sections of `X` along a section are holomorphic. -/
lemma contDiffOn_evalTop_sect (i : Fin P.f.natDegree) (b : Γ(X, ⊤)) :
    ContDiffOn ℂ ω (fun k ↦ evalTop (D.sect hg i k) b) D.S := by
  have h : ContDiffOn ℂ ω (fun k ↦ (P.numer b).eval₂ (evalHom (e.symm k)) (D.ψ i k) /
      evalHom (e.symm k) P.c) D.S :=
    (contDiffOn_eval₂ _ _ _ (fun j ↦ D.contDiffOn_coeff _) (D.contDiffOn_ψ i)).div
      (D.contDiffOn_coeff P.c) D.ne_zero_c
  refine h.congr fun k hk ↦ ?_
  rw [D.sect_of_mem hg i hk, evalTop_liftPoint]
  rfl

/-- Each section is continuous on `S`. -/
lemma continuousOn_sect (i : Fin P.f.natDegree) : ContinuousOn (D.sect hg i) D.S := by
  rw [(isInducing_evalTop (K := ℂ) (X := X)).continuousOn_iff, continuousOn_pi]
  exact fun b ↦ (D.contDiffOn_evalTop_sect hg i b).continuousOn

/-- The `i`-th sheet: the points `q` over `e⁻¹(S)` with `q(y) = ψ_i(e(g q))`. -/
def sheet (i : Fin P.f.natDegree) : Set (UnderlyingSpace ℂ X) :=
  {q | mapFun g q ∈ e.source ∧ e (mapFun g q) ∈ D.S ∧ evalTop q P.y = D.ψ i (e (mapFun g q))}

/-- On `S`, the `i`-th section takes values in the `i`-th sheet. -/
lemma sect_mem_sheet [IsAffine Y] (i : Fin P.f.natDegree) {k : E} (hk : k ∈ D.S) :
    D.sect hg i k ∈ D.sheet (g := g) i := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [D.mapFun_sect hg i hk]
  · exact e.map_target (D.subset_target hk)
  · rwa [e.right_inv (D.subset_target hk)]
  · rw [e.right_inv (D.subset_target hk), D.evalTop_sect_y hg i hk]

/-- A point `q` of the `i`-th sheet is the `i`-th section at `e(g q)`. -/
lemma sect_apply_mapFun {i : Fin P.f.natDegree} {q : UnderlyingSpace ℂ X}
    (hq : q ∈ D.sheet (g := g) i) : D.sect hg i (e (mapFun g q)) = q := by
  obtain ⟨h1, h2, h3⟩ := hq
  have hc : evalHom (mapFun g q) P.c ≠ 0 := by
    have := D.ne_zero_c _ h2
    rwa [e.left_inv h1] at this
  rw [D.sect_of_mem hg i h2]
  exact (P.liftPoint_congr hg _ _ _ hc (e.left_inv h1) h3.symm).trans (P.eq_liftPoint hg q hc).symm

omit [IsAffine X] in
include hg in
/-- Every point over `e⁻¹(S)` lies on a sheet. -/
lemma exists_mem_sheet {q : UnderlyingSpace ℂ X} (h1 : mapFun g q ∈ e.source)
    (h2 : e (mapFun g q) ∈ D.S) : ∃ i, q ∈ D.sheet (g := g) i := by
  have hroot := P.eval_map_evalTop_y hg q
  rw [← e.left_inv h1] at hroot
  obtain ⟨i, hi⟩ := D.exists_eq _ h2 _ hroot
  exact ⟨i, h1, h2, hi.symm⟩

omit [IsAffine X] in
/-- Distinct sheets are disjoint. -/
lemma disjoint_sheet {i j : Fin P.f.natDegree} (hij : i ≠ j) :
    Disjoint (D.sheet (g := g) i) (D.sheet (g := g) j) := by
  refine Set.disjoint_left.mpr fun q hi hj ↦ hij (D.injective _ hi.2.1 ?_)
  exact hi.2.2.symm.trans hj.2.2

omit [IsAffine X] in
include hg in
/-- The points of `X(ℂ)` over `e⁻¹(S)` are the union of the sheets. -/
lemma preimage_eq_iUnion_sheet :
    mapFun g ⁻¹' (e.source ∩ e ⁻¹' D.S) = ⋃ i, D.sheet (g := g) i := by
  ext q
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_iUnion]
  exact ⟨fun h ↦ D.exists_mem_sheet hg h.1 h.2, fun ⟨i, hi⟩ ↦ ⟨hi.1, hi.2.1⟩⟩

include hg in
/-- Each sheet is open in `X(ℂ)`. -/
lemma isOpen_sheet (i : Fin P.f.natDegree) : IsOpen (D.sheet (g := g) i) := by
  set O := mapFun g ⁻¹' (e.source ∩ e ⁻¹' D.S)
  have hO : IsOpen O :=
    (e.isOpen_inter_preimage D.isOpen).preimage (continuous_mapFun (K := ℂ) g)
  have hcont : ∀ j : Fin P.f.natDegree, ContinuousOn
      (fun q ↦ evalTop q P.y - D.ψ j (e (mapFun g q))) O := fun j ↦ by
    refine (continuous_evalTop_apply P.y).continuousOn.sub ?_
    refine ((D.contDiffOn_ψ j).continuousOn.comp (e.continuousOn.comp
      (continuous_mapFun (K := ℂ) g).continuousOn fun q hq ↦ hq.1) fun q hq ↦ hq.2)
  set T : Fin P.f.natDegree → Set (UnderlyingSpace ℂ X) := fun j ↦
    O ∩ (fun q ↦ evalTop q P.y - D.ψ j (e (mapFun g q))) ⁻¹' {0}ᶜ
  have hT : ∀ j, IsOpen (T j) := fun j ↦ (hcont j).isOpen_inter_preimage hO isOpen_compl_singleton
  have heq : D.sheet (g := g) i = O ∩ ⋂ j ∈ Finset.univ.filter (· ≠ i), T j := by
    ext q
    simp only [Set.mem_inter_iff, Set.mem_iInter, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun hq ↦ ⟨⟨hq.1, hq.2.1⟩, fun j hj ↦ ⟨⟨hq.1, hq.2.1⟩, fun h ↦ hj ?_⟩⟩,
      fun ⟨hO', hj⟩ ↦ ?_⟩
    · exact (D.injective _ hq.2.1 (hq.2.2.symm.trans (sub_eq_zero.1 h))).symm
    · obtain ⟨j, hqj⟩ := D.exists_mem_sheet hg hO'.1 hO'.2
      obtain rfl | hji := eq_or_ne j i
      · exact hqj
      · exact ((hj j hji).2 (sub_eq_zero.2 hqj.2.2)).elim
  rw [heq]
  exact hO.inter (isOpen_biInter_finset fun j _ ↦ hT j)

/-- The chart `e ∘ g` of the `i`-th sheet, onto `S`, with inverse the `i`-th section. -/
def chart [IsAffine Y] (i : Fin P.f.natDegree) : OpenPartialHomeomorph (UnderlyingSpace ℂ X) E where
  toFun q := e (mapFun g q)
  invFun := D.sect hg i
  source := D.sheet (g := g) i
  target := D.S
  map_source' _ hq := hq.2.1
  map_target' _ hk := D.sect_mem_sheet hg i hk
  left_inv' _ hq := D.sect_apply_mapFun hg hq
  right_inv' k hk := by rw [D.mapFun_sect hg i hk, e.right_inv (D.subset_target hk)]
  open_source := D.isOpen_sheet hg i
  open_target := D.isOpen
  continuousOn_toFun :=
    e.continuousOn.comp (continuous_mapFun (K := ℂ) g).continuousOn fun _ hq ↦ hq.1
  continuousOn_invFun := D.continuousOn_sect hg i

/-- The chart of the `i`-th sheet sends `q` to `e(g q)`. -/
@[simp]
lemma chart_apply [IsAffine Y] (i : Fin P.f.natDegree) (q : UnderlyingSpace ℂ X) :
    D.chart hg i q = e (mapFun g q) :=
  rfl

/-- The inverse of the chart of the `i`-th sheet is the `i`-th section. -/
@[simp]
lemma chart_symm_apply [IsAffine Y] (i : Fin P.f.natDegree) (k : E) :
    (D.chart hg i).symm k = D.sect hg i k :=
  rfl

/-- The source of the chart of the `i`-th sheet is the `i`-th sheet. -/
@[simp]
lemma chart_source [IsAffine Y] (i : Fin P.f.natDegree) :
    (D.chart hg i).source = D.sheet (g := g) i :=
  rfl

/-- The target of the chart of each sheet is `S`. -/
@[simp]
lemma chart_target [IsAffine Y] (i : Fin P.f.natDegree) : (D.chart hg i).target = D.S :=
  rfl

/-- **The charts of the sheets are algebraic.** If `e` is an algebraic chart of `Y(ℂ)`, then
`e ∘ g`, on the `i`-th sheet, is an algebraic chart of `X(ℂ)`. -/
theorem isAlgebraicChart_chart [IsAffine Y] (he : IsAlgebraicChart e) (i : Fin P.f.natDegree) :
    IsAlgebraicChart (D.chart hg i) where
  contDiffOn_evalExt V a := by
    refine contDiffOn_of_locally_contDiffOn fun k hk ↦ ?_
    obtain ⟨hkt, hkV⟩ := hk
    have hx : (D.sect hg i k).toHom (IsLocalRing.closedPoint ℂ) ∈ V :=
      (top_le_preimage_iff (D.sect hg i k) V).1 hkV
    obtain ⟨h, hhV, hxh⟩ := (isAffineOpen_top X).exists_basicOpen_le ⟨_, hx⟩ trivial
    obtain ⟨⟨b, ⟨_, m, rfl⟩⟩, hb⟩ := IsLocalization.mk'_surjective (Submonoid.powers h)
      (X.presheaf.map (homOfLE hhV).op a)
    set Dh := {p : UnderlyingSpace ℂ X | ⊤ ≤ p.toHom ⁻¹ᵁ X.basicOpen h}
    have hval : ∀ p ∈ Dh, evalExt V a p = evalTop p b / evalTop p h ^ m := by
      intro p hp
      have hpV : ⊤ ≤ p.toHom ⁻¹ᵁ V := hp.trans (Scheme.Hom.preimage_mono _ hhV)
      rw [evalExt_of_le a hpV, ← eval_restrict hhV p hp, ← hb]
      exact eval_mk' h b m p hp
    have hne : ∀ p ∈ Dh, evalTop p h ≠ 0 := fun p hp ↦
      (top_le_preimage_basicOpen_iff (U := ⊤) p (Scheme.Hom.preimage_top _).ge h).1 hp
    refine ⟨D.S ∩ D.sect hg i ⁻¹' Dh,
      (D.continuousOn_sect hg i).isOpen_inter_preimage D.isOpen (isOpen_setOf_le_preimage _),
      ⟨hkt, (top_le_preimage_iff (D.sect hg i k) _).2 hxh⟩, ?_⟩
    have hsub' : (D.chart hg i).target ∩ (D.chart hg i).symm ⁻¹'
        {p | ⊤ ≤ p.toHom ⁻¹ᵁ V} ∩ (D.S ∩ D.sect hg i ⁻¹' Dh) ⊆ D.S := fun k hk ↦ hk.1.1
    refine (((D.contDiffOn_evalTop_sect hg i b).mono hsub').div
      (((D.contDiffOn_evalTop_sect hg i h).mono hsub').pow m)
      fun k hk ↦ pow_ne_zero _ (hne _ hk.2.2)).congr fun k hk ↦ ?_
    exact hval _ hk.2.2
  exists_eq_evalExt q hq := by
    obtain ⟨V, ι, _, a, L, hV, hL⟩ := he.exists_eq_evalExt (mapFun g q) hq.1
    have hpre : ∀ q' : UnderlyingSpace ℂ X, ⊤ ≤ (mapFun g q').toHom ⁻¹ᵁ V ↔
        ⊤ ≤ q'.toHom ⁻¹ᵁ (g ⁻¹ᵁ V) := fun q' ↦ by
      rw [toHom_mapFun, Scheme.Hom.comp_preimage]
    refine ⟨g ⁻¹ᵁ V, ι, inferInstance, fun j ↦ g.app V (a j), L, (hpre q).1 hV, ?_⟩
    intro q' hq' hq'V
    rw [chart_apply, hL _ hq'.1 ((hpre q').2 hq'V)]
    exact congrArg L (funext fun j ↦ evalExt_mapFun g V (a j) q')

end SheetData

/-- Global sections of `Y` are holomorphic in an algebraic chart of `Y(ℂ)`. -/
lemma _root_.MMP.UnderlyingSpace.IsAlgebraicChart.contDiffOn_evalTop
    {e : OpenPartialHomeomorph (UnderlyingSpace ℂ Y) E} (he : IsAlgebraicChart e) (a : Γ(Y, ⊤)) :
    ContDiffOn ℂ ω (fun k ↦ evalTop (e.symm k) a) e.target :=
  ((he.contDiffOn_evalExt ⊤ a).mono fun _ hk ↦ ⟨hk, (Scheme.Hom.preimage_top _).ge⟩).congr
    fun _ _ ↦ (evalExt_of_le a _).symm

omit [X.Over (Spec (.of ℂ))] [IsAffine X] in
/-- **Sheet data exist over a ball.** Let `e` be an algebraic chart of `Y(ℂ)` at a point `w₀` with
`c(w₀) ≠ 0` and `δ(w₀) ≠ 0`. There are sheet data over a ball centred at `e(w₀)` on which `δ`
does not vanish. -/
theorem exists_sheetData [CompleteSpace E] {e : OpenPartialHomeomorph (UnderlyingSpace ℂ Y) E}
    (he : IsAlgebraicChart e) {w₀ : UnderlyingSpace ℂ Y} (hw₀ : w₀ ∈ e.source)
    (hc : evalTop w₀ P.c ≠ 0) (hδ : evalTop w₀ P.δ ≠ 0) :
    ∃ D : P.SheetData e, (∃ r, D.S = Metric.ball (e w₀) r) ∧ e w₀ ∈ D.S ∧
      ∀ k ∈ D.S, evalTop (e.symm k) P.δ ≠ 0 := by
  classical
  set ev : E → Γ(Y, ⊤) →+* ℂ := fun k ↦ evalHom (e.symm k)
  have ht : e.target ∈ 𝓝 (e w₀) := e.open_target.mem_nhds (e.map_source hw₀)
  have hev : ∀ i, ContDiffAt ℂ ω (fun k ↦ ev k (P.f.coeff i)) (e w₀) := fun i ↦
    (he.contDiffOn_evalTop _).contDiffAt ht
  have h0 : ev (e w₀) = evalHom w₀ := by simp only [ev, e.left_inv hw₀]
  have hsep : (P.f.map (ev (e w₀))).Separable := h0 ▸ P.separable_map (evalHom w₀) hδ
  obtain ⟨φ, -, hφ⟩ := exists_analytic_sheets P.monic ev hev hsep
  set R₀ := (P.f.map (ev (e w₀))).roots.toFinset
  have hcard : R₀.card = P.f.natDegree := by
    rw [SmoothLocusConnected.card_roots_toFinset_of_separable hsep, P.monic.natDegree_map]
  set σ : Fin P.f.natDegree ≃ R₀ := (R₀.equivFinOfCardEq hcard).symm
  have hcont : ∀ a : Γ(Y, ⊤), ContinuousAt (fun k ↦ ev k a) (e w₀) := fun a ↦
    (he.contDiffOn_evalTop a).continuousOn.continuousAt ht
  have hcδ : ∀ᶠ k in 𝓝 (e w₀), ev k P.c ≠ 0 ∧ ev k P.δ ≠ 0 :=
    ((hcont P.c).eventually_ne (by rwa [h0])).and ((hcont P.δ).eventually_ne (by rwa [h0]))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hφ.and (hcδ.and ht))
  have hroot : ∀ k ∈ Metric.ball (e w₀) ε, ∀ t, (P.f.map (ev k)).eval t = 0 ↔
      t ∈ R₀.image fun r ↦ φ r k := fun k hk t ↦ by
    rw [← (hball hk).1.2.2, Multiset.mem_toFinset, mem_roots (P.monic.map _).ne_zero, IsRoot.def]
  refine ⟨⟨Metric.ball (e w₀) ε, fun i ↦ φ (σ i), Metric.isOpen_ball, ⟨_, Metric.mem_ball_self hε⟩,
    fun k hk ↦ (hball hk).2.2, fun k hk ↦ (hball hk).2.1.1,
    fun i k hk ↦ ((hball hk).1.1 _ (σ i).2).contDiffWithinAt,
    fun a ↦ (he.contDiffOn_evalTop a).mono fun k hk ↦ (hball hk).2.2,
    fun i k hk ↦ (hroot k hk _).2 (Finset.mem_image_of_mem _ (σ i).2),
    fun k hk i j hij ↦ σ.injective (Subtype.ext ((hball hk).1.2.1 (σ i).2 (σ j).2 hij)),
    fun k hk t ht ↦ ?_⟩, ⟨ε, rfl⟩, Metric.mem_ball_self hε, fun k hk ↦ (hball hk).2.1.2⟩
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ((hroot k hk t).1 ht)
  exact ⟨σ.symm ⟨r, hr⟩, by simp⟩

end CoveringPresentation

end MMP.GenericCovering
