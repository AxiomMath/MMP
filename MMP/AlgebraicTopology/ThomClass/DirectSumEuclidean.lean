module

public import MMP.AlgebraicTopology.FundamentalClass.Product
public import MMP.AlgebraicTopology.ThomClass.Natural
public import MMP.AlgebraicTopology.BorelMoore.ExteriorProductRestriction
public import MMP.AlgebraicTopology.FundamentalClass.Locality
public import MMP.AlgebraicTopology.CapProduct.Cup

/-!
# The cup product of the Thom classes of two Euclidean spaces (Fulton, §19.1)

Let `V`, `W` be real vector spaces oriented by bases `b`, `b'`, and let `α`, `β` be relative
cocycles of `(V, V - 0)` and `(W, W - 0)` taking the value `1` on the oriented simplices around
`0` (cocycles representing the Thom classes, i.e. the orientation classes). Pull them back to
`V × W` along the projections: they become relative cocycles of `(V × W, A)` and `(V × W, B)`,
`A = (V - 0) × W`, `B = V × (W - 0)`, with `A ∪ B = V × W - 0`. Their relative cup product
`θ = ρ^* (a ∪ b)` (`ρ` the small-chains map of the open couple `{A, B}`) takes the value `1` on
every simplex around `0` oriented for the product basis `b × b'`. This is the computation behind
"the Thom class of a direct sum is the cup product of the Thom classes" (Milnor–Stasheff,
Lemma 9.6 / Thm. 10.4).

The proof is the one of the product formula for fundamental classes. Choose oriented simplices
`Δ` around `0` in `V` and `Δ'` in `W` with barycentric coordinates of `0` above `1/2` at the last
vertex of `Δ` and at the first vertex of `Δ'`. Since `θ` is a relative cocycle of
`(V × W, V × W - 0)`, its value on an oriented simplex is that on the corner simplex of the
shuffle triangulation of `Δ × Δ'`, the only simplex of the triangulation through `0`, hence its
value on the cross product `Δ × Δ'`. As `a ∪ b` is a cocycle, `θ - a ∪ b` is the coboundary of a
cochain vanishing on `A` and on `B`, and the Leibniz rule `∂(Δ × Δ') = ∂Δ × Δ' ± Δ × ∂Δ'` puts
the boundary of `Δ × Δ'` in `A` and `B`; so `θ` and `a ∪ b` agree on `Δ × Δ'`. By the
Alexander–Whitney formula only the corner simplex contributes to `(a ∪ b)(Δ × Δ')`: the front
face of every other simplex of the triangulation projects into the face of `Δ` opposite its last
vertex, which misses `0`. On the corner simplex the front face projects to `Δ` and the back face
to `Δ'`, giving `α(Δ) β(Δ') = 1`.

## Main results

* `MMP.SingularChain.evalSimp_pullback_smallChainMap_crossSimplex`: the
  small-chains correction does not change the value of a cocycle on `σ × τ` when `∂σ ⊆ A`,
  `∂τ ⊆ B`.
* `MMP.SingularChain.evalSimp_cup_cochainPullback_crossSimplex`: the
  Alexander–Whitney evaluation `(pr₁^* α ∪ pr₂^* β)(σ × τ) = α(σ) β(τ)`.
* `MMP.ThomClass.relCupCochain_cochainPullback_fst_snd_affineSimplex`: the
  relative cup product of the Euclidean orientation cocycles is `1` on oriented simplices of
  `V × W` around `0`.

## Implementation notes

The degree of the cup product is any `n` with `p + q = n`, and the product basis is reindexed
along `finCongr`, so that the statement applies when `n` is not definitionally `p + q`. The
spaces are `T₁`, so that `V - 0` and `W - 0` are open.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [J. Milnor, J. Stasheff, *Characteristic classes*][milnorstasheff1974], §§9–10.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Simplicial Finsupp Set MMP.LatticePath
  MMP.SingularCross MMP.SingularChain
  MMP.SingularCochain MMP.FundamentalClass

universe u

namespace MMP

open MMP

namespace LatticePath

/-- The `j`-th vertex `(a, b)` of a path of the shuffle sum satisfies `a + b = j`. -/
lemma getD_fst_add_snd_of_mem_support {m p q : ℕ} {l : List (ℕ × ℕ)}
    (h : l ∈ (shuffleSum m p q).support) {j : ℕ} (hj : j < l.length) :
    (l.getD j (0, 0)).1 + (l.getD j (0, 0)).2 = j := by
  classical
  induction m generalizing p q l j with
  | zero =>
    simp only [shuffleSum] at h
    split_ifs at h with hpq
    · rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at h
      subst h
      obtain rfl : j = 0 := by simpa using hj
      rfl
    · simp at h
  | succ m ih =>
    rw [shuffleSum_succ] at h
    rcases Finset.mem_union.1 (Finsupp.support_add h) with h | h
    · rcases p with _ | p
      · simp at h
      obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support h)
      rcases j with _ | j
      · rfl
      · simp only [stepFst, List.length_cons, List.length_map] at hj
        have := ih hl' (j := j) (by omega)
        have hjl : j < l'.length := by omega
        have e : (stepFst l').getD (j + 1) (0, 0) =
            (fun x : ℕ × ℕ ↦ (x.1 + 1, x.2)) (l'.getD j (0, 0)) := by
          rw [List.getD_eq_getElem _ _ (by simp [stepFst]; omega), List.getD_eq_getElem _ _ hjl]
          simp [stepFst]
        rw [e]
        dsimp only
        omega
    · have h := Finsupp.support_smul h
      rcases q with _ | q
      · simp at h
      obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support h)
      rcases j with _ | j
      · rfl
      · simp only [stepSnd, List.length_cons, List.length_map] at hj
        have := ih hl' (j := j) (by omega)
        have hjl : j < l'.length := by omega
        have e : (stepSnd l').getD (j + 1) (0, 0) =
            (fun x : ℕ × ℕ ↦ (x.1, x.2 + 1)) (l'.getD j (0, 0)) := by
          rw [List.getD_eq_getElem _ _ (by simp [stepSnd]; omega), List.getD_eq_getElem _ _ hjl]
          simp [stepSnd]
        rw [e]
        dsimp only
        omega

/-- A path of the shuffle sum `∇_{p,q}` other than the corner path reaches the first coordinate
`p` only after its `p`-th vertex. -/
lemma fst_getD_lt_of_mem_support {m p q : ℕ} {l : List (ℕ × ℕ)}
    (h : l ∈ (shuffleSum m p q).support) (hl : l ≠ cornerPath p q) {j : ℕ} (hjp : j ≤ p)
    (hj : j < l.length) : (l.getD j (0, 0)).1 < p := by
  have hs := getD_fst_add_snd_of_mem_support h hj
  by_contra hlt
  apply hl
  apply eq_cornerPath_of_mem_support h
  have hpt : ((p, 0) : ℕ × ℕ) = l.getD j (0, 0) := Prod.ext (by omega) (by omega)
  rw [hpt, List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

end LatticePath

namespace ThomClass

section Faces

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V]
  [ContinuousSMul ℝ V]

/-- The boundary of an oriented simplex around `0` is a chain of `V - 0`. -/
lemma IsOrientedSimplexAroundZero.bdSub_single_mem_inside {p : ℕ} {b : Module.Basis (Fin p) ℝ V}
    {v : Fin (p + 1) → V} (h : IsOrientedSimplexAroundZero b v) :
    bdSub ℤ p (single (affineSimplex v) 1) ∈ inside ℤ (p - 1) ({0}ᶜ : Set V) := by
  cases p with
  | zero => simp
  | succ m =>
    rw [bdSub_succ, bd_single]
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ ?_
    refine single_mem_supported ℤ _ ?_
    rintro _ ⟨t, rfl⟩
    refine h.affineSimplex_ne_zero _ ⟨i, ?_⟩
    change (stdSimplex.map i.succAbove t : Fin (m + 2) → ℝ) i = 0
    rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    exact absurd (Finset.mem_filter.1 hk).2 (Fin.succAbove_ne i k)

end Faces

end ThomClass

namespace SingularChain

variable {R : Type u} [CommRing R] {X Y : TopCat.{u}}

/-- A coboundary of a cochain vanishing on the simplices of `A × Y` and on those of `X × B`
vanishes on `σ × τ` when `∂ σ` is a chain of `A` and `∂ τ` a chain of `B`. -/
lemma linearCombination_crossSimplexChain_eq_zero {N p q : ℕ} {σ : Simplex X p}
    {τ : Simplex Y q} {A : Set X} {B : Set Y} (hσ : bdSub ℤ p (single σ 1) ∈ inside ℤ (p - 1) A)
    (hτ : bdSub ℤ q (single τ 1) ∈ inside ℤ (q - 1) B) {χ : Simplex (X × Y) N → R}
    (hχ : χ ∈ pairCoboundaries R (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B) N) :
    linearCombination ℤ χ (crossSimplexChain N σ τ) = 0 := by
  cases N with
  | zero =>
    rw [show χ = 0 from (Submodule.mem_bot R).1 hχ]
    simp
  | succ n =>
    obtain ⟨γ, ⟨hγA, hγB⟩, rfl⟩ := hχ
    rw [← linearCombination_int_bd, bd_crossSimplexChain, map_add, map_smul,
      linearCombination_int_eq_zero_of_mem_inside hγA (supported_mono ?_
        (cross_mem_inside n hσ (single_mem_supported ℤ (1 : ℤ) (subset_univ (range τ))))),
      linearCombination_int_eq_zero_of_mem_inside hγB (supported_mono ?_
        (cross_mem_inside n (single_mem_supported ℤ (1 : ℤ) (subset_univ (range σ))) hτ)),
      smul_zero, add_zero]
    · exact fun ρ (hρ : range ρ ⊆ _) ↦ hρ.trans fun _ hx ↦ hx.2
    · exact fun ρ (hρ : range ρ ⊆ _) ↦ hρ.trans fun _ hx ↦ hx.1

/-- Evaluation of a cochain on a chain of simplicial singular simplices is evaluation on its
image in singular chains. -/
lemma evalSimp_eq_linearCombination {Z : TopCat.{u}} {m : ℕ} (φ : Simplex Z m → R)
    (c : Simp Z m →₀ ℤ) :
    FundamentalClass.evalSimp φ c =
      linearCombination ℤ φ (Finsupp.mapDomain (fun ρ ↦ (SingularCochain.simplexEquiv _ _ ρ : Simplex Z m)) c) := by
  rw [FundamentalClass.evalSimp, Finsupp.linearCombination_mapDomain]
  rfl

/-- **The small-chains correction on a cross product.** For a cocycle `χ` of `X × Y` and
simplices `σ`, `τ` whose boundaries are chains of `A` and of `B`, the pull-back of `χ` along the
small-chains map `ρ` of the open couple `{A × Y, X × B}` takes the same value as `χ` on the
cross product `σ × τ`. -/
lemma evalSimp_pullback_smallChainMap_crossSimplex {N p q : ℕ} (σ : Simp X p) (τ : Simp Y q)
    {A : Set X} {B : Set Y} (hσ : bdSub ℤ p (single (SingularCochain.simplexEquiv _ _ σ) 1) ∈ inside ℤ (p - 1) A)
    (hτ : bdSub ℤ q (single (SingularCochain.simplexEquiv _ _ τ) 1) ∈ inside ℤ (q - 1) B)
    {χ : Simplex (TopCat.of (X × Y)) N → R} (hχ : coboundary R N χ = 0) :
    FundamentalClass.evalSimp
        (pullback (smallChainMap R {Prod.fst ⁻¹' A, Prod.snd ⁻¹' B} N) χ)
        (crossSimplex N σ τ) =
      FundamentalClass.evalSimp χ (crossSimplex N σ τ) := by
  have h := linearCombination_crossSimplexChain_eq_zero (R := R) hσ hτ
    (pullback_smallChainMap_sub_mem_pairCoboundaries (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B) hχ)
  rw [crossSimplexChain_toC] at h
  rw [evalSimp_eq_linearCombination, evalSimp_eq_linearCombination, ← sub_eq_zero, ← h,
    linearCombination_apply, linearCombination_apply, linearCombination_apply, Finsupp.sum,
    Finsupp.sum, Finsupp.sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ρ _ ↦ ?_
  rw [Pi.sub_apply, smul_sub]

/-- **The Alexander–Whitney evaluation on the shuffle triangulation.** Let `α` be a `p`-cochain
of `X` vanishing on the simplices of `A`, where `σ` maps the face of `Δᵖ` opposite its last
vertex into `A`. On the cross product `σ × τ`, the cup product of the pull-backs of `α` and of a
`q`-cochain `β` along the projections takes the value `α(σ) β(τ)`: only the corner simplex of the
shuffle triangulation contributes. -/
lemma evalSimp_cup_cochainPullback_crossSimplex {p q : ℕ} (σ : Simp X p) (τ : Simp Y q)
    {A : Set X} {α : Simplex X p → R} (hα : α ∈ vanishing R p A)
    (hσ : ∀ t : stdSimplex ℝ (Fin (p + 1)), (t : Fin (p + 1) → ℝ) (Fin.last p) = 0 →
      SingularCochain.simplexEquiv _ _ σ t ∈ A) (β : Simplex Y q → R) :
    FundamentalClass.evalSimp
        (cup p q (p + q) rfl
          (cochainPullback R (TopCat.ofHom (ContinuousMap.fst : C(X × Y, X))) p α)
          (cochainPullback R (TopCat.ofHom (ContinuousMap.snd : C(X × Y, Y))) q β))
        (crossSimplex (p + q) σ τ) =
      α (SingularCochain.simplexEquiv _ _ σ) * β (SingularCochain.simplexEquiv _ _ τ) := by
  classical
  rw [FundamentalClass.evalSimp, crossSimplex, Finsupp.linearCombination_mapDomain,
    Finsupp.linearCombination_apply, Finsupp.sum,
    Finset.sum_eq_single (cornerPath p q) ?_ ?_, shuffleSum_cornerPath, one_smul]
  · simp only [Function.comp_apply]
    rw [cup_apply, cochainPullback_apply, cochainPullback_apply]
    congr 2
    · ext1 t
      change (SingularCochain.simplexEquiv _ _ (pathSimplex (p + q) σ τ (cornerPath p q)) (smap _ t)).1 = _
      rw [FundamentalClass.toC_pathSimplex_apply, FundamentalClass.vtx_cornerPath_fst]
      change SingularCochain.simplexEquiv _ _ σ (stdSimplex.map _ (stdSimplex.map _ t)) = _
      rw [stdSimplex.map_comp_apply]
      congr 1
      convert stdSimplex.map_id_apply t
      funext j
      apply Fin.ext
      have := j.isLt
      simp only [Function.comp_apply, front_val, id]
      omega
    · ext1 t
      change (SingularCochain.simplexEquiv _ _ (pathSimplex (p + q) σ τ (cornerPath p q)) (smap _ t)).2 = _
      rw [FundamentalClass.toC_pathSimplex_apply, FundamentalClass.vtx_cornerPath_snd]
      change SingularCochain.simplexEquiv _ _ τ (stdSimplex.map _ (stdSimplex.map _ t)) = _
      rw [stdSimplex.map_comp_apply]
      congr 1
      convert stdSimplex.map_id_apply t
      funext j
      apply Fin.ext
      simp [back_val]
  · intro L hL hLc
    simp only [Function.comp_apply]
    rw [cup_apply, cochainPullback_apply, hα _ ?_, zero_mul, smul_zero]
    rintro _ ⟨t, rfl⟩
    change (SingularCochain.simplexEquiv _ _ (pathSimplex (p + q) σ τ L) (smap _ t)).1 ∈ A
    rw [FundamentalClass.toC_pathSimplex_apply]
    change SingularCochain.simplexEquiv _ _ σ (stdSimplex.map _ (stdSimplex.map _ t)) ∈ A
    rw [stdSimplex.map_comp_apply]
    refine hσ _ ?_
    rw [FundamentalClass.stdSimplex_map_apply]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    exfalso
    have hj' := congrArg Fin.val (Finset.mem_filter.1 hj).2
    have hlen := (mem_support_shuffleSum hL).1
    have := fst_getD_lt_of_mem_support hL hLc (j := j) (by omega) (by omega)
    simp only [Function.comp_apply, vtx, front_val, Fin.val_last] at hj'
    omega
  · intro h
    exact absurd (Finsupp.mem_support_iff.2 (by rw [shuffleSum_cornerPath]; exact one_ne_zero)) h

end SingularChain

namespace ThomClass

section Product

variable {R : Type u} [CommRing R] {V W : Type u} [AddCommGroup V] [Module ℝ V]
  [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V] [AddCommGroup W] [Module ℝ W]
  [TopologicalSpace W] [ContinuousAdd W] [ContinuousSMul ℝ W] [T1Space V] [T1Space W]

/-- **The cup product of the Euclidean Thom classes**, in degree `p + q`. Let `α`, `β` be
relative cocycles of `(V, V - 0)`, `(W, W - 0)` taking the value `1` on the oriented simplices
around `0` for the bases `b`, `b'`. Then the relative cup product of their pull-backs along the
projections, a relative cocycle of `(V × W, V × W - 0)`, takes the value `1` on every simplex
around `0` oriented for the product basis `b × b'`. -/
theorem relCupCochain_cochainPullback_fst_snd_affineSimplex_add {p q : ℕ}
    (b : Module.Basis (Fin p) ℝ V) (b' : Module.Basis (Fin q) ℝ W)
    {α : Simplex V p → R} (hα : α ∈ relCocycles R ({0}ᶜ : Set V) p)
    (hα1 : ∀ v, IsOrientedSimplexAroundZero b v → α (affineSimplex v) = 1)
    {β : Simplex W q → R} (hβ : β ∈ relCocycles R ({0}ᶜ : Set W) q)
    (hβ1 : ∀ v, IsOrientedSimplexAroundZero b' v → β (affineSimplex v) = 1)
    {w : Fin (p + q + 1) → V × W}
    (hw : IsOrientedSimplexAroundZero ((b.prod b').reindex finSumFinEquiv) w) :
    relCupCochain (Y := V × W) (A := Prod.fst ⁻¹' ({0}ᶜ : Set V))
        (B := Prod.snd ⁻¹' ({0}ᶜ : Set W)) p q (p + q) rfl
        (cochainPullback R (TopCat.ofHom (ContinuousMap.fst : C(V × W, V))) p α)
        (cochainPullback R (TopCat.ofHom (ContinuousMap.snd : C(V × W, W))) q β)
        (affineSimplex w) = 1 := by
  classical
  set l : Fin (p + 1) → ℝ := fun k ↦ 1 / (2 * ((p : ℝ) + 1)) + if k = Fin.last p then 1 / 2 else 0
  set l' : Fin (q + 1) → ℝ := fun k ↦ 1 / (2 * ((q : ℝ) + 1)) + if k = 0 then 1 / 2 else 0
  have hl0 : ∀ k, 0 < l k := fun k ↦ by
    simp only [l]
    split_ifs <;> positivity
  have hl0' : ∀ k, 0 < l' k := fun k ↦ by
    simp only [l']
    split_ifs <;> positivity
  have hl1 : ∑ k, l k = 1 := by
    simp only [l, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
    ring
  have hl1' : ∑ k, l' k = 1 := by
    simp only [l', Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
    ring
  have hll : 1 < l (Fin.last p) + l' 0 := by
    simp only [l, l', ite_true]
    have : 0 < 1 / (2 * ((p : ℝ) + 1)) := by positivity
    have : 0 < 1 / (2 * ((q : ℝ) + 1)) := by positivity
    linarith
  obtain ⟨v, hv, hlv, -⟩ := exists_isOrientedSimplexAroundZero_barycentric b (0 : V)
    Filter.univ_mem hl0 hl1
  obtain ⟨v', hv', hlv', -⟩ := exists_isOrientedSimplexAroundZero_barycentric b' (0 : W)
    Filter.univ_mem hl0' hl1'
  have hv0 : IsOrientedSimplexAroundZero b v := by simpa using hv
  have hv0' : IsOrientedSimplexAroundZero b' v' := by simpa using hv'
  set σ₀ : Simp (TopCat.of V) p := (SingularCochain.simplexEquiv (TopCat.of V) p).symm (affineSimplex v)
  set τ₀ : Simp (TopCat.of W) q :=
    (SingularCochain.simplexEquiv (TopCat.of W) q).symm (affineSimplex v')
  have hσ₀ : SingularCochain.simplexEquiv _ _ σ₀ = affineSimplex v := toC_symm_apply _
  have hτ₀ : SingularCochain.simplexEquiv _ _ τ₀ = affineSimplex v' := toC_symm_apply _
  set A : Set (V × W) := Prod.fst ⁻¹' ({0}ᶜ : Set V)
  set B : Set (V × W) := Prod.snd ⁻¹' ({0}ᶜ : Set W)
  have hA : IsOpen A := isOpen_compl_singleton.preimage continuous_fst
  have hB : IsOpen B := isOpen_compl_singleton.preimage continuous_snd
  have hAB : A ∪ B = ({0}ᶜ : Set (V × W)) := by
    ext ⟨x, y⟩
    simp only [A, B, mem_union, mem_preimage, mem_compl_iff, mem_singleton_iff, Prod.ext_iff,
      Prod.fst_zero, Prod.snd_zero]
    tauto
  set a := cochainPullback R (TopCat.ofHom (ContinuousMap.fst : C(V × W, V))) p α
  set c := cochainPullback R (TopCat.ofHom (ContinuousMap.snd : C(V × W, W))) q β
  have ha : a ∈ relCocycles R A p :=
    cochainPullback_mem_relCocycles (TopCat.ofHom (ContinuousMap.fst : C(V × W, V)))
      (A' := A) (A := ({0}ᶜ : Set V)) (fun _ hx ↦ hx) hα
  have hc : c ∈ relCocycles R B q :=
    cochainPullback_mem_relCocycles (TopCat.ofHom (ContinuousMap.snd : C(V × W, W)))
      (A' := B) (A := ({0}ᶜ : Set W)) (fun _ hx ↦ hx) hβ
  have hδ : coboundary R (p + q) (cup p q (p + q) rfl a c) = 0 :=
    coboundary_cup_eq_zero p q _ rfl ha.2 hc.2
  have hθ : relCupCochain (A := A) (B := B) p q (p + q) rfl a c ∈
      relCocycles R ({0}ᶜ : Set (V × W)) (p + q) := by
    rw [← hAB]
    exact relCupCochain_mem_relCocycles hA hB p q _ rfl ha hc
  set θ := relCupCochain (A := A) (B := B) p q (p + q) rfl a c
  have hcor := isOrientedSimplexAroundZero_cornerVertices (b := b) (b' := b') hv hv' hl0 hl1 hlv
    hl0' hl1' hlv' hll
  have hfst : ∀ t : stdSimplex ℝ (Fin (p + q + 1)),
      (affineSimplex (cornerVertices v v') t).1 = affineSimplex v
        (stdSimplex.map (fun j : Fin (p + q + 1) ↦ (⟨min j p, by omega⟩ : Fin (p + 1))) t) :=
    fun t ↦ by
      rw [affineSimplex_apply, affineSimplex_apply, sum_stdSimplex_map_smul, Prod.fst_sum]
      rfl
  have hsnd : ∀ t : stdSimplex ℝ (Fin (p + q + 1)),
      (affineSimplex (cornerVertices v v') t).2 = affineSimplex v'
        (stdSimplex.map (fun j : Fin (p + q + 1) ↦ (⟨j - p, by omega⟩ : Fin (q + 1))) t) :=
    fun t ↦ by
      rw [affineSimplex_apply, affineSimplex_apply, sum_stdSimplex_map_smul, Prod.snd_sum]
      rfl
  have step1 : θ (affineSimplex w) =
      θ (SingularCochain.simplexEquiv _ _ (pathSimplex (p + q) σ₀ τ₀ (cornerPath p q))) := by
    refine (isLocallyHomologous_of_isOrientedSimplexAroundZero
      (OpenPartialHomeomorph.refl (V × W)) (x := 0) (mem_univ _)
      (b := (b.prod b').reindex finSumFinEquiv) (v := w) (w := cornerVertices v v')
      (by simpa using hw) (subset_univ _) (by simpa [← Prod.zero_eq_mk] using hcor)
      (subset_univ _)
      (fun t ↦ rfl) (fun t ↦ ?_)).apply_eq hθ
    rw [toC_pathSimplex_apply, vtx_cornerPath_fst, vtx_cornerPath_snd]
    refine Prod.ext ?_ ?_
    · change SingularCochain.simplexEquiv _ _ σ₀ _ = _
      rw [hσ₀]
      exact (hfst t).symm
    · change SingularCochain.simplexEquiv _ _ τ₀ _ = _
      rw [hτ₀]
      exact (hsnd t).symm
  have hσ : ∀ x, SingularCochain.simplexEquiv _ _ σ₀ x = (0 : V) → (x : Fin (p + 1) → ℝ) = l := fun x hx ↦
    eq_of_affineSimplex_eq hv hl1 hlv x (by rw [← hσ₀]; exact hx)
  have hτ : ∀ x, SingularCochain.simplexEquiv _ _ τ₀ x = (0 : W) → (x : Fin (q + 1) → ℝ) = l' := fun x hx ↦
    eq_of_affineSimplex_eq hv' hl1' hlv' x (by rw [← hτ₀]; exact hx)
  have step2 : θ (SingularCochain.simplexEquiv _ _ (pathSimplex (p + q) σ₀ τ₀ (cornerPath p q))) =
      evalSimp θ (crossSimplex (p + q) σ₀ τ₀) := by
    rw [evalSimp, crossSimplex, Finsupp.linearCombination_mapDomain,
      Finsupp.linearCombination_apply, Finsupp.sum,
      Finset.sum_eq_single (cornerPath p q) ?_ ?_, shuffleSum_cornerPath, one_smul]
    · rfl
    · intro L hL hLc
      simp only [Function.comp_apply]
      rw [hθ.1 _ ?_, smul_zero]
      intro pt hpt hpt'
      rw [Set.mem_singleton_iff.1 hpt'] at hpt
      obtain ⟨t, ht⟩ := hpt
      exact notMem_range_pathSimplex hL hLc hσ hτ hll ⟨SingularChain.stdSimplexHomeo _ t, ht⟩
    · intro h
      exact absurd (Finsupp.mem_support_iff.2 (by rw [shuffleSum_cornerPath]; exact one_ne_zero)) h
  have step3 : evalSimp θ (crossSimplex (p + q) σ₀ τ₀) =
      evalSimp (cup p q (p + q) rfl a c) (crossSimplex (p + q) σ₀ τ₀) :=
    evalSimp_pullback_smallChainMap_crossSimplex σ₀ τ₀ (A := ({0}ᶜ : Set V))
      (B := ({0}ᶜ : Set W)) (by rw [hσ₀]; exact hv0.bdSub_single_mem_inside)
      (by rw [hτ₀]; exact hv0'.bdSub_single_mem_inside) hδ
  have step4 : evalSimp (cup p q (p + q) rfl a c) (crossSimplex (p + q) σ₀ τ₀) = 1 := by
    rw [evalSimp_cup_cochainPullback_crossSimplex σ₀ τ₀ hα.1 ?_ β, hσ₀, hτ₀, hα1 v hv0,
      hβ1 v' hv0', one_mul]
    intro t ht
    rw [hσ₀]
    exact hv0.affineSimplex_ne_zero t ⟨_, ht⟩
  exact step1.trans (step2.trans (step3.trans step4))

/-- **The cup product of the Euclidean Thom classes.** Let `α`, `β` be relative cocycles of
`(V, V - 0)`, `(W, W - 0)` taking the value `1` on the oriented simplices around `0` for the
bases `b`, `b'`. Then the relative cup product of their pull-backs along the projections, a
relative cocycle of `(V × W, V × W - 0)` of degree `n = p + q`, takes the value `1` on every
simplex around `0` oriented for the product basis `b × b'`. -/
theorem relCupCochain_cochainPullback_fst_snd_affineSimplex {p q n : ℕ} (h : p + q = n)
    (b : Module.Basis (Fin p) ℝ V) (b' : Module.Basis (Fin q) ℝ W)
    {α : Simplex V p → R} (hα : α ∈ relCocycles R ({0}ᶜ : Set V) p)
    (hα1 : ∀ v, IsOrientedSimplexAroundZero b v → α (affineSimplex v) = 1)
    {β : Simplex W q → R} (hβ : β ∈ relCocycles R ({0}ᶜ : Set W) q)
    (hβ1 : ∀ v, IsOrientedSimplexAroundZero b' v → β (affineSimplex v) = 1)
    {w : Fin (n + 1) → V × W}
    (hw : IsOrientedSimplexAroundZero
      (((b.prod b').reindex finSumFinEquiv).reindex (finCongr h)) w) :
    relCupCochain (Y := V × W) (A := Prod.fst ⁻¹' ({0}ᶜ : Set V))
        (B := Prod.snd ⁻¹' ({0}ᶜ : Set W)) p q n h
        (cochainPullback R (TopCat.ofHom (ContinuousMap.fst : C(V × W, V))) p α)
        (cochainPullback R (TopCat.ofHom (ContinuousMap.snd : C(V × W, W))) q β)
        (affineSimplex w) = 1 := by
  subst h
  have e : ((b.prod b').reindex finSumFinEquiv).reindex (finCongr rfl) =
      (b.prod b').reindex finSumFinEquiv := by
    refine Module.Basis.eq_of_apply_eq fun i ↦ ?_
    rw [Module.Basis.reindex_apply]
    rfl
  rw [e] at hw
  exact relCupCochain_cochainPullback_fst_snd_affineSimplex_add b b' hα hα1 hβ hβ1 hw

end Product

end ThomClass

end MMP
