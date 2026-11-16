module

public import MMP.AlgebraicTopology.FundamentalClass.CrossSlant
public import MMP.AlgebraicTopology.SingularHomology.ChartSimplexLocalHomology
public import MMP.AlgebraicTopology.SingularHomology.PrismCornerSimplex
public import MMP.AlgebraicTopology.SingularHomology.ShuffleSumCornerPath
public import MMP.AlgebraicTopology.FundamentalClass.Basic
/-!
# The fundamental class of a product of manifolds (Fulton, §19.1)

For oriented manifolds `M`, `N` of dimensions `n`, `n'`, with the product orientation on
`M × N`, the fundamental classes satisfy `μ_{M × N} = μ_M × μ_N`.

The proof is local. In a product chart `e × e'` at `(x, y)`, choose oriented affine simplices
`Δ` around `e x` and `Δ'` around `e' y`. The class `μ_M` is locally the class of `e⁻¹ ∘ Δ` at
`x` and `μ_N` that of `e'⁻¹ ∘ Δ'` at `y`; by the slant identity
(`MMP.FundamentalClass.localPairing_crossFun_eq_evalSimp`) `μ_M × μ_N` is locally
the class of the chain `e⁻¹ ∘ Δ × e'⁻¹ ∘ Δ'`. This chain is the image under `(e × e')⁻¹` of the
shuffle triangulation of the prism `Δ × Δ'`. With `Δ`, `Δ'` chosen so that the barycentric
coordinates of `e x` at the last vertex of `Δ` and of `e' y` at the first vertex of `Δ'` exceed
`1/2`, the point `(e x, e' y)` lies only in the simplex of the triangulation along the lattice
path `(0, 0), (1, 0), …, (n, 0), (n, 1), …, (n, n')`, which has coefficient `1` and is positively
oriented for the product orientation. So `μ_M × μ_N` is locally the class of an oriented simplex
of the product chart, hence of every such simplex
(`MMP.FundamentalClass.isLocallyHomologous_of_isOrientedSimplexAroundZero`).

## Main results

* `MMP.FundamentalClass.localPairing_eq_of_exteriorProduct`: the local pairings
  of a cycle representing `μ × ν` are those of the cross product of cycles representing `μ`,
  `ν`.
* `MMP.IsFundamentalClass.exteriorProduct`: `μ_{M × N} = μ_M × μ_N`.

## Implementation notes

The product `M × N` of charted spaces is modelled on `ModelProd H H'`, a type synonym for
`H × H'`; the real vector space and topological module structures of `H × H'` are transported
to it. The product orientation is that of the basis `b × b'` of `H × H'`, indexed by
`Fin (n + n')` through `finSumFinEquiv`: the vectors of `b` followed by those of `b'`. The
class `μ_M × μ_N` lies in degree `n + n'` of `ℤ`, identified with `(n + n' : ℕ)` by
`MMP.BorelMooreCross.congrDegree`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [B. Iversen, *Cohomology of Sheaves*][iversen1986], IX.4.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Simplicial Finsupp Set MMP.LatticePath
  MMP.SingularCross MMP.SingularChain
  MMP.SingularCochain MMP.BorelMooreCross
  MMP.LocallyFiniteChain MMP.ThomClass

universe u

namespace MMP

namespace FundamentalClass

variable {R : Type u} [CommRing R]

section Representatives

variable {X Y : TopCat.{u}}

/-- On the class of a cycle `z`, the identification of Borel–Moore homology with cycles modulo
boundaries is the class of `z`. -/
lemma homologyEquiv_eq_mk {n : ℕ} {θ : borelMooreHomology R (ModuleCat.of R R) X n}
    (z : (borelMooreChainComplex R (ModuleCat.of R R) X).cycles n)
    (hz : (borelMooreChainComplex R (ModuleCat.of R R) X).homologyπ n z =
      (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) X n).hom θ) :
    homologyEquiv R X n θ = Submodule.Quotient.mk
      (((borelMooreChainComplex R (ModuleCat.of R R) X).sc n).moduleCatCyclesIso.hom.hom z) := by
  change ((BM R X).sc n).moduleCatHomologyIso.hom.hom
    ((borelMooreHomologyIsoOfNat R (ModuleCat.of R R) X n).hom.hom θ) = _
  rw [← hz]
  exact ShortComplex.π_moduleCatCyclesIso_hom_apply _ z

/-- The underlying chain of the image of a cycle `z` under `moduleCatCyclesIso` is the chain
`iCycles z`. -/
lemma coe_moduleCatCyclesIso_hom {n : ℕ}
    (z : (borelMooreChainComplex R (ModuleCat.of R R) X).cycles n) :
    (((borelMooreChainComplex R (ModuleCat.of R R) X).sc n).moduleCatCyclesIso.hom.hom z).1 =
      (borelMooreChainComplex R (ModuleCat.of R R) X).iCycles n z :=
  ShortComplex.moduleCatCyclesIso_hom_i_apply _ z

/-- **Representatives of exterior products.** For cycles `z`, `w` representing `μ ∈ H_p X` and
`ν ∈ H_q Y`, a cycle `Z` representing `μ × ν` and a relative cocycle `φ` of
`(X × Y, X × Y - x)`, `⟨φ, Z⟩ = ⟨φ, z × w⟩`. -/
theorem localPairing_eq_of_exteriorProduct {p q : ℕ}
    {μ : borelMooreHomology R (ModuleCat.of R R) X p}
    {ν : borelMooreHomology R (ModuleCat.of R R) Y q}
    (z : (borelMooreChainComplex R (ModuleCat.of R R) X).cycles p)
    (hz : (borelMooreChainComplex R (ModuleCat.of R R) X).homologyπ p z =
      (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) X p).hom μ)
    (w : (borelMooreChainComplex R (ModuleCat.of R R) Y).cycles q)
    (hw : (borelMooreChainComplex R (ModuleCat.of R R) Y).homologyπ q w =
      (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) Y q).hom ν)
    (Z : (borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of (X × Y))).cycles (p + q))
    (hZ : (borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of (X × Y))).homologyπ (p + q) Z =
      (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) (TopCat.of (X × Y)) (p + q)).hom
        (congrDegree R _ (Nat.cast_add p q).symm
          (borelMooreHomology.exteriorProduct R X Y p q (μ ⊗ₜ ν))))
    {x : TopCat.of (X × Y)} {φ : Simplex (TopCat.of (X × Y)) (p + q) → R}
    (hφ : φ ∈ relCocycles R ({x}ᶜ : Set (TopCat.of (X × Y))) (p + q)) :
    localPairing (((borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of (X × Y))).iCycles
        (p + q) Z).1 : (TopCat.toSSet.obj (TopCat.of (X × Y))).obj (op ⦋p + q⦌) → R) φ =
      localPairing (crossFun (p + q) p q
        (((borelMooreChainComplex R (ModuleCat.of R R) X).iCycles p z).1 :
          (TopCat.toSSet.obj X).obj (op ⦋p⦌) → R)
        (((borelMooreChainComplex R (ModuleCat.of R R) Y).iCycles q w).1 :
          (TopCat.toSSet.obj Y).obj (op ⦋q⦌) → R)) φ := by
  set zc := ((BM R X).sc p).moduleCatCyclesIso.hom.hom z
  set wc := ((BM R Y).sc q).moduleCatCyclesIso.hom.hom w
  have h1 := homologyEquiv_eq_mk Z hZ
  have h2 : homologyEquiv R (TopCat.of (X × Y)) (p + q) (congrDegree R _ (Nat.cast_add p q).symm
      (borelMooreHomology.exteriorProduct R X Y p q (μ ⊗ₜ ν))) =
      Submodule.Quotient.mk ⟨crossChain R (p + q) p q zc.1 wc.1, crossChain_mem_cyc p q zc wc⟩ := by
    rw [borelMooreHomology.exteriorProduct_tmul,
      ← (homologyEquiv R X p).symm_apply_apply μ, ← (homologyEquiv R Y q).symm_apply_apply ν,
      exteriorProductBilin_natCast, homologyEquiv_eq_mk z hz, homologyEquiv_eq_mk w hw]
    refine ((homologyEquiv R (TopCat.of (X × Y)) (p + q)).apply_symm_apply _).trans ?_
    exact crossHomQ_mk p q zc wc
  rw [h1] at h2
  obtain ⟨c, hc⟩ := (Submodule.Quotient.eq _).1 h2
  have hc' : ((BM R (TopCat.of (X × Y))).iCycles (p + q) Z : (BM R (TopCat.of (X × Y))).X (p + q)) -
      crossChain R (p + q) p q zc.1 wc.1 =
      ((BM R (TopCat.of (X × Y))).d _ (p + q)).hom c := by
    rw [← coe_moduleCatCyclesIso_hom]
    exact (congrArg Subtype.val hc).symm
  have hlin := congrArg (chainPairing hφ.1) hc'
  rw [map_sub, chainPairing_apply, chainPairing_apply, chainPairing_apply,
    localPairing_d_eq_zero_of_eq c hφ, sub_eq_zero] at hlin
  rw [hlin, coe_moduleCatCyclesIso_hom, coe_moduleCatCyclesIso_hom]
  rfl

end Representatives

section PathSimplex

variable {X Y : TopCat.{u}}

/-- The simplex of `σ × τ` along a lattice path `l` sends `t` to the pair of the images under `σ`
and `τ` of the pushforwards of `t` along the coordinates of the vertices of `l`. -/
lemma toC_pathSimplex_apply (m : ℕ) {p q : ℕ} (σ : Simp X p) (τ : Simp Y q)
    (l : List (ℕ × ℕ)) (t : stdSimplex ℝ (Fin (m + 1))) :
    SingularCochain.simplexEquiv _ _ (pathSimplex m σ τ l) t =
      (SingularCochain.simplexEquiv _ _ σ (stdSimplex.map (vtx m p fun j ↦ (l.getD j (0, 0)).1) t),
        SingularCochain.simplexEquiv _ _ τ (stdSimplex.map (vtx m q fun j ↦ (l.getD j (0, 0)).2) t)) := by
  change toC (pathSimplex m σ τ l) (SingularChain.stdSimplexHomeo _ t) =
    (toC σ (SingularChain.stdSimplexHomeo _ (stdSimplex.map (vtx m p fun j ↦ (l.getD j (0, 0)).1) t)),
      toC τ (SingularChain.stdSimplexHomeo _ (stdSimplex.map (vtx m q fun j ↦ (l.getD j (0, 0)).2) t)))
  rw [toC_pathSimplex, SingularChain.stdSimplexHomeo_map, SingularChain.stdSimplexHomeo_map]
  rfl

/-- The `i`-th barycentric coordinate of the pushforward of `t` along `g` is the sum of the
coordinates of `t` over the preimage of `i` under `g`. -/
lemma stdSimplex_map_apply {m p : ℕ} (g : Fin (m + 1) → Fin (p + 1))
    (t : stdSimplex ℝ (Fin (m + 1))) (i : Fin (p + 1)) :
    ((stdSimplex.map g t : stdSimplex ℝ (Fin (p + 1))) : Fin (p + 1) → ℝ) i =
      ∑ j ∈ Finset.univ.filter (fun j ↦ g j = i), (t : Fin (m + 1) → ℝ) j :=
  FunOnFinite.linearMap_apply_apply ℝ ℝ g t i

/-- **Only the corner simplex meets the corner.** Let `σ`, `τ` be singular simplices meeting `x`
and `y` only at barycentric coordinates `s`, `s'` with `s_p + s'_0 > 1`. Then no simplex of
`σ × τ` along a lattice path other than the corner path meets `(x, y)`. -/
theorem notMem_range_pathSimplex {m p q : ℕ} {σ : Simp X p} {τ : Simp Y q} {x : X} {y : Y}
    {l : List (ℕ × ℕ)} (hl : l ∈ (shuffleSum m p q).support) (hlc : l ≠ cornerPath p q)
    {s : Fin (p + 1) → ℝ} {s' : Fin (q + 1) → ℝ}
    (hσ : ∀ a, SingularCochain.simplexEquiv _ _ σ a = x → (a : Fin (p + 1) → ℝ) = s)
    (hτ : ∀ a, SingularCochain.simplexEquiv _ _ τ a = y → (a : Fin (q + 1) → ℝ) = s')
    (hs : 1 < s (Fin.last p) + s' 0) :
    ((x, y) : X × Y) ∉ range (toC (pathSimplex m σ τ l)) := by
  classical
  rintro ⟨t₀, ht⟩
  obtain ⟨t, rfl⟩ := (SingularChain.stdSimplexHomeo (Fin (m + 1))).surjective t₀
  change SingularCochain.simplexEquiv _ m (pathSimplex m σ τ l) t = _ at ht
  rw [toC_pathSimplex_apply, Prod.mk.injEq] at ht
  have h1 := congrFun (hσ _ ht.1) (Fin.last p)
  have h2 := congrFun (hτ _ ht.2) 0
  rw [stdSimplex_map_apply] at h1 h2
  obtain ⟨hlen, hle⟩ := mem_support_shuffleSum hl
  have hdisj : Disjoint
      (Finset.univ.filter fun j ↦ vtx m p (fun j ↦ (l.getD j (0, 0)).1) j = Fin.last p)
      (Finset.univ.filter fun j ↦ vtx m q (fun j ↦ (l.getD j (0, 0)).2) j = 0) := by
    rw [Finset.disjoint_filter]
    intro j _ hj1 hj2
    have hj : (j : ℕ) < l.length := by omega
    have hmem : l.getD j (0, 0) ∈ l := by
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    have hb := hle _ hmem
    have e1 : (l.getD j (0, 0)).1 = p := by
      have := congrArg Fin.val hj1
      simp only [vtx, Fin.val_last] at this
      omega
    have e2 : (l.getD j (0, 0)).2 = 0 := by
      have := congrArg Fin.val hj2
      simp only [vtx, Fin.val_zero] at this
      omega
    apply hlc
    apply eq_cornerPath_of_mem_support hl
    have hpt : ((p, 0) : ℕ × ℕ) = l.getD j (0, 0) := Prod.ext e1.symm e2.symm
    rw [hpt]
    exact hmem
  have hsum := Finset.sum_union hdisj (f := fun j ↦ (t : Fin (m + 1) → ℝ) j)
  have hle1 : ∑ j ∈ (Finset.univ.filter fun j ↦
        vtx m p (fun j ↦ (l.getD j (0, 0)).1) j = Fin.last p) ∪
      (Finset.univ.filter fun j ↦ vtx m q (fun j ↦ (l.getD j (0, 0)).2) j = 0),
        (t : Fin (m + 1) → ℝ) j ≤ ∑ j, (t : Fin (m + 1) → ℝ) j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ ↦ t.2.1 j
  have ht1 : ∑ j, (t : Fin (m + 1) → ℝ) j = 1 := t.2.2
  linarith

/-- The first coordinates of the vertices of the corner path are `j ↦ min j p`. -/
lemma vtx_cornerPath_fst (p q : ℕ) :
    vtx (p + q) p (fun j ↦ ((cornerPath p q).getD j (0, 0)).1) =
      fun j ↦ ⟨min j p, by omega⟩ := by
  funext j
  apply Fin.ext
  simp only [vtx, getD_cornerPath p q j.isLt]
  omega

/-- The second coordinates of the vertices of the corner path are `j ↦ j - p`. -/
lemma vtx_cornerPath_snd (p q : ℕ) :
    vtx (p + q) q (fun j ↦ ((cornerPath p q).getD j (0, 0)).2) =
      fun j ↦ ⟨j - p, by omega⟩ := by
  funext j
  apply Fin.ext
  simp only [vtx, getD_cornerPath p q j.isLt]
  omega

end PathSimplex

section Chart

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V]
  [ContinuousSMul ℝ V] {n : ℕ}

/-- Barycentric coordinates in an oriented simplex are unique. -/
lemma eq_of_affineSimplex_eq {b : Module.Basis (Fin n) ℝ V} {v : Fin (n + 1) → V} {p : V}
    (hv : IsOrientedSimplexAroundZero b fun k ↦ v k - p) {l : Fin (n + 1) → ℝ}
    (hl1 : ∑ k, l k = 1) (hlv : ∑ k, l k • v k = p) (a : stdSimplex ℝ (Fin (n + 1)))
    (ha : affineSimplex v a = p) : (a : Fin (n + 1) → ℝ) = l := by
  have ha1 : ∑ k, (a : Fin (n + 1) → ℝ) k = 1 := a.2.2
  rw [affineSimplex_apply] at ha
  have := hv.eq_zero_of_sum_eq_zero (c := (a : Fin (n + 1) → ℝ) - l)
    (by simp [Finset.sum_sub_distrib, ha1, hl1]) (by
      simp only [Pi.sub_apply, sub_smul, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
        ha1, hl1, ha, hlv, sub_self])
  exact sub_eq_zero.1 this

end Chart

end FundamentalClass

open FundamentalClass

section ModelProd

variable {H H' : Type*}

/-- The additive group structure of `H × H'` on `ModelProd H H'`. -/
instance [AddCommGroup H] [AddCommGroup H'] : AddCommGroup (ModelProd H H') :=
  inferInstanceAs (AddCommGroup (H × H'))

/-- The real vector space structure of `H × H'` on `ModelProd H H'`. -/
instance [AddCommGroup H] [AddCommGroup H'] [Module ℝ H] [Module ℝ H'] :
    Module ℝ (ModelProd H H') :=
  inferInstanceAs (Module ℝ (H × H'))

/-- Addition on `ModelProd H H'` is continuous. -/
instance [AddCommGroup H] [AddCommGroup H'] [TopologicalSpace H] [TopologicalSpace H']
    [ContinuousAdd H] [ContinuousAdd H'] : ContinuousAdd (ModelProd H H') :=
  inferInstanceAs (ContinuousAdd (H × H'))

/-- Scalar multiplication on `ModelProd H H'` is continuous. -/
instance [AddCommGroup H] [AddCommGroup H'] [Module ℝ H] [Module ℝ H'] [TopologicalSpace H]
    [TopologicalSpace H'] [ContinuousSMul ℝ H] [ContinuousSMul ℝ H'] :
    ContinuousSMul ℝ (ModelProd H H') :=
  inferInstanceAs (ContinuousSMul ℝ (H × H'))

end ModelProd

section Manifold

variable (R : Type u) [CommRing R] {H H' : Type*} [AddCommGroup H] [Module ℝ H]
  [TopologicalSpace H] [ContinuousAdd H] [ContinuousSMul ℝ H] [AddCommGroup H'] [Module ℝ H']
  [TopologicalSpace H'] [ContinuousAdd H'] [ContinuousSMul ℝ H'] {M N : Type u}
  [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [TopologicalSpace N] [T2Space N]
  [ChartedSpace H' N]

/-- **The fundamental class of a product** (Fulton, §19.1). For oriented manifolds `M`, `N`
(with the orientations of the bases `b`, `b'` of the model spaces) and the product orientation
on `M × N` (that of the basis `b × b'`), `μ_{M × N} = μ_M × μ_N`. -/
theorem IsFundamentalClass.exteriorProduct {n n' : ℕ} {b : Module.Basis (Fin n) ℝ H}
    {b' : Module.Basis (Fin n') ℝ H'}
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) n}
    {ν : borelMooreHomology R (ModuleCat.of R R) (TopCat.of N) n'}
    (hμ : IsFundamentalClass R b μ) (hν : IsFundamentalClass R b' ν) :
    IsFundamentalClass (H := ModelProd H H') (M := M × N) R
      ((b.prod b').reindex finSumFinEquiv)
      (congrDegree R _ (Nat.cast_add n n').symm
        (borelMooreHomology.exteriorProduct R (TopCat.of M) (TopCat.of N) n n' (μ ⊗ₜ ν))) := by
  classical
  rintro E ⟨e, he, e', he', rfl⟩ ⟨⟨x, y⟩, hxy⟩ V hV hVt
  have hxy' : (x, y) ∈ (e.prod e').source := hxy
  rw [OpenPartialHomeomorph.prod_source] at hxy'
  obtain ⟨hx, hy⟩ := hxy'
  set l : Fin (n + 1) → ℝ := fun k ↦ 1 / (2 * ((n : ℝ) + 1)) + if k = Fin.last n then 1 / 2 else 0
  set l' : Fin (n' + 1) → ℝ := fun k ↦ 1 / (2 * ((n' : ℝ) + 1)) + if k = 0 then 1 / 2 else 0
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
  have hll : 1 < l (Fin.last n) + l' 0 := by
    simp only [l, l', ite_true]
    have : 0 < 1 / (2 * ((n : ℝ) + 1)) := by positivity
    have : 0 < 1 / (2 * ((n' : ℝ) + 1)) := by positivity
    linarith
  obtain ⟨v, hv, hlv, hvt⟩ := exists_isOrientedSimplexAroundZero_barycentric b (e x)
    (e.open_target.mem_nhds (e.map_source hx)) hl0 hl1
  obtain ⟨w, hw, hlw, hwt⟩ := exists_isOrientedSimplexAroundZero_barycentric b' (e' y)
    (e'.open_target.mem_nhds (e'.map_source hy)) hl0' hl1'
  have h1 := IsLocallyClassOf.of_restrict (chartOpens e) (hμ e he ⟨x, hx⟩ v hv hvt)
  have h2 := IsLocallyClassOf.of_restrict (chartOpens e') (hν e' he' ⟨y, hy⟩ w hw hwt)
  set ΔM := inclChainSimplex (chartOpens e) (chartSimplex e v hvt)
  set ΔN := inclChainSimplex (chartOpens e') (chartSimplex e' w hwt)
  have hΔ : ∀ t : stdSimplex ℝ (Fin (n + 1)), (∃ i, (t : Fin (n + 1) → ℝ) i = 0) → ΔM t ≠ x :=
    fun t ht h ↦ chartSimplex_ne (x := ⟨x, hx⟩) hv hvt t ht (Subtype.ext h)
  refine IsLocallyClassOf.restrict (chartOpens (e.prod e')) ?_
  intro Z hZ φ hφ
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective
    ((borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of M)).homologyπ n)).1 inferInstance
    ((borelMooreHomologyIsoOfNat R (ModuleCat.of R R) (TopCat.of M) n).hom μ)
  obtain ⟨z', hz'⟩ := (ModuleCat.epi_iff_surjective
    ((borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of N)).homologyπ n')).1 inferInstance
    ((borelMooreHomologyIsoOfNat R (ModuleCat.of R R) (TopCat.of N) n').hom ν)
  rw [localPairing_eq_of_exteriorProduct z hz z' hz' Z hZ hφ,
    localPairing_crossFun_eq_evalSimp h1 h2 hΔ z hz z' hz' hφ]
  have hσ : ∀ a, SingularCochain.simplexEquiv _ _ (toSimp ΔM) a = x → (a : Fin (n + 1) → ℝ) = l := fun a ha ↦ by
    have ha'' : ((chartSimplex e v hvt a : chartOpens e) : M) = x := by
      simpa [toSimp, ΔM] using ha
    have ha' : e.symm (affineSimplex v a) = x := ha''
    refine eq_of_affineSimplex_eq hv hl1 hlv a ?_
    rw [← e.right_inv (hvt ⟨a, rfl⟩), ha']
  have hτ : ∀ a, SingularCochain.simplexEquiv _ _ (toSimp ΔN) a = y → (a : Fin (n' + 1) → ℝ) = l' := fun a ha ↦ by
    have ha'' : ((chartSimplex e' w hwt a : chartOpens e') : N) = y := by
      simpa [toSimp, ΔN] using ha
    have ha' : e'.symm (affineSimplex w a) = y := ha''
    refine eq_of_affineSimplex_eq hw hl1' hlw a ?_
    rw [← e'.right_inv (hwt ⟨a, rfl⟩), ha']
  rw [evalSimp, crossSimplex, Finsupp.linearCombination_mapDomain,
    Finsupp.linearCombination_apply, Finsupp.sum,
    Finset.sum_eq_single (cornerPath n n') ?_ ?_, shuffleSum_cornerPath, one_smul]
  · have hcor := isOrientedSimplexAroundZero_cornerVertices (b := b) (b' := b') hv hw hl0 hl1 hlv
      hl0' hl1' hlw hll
    have hfst : ∀ t : stdSimplex ℝ (Fin (n + n' + 1)),
        (affineSimplex (cornerVertices v w) t).1 = affineSimplex v
          (stdSimplex.map (fun j : Fin (n + n' + 1) ↦ (⟨min j n, by omega⟩ : Fin (n + 1))) t) :=
      fun t ↦ by
        rw [affineSimplex_apply, affineSimplex_apply, sum_stdSimplex_map_smul, Prod.fst_sum]
        rfl
    have hsnd : ∀ t : stdSimplex ℝ (Fin (n + n' + 1)),
        (affineSimplex (cornerVertices v w) t).2 = affineSimplex w
          (stdSimplex.map (fun j : Fin (n + n' + 1) ↦ (⟨j - n, by omega⟩ : Fin (n' + 1))) t) :=
      fun t ↦ by
        rw [affineSimplex_apply, affineSimplex_apply, sum_stdSimplex_map_smul, Prod.snd_sum]
        rfl
    have hrange : range (affineSimplex (cornerVertices v w)) ⊆ (e.prod e').target := by
      rintro _ ⟨t, rfl⟩
      rw [OpenPartialHomeomorph.prod_target]
      exact ⟨by rw [hfst]; exact hvt ⟨_, rfl⟩, by rw [hsnd]; exact hwt ⟨_, rfl⟩⟩
    refine (isLocallyHomologous_of_isOrientedSimplexAroundZero (e.prod e') hxy (b := _)
      (v := cornerVertices v w) hcor hrange hV hVt (fun t ↦ ?_) (fun t ↦ rfl)).apply_eq hφ
    rw [toC_pathSimplex_apply, vtx_cornerPath_fst, vtx_cornerPath_snd,
      OpenPartialHomeomorph.prod_symm, OpenPartialHomeomorph.prod_apply]
    refine Prod.ext ?_ ?_
    · change e.symm (affineSimplex v _) = e.symm _
      rw [hfst]
      rfl
    · change e'.symm (affineSimplex w _) = e'.symm _
      rw [hsnd]
      rfl
  · intro L hL hLc
    simp only [Function.comp_apply]
    rw [hφ.1 _ ?_, smul_zero]
    intro pt hpt hpt'
    rw [Set.mem_singleton_iff.1 hpt'] at hpt
    exact notMem_range_pathSimplex hL hLc hσ hτ hll ((range_simplexEquiv _).subset hpt)
  · intro h
    exact absurd (Finsupp.mem_support_iff.2 (by rw [shuffleSum_cornerPath]; exact one_ne_zero)) h

end Manifold

end MMP
