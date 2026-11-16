module

public import MMP.AlgebraicTopology.FundamentalClass.Basic
public import MMP.AlgebraicTopology.BorelMoore.RestrictionFunctorial
public import MMP.AlgebraicTopology.BorelMoore.DisjointUnion
/-!
# Restriction of the fundamental class to an open subset (Fulton, §19.1)

Let `M` be an oriented real `n`-manifold and `U ⊆ M` open, with the induced orientation (the
charts of `U` are the restrictions of the charts of `M`). Then `μ_M|_U = μ_U`.

The fundamental class is characterised locally: at every point `x` of a coordinate ball `B`,
`μ_M|_B` has the same image in `H_n(B, B - x)` as the oriented simplices around `x`, which is
tested by pairing a representing locally finite cycle with the relative cocycles of `(B, B - x)`.
A locally finite chain meets `x` in finitely many simplices, so the pairing is a finite sum; it
vanishes on boundaries, so it is defined on homology classes.

Restriction of chains to an open `U` is given by an integer kernel `k(σ, τ)`. A relative cocycle
`φ'` of `(U, U - x)` pulls back to the cochain `σ ↦ ∑_τ k(σ, τ) φ'(τ)` of `Y`, a relative cocycle
of `(Y, Y - x)` (restriction is a chain map and does not enlarge supports), and
`⟨φ', z|_U⟩ = ⟨φ, z⟩`. A simplex lying in `U` restricts to itself, so the local class of a
simplex of `U` at a point of `U` is preserved by restriction. Push-forward along a proper map
injective over the point is handled the same way, with `φ = φ' ∘ f_*`. The theorem follows by
functoriality of restriction, which identifies the restriction of `μ_M|_U` to the coordinate ball
`B ∩ U` of a restricted chart with the restriction of `μ_M|_B`, up to the homeomorphisms between
the various models of `B ∩ U`.

## Main results

* `MMP.FundamentalClass.IsLocallyClassOf.of_chainMap`: transfer of local classes
  along a map of complexes of locally finite chains that pulls relative cocycles back.
* `MMP.FundamentalClass.IsLocallyClassOf.restrict`: restriction of local classes
  to an open subset.
* `MMP.FundamentalClass.IsLocallyClassOf.pushforward`: push-forward of local
  classes along a proper map injective over the point.
* `MMP.FundamentalClass.IsChartOrientationClass.subtypeRestr`: restriction of the
  orientation generator of a coordinate ball to a restricted chart.
* `MMP.IsFundamentalClass.restrict`: `μ_M|_U = μ_U`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [B. Iversen, *Cohomology of Sheaves*][iversen1986], IX.4.
-/

@[expose] public noncomputable section

open CategoryTheory Set Topology Opposite Simplicial
open MMP.SingularChain MMP.SingularCochain
  MMP.LocallyFiniteChain MMP.borelMooreHomology
  MMP.ThomClass

universe u

namespace MMP

namespace FundamentalClass

section Pairing

variable {R : Type u} [CommRing R] {X : TopCat.{u}}

/-- A simplex on which a cochain vanishing off `x` is nonzero contains `x`. -/
lemma mem_singularSimplexImage_of_ne_zero {n : ℕ} {x : X} {φ : Simplex X n → R}
    (hφ : φ ∈ vanishing R n ({x}ᶜ : Set X)) {τ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)}
    (h : φ (SingularCochain.simplexEquiv X _ τ) ≠ 0) : x ∈ singularSimplexImage X τ := by
  by_contra hx
  exact h (hφ _ fun y hy ↦ by
    rintro rfl
    exact hx ((range_simplexEquiv _).subset hy))

/-- A locally finite chain meets a point in only finitely many simplices, so its pairing with a
cochain vanishing off that point is a finite sum. -/
lemma finite_support_mul {n : ℕ} {c : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R}
    (hc : IsLocallyFiniteSet (singularSimplexImage X) (Function.support c)) {x : X}
    {φ : Simplex X n → R} (hφ : φ ∈ vanishing R n ({x}ᶜ : Set X)) :
    (Function.support fun σ ↦ c σ * φ (SingularCochain.simplexEquiv X _ σ)).Finite := by
  refine (hc.finite_inter_compact (isCompact_singleton (x := x))).subset fun σ hσ ↦ ?_
  exact ⟨fun h ↦ hσ (by simp [h]), x,
    mem_singularSimplexImage_of_ne_zero hφ fun h ↦ hσ (by simp [h]), rfl⟩

/-- The pairing with a cochain vanishing off a point is additive in the locally finite chain. -/
lemma localPairing_add {n : ℕ} {c d : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R}
    (hc : IsLocallyFiniteSet (singularSimplexImage X) (Function.support c))
    (hd : IsLocallyFiniteSet (singularSimplexImage X) (Function.support d)) {x : X}
    {φ : Simplex X n → R} (hφ : φ ∈ vanishing R n ({x}ᶜ : Set X)) :
    localPairing (c + d) φ = localPairing c φ + localPairing d φ := by
  rw [localPairing, localPairing, localPairing, ← finsum_add_distrib (finite_support_mul hc hφ)
    (finite_support_mul hd hφ)]
  exact finsum_congr fun σ ↦ by simp [add_mul]

/-- The pairing of a boundary of a locally finite chain with a relative cocycle of
`(X, X - x)` vanishes. -/
lemma localPairing_d_eq_zero {n : ℕ}
    (w : (borelMooreChainComplex R (ModuleCat.of R R) X).X (n + 1)) {x : X}
    {φ : Simplex X n → R} (hφ : φ ∈ relCocycles R ({x}ᶜ : Set X) n) :
    localPairing ((((borelMooreChainComplex R (ModuleCat.of R R) X).d (n + 1) n).hom w).1
      : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R) φ = 0 := by
  classical
  obtain ⟨hφv, hφc⟩ := hφ
  have hφc : coboundary R n φ = 0 := hφc
  rw [borelMooreChainComplex_d_apply R (ModuleCat.of R R) X n w]
  set c : (TopCat.toSSet.obj X).obj (op ⦋n + 1⦌) → R := w.1
  have hc : IsLocallyFiniteSet (singularSimplexImage X) (Function.support c) := w.2
  let F := (hc.finite_inter_compact (isCompact_singleton (x := x))).toFinset
  have hF : ∀ ω, c ω ≠ 0 → x ∈ singularSimplexImage X ω → ω ∈ F := fun ω h1 h2 ↦
    (Finite.mem_toFinset _).2 ⟨h1, x, h2, rfl⟩
  let T := F.biUnion fun ω ↦ Finset.univ.image fun i : Fin (n + 2) ↦
    (TopCat.toSSet.obj X).δ i ω
  have hterm : ∀ τ, dFun (fun i : Fin (n + 2) ↦ (TopCat.toSSet.obj X).δ i) c τ *
      φ (SingularCochain.simplexEquiv X _ τ) = ∑ i : Fin (n + 2), ∑ ω ∈ F,
        (-1 : R) ^ (i : ℕ) * ((if (TopCat.toSSet.obj X).δ i ω = τ then c ω else 0) *
          φ (SingularCochain.simplexEquiv X _ τ)) := by
    intro τ
    by_cases h : φ (SingularCochain.simplexEquiv X _ τ) = 0
    · simp [h]
    rw [dFun, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [pushforwardFun_apply_eq_sum _ c τ F (fun ω h1 (h2 : (TopCat.toSSet.obj X).δ i ω = τ) ↦
      hF ω h1 (singularSimplexImage_map_subset _ ω
        (h2.symm ▸ mem_singularSimplexImage_of_ne_zero hφv h))),
      Finset.smul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    rw [zsmul_eq_mul]
    push_cast
    ring
  rw [localPairing, finsum_eq_sum_of_support_subset (s := T) _ (fun τ hτ ↦ by
    rw [Function.mem_support, hterm] at hτ
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hτ
    obtain ⟨ω, hω, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
    have hδ : (TopCat.toSSet.obj X).δ i ω = τ := by
      by_contra h
      simp [h] at hi
    rw [Finset.coe_biUnion]
    exact mem_iUnion₂.2 ⟨ω, hω, by simp [← hδ]⟩)]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  have hinner : ∀ i : Fin (n + 2), ∑ τ ∈ T, ∑ ω ∈ F, (-1 : R) ^ (i : ℕ) *
      ((if (TopCat.toSSet.obj X).δ i ω = τ then c ω else 0) * φ (SingularCochain.simplexEquiv X _ τ)) =
      ∑ ω ∈ F, c ω * ((-1 : R) ^ (i : ℕ) *
        φ ((SingularCochain.simplexEquiv X _ ω : Simplex X (n + 1)).comp (face n i))) := by
    intro i
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω hω ↦ ?_
    have hmem : (TopCat.toSSet.obj X).δ i ω ∈ T :=
      Finset.mem_biUnion.2 ⟨ω, hω, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
    simp_rw [ite_mul, zero_mul, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq, ite_eq_left hmem, ← toSSetObjEquiv_δ]
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ hinner i, Finset.sum_comm]
  refine Finset.sum_eq_zero fun ω _ ↦ ?_
  rw [← Finset.mul_sum, ← coboundary_apply, hφc]
  simp

/-- The pairing of the image of a locally finite chain under any differential of the complex
with a relative cocycle of `(X, X - x)` vanishes. -/
lemma localPairing_d_eq_zero_of_eq {n j : ℕ}
    (w : (borelMooreChainComplex R (ModuleCat.of R R) X).X j) {x : X}
    {φ : Simplex X n → R} (hφ : φ ∈ relCocycles R ({x}ᶜ : Set X) n) :
    localPairing ((((borelMooreChainComplex R (ModuleCat.of R R) X).d j n).hom w).1
      : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R) φ = 0 := by
  by_cases hj : j = n + 1
  · subst hj
    exact localPairing_d_eq_zero w hφ
  · rw [(borelMooreChainComplex R (ModuleCat.of R R) X).shape j n (by
      simp only [ComplexShape.down_Rel]
      omega)]
    exact finsum_eq_zero_of_forall_eq_zero fun _ ↦ zero_mul _

end Pairing

section Transfer

variable {R : Type u} [CommRing R] {X X' : TopCat.{u}}

/-- The pairing of a locally finite chain with a cochain vanishing off the point `x`, as a linear
map. -/
def chainPairing {n : ℕ} {x : X} {φ : Simplex X n → R}
    (hφ : φ ∈ vanishing R n ({x}ᶜ : Set X)) :
    (borelMooreChainComplex R (ModuleCat.of R R) X).X n →ₗ[R] R where
  toFun c := localPairing (c.1 : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R) φ
  map_add' c d := localPairing_add c.2 d.2 hφ
  map_smul' r c := by
    rw [RingHom.id_apply, smul_eq_mul]
    change ∑ᶠ σ, (r • (c.1 : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R)) σ * _ =
      r * localPairing _ φ
    have hfin := finite_support_mul c.2 hφ
    rw [localPairing, finsum_eq_sum_of_support_subset _ hfin.coe_toFinset.ge,
      finsum_eq_sum_of_support_subset (s := hfin.toFinset) _ (fun σ hσ ↦ by
        rw [hfin.coe_toFinset]
        intro h0
        apply hσ
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
        exact (congrArg (r * ·) h0).trans (mul_zero r)), Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ ↦ by simp [mul_assoc]

/-- `chainPairing hφ c` is the pairing of the chain `c` with `φ`. -/
lemma chainPairing_apply {n : ℕ} {x : X} {φ : Simplex X n → R}
    (hφ : φ ∈ vanishing R n ({x}ᶜ : Set X))
    (c : (borelMooreChainComplex R (ModuleCat.of R R) X).X n) :
    chainPairing hφ c = localPairing (c.1 : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R) φ :=
  rfl

/-- The pairing of a cycle with a relative cocycle of `(X, X - x)` depends only on its homology
class. -/
lemma localPairing_eq_of_homologyπ_eq {n : ℕ}
    {z z' : (borelMooreChainComplex R (ModuleCat.of R R) X).cycles n}
    (h : (borelMooreChainComplex R (ModuleCat.of R R) X).homologyπ n z =
      (borelMooreChainComplex R (ModuleCat.of R R) X).homologyπ n z') {x : X}
    {φ : Simplex X n → R} (hφ : φ ∈ relCocycles R ({x}ᶜ : Set X) n) :
    localPairing (((borelMooreChainComplex R (ModuleCat.of R R) X).iCycles n z).1 :
      (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R) φ =
    localPairing (((borelMooreChainComplex R (ModuleCat.of R R) X).iCycles n z').1 :
      (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R) φ := by
  let P : (borelMooreChainComplex R (ModuleCat.of R R) X).cycles n ⟶ ModuleCat.of R R :=
    ModuleCat.ofHom ((chainPairing hφ.1).comp
      ((borelMooreChainComplex R (ModuleCat.of R R) X).iCycles n).hom)
  have hP : (borelMooreChainComplex R (ModuleCat.of R R) X).toCycles (n + 1) n ≫ P = 0 := by
    refine ModuleCat.hom_ext (LinearMap.ext fun w ↦ ?_)
    have e : (borelMooreChainComplex R (ModuleCat.of R R) X).iCycles n
        ((borelMooreChainComplex R (ModuleCat.of R R) X).toCycles (n + 1) n w) =
        (borelMooreChainComplex R (ModuleCat.of R R) X).d (n + 1) n w :=
      ConcreteCategory.congr_hom
        ((borelMooreChainComplex R (ModuleCat.of R R) X).toCycles_i (n + 1) n) w
    change localPairing (((borelMooreChainComplex R (ModuleCat.of R R) X).iCycles n
      ((borelMooreChainComplex R (ModuleCat.of R R) X).toCycles (n + 1) n w)).1 :
        (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R) φ = 0
    rw [e]
    exact localPairing_d_eq_zero w hφ
  obtain ⟨l, hl⟩ := Limits.CokernelCofork.IsColimit.desc'
    ((borelMooreChainComplex R (ModuleCat.of R R) X).homologyIsCokernel (n + 1) n (by simp)) P hP
  have e : ∀ a, (chainPairing hφ.1).comp
      ((borelMooreChainComplex R (ModuleCat.of R R) X).iCycles n).hom a =
      l ((borelMooreChainComplex R (ModuleCat.of R R) X).homologyπ n a) := fun a ↦
    (ConcreteCategory.congr_hom hl a).symm
  change (chainPairing hφ.1).comp
      ((borelMooreChainComplex R (ModuleCat.of R R) X).iCycles n).hom z =
    (chainPairing hφ.1).comp ((borelMooreChainComplex R (ModuleCat.of R R) X).iCycles n).hom z'
  rw [e, e, h]

/-- **Transfer of local classes along a map of chain complexes.** Let `Φ` be a map of complexes
of locally finite chains from `X` to `X'`. If every relative cocycle `φ'` of `(X', X' - x')`
pulls back along `Φ` (for the pairings with chains) to a relative cocycle `φ` of `(X, X - x)` with
`φ(Δ) = φ'(Δ')`, then `Φ` carries a class that is locally the class of `Δ` at `x` to one that is
locally the class of `Δ'` at `x'`. -/
theorem IsLocallyClassOf.of_chainMap {n : ℕ}
    (Φ : borelMooreChainComplex R (ModuleCat.of R R) X ⟶
      borelMooreChainComplex R (ModuleCat.of R R) X')
    {ν : borelMooreHomology R (ModuleCat.of R R) X n} {x : X} {Δ : Simplex X n}
    (h : IsLocallyClassOf R ν x Δ) {x' : X'} {Δ' : Simplex X' n}
    (hΦ : ∀ φ' ∈ relCocycles R ({x'}ᶜ : Set X') n, ∃ φ ∈ relCocycles R ({x}ᶜ : Set X) n,
      φ Δ = φ' Δ' ∧ ∀ c : (borelMooreChainComplex R (ModuleCat.of R R) X).X n,
        localPairing (((Φ.f n).hom c).1 : (TopCat.toSSet.obj X').obj (op ⦋n⦌) → R) φ' =
          localPairing (c.1 : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R) φ) :
    IsLocallyClassOf R ((HomologicalComplex.homologyMap
      (HomologicalComplex.extendMap Φ ComplexShape.embeddingDownNat) (-(n : ℤ))).hom ν) x' Δ' := by
  intro z' hz' φ' hφ'
  obtain ⟨φ, hφ, hΔ, hpair⟩ := hΦ φ' hφ'
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective
    ((borelMooreChainComplex R (ModuleCat.of R R) X).homologyπ n)).1 inferInstance
    ((borelMooreHomologyIsoOfNat R (ModuleCat.of R R) X n).hom ν)
  have e2 : (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) X' n).hom
      ((HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap Φ ComplexShape.embeddingDownNat) (-(n : ℤ))).hom ν) =
      HomologicalComplex.homologyMap Φ n
        ((borelMooreHomologyIsoOfNat R (ModuleCat.of R R) X n).hom ν) :=
    ConcreteCategory.congr_hom
      (HomologicalComplex.extendHomologyIso_hom_naturality Φ ComplexShape.embeddingDownNat _) ν
  have e1 : (borelMooreChainComplex R (ModuleCat.of R R) X').homologyπ n
      (HomologicalComplex.cyclesMap Φ n z) =
      HomologicalComplex.homologyMap Φ n
        ((borelMooreChainComplex R (ModuleCat.of R R) X).homologyπ n z) :=
    (ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality Φ n) z).symm
  have heq : (borelMooreChainComplex R (ModuleCat.of R R) X').homologyπ n z' =
      (borelMooreChainComplex R (ModuleCat.of R R) X').homologyπ n
        (HomologicalComplex.cyclesMap Φ n z) := by
    rw [e1, hz, ← e2]
    exact hz'
  have hi : (borelMooreChainComplex R (ModuleCat.of R R) X').iCycles n
      (HomologicalComplex.cyclesMap Φ n z) =
      Φ.f n ((borelMooreChainComplex R (ModuleCat.of R R) X).iCycles n z) :=
    ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i Φ n) z
  rw [localPairing_eq_of_homologyπ_eq heq hφ', hi]
  change localPairing (((Φ.f n).hom _).1 : (TopCat.toSSet.obj X').obj (op ⦋n⦌) → R) φ' = _
  rw [hpair, h z hz φ hφ, hΔ]

end Transfer

section Pullback

variable {R : Type u} [CommRing R] {X X' : TopCat.{u}}

/-- A finite set of singular simplices is locally finite. -/
lemma isLocallyFiniteSet_of_finite {n : ℕ} {s : Set ((TopCat.toSSet.obj X).obj (op ⦋n⦌))}
    (hs : s.Finite) : IsLocallyFiniteSet (singularSimplexImage X) s := fun _ ↦
  ⟨univ, Filter.univ_mem, hs.subset fun _ hσ ↦ hσ.1⟩

/-- The underlying function of a finite sum of locally finite chains is the sum of the
underlying functions. -/
lemma val_sum_chain {n m : ℕ} (f : Fin m → (borelMooreChainComplex R (ModuleCat.of R R) X).X n) :
    ((∑ i, f i).1 : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R) = ∑ i, ((f i).1 : _ → R) :=
  Submodule.coe_sum _ _ _

/-- The underlying function of a scalar multiple of a locally finite chain is the scalar multiple
of the underlying function. -/
lemma val_smul_chain {n : ℕ} (r : R) (c : (borelMooreChainComplex R (ModuleCat.of R R) X).X n) :
    ((r • c).1 : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R) = r • (c.1 : _ → R) :=
  rfl

open Classical in
variable (R) in
/-- A single singular simplex, as a locally finite chain. -/
def singleChain {n : ℕ} (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) :
    (borelMooreChainComplex R (ModuleCat.of R R) X).X n :=
  (⟨Pi.single σ 1, isLocallyFiniteSet_of_finite
    ((Set.finite_singleton σ).subset Pi.support_single_subset)⟩ :
      lfChains R (ModuleCat.of R R) (singularSimplexImage X))

open Classical in
/-- The underlying function of `singleChain R σ` is the indicator `Pi.single σ 1`. -/
lemma coe_singleChain {n : ℕ} (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) :
    ((singleChain R σ).1 : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R) = Pi.single σ 1 :=
  rfl

/-- The boundary of a single simplex is the alternating sum of its faces. -/
lemma d_singleChain {n : ℕ} (ω : (TopCat.toSSet.obj X).obj (op ⦋n + 1⦌)) :
    ((borelMooreChainComplex R (ModuleCat.of R R) X).d (n + 1) n).hom (singleChain R ω) =
      ∑ i : Fin (n + 2), ((-1 : R) ^ (i : ℕ)) • singleChain R ((TopCat.toSSet.obj X).δ i ω) := by
  classical
  apply Subtype.ext
  rw [borelMooreChainComplex_d_apply]
  funext τ
  rw [val_sum_chain, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [pushforwardFun, finsum_eq_single _ ω (fun σ hσ ↦ by
    rw [coe_singleChain, Pi.single_eq_of_ne hσ]
    simp)]
  rw [val_smul_chain, Pi.smul_apply, coe_singleChain, coe_singleChain, Pi.single_eq_same,
    Pi.single_apply, zsmul_eq_mul, smul_eq_mul]
  by_cases h : (TopCat.toSSet.obj X).δ i ω = τ
  · simp [h]
  · simp [h, Ne.symm h]

/-- The cochain `σ ↦ ⟨φ', Φ σ⟩` of `X` obtained by pulling back along a map `Φ` of complexes of
locally finite chains a cochain `φ'` of `X'` vanishing off the point `x'`. -/
def pullbackCochain (Φ : borelMooreChainComplex R (ModuleCat.of R R) X ⟶
      borelMooreChainComplex R (ModuleCat.of R R) X') {n : ℕ} {x' : X'}
    {φ' : Simplex X' n → R} (hφ' : φ' ∈ vanishing R n ({x'}ᶜ : Set X')) : Simplex X n → R :=
  fun σ ↦ chainPairing hφ' ((Φ.f n).hom (singleChain R ((SingularCochain.simplexEquiv X n).symm σ)))

/-- The pull-back of a cocycle is a cocycle. -/
lemma coboundary_pullbackCochain (Φ : borelMooreChainComplex R (ModuleCat.of R R) X ⟶
      borelMooreChainComplex R (ModuleCat.of R R) X') {n : ℕ} {x' : X'}
    {φ' : Simplex X' n → R} (hφ' : φ' ∈ relCocycles R ({x'}ᶜ : Set X') n) :
    coboundary R n (pullbackCochain Φ hφ'.1) = 0 := by
  funext ω
  rw [coboundary_apply, Pi.zero_apply]
  set ω' := (SingularCochain.simplexEquiv X (n + 1)).symm ω
  have hω : SingularCochain.simplexEquiv X (n + 1) ω' = ω := by simp [ω']
  have key := localPairing_d_eq_zero ((Φ.f (n + 1)).hom (singleChain R ω')) hφ'
  rw [← chainPairing_apply hφ'.1] at key
  have hd : ((borelMooreChainComplex R (ModuleCat.of R R) X').d (n + 1) n).hom
      ((Φ.f (n + 1)).hom (singleChain R ω')) = ∑ i : Fin (n + 2), ((-1 : R) ^ (i : ℕ)) •
        (Φ.f n).hom (singleChain R ((TopCat.toSSet.obj X).δ i ω')) := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Φ.comm, ModuleCat.hom_comp,
      LinearMap.comp_apply, d_singleChain, map_sum]
    simp only [map_smul]
  rw [hd, map_sum] at key
  rw [← key]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, smul_eq_mul]
  congr 1
  simp only [pullbackCochain]
  rw [← SingularCochain.simplexEquiv_symm_δ]

end Pullback

section Restriction

variable {R : Type u} [CommRing R] {Y : TopCat.{u}} [T2Space Y] (U : TopologicalSpace.Opens Y)

/-- A singular simplex of the open subset `U`, as a singular simplex of `Y`. -/
abbrev inclChainSimplex {n : ℕ} (Δ : Simplex (TopCat.of U) n) : Simplex Y n :=
  (⟨Subtype.val, continuous_subtype_val⟩ : C(U, Y)).comp Δ

/-- The coefficient of `τ` in the restriction to `U` of the single simplex `σ` is the restriction
kernel `restrictKernel U n σ τ`. -/
lemma restrictChainMap_singleChain_apply {n : ℕ} (σ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌))
    (τ : (TopCat.toSSet.obj (TopCat.of U)).obj (op ⦋n⦌)) :
    ((((restrictChainMap R (ModuleCat.of R R) U).f n).hom (singleChain R σ)).1 :
      (TopCat.toSSet.obj (TopCat.of U)).obj (op ⦋n⦌) → R) τ =
      (restrictKernel U n σ τ : R) := by
  classical
  change kernelFun (restrictKernel U n) (Pi.single σ (1 : R)) τ = _
  rw [kernelFun, finsum_eq_single _ σ (fun σ' hσ' ↦ by
    rw [Pi.single_eq_of_ne hσ', smul_zero]), Pi.single_eq_same, zsmul_eq_mul, mul_one]

/-- The pull-back along restriction to `U` of a cochain `φ'` of `U` is
`σ ↦ ∑ᶠ τ, restrictKernel U n σ τ * φ' τ`. -/
lemma pullbackCochain_restrictChainMap_apply {n : ℕ} {x : U}
    {φ' : Simplex (TopCat.of U) n → R} (hφ' : φ' ∈ vanishing R n ({x}ᶜ : Set U))
    (σ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌)) :
    pullbackCochain (restrictChainMap R (ModuleCat.of R R) U) hφ' (SingularCochain.simplexEquiv Y _ σ) =
      ∑ᶠ τ, (restrictKernel U n σ τ : R) * φ' (SingularCochain.simplexEquiv (TopCat.of U) _ τ) := by
  rw [pullbackCochain, Equiv.symm_apply_apply, chainPairing_apply, localPairing]
  exact finsum_congr fun τ ↦ by rw [restrictChainMap_singleChain_apply]

/-- The pull-back along restriction to `U` of a cochain of `U` vanishing off `x` vanishes off `x`
in `Y`. -/
lemma pullbackCochain_restrictChainMap_mem_vanishing {n : ℕ} {x : U}
    {φ' : Simplex (TopCat.of U) n → R} (hφ' : φ' ∈ vanishing R n ({x}ᶜ : Set U)) :
    pullbackCochain (restrictChainMap R (ModuleCat.of R R) U) hφ' ∈
      vanishing R n ({x.1}ᶜ : Set Y) := by
  intro σ hσ
  obtain ⟨σ', rfl⟩ := (SingularCochain.simplexEquiv Y n).surjective σ
  rw [pullbackCochain_restrictChainMap_apply]
  refine finsum_eq_zero_of_forall_eq_zero fun τ ↦ ?_
  by_cases hk : restrictKernel U n σ' τ = 0
  · simp [hk]
  · have hsub := (range_subset_of_restrCoeff_ne_zero hk).trans inter_subset_left
    rw [hφ' _ (fun y hy ↦ ?_), mul_zero]
    rintro rfl
    exact hσ (hsub (by rw [range_inclSimplex]; exact ⟨_, (range_simplexEquiv _).subset hy, rfl⟩)) rfl

/-- On a simplex of `U`, viewed in `Y`, the pull-back along restriction to `U` of a cochain `φ'`
takes the value of `φ'` on that simplex. -/
lemma pullbackCochain_restrictChainMap_inclChainSimplex {n : ℕ} {x : U}
    {φ' : Simplex (TopCat.of U) n → R} (hφ' : φ' ∈ vanishing R n ({x}ᶜ : Set U))
    (Δ : Simplex (TopCat.of U) n) :
    pullbackCochain (restrictChainMap R (ModuleCat.of R R) U) hφ' (inclChainSimplex U Δ) =
      φ' Δ := by
  classical
  obtain ⟨Δ', rfl⟩ := (SingularCochain.simplexEquiv (TopCat.of U) n).surjective Δ
  have hincl : inclChainSimplex U (SingularCochain.simplexEquiv (TopCat.of U) _ Δ') = inclSimplex U Δ' := rfl
  obtain ⟨σ, hσ⟩ := (SingularCochain.simplexEquiv Y n).surjective (inclSimplex U Δ')
  rw [hincl, ← hσ, pullbackCochain_restrictChainMap_apply, finsum_eq_single _ Δ' (fun τ hτ ↦ by
    rw [restrictKernel, hσ, restrCoeff_of_range_subset (range_inclSimplex_subset U Δ'),
      Finsupp.single_apply, ite_eq_right (fun h ↦ hτ (inclSimplex_injective U n h).symm)]
    simp)]
  rw [restrictKernel, hσ, restrCoeff_of_range_subset (range_inclSimplex_subset U Δ'),
    Finsupp.single_eq_same]
  simp

/-- Pairing with a restricted chain is pairing with the pulled-back cochain. -/
lemma localPairing_restrictChainMap {n : ℕ} {x : U}
    {φ' : Simplex (TopCat.of U) n → R} (hφ' : φ' ∈ vanishing R n ({x}ᶜ : Set U))
    (c : (borelMooreChainComplex R (ModuleCat.of R R) Y).X n) :
    localPairing ((((restrictChainMap R (ModuleCat.of R R) U).f n).hom c).1 :
      (TopCat.toSSet.obj (TopCat.of U)).obj (op ⦋n⦌) → R) φ' =
    localPairing (c.1 : (TopCat.toSSet.obj Y).obj (op ⦋n⦌) → R)
      (pullbackCochain (restrictChainMap R (ModuleCat.of R R) U) hφ') := by
  classical
  have hk := isAdmissibleKernel_restrictKernel U n
  set f : (TopCat.toSSet.obj Y).obj (op ⦋n⦌) → R := c.1
  have hf : IsLocallyFiniteSet (singularSimplexImage Y) (Function.support f) := c.2
  change ∑ᶠ τ, kernelFun (restrictKernel U n) f τ * φ' (SingularCochain.simplexEquiv (TopCat.of U) _ τ) =
    ∑ᶠ σ, f σ * pullbackCochain (restrictChainMap R (ModuleCat.of R R) U) hφ'
      (SingularCochain.simplexEquiv Y _ σ)
  simp_rw [pullbackCochain_restrictChainMap_apply]
  let A := (hf.finite_inter_compact (isCompact_singleton (x := x.1))).toFinset
  let B := A.biUnion fun σ ↦
    ((hk.isLocallyFiniteSet σ).finite_inter_compact (isCompact_singleton (x := x))).toFinset
  have hA : ∀ σ τ, f σ ≠ 0 → restrictKernel U n σ τ ≠ 0 →
      φ' (SingularCochain.simplexEquiv (TopCat.of U) _ τ) ≠ 0 → σ ∈ A := fun σ τ h1 h2 h3 ↦
    (Finite.mem_toFinset _).2 ⟨h1, x.1,
      hk.image_subset σ τ h2 ⟨x, mem_singularSimplexImage_of_ne_zero hφ' h3, rfl⟩, rfl⟩
  have hB : ∀ σ τ, f σ ≠ 0 → restrictKernel U n σ τ ≠ 0 →
      φ' (SingularCochain.simplexEquiv (TopCat.of U) _ τ) ≠ 0 → τ ∈ B := fun σ τ h1 h2 h3 ↦
    Finset.mem_biUnion.2 ⟨σ, hA σ τ h1 h2 h3,
      (Finite.mem_toFinset _).2 ⟨h2, x, mem_singularSimplexImage_of_ne_zero hφ' h3, rfl⟩⟩
  have hL : ∀ τ, kernelFun (restrictKernel U n) f τ * φ' (SingularCochain.simplexEquiv (TopCat.of U) _ τ) =
      ∑ σ ∈ A, f σ * ((restrictKernel U n σ τ : R) * φ' (SingularCochain.simplexEquiv (TopCat.of U) _ τ)) := by
    intro τ
    by_cases h : φ' (SingularCochain.simplexEquiv (TopCat.of U) _ τ) = 0
    · simp [h]
    rw [hk.kernelFun_eq_sum f τ A (fun σ h1 h2 ↦ hA σ τ h1 h2 h), Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    rw [zsmul_eq_mul]
    ring
  rw [finsum_eq_sum_of_support_subset (s := B) _ (fun τ hτ ↦ by
    rw [Function.mem_support, hL] at hτ
    obtain ⟨σ, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hτ
    exact hB σ τ (fun h0 ↦ h (by simp [h0])) (fun h0 ↦ h (by simp [h0]))
      (fun h0 ↦ h (by simp [h0])))]
  simp_rw [hL]
  have hR : ∀ σ, f σ * ∑ᶠ τ, (restrictKernel U n σ τ : R) *
      φ' (SingularCochain.simplexEquiv (TopCat.of U) _ τ) =
      ∑ τ ∈ B, f σ * ((restrictKernel U n σ τ : R) * φ' (SingularCochain.simplexEquiv (TopCat.of U) _ τ)) := by
    intro σ
    by_cases h1 : f σ = 0
    · simp [h1]
    rw [finsum_eq_sum_of_support_subset (s := B) _ (fun τ hτ ↦ by
      rw [Function.mem_support] at hτ
      exact hB σ τ h1 (fun h0 ↦ hτ (by simp [h0])) (fun h0 ↦ hτ (by simp [h0]))),
      Finset.mul_sum]
  rw [finsum_eq_sum_of_support_subset (s := A) _ (fun σ hσ ↦ by
    rw [Function.mem_support, hR] at hσ
    obtain ⟨τ, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hσ
    exact hA σ τ (fun h0 ↦ h (by simp [h0])) (fun h0 ↦ h (by simp [h0]))
      (fun h0 ↦ h (by simp [h0])))]
  simp_rw [hR]
  exact Finset.sum_comm

/-- **Restriction of local classes.** For an open subset `U` of a Hausdorff space `Y`, a point
`x` of `U` and a simplex `Δ` of `U`: if `ν ∈ H_n Y` is locally the class of `Δ` at `x`, then so
is `ν|_U ∈ H_n U`. -/
theorem IsLocallyClassOf.restrict {n : ℕ} {ν : borelMooreHomology R (ModuleCat.of R R) Y n}
    {x : U} {Δ : Simplex (TopCat.of U) n} (h : IsLocallyClassOf R ν x.1 (inclChainSimplex U Δ)) :
    IsLocallyClassOf R (borelMooreHomology.restrict R (ModuleCat.of R R) U n ν) x Δ :=
  IsLocallyClassOf.of_chainMap (restrictChainMap R (ModuleCat.of R R) U) h fun _ hφ' ↦
    ⟨pullbackCochain (restrictChainMap R (ModuleCat.of R R) U) hφ'.1,
      ⟨pullbackCochain_restrictChainMap_mem_vanishing U hφ'.1,
        coboundary_pullbackCochain _ hφ'⟩,
      pullbackCochain_restrictChainMap_inclChainSimplex U hφ'.1 Δ,
      localPairing_restrictChainMap U hφ'.1⟩

end Restriction

section Pushforward

variable {R : Type u} [CommRing R] {X X' : TopCat.{u}} (f : X ⟶ X') (hf : IsProperMap f)

open Classical in
/-- The push-forward along `f` of the single simplex `σ` is the single simplex `f ∘ σ`. -/
lemma chainMap_singleChain_apply {n : ℕ} (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌))
    (τ : (TopCat.toSSet.obj X').obj (op ⦋n⦌)) :
    ((((chainMap R (ModuleCat.of R R) f hf).f n).hom (singleChain R σ)).1 :
      (TopCat.toSSet.obj X').obj (op ⦋n⦌) → R) τ =
      if (TopCat.toSSet.map f).app _ σ = τ then 1 else 0 := by
  classical
  change pushforwardFun ((TopCat.toSSet.map f).app _) (Pi.single σ (1 : R)) τ = _
  rw [pushforwardFun, finsum_eq_single _ σ (fun σ' hσ' ↦ by
    rw [Pi.single_eq_of_ne hσ']
    simp), Pi.single_eq_same]

/-- The pull-back along push-forward by `f` of a cochain `φ'` of `X'` is `σ ↦ φ' (f ∘ σ)`. -/
lemma pullbackCochain_chainMap_apply {n : ℕ} {x' : X'}
    {φ' : Simplex X' n → R} (hφ' : φ' ∈ vanishing R n ({x'}ᶜ : Set X')) (σ : Simplex X n) :
    pullbackCochain (chainMap R (ModuleCat.of R R) f hf) hφ' σ = φ' (f.hom.comp σ) := by
  classical
  obtain ⟨σ', rfl⟩ := (SingularCochain.simplexEquiv X n).surjective σ
  rw [pullbackCochain, Equiv.symm_apply_apply, chainPairing_apply, localPairing,
    finsum_eq_single _ ((TopCat.toSSet.map f).app _ σ') (fun τ hτ ↦ by
      rw [chainMap_singleChain_apply, ite_eq_right (Ne.symm hτ), zero_mul]),
    chainMap_singleChain_apply, ite_eq_left rfl, one_mul]
  rfl

/-- Pairing with a pushed-forward chain is pairing with the pulled-back cochain. -/
lemma localPairing_chainMap {n : ℕ} {x : X} (hx : ∀ y, f y = f x → y = x)
    {φ' : Simplex X' n → R} (hφ' : φ' ∈ vanishing R n ({f x}ᶜ : Set X'))
    (c : (borelMooreChainComplex R (ModuleCat.of R R) X).X n) :
    localPairing ((((chainMap R (ModuleCat.of R R) f hf).f n).hom c).1 :
      (TopCat.toSSet.obj X').obj (op ⦋n⦌) → R) φ' =
    localPairing (c.1 : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R)
      (pullbackCochain (chainMap R (ModuleCat.of R R) f hf) hφ') := by
  classical
  set g : (TopCat.toSSet.obj X).obj (op ⦋n⦌) → R := c.1
  have hg : IsLocallyFiniteSet (singularSimplexImage X) (Function.support g) := c.2
  change ∑ᶠ τ, pushforwardFun ((TopCat.toSSet.map f).app _) g τ *
      φ' (SingularCochain.simplexEquiv X' _ τ) =
    ∑ᶠ σ, g σ * pullbackCochain (chainMap R (ModuleCat.of R R) f hf) hφ' (SingularCochain.simplexEquiv X _ σ)
  simp_rw [pullbackCochain_chainMap_apply]
  let A := (hg.finite_inter_compact (isCompact_singleton (x := x))).toFinset
  have hA : ∀ σ, g σ ≠ 0 → φ' (SingularCochain.simplexEquiv X' _ ((TopCat.toSSet.map f).app _ σ)) ≠ 0 →
      σ ∈ A := fun σ h1 h2 ↦ by
    obtain ⟨y, hy, hyx⟩ :=
      (singularSimplexImage_map f σ ▸ mem_singularSimplexImage_of_ne_zero hφ' h2 :
        f x ∈ f '' singularSimplexImage X σ)
    exact (Finite.mem_toFinset _).2 ⟨h1, x, hx y hyx ▸ hy, rfl⟩
  have hL : ∀ τ, pushforwardFun ((TopCat.toSSet.map f).app _) g τ *
      φ' (SingularCochain.simplexEquiv X' _ τ) = ∑ σ ∈ A, if (TopCat.toSSet.map f).app _ σ = τ then
        g σ * φ' (SingularCochain.simplexEquiv X' _ τ) else 0 := by
    intro τ
    by_cases h : φ' (SingularCochain.simplexEquiv X' _ τ) = 0
    · simp [h]
    rw [pushforwardFun_apply_eq_sum _ g τ A (fun σ h1 (h2 : (TopCat.toSSet.map f).app _ σ = τ) ↦
      hA σ h1 (h2.symm ▸ h)), Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    split_ifs <;> simp
  rw [finsum_eq_sum_of_support_subset (s := A.image ((TopCat.toSSet.map f).app _)) _
    (fun τ hτ ↦ by
      rw [Function.mem_support, hL] at hτ
      obtain ⟨σ, hσ, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hτ
      have hστ : (TopCat.toSSet.map f).app _ σ = τ := by
        by_contra h'
        exact h (ite_eq_right h')
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨σ, hσ, hστ⟩))]
  simp_rw [hL]
  rw [Finset.sum_comm, finsum_eq_sum_of_support_subset (s := A) _ (fun σ hσ ↦ by
    rw [Function.mem_support] at hσ
    exact hA σ (fun h0 ↦ hσ (by simp [h0])) (fun h0 ↦ hσ (by
      change g σ * φ' (SingularCochain.simplexEquiv X' _ ((TopCat.toSSet.map f).app _ σ)) = 0
      rw [h0, mul_zero])))]
  refine Finset.sum_congr rfl fun σ hσ ↦ ?_
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_image_of_mem _ hσ)]
  rfl

/-- **Push-forward of local classes.** For a proper map `f : X → X'` injective over `f x`, if
`ν ∈ H_n X` is locally the class of `Δ` at `x`, then `f_* ν` is locally the class of `f ∘ Δ` at
`f x`. -/
theorem IsLocallyClassOf.pushforward {n : ℕ} {ν : borelMooreHomology R (ModuleCat.of R R) X n}
    {x : X} (hx : ∀ y, f y = f x → y = x) {Δ : Simplex X n} (h : IsLocallyClassOf R ν x Δ) :
    IsLocallyClassOf R (borelMooreHomology.pushforward R (ModuleCat.of R R) f hf n ν) (f x)
      (f.hom.comp Δ) :=
  IsLocallyClassOf.of_chainMap (chainMap R (ModuleCat.of R R) f hf) h fun _ hφ' ↦
    ⟨pullbackCochain (chainMap R (ModuleCat.of R R) f hf) hφ'.1,
      ⟨fun σ hσ ↦ by
        rw [pullbackCochain_chainMap_apply]
        refine hφ'.1 _ fun y ⟨t, ht⟩ hy ↦ ?_
        rw [← ht] at hy
        exact hσ ⟨t, rfl⟩ (hx _ hy),
        coboundary_pullbackCochain _ hφ'⟩,
      pullbackCochain_chainMap_apply f hf hφ'.1 Δ,
      localPairing_chainMap f hf hx hφ'.1⟩

end Pushforward

section Opens

variable {R : Type u} [CommRing R] {Z : TopCat.{u}} [T2Space Z]

/-- The identification of two equal open subsets. -/
def opensEqMap {V₁ V₂ : TopologicalSpace.Opens Z} (h : V₂ = V₁) : TopCat.of V₂ ⟶ TopCat.of V₁ :=
  TopCat.ofHom ⟨fun y ↦ ⟨y.1, h ▸ y.2⟩, continuous_subtype_val.subtype_mk _⟩

omit [T2Space Z] in
/-- The identification of two equal open subsets is a proper map. -/
lemma isProperMap_opensEqMap {V₁ V₂ : TopologicalSpace.Opens Z} (h : V₂ = V₁) :
    IsProperMap (opensEqMap h) := by
  subst h
  exact isProperMap_id

/-- Restriction to equal open subsets agrees up to their identification. -/
lemma restrict_eq_pushforward_opensEqMap {V₁ V₂ : TopologicalSpace.Opens Z} (h : V₂ = V₁)
    (j : ℤ) (a : borelMooreHomology R (ModuleCat.of R R) Z j) :
    borelMooreHomology.restrict R (ModuleCat.of R R) V₁ j a =
      borelMooreHomology.pushforward R (ModuleCat.of R R) (opensEqMap h)
        (isProperMap_opensEqMap h) j (borelMooreHomology.restrict R (ModuleCat.of R R) V₂ j a) := by
  subst h
  change _ = (borelMooreHomology.pushforward R (ModuleCat.of R R) (𝟙 _)
    (by simp [isProperMap_id]) j) _
  rw [borelMooreHomology.pushforward_id]
  rfl

omit [T2Space Z] in
/-- The map `subOpensInv U h` is proper. -/
lemma isProperMap_subOpensInv {U U' : TopologicalSpace.Opens Z} (h : U' ≤ U) :
    IsProperMap (borelMooreHomology.subOpensInv U h) := by
  change IsProperMap (borelMooreHomology.subOpensHomeo U h).symm
  exact (borelMooreHomology.subOpensHomeo U h).symm.isProperMap

/-- For `U' ≤ U`, restriction to `U'` is restriction to `U` and then to `U'`, read in `U'`. -/
lemma restrict_eq_pushforward_subOpensInv {U U' : TopologicalSpace.Opens Z} (h : U' ≤ U)
    (j : ℤ) (a : borelMooreHomology R (ModuleCat.of R R) Z j) :
    borelMooreHomology.restrict R (ModuleCat.of R R) U' j a =
      borelMooreHomology.pushforward R (ModuleCat.of R R) (borelMooreHomology.subOpensInv U h)
        (isProperMap_subOpensInv h) j
        (borelMooreHomology.restrict R (ModuleCat.of R R) (borelMooreHomology.subOpens U U') j
          (borelMooreHomology.restrict R (ModuleCat.of R R) U j a)) := by
  rw [borelMooreHomology.restrict_restrict_apply R (ModuleCat.of R R) U h j a]
  have hcomp := borelMooreHomology.pushforward_comp R (ModuleCat.of R R)
    (borelMooreHomology.subOpensMap U h) (borelMooreHomology.subOpensInv U h)
    (borelMooreHomology.isProperMap_subOpensMap U h) (isProperMap_subOpensInv h) j
  have := ConcreteCategory.congr_hom hcomp (borelMooreHomology.restrict R (ModuleCat.of R R) U' j a)
  rw [ConcreteCategory.comp_apply] at this
  rw [← this]
  change _ = (borelMooreHomology.pushforward R (ModuleCat.of R R) (𝟙 _)
    (by simp [isProperMap_id]) j) _
  rw [borelMooreHomology.pushforward_id]
  rfl

end Opens

section Chart

variable {R : Type u} [CommRing R] {H : Type*} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H]
  [ContinuousAdd H] [ContinuousSMul ℝ H] {M : Type u} [TopologicalSpace M] [T2Space M]

/-- The coordinate ball of `e` meets `U` in the coordinate ball of the restricted chart `e|_U`. -/
lemma subOpens_chartOpens_inf_eq (e : OpenPartialHomeomorph M H) (U : TopologicalSpace.Opens M)
    (hU : Nonempty U) :
    borelMooreHomology.subOpens (U : TopologicalSpace.Opens (TopCat.of M))
      (chartOpens e ⊓ (U : TopologicalSpace.Opens (TopCat.of M))) =
      chartOpens (e.subtypeRestr hU) := by
  ext y
  change y.1 ∈ e.source ∧ y.1 ∈ U ↔ y ∈ (e.subtypeRestr hU).source
  rw [OpenPartialHomeomorph.subtypeRestr_source]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, y.2⟩⟩

/-- Restricting to `U` and then to the coordinate ball of `e|_U` is restricting to the coordinate
ball of `e` and transporting along the inclusions of `e.source ∩ U`. -/
lemma restrict_chartOpens_subtypeRestr {n : ℕ} (e : OpenPartialHomeomorph M H)
    (U : TopologicalSpace.Opens M) (hU : Nonempty U)
    (μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) n) :
    borelMooreHomology.restrict R (ModuleCat.of R R) (chartOpens (e.subtypeRestr hU)) n
      (borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of M) U n μ) =
      borelMooreHomology.pushforward R (ModuleCat.of R R)
        (opensEqMap (subOpens_chartOpens_inf_eq e U hU))
        (isProperMap_opensEqMap (subOpens_chartOpens_inf_eq e U hU)) n
        (borelMooreHomology.pushforward R (ModuleCat.of R R)
          (borelMooreHomology.subOpensMap _ (inf_le_right :
            chartOpens e ⊓ (U : TopologicalSpace.Opens (TopCat.of M)) ≤ U))
          (borelMooreHomology.isProperMap_subOpensMap _ inf_le_right) n
          (borelMooreHomology.pushforward R (ModuleCat.of R R)
            (borelMooreHomology.subOpensInv _ (inf_le_left :
              chartOpens e ⊓ (U : TopologicalSpace.Opens (TopCat.of M)) ≤ chartOpens e))
            (isProperMap_subOpensInv inf_le_left) n
            (borelMooreHomology.restrict R (ModuleCat.of R R)
              (borelMooreHomology.subOpens (chartOpens e)
                (chartOpens e ⊓ (U : TopologicalSpace.Opens (TopCat.of M)))) n
              (borelMooreHomology.restrict R (ModuleCat.of R R) (chartOpens e) n μ)))) := by
  rw [restrict_eq_pushforward_opensEqMap (subOpens_chartOpens_inf_eq e U hU),
    borelMooreHomology.restrict_restrict_apply R (ModuleCat.of R R) _ inf_le_right,
    ← restrict_eq_pushforward_subOpensInv inf_le_left]

/-- **Restriction of a chart orientation class.** If the restriction of `μ ∈ H_n M` to the
coordinate ball of a chart `e` is its orientation generator, then for every open `U ⊆ M` the
restriction of `μ|_U` to the coordinate ball of the restricted chart `e|_U` is the orientation
generator. -/
theorem IsChartOrientationClass.subtypeRestr {n : ℕ} {b : Module.Basis (Fin n) ℝ H}
    {e : OpenPartialHomeomorph M H}
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) n}
    (h : IsChartOrientationClass R b e
      (borelMooreHomology.restrict R (ModuleCat.of R R) (chartOpens e) n μ))
    (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    IsChartOrientationClass R b (e.subtypeRestr hU)
      (borelMooreHomology.restrict R (ModuleCat.of R R) (chartOpens (e.subtypeRestr hU)) n
        (borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of M) U n μ)) := by
  have hWB : chartOpens e ⊓ (U : TopologicalSpace.Opens (TopCat.of M)) ≤ chartOpens e :=
    inf_le_left
  have hWU : chartOpens e ⊓ (U : TopologicalSpace.Opens (TopCat.of M)) ≤
      (U : TopologicalSpace.Opens (TopCat.of M)) := inf_le_right
  have hV := subOpens_chartOpens_inf_eq e U hU
  rw [restrict_chartOpens_subtypeRestr]
  intro x' v hv hvt'
  have hx'src : x'.1.1 ∈ e.source := by
    have := x'.2
    change x'.1 ∈ (e.subtypeRestr hU).source at this
    rwa [OpenPartialHomeomorph.subtypeRestr_source] at this
  let x₀ : chartOpens e := ⟨x'.1.1, hx'src⟩
  have hvt : range (affineSimplex v) ⊆ e.target :=
    hvt'.trans (e.subtypeRestr_target_subset hU)
  have hsymm : ∀ t, ((e.subtypeRestr hU).symm (affineSimplex v t) : M) =
      e.symm (affineSimplex v t) := fun t ↦
    e.subtypeRestr_symm_apply hU (hvt' ⟨t, rfl⟩)
  have hmemU : ∀ t, e.symm (affineSimplex v t) ∈ U := fun t ↦ by
    rw [← hsymm t]
    exact ((e.subtypeRestr hU).symm (affineSimplex v t)).2
  let Δ₁ : Simplex (TopCat.of (borelMooreHomology.subOpens (chartOpens e)
      (chartOpens e ⊓ (U : TopologicalSpace.Opens (TopCat.of M))))) n :=
    ⟨fun t ↦ ⟨chartSimplex e v hvt t, ⟨(chartSimplex e v hvt t).2, hmemU t⟩⟩,
      (chartSimplex e v hvt).continuous.subtype_mk _⟩
  let x₁ : borelMooreHomology.subOpens (chartOpens e)
      (chartOpens e ⊓ (U : TopologicalSpace.Opens (TopCat.of M))) := ⟨x₀, ⟨hx'src, x'.1.2⟩⟩
  have h1 := IsLocallyClassOf.restrict (borelMooreHomology.subOpens (chartOpens e)
      (chartOpens e ⊓ (U : TopologicalSpace.Opens (TopCat.of M)))) (x := x₁) (Δ := Δ₁)
      (h x₀ v hv hvt)
  have h2 := IsLocallyClassOf.pushforward (borelMooreHomology.subOpensInv _ hWB)
    (isProperMap_subOpensInv hWB)
    (fun y hy ↦ (borelMooreHomology.subOpensHomeo _ hWB).symm.injective hy) h1
  have h3 := IsLocallyClassOf.pushforward (borelMooreHomology.subOpensMap _ hWU)
    (borelMooreHomology.isProperMap_subOpensMap _ hWU)
    (fun y hy ↦ (borelMooreHomology.subOpensHomeo _ hWU).injective hy) h2
  have h4 := IsLocallyClassOf.pushforward (opensEqMap hV) (isProperMap_opensEqMap hV)
    (fun y hy ↦ Subtype.ext
      (congrArg (fun z : chartOpens (e.subtypeRestr hU) ↦ (z : U)) hy)) h3
  convert h4 using 1
  · exact Subtype.ext (Subtype.ext rfl)
  · exact ContinuousMap.ext fun t ↦ Subtype.ext (Subtype.ext (hsymm t))

end Chart

end FundamentalClass

open FundamentalClass

section Manifold

variable {R : Type u} [CommRing R] {H : Type*} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H]
  [ContinuousAdd H] [ContinuousSMul ℝ H] {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace H M]

/-- **Restriction of the fundamental class to an open subset** (Fulton, §19.1). Let `M` be an
oriented real `n`-manifold and `U ⊆ M` open, with the induced orientation. Then
`μ_M|_U = μ_U`. -/
theorem IsFundamentalClass.restrict {n : ℕ} {b : Module.Basis (Fin n) ℝ H}
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) n}
    (h : IsFundamentalClass R b μ) (U : TopologicalSpace.Opens M) :
    IsFundamentalClass R b
      (borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of M) U n μ) := by
  rintro e' ⟨_, ⟨x, rfl⟩, he'⟩
  rw [Set.mem_singleton_iff] at he'
  subst he'
  exact IsChartOrientationClass.subtypeRestr (h _ (chart_mem_atlas H x.1)) U ⟨x⟩

end Manifold

end MMP
