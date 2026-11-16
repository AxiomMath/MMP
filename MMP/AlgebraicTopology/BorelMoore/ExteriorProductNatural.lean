module

public import MMP.AlgebraicTopology.BorelMoore.ExteriorProduct
public import MMP.AlgebraicTopology.BorelMoore.Pushforward
/-!
# Naturality of the exterior product in Borel–Moore homology (Fulton, §19.1)

For proper maps `f : X → X'` and `g : Y → Y'` the exterior product commutes with push-forward:
`(f × g)_* (a × b) = f_* a × g_* b` for `a ∈ H_i X`, `b ∈ H_j Y`.

This holds already on chains. The cross product of singular simplices is natural,
`(f × g) ∘ (σ × τ) = (f ∘ σ) × (g ∘ τ)`, since each simplex of `σ × τ` is
`t ↦ (σ (A t), τ (B t))` for affine maps `A`, `B`. Hence for locally finite chains
`c = ∑ a_σ σ` and `d = ∑ b_τ τ`, `(f × g)_♯ (c × d) = ∑ a_σ b_τ (f ∘ σ) × (g ∘ τ) = f_♯ c × g_♯ d`;
the sums are finite at each simplex of `X' × Y'` because `f` and `g` are proper.

More generally, chain maps `φ_X`, `φ_Y`, `φ` of complexes of locally finite chains with
`φ (c × d) = φ_X c × φ_Y d` satisfy `φ_* (a × b) = φ_{X*} a × φ_{Y*} b` on homology
(`MMP.BorelMooreCross.homologyMap_exteriorProduct`).

The compatibility with restriction to open subsets, `(a × b)|_{U × V} = a|_U × b|_V`, is
`MMP.borelMooreHomology.restrict_exteriorProduct`.

## Main results

* `MMP.BorelMooreCross.chainMap_prodHom_crossChain`: the identity on chains.
* `MMP.BorelMooreCross.homologyMap_exteriorProduct`: chain maps compatible with
  the cross product of chains are compatible with the exterior product.
* `MMP.borelMooreHomology.pushforward_exteriorProduct`:
  `(f × g)_* (a × b) = f_* a × g_* b`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [A. Borel, J. C. Moore, *Homology theory for locally compact spaces*][borelmoore1960], §6.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Simplicial AlgebraicTopology MMP.LatticePath
  MMP.SingularCross MMP.LocallyFiniteChain TensorProduct

universe u

namespace MMP

namespace LocallyFiniteChain

section Proper

variable {X X' : Type*} [TopologicalSpace X] [TopologicalSpace X'] {I I' T T' : Type*}
  {carI : I → Set X} {carI' : I' → Set X'} {carT : T → Set X} {carT' : T' → Set X'}
  {R : Type*} [CommRing R]

open Classical in
/-- Push-forward along a proper map of a transfer is the transfer along the pushed-forward
family. -/
lemma pushforwardFun_lfTransferFun_of_isProperMap {c : I → R} (hc : c ∈ lfChains R R carI)
    {Ψ : I → T →₀ ℤ} (hΨ : IsCarrierDecreasing carI carT Ψ) {f : X → X'} (hf : IsProperMap f)
    (φ : T → T') (hφ : ∀ t, carT' (φ t) ⊆ f '' carT t)
    (hT' : ∀ t', IsCompact (carT' t') ∧ (carT' t').Nonempty) :
    pushforwardFun φ (lfTransferFun Ψ c) =
      lfTransferFun (fun i ↦ Finsupp.mapDomain φ (Ψ i)) c := by
  ext t'
  have hfin : {i | c i ≠ 0 ∧ (carI i ∩ f ⁻¹' carT' t').Nonempty}.Finite :=
    hc.finite_inter_compact (hf.isCompact_preimage (hT' t').1)
  let FI := hfin.toFinset
  let FT := FI.biUnion fun i ↦ (Ψ i).support
  have hmem : ∀ i t, c i ≠ 0 → Ψ i t ≠ 0 → φ t = t' → i ∈ FI ∧ t ∈ FT := fun i t h h' h'' ↦ by
    have hi : i ∈ FI := by
      obtain ⟨x, hx⟩ := (hT' t').2
      obtain ⟨y, hy, hyx⟩ := hφ t (h'' ▸ hx)
      simpa [FI] using And.intro h ⟨y, hΨ i t h' hy, show f y ∈ carT' t' from hyx ▸ hx⟩
    exact ⟨hi, Finset.mem_biUnion.2 ⟨i, hi, by simpa using h'⟩⟩
  have hL : pushforwardFun φ (lfTransferFun Ψ c) t' =
      ∑ t ∈ FT, if φ t = t' then ∑ i ∈ FI, c i * (Ψ i t : R) else 0 := by
    refine (pushforwardFun_apply_eq_sum φ _ t' FT fun t ht h ↦ ?_).trans
      (Finset.sum_congr rfl fun t _ ↦ ?_)
    · obtain ⟨i, hi⟩ : ∃ i, c i * (Ψ i t : R) ≠ 0 := by
        by_contra! hh
        exact ht (finsum_eq_zero_of_forall_eq_zero hh)
      exact (hmem i t (fun h0 ↦ hi (by simp [h0])) (fun h0 ↦ hi (by simp [h0])) h).2
    · split_ifs with h
      · exact lfTransferFun_eq_sum Ψ c t FI fun i hi hi' ↦ (hmem i t hi hi' h).1
      · rfl
  rw [hL, lfTransferFun_eq_sum _ c t' FI fun i hi hi' ↦ ?_]
  · symm
    calc ∑ i ∈ FI, c i * ((Finsupp.mapDomain φ (Ψ i) t' : ℤ) : R)
        = ∑ i ∈ FI, ∑ t ∈ FT, (if φ t = t' then c i * (Ψ i t : R) else 0) :=
          Finset.sum_congr rfl fun i hi ↦ by
            rw [mapDomain_apply_eq_sum' φ (Ψ i) t' FT fun t ht ↦
              Finset.mem_biUnion.2 ⟨i, hi, ht⟩, Int.cast_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun t _ ↦ by split_ifs <;> simp
      _ = ∑ t ∈ FT, ∑ i ∈ FI, (if φ t = t' then c i * (Ψ i t : R) else 0) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun t _ ↦ by split_ifs <;> simp
  · obtain ⟨t, ht, rfl⟩ : ∃ t, Ψ i t ≠ 0 ∧ φ t = t' := by
      by_contra! hh
      refine hi' ?_
      rw [mapDomain_apply_eq_sum]
      exact Finset.sum_eq_zero fun t ht ↦ by
        split_ifs with h
        · exact absurd (hh t (by simpa using ht)) (by simp [h])
        · rfl
    exact (hmem i t hi ht rfl).1

open Classical in
/-- A transfer of a push-forward along a proper map is the transfer along the composite
family. -/
lemma lfTransferFun_pushforwardFun_of_isProperMap {c : I → R} (hc : c ∈ lfChains R R carI)
    {f : X → X'} (hf : IsProperMap f) (g : I → I') (hg : ∀ i, carI' (g i) ⊆ f '' carI i)
    {Ψ : I' → T' →₀ ℤ} (hΨ : IsCarrierDecreasing carI' carT' Ψ)
    (hT : ∀ t, IsCompact (carT' t) ∧ (carT' t).Nonempty) :
    lfTransferFun Ψ (pushforwardFun g c) = lfTransferFun (Ψ ∘ g) c := by
  ext t
  have hfin : {i | c i ≠ 0 ∧ (carI i ∩ f ⁻¹' carT' t).Nonempty}.Finite :=
    hc.finite_inter_compact (hf.isCompact_preimage (hT t).1)
  let F' := hfin.toFinset
  have hmem : ∀ i, c i ≠ 0 → Ψ (g i) t ≠ 0 → i ∈ F' := fun i h h' ↦ by
    obtain ⟨x, hx⟩ := (hT t).2
    obtain ⟨y, hy, hyx⟩ := hg i (hΨ _ t h' hx)
    simpa [F'] using And.intro h ⟨y, hy, show f y ∈ carT' t from hyx ▸ hx⟩
  rw [lfTransferFun_eq_sum (Ψ ∘ g) c t F' hmem,
    lfTransferFun_eq_sum Ψ _ t (F'.image g) fun i hi hi' ↦ ?_]
  · have : ∀ i ∈ F'.image g, pushforwardFun g c i * (Ψ i t : R) =
        ∑ i' ∈ F', if g i' = i then c i' * (Ψ i t : R) else 0 := fun i _ ↦ by
      by_cases hΨi : Ψ i t = 0
      · simp [hΨi]
      · rw [pushforwardFun_apply_eq_sum g c i F' fun i' h h' ↦ hmem i' h (h' ▸ hΨi),
          Finset.sum_mul]
        exact Finset.sum_congr rfl fun i' _ ↦ by split_ifs <;> simp
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i' hi' ↦ ?_
    rw [Finset.sum_ite_eq (F'.image g) (g i')]
    simp only [Finset.mem_image_of_mem g hi', ↓reduceIte]
    rfl
  · obtain ⟨i', hi'c, rfl⟩ := support_pushforwardFun_subset g c hi
    exact Finset.mem_image_of_mem g (hmem i' hi'c hi')

end Proper

section ProperTensor

variable {X X' Y Y' : Type*} [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y]
  [TopologicalSpace Y'] {S S' U U' : Type*} {carS : S → Set X} {carS' : S' → Set Y}
  {carU : U → Set X'} {carU' : U' → Set Y'} {R : Type*} [CommRing R]

open Classical in
/-- Push-forward of the tensor of two chains along proper maps on both factors. -/
lemma pushforwardFun_prodMap_lfTensor {c : S → R} (hc : c ∈ lfChains R R carS) {d : S' → R}
    (hd : d ∈ lfChains R R carS') {f : X → X'} (hf : IsProperMap f) {g : Y → Y'}
    (hg : IsProperMap g) (φ : S → U) (hφ : ∀ σ, carU (φ σ) ⊆ f '' carS σ)
    (hU : ∀ υ, IsCompact (carU υ) ∧ (carU υ).Nonempty) (ψ : S' → U')
    (hψ : ∀ τ, carU' (ψ τ) ⊆ g '' carS' τ) (hU' : ∀ υ, IsCompact (carU' υ) ∧ (carU' υ).Nonempty) :
    pushforwardFun (Prod.map φ ψ) (lfTensor c d) =
      lfTensor (pushforwardFun φ c) (pushforwardFun ψ d) := by
  ext ⟨υ, υ'⟩
  let F := (finite_fiber_of_isProperMap hc hf φ hφ υ (hU υ).1 (hU υ).2).toFinset
  let G := (finite_fiber_of_isProperMap hd hg ψ hψ υ' (hU' υ').1 (hU' υ').2).toFinset
  have hF : ∀ σ, c σ ≠ 0 → φ σ = υ → σ ∈ F := fun σ h h' ↦ by simpa [F] using And.intro h h'
  have hG : ∀ τ, d τ ≠ 0 → ψ τ = υ' → τ ∈ G := fun τ h h' ↦ by simpa [G] using And.intro h h'
  rw [pushforwardFun_apply_eq_sum _ _ _ (F ×ˢ G) fun p hp hp' ↦ ?_]
  · simp only [lfTensor]
    rw [pushforwardFun_apply_eq_sum φ c υ F hF, pushforwardFun_apply_eq_sum ψ d υ' G hG,
      Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun σ _ ↦ Finset.sum_congr rfl fun τ _ ↦ ?_
    simp only [Prod.map, Prod.mk.injEq]
    split_ifs <;> simp_all
  · obtain ⟨σ, τ⟩ := p
    simp only [Prod.map, Prod.mk.injEq] at hp'
    have h1 : c σ ≠ 0 := fun h ↦ hp (by simp [lfTensor, h])
    have h2 : d τ ≠ 0 := fun h ↦ hp (by simp [lfTensor, h])
    exact Finset.mem_product.2 ⟨hF σ h1 hp'.1, hG τ h2 hp'.2⟩

end ProperTensor

end LocallyFiniteChain

namespace SingularCross

variable {X X' Y Y' : TopCat.{u}}

/-- The product `f × g : X × Y → X' × Y'` of continuous maps, as a morphism of spaces. -/
abbrev prodHom (f : X ⟶ X') (g : Y ⟶ Y') : TopCat.of (X × Y) ⟶ TopCat.of (X' × Y') :=
  TopCat.ofHom (f.hom.prodMap g.hom)

/-- The product of two proper maps is proper. -/
lemma isProperMap_prodHom {f : X ⟶ X'} {g : Y ⟶ Y'} (hf : IsProperMap f) (hg : IsProperMap g) :
    IsProperMap (prodHom f g) :=
  hf.prodMap hg

/-- The continuous map underlying the image of a singular simplex `ρ` under `h` is `h ∘ ρ`. -/
lemma toC_map {Z Z' : TopCat.{u}} (h : Z ⟶ Z') {n : ℕ} (ρ : Simp Z n) :
    toC ((TopCat.toSSet.map h).app (op ⦋n⦌) ρ) = h.hom.comp (toC ρ) :=
  rfl

/-- Path simplices are natural in both factors. -/
lemma map_pathSimplex (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) {p q : ℕ} (σ : Simp X p)
    (τ : Simp Y q) (l : List (ℕ × ℕ)) :
    (TopCat.toSSet.map (prodHom f g)).app (op ⦋n⦌) (pathSimplex n σ τ l) =
      pathSimplex n ((TopCat.toSSet.map f).app (op ⦋p⦌) σ)
        ((TopCat.toSSet.map g).app (op ⦋q⦌) τ) l := by
  apply toC_injective
  rw [toC_map, toC_pathSimplex, toC_pathSimplex, toC_map, toC_map]
  rfl

/-- The cross product of singular simplices is natural: `(f × g) ∘ (σ × τ) = (f ∘ σ) × (g ∘ τ)`. -/
lemma mapDomain_crossSimplex (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) {p q : ℕ} (σ : Simp X p)
    (τ : Simp Y q) :
    Finsupp.mapDomain ((TopCat.toSSet.map (prodHom f g)).app (op ⦋n⦌)) (crossSimplex n σ τ) =
      crossSimplex n ((TopCat.toSSet.map f).app (op ⦋p⦌) σ)
        ((TopCat.toSSet.map g).app (op ⦋q⦌) τ) := by
  rw [crossSimplex, crossSimplex, ← Finsupp.mapDomain_comp]
  exact congrArg (fun φ ↦ Finsupp.mapDomain φ (shuffleSum n p q))
    (funext fun l ↦ map_pathSimplex f g n σ τ l)

end SingularCross

namespace BorelMooreCross

variable {R : Type u} [CommRing R] {X X' Y Y' : TopCat.{u}}

/-- The coefficients of the push-forward `f_♯ c` of a locally finite chain are the push-forward
of the coefficients of `c` along `σ ↦ f ∘ σ`. -/
lemma coeff_chainMap_f (f : X ⟶ X') (hf : IsProperMap f) (n : ℕ) (c : (BM R X).X n) :
    coeff R (((borelMooreHomology.chainMap R (ModuleCat.of R R) f hf).f n).hom c) =
      pushforwardFun ((TopCat.toSSet.map f).app (op ⦋n⦌)) (coeff R c) :=
  rfl

/-- On chains, the push-forward along `f × g` of a cross product is the cross product of the
push-forwards: `(f × g)_♯ (c × d) = f_♯ c × g_♯ d`. -/
theorem chainMap_prodHom_crossChain (f : X ⟶ X') (g : Y ⟶ Y') (hf : IsProperMap f)
    (hg : IsProperMap g) (n p q : ℕ) (c : (BM R X).X p) (d : (BM R Y).X q) :
    ((borelMooreHomology.chainMap R (ModuleCat.of R R) (prodHom f g)
        (isProperMap_prodHom hf hg)).f n).hom (crossChain R n p q c d) =
      crossChain R n p q (((borelMooreHomology.chainMap R (ModuleCat.of R R) f hf).f p).hom c)
        (((borelMooreHomology.chainMap R (ModuleCat.of R R) g hg).f q).hom d) := by
  apply coeff_injective R
  rw [coeff_chainMap_f, coeff_crossChain, coeff_crossChain, coeff_chainMap_f, coeff_chainMap_f,
    crossFun, crossFun,
    pushforwardFun_lfTransferFun_of_isProperMap (lfTensor_mem (coeff_mem R c) (coeff_mem R d))
      (isCarrierDecreasing_crossFamily n p q) (isProperMap_prodHom hf hg) _
      (fun ρ ↦ (singularSimplexImage_map _ ρ).le) compact_nonempty,
    ← pushforwardFun_prodMap_lfTensor (coeff_mem R c) (coeff_mem R d) hf hg _
      (fun σ ↦ (singularSimplexImage_map f σ).le) compact_nonempty _
      (fun τ ↦ (singularSimplexImage_map g τ).le) compact_nonempty,
    lfTransferFun_pushforwardFun_of_isProperMap (lfTensor_mem (coeff_mem R c) (coeff_mem R d))
      (hf.prodMap hg) _ (fun st ↦ ?_) (isCarrierDecreasing_crossFamily n p q) compact_nonempty]
  · exact congrArg (fun Ψ ↦ lfTransferFun Ψ (lfTensor (coeff R c) (coeff R d)))
      (funext fun st ↦ mapDomain_crossSimplex f g n st.1 st.2)
  · obtain ⟨σ, τ⟩ := st
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    change a ∈ singularSimplexImage X' ((TopCat.toSSet.map f).app (op ⦋p⦌) σ) at ha
    change b ∈ singularSimplexImage Y' ((TopCat.toSSet.map g).app (op ⦋q⦌) τ) at hb
    rw [singularSimplexImage_map] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩

section Homology

variable (R)

/-- The map on Borel–Moore homology in degree `i` induced by a map of complexes of locally finite
chains. -/
def homologyMap (φ : BM R X ⟶ BM R X') (i : ℤ) :
    borelMooreHomology R (ModuleCat.of R R) X i ⟶ borelMooreHomology R (ModuleCat.of R R) X' i :=
  HomologicalComplex.homologyMap (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat) (-i)

/-- Push-forward along a proper map `f` is the map on homology induced by the chain map `f_♯`. -/
lemma pushforward_eq_homologyMap (f : X ⟶ X') (hf : IsProperMap f) (i : ℤ) :
    borelMooreHomology.pushforward R (ModuleCat.of R R) f hf i =
      homologyMap R (borelMooreHomology.chainMap R (ModuleCat.of R R) f hf) i :=
  rfl

/-- A map of complexes of locally finite chains sends cycles to cycles. -/
lemma chainMap_mem_cyc (φ : BM R X ⟶ BM R X') {n : ℕ} (z : Cyc (R := R) X n) :
    (φ.f n).hom z.1 ∈ Cyc (R := R) X' n := by
  rw [mem_cyc_iff]
  have h := congrArg (fun m ↦ m.hom z.1) (φ.comm n (n - 1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h, (mem_cyc_iff z.1).1 z.2, map_zero]

/-- A map of complexes of locally finite chains acts on Borel–Moore homology in degree `p : ℕ`,
identified with cycles modulo boundaries, by `[z] ↦ [φ z]`. -/
lemma homologyMap_homologyEquiv_symm_mk (φ : BM R X ⟶ BM R X') (p : ℕ) (z : Cyc (R := R) X p) :
    (homologyMap R φ p).hom ((homologyEquiv R X p).symm (Submodule.Quotient.mk z)) =
      (homologyEquiv R X' p).symm
        (Submodule.Quotient.mk ⟨(φ.f p).hom z.1, chainMap_mem_cyc R φ z⟩) := by
  refine (LinearEquiv.eq_symm_apply _).2 ?_
  set Y := ((BM R X).sc p).moduleCatCyclesIso.inv.hom z
  have h1 : (homologyEquiv R X p).symm (Submodule.Quotient.mk z) =
      (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) X p).inv.hom
        (((BM R X).sc p).homologyπ.hom Y) := by
    have := congrArg (fun m ↦ m.hom z) ((BM R X).sc p).moduleCatCyclesIso_inv_π
    exact (congrArg (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) X p).inv.hom this).symm
  have hn := congrArg (fun m ↦ m.hom ((borelMooreHomologyIsoOfNat R (ModuleCat.of R R) X p).inv.hom
      (((BM R X).sc p).homologyπ.hom Y)))
    (HomologicalComplex.extendHomologyIso_hom_naturality φ ComplexShape.embeddingDownNat
      (j := p) (j' := -(p : ℤ)) (by simp))
  simp only [ModuleCat.hom_comp] at hn
  rw [h1]
  change ((BM R X').sc p).moduleCatHomologyIso.hom.hom
    ((borelMooreHomologyIsoOfNat R (ModuleCat.of R R) X' p).hom.hom
      ((homologyMap R φ p).hom ((borelMooreHomologyIsoOfNat R (ModuleCat.of R R) X p).inv.hom
        (((BM R X).sc p).homologyπ.hom Y)))) = _
  erw [hn]
  have e : ∀ x, (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) X p).hom.hom
      ((borelMooreHomologyIsoOfNat R (ModuleCat.of R R) X p).inv.hom x) = x := fun x ↦ by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Iso.inv_hom_id, ModuleCat.hom_id,
      LinearMap.id_apply]
  change ((BM R X').sc p).moduleCatHomologyIso.hom.hom ((HomologicalComplex.homologyMap φ p).hom
    ((borelMooreHomologyIsoOfNat R (ModuleCat.of R R) X p).hom.hom
      ((borelMooreHomologyIsoOfNat R (ModuleCat.of R R) X p).inv.hom
        (((BM R X).homologyπ p).hom Y)))) = _
  rw [e]
  have h2 := congrArg (fun m ↦ m.hom Y) (HomologicalComplex.homologyπ_naturality φ p)
  refine (congrArg ((BM R X').sc p).moduleCatHomologyIso.hom.hom h2).trans ?_
  refine (ShortComplex.π_moduleCatCyclesIso_hom_apply ((BM R X').sc p)
    ((HomologicalComplex.cyclesMap φ p).hom Y)).trans ?_
  change Submodule.Quotient.mk _ = _
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  refine (ShortComplex.moduleCatCyclesIso_hom_i_apply ((BM R X').sc p)
    ((HomologicalComplex.cyclesMap φ p).hom Y)).trans ?_
  have h3 := congrArg (fun m ↦ m.hom Y) (HomologicalComplex.cyclesMap_i φ p)
  simp only [ModuleCat.hom_comp] at h3
  refine h3.trans ?_
  change (φ.f p).hom ((((BM R X).sc p).iCycles).hom
    (((BM R X).sc p).moduleCatCyclesIso.inv.hom z)) = _
  exact congrArg (φ.f p).hom
    (ShortComplex.moduleCatCyclesIso_inv_iCycles_apply ((BM R X).sc p) z)

/-- The map on homology induced by `φ` commutes with the identification of Borel–Moore homology
in equal degrees `i = i'`. -/
lemma homologyMap_congrDegree (φ : BM R X ⟶ BM R X') {i i' : ℤ} (h : i = i')
    (x : borelMooreHomology R (ModuleCat.of R R) X i) :
    (homologyMap R φ i').hom (congrDegree R X h x) =
      congrDegree R X' h ((homologyMap R φ i).hom x) := by
  subst h
  simp only [congrDegree_self, LinearEquiv.refl_apply]

/-- **Naturality of the exterior product.** Maps of complexes of locally finite chains
`φ_X`, `φ_Y`, `φ` such that `φ (z × w) - φ_X z × φ_Y w` is a boundary for all cycles `z`, `w`
satisfy `φ_* (a × b) = φ_{X*} a × φ_{Y*} b` on Borel–Moore homology. -/
theorem homologyMap_exteriorProduct_of_exists_d (φX : BM R X ⟶ BM R X')
    (φY : BM R Y ⟶ BM R Y') (φ : BM R (TopCat.of (X × Y)) ⟶ BM R (TopCat.of (X' × Y')))
    (h : ∀ p q (z : Cyc (R := R) X p) (w : Cyc (R := R) Y q),
      ∃ u : (BM R (TopCat.of (X' × Y'))).X (p + q + 1),
        ((BM R (TopCat.of (X' × Y'))).d (p + q + 1) (p + q)).hom u =
          (φ.f (p + q)).hom (crossChain R (p + q) p q z.1 w.1) -
            crossChain R (p + q) p q ((φX.f p).hom z.1) ((φY.f q).hom w.1))
    (i j : ℤ) (a : borelMooreHomology R (ModuleCat.of R R) X i)
    (b : borelMooreHomology R (ModuleCat.of R R) Y j) :
    (homologyMap R φ (i + j)).hom (borelMooreHomology.exteriorProduct R X Y i j (a ⊗ₜ b)) =
      borelMooreHomology.exteriorProduct R X' Y' i j
        ((homologyMap R φX i).hom a ⊗ₜ (homologyMap R φY j).hom b) := by
  rw [borelMooreHomology.exteriorProduct_tmul, borelMooreHomology.exteriorProduct_tmul]
  by_cases hij : 0 ≤ i ∧ 0 ≤ j
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hij.1
    obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hij.2
    obtain ⟨z, rfl⟩ : ∃ z : Cyc (R := R) X p,
        (homologyEquiv R X p).symm (Submodule.Quotient.mk z) = a := by
      obtain ⟨x, rfl⟩ := (homologyEquiv R X p).symm.surjective a
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact ⟨z, rfl⟩
    obtain ⟨w, rfl⟩ : ∃ w : Cyc (R := R) Y q,
        (homologyEquiv R Y q).symm (Submodule.Quotient.mk w) = b := by
      obtain ⟨y, rfl⟩ := (homologyEquiv R Y q).symm.surjective b
      obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨w, rfl⟩
    rw [homologyMap_homologyEquiv_symm_mk, homologyMap_homologyEquiv_symm_mk]
    refine (congrArg (homologyMap R φ _).hom (exteriorProductBilin_natCast R X Y p q _ _)).trans ?_
    refine Eq.trans ?_ (exteriorProductBilin_natCast R X' Y' p q _ _).symm
    rw [homologyMap_congrDegree]
    congr 1
    refine (congrArg (homologyMap R φ _).hom
      (congrArg (homologyEquiv R _ _).symm (crossHomQ_mk p q z w))).trans ?_
    refine Eq.trans ?_ (congrArg (homologyEquiv R _ _).symm (crossHomQ_mk p q _ _)).symm
    refine (homologyMap_homologyEquiv_symm_mk R φ (p + q)
      ⟨crossChain R (p + q) p q z.1 w.1, crossChain_mem_cyc p q z w⟩).trans ?_
    congr 1
    refine (Submodule.Quotient.eq _).2 ?_
    obtain ⟨u, hu⟩ := h p q z w
    exact mem_bdry_of _ u hu
  · rw [exteriorProductBilin_of_neg R X Y (by omega),
      exteriorProductBilin_of_neg R X' Y' (by omega)]
    simp

/-- **Naturality of the exterior product.** Maps of complexes of locally finite chains
`φ_X`, `φ_Y`, `φ` with `φ (c × d) = φ_X c × φ_Y d` satisfy `φ_* (a × b) = φ_{X*} a × φ_{Y*} b`
on Borel–Moore homology. -/
theorem homologyMap_exteriorProduct (φX : BM R X ⟶ BM R X') (φY : BM R Y ⟶ BM R Y')
    (φ : BM R (TopCat.of (X × Y)) ⟶ BM R (TopCat.of (X' × Y')))
    (h : ∀ p q (c : (BM R X).X p) (d : (BM R Y).X q),
      (φ.f (p + q)).hom (crossChain R (p + q) p q c d) =
        crossChain R (p + q) p q ((φX.f p).hom c) ((φY.f q).hom d))
    (i j : ℤ) (a : borelMooreHomology R (ModuleCat.of R R) X i)
    (b : borelMooreHomology R (ModuleCat.of R R) Y j) :
    (homologyMap R φ (i + j)).hom (borelMooreHomology.exteriorProduct R X Y i j (a ⊗ₜ b)) =
      borelMooreHomology.exteriorProduct R X' Y' i j
        ((homologyMap R φX i).hom a ⊗ₜ (homologyMap R φY j).hom b) :=
  homologyMap_exteriorProduct_of_exists_d R φX φY φ (fun p q z w ↦ ⟨0, by
    rw [map_zero, h, sub_self]⟩) i j a b

end Homology

end BorelMooreCross

namespace borelMooreHomology

open BorelMooreCross

variable (R : Type u) [CommRing R] {X X' Y Y' : TopCat.{u}}

/-- **The exterior product commutes with proper push-forward** (Fulton, §19.1): for proper maps
`f : X → X'`, `g : Y → Y'` and `a ∈ H_i X`, `b ∈ H_j Y`, `(f × g)_* (a × b) = f_* a × g_* b`. -/
theorem pushforward_exteriorProduct (f : X ⟶ X') (g : Y ⟶ Y') (hf : IsProperMap f)
    (hg : IsProperMap g) (i j : ℤ) (a : borelMooreHomology R (ModuleCat.of R R) X i)
    (b : borelMooreHomology R (ModuleCat.of R R) Y j) :
    (pushforward R (ModuleCat.of R R) (prodHom f g) (isProperMap_prodHom hf hg) (i + j)).hom
        (exteriorProduct R X Y i j (a ⊗ₜ b)) =
      exteriorProduct R X' Y' i j
        ((pushforward R (ModuleCat.of R R) f hf i).hom a ⊗ₜ
          (pushforward R (ModuleCat.of R R) g hg j).hom b) :=
  homologyMap_exteriorProduct R _ _ _
    (fun p q c d ↦ chainMap_prodHom_crossChain f g hf hg (p + q) p q c d) i j a b

end borelMooreHomology

end MMP
