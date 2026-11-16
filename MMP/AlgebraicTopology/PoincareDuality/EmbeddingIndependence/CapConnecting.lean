module

public import MMP.AlgebraicTopology.BorelMoore.MayerVietoris
public import MMP.AlgebraicTopology.SingularCohomology.MayerVietoris.Subspace
public import MMP.AlgebraicTopology.CapProduct.RestrictionCycles
public import MMP.AlgebraicTopology.CapProduct.RestrictionNbhd

/-!
# The cap product commutes with the Mayer–Vietoris connecting maps

Let `A`, `B` be open subsets of a Hausdorff space `Y`, `I = A ⊓ B`, and `S`, `T` disjoint closed
sets with `Y - B ⊆ interior S`, `Y - A ⊆ interior T` (`exists_mvSeparation`). For a cochain `e`
of `Y` which is a cocycle on `A ∩ B` (of degree `p`) and a locally finite `(p + q + 1)`-cycle `μ`
of `Y`, the homology Mayer–Vietoris connecting chain (`IsMVConn`) of `e|_I ∩ μ|_I` is homologous
to `(-1) ^ (q + 1) (δ_MV e ∩ μ)`, where `δ_MV = mvCoboundary` is the cohomology Mayer–Vietoris
coboundary (`IsMVConn.exists_sub_capChain_mvCoboundary_eq_d`).

Proof. Subdivide `μ = μ₁ + μ₂ + ∂ E` with `μ₁` supported off `interior S` (so in `B`) and `μ₂`
off `interior T` (so in `A`). Then `∂ μ₁ = -∂ μ₂` is supported in `F = (interior S)ᶜ ∩
(interior T)ᶜ ⊆ A ∩ B`.

* On `I`: `e|_I ∩ μ|_I = e|_I ∩ μ₁|_I + e|_I ∩ μ₂|_I + ∂(e|_I ∩ E|_I)` (Leibniz, `e|_I` a
  cocycle), so `e ∩ ∂ μ₁`, a chain of `Y` supported in `F`, whose restriction to `I` is
  `∂(e|_I ∩ μ₁|_I)` (the cap product commutes with the literal restriction of chains supported in
  `I`, `restrictChainMap_capChain_of_isSupportedIn`), is a connecting chain.
* On `Y`: `δ_MV e` vanishes on the simplices of `B` and agrees with `δ e_I` on those of `A`
  (`e_I = e` on the simplices of `A ∩ B`, `0` elsewhere), and a cochain vanishing on the simplices
  of `N` caps to `0` with a chain supported in `N` (`capChain_eq_zero_of_mem_vanishing`). So
  `δ_MV e ∩ μ ~ δ e_I ∩ μ₂ ~ (-1) ^ q e_I ∩ ∂ μ₂ = -(-1) ^ q (e ∩ ∂ μ₁)` (Leibniz,
  `φ ∩ ∂ c = ∂ (φ ∩ c) + (-1) ^ q δ φ ∩ c`).
## Main results

* `MMP.BorelMooreCap.isSupportedIn_capChain`
* `MMP.BorelMooreCap.capChain_eq_zero_of_mem_vanishing`
* `MMP.BorelMooreCap.restrictChainMap_capChain_of_isSupportedIn`
* `MMP.borelMooreHomology.IsMVConn.exists_sub_capChain_mvCoboundary_eq_d`

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.3, proof of Lemma 3.36.
* [G. Bredon, *Topology and Geometry*][bredon1993], VI.8.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology Opposite Topology Set Simplicial

universe u

namespace MMP

open MMP

namespace BorelMooreCap

open SingularChain SingularCochain LocallyFiniteChain BorelMooreCross borelMooreHomology
  SingularCross

variable {R : Type u} [CommRing R] {Y : TopCat.{u}}

/-- The cap product `φ ∩ c` is supported wherever `c` is. -/
lemma isSupportedIn_capChain {N : Set Y} (p q n : ℕ) (h : p + q = n) (φ : Simplex Y p → R)
    {c : (BM R Y).X n} (hc : IsSupportedIn R (ModuleCat.of R R) N c) :
    IsSupportedIn R (ModuleCat.of R R) N (capChain R p q n h φ c) := by
  classical
  intro τ hτ
  have h1 : pushforwardFun (opS (front q n (by omega)))
      (fun σ ↦ wt φ (back p n q (by omega)) σ * coeff R c σ) τ ≠ 0 := hτ
  obtain ⟨σ, hσ⟩ : ∃ σ, (if opS (front q n (by omega)) σ = τ then
      wt φ (back p n q (by omega)) σ * coeff R c σ else 0) ≠ 0 := by
    by_contra h2
    push Not at h2
    exact h1 (finsum_eq_zero_of_forall_eq_zero h2)
  split_ifs at hσ with hστ
  · subst hστ
    exact (image_opS_subset _ σ).trans (hc σ (right_ne_zero_of_mul hσ))
  · exact absurd rfl hσ

/-- A cochain vanishing on the simplices of `N` caps to `0` with a chain supported in `N`. -/
lemma capChain_eq_zero_of_mem_vanishing {N : Set Y} (p q n : ℕ) (h : p + q = n)
    {φ : Simplex Y p → R} (hφ : φ ∈ vanishing R p N) {c : (BM R Y).X n}
    (hc : IsSupportedIn R (ModuleCat.of R R) N c) : capChain R p q n h φ c = 0 := by
  rw [capChain_apply]
  have hW : W R (wt φ (back p n q (by omega))) c = 0 := by
    apply coeff_injective R
    funext σ
    rw [coeff_W, coeff_zero]
    by_cases h0 : coeff R c σ = 0
    · simp [h0]
    · have h2 : wt φ (back p n q (by omega)) σ = 0 :=
        hφ _ ((range_comp_smap_subset _ _).trans ((range_simplexEquiv σ).le.trans (hc σ h0)))
      simp [h2]
  rw [hW, map_zero]

/-- Two cochains agreeing on the simplices of `N` cap to the same chain with a chain supported in
`N`. -/
lemma capChain_congr_of_sub_mem_vanishing {N : Set Y} (p q n : ℕ) (h : p + q = n)
    {φ ψ : Simplex Y p → R} (hφ : φ - ψ ∈ vanishing R p N) {c : (BM R Y).X n}
    (hc : IsSupportedIn R (ModuleCat.of R R) N c) :
    capChain R p q n h φ c = capChain R p q n h ψ c := by
  have := capChain_eq_zero_of_mem_vanishing p q n h hφ hc
  rwa [map_sub, LinearMap.sub_apply, sub_eq_zero] at this

variable [T2Space Y]

/-- **The cap product commutes with the restriction of a chain supported in an open set.** -/
lemma restrictChainMap_capChain_of_isSupportedIn (U : TopologicalSpace.Opens Y) (p q n : ℕ)
    (h : p + q = n) (φ : Simplex Y p → R) {z : (BM R Y).X n}
    (hz : IsSupportedIn R (ModuleCat.of R R) (U : Set Y) z) :
    ((restrictChainMap R (ModuleCat.of R R) U).f q).hom (capChain R p q n h φ z) =
      capChain R p q n h (cochainPullback R (inclHom U) p φ)
        (((restrictChainMap R (ModuleCat.of R R) U).f n).hom z) := by
  classical
  apply coeff_injective R
  funext ν
  rw [coeff_restrictChainMap_capChain, coeff_capChain_restrictChainMap]
  refine finsum_congr fun σ ↦ ?_
  by_cases h0 : coeff R z σ = 0
  · simp [h0]
  congr 1
  have hσ : range (SingularCochain.simplexEquiv Y _ σ) ⊆ (U : Set Y) :=
    (range_simplexEquiv σ).le.trans (hz σ h0)
  rw [capRestrCoeff, SingularChain.restrFin_of_mem_inside
    (capFin_mem_inside p q n h φ (Finsupp.single_mem_supported R _ hσ)),
    finsum_eq_single _ (SingularCochain.simplexEquiv Y _ σ)]
  · rw [borelMooreHomology.restrCoeff_of_range_subset hσ, Finsupp.single_eq_same, one_mul]
  · intro τ hτ
    rw [borelMooreHomology.restrCoeff_of_range_subset hσ, Finsupp.single_eq_of_ne hτ, zero_mul]

end BorelMooreCap

namespace borelMooreHomology

open BorelMooreCap SingularChain SingularCochain LocallyFiniteChain BorelMooreCross SingularCross

variable {R : Type u} [CommRing R] {Y : TopCat.{u}} [T2Space Y]
  {A B : TopologicalSpace.Opens Y} {S T : Set Y}

/-- An integer multiple of a locally finite chain supported in `N` is supported in `N`. -/
lemma isSupportedIn_zsmul {P : TopCat.{u}} {N : Set P} {n : ℕ} {c : (BM R P).X n}
    (hc : IsSupportedIn R (ModuleCat.of R R) N c) (k : ℤ) :
    IsSupportedIn R (ModuleCat.of R R) N (k • c) := by
  rw [← Int.cast_smul_eq_zsmul R]
  exact hc.smul _

/-- **The cap product commutes, up to the sign `(-1) ^ (q + 1)`, with the Mayer–Vietoris
connecting maps.** Let `e` be a `p`-cochain of `Y` which is a cocycle on `A ∩ B`, and `μ` a
locally finite `(p + q + 1)`-cycle of `Y`. Every Mayer–Vietoris connecting chain `c` of
`e|_{A ∩ B} ∩ μ|_{A ∩ B}` is homologous to `(-1) ^ (q + 1) (δ_MV e ∩ μ)`, where
`δ_MV = mvCoboundary` is the cohomology Mayer–Vietoris coboundary. -/
theorem IsMVConn.exists_sub_capChain_mvCoboundary_eq_d (hS : IsClosed S) (hT : IsClosed T)
    (hST : Disjoint S T) (hBS : (B : Set Y)ᶜ ⊆ interior S) (hAT : (A : Set Y)ᶜ ⊆ interior T)
    {p q : ℕ} {e : Simplex Y p → R}
    (he : coboundary R p e ∈ vanishing R (p + 1) ((A : Set Y) ∩ B))
    (μ : (BM R Y).X (p + q + 1)) (hμ : ((BM R Y).d (p + q + 1) (p + q)).hom μ = 0)
    {c : (BM R Y).X q}
    (hc : IsMVConn R (ModuleCat.of R R) (A ⊓ B) S T
      (capChain R p (q + 1) (p + q + 1) (by omega) (cochainPullback R (inclHom (A ⊓ B)) p e)
        (((restrictChainMap R (ModuleCat.of R R) (A ⊓ B)).f (p + q + 1)).hom μ)) c) :
    ∃ v : (BM R Y).X (q + 1), c - (-1 : ℤ) ^ (q + 1) •
        capChain R (p + 1) q (p + q + 1) (by omega) (mvCoboundary R (A : Set Y) B p e) μ =
      ((BM R Y).d (q + 1) q).hom v := by
  set M := ModuleCat.of R R
  set I := A ⊓ B
  have hSB : (interior S)ᶜ ⊆ (B : Set Y) := fun y hy ↦ by
    by_contra hyB
    exact hy (hBS hyB)
  have hTA : (interior T)ᶜ ⊆ (A : Set Y) := fun y hy ↦ by
    by_contra hyA
    exact hy (hAT hyA)
  have hFAB : (interior S)ᶜ ∩ (interior T)ᶜ ⊆ (A : Set Y) ∩ B := fun x hx ↦ ⟨hTA hx.2, hSB hx.1⟩
  have hFI : (interior S)ᶜ ∩ (interior T)ᶜ ⊆ (I : Set Y) := hFAB
  have hAB : (A : Set Y) ∪ B = univ := by
    ext x
    simp only [mem_union, mem_univ, iff_true]
    by_contra h
    push Not at h
    exact Set.disjoint_left.1 hST (interior_subset (hBS h.2)) (interior_subset (hAT h.1))
  have hSi : Sᶜ ⊆ (interior S)ᶜ := compl_subset_compl.2 interior_subset
  have hTi : Tᶜ ⊆ (interior T)ᶜ := compl_subset_compl.2 interior_subset
  have hcov : Tᶜ ∪ Sᶜ = univ := by
    ext x
    simp only [mem_union, mem_compl_iff, mem_univ, iff_true]
    by_contra h
    push Not at h
    exact Set.disjoint_left.1 hST h.2 h.1
  -- subdivide `μ` for the cover `{Y - S, Y - T}`
  set 𝒱 : Set (Set Y) := {Sᶜ, Tᶜ}
  set s : Set ((TopCat.toSSet.obj Y).obj (op ⦋p + q + 1⦌)) := {τ | singularSimplexImage Y τ ⊆ Sᶜ}
  set μ₁ := (chainPart R M s).hom (((smallChainMapLF R M 𝒱).f (p + q + 1)).hom μ)
  set μ₂ := (chainPart R M sᶜ).hom (((smallChainMapLF R M 𝒱).f (p + q + 1)).hom μ)
  have hsplit : μ₁ + μ₂ = ((smallChainMapLF R M 𝒱).f (p + q + 1)).hom μ :=
    chainPart_add_chainPart_compl R M s _
  have hρ := sub_smallChainMapLF_eq_d_of_cycle R M 𝒱 μ (fun m hm ↦ by
    obtain rfl : m = p + q := by omega
    exact hμ)
  have hμ₁ : IsSupportedIn R M (interior S)ᶜ μ₁ := fun τ hτ ↦
    (isSupportedIn_chainPart _ τ hτ).trans hSi
  have hμ₂ : IsSupportedIn R M (interior T)ᶜ μ₂ := by
    intro τ hτ
    obtain ⟨hτ', hΨτ⟩ := mem_of_chainPart_ne_zero hτ
    rcases smallChainMapLF_small_of_union R M hS.isOpen_compl hT.isOpen_compl
        (by rw [union_comm]; exact hcov) (p + q + 1) μ hΨτ with h | h
    · exact absurd h hτ'
    · exact h.trans hTi
  set E := (smallHomotopyMap R M 𝒱 (p + q + 1)).hom μ
  have hμE : μ = μ₁ + μ₂ + ((BM R Y).d (p + q + 1 + 1) (p + q + 1)).hom E := by
    rw [hsplit, ← hρ]
    abel
  have hd12 : ((BM R Y).d (p + q + 1) (p + q)).hom μ₂ =
      -((BM R Y).d (p + q + 1) (p + q)).hom μ₁ := by
    have := congrArg ((BM R Y).d (p + q + 1) (p + q)).hom hμE
    rw [hμ, map_add, map_add, d_d_apply, add_zero] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  have hdF : IsSupportedIn R M ((interior S)ᶜ ∩ (interior T)ᶜ)
      (((BM R Y).d (p + q + 1) (p + q)).hom μ₁) := by
    refine IsSupportedIn.inter hμ₁.d_of ?_
    have h2 := (hμ₂.d_of (j := p + q)).neg
    rwa [hd12, neg_neg] at h2
  -- the side of `I`
  set r : ∀ k, (BM R Y).X k →ₗ[R] (BM R (TopCat.of I)).X k :=
    fun k ↦ ((restrictChainMap R M I).f k).hom
  set e' := cochainPullback R (inclHom I) p e
  have he' : coboundary R p e' = 0 := coboundary_cochainPullback_eq_zero ((A : Set Y) ∩ B) he
  set c₀ : (BM R Y).X q :=
    capChain R p q (p + q) rfl e (((BM R Y).d (p + q + 1) (p + q)).hom μ₁)
  have hc₀ : IsMVConn R M I S T
      (capChain R p (q + 1) (p + q + 1) (by omega) e' (r (p + q + 1) μ)) c₀ := by
    refine ⟨capChain R p (q + 1) (p + q + 1) (by omega) e' (r (p + q + 1) μ₁),
      capChain R p (q + 1) (p + q + 1) (by omega) e' (r (p + q + 1) μ₂),
      capChain R p (q + 1 + 1) (p + q + 1 + 1) (by omega) e' (r _ E), ?_,
      isSupportedIn_capChain _ _ _ _ _ (isSupportedIn_restrictChainMap R hμ₁),
      isSupportedIn_capChain _ _ _ _ _ (isSupportedIn_restrictChainMap R hμ₂),
      isSupportedIn_capChain _ _ _ _ _ (hdF.mono hFI), ?_⟩
    · have h1 := capChain_d (Y := TopCat.of I) p (q + 1) (p + q + 1) (by omega) e' (r _ E)
      rw [he', map_zero, LinearMap.zero_apply, smul_zero, add_zero] at h1
      have h2 : r (p + q + 1) (((BM R Y).d (p + q + 1 + 1) (p + q + 1)).hom E) =
          ((BM R (TopCat.of I)).d (p + q + 1 + 1) (p + q + 1)).hom (r _ E) :=
        hom_f_d_apply _ _ _ E
      conv_lhs => rw [hμE, map_add, map_add, h2, map_add, map_add, h1]
    · have h1 := capChain_d (Y := TopCat.of I) p q (p + q) rfl e' (r _ μ₁)
      rw [he', map_zero, LinearMap.zero_apply, smul_zero, add_zero] at h1
      have h2 : r (p + q) (((BM R Y).d (p + q + 1) (p + q)).hom μ₁) =
          ((BM R (TopCat.of I)).d (p + q + 1) (p + q)).hom (r _ μ₁) :=
        hom_f_d_apply _ _ _ μ₁
      change r q c₀ = _
      rw [restrictChainMap_capChain_of_isSupportedIn I p q (p + q) rfl e (hdF.mono hFI)]
      change capChain R p q (p + q) rfl e' (r (p + q) _) = _
      rw [h2, h1]
  obtain ⟨v₁, hv₁⟩ := IsMVConn.exists_sub_eq_d hS hT hST hFI hc hc₀ 0 (by rw [sub_self, map_zero])
  -- the side of `Y`
  set K := mvCoboundary R (A : Set Y) B p e
  set κ := mvKappa R (A : Set Y) B p e
  set eI := restrictTo R ((A : Set Y) ∩ B) p e
  have hKB : K ∈ vanishing R (p + 1) (B : Set Y) := by
    have h1 := (pullback_smallChainMap_sub_mem (A := (A : Set Y)) (B := (B : Set Y)) κ).2
    have h2 := mvKappa_mem_vanishing_right (A := (A : Set Y)) (B := (B : Set Y)) he
    have := Submodule.add_mem _ h1 h2
    rwa [sub_add_cancel] at this
  have hKA : K - coboundary R p eI ∈ vanishing R (p + 1) (A : Set Y) := by
    have h1 := (pullback_smallChainMap_sub_mem (A := (A : Set Y)) (B := (B : Set Y)) κ).1
    have h2 := mvKappa_sub_mem_vanishing (A := (A : Set Y)) (B := (B : Set Y)) e
    have := Submodule.add_mem _ h1 h2
    rwa [sub_add_sub_cancel] at this
  have hY1 : capChain R (p + 1) q (p + q + 1) (by omega) K μ₁ = 0 :=
    capChain_eq_zero_of_mem_vanishing _ _ _ _ hKB (hμ₁.mono hSB)
  have hY2 : capChain R (p + 1) q (p + q + 1) (by omega) K μ₂ =
      capChain R (p + 1) q (p + q + 1) (by omega) (coboundary R p eI) μ₂ :=
    capChain_congr_of_sub_mem_vanishing _ _ _ _ hKA (hμ₂.mono hTA)
  have hY3 := capChain_d p q (p + q) rfl eI μ₂
  have hY4 : capChain R p q (p + q) rfl eI (((BM R Y).d (p + q + 1) (p + q)).hom μ₂) =
      -capChain R p q (p + q) rfl e (((BM R Y).d (p + q + 1) (p + q)).hom μ₁) := by
    rw [capChain_congr_of_sub_mem_vanishing _ _ _ _ (restrictTo_sub_mem_vanishing _ e)
      (by rw [hd12]; exact (hdF.mono hFAB).neg), hd12, map_neg]
  have hY5 := capChain_d (p + 1) q (p + q + 1) (by omega) K E
  rw [coboundary_mvCoboundary (A := (A : Set Y)) (B := (B : Set Y)) A.isOpen B.isOpen hAB he,
    map_zero, LinearMap.zero_apply, smul_zero, add_zero] at hY5
  set X₂ := capChain R p (q + 1) (p + q + 1) (by omega) eI μ₂
  set X₃ := capChain R (p + 1) (q + 1) (p + q + 1 + 1) (by omega) K E
  have hss : ∀ x : (BM R Y).X q, (-1 : ℤ) ^ q • (-1 : ℤ) ^ q • x = x := fun x ↦ by
    rw [smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
  have hY3' : capChain R (p + 1) q (p + q + 1) (by omega) (coboundary R p eI) μ₂ =
      (-1 : ℤ) ^ q • (capChain R p q (p + q) rfl eI (((BM R Y).d (p + q + 1) (p + q)).hom μ₂) -
        ((BM R Y).d (q + 1) q).hom X₂) := by
    rw [hY3, add_sub_cancel_left, hss]
  refine ⟨v₁ - X₂ - (-1 : ℤ) ^ (q + 1) • X₃, ?_⟩
  have hYμ : capChain R (p + 1) q (p + q + 1) (by omega) K μ =
      (-1 : ℤ) ^ q • (-capChain R p q (p + q) rfl e (((BM R Y).d (p + q + 1) (p + q)).hom μ₁) -
        ((BM R Y).d (q + 1) q).hom X₂) + ((BM R Y).d (q + 1) q).hom X₃ := by
    conv_lhs => rw [hμE, map_add, map_add, hY1, hY2, hY5]
    rw [hY3', hY4, zero_add]
  rw [hYμ, map_sub, map_sub, ← hv₁, map_zsmul, pow_succ, mul_neg_one, neg_smul, neg_smul,
    smul_add, hss]
  simp only [c₀, smul_sub, smul_neg, hss]
  abel

end borelMooreHomology

end MMP
