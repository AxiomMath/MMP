module

public import MMP.AlgebraicTopology.BorelMoore.Connecting
public import MMP.AlgebraicTopology.PoincareDuality.EmbeddingIndependence.CapConnecting
public import MMP.AlgebraicTopology.SingularCohomology.PairSequence.Supports
public import MMP.AlgebraicTopology.BorelMoore.MayerVietorisExact
public import MMP.AlgebraicTopology.CapProduct.SupportRetraction
public import MMP.AlgebraicTopology.CapProduct.ExteriorProduct

/-!
# The cap product and the connecting maps of the pair `(Y, Y - X)`

For a closed subset `X` of a Hausdorff space `Y` with `U = Y - X`, a closed neighbourhood `N` of
`X` deformed into `X` by a proper homotopy `G` fixing `X`, a `p`-cocycle `ψ` of `U` extending to
a cochain `χ` of `Y`, and a locally finite `n`-cycle `z` of `Y`, `n = p + k + 1`: the
Borel–Moore connecting map `∂ : H_{k+1} U → H_k X` sends `[ψ ∩ z|_U]` to `(-1) ^ (k + 1)` times
`G(·, 1)_* [(δ χ ∩ ρ z)|_N]`, `ρ` the subdivision towards `{U, int N}`; that is, up to sign, the
cap product with supports of `δ [ψ] ∈ H^{p+1}(Y, U)` and `[z]`.

Proof (Hatcher 3.36, Bredon VI.8). Split `ρ z = z₁ + z₂`, `z₂` the simplices inside `int N`, so
`z₁` lies in `U`. As `δ χ` vanishes on the simplices of `U`, `b = χ ∩ z₁` has
`∂ b = χ ∩ ∂ z₁ =: β`, supported in the closed union `B ⊆ N - X` of the simplices of `∂ z₁`. On
`U`, `ψ ∩ z₂|_U = ∂ H c - H β` (the deformation operator, `c` the restriction of `χ ∩ z₂` to
`N - X`), so `connecting_homologyEquiv_symm_mk_of_fill` gives `∂ [ψ ∩ z|_U] = [G(·, 1)_* β]`. On
`N`, `δ χ ∩ ρ z = δ χ ∩ z₂ = (-1) ^ k (χ ∩ ∂ z₂ - ∂ (χ ∩ z₂))` and `χ ∩ ∂ z₂ = -β`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology Opposite Topology Set Simplicial

universe u

namespace MMP

open MMP

namespace borelMooreHomology

open MMP.borelMooreHomology

open BorelMooreCap SingularChain SingularCochain LocallyFiniteChain BorelMooreCross SingularCross

variable {R : Type u} [CommRing R] {Y : TopCat.{u}}

/-- The union of the simplices of a locally finite chain is closed. -/
lemma isClosed_iUnion_singularSimplexImage [T2Space Y] {n : ℕ} (c : (BM R Y).X n) :
    IsClosed (⋃ σ ∈ Function.support c.1, singularSimplexImage Y σ) := by
  have hc : IsLocallyFiniteSet (singularSimplexImage Y) (Function.support c.1) := c.2
  have hlf : LocallyFinite fun σ : Function.support c.1 ↦ singularSimplexImage Y σ.1 :=
    fun x ↦ by
      obtain ⟨V, hV, hfin⟩ := hc x
      exact ⟨V, hV, hfin.preimage Subtype.val_injective.injOn |>.subset fun σ hσ ↦ ⟨σ.2, hσ⟩⟩
  rw [biUnion_eq_iUnion]
  exact hlf.isClosed_iUnion fun σ ↦ (isCompact_singularSimplexImage σ.1).isClosed

/-- A locally finite chain is supported in the union of its simplices. -/
lemma isSupportedIn_iUnion_singularSimplexImage {n : ℕ} (c : (BM R Y).X n) :
    IsSupportedIn R (ModuleCat.of R R) (⋃ σ ∈ Function.support c.1, singularSimplexImage Y σ)
      c :=
  fun _ hσ ↦ subset_biUnion_of_mem (u := fun σ ↦ singularSimplexImage Y σ) hσ

/-- The union of the simplices of a locally finite chain supported in `N` is contained in `N`. -/
lemma iUnion_singularSimplexImage_subset {n : ℕ} {c : (BM R Y).X n} {N : Set Y}
    (hc : IsSupportedIn R (ModuleCat.of R R) N c) :
    (⋃ σ ∈ Function.support c.1, singularSimplexImage Y σ) ⊆ N :=
  iUnion₂_subset fun σ hσ ↦ hc σ hσ

/-- **Leibniz off the support of `δ χ`.** If `δ χ` vanishes on the simplices of `A` and `c` is
supported in `A`, then `∂ (χ ∩ c) = χ ∩ ∂ c`. -/
lemma d_capChain_of_isSupportedIn {A : Set Y} (p q : ℕ) {χ : Simplex Y p → R}
    (hχ : coboundary R p χ ∈ vanishing R (p + 1) A) {c : (BM R Y).X (p + q + 1)}
    (hc : IsSupportedIn R (ModuleCat.of R R) A c) :
    ((BM R Y).d (q + 1) q).hom (capChain R p (q + 1) (p + q + 1) (by omega) χ c) =
      capChain R p q (p + q) rfl χ (((BM R Y).d (p + q + 1) (p + q)).hom c) := by
  rw [capChain_d p q (p + q) rfl χ c,
    capChain_eq_zero_of_mem_vanishing (p + 1) q (p + q + 1) _ hχ hc, smul_zero, add_zero]

section connecting

variable [T2Space Y] {X : Set Y} (hX : IsClosed X)

omit [T2Space Y] in
/-- The pull-back of a cochain whose coboundary vanishes on the simplices of `U = Y - X` is a
cocycle of `U`. -/
lemma coboundary_cochainPullback_inclHom_eq_zero {p : ℕ} {χ : Simplex Y p → R}
    (hχ : coboundary R p χ ∈ vanishing R (p + 1) Xᶜ) :
    coboundary R p (cochainPullback R (inclHom (complOpens hX)) p χ) = 0 := by
  rw [coboundary_cochainPullback]
  funext τ
  exact hχ _ (by rintro _ ⟨t, rfl⟩; exact (τ t).2)

variable {N : Set Y} {B : Set Y} (hB : IsClosed B) (hBN : B ⊆ N) (hBX : B ⊆ Xᶜ)

/-- A chain of `B ⊆ N - X` pushed into `A = N - X` and then into `U = Y - X` is its push-forward
to `Y`, restricted to `U`. -/
lemma chainMap_deformDomain_chainMap_fillIncl (hN : IsClosed N) {k : ℕ}
    (β : (BM R (TopCat.of B)).X k) :
    ((chainMap R (ModuleCat.of R R) (borelMooreHomology.subsetInclusion (deformDomain hX N))
        (isProperMap_deformDomainInclusion hX hN)).f k).hom
      (((chainMap R (ModuleCat.of R R) (fillIncl hX hBN hBX)
        (isProperMap_fillIncl hX hB hBN hBX)).f k).hom β) =
    ((restrictChainMap R (ModuleCat.of R R) (complOpens hX)).f k).hom
      (((chainMap R (ModuleCat.of R R) (borelMooreHomology.subsetInclusion B)
        (isProperMap_subsetInclusion hB)).f k).hom β) := by
  have hsupp : IsSupportedIn R (ModuleCat.of R R) ((complOpens hX : Set Y))
      (((chainMap R (ModuleCat.of R R) (borelMooreHomology.subsetInclusion B)
        (isProperMap_subsetInclusion hB)).f k).hom β) :=
    IsSupportedIn.chainMap _ _ (N := univ) (by rintro _ ⟨y, -, rfl⟩; exact hBX y.2)
      (fun _ _ ↦ subset_univ _)
  apply Subtype.ext
  funext τ
  rw [restrictChainMap_apply_of_isSupportedIn R _ _ hsupp τ]
  have hcomp := congrArg (fun φ ↦ (φ.f k).hom β)
    (chainMap_comp R (ModuleCat.of R R) (fillIncl hX hBN hBX)
      (borelMooreHomology.subsetInclusion (deformDomain hX N))
      (isProperMap_fillIncl hX hB hBN hBX) (isProperMap_deformDomainInclusion hX hN))
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at hcomp
  rw [← hcomp, chainMap_f_apply_coe, chainMap_f_apply_coe]
  have hinj : Function.Injective
      ((TopCat.toSSet.map (clopenInclusion (complOpens hX))).app (op ⦋k⦌)) :=
    injective_toSSet_map_subspaceInclusion (Xᶜ) _
  have hfac : borelMooreHomology.subsetInclusion B =
      (fillIncl hX hBN hBX ≫ borelMooreHomology.subsetInclusion (deformDomain hX N)) ≫
        clopenInclusion (complOpens hX) := rfl
  rw [hfac, Functor.map_comp, NatTrans.comp_app]
  exact (pushforwardFun_comp_apply_of_injective hinj _ _).symm

variable {G : C(N × unitInterval, Y)} (hG : IsProperMap G)
  (hGX : ∀ y : N, ∀ t, (y : Y) ∈ X → G (y, t) = y) (hG0 : ∀ y, G (y, 0) = y)
  (hG1 : ∀ y, G (y, 1) ∈ X)

include hBX hGX in
/-- **The connecting map of a cap product, on chains.** Let `χ` be a `p`-cochain of `Y` whose
coboundary vanishes on the simplices of `U = Y - X`, and `z₁ + z₂` a locally finite
`(p + k + 1)`-cycle of `Y` with `z₁` supported in `U` and `z₂` in `N`. If `β` is a `k`-cycle of
a closed `B ⊆ N - X` pushing forward to `χ ∩ ∂ z₁`, then the connecting map sends the class of
`ψ ∩ (z₁ + z₂)|_U` (`ψ = χ|_U`) to the class of `G(·, 1)_* β`. -/
theorem connecting_homologyEquiv_symm_mk_capChain (h : IsRelativeQuasiIso R (ModuleCat.of R R) hX)
    (hN : IsClosed N) (p k : ℕ) {χ : Simplex Y p → R}
    (hχ : coboundary R p χ ∈ vanishing R (p + 1) Xᶜ) (z₁ z₂ : (BM R Y).X (p + k + 1))
    (hz₁ : IsSupportedIn R (ModuleCat.of R R) Xᶜ z₁)
    (hz₂ : IsSupportedIn R (ModuleCat.of R R) N z₂)
    (hz : ((BM R Y).d (p + k + 1) (p + k)).hom (z₁ + z₂) = 0)
    (β : Cyc (R := R) (TopCat.of B) k)
    (hβ : ((chainMap R (ModuleCat.of R R) (borelMooreHomology.subsetInclusion B)
      (isProperMap_subsetInclusion hB)).f k).hom β.1 =
        capChain R p k (p + k) rfl χ (((BM R Y).d (p + k + 1) (p + k)).hom z₁))
    (w : Cyc (R := R) (TopCat.of (complOpens hX)) (k + 1))
    (hw : w.1 = capChain R p (k + 1) (p + k + 1) (by omega)
      (cochainPullback R (inclHom (complOpens hX)) p χ)
      (((restrictChainMap R (ModuleCat.of R R) (complOpens hX)).f (p + k + 1)).hom (z₁ + z₂))) :
    (connecting R (ModuleCat.of R R) hX h k).hom
        ((homologyEquiv R (TopCat.of (complOpens hX)) (k + 1)).symm (Submodule.Quotient.mk w)) =
      (homologyEquiv R (TopCat.of X) k).symm (Submodule.Quotient.mk
        ⟨((chainMap R (ModuleCat.of R R) (fillEnd hBN hG1)
          (isProperMap_fillEnd hG hB hBN hG0 hG1)).f k).hom β.1,
          chainMap_mem_cyc R _ β⟩) := by
  set ψ := cochainPullback R (inclHom (complOpens hX)) p χ
  set ρU := restrictChainMap R (ModuleCat.of R R) (complOpens hX)
  have hD : IsClosed (deformDomain hX N) := hN.preimage continuous_subtype_val
  set c' := capChain R p (k + 1) (p + k + 1) (by omega) ψ ((ρU.f (p + k + 1)).hom z₂)
  have hc' : IsSupportedIn R (ModuleCat.of R R) (deformDomain hX N) c' :=
    isSupportedIn_capChain _ _ _ _ _ (hz₂.restrictChainMap _)
  set c := (subsetRestrictMap R (ModuleCat.of R R) (deformDomain hX N) (k + 1)).hom c'
  have hιc : ((chainMap R _ (borelMooreHomology.subsetInclusion (deformDomain hX N))
      (isProperMap_deformDomainInclusion hX hN)).f (k + 1)).hom c = c' :=
    chainMap_subsetRestrictMap R _ hD hc'
  have hψ : coboundary R p ψ ∈ vanishing R (p + 1) (univ : Set (TopCat.of (complOpens hX))) := by
    rw [coboundary_cochainPullback_inclHom_eq_zero hX hχ]
    exact zero_mem _
  have hdc : ((BM R (TopCat.of (deformDomain hX N))).d (k + 1) k).hom c =
      -((chainMap R _ (fillIncl hX hBN hBX) (isProperMap_fillIncl hX hB hBN hBX)).f k).hom β.1 := by
    apply chainMap_subsetInclusion_injective R (ModuleCat.of R R) hD k
    rw [map_neg, chainMap_deformDomain_chainMap_fillIncl hX hB hBN hBX hN, hβ]
    have hcomm := ConcreteCategory.congr_hom ((chainMap R (ModuleCat.of R R)
      (borelMooreHomology.subsetInclusion (deformDomain hX N))
        (isProperMap_subsetInclusion hD)).comm (k + 1) k) c
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
    rw [← hcomm, hιc, d_capChain_of_isSupportedIn (A := univ) p k hψ (fun _ _ ↦ subset_univ _)]
    have hρ := ConcreteCategory.congr_hom (ρU.comm (p + k + 1) (p + k)) z₂
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hρ
    have hz₂' : ((BM R Y).d (p + k + 1) (p + k)).hom z₂ =
        -((BM R Y).d (p + k + 1) (p + k)).hom z₁ := by
      rw [map_add] at hz
      exact eq_neg_of_add_eq_zero_right hz
    rw [hρ, hz₂', map_neg, map_neg,
      restrictChainMap_capChain_of_isSupportedIn (complOpens hX) p k (p + k) rfl χ hz₁.d]
  refine connecting_homologyEquiv_symm_mk_of_fill hG hGX hG0 hG1 hB hBN hBX h k w
    (capChain R p (k + 1) (p + k + 1) (by omega) χ z₁) β ?_
    (-(deformOp R (ModuleCat.of R R) hX hG hGX (k + 1)).hom c) ?_
  · rw [hβ, d_capChain_of_isSupportedIn p k hχ hz₁]
  · have hH := chainMap_deformDomain_eq_succ R (ModuleCat.of R R) hX hG hGX hN hG0 hG1 k c
    rw [hιc, hdc, map_neg] at hH
    rw [restrictChainMap_capChain_of_isSupportedIn (complOpens hX) p (k + 1) (p + k + 1) _ χ hz₁,
      hw, map_add, map_add]
    change capChain R p (k + 1) (p + k + 1) _ ψ ((ρU.f (p + k + 1)).hom z₁) - _ -
      (capChain R p (k + 1) (p + k + 1) _ ψ ((ρU.f (p + k + 1)).hom z₁) + c') = _
    rw [hH, map_neg]
    abel

omit [T2Space Y] in
/-- **The neighbourhood cap product of a coboundary, on chains.** Let `χ` be a `p`-cochain of `Y`
whose coboundary vanishes on the simplices of `U = Y - X`, and `z₁ + z₂` a locally finite
`(p + k + 1)`-cycle with `z₁` supported in `U` and `z₂` in `N`. If `β` is a `k`-cycle of a closed
`B ⊆ N` pushing forward to `χ ∩ ∂ z₁`, the class of the cycle `(δ χ ∩ (z₁ + z₂))|_N` of `N` is
`-(-1) ^ k` times that of `β` pushed into `N`. -/
theorem mk_subsetRestrictMap_capChain_coboundary (hN : IsClosed N)
    (p k : ℕ) {χ : Simplex Y p → R} (hχ : coboundary R p χ ∈ vanishing R (p + 1) Xᶜ)
    (z₁ z₂ : (BM R Y).X (p + k + 1)) (hz₁ : IsSupportedIn R (ModuleCat.of R R) Xᶜ z₁)
    (hz₂ : IsSupportedIn R (ModuleCat.of R R) N z₂)
    (hz : ((BM R Y).d (p + k + 1) (p + k)).hom (z₁ + z₂) = 0)
    (β : Cyc (R := R) (TopCat.of B) k)
    (hβ : ((chainMap R (ModuleCat.of R R) (borelMooreHomology.subsetInclusion B)
      (isProperMap_subsetInclusion hB)).f k).hom β.1 =
        capChain R p k (p + k) rfl χ (((BM R Y).d (p + k + 1) (p + k)).hom z₁))
    (w : Cyc (R := R) (TopCat.of N) k)
    (hw : w.1 = (subsetRestrictMap R (ModuleCat.of R R) N k).hom
      (capChain R (p + 1) k (p + k + 1) (by omega) (coboundary R p χ) (z₁ + z₂))) :
    (Submodule.Quotient.mk w : HomQ (R := R) (TopCat.of N) k) =
      (-(-1 : ℤ) ^ k) • Submodule.Quotient.mk
        ⟨((chainMap R (ModuleCat.of R R) (subsetInclusionOfSubset hBN)
          (isProperMap_subsetInclusionOfSubset hB hBN)).f k).hom β.1,
          chainMap_mem_cyc R _ β⟩ := by
  set s : ℤ := -(-1 : ℤ) ^ k
  set T := capChain R (p + 1) k (p + k + 1) (by omega) (coboundary R p χ) z₂
  set A := capChain R p (k + 1) (p + k + 1) (by omega) χ z₂
  have hT : capChain R (p + 1) k (p + k + 1) (by omega) (coboundary R p χ) (z₁ + z₂) = T := by
    rw [map_add, capChain_eq_zero_of_mem_vanishing (p + 1) k (p + k + 1) _ hχ hz₁, zero_add]
  have hTN : IsSupportedIn R (ModuleCat.of R R) N T := isSupportedIn_capChain _ _ _ _ _ hz₂
  have hAN : IsSupportedIn R (ModuleCat.of R R) N A := isSupportedIn_capChain _ _ _ _ _ hz₂
  have hu : IsSupportedIn R (ModuleCat.of R R) N (s • A) :=
    borelMooreHomology.isSupportedIn_zsmul hAN s
  rw [← Submodule.Quotient.mk_smul]
  refine (Submodule.Quotient.eq _).2 ?_
  refine restrict_d_mem_bdry hN (s • A) hu _ ?_
  refine Eq.trans (b := w.1 - s • ((chainMap R (ModuleCat.of R R) (subsetInclusionOfSubset hBN)
    (isProperMap_subsetInclusionOfSubset hB hBN)).f k).hom β.1) rfl ?_
  apply chainMap_subsetInclusion_injective R (ModuleCat.of R R) hN k
  have hcomp := congrArg (fun φ ↦ (φ.f k).hom β.1)
    (chainMap_comp R (ModuleCat.of R R) (subsetInclusionOfSubset hBN)
      (borelMooreHomology.subsetInclusion N)
      (isProperMap_subsetInclusionOfSubset hB hBN) (isProperMap_subsetInclusion hN))
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at hcomp
  have hβ' : ((chainMap R (ModuleCat.of R R)
      (subsetInclusionOfSubset hBN ≫ borelMooreHomology.subsetInclusion N)
      ((isProperMap_subsetInclusion hN).comp (isProperMap_subsetInclusionOfSubset hB hBN))).f
        k).hom β.1 = capChain R p k (p + k) rfl χ (((BM R Y).d (p + k + 1) (p + k)).hom z₁) := hβ
  rw [map_sub, map_zsmul, hw, hT, chainMap_subsetRestrictMap R _ hN hTN, ← hcomp, hβ',
    chainMap_subsetRestrictMap R _ hN hu.d, map_zsmul]
  have e := capChain_d p k (p + k) rfl χ z₂
  have hz₂' : ((BM R Y).d (p + k + 1) (p + k)).hom z₂ =
      -((BM R Y).d (p + k + 1) (p + k)).hom z₁ := by
    rw [map_add] at hz
    exact eq_neg_of_add_eq_zero_right hz
  rw [hz₂', map_neg] at e
  rw [neg_eq_iff_eq_neg] at e
  change _ - s • capChain R p k (p + k) rfl χ _ = s • ((BM R Y).d (k + 1) k).hom A
  rw [e]
  simp only [s, neg_smul, smul_neg, smul_add, smul_smul]
  rw [neg_mul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, neg_smul, one_smul]
  abel

/-- **Splitting a cycle along `{U, int N}`.** A locally finite `(p + k + 1)`-cycle `z` of `Y` each
of whose simplices lies in `U = Y - X` or in `int N` is `z₁ + z₂` with `z₁` supported in `U` and
`z₂` in `N`; and for a `p`-cochain `χ` with `δ χ` vanishing on the simplices of `U`, `χ ∩ ∂ z₁`
is the push-forward of a `k`-cycle of a closed `B ⊆ N - X` (the union of the simplices of
`∂ z₁`). -/
theorem exists_split_capChain (p k : ℕ) {χ : Simplex Y p → R}
    (hχ : coboundary R p χ ∈ vanishing R (p + 1) Xᶜ) (z : (BM R Y).X (p + k + 1))
    (hz : ((BM R Y).d (p + k + 1) (p + k)).hom z = 0)
    (hcov : ∀ σ, z.1 σ ≠ 0 → singularSimplexImage Y σ ⊆ Xᶜ ∨
      singularSimplexImage Y σ ⊆ interior N) :
    ∃ z₁ z₂ : (BM R Y).X (p + k + 1), z₁ + z₂ = z ∧
      IsSupportedIn R (ModuleCat.of R R) Xᶜ z₁ ∧ IsSupportedIn R (ModuleCat.of R R) N z₂ ∧
      ∃ B : Set Y, ∃ hB : IsClosed B, ∃ hBN : B ⊆ N, B ⊆ Xᶜ ∧
        ∃ β : Cyc (R := R) (TopCat.of B) k,
          ((chainMap R (ModuleCat.of R R) (borelMooreHomology.subsetInclusion B)
            (isProperMap_subsetInclusion hB)).f k).hom β.1 =
            capChain R p k (p + k) rfl χ (((BM R Y).d (p + k + 1) (p + k)).hom z₁) := by
  set s := {σ | singularSimplexImage Y σ ⊆ interior N}
  set z₂ := (chainPart R (ModuleCat.of R R) s).hom z
  set z₁ := (chainPart R (ModuleCat.of R R) sᶜ).hom z
  have h12 : z₁ + z₂ = z := (add_comm _ _).trans (chainPart_add_chainPart_compl R _ s z)
  have hz₂ : IsSupportedIn R (ModuleCat.of R R) N z₂ :=
    (isSupportedIn_chainPart (N := interior N) z).mono interior_subset
  have hz₁ : IsSupportedIn R (ModuleCat.of R R) Xᶜ z₁ := by
    intro σ hσ
    rw [chainPart_apply_coe] at hσ
    have hσs : σ ∈ sᶜ := by
      by_contra h
      exact hσ (Set.indicator_of_notMem h _)
    rw [Set.indicator_of_mem hσs] at hσ
    exact (hcov σ hσ).resolve_right hσs
  have hd : ((BM R Y).d (p + k + 1) (p + k)).hom z₁ =
      -((BM R Y).d (p + k + 1) (p + k)).hom z₂ := by
    rw [← h12, map_add] at hz
    exact eq_neg_of_add_eq_zero_left hz
  set B := ⋃ σ ∈ Function.support (((BM R Y).d (p + k + 1) (p + k)).hom z₁).1,
    singularSimplexImage Y σ
  have hB : IsClosed B := isClosed_iUnion_singularSimplexImage _
  have hBN : B ⊆ N := iUnion_singularSimplexImage_subset (by rw [hd]; exact hz₂.d.neg)
  have hBX : B ⊆ Xᶜ := iUnion_singularSimplexImage_subset hz₁.d
  set βY := capChain R p k (p + k) rfl χ (((BM R Y).d (p + k + 1) (p + k)).hom z₁)
  have hβY : IsSupportedIn R (ModuleCat.of R R) B βY :=
    isSupportedIn_capChain _ _ _ _ _ (isSupportedIn_iUnion_singularSimplexImage _)
  have hcyc : (subsetRestrictMap R (ModuleCat.of R R) B k).hom βY ∈
      Cyc (R := R) (TopCat.of B) k := by
    rw [mem_cyc_iff]
    rcases k with _ | k
    · rw [show (0 : ℕ) - 1 = 0 from rfl, (BM R _).shape 0 0 (by simp)]
      rfl
    · change ((BM R (TopCat.of B)).d (k + 1) k).hom _ = 0
      rw [d_subsetRestrictMap R _ hB hβY]
      have e := d_capChain_of_isSupportedIn p (k + 1) hχ hz₁
      rw [show βY = ((BM R Y).d (k + 2) (k + 1)).hom
        (capChain R p (k + 2) (p + (k + 1) + 1) (by omega) χ z₁) from e.symm]
      have := ConcreteCategory.congr_hom ((BM R Y).d_comp_d (k + 2) (k + 1) k)
        (capChain R p (k + 2) (p + (k + 1) + 1) (by omega) χ z₁)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
      rw [this]
      exact map_zero _
  exact ⟨z₁, z₂, h12, hz₁, hz₂, B, hB, hBN, hBX, ⟨_, hcyc⟩,
    chainMap_subsetRestrictMap R _ hB hβY⟩

omit [T2Space Y] in
/-- A cochain with zero coboundary has coboundary vanishing on the simplices of the whole space. -/
lemma coboundary_mem_vanishing_univ_of_eq_zero {P : TopCat.{u}} {p : ℕ} {ψ : Simplex P p → R}
    (hψ : coboundary R p ψ = 0) : coboundary R p ψ ∈ vanishing R (p + 1) (univ : Set P) := by
  rw [hψ]
  exact zero_mem _

/-- **Subdividing before restricting does not change the class of a cap product.** For a cocycle
`ψ` of `U` and a locally finite `(p + k + 1)`-cycle `w` of `Y`, `ψ ∩ w|_U` and `ψ ∩ (ρ w)|_U`
(`ρ` the subdivision towards `{U, int N}`) are homologous. -/
lemma mk_capChain_restrict_nbhdSubdiv (p k : ℕ)
    {ψ : Simplex (TopCat.of (complOpens hX)) p → R} (hψ : coboundary R p ψ = 0)
    (w : (BM R Y).X (p + k + 1)) (hw : ((BM R Y).d (p + k + 1) (p + k)).hom w = 0)
    (u u' : Cyc (R := R) (TopCat.of (complOpens hX)) (k + 1))
    (hu : u.1 = capChain R p (k + 1) (p + k + 1) (by omega) ψ
      (((restrictChainMap R (ModuleCat.of R R) (complOpens hX)).f (p + k + 1)).hom w))
    (hu' : u'.1 = capChain R p (k + 1) (p + k + 1) (by omega) ψ
      (((restrictChainMap R (ModuleCat.of R R) (complOpens hX)).f (p + k + 1)).hom
        ((nbhdSubdiv R Xᶜ N (p + k + 1)).hom w))) :
    (Submodule.Quotient.mk u : HomQ (R := R) (TopCat.of (complOpens hX)) (k + 1)) =
      Submodule.Quotient.mk u' := by
  set ρU := restrictChainMap R (ModuleCat.of R R) (complOpens hX)
  set H := smallChainMapLFHomotopy R (ModuleCat.of R R) ({Xᶜ, interior N} : Set (Set Y))
  have hH := MMP.ChainHomotopyAux.apply_succ H (p + k) w
  rw [hw, map_zero, zero_add, HomologicalComplex.id_f, ModuleCat.id_apply] at hH
  set c := (H.hom (p + k + 1) (p + k + 2)).hom w
  refine (Submodule.Quotient.eq _).2 (mem_bdry_of _
    (capChain R p (k + 2) (p + (k + 1) + 1) (by omega) ψ ((ρU.f (p + k + 2)).hom c)) ?_)
  refine (d_capChain_of_isSupportedIn (A := univ) p (k + 1)
    (coboundary_mem_vanishing_univ_of_eq_zero hψ) (fun _ _ ↦ subset_univ _)).trans ?_
  change _ = (u : (BM R (TopCat.of (complOpens hX))).X (k + 1)) - u'
  rw [hu, hu', ← map_sub, ← map_sub]
  congr 1
  have hρ := ConcreteCategory.congr_hom (ρU.comm (p + k + 2) (p + k + 1)) c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hρ
  refine hρ.trans ?_
  exact congrArg _ hH.symm

omit [T2Space Y] in
/-- The cap product of a cocycle and a cycle of degree `p + k + 1` is a cycle. -/
lemma capChain_mem_cyc_of_coboundary_eq_zero {P : TopCat.{u}} (p k : ℕ)
    {ψ : Simplex P p → R} (hψ : coboundary R p ψ = 0) {c : (BM R P).X (p + k + 1)}
    (hc : ((BM R P).d (p + k + 1) (p + k)).hom c = 0) :
    capChain R p (k + 1) (p + k + 1) (by omega) ψ c ∈ Cyc (R := R) P (k + 1) := by
  rw [mem_cyc_iff]
  change ((BM R P).d (k + 1) k).hom _ = 0
  rw [d_capChain_of_isSupportedIn (A := univ) p k (coboundary_mem_vanishing_univ_of_eq_zero hψ)
    (fun _ _ ↦ subset_univ _), hc, map_zero]

/-- Equal proper maps induce the same map on locally finite chains. -/
lemma chainMap_congr_apply {P Q : TopCat.{u}} {f g : P ⟶ Q} (hfg : f = g) (hf : IsProperMap f)
    (hg : IsProperMap g) {n : ℕ} (c : (BM R P).X n) :
    ((chainMap R (ModuleCat.of R R) f hf).f n).hom c =
      ((chainMap R (ModuleCat.of R R) g hg).f n).hom c := by
  subst hfg
  rfl

include hG hGX hG0 in
/-- **The connecting square on chains.** Let `G : N × [0, 1] → Y` be a proper deformation of the
closed neighbourhood `N` of `X` into `X`, fixing `X`, ending at the proper retraction `r`; `χ` a
`p`-cochain of `Y` whose coboundary vanishes on the simplices of `U = Y - X`, `ψ = χ|_U`, and `w`
a locally finite `(p + k + 1)`-cycle of `Y`. Then the connecting map sends the class of
`ψ ∩ w|_U` to `-(-1) ^ k` times `r_*` of the class of `(δ χ ∩ ρ w)|_N`, `ρ` the subdivision
towards `{U, int N}`. -/
theorem connecting_homologyEquiv_symm_mk_capChain_eq_smul
    (h : IsRelativeQuasiIso R (ModuleCat.of R R) hX) (hN : IsClosed N) (hXN : X ⊆ interior N)
    {r : C(N, X)} (hr : IsProperMap r) (hGr : ∀ y, G (y, 1) = r y) (p k : ℕ)
    {χ : Simplex Y p → R} (hχ : coboundary R p χ ∈ vanishing R (p + 1) Xᶜ)
    (w : Cyc (R := R) Y (p + k + 1)) (u : Cyc (R := R) (TopCat.of (complOpens hX)) (k + 1))
    (hu : u.1 = capChain R p (k + 1) (p + k + 1) (by omega)
      (cochainPullback R (inclHom (complOpens hX)) p χ)
      (((restrictChainMap R (ModuleCat.of R R) (complOpens hX)).f (p + k + 1)).hom w.1))
    (v : Cyc (R := R) (TopCat.of N) k)
    (hv : v.1 = (subsetRestrictMap R (ModuleCat.of R R) N k).hom
      (capChain R (p + 1) k (p + k + 1) (by omega) (coboundary R p χ)
        ((nbhdSubdiv R Xᶜ N (p + k + 1)).hom w.1))) :
    (connecting R (ModuleCat.of R R) hX h k).hom
        ((homologyEquiv R (TopCat.of (complOpens hX)) (k + 1)).symm (Submodule.Quotient.mk u)) =
      (-(-1 : ℤ) ^ k) • (pushforward R (ModuleCat.of R R) (TopCat.ofHom r) hr k).hom
        ((homologyEquiv R (TopCat.of N) k).symm (Submodule.Quotient.mk v)) := by
  have hG1 : ∀ y, G (y, 1) ∈ X := fun y ↦ (hGr y).symm ▸ (r y).2
  set ψ := cochainPullback R (inclHom (complOpens hX)) p χ
  have hψ : coboundary R p ψ = 0 := coboundary_cochainPullback_inclHom_eq_zero hX hχ
  set z' := (nbhdSubdiv R Xᶜ N (p + k + 1)).hom w.1
  have hz' : ((BM R Y).d (p + k + 1) (p + k)).hom z' = 0 :=
    (mem_cyc_iff _).1 (nbhdSubdiv_mem_cyc (A := Xᶜ) (N := N) w.2)
  have hcov : ∀ σ, z'.1 σ ≠ 0 → singularSimplexImage Y σ ⊆ Xᶜ ∨
      singularSimplexImage Y σ ⊆ interior N := by
    intro σ hσ
    obtain ⟨V, hV, hσV⟩ := smallChainMapLF_small R (ModuleCat.of R R)
      (𝒰 := ({Xᶜ, interior N} : Set (Set Y)))
      (by rintro V (rfl | rfl); exacts [hX.isOpen_compl, isOpen_interior])
      (by rw [sUnion_insert, sUnion_singleton]; exact compl_union_interior_eq_univ hXN) _ w.1 hσ
    rcases hV with rfl | rfl
    · exact Or.inl hσV
    · exact Or.inr hσV
  obtain ⟨z₁, z₂, h12, hz₁, hz₂, B, hB, hBN, hBX, β, hβ⟩ :=
    exists_split_capChain p k hχ z' hz' hcov
  have hρz : ((BM R (TopCat.of (complOpens hX))).d (p + k + 1) (p + k)).hom
      (((restrictChainMap R (ModuleCat.of R R) (complOpens hX)).f (p + k + 1)).hom z') = 0 := by
    have hρ := ConcreteCategory.congr_hom
      ((restrictChainMap R (ModuleCat.of R R) (complOpens hX)).comm (p + k + 1) (p + k)) z'
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hρ
    rw [hρ, hz', map_zero]
  set u'' : Cyc (R := R) (TopCat.of (complOpens hX)) (k + 1) :=
    ⟨_, capChain_mem_cyc_of_coboundary_eq_zero p k hψ hρz⟩
  have hU : (Submodule.Quotient.mk u : HomQ (R := R) (TopCat.of (complOpens hX)) (k + 1)) =
      Submodule.Quotient.mk u'' :=
    mk_capChain_restrict_nbhdSubdiv hX p k hψ w.1 ((mem_cyc_iff _).1 w.2) u u'' hu rfl
  refine (congrArg (fun x ↦ (connecting R (ModuleCat.of R R) hX h k).hom
    ((homologyEquiv R (TopCat.of (complOpens hX)) (k + 1)).symm x)) hU).trans ?_
  refine (connecting_homologyEquiv_symm_mk_capChain hX hB hBN hBX hG hGX hG0 hG1 h hN p k hχ
    z₁ z₂ hz₁ hz₂ (h12 ▸ hz') β hβ u'' (by rw [h12])).trans ?_
  have hXs := mk_subsetRestrictMap_capChain_coboundary hB hBN hN p k hχ z₁ z₂ hz₁ hz₂
    (h12 ▸ hz') β hβ v (by rw [hv, h12])
  rw [hXs]
  erw [map_zsmul, map_zsmul]
  rw [pushforward_eq_homologyMap]
  erw [homologyMap_homologyEquiv_symm_mk]
  rw [smul_smul, neg_mul_neg, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
  congr 2
  apply Subtype.ext
  have hcomp := congrArg (fun φ ↦ (φ.f k).hom β.1)
    (chainMap_comp R (ModuleCat.of R R) (subsetInclusionOfSubset hBN) (TopCat.ofHom r)
      (isProperMap_subsetInclusionOfSubset hB hBN) hr)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at hcomp
  refine Eq.trans ?_ hcomp
  exact chainMap_congr_apply (by ext y; exact hGr ⟨y.1, hBN y.2⟩) _ _ _

end connecting

end borelMooreHomology

end MMP
