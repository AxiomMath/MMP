module

public import MMP.AlgebraicTopology.PoincareDuality.EmbeddingIndependence.CapConnecting
public import MMP.AlgebraicTopology.SingularCohomology.MayerVietoris.Classes
public import MMP.AlgebraicTopology.BorelMoore.MayerVietorisCycles
public import MMP.AlgebraicTopology.PoincareDuality.EmbeddingIndependence.CapRestrict
public import MMP.AlgebraicTopology.PoincareDuality.AlexanderTransport

/-!
# The Mayer–Vietoris step of Poincaré duality on open sets

Let `A`, `B` be open subsets covering a normal Hausdorff space `Y`, `I = A ⊓ B`, and `μ` a
locally finite `n`-cycle of `Y`. If the duality property `PoincareAlexander.DualityAt`
(`[φ] ↦ [φ ∩ μ]` bijective `H^p → H_{n-p}`, and `H^p = 0 = H_p` for `p > n`) holds on `A`, `B`
and `I` at the restrictions of `μ`, it holds on `Y` (`dualityAt_of_mayerVietoris`). This is the
five lemma between the cohomology Mayer–Vietoris sequence
`H^p A ⊕ H^p B → H^p I → H^{p+1} Y → H^{p+1} A ⊕ H^{p+1} B → H^{p+1} I` and the Borel–Moore one
`H_q A ⊕ H_q B → H_q I → H_{q-1} Y → H_{q-1} A ⊕ H_{q-1} B → H_{q-1} I`, done by hand in the
cocycle/cycle model:

* cohomology exactness on classes: `MayerVietorisCochainsClasses`;
* Borel–Moore exactness at `H_q Y` and at `H_{q+1} I`: `BorelMooreMayerVietoris*`; at `H_0 I`
  (needed for `H^{n+1} Y = 0`): `exists_eq_subRestrict_sub_add_d_zero` here;
* the connecting maps commute with the cap product up to the sign `(-1)^(q+1)`
  (`IsMVConn.exists_sub_capChain_mvCoboundary_eq_d`), and the restriction maps commute with it
  (`capHomQ_pullCoc_resCycOpen` from `Y`, `capHomQ_pullCoc_opensLE` from `A` or `B` to `I`).

The proofs here use the cap product on classes (`capHomQ`, `capHomQ_mk`) and the linearity of
`capChain` in the cochain; no chain-level cap formula is unfolded.

## Main results

* `MMP.borelMooreHomology.exists_eq_subRestrict_sub_add_d_zero`: exactness of the
  Borel–Moore Mayer–Vietoris sequence at `H_0(A ∩ B)`.
* `MMP.PoincareAlexander.capHomQ_pullCoc_opensLE`: cap product and restriction from
  `U` to `U' ≤ U`.
* `MMP.PoincareAlexander.dualityAt_of_mayerVietoris`.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.3, Lemma 3.36.
* [G. Bredon, *Topology and Geometry*][bredon1993], VI.8.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology Opposite Topology Set Simplicial Function

universe u

namespace MMP

namespace borelMooreHomology

open SingularChain LocallyFiniteChain

section zero

variable {R : Type u} [CommRing R] {M : ModuleCat.{u} R} {Y : TopCat.{u}} [T2Space Y]

/-- A chain of `I ≤ U` supported in a closed set `K` of `Y` with `K ∩ U ⊆ I` is the restriction
of a chain of `U`. -/
theorem exists_subRestrict_eq {I U : TopologicalSpace.Opens Y} (h : I ≤ U) {K : Set Y}
    (hK : IsClosed K) (hKU : K ∩ U ⊆ (I : Set Y)) {n : ℕ}
    {w₁ : (borelMooreChainComplex R M (TopCat.of I)).X n}
    (hw₁ : IsSupportedIn R M (Subtype.val ⁻¹' K : Set (TopCat.of I)) w₁) :
    ∃ a : (borelMooreChainComplex R M (TopCat.of U)).X n, subRestrict R M U h n a = w₁ := by
  set FU : Set (TopCat.of U) := Subtype.val ⁻¹' K
  have hFU : IsClosed FU := hK.preimage continuous_subtype_val
  have hFUs : FU ⊆ (subOpens U I : Set (TopCat.of U)) := fun z hz ↦
    (mem_subOpens U).2 (hKU ⟨hz, z.2⟩)
  have hw₁' : IsSupportedIn R M (Subtype.val ⁻¹' FU : Set (TopCat.of (subOpens U I)))
      (((borelMooreHomology.chainMap R M (subOpensMap U h)
        (isProperMap_subOpensMap U h)).f n).hom w₁) :=
    hw₁.chainMap _ _ (by rintro _ ⟨z, hz, rfl⟩; exact hz)
  obtain ⟨a, -, ha⟩ := exists_restrictChainMap_eq hFU hFUs hw₁'
  refine ⟨a, ?_⟩
  rw [subRestrict_apply, ha]
  exact chainMap_chainMap_of_comp_eq_id R M _ _ _ _ rfl n w₁

variable {A B : TopologicalSpace.Opens Y} {S T : Set Y}

/-- **Exactness of the Borel–Moore Mayer–Vietoris sequence at `H_0(A ∩ B)`.** Every `0`-chain
of `A ⊓ B` is `x|_{A ⊓ B} - y|_{A ⊓ B}` modulo boundaries, for `0`-chains `x` of `A` and `y`
of `B`. -/
theorem exists_eq_subRestrict_sub_add_d_zero (hS : IsClosed S) (hT : IsClosed T)
    (hST : Disjoint S T) (hBS : (B : Set Y)ᶜ ⊆ interior S) (hAT : (A : Set Y)ᶜ ⊆ interior T)
    (w : (borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).X 0) :
    ∃ (x : (borelMooreChainComplex R M (TopCat.of A)).X 0)
      (y : (borelMooreChainComplex R M (TopCat.of B)).X 0)
      (u : (borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).X 1),
      w = subRestrict R M A inf_le_left 0 x - subRestrict R M B inf_le_right 0 y +
        ((borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).d 1 0).hom u := by
  set 𝒰 := mvCover (A ⊓ B) S T
  set Ψ := smallChainMapLF R M 𝒰
  set s : Set ((TopCat.toSSet.obj (TopCat.of ↥(A ⊓ B))).obj (op ⦋0⦌)) :=
    {τ | singularSimplexImage _ τ ⊆ (Subtype.val ⁻¹' Sᶜ : Set (TopCat.of ↥(A ⊓ B)))}
  set w₁ := (chainPart R M s).hom ((Ψ.f 0).hom w)
  set w₂ := (chainPart R M sᶜ).hom ((Ψ.f 0).hom w)
  set e := (smallHomotopyMap R M 𝒰 0).hom w
  have hsplit : w₁ + w₂ = (Ψ.f 0).hom w := chainPart_add_chainPart_compl R M s _
  have hρ := sub_smallChainMapLF_eq_d_of_cycle R M 𝒰 w (fun m hm ↦ by omega)
  have hw' : w = w₁ + w₂ + ((borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).d 1 0).hom e := by
    rw [hsplit, ← hρ]
    abel
  obtain ⟨h₁, h₂⟩ := isSupportedIn_chainPart_mvCover (I := A ⊓ B) hS hT hST (M := M) w
  obtain ⟨x, hx⟩ := exists_subRestrict_eq (R := R) (M := M) (I := A ⊓ B) (U := A) inf_le_left
    isOpen_interior.isClosed_compl (fun y hy ↦ ⟨hy.2, compl_subset_comm.1 hBS hy.1⟩) h₁
  obtain ⟨y, hy⟩ := exists_subRestrict_eq (R := R) (M := M) (I := A ⊓ B) (U := B) inf_le_right
    isOpen_interior.isClosed_compl (fun y hy ↦ ⟨compl_subset_comm.1 hAT hy.1, hy.2⟩) h₂.neg
  exact ⟨x, y, e, by rwa [hx, hy, sub_neg_eq_add]⟩

end zero

end borelMooreHomology

namespace PoincareAlexander

open SingularChain SingularCochain BorelMooreCross BorelMooreCap borelMooreHomology

section restrict

variable {R : Type u} [CommRing R] {Y : TopCat.{u}} [T2Space Y]

/-- The inclusion `U' → U` of open subsets `U' ≤ U` of `Y`. -/
def opensLE (U : TopologicalSpace.Opens Y) {U' : TopologicalSpace.Opens Y} (h : U' ≤ U) :
    TopCat.of U' ⟶ TopCat.of U :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.1, h x.2⟩, by fun_prop⟩

/-- **The cap product commutes with the restriction from `U` to `U' ≤ U`, up to a boundary**:
`(φ ∩ z)|_{U'} - φ|_{U'} ∩ z|_{U'} = ∂ u` for a cocycle `φ` and a cycle `z` of `U`. -/
theorem exists_d_eq_subRestrict_capChain_sub (U : TopologicalSpace.Opens Y)
    {U' : TopologicalSpace.Opens Y} (h : U' ≤ U) {p q n : ℕ} (hpq : p + q = n)
    {φ : Simplex (TopCat.of U) p → R} (hφ : coboundary R p φ = 0)
    (z : Cyc (R := R) (TopCat.of U) n) :
    ∃ u : (BM R (TopCat.of U')).X (q + 1), ((BM R (TopCat.of U')).d (q + 1) q).hom u =
      subRestrict R (ModuleCat.of R R) U h q (capChain R p q n hpq φ z.1) -
        capChain R p q n hpq (cochainPullback R (opensLE U h) p φ)
          (subRestrict R (ModuleCat.of R R) U h n z.1) := by
  obtain ⟨u, hu, -⟩ := exists_d_eq_restrictChainMap_capChain_sub (U := subOpens U U') p q n hpq
    (A := ∅) hφ (mem_vanishing_empty _) z
  refine ⟨pushChain R (subOpensInv U h) (isProperMap_subOpensInv U h) (q + 1) u, ?_⟩
  rw [← pushChain_d, hu, map_sub, subRestrict_apply, subRestrict_apply,
    ← chainMap_capChain (subOpensInv U h) (isProperMap_subOpensInv U h) p q n hpq]
  rfl

variable (R) in
/-- The restriction `w|_{U'}` of a cycle `w` of an open set `U ⊇ U'`, read in `U'`. -/
def subRestrictCyc (U : TopologicalSpace.Opens Y) {U' : TopologicalSpace.Opens Y} (h : U' ≤ U)
    {m : ℕ} (w : Cyc (R := R) (TopCat.of U) m) : Cyc (R := R) (TopCat.of U') m :=
  pushCyc R (subOpensInv U h) (isProperMap_subOpensInv U h) (resCycOpen R (subOpens U U') w)

/-- The underlying chain of `subRestrictCyc R U h w` is `subRestrict` of the chain of `w`. -/
@[simp] lemma subRestrictCyc_coe (U : TopologicalSpace.Opens Y) {U' : TopologicalSpace.Opens Y}
    (h : U' ≤ U) {m : ℕ} (w : Cyc (R := R) (TopCat.of U) m) :
    (subRestrictCyc R U h w).1 = subRestrict R (ModuleCat.of R R) U h m w.1 :=
  rfl

/-- Homologous cycles of `Y` have homologous restrictions to an open set `U`. -/
lemma mk_resCycOpen_eq (U : TopologicalSpace.Opens Y) {m : ℕ} {w w' : Cyc (R := R) Y m}
    (hw : (Submodule.Quotient.mk w : HomQ (R := R) Y m) = Submodule.Quotient.mk w') :
    (Submodule.Quotient.mk (resCycOpen R U w) : HomQ (R := R) (TopCat.of U) m) =
      Submodule.Quotient.mk (resCycOpen R U w') := by
  obtain ⟨u, hu⟩ := (mk_eq_mk_iff_exists _ _).1 hw
  refine (mk_eq_mk_iff_exists _ _).2
    ⟨((restrictChainMap R (ModuleCat.of R R) U).f (m + 1)).hom u, ?_⟩
  rw [← hom_f_d_apply, hu, map_sub]
  rfl

/-- Homologous cycles of `U` have homologous restrictions to `U' ≤ U`. -/
lemma mk_subRestrictCyc_eq (U : TopologicalSpace.Opens Y) {U' : TopologicalSpace.Opens Y}
    (h : U' ≤ U) {m : ℕ} {w w' : Cyc (R := R) (TopCat.of U) m}
    (hw : (Submodule.Quotient.mk w : HomQ (R := R) (TopCat.of U) m) = Submodule.Quotient.mk w') :
    (Submodule.Quotient.mk (subRestrictCyc R U h w) : HomQ (R := R) (TopCat.of U') m) =
      Submodule.Quotient.mk (subRestrictCyc R U h w') :=
  mk_pushCyc_eq _ _ (mk_resCycOpen_eq _ hw)

/-- `(z|_U)|_{U'}` is homologous to `z|_{U'}`. -/
lemma mk_subRestrictCyc_resCycOpen (U : TopologicalSpace.Opens Y)
    {U' : TopologicalSpace.Opens Y} (h : U' ≤ U) {m : ℕ} (z : Cyc (R := R) Y m) :
    (Submodule.Quotient.mk (subRestrictCyc R U h (resCycOpen R U z)) :
        HomQ (R := R) (TopCat.of U') m) = Submodule.Quotient.mk (resCycOpen R U' z) := by
  refine (mk_pushCyc_eq (subOpensInv U h) (isProperMap_subOpensInv U h)
    (mk_resCycOpen_subOpens U h z)).trans ?_
  congr 1
  exact Subtype.ext (pushChain_pushChain_of_comp_eq_id _ _ _ _ rfl m _)

/-- **The cap product commutes with restriction from `U` to `U' ≤ U`** on classes:
`[a|_{U'}] ∩ [z|_{U'}] = [(a ∩ z|_U)|_{U'}]`. -/
theorem capHomQ_pullCoc_opensLE (U : TopologicalSpace.Opens Y) {U' : TopologicalSpace.Opens Y}
    (h : U' ≤ U) {p q n : ℕ} (hpq : p + q = n) (a : relCocycles R (∅ : Set (TopCat.of U)) p)
    (z : Cyc (R := R) Y n) :
    capHomQ R (∅ : Set (TopCat.of U')) p q n hpq
        (Submodule.Quotient.mk (pullCoc R (opensLE U h) a))
        (Submodule.Quotient.mk (resCycOpen R U' z)) =
      Submodule.Quotient.mk (subRestrictCyc R U h (capCycle R hpq a (resCycOpen R U z))) := by
  refine (congrArg (capHomQ R (∅ : Set (TopCat.of U')) p q n hpq
    (Submodule.Quotient.mk (pullCoc R (opensLE U h) a)))
      (mk_subRestrictCyc_resCycOpen U h z).symm).trans ?_
  rw [capHomQ_mk]
  obtain ⟨u, hu⟩ := exists_d_eq_subRestrict_capChain_sub U h hpq a.2.2 (resCycOpen R U z)
  refine (mk_eq_mk_iff_exists _ _).2 ⟨-u, ?_⟩
  rw [map_neg, hu, neg_sub]
  rfl

end restrict

section mayerVietoris

variable {R : Type u} [CommRing R] {Y : TopCat.{u}} [T2Space Y] {A B : TopologicalSpace.Opens Y}

/-- For `A ⊓ B ≤ U`, a class `[γ|_U]` with `[γ|_U] ∩ [μ|_U] = [w]` restricts to
`[w|_{A ⊓ B}] = [γ|_{A ⊓ B}] ∩ [μ|_{A ⊓ B}]`. -/
lemma mk_subRestrictCyc_eq_capHomQ {U : TopologicalSpace.Opens Y} (hU : A ⊓ B ≤ U)
    {k m n : ℕ} (hkm : k + m = n) (μ : Cyc (R := R) Y n) {γ : Simplex Y k → R}
    (hγ : coboundary R k γ ∈ vanishing R (k + 1) (U : Set Y)) {w : Cyc (R := R) (TopCat.of U) m}
    (hw : capHomQ R (∅ : Set (TopCat.of U)) k m n hkm
        (Submodule.Quotient.mk (subCocycle R (U : Set Y) γ hγ))
        (Submodule.Quotient.mk (resCycOpen R U μ)) = Submodule.Quotient.mk w) :
    (Submodule.Quotient.mk (subRestrictCyc R U hU w) : HomQ (R := R) (TopCat.of ↥(A ⊓ B)) m) =
      capHomQ R (∅ : Set (TopCat.of ↥(A ⊓ B))) k m n hkm
        (Submodule.Quotient.mk (subCocycle R ((A : Set Y) ∩ B) γ
          (vanishing_anti (show (A : Set Y) ∩ B ⊆ U from hU) hγ)))
        (Submodule.Quotient.mk (resCycOpen R (A ⊓ B) μ)) := by
  rw [capHomQ_mk] at hw
  exact (mk_subRestrictCyc_eq U hU hw.symm).trans (capHomQ_pullCoc_opensLE U hU hkm _ μ).symm

/-- **The cohomological half of the five lemma.** Let `e` be a `k`-cochain of `Y` which is a
cocycle on `A ∩ B`. If `[e|_{A ∩ B}] ∩ [μ|_{A ⊓ B}] = [x|_{A ⊓ B}] - [y|_{A ⊓ B}]` for cycles `x`
of `A` and `y` of `B`, and the duality maps of `A`, `B` are onto and that of `A ⊓ B` is one to
one in bidegree `(k, m)`, then the Mayer–Vietoris coboundary `[δ_MV e]` vanishes. -/
theorem mk_mvCoboundary_eq_zero_of_capHomQ (hAB : (A : Set Y) ∪ B = univ) {k m n : ℕ}
    (hkm : k + m = n) (μ : Cyc (R := R) Y n)
    (hAs : Surjective fun c ↦ capHomQ R (∅ : Set (TopCat.of A)) k m n hkm c
      (Submodule.Quotient.mk (resCycOpen R A μ)))
    (hBs : Surjective fun c ↦ capHomQ R (∅ : Set (TopCat.of B)) k m n hkm c
      (Submodule.Quotient.mk (resCycOpen R B μ)))
    (hIi : Injective fun c ↦ capHomQ R (∅ : Set (TopCat.of ↥(A ⊓ B))) k m n hkm c
      (Submodule.Quotient.mk (resCycOpen R (A ⊓ B) μ)))
    {e : Simplex Y k → R} (he : coboundary R k e ∈ vanishing R (k + 1) ((A : Set Y) ∩ B))
    (x : Cyc (R := R) (TopCat.of A) m) (y : Cyc (R := R) (TopCat.of B) m)
    (hxy : capHomQ R (∅ : Set (TopCat.of ↥(A ⊓ B))) k m n hkm
        (Submodule.Quotient.mk (subCocycle R ((A : Set Y) ∩ B) e he))
        (Submodule.Quotient.mk (resCycOpen R (A ⊓ B) μ)) =
      (Submodule.Quotient.mk (subRestrictCyc R A (inf_le_left : A ⊓ B ≤ A) x) :
          HomQ (R := R) (TopCat.of ↥(A ⊓ B)) m) -
        Submodule.Quotient.mk (subRestrictCyc R B (inf_le_right : A ⊓ B ≤ B) y)) :
    (Submodule.Quotient.mk (ofCocycle (mvCoboundary R (A : Set Y) B k e)
        (coboundary_mvCoboundary (A := (A : Set Y)) (B := (B : Set Y)) A.isOpen B.isOpen hAB
          he)) :
      relCohomology R (∅ : Set Y) (k + 1)) = 0 := by
  obtain ⟨ca, hca⟩ := hAs (Submodule.Quotient.mk x)
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ ca
  obtain ⟨α, hα, rfl⟩ := exists_subCocycle_eq (R := R) (Y := Y) (A : Set Y) a
  obtain ⟨cb, hcb⟩ := hBs (Submodule.Quotient.mk y)
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ cb
  obtain ⟨β, hβ, rfl⟩ := exists_subCocycle_eq (R := R) (Y := Y) (B : Set Y) b
  have hx := mk_subRestrictCyc_eq_capHomQ (A := A) (B := B) inf_le_left hkm μ hα hca
  have hy := mk_subRestrictCyc_eq_capHomQ (A := A) (B := B) inf_le_right hkm μ hβ hcb
  have hsub : capHomQ R (∅ : Set (TopCat.of ↥(A ⊓ B))) k m n hkm
        (Submodule.Quotient.mk (subCocycle R ((A : Set Y) ∩ B) α
          (vanishing_anti inter_subset_left hα)))
        (Submodule.Quotient.mk (resCycOpen R (A ⊓ B) μ)) -
      capHomQ R (∅ : Set (TopCat.of ↥(A ⊓ B))) k m n hkm
        (Submodule.Quotient.mk (subCocycle R ((A : Set Y) ∩ B) β
          (vanishing_anti inter_subset_right hβ)))
        (Submodule.Quotient.mk (resCycOpen R (A ⊓ B) μ)) =
      capHomQ R (∅ : Set (TopCat.of ↥(A ⊓ B))) k m n hkm
        (Submodule.Quotient.mk (subCocycle R ((A : Set Y) ∩ B) (α - β) (by
          rw [map_sub]
          exact Submodule.sub_mem _ (vanishing_anti inter_subset_left hα)
            (vanishing_anti inter_subset_right hβ))))
        (Submodule.Quotient.mk (resCycOpen R (A ⊓ B) μ)) := by
    rw [subCocycle_sub, Submodule.Quotient.mk_sub, map_sub]
    rfl
  have hcl := hIi (hxy.trans ((congrArg₂ (· - ·) hx hy).trans hsub))
  cases k with
  | zero =>
    exact mk_mvCoboundary_eq_zero_of_sub_mem A.isOpen B.isOpen hAB he hα hβ
      ((mk_subCocycle_eq_mk_iff_zero _ _ _).1 hcl)
  | succ k =>
    obtain ⟨θ, hθ⟩ := (mk_subCocycle_eq_mk_iff_succ _ _ _).1 hcl
    exact mk_mvCoboundary_eq_zero_succ A.isOpen B.isOpen hAB he hα hβ θ hθ

/-- The restriction to an open set `U` of a boundary of `Y` is a boundary of `U`. -/
lemma mk_resCycOpen_eq_zero (U : TopologicalSpace.Opens Y) {m : ℕ} {w : Cyc (R := R) Y m}
    (hw : (Submodule.Quotient.mk w : HomQ (R := R) Y m) = 0) :
    (Submodule.Quotient.mk (resCycOpen R U w) : HomQ (R := R) (TopCat.of U) m) = 0 := by
  obtain ⟨u, hu⟩ := (mk_eq_zero_iff_exists _).1 hw
  refine (mk_eq_zero_iff_exists _).2
    ⟨((restrictChainMap R (ModuleCat.of R R) U).f (m + 1)).hom u, ?_⟩
  rw [← hom_f_d_apply, hu]
  rfl

omit [T2Space Y] in
/-- If `Bᶜ ⊆ interior S` and `Aᶜ ⊆ interior T`, then `(interior S)ᶜ ∩ (interior T)ᶜ ⊆ A ⊓ B`. -/
lemma inter_compl_interior_subset {S T : Set Y} (hBS : (B : Set Y)ᶜ ⊆ interior S)
    (hAT : (A : Set Y)ᶜ ⊆ interior T) :
    (interior S)ᶜ ∩ (interior T)ᶜ ⊆ ((A ⊓ B : TopologicalSpace.Opens Y) : Set Y) :=
  fun _ hx ↦ ⟨compl_subset_comm.1 hAT hx.2, compl_subset_comm.1 hBS hx.1⟩

/-- Every `0`-chain is a cycle. -/
lemma mem_cyc_zero {Z : TopCat.{u}} (x : (BM R Z).X 0) : x ∈ Cyc (R := R) Z 0 := by
  rw [mem_cyc_iff, show (0 : ℕ) - 1 = 0 from rfl, (BM R Z).shape 0 0 (by simp)]
  rfl

/-- A cycle `z` of `Y` whose restrictions to `A` and `B` are boundaries is, up to a boundary, the
connecting chain of a cycle of `A ⊓ B`. -/
lemma exists_isMVConn_of_mk_resCycOpen_eq_zero {S T : Set Y} (hS : IsClosed S) (hT : IsClosed T)
    (hST : Disjoint S T) (hBS : (B : Set Y)ᶜ ⊆ interior S) (hAT : (A : Set Y)ᶜ ⊆ interior T)
    {q : ℕ} (z : Cyc (R := R) Y q)
    (hzA : (Submodule.Quotient.mk (resCycOpen R A z) : HomQ (R := R) (TopCat.of A) q) = 0)
    (hzB : (Submodule.Quotient.mk (resCycOpen R B z) : HomQ (R := R) (TopCat.of B) q) = 0) :
    ∃ (w : Cyc (R := R) (TopCat.of ↥(A ⊓ B)) (q + 1)) (c : (BM R Y).X q) (v : (BM R Y).X (q + 1)),
      IsMVConn R (ModuleCat.of R R) (A ⊓ B) S T w.1 c ∧ z.1 = c + ((BM R Y).d (q + 1) q).hom v := by
  obtain ⟨a, ha⟩ := (mk_eq_zero_iff_exists _).1 hzA
  obtain ⟨b, hb⟩ := (mk_eq_zero_iff_exists _).1 hzB
  obtain ⟨w, c, v, hw, hc, hz⟩ := exists_isMVConn_of_restrictChainMap_eq_d hS hT hST hBS hAT z.1
    (fun m hm ↦ by subst hm; exact (mem_cyc_iff _).1 z.2) a ha.symm b hb.symm
  exact ⟨⟨w, (mem_cyc_iff _).2 hw⟩, c, v, hc, hz⟩

/-- If the cycle `w` of `A ⊓ B` is a boundary, so is every `z ~ c` with `c` a connecting chain
of `w`. -/
lemma mk_eq_zero_of_isMVConn {S T : Set Y} (hS : IsClosed S) (hT : IsClosed T) (hST : Disjoint S T)
    (hFI : (interior S)ᶜ ∩ (interior T)ᶜ ⊆ ((A ⊓ B : TopologicalSpace.Opens Y) : Set Y)) {q : ℕ}
    {w : Cyc (R := R) (TopCat.of ↥(A ⊓ B)) (q + 1)} {c : (BM R Y).X q}
    (hc : IsMVConn R (ModuleCat.of R R) (A ⊓ B) S T w.1 c)
    (hw : (Submodule.Quotient.mk w : HomQ (R := R) (TopCat.of ↥(A ⊓ B)) (q + 1)) = 0)
    (z : Cyc (R := R) Y q) (v : (BM R Y).X (q + 1)) (hz : z.1 = c + ((BM R Y).d (q + 1) q).hom v) :
    (Submodule.Quotient.mk z : HomQ (R := R) Y q) = 0 := by
  obtain ⟨u, hu⟩ := (mk_eq_zero_iff_exists _).1 hw
  obtain ⟨v', hv'⟩ := hc.exists_sub_eq_d hS hT hST hFI isMVConn_zero u (by rw [sub_zero, hu])
  exact (mk_eq_zero_iff_exists _).2 ⟨v' + v, by rw [map_add, ← hv', sub_zero, hz]⟩

/-- If `w|_U` and `w'|_U` are homologous, then `(w - w')|_U` is a boundary of `U`. -/
lemma mk_resCycOpen_sub_eq_zero (U : TopologicalSpace.Opens Y) {m : ℕ} {w w' : Cyc (R := R) Y m}
    (h : (Submodule.Quotient.mk (resCycOpen R U w) : HomQ (R := R) (TopCat.of U) m) =
      Submodule.Quotient.mk (resCycOpen R U w')) :
    (Submodule.Quotient.mk (resCycOpen R U (w - w')) : HomQ (R := R) (TopCat.of U) m) = 0 := by
  obtain ⟨u, hu⟩ := (mk_eq_mk_iff_exists _ _).1 h
  exact (mk_eq_zero_iff_exists _).2 ⟨u, hu.trans (map_sub _ _ _).symm⟩

/-- If `[φ] ∩ [μ] = 0` on `Y` and the duality map of `U` is one to one, then `[φ|_U] = 0`. -/
lemma mk_pullCoc_inclHom_eq_zero_of_capHomQ (U : TopologicalSpace.Opens Y) {p q n : ℕ}
    (h : p + q = n) {μ : Cyc (R := R) Y n} (hU : DualityAt (TopCat.of U) n (resCycOpen R U μ))
    {φ : relCocycles R (∅ : Set Y) p}
    (hc : capHomQ R (∅ : Set Y) p q n h (Submodule.Quotient.mk φ) (Submodule.Quotient.mk μ) = 0) :
    (Submodule.Quotient.mk (pullCoc R (inclHom U) φ) :
      relCohomology R (∅ : Set (TopCat.of U)) p) = 0 := by
  rw [capHomQ_mk] at hc
  exact (injective_iff_map_eq_zero ((capHomQ R (∅ : Set (TopCat.of U)) p q n h).flip
    (Submodule.Quotient.mk (resCycOpen R U μ)))).1 (hU.1 p q h).1 _
    ((capHomQ_pullCoc_resCycOpen U h φ μ).trans (mk_resCycOpen_eq_zero U hc))

/-- If `[φ|_U] = [γ|_U]` and `[γ|_U] ∩ [μ|_U] = [x|_U]`, then `(φ ∩ μ - x)|_U` is a boundary
of `U`. -/
lemma mk_resCycOpen_capCycle_sub_eq_zero (U : TopologicalSpace.Opens Y) {p q n : ℕ}
    (h : p + q = n) (φ : relCocycles R (∅ : Set Y) p) (μ : Cyc (R := R) Y n)
    (x : Cyc (R := R) Y q) {γ : Simplex Y p → R}
    {hγ : coboundary R p γ ∈ vanishing R (p + 1) (U : Set Y)}
    (hφγ : (Submodule.Quotient.mk (subCocycle R U φ.1 (coboundary_mem_vanishing_of_cocycle U φ)) :
        relCohomology R (∅ : Set (TopCat.of (U : Set Y))) p) =
      Submodule.Quotient.mk (subCocycle R U γ hγ))
    (hγx : capHomQ R (∅ : Set (TopCat.of U)) p q n h (Submodule.Quotient.mk (subCocycle R U γ hγ))
      (Submodule.Quotient.mk (resCycOpen R U μ)) = Submodule.Quotient.mk (resCycOpen R U x)) :
    (Submodule.Quotient.mk (resCycOpen R U (capCycle R h φ μ - x)) :
      HomQ (R := R) (TopCat.of U) q) = 0 :=
  mk_resCycOpen_sub_eq_zero U <| (capHomQ_pullCoc_resCycOpen U h φ μ).symm.trans <|
    (congrArg (fun c ↦ capHomQ R (∅ : Set (TopCat.of U)) p q n h c
      (Submodule.Quotient.mk (resCycOpen R U μ))) hφγ).trans hγx

variable [NormalSpace Y]

/-- **Injectivity in the Mayer–Vietoris step.** If `DualityAt` holds on `A`, `B` and `A ⊓ B` at
the restrictions of `μ`, with `A ∪ B = Y`, then `[φ] ↦ [φ ∩ μ]` is one to one on `H^p Y`. -/
theorem injective_capHomQ_of_mayerVietoris (hAB : (A : Set Y) ∪ B = univ) {n : ℕ}
    (μ : Cyc (R := R) Y n) (hA : DualityAt (TopCat.of A) n (resCycOpen R A μ))
    (hB : DualityAt (TopCat.of B) n (resCycOpen R B μ))
    (hI : DualityAt (TopCat.of ↥(A ⊓ B)) n (resCycOpen R (A ⊓ B) μ)) (p q : ℕ)
    (h : p + q = n) :
    Injective fun c ↦ capHomQ R (∅ : Set Y) p q n h c (Submodule.Quotient.mk μ) := by
  obtain ⟨S, T, hS, hT, hST, hBS, hAT⟩ := exists_mvSeparation A.isOpen B.isOpen hAB
  refine (injective_iff_map_eq_zero ((capHomQ R (∅ : Set Y) p q n h).flip
    (Submodule.Quotient.mk μ))).2 fun c hc ↦ ?_
  obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  change capHomQ R (∅ : Set Y) p q n h (Submodule.Quotient.mk φ) (Submodule.Quotient.mk μ) = 0
    at hc
  have hφA := mk_pullCoc_inclHom_eq_zero_of_capHomQ A h hA hc
  have hφB := mk_pullCoc_inclHom_eq_zero_of_capHomQ B h hB hc
  cases p with
  | zero =>
    rw [eq_zero_of_mk_subCocycle_eq_zero (A := (A : Set Y)) (B := (B : Set Y)) A.isOpen B.isOpen
      hAB φ hφA hφB]
    rfl
  | succ k =>
    obtain ⟨e, he, hφe⟩ := exists_mk_eq_mk_mvCoboundary (A := (A : Set Y)) (B := (B : Set Y))
      A.isOpen B.isOpen hAB φ hφA hφB
    change (Submodule.Quotient.mk φ : relCohomology R (∅ : Set Y) (k + 1)) = 0
    rw [hφe]
    rw [hφe, capHomQ_mk] at hc
    obtain rfl : n = k + q + 1 := by omega
    obtain ⟨v₀, hv₀⟩ := (mk_eq_zero_iff_exists _).1 hc
    let eI : relCocycles R (∅ : Set (TopCat.of ↥(A ⊓ B))) k := subCocycle R ((A : Set Y) ∩ B) e he
    let w := capCycle R (show k + (q + 1) = k + q + 1 by omega) eI (resCycOpen R (A ⊓ B) μ)
    have hw : ((BM R (TopCat.of ↥(A ⊓ B))).d (q + 1) q).hom w.1 = 0 := (mem_cyc_iff _).1 w.2
    obtain ⟨c, hc'⟩ := exists_isMVConn hS hT hST (inter_compl_interior_subset hBS hAT) w.1 hw
    obtain ⟨v₁, hv₁⟩ := IsMVConn.exists_sub_capChain_mvCoboundary_eq_d hS hT hST hBS hAT he μ.1
      ((mem_cyc_iff _).1 μ.2) hc'
    obtain ⟨x, y, u, hx, hy, hwxy⟩ := IsMVConn.exists_eq_sub_add_d hBS hAT hw hc'
      (v₁ + (-1 : ℤ) ^ (q + 1) • v₀) (by
        rw [map_add, map_zsmul, hv₀, ← hv₁]
        exact sub_add_cancel _ _)
    refine mk_mvCoboundary_eq_zero_of_capHomQ hAB (show k + (q + 1) = k + q + 1 by omega) μ
      (hA.1 _ _ _).2 (hB.1 _ _ _).2 (hI.1 _ _ _).1 he ⟨x, (mem_cyc_iff _).2 hx⟩
      ⟨y, (mem_cyc_iff _).2 hy⟩ ?_
    rw [capHomQ_mk]
    refine Eq.trans ((mk_eq_mk_iff_exists _
      (subRestrictCyc R A (inf_le_left : A ⊓ B ≤ A) ⟨x, (mem_cyc_iff _).2 hx⟩ -
        subRestrictCyc R B (inf_le_right : A ⊓ B ≤ B) ⟨y, (mem_cyc_iff _).2 hy⟩)).2 ⟨u, ?_⟩)
      (Submodule.Quotient.mk_sub _)
    change _ = w.1 - (subRestrict _ _ A _ (q + 1) x - subRestrict _ _ B _ (q + 1) y)
    rw [hwxy]
    abel

/-- **Vanishing of `H_q Y` for `q > n` in the Mayer–Vietoris step**: if `DualityAt` holds on `A`,
`B` and `A ⊓ B` at the restrictions of `μ`, with `A ∪ B = Y`, then `H_q Y` is trivial. -/
theorem subsingleton_homQ_of_mayerVietoris (hAB : (A : Set Y) ∪ B = univ) {n : ℕ}
    (μ : Cyc (R := R) Y n) (hA : DualityAt (TopCat.of A) n (resCycOpen R A μ))
    (hB : DualityAt (TopCat.of B) n (resCycOpen R B μ))
    (hI : DualityAt (TopCat.of ↥(A ⊓ B)) n (resCycOpen R (A ⊓ B) μ)) {q : ℕ} (hq : n < q) :
    Subsingleton (HomQ (R := R) Y q) := by
  obtain ⟨S, T, hS, hT, hST, hBS, hAT⟩ := exists_mvSeparation A.isOpen B.isOpen hAB
  have key : ∀ z : Cyc (R := R) Y q, (Submodule.Quotient.mk z : HomQ (R := R) Y q) = 0 := by
    intro z
    obtain ⟨w, c, v, hc, hz⟩ := exists_isMVConn_of_mk_resCycOpen_eq_zero hS hT hST hBS hAT z
      ((hA.2.2 q hq).elim _ _) ((hB.2.2 q hq).elim _ _)
    exact mk_eq_zero_of_isMVConn hS hT hST (inter_compl_interior_subset hBS hAT) hc
      ((hI.2.2 (q + 1) (by omega)).elim _ _) z v hz
  exact subsingleton_of_forall_eq 0 ((Submodule.Quotient.mk_surjective _).forall.2 key)

/-- **Vanishing of `H^p Y` for `p > n` in the Mayer–Vietoris step**: if `DualityAt` holds on `A`,
`B` and `A ⊓ B` at the restrictions of `μ`, with `A ∪ B = Y`, then `H^p Y` is trivial. -/
theorem subsingleton_relCohomology_of_mayerVietoris (hAB : (A : Set Y) ∪ B = univ) {n : ℕ}
    (μ : Cyc (R := R) Y n) (hA : DualityAt (TopCat.of A) n (resCycOpen R A μ))
    (hB : DualityAt (TopCat.of B) n (resCycOpen R B μ))
    (hI : DualityAt (TopCat.of ↥(A ⊓ B)) n (resCycOpen R (A ⊓ B) μ)) {p : ℕ} (hp : n < p) :
    Subsingleton (relCohomology R (∅ : Set Y) p) := by
  obtain ⟨S, T, hS, hT, hST, hBS, hAT⟩ := exists_mvSeparation A.isOpen B.isOpen hAB
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  have key : ∀ φ : relCocycles R (∅ : Set Y) (k + 1),
      (Submodule.Quotient.mk φ : relCohomology R (∅ : Set Y) (k + 1)) = 0 := by
    intro φ
    obtain ⟨e, he, hφe⟩ := exists_mk_eq_mk_mvCoboundary (A := (A : Set Y)) (B := (B : Set Y))
      A.isOpen B.isOpen hAB φ ((hA.2.1 (k + 1) hp).elim _ _) ((hB.2.1 (k + 1) hp).elim _ _)
    rw [hφe]
    let eI : relCocycles R (∅ : Set (TopCat.of ↥(A ⊓ B))) k :=
      subCocycle R ((A : Set Y) ∩ B) e he
    rcases (show n < k ∨ n = k by omega) with hk | rfl
    · have h0 : (Submodule.Quotient.mk eI : relCohomology R (∅ : Set (TopCat.of ↥(A ⊓ B))) k) =
          0 := (hI.2.1 k hk).elim _ _
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      obtain ⟨θ, hθ⟩ := (mk_subCocycle_eq_zero_iff_succ _ _ _).1 h0
      have h00 : coboundary R (j + 1) (0 : Simplex Y (j + 1) → R) = 0 := map_zero _
      exact mk_mvCoboundary_eq_zero_succ A.isOpen B.isOpen hAB he
        (h00 ▸ Submodule.zero_mem _) (h00 ▸ Submodule.zero_mem _) θ (by rwa [sub_zero, sub_zero])
    · obtain ⟨w₀, hw₀⟩ := Submodule.Quotient.mk_surjective _
        (capHomQ R (∅ : Set (TopCat.of ↥(A ⊓ B))) n 0 n (add_zero n)
          (Submodule.Quotient.mk eI) (Submodule.Quotient.mk (resCycOpen R (A ⊓ B) μ)))
      obtain ⟨x, y, u, hxy⟩ := exists_eq_subRestrict_sub_add_d_zero (R := R)
        (M := ModuleCat.of R R) hS hT hST hBS hAT w₀.1
      refine mk_mvCoboundary_eq_zero_of_capHomQ hAB (add_zero n) μ
        (hA.1 _ _ _).2 (hB.1 _ _ _).2 (hI.1 _ _ _).1 he ⟨x, mem_cyc_zero x⟩ ⟨y, mem_cyc_zero y⟩ ?_
      refine hw₀.symm.trans (Eq.trans ((mk_eq_mk_iff_exists _
        (subRestrictCyc R A (inf_le_left : A ⊓ B ≤ A) ⟨x, mem_cyc_zero x⟩ -
          subRestrictCyc R B (inf_le_right : A ⊓ B ≤ B) ⟨y, mem_cyc_zero y⟩)).2 ⟨u, ?_⟩)
        (Submodule.Quotient.mk_sub _))
      change ((BM R (TopCat.of ↥(A ⊓ B))).d 1 0).hom u =
        (show (BM R (TopCat.of ↥(A ⊓ B))).X 0 from w₀.1) -
          (subRestrict _ _ A _ 0 x - subRestrict _ _ B _ 0 y)
      rw [hxy]
      exact (add_sub_cancel_left _ _).symm
  exact subsingleton_of_forall_eq 0 ((Submodule.Quotient.mk_surjective _).forall.2 key)

omit [NormalSpace Y] in
/-- The degree `k + 1` case of surjectivity in the Mayer–Vietoris step: if `φ ∩ μ - x` is, up to
a boundary, a connecting chain of a cycle of `A ⊓ B`, then `[x]` is in the image of `· ∩ [μ]`. -/
lemma exists_capHomQ_eq_of_isMVConn_succ (hAB : (A : Set Y) ∪ B = univ) {S T : Set Y}
    (hS : IsClosed S) (hT : IsClosed T) (hST : Disjoint S T) (hBS : (B : Set Y)ᶜ ⊆ interior S)
    (hAT : (A : Set Y)ᶜ ⊆ interior T) {k q : ℕ} (μ : Cyc (R := R) Y (k + q + 1))
    (hI : DualityAt (TopCat.of ↥(A ⊓ B)) (k + q + 1) (resCycOpen R (A ⊓ B) μ))
    (h : k + 1 + q = k + q + 1) (φ : relCocycles R (∅ : Set Y) (k + 1)) (x : Cyc (R := R) Y q)
    {w : Cyc (R := R) (TopCat.of ↥(A ⊓ B)) (q + 1)} {c : (BM R Y).X q} {v : (BM R Y).X (q + 1)}
    (hc : IsMVConn R (ModuleCat.of R R) (A ⊓ B) S T w.1 c)
    (hzc : capChain R (k + 1) q (k + q + 1) h φ.1 μ.1 - x.1 = c + ((BM R Y).d (q + 1) q).hom v) :
    ∃ c' : relCohomology R (∅ : Set Y) (k + 1),
      capHomQ R (∅ : Set Y) (k + 1) q (k + q + 1) h c' (Submodule.Quotient.mk μ) =
        Submodule.Quotient.mk x := by
  have hFI := inter_compl_interior_subset (A := A) (B := B) hBS hAT
  obtain ⟨cε, hcε⟩ := (hI.1 k (q + 1) (by omega)).2 (Submodule.Quotient.mk w)
  obtain ⟨ε', rfl⟩ := Submodule.Quotient.mk_surjective _ cε
  obtain ⟨ε, hε, rfl⟩ := exists_subCocycle_eq (R := R) (Y := Y) ((A : Set Y) ∩ B) ε'
  let eI : relCocycles R (∅ : Set (TopCat.of ↥(A ⊓ B))) k := subCocycle R ((A : Set Y) ∩ B) ε hε
  let w' := capCycle R (show k + (q + 1) = k + q + 1 by omega) eI (resCycOpen R (A ⊓ B) μ)
  have hw' : ((BM R (TopCat.of ↥(A ⊓ B))).d (q + 1) q).hom w'.1 = 0 := (mem_cyc_iff _).1 w'.2
  obtain ⟨c', hc'⟩ := exists_isMVConn hS hT hST hFI w'.1 hw'
  obtain ⟨v₁, hv₁⟩ := IsMVConn.exists_sub_capChain_mvCoboundary_eq_d hS hT hST hBS hAT hε μ.1
    ((mem_cyc_iff _).1 μ.2) hc'
  have hcε' : (Submodule.Quotient.mk w' : HomQ (R := R) (TopCat.of ↥(A ⊓ B)) (q + 1)) =
      Submodule.Quotient.mk w := hcε
  obtain ⟨u, hu⟩ := (mk_eq_mk_iff_exists w w').1 hcε'.symm
  obtain ⟨v₂, hv₂⟩ := hc.exists_sub_eq_d hS hT hST hFI hc' u hu.symm
  set s : ℤ := (-1 : ℤ) ^ (q + 1)
  let ψ := ofCocycle (mvCoboundary R (A : Set Y) B k ε)
    (coboundary_mvCoboundary (A := (A : Set Y)) (B := (B : Set Y)) A.isOpen B.isOpen hAB hε)
  refine ⟨Submodule.Quotient.mk (φ - s • ψ), ?_⟩
  rw [capHomQ_mk]
  refine (mk_eq_mk_iff_exists _ x).2 ⟨v₁ + v₂ + v, ?_⟩
  have hcap : capChain R (k + 1) q (k + q + 1) h (φ - s • ψ).1 μ.1 =
      capChain R (k + 1) q (k + q + 1) h φ.1 μ.1 -
        s • capChain R (k + 1) q (k + q + 1) h (mvCoboundary R (A : Set Y) B k ε) μ.1 := by
    rw [Submodule.coe_sub, Submodule.coe_smul_of_tower, map_sub, map_zsmul, LinearMap.sub_apply,
      LinearMap.smul_apply]
    rfl
  have hdv : ((BM R Y).d (q + 1) q).hom v =
      (capChain R (k + 1) q (k + q + 1) h φ.1 μ.1 - x.1) - c := eq_sub_of_add_eq' hzc.symm
  change _ = capChain R (k + 1) q (k + q + 1) h (φ - s • ψ).1 μ.1 - x.1
  rw [map_add, map_add, ← hv₁, ← hv₂, hdv, hcap]
  abel

/-- **Surjectivity in the Mayer–Vietoris step.** If `DualityAt` holds on `A`, `B` and `A ⊓ B` at
the restrictions of `μ`, with `A ∪ B = Y`, then `[φ] ↦ [φ ∩ μ]` is onto `H_q Y`. -/
theorem surjective_capHomQ_of_mayerVietoris (hAB : (A : Set Y) ∪ B = univ) {n : ℕ}
    (μ : Cyc (R := R) Y n) (hA : DualityAt (TopCat.of A) n (resCycOpen R A μ))
    (hB : DualityAt (TopCat.of B) n (resCycOpen R B μ))
    (hI : DualityAt (TopCat.of ↥(A ⊓ B)) n (resCycOpen R (A ⊓ B) μ)) (p q : ℕ)
    (h : p + q = n) :
    Surjective fun c ↦ capHomQ R (∅ : Set Y) p q n h c (Submodule.Quotient.mk μ) := by
  obtain ⟨S, T, hS, hT, hST, hBS, hAT⟩ := exists_mvSeparation A.isOpen B.isOpen hAB
  have hFI := inter_compl_interior_subset (A := A) (B := B) hBS hAT
  intro X
  obtain ⟨x, rfl⟩ : ∃ x : Cyc (R := R) Y q, Submodule.Quotient.mk x = X :=
    Submodule.Quotient.mk_surjective _ X
  obtain ⟨ca, hca⟩ := (hA.1 p q h).2 (Submodule.Quotient.mk (resCycOpen R A x))
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ ca
  obtain ⟨α, hα, rfl⟩ := exists_subCocycle_eq (R := R) (Y := Y) (A : Set Y) a
  obtain ⟨cb, hcb⟩ := (hB.1 p q h).2 (Submodule.Quotient.mk (resCycOpen R B x))
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ cb
  obtain ⟨β, hβ, rfl⟩ := exists_subCocycle_eq (R := R) (Y := Y) (B : Set Y) b
  -- the classes `[α|_{A ∩ B}]` and `[β|_{A ∩ B}]` agree
  have hxA := (mk_subRestrictCyc_eq_capHomQ (A := A) (B := B) inf_le_left h μ hα hca).symm.trans
    (mk_subRestrictCyc_resCycOpen A inf_le_left x)
  have hxB := (mk_subRestrictCyc_eq_capHomQ (A := A) (B := B) inf_le_right h μ hβ hcb).symm.trans
    (mk_subRestrictCyc_resCycOpen B inf_le_right x)
  have hαβ := (hI.1 p q h).1 (hxA.trans hxB.symm)
  -- glue them to a cocycle `φ` of `Y`
  obtain ⟨φ, hφA, hφB⟩ : ∃ φ : relCocycles R (∅ : Set Y) p,
      (Submodule.Quotient.mk (subCocycle R A φ.1 (coboundary_mem_vanishing_of_cocycle A φ)) :
          relCohomology R (∅ : Set (TopCat.of (A : Set Y))) p) =
        Submodule.Quotient.mk (subCocycle R A α hα) ∧
      (Submodule.Quotient.mk (subCocycle R B φ.1 (coboundary_mem_vanishing_of_cocycle B φ)) :
          relCohomology R (∅ : Set (TopCat.of (B : Set Y))) p) =
        Submodule.Quotient.mk (subCocycle R B β hβ) := by
    cases p with
    | zero => exact exists_glue_mk_zero A.isOpen B.isOpen hAB hα hβ hαβ
    | succ k => exact exists_glue_mk_succ A.isOpen B.isOpen hAB hα hβ hαβ
  -- `z = φ ∩ μ - x` restricts to boundaries on `A` and on `B`
  set z := capCycle R h φ μ - x
  obtain ⟨w, c, v, hc, hz⟩ := exists_isMVConn_of_mk_resCycOpen_eq_zero hS hT hST hBS hAT z
    (mk_resCycOpen_capCycle_sub_eq_zero A h φ μ x hφA hca)
    (mk_resCycOpen_capCycle_sub_eq_zero B h φ μ x hφB hcb)
  have hzc : capChain R p q n h φ.1 μ.1 - x.1 = c + ((BM R Y).d (q + 1) q).hom v := hz
  cases p with
  | zero =>
    obtain rfl : n = q := by omega
    have hz0 := mk_eq_zero_of_isMVConn hS hT hST hFI hc ((hI.2.2 (n + 1) (by omega)).elim _ _) z
      v hz
    refine ⟨Submodule.Quotient.mk φ, ?_⟩
    change capHomQ R (∅ : Set Y) 0 n n h _ _ = _
    rw [capHomQ_mk]
    exact (Submodule.Quotient.eq _).2 ((Submodule.Quotient.mk_eq_zero _).1 hz0)
  | succ k =>
    obtain rfl : n = k + q + 1 := by omega
    exact exists_capHomQ_eq_of_isMVConn_succ hAB hS hT hST hBS hAT μ hI h φ x hc hzc

/-- **The Mayer–Vietoris step of Poincaré duality** (Hatcher, Lemma 3.36; Bredon, VI.8). Let
`A`, `B` be open subsets covering a normal Hausdorff space `Y` and `μ` a locally finite
`n`-cycle of `Y`. If the duality property `DualityAt` holds on `A`, on `B` and on `A ⊓ B` at the
restrictions of `μ`, it holds on `Y` at `μ`. -/
theorem dualityAt_of_mayerVietoris (hAB : (A : Set Y) ∪ B = univ) {n : ℕ}
    (μ : Cyc (R := R) Y n) (hA : DualityAt (TopCat.of A) n (resCycOpen R A μ))
    (hB : DualityAt (TopCat.of B) n (resCycOpen R B μ))
    (hI : DualityAt (TopCat.of ↥(A ⊓ B)) n (resCycOpen R (A ⊓ B) μ)) :
    DualityAt Y n μ :=
  ⟨fun p q h ↦ ⟨injective_capHomQ_of_mayerVietoris hAB μ hA hB hI p q h,
      surjective_capHomQ_of_mayerVietoris hAB μ hA hB hI p q h⟩,
    fun _ hp ↦ subsingleton_relCohomology_of_mayerVietoris hAB μ hA hB hI hp,
    fun _ hq ↦ subsingleton_homQ_of_mayerVietoris hAB μ hA hB hI hq⟩

end mayerVietoris

end PoincareAlexander

end MMP
