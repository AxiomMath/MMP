module

public import MMP.AlgebraicTopology.CapProduct.SupportLemmas
public import MMP.AlgebraicTopology.SingularCohomology.CupProduct.Commutative
public import MMP.AlgebraicTopology.PoincareDuality.MayerVietoris

/-!
# The cap product with a cup product: chain level (Fulton, §19.1)

For singular cochains `φ` of degree `p`, `ψ` of degree `q` and a locally finite `n`-chain `c`,
with the cap product `φ ∩ σ = φ (σ ⌊ [n - p, …, n]) σ ⌊ [0, …, n - p]` of
`MMP.BorelMooreCap.capChain`, `(φ ∪ ψ) ∩ c = φ ∩ (ψ ∩ c)`
(`MMP.BorelMooreCap.capChain_cup`): with `l = n - p - q`, both sides weight `σ` by
`φ (σ ⌊ [l, …, l + p]) ψ (σ ⌊ [l + p, …, n])` and keep its front face `σ ⌊ [0, …, l]`.

On classes the cup product is `[φ] ∪ [ψ] = [ρ^* (φ ∪ ψ)]`, `ρ` the small-chains map of the open
couple `{A, B}`; for a cocycle `χ`, `ρ^* χ - χ = δ η` with `η` vanishing on the simplices of `A`
and on those of `B`
(`MMP.SingularCochain.pullback_smallChainMap_sub_mem_pairCoboundaries`),
so on cycles all of whose simplices lie in `A`, in `B` or in a closed `L`, the cap products with
`ρ^* χ` and with `χ` restrict to homologous cycles of `L`.

## Main results

* `MMP.BorelMooreCap.capChain_cup`: `(φ ∪ ψ) ∩ c = φ ∩ (ψ ∩ c)`.
* `MMP.BorelMooreCap.homologyMap_preimageRestrict_capHomQNbhd_capHomQNbhd`: for
  `A`, `B` open, `N`, `L` closed with `B ∪ int N = Y` and `A ∪ B ∪ int L = Y`, the push-forward to
  `L` of `ι^* x ∩ (y ∩_N b) ∈ H_l (N ∩ L)` is `(x ∪ y) ∩_L b`, `ι : N → Y` the inclusion.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.3.
-/

@[expose] public noncomputable section

open CategoryTheory Set Topology Opposite Simplicial Finsupp

universe u

namespace MMP

open MMP

namespace SingularCochain

open SingularChain

variable {R : Type*} [CommRing R] {Y : Type*} [TopologicalSpace Y]

/-- The pull-back `τ ↦ χ (D τ)` of a cochain along Hatcher's homotopy `D` towards `𝒰`. -/
def homotopyPullback (𝒰 : Set (Set Y)) (n : ℕ) (χ : Simplex Y (n + 1) → R) : Simplex Y n → R :=
  fun τ ↦ eval χ (smallHomotopy R 𝒰 n (single τ 1))

/-- Evaluating `τ ↦ χ (D τ)` on a chain `c` is evaluating `χ` on `D c`. -/
lemma eval_homotopyPullback (𝒰 : Set (Set Y)) (n : ℕ) (χ : Simplex Y (n + 1) → R)
    (c : Chain R Y n) : eval (homotopyPullback 𝒰 n χ) c = eval χ (smallHomotopy R 𝒰 n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul]
    simp [homotopyPullback]

/-- `D` vanishes on a simplex lying in a member of `𝒰`, so `τ ↦ χ (D τ)` vanishes there. -/
lemma homotopyPullback_mem_vanishing {𝒰 : Set (Set Y)} {U : Set Y} (hU : U ∈ 𝒰) (n : ℕ)
    (χ : Simplex Y (n + 1) → R) : homotopyPullback 𝒰 n χ ∈ vanishing R n U := fun τ hτ ↦ by
  rw [homotopyPullback, smallHomotopy_eq_zero_of_mem_small
    (mem_small_of_mem_inside hU (single_mem_supported R (1 : R) hτ)), map_zero]

/-- For a cocycle `χ`, `ρ^* χ - χ` is the coboundary of a cochain vanishing on the simplices of
`A` and on those of `B`, `ρ` Hatcher's small-chains map for `{A, B}`: `ρ = 1 - ∂ D - D ∂`. -/
lemma pullback_smallChainMap_sub_mem_pairCoboundaries (A B : Set Y) {m : ℕ}
    {χ : Simplex Y m → R} (hδ : coboundary R m χ = 0) :
    pullback (smallChainMap R {A, B} m) χ - χ ∈ pairCoboundaries R A B m := by
  cases m with
  | zero =>
    have : pullback (smallChainMap R {A, B} 0) χ = χ := by
      ext σ
      change eval χ (smallChainMap R {A, B} 0 (single σ 1)) = χ σ
      rw [smallChainMap_zero, map_sub, ← eval_coboundary, hδ]
      simp
    rw [this, sub_self]
    exact zero_mem _
  | succ m =>
    refine ⟨-homotopyPullback {A, B} m χ, ⟨neg_mem (homotopyPullback_mem_vanishing (by simp) m χ),
      neg_mem (homotopyPullback_mem_vanishing (by simp) m χ)⟩, ?_⟩
    ext σ
    have h1 := eval_coboundary m (homotopyPullback {A, B} m χ) (single σ 1)
    rw [eval_homotopyPullback] at h1
    rw [map_neg, Pi.neg_apply, Pi.sub_apply]
    change _ = eval χ (smallChainMap R {A, B} (m + 1) (single σ 1)) - χ σ
    rw [smallChainMap_succ, map_sub, map_sub, ← eval_coboundary, hδ]
    simp only [linearCombination_single, one_smul] at h1 ⊢
    rw [← h1]
    simp

/-- The cup product of two cocycles is a cocycle. -/
lemma coboundary_cup_eq_zero (p q n : ℕ) (h : p + q = n) {φ : Simplex Y p → R}
    (hφ : coboundary R p φ = 0) {ψ : Simplex Y q → R} (hψ : coboundary R q ψ = 0) :
    coboundary R n (cup p q n h φ ψ) = 0 := by
  rw [coboundary_cup, hφ, hψ]
  simp

end SingularCochain

namespace cohomologyWithSupports

variable {R : Type u} [CommRing R]

/-- Transporting a relative cohomology class along reflexivity is the identity. -/
lemma congrIndex_rfl (Y : TopCat.{u}) {S : Set Y} {k : ℤ}
    (x : relativeSingularCohomology R (ModuleCat.of R R) Y S k) :
    congrIndex R Y rfl rfl x = x :=
  rfl

end cohomologyWithSupports

namespace BorelMooreCap

open SingularCross BorelMooreCross SingularCochain SingularChain LocallyFiniteChain
  borelMooreHomology

variable {R : Type u} [CommRing R] {Y : TopCat.{u}}

/-- Multiplying a locally finite chain by `g'` and then by `g` is multiplying it by the pointwise
product `g * g'`. -/
lemma W_W {n : ℕ} (g g' : Simp Y n → R) (c : (BM R Y).X n) :
    W R g (W R g' c) = W R (fun σ ↦ g σ * g' σ) c := by
  apply coeff_injective R
  funext σ
  simp only [coeff_W, mul_assoc]

/-- **The cap product with a cup product**, on chains: `(φ ∪ ψ) ∩ c = φ ∩ (ψ ∩ c)`. -/
theorem capChain_cup (p q l m n : ℕ) (h₁ : q + m = n) (h₂ : p + l = m) (h : p + q + l = n)
    (φ : Simplex Y p → R) (ψ : Simplex Y q → R) (c : (BM R Y).X n) :
    capChain R (p + q) l n h (cup p q (p + q) rfl φ ψ) c =
      capChain R p l m h₂ φ (capChain R q m n h₁ ψ c) := by
  rw [capChain_apply, capChain_apply, capChain_apply, W_pf, pf_pf, wt_comp_opS, W_W]
  have e1 : front m n (by omega) ∘ front l m (by omega) = front l n (by omega) := by
    funext j; apply Fin.ext; simp only [Function.comp_apply, front_val]
  rw [e1]
  refine congrArg (fun g ↦ pf R _ (W R g c)) ?_
  funext σ
  have e2 : back (p + q) n l (by omega) ∘ front p (p + q) (by omega) =
      front m n (by omega) ∘ back p m l (by omega) := by
    funext j; apply Fin.ext; simp only [Function.comp_apply, front_val, back_val]
  have e3 : back (p + q) n l (by omega) ∘ back q (p + q) p (by omega) = back q n m (by omega) := by
    funext j; apply Fin.ext; simp only [Function.comp_apply, back_val]; omega
  simp only [wt, cup_apply, comp_smap_comp, e2, e3]

/-- A simplex of `φ ∩ c` is the front face of a simplex `σ` of `c` with
`φ (σ ⌊ [q, …, n]) ≠ 0`. -/
lemma exists_of_coeff_capChain_ne_zero (p q n : ℕ) (h : p + q = n) (φ : Simplex Y p → R)
    (c : (BM R Y).X n) {τ : Simp Y q} (hτ : coeff R (capChain R p q n h φ c) τ ≠ 0) :
    ∃ σ, coeff R c σ ≠ 0 ∧ wt φ (back p n q (by omega)) σ ≠ 0 ∧
      singularSimplexImage Y τ ⊆ singularSimplexImage Y σ := by
  rw [capChain_apply, coeff_pf] at hτ
  obtain ⟨σ, hσ, rfl⟩ := support_pushforwardFun_subset _ _ hτ
  rw [Function.mem_support, coeff_W] at hσ
  exact ⟨σ, right_ne_zero_of_mul hσ, left_ne_zero_of_mul hσ, image_opS_subset _ σ⟩

/-- The weight of a cochain vanishing on `A` vanishes on a simplex lying in `A`. -/
lemma wt_eq_zero_of_vanishing {A : Set Y} {p n : ℕ} (f : Fin (p + 1) → Fin (n + 1))
    {φ : Simplex Y p → R} (hφ : φ ∈ vanishing R p A) {σ : Simp Y n}
    (hσ : singularSimplexImage Y σ ⊆ A) : wt φ f σ = 0 :=
  hφ _ (by rintro _ ⟨t, rfl⟩; exact hσ ⟨_, rfl⟩)

/-- If `φ` vanishes on the simplices of `A` and on those of `B`, and every simplex of `c` lies in
`A`, in `B` or in `V`, then `φ ∩ c` is supported in `V`. -/
lemma singularSimplexImage_subset_of_coeff_capChain_ne_zero_of_three {A B V : Set Y}
    (p q n : ℕ) (h : p + q = n) {φ : Simplex Y p → R} (hφA : φ ∈ vanishing R p A)
    (hφB : φ ∈ vanishing R p B) (c : (BM R Y).X n)
    (hc : ∀ σ, coeff R c σ ≠ 0 → singularSimplexImage Y σ ⊆ A ∨ singularSimplexImage Y σ ⊆ B ∨
      singularSimplexImage Y σ ⊆ V)
    {τ : Simp Y q} (hτ : coeff R (capChain R p q n h φ c) τ ≠ 0) :
    singularSimplexImage Y τ ⊆ V := by
  obtain ⟨σ, hσ, hw, hτσ⟩ := exists_of_coeff_capChain_ne_zero p q n h φ c hτ
  rcases hc σ hσ with hA | hB | hV
  · exact absurd (wt_eq_zero_of_vanishing _ hφA hA) hw
  · exact absurd (wt_eq_zero_of_vanishing _ hφB hB) hw
  · exact hτσ.trans hV

/-- The restriction to a closed `N` of a cycle supported in `N` is a cycle of `N`. -/
lemma subsetRestrictMap_mem_cyc {N : Set Y} (hN : IsClosed N) {q : ℕ} {c : (BM R Y).X q}
    (hc : IsSupportedIn R (ModuleCat.of R R) N c) (hz : c ∈ Cyc (R := R) Y q) :
    (subsetRestrictMap R (ModuleCat.of R R) N q).hom c ∈ Cyc (R := R) (TopCat.of N) q := by
  rw [mem_cyc_iff]
  rcases q with _ | q
  · rw [show (0 : ℕ) - 1 = 0 from rfl, (BM R _).shape 0 0 (by simp)]
    rfl
  · rw [mem_cyc_iff] at hz
    change ((BM R (TopCat.of N)).d (q + 1) q).hom _ = 0
    rw [d_subsetRestrictMap R _ hN hc]
    change (subsetRestrictMap R (ModuleCat.of R R) N q).hom
      (((BM R Y).d (q + 1) q).hom c) = 0
    rw [show ((BM R Y).d (q + 1) q).hom c = 0 from hz, map_zero]

/-- For cochains `χ`, `χ'` with `χ' - χ = δ η`, `η` vanishing on the simplices of `A` and on
those of `B`, and a cycle `w` all of whose simplices lie in `A`, in `B` or in a closed `L`, the
restrictions to `L` of `χ' ∩ w` and `χ ∩ w` are homologous in `L`. -/
lemma mk_restrict_capChain_eq_of_sub_mem_pairCoboundaries {A B L : Set Y} (hL : IsClosed L)
    (m q n : ℕ) (h : m + q = n) {χ χ' : Simplex Y m → R}
    (hχ : χ' - χ ∈ pairCoboundaries R A B m) (w : Cyc (R := R) Y n)
    (hw : ∀ σ, coeff R w.1 σ ≠ 0 → singularSimplexImage Y σ ⊆ A ∨
      singularSimplexImage Y σ ⊆ B ∨ singularSimplexImage Y σ ⊆ L)
    (hc : (subsetRestrictMap R (ModuleCat.of R R) L q).hom (capChain R m q n h χ w.1) ∈
      Cyc (R := R) (TopCat.of L) q)
    (hc' : (subsetRestrictMap R (ModuleCat.of R R) L q).hom (capChain R m q n h χ' w.1) ∈
      Cyc (R := R) (TopCat.of L) q) :
    (Submodule.Quotient.mk ⟨_, hc'⟩ : HomQ (R := R) (TopCat.of L) q) =
      Submodule.Quotient.mk ⟨_, hc⟩ := by
  rcases m with _ | m
  · have : χ' = χ := sub_eq_zero.1 hχ
    subst this
    rfl
  obtain ⟨η, hη, he⟩ := hχ
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine (Submodule.Quotient.eq _).2 ?_
  set u := -((-1 : ℤ) ^ q • capChain R m (q + 1) (n + 1) (by omega) η w.1)
  have hu : IsSupportedIn R (ModuleCat.of R R) L u :=
    isSupportedIn_neg (isSupportedIn_zsmul (fun τ hτ ↦
      singularSimplexImage_subset_of_coeff_capChain_ne_zero_of_three m (q + 1) (n + 1) _ hη.1 hη.2
        w.1 hw hτ) _)
  refine mem_bdry_of _ ((subsetRestrictMap R (ModuleCat.of R R) L (q + 1)).hom u) ?_
  rw [d_subsetRestrictMap R _ hL hu]
  have key := d_neg_zsmul_capChain_cyc m q n (by omega) η w
  change _ = (subsetRestrictMap R (ModuleCat.of R R) L q).hom
      (capChain R (m + 1) q (n + 1) h χ' w.1) -
    (subsetRestrictMap R (ModuleCat.of R R) L q).hom (capChain R (m + 1) q (n + 1) h χ w.1)
  rw [← map_sub, ← LinearMap.sub_apply, ← map_sub, ← he]
  exact congrArg _ key

section cup

/-! ### The cap product with a cup product, on cocycles modulo coboundaries -/

variable {A B N L : Set Y}

/-- If `A` and `B` are open, every member of `{A, B ∩ int N, int L ∩ int N}` is open. -/
lemma cupCover_isOpen (hA : IsOpen A) (hB : IsOpen B) :
    ∀ U ∈ ({A, B ∩ interior N, interior L ∩ interior N} : Set (Set Y)), IsOpen U := by
  rintro U (rfl | rfl | rfl)
  · exact hA
  · exact hB.inter isOpen_interior
  · exact isOpen_interior.inter isOpen_interior

/-- If `A ∪ int N` and `A ∪ B ∪ int L` are the whole space, then so is the union of
`{A, B ∩ int N, int L ∩ int N}`. -/
lemma cupCover_sUnion (hAN : A ∪ interior N = univ) (hABL : A ∪ B ∪ interior L = univ) :
    ⋃₀ ({A, B ∩ interior N, interior L ∩ interior N} : Set (Set Y)) = univ := by
  refine eq_univ_of_forall fun y ↦ ?_
  simp only [sUnion_insert, sUnion_singleton, mem_union, mem_inter_iff]
  by_cases hy : y ∈ A
  · exact Or.inl hy
  have hN : y ∈ interior N := (eq_univ_iff_forall.1 hAN y).resolve_left hy
  rcases eq_univ_iff_forall.1 hABL y with (h | h) | h
  · exact absurd h hy
  · exact Or.inr (Or.inl ⟨h, hN⟩)
  · exact Or.inr (Or.inr ⟨h, hN⟩)

/-- **The cap product with a cup product, for neighbourhood cap products.** Let `A`, `B` be open
and `N`, `L` closed in `Y` with `B ∪ int N = Y` and `A ∪ B ∪ int L = Y`, `ι : N → Y` the
inclusion. For `x ∈ H^p(Y, A)`, `y ∈ H^q(Y, B)` and `b ∈ H_n Y`, the push-forward along
`ι⁻¹ L → L` of `ι^* x ∩_{ι⁻¹ L} (y ∩_N b)` is `(x ∪ y) ∩_L b`. On chains: subdivide a cycle `z`
towards `{B, A ∩ int N, int L ∩ int N}` into `w`; then `(φ ∪ ψ) ∩ w = φ ∩ (ψ ∩ w)`, and `w`
computes all three neighbourhood cap products. -/
theorem homologyMap_preimageRestrict_capHomQNbhd_capHomQNbhd (hA : IsOpen A) (hB : IsOpen B)
    (hN : IsClosed N) (hL : IsClosed L) (hBN : B ∪ interior N = univ)
    (hABL : A ∪ B ∪ interior L = univ)
    (hA' : IsOpen (subsetInclusion N ⁻¹' A)) (hL' : IsClosed (subsetInclusion N ⁻¹' L))
    (hAL' : subsetInclusion N ⁻¹' A ∪ interior (subsetInclusion N ⁻¹' L) = univ)
    (p q l m n : ℕ) (h₁ : q + m = n) (h₂ : p + l = m) (h : p + q + l = n)
    (x : relCohomology R A p) (y : relCohomology R B q) (b : HomQ (R := R) Y n) :
    (homologyMap R (chainMap R (ModuleCat.of R R)
        (preimageRestrict (subsetInclusion N) (subset_refl L))
        (isProperMap_preimageRestrict _ (isProperMap_subsetInclusion hN) hL _)) l).hom
      ((homologyEquiv R (TopCat.of (subsetInclusion N ⁻¹' L)) l).symm
        (capHomQNbhd R hA' hL' hAL' p l m h₂
          (relCohomologyMap R (subsetInclusion N) subset_rfl p x)
          (capHomQNbhd R hB hN hBN q m n h₁ y b))) =
      (homologyEquiv R (TopCat.of L) l).symm
        (capHomQNbhd R (hA.union hB) hL hABL (p + q) l n h
          (relCup (R := R) hA hB p q (p + q) rfl x y) b) := by
  induction x using Submodule.Quotient.induction_on with | H φ => ?_
  induction y using Submodule.Quotient.induction_on with | H ψ => ?_
  induction b using Submodule.Quotient.induction_on with | H z => ?_
  have hBAL : B ∪ A ∪ interior L = univ := by rw [union_comm B A]; exact hABL
  set 𝒲 : Set (Set Y) := {B, A ∩ interior N, interior L ∩ interior N}
  set w : (BM R Y).X n := ((smallChainMapLF R (ModuleCat.of R R) 𝒲).f n).hom z.1 with hw_def
  have hwc : w ∈ Cyc (R := R) Y n := chainMap_mem_cyc R _ z
  have hsm : ∀ σ, coeff R w σ ≠ 0 → singularSimplexImage Y σ ⊆ B ∨
      singularSimplexImage Y σ ⊆ A ∩ interior N ∨
        singularSimplexImage Y σ ⊆ interior L ∩ interior N := by
    intro σ hσ
    obtain ⟨U, hU, hσU⟩ := smallChainMapLF_small R (ModuleCat.of R R) (cupCover_isOpen hB hA)
      (cupCover_sUnion hBN hBAL) n z.1 hσ
    rcases hU with rfl | rfl | rfl
    · exact Or.inl hσU
    · exact Or.inr (Or.inl hσU)
    · exact Or.inr (Or.inr hσU)
  have hu := sub_smallChainMapLF_eq_d (R := R) 𝒲 z.2
  -- the inner cap product `ψ ∩ w`, a cycle of `N`
  have hsN : IsSupportedIn R (ModuleCat.of R R) N (capChain R q m n h₁ ψ.1 w) := fun τ hτ ↦
    (singularSimplexImage_subset_of_coeff_capChain_ne_zero q m n h₁ ψ.2.1 w (fun σ hσ ↦
      (hsm σ hσ).imp_right fun h ↦ h.elim (fun h ↦ h.trans inter_subset_right)
        (fun h ↦ h.trans inter_subset_right)) hτ).trans interior_subset
  set e := (subsetRestrictMap R (ModuleCat.of R R) N m).hom (capChain R q m n h₁ ψ.1 w)
  have he : e ∈ Cyc (R := R) (TopCat.of N) m :=
    subsetRestrictMap_mem_cyc hN hsN (capChain_mem_cyc B q m n h₁ ψ ⟨w, hwc⟩)
  have e1 := mk_restrict_capChain_of_small hB hN hBN q m n h₁ ψ z w (fun σ hσ ↦ by
    rcases hsm σ hσ with h0 | h0 | h0
    · exact ⟨B, Or.inl rfl, h0⟩
    · exact ⟨_, Or.inr rfl, h0.trans inter_subset_right⟩
    · exact ⟨_, Or.inr rfl, h0.trans inter_subset_right⟩) _ hu he
  -- the simplices of `e` lie in `ι⁻¹ A` or in `int ι⁻¹ L`
  have hes : ∀ σ, coeff R e σ ≠ 0 → ∃ U ∈ ({subsetInclusion N ⁻¹' A,
      interior (subsetInclusion N ⁻¹' L)} : Set (Set (TopCat.of N))),
        singularSimplexImage (TopCat.of N) σ ⊆ U := by
    intro σ hσ
    have hσ' : coeff R (capChain R q m n h₁ ψ.1 w)
        ((TopCat.toSSet.map (subsetInclusion N)).app _ σ) ≠ 0 := by
      have := subsetRestrictMap_apply_coe R (ModuleCat.of R R) (N := N)
        (capChain R q m n h₁ ψ.1 w) σ
      exact fun h0 ↦ hσ (this.trans h0)
    obtain ⟨σ₀, hσ₀, hwt, hsub⟩ := exists_of_coeff_capChain_ne_zero q m n h₁ ψ.1 w hσ'
    rw [singularSimplexImage_map_subsetInclusion, image_subset_iff] at hsub
    rcases hsm σ₀ hσ₀ with h0 | h0 | h0
    · exact absurd (wt_eq_zero_of_vanishing _ ψ.2.1 h0) hwt
    · exact ⟨_, Or.inl rfl, hsub.trans (preimage_mono (h0.trans inter_subset_left))⟩
    · exact ⟨_, Or.inr rfl, hsub.trans ((preimage_mono (h0.trans inter_subset_left)).trans
        (preimage_interior_subset_interior_preimage continuous_subtype_val))⟩
  -- the outer cap product `ι^* φ ∩ e`, a cycle of `ι⁻¹ L`
  set φ' : relCocycles R (subsetInclusion N ⁻¹' A) p :=
    ⟨cochainPullback R (subsetInclusion N) p φ.1,
      cochainPullback_mem_relCocycles _ subset_rfl φ.2⟩
  have hsL' : IsSupportedIn R (ModuleCat.of R R) (subsetInclusion N ⁻¹' L)
      (capChain R p l m h₂ φ'.1 e) := fun τ hτ ↦
    (singularSimplexImage_subset_of_coeff_capChain_ne_zero p l m h₂ φ'.2.1 e (fun σ hσ ↦ by
      obtain ⟨U, hU, hσU⟩ := hes σ hσ
      rcases hU with rfl | rfl
      exacts [Or.inl hσU, Or.inr hσU]) hτ).trans interior_subset
  set e' := (subsetRestrictMap R (ModuleCat.of R R) (subsetInclusion N ⁻¹' L) l).hom
    (capChain R p l m h₂ φ'.1 e)
  have he' : e' ∈ Cyc (R := R) (TopCat.of (subsetInclusion N ⁻¹' L)) l :=
    subsetRestrictMap_mem_cyc hL' hsL' (capChain_mem_cyc _ p l m h₂ φ' ⟨e, he⟩)
  have e2 := mk_restrict_capChain_of_small hA' hL' hAL' p l m h₂ φ' ⟨e, he⟩ e hes 0
    (by rw [sub_self, map_zero]) he'
  -- the cap product with the cup product
  set χ := cup p q (p + q) rfl φ.1 ψ.1
  have hχδ : coboundary R (p + q) χ = 0 := coboundary_cup_eq_zero p q (p + q) rfl φ.2.2 ψ.2.2
  set Φ := relCupCocycles hA hB p q (p + q) rfl φ ψ
  have hsR : IsSupportedIn R (ModuleCat.of R R) L (capChain R (p + q) l n h Φ.1 w) := fun τ hτ ↦
    (singularSimplexImage_subset_of_coeff_capChain_ne_zero (p + q) l n h Φ.2.1 w (fun σ hσ ↦ by
      rcases hsm σ hσ with h0 | h0 | h0
      · exact Or.inl (h0.trans subset_union_right)
      · exact Or.inl ((h0.trans inter_subset_left).trans subset_union_left)
      · exact Or.inr (h0.trans inter_subset_left)) hτ).trans interior_subset
  have hcR := subsetRestrictMap_mem_cyc hL hsR (capChain_mem_cyc _ (p + q) l n h Φ ⟨w, hwc⟩)
  have e3 := mk_restrict_capChain_of_small (hA.union hB) hL hABL (p + q) l n h Φ z w
    (fun σ hσ ↦ by
      rcases hsm σ hσ with h0 | h0 | h0
      · exact ⟨_, Or.inl rfl, h0.trans subset_union_right⟩
      · exact ⟨_, Or.inl rfl, (h0.trans inter_subset_left).trans subset_union_left⟩
      · exact ⟨_, Or.inr rfl, h0.trans inter_subset_left⟩) _ hu hcR
  have hw3 : ∀ σ, coeff R w σ ≠ 0 → singularSimplexImage Y σ ⊆ A ∨
      singularSimplexImage Y σ ⊆ B ∨ singularSimplexImage Y σ ⊆ L := fun σ hσ ↦ by
    rcases hsm σ hσ with h0 | h0 | h0
    · exact Or.inr (Or.inl h0)
    · exact Or.inl (h0.trans inter_subset_left)
    · exact Or.inr (Or.inr ((h0.trans inter_subset_left).trans interior_subset))
  have hsχ : IsSupportedIn R (ModuleCat.of R R) L (capChain R (p + q) l n h χ w) := fun τ hτ ↦
    singularSimplexImage_subset_of_coeff_capChain_ne_zero_of_three (p + q) l n h
      (cup_mem_vanishing rfl φ.2.1 ψ.2.1).1 (cup_mem_vanishing rfl φ.2.1 ψ.2.1).2 w hw3 hτ
  have hcχ := subsetRestrictMap_mem_cyc hL hsχ (capChain_mem_cyc A (p + q) l n h
    ⟨χ, (cup_mem_vanishing rfl φ.2.1 ψ.2.1).1, hχδ⟩ ⟨w, hwc⟩)
  have e4 := mk_restrict_capChain_eq_of_sub_mem_pairCoboundaries hL (p + q) l n h
    (χ := χ) (χ' := Φ.1) (pullback_smallChainMap_sub_mem_pairCoboundaries A B hχδ) ⟨w, hwc⟩
    hw3 hcχ hcR
  have i1 := (capHomQNbhd_mk hB hN hBN q m n h₁ ψ z).trans e1.symm
  have i2 := (capHomQNbhd_mk hA' hL' hAL' p l m h₂ φ' ⟨e, he⟩).trans e2.symm
  have i3 := ((congrArg (fun t ↦ capHomQNbhd R (hA.union hB) hL hABL (p + q) l n h t
    (Submodule.Quotient.mk z)) (relCup_mk hA hB p q (p + q) rfl φ ψ)).trans
    (capHomQNbhd_mk (hA.union hB) hL hABL (p + q) l n h Φ z)).trans (e3.symm.trans e4)
  rw [i1, relCohomologyMap_mk, i3]
  refine (congrArg (fun t ↦ (homologyMap R (chainMap R (ModuleCat.of R R)
      (preimageRestrict (subsetInclusion N) (subset_refl L))
      (isProperMap_preimageRestrict _ (isProperMap_subsetInclusion hN) hL _)) l).hom
        ((homologyEquiv R (TopCat.of (subsetInclusion N ⁻¹' L)) l).symm t)) i2).trans ?_
  refine (homologyMap_homologyEquiv_symm_mk R _ l ⟨e', he'⟩).trans ?_
  congr 2
  apply Subtype.ext
  change ((chainMap R (ModuleCat.of R R) (preimageRestrict (subsetInclusion N) (subset_refl L))
      (isProperMap_preimageRestrict _ (isProperMap_subsetInclusion hN) hL _)).f l).hom e' =
    (subsetRestrictMap R (ModuleCat.of R R) L l).hom (capChain R (p + q) l n h χ w)
  rw [chainMap_preimageRestrict_subsetRestrictMap R (subsetInclusion N)
    (isProperMap_subsetInclusion hN) hL hL (subset_refl L) hsL', chainMap_capChain,
    chainMap_subsetRestrictMap R _ hN hsN, capChain_cup p q l m n h₁ h₂ h]

/-- `homologyMap_preimageRestrict_capHomQNbhd_capHomQNbhd` with the degrees and the support of
the cup product written as they come out of the integer-graded cap and cup products. -/
theorem congrDegree_homologyMap_capHomQNbhd_capHomQNbhd (hA : IsOpen A) (hB : IsOpen B)
    (hN : IsClosed N) (hL : IsClosed L) (hBN : B ∪ interior N = univ)
    (hABL : A ∪ B ∪ interior L = univ)
    (hA' : IsOpen (subsetInclusion N ⁻¹' A)) (hL' : IsClosed (subsetInclusion N ⁻¹' L))
    (hAL' : subsetInclusion N ⁻¹' A ∪ interior (subsetInclusion N ⁻¹' L) = univ)
    {S : Set Y} (hS : A ∪ B = S) (hSo : IsOpen S) (hSL : S ∪ interior L = univ)
    (p q n m₀ m l s l' : ℕ) (h₁ : q + m₀ = n) (h₂ : p + l = m) (h : s + l' = n)
    (hm : (m₀ : ℤ) = m) (hs : ((p + q : ℕ) : ℤ) = s) (hl : (l : ℤ) = l')
    (x : relCohomology R A p) (y : relCohomology R B q) (b : HomQ (R := R) Y n) :
    congrDegree R (TopCat.of L) hl ((homologyMap R (chainMap R (ModuleCat.of R R)
        (preimageRestrict (subsetInclusion N) (subset_refl L))
        (isProperMap_preimageRestrict _ (isProperMap_subsetInclusion hN) hL _)) l).hom
      ((homologyEquiv R (TopCat.of (subsetInclusion N ⁻¹' L)) l).symm
        (capHomQNbhd R hA' hL' hAL' p l m h₂
          (relCohomologyMap R (subsetInclusion N) subset_rfl p x)
          (homologyEquiv R (TopCat.of N) m (congrDegree R (TopCat.of N) hm
            ((homologyEquiv R (TopCat.of N) m₀).symm (capHomQNbhd R hB hN hBN q m₀ n h₁ y b))))))) =
      (homologyEquiv R (TopCat.of L) l').symm
        (capHomQNbhd R hSo hL hSL s l' n h
          (relativeSingularCohomologyEquiv R S s (cohomologyWithSupports.congrIndex R Y hS hs
            ((relativeSingularCohomologyEquiv R (A ∪ B) (p + q)).symm
              (relCup (R := R) hA hB p q (p + q) rfl x y)))) b) := by
  obtain rfl : m₀ = m := Nat.cast_injective hm
  obtain rfl : p + q = s := Nat.cast_injective hs
  obtain rfl : l = l' := Nat.cast_injective hl
  subst hS
  rw [congrDegree_self, congrDegree_self, LinearEquiv.refl_apply, LinearEquiv.refl_apply,
    LinearEquiv.apply_symm_apply, cohomologyWithSupports.congrIndex_rfl,
    LinearEquiv.apply_symm_apply]
  exact homologyMap_preimageRestrict_capHomQNbhd_capHomQNbhd hA hB hN hL hBN hABL hA' hL' hAL'
    p q l m₀ n h₁ h₂ (by omega) x y b

end cup

end BorelMooreCap

namespace borelMooreHomology

open BorelMooreCap BorelMooreCross SingularCochain

variable (R : Type u) [CommRing R]

/-- Transporting a Borel–Moore homology class along `i = i'` and then along `i' = i''` is
transporting it along `i = i''`. -/
lemma congrDegree_congrDegree (X : TopCat.{u}) {i i' i'' : ℤ} (h₁ : i = i') (h₂ : i' = i'')
    (x : borelMooreHomology R (ModuleCat.of R R) X i) :
    congrDegree R X h₂ (congrDegree R X h₁ x) = congrDegree R X (h₁.trans h₂) x := by
  subst h₁ h₂
  rfl

/-- The neighbourhood cap product `H^j(Y, Y - X) × H_k Y → H_{k-j} N` vanishes unless
`0 ≤ j ≤ k`. -/
lemma capProductNbhd_of_not (Y : TopCat.{u}) {X N : Set Y} (hX : IsClosed X) (hN : IsClosed N)
    (hXN : X ⊆ interior N) {j k : ℤ} (h : ¬ (0 ≤ j ∧ j ≤ k)) :
    capProductNbhd R Y hX hN hXN j k = 0 := by
  rw [capProductNbhd, dite_eq_right_of_eq_false (eq_false h)]

/-- **The cap product with a cup product, for neighbourhood cap products.** Let `X`, `W`, `N`,
`L` be closed in `Y` with `W ⊆ int N`, `X ∩ W ⊆ int L` and `ι⁻¹ X ⊆ int ι⁻¹ L`, `ι : N → Y` the
inclusion. For `u ∈ H^i(Y, Y - X)`, `v ∈ H^j(Y, Y - W)` and `a ∈ H_k Y`, the push-forward along
`ι⁻¹ L → L` of `ι^* u ∩_{ι⁻¹ L} (v ∩_N a)` is `(u ∪ v) ∩_L a`. -/
theorem pushforward_preimageRestrict_capProductNbhd_capProductNbhd (Y : TopCat.{u})
    {X W N L : Set Y} (hX : IsClosed X) (hW : IsClosed W) (hN : IsClosed N) (hL : IsClosed L)
    (hWN : W ⊆ interior N) (hXWL : X ∩ W ⊆ interior L)
    (hXL : subsetInclusion N ⁻¹' X ⊆ interior (subsetInclusion N ⁻¹' L)) (i j k : ℤ)
    (u : cohomologyWithSupports R (ModuleCat.of R R) Y X i)
    (v : cohomologyWithSupports R (ModuleCat.of R R) Y W j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    (pushforward R (ModuleCat.of R R) (preimageRestrict (subsetInclusion N) (subset_refl L))
        (isProperMap_preimageRestrict _ (isProperMap_subsetInclusion hN) hL _) (k - j - i)).hom
      (capProductNbhd R (TopCat.of N) (hX.preimage (subsetInclusion N).hom.continuous)
        (hL.preimage (subsetInclusion N).hom.continuous) hXL i (k - j)
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (subsetInclusion N) X i).hom u)
        (capProductNbhd R Y hW hN hWN j k v a)) =
      congrDegree R (TopCat.of L) (by ring) (capProductNbhd R Y (hX.inter hW) hL hXWL (i + j) k
        (cohomologyWithSupports.cup R Y hX hW i j u v) a) := by
  by_cases hg : 0 ≤ i ∧ 0 ≤ j ∧ i + j ≤ k
  · have hBN := compl_union_interior_eq_univ hWN
    have hABL : Xᶜ ∪ Wᶜ ∪ interior L = univ := by
      rw [← compl_inter]; exact compl_union_interior_eq_univ hXWL
    unfold capProductNbhd cohomologyWithSupports.cup
    rw [dite_eq_left_of_eq_true (eq_true (show 0 ≤ j ∧ j ≤ k by omega)),
      dite_eq_left_of_eq_true (eq_true (show 0 ≤ i ∧ i ≤ k - j by omega)),
      dite_eq_left_of_eq_true (eq_true (show 0 ≤ i + j ∧ i + j ≤ k by omega)),
      dite_eq_left_of_eq_true (eq_true (show 0 ≤ i ∧ 0 ≤ j by omega))]
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
      LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply, congrDegree_symm,
      pushforward_eq_homologyMap]
    rw [congrDegree_congrDegree, congrDegree_congrDegree, homologyMap_congrDegree,
      cohomologyWithSupports.congrIndex_congrIndex, cohomologyWithSupports.congrIndex_pullback,
      cohomologyWithSupports.pullback]
    erw [relativeSingularCohomologyEquiv_map]
    simp only [cohomologyWithSupports.cupNat, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
      LinearEquiv.coe_coe]
    refine Eq.trans ?_ (congrArg (congrDegree R (TopCat.of L) (by omega))
      (congrDegree_homologyMap_capHomQNbhd_capHomQNbhd hX.isOpen_compl hW.isOpen_compl hN hL hBN
        hABL (hX.isOpen_compl.preimage (subsetInclusion N).hom.continuous)
        (hL.preimage (subsetInclusion N).hom.continuous) (compl_union_interior_eq_univ hXL)
        (compl_inter X W).symm (hX.inter hW).isOpen_compl (compl_union_interior_eq_univ hXWL)
        i.toNat j.toNat k.toNat (k.toNat - j.toNat) (k - j).toNat ((k - j).toNat - i.toNat)
        (i + j).toNat (k.toNat - (i + j).toNat) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) _ _ _))
    rw [congrDegree_congrDegree]
  · have hR : capProductNbhd R Y (hX.inter hW) hL hXWL (i + j) k
        (cohomologyWithSupports.cup R Y hX hW i j u v) a = 0 := by
      by_cases hc : 0 ≤ i ∧ 0 ≤ j
      · rw [capProductNbhd_of_not R Y _ hL hXWL (by omega)]
        rfl
      · rw [cohomologyWithSupports.cup_of_neg R Y hX hW (by omega)]
        simp
    have hL0 : capProductNbhd R (TopCat.of N) (hX.preimage (subsetInclusion N).hom.continuous)
        (hL.preimage (subsetInclusion N).hom.continuous) hXL i (k - j)
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (subsetInclusion N) X i).hom u)
        (capProductNbhd R Y hW hN hWN j k v a) = 0 := by
      by_cases hj : 0 ≤ j ∧ j ≤ k
      · rw [capProductNbhd_of_not R (TopCat.of N) _ _ hXL (by omega)]
        rfl
      · rw [capProductNbhd_of_not R Y hW hN hWN hj]
        simp
    rw [hR, hL0, map_zero, map_zero]

end borelMooreHomology

end MMP
