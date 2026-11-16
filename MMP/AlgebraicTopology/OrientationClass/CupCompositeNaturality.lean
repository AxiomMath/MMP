module

public import MMP.AlgebraicTopology.ThomClass.Natural
public import MMP.AlgebraicTopology.CapProduct.Cup
public import MMP.AlgebraicTopology.PoincareDuality.Excision

/-!
# Naturality of the cup product (Fulton, §19.1)

Let `g : Y' → Y` be continuous, `X, W ⊆ Y` and `X', W' ⊆ Y'` closed with `g⁻¹ X ⊆ X'` and
`g⁻¹ W ⊆ W'`. Then `g` is a map of pairs `(Y', Y' - X') → (Y, Y - X)`, and likewise for `W` and
for `X ∩ W`, and the cup product commutes with the induced maps:
`g^* (u ∪ v) = g^* u ∪ g^* v` in `H^{i+j}(Y', Y' - (X' ∩ W'))`.

On cochains the Alexander–Whitney product is natural, `g^* (φ ∪ ψ) = g^* φ ∪ g^* ψ`, since `g`
commutes with taking front and back faces. The cup product of classes is the class of
`ρ^* (φ ∪ ψ)`, `ρ` the small-chains map of the open couple `{A, B} = {Y - X, Y - W}`, and the
small-chains map `ρ'` of `{A', B'} = {Y' - X', Y' - W'}` is a different one; but for a cocycle `θ`
vanishing on `A` and on `B`, `ρ^* θ - θ = δ γ` with `γ` vanishing on `A` and on `B`, so
`g^* ρ^* θ - g^* θ` is the coboundary of a cochain vanishing on `A'` and on `B'`, and its pull-back
by `ρ'` is a relative coboundary of `A' ∪ B'`. Finally `ρ'^* x - x` is a relative coboundary of
`A' ∪ B'` for every relative cocycle `x` of `A' ∪ B'`, as Hatcher's homotopy `D` with
`ρ' = 1 - ∂ D - D ∂` keeps chains inside `A' ∪ B'`.

## Main results

* `MMP.SingularCochain.cochainPullback_cup`: `g^* (φ ∪ ψ) = g^* φ ∪ g^* ψ`.
* `MMP.cohomologyWithSupports.relCohomologyMap_relCup`: the relative cup product
  on cocycles modulo coboundaries is natural.
* `MMP.cohomologyWithSupports.map_cup`: the cup product is natural in maps of
  pairs.
* `MMP.cohomologyWithSupports.pullback_cup`: `f^* (u ∪ v) = f^* u ∪ f^* v`.
* `MMP.cohomologyWithSupports.forget_cup`: the cup product commutes with the
  forgetful maps `H^i(Y, Y - X) → H^i(Y, Y - X')`, `X ⊆ X'`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [A. Dold, *Lectures on Algebraic Topology*][dold1995], VII.8.
* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.2.
-/

@[expose] public noncomputable section

open CategoryTheory Set Finsupp

universe u

namespace MMP

/-- If `f⁻¹ X ⊆ X'` then `f` maps `X'ᶜ` into `Xᶜ`. -/
lemma compl_subset_preimage_compl {α β : Type*} {f : α → β} {X : Set β} {X' : Set α}
    (h : f ⁻¹' X ⊆ X') : X'ᶜ ⊆ f ⁻¹' Xᶜ :=
  fun _ hy hfy ↦ hy (h hfy)

namespace SingularCochain

open SingularChain

section homotopy

variable {R : Type*} [CommRing R] {Y : Type*} [TopologicalSpace Y]

/-- If `χ` vanishes on `V`, then so does `homotopyPullback 𝒰 n χ`. -/
lemma homotopyPullback_mem_vanishing_of_mem_vanishing (𝒰 : Set (Set Y)) {V : Set Y} (n : ℕ)
    {χ : Simplex Y (n + 1) → R} (hχ : χ ∈ vanishing R (n + 1) V) :
    homotopyPullback 𝒰 n χ ∈ vanishing R n V := fun _ hτ ↦
  eval_eq_zero_of_mem_inside hχ
    (smallHomotopy_mem_inside_of_mem 𝒰 (single_mem_supported R (1 : R) hτ))

/-- For a relative cocycle `χ` of `V`, `ρ^* χ - χ` is a relative coboundary of `V`, `ρ` the
small-chains map towards any family `𝒰`. -/
lemma pullback_smallChainMap_sub_mem_relCoboundaries (𝒰 : Set (Set Y)) {V : Set Y} {m : ℕ}
    {χ : Simplex Y m → R} (hχ : χ ∈ relCocycles R V m) :
    pullback (smallChainMap R 𝒰 m) χ - χ ∈ relCoboundaries R V m := by
  have hδ : coboundary R m χ = 0 := hχ.2
  cases m with
  | zero =>
    have : pullback (smallChainMap R 𝒰 0) χ = χ := by
      ext σ
      change eval χ (smallChainMap R 𝒰 0 (single σ 1)) = χ σ
      rw [smallChainMap_zero, map_sub, ← eval_coboundary, hδ]
      simp
    rw [this, sub_self]
    exact zero_mem _
  | succ m =>
    refine ⟨-homotopyPullback 𝒰 m χ,
      neg_mem (homotopyPullback_mem_vanishing_of_mem_vanishing 𝒰 m hχ.1), ?_⟩
    ext σ
    have h1 := eval_coboundary m (homotopyPullback 𝒰 m χ) (single σ 1)
    rw [eval_homotopyPullback] at h1
    rw [map_neg, Pi.neg_apply, Pi.sub_apply]
    change _ = eval χ (smallChainMap R 𝒰 (m + 1) (single σ 1)) - χ σ
    rw [smallChainMap_succ, map_sub, map_sub, ← eval_coboundary, hδ]
    simp only [linearCombination_single, one_smul] at h1 ⊢
    rw [← h1]
    simp

end homotopy

variable {R : Type u} [CommRing R] {Y' Y : TopCat.{u}} (g : Y' ⟶ Y)

/-- The Alexander–Whitney cup product is natural: `g^* (φ ∪ ψ) = g^* φ ∪ g^* ψ`. -/
lemma cochainPullback_cup (p q n : ℕ) (h : p + q = n) (φ : Simplex Y p → R)
    (ψ : Simplex Y q → R) :
    cochainPullback R g n (cup p q n h φ ψ) =
      cup p q n h (cochainPullback R g p φ) (cochainPullback R g q ψ) := by
  ext τ
  simp only [cochainPullback_apply, cup_apply, ContinuousMap.comp_assoc]

/-- If `A' ⊆ g⁻¹ A` and `B' ⊆ g⁻¹ B`, then `g^*` maps coboundaries of cochains vanishing on `A` and
on `B` to coboundaries of cochains vanishing on `A'` and on `B'`. -/
lemma cochainPullback_mem_pairCoboundaries {A B : Set Y} {A' B' : Set Y'} (hA : A' ⊆ g ⁻¹' A)
    (hB : B' ⊆ g ⁻¹' B) {n : ℕ} {χ : Simplex Y n → R} (hχ : χ ∈ pairCoboundaries R A B n) :
    cochainPullback R g n χ ∈ pairCoboundaries R A' B' n := by
  cases n with
  | zero =>
    rw [show χ = 0 from hχ, map_zero]
    exact zero_mem _
  | succ n =>
    obtain ⟨γ, hγ, rfl⟩ := hχ
    exact ⟨_, ⟨cochainPullback_mem_vanishing g hA hγ.1, cochainPullback_mem_vanishing g hB hγ.2⟩,
      coboundary_cochainPullback g n γ⟩

/-- For a cocycle `θ` vanishing on `A` and on `B`, `g^* ρ^* θ` and `ρ'^* g^* θ` differ by a
relative coboundary of `A' ∪ B'`, `ρ`, `ρ'` the small-chains maps of `{A, B}` and `{A', B'}`. -/
lemma cochainPullback_pullback_smallChainMap_sub_mem_relCoboundaries {A B : Set Y}
    {A' B' : Set Y'} (hA : IsOpen A) (hB : IsOpen B) (hA' : IsOpen A') (hB' : IsOpen B')
    (hAA : A' ⊆ g ⁻¹' A) (hBB : B' ⊆ g ⁻¹' B) {n : ℕ} {θ : Simplex Y n → R}
    (hθ : θ ∈ vanishing R n A ⊓ vanishing R n B) (hδ : coboundary R n θ = 0) :
    cochainPullback R g n (pullback (smallChainMap R {A, B} n) θ) -
        pullback (smallChainMap R {A', B'} n) (cochainPullback R g n θ) ∈
      relCoboundaries R (A' ∪ B') n := by
  set x := cochainPullback R g n (pullback (smallChainMap R {A, B} n) θ) with hx_def
  have hx : x ∈ relCocycles R (A' ∪ B') n := by
    refine cochainPullback_mem_relCocycles g (A := A ∪ B) (union_subset_union hAA hBB) ⟨?_, ?_⟩
    · exact pullback_mem_vanishing hA hB hθ
    · change coboundary R n _ = 0
      rw [coboundary_pullback_smallChainMap, hδ, map_zero]
  have h1 := pullback_smallChainMap_sub_mem_relCoboundaries (R := R) {A', B'} hx
  have h2 : pullback (smallChainMap R {A', B'} n) (x - cochainPullback R g n θ) ∈
      relCoboundaries R (A' ∪ B') n := by
    refine pullback_smallChainMap_mem_relCoboundaries hA' hB' ?_
    rw [hx_def, ← map_sub]
    exact cochainPullback_mem_pairCoboundaries g hAA hBB
      (pullback_smallChainMap_sub_mem_pairCoboundaries A B hδ)
  rw [map_sub] at h2
  have := sub_mem h2 h1
  rw [show pullback (smallChainMap R {A', B'} n) x - pullback (smallChainMap R {A', B'} n)
      (cochainPullback R g n θ) - (pullback (smallChainMap R {A', B'} n) x - x) =
      x - pullback (smallChainMap R {A', B'} n) (cochainPullback R g n θ) by abel] at this
  exact this

end SingularCochain

namespace cohomologyWithSupports

open SingularCochain SingularChain

variable {R : Type u} [CommRing R] {Y' Y : TopCat.{u}} (g : Y' ⟶ Y)

/-- The relative cup product on cocycles modulo coboundaries is natural in maps of pairs. -/
lemma relCohomologyMap_relCup {A B : Set Y} {A' B' : Set Y'} (hA : IsOpen A) (hB : IsOpen B)
    (hA' : IsOpen A') (hB' : IsOpen B') (hAA : A' ⊆ g ⁻¹' A) (hBB : B' ⊆ g ⁻¹' B)
    (hAB : A' ∪ B' ⊆ g ⁻¹' (A ∪ B)) (p q n : ℕ) (h : p + q = n) (a : relCohomology R A p)
    (b : relCohomology R B q) :
    relCohomologyMap R g hAB n (relCup (R := R) hA hB p q n h a b) =
      relCup (R := R) hA' hB' p q n h (relCohomologyMap R g hAA p a)
        (relCohomologyMap R g hBB q b) := by
  induction a using Submodule.Quotient.induction_on with | _ x =>
  induction b using Submodule.Quotient.induction_on with | _ y =>
  rw [relCup_mk, relCohomologyMap_mk, relCohomologyMap_mk, relCohomologyMap_mk, relCup_mk,
    Submodule.Quotient.eq]
  change cochainPullback R g n (SingularCochain.pullback (smallChainMap R {A, B} n)
      (SingularCochain.cup p q n h x.1 y.1)) -
    SingularCochain.pullback (smallChainMap R {A', B'} n)
      (SingularCochain.cup p q n h (cochainPullback R g p x.1) (cochainPullback R g q y.1)) ∈
        relCoboundaries R (A' ∪ B') n
  rw [← cochainPullback_cup]
  exact cochainPullback_pullback_smallChainMap_sub_mem_relCoboundaries g hA hB hA' hB' hAA hBB
    (cup_mem_vanishing h x.2.1 y.2.1) (coboundary_cup_eq_zero p q n h x.2.2 y.2.2)

/-- The map induced by `g` on relative cohomology commutes with the identifications `congrIndex`
along equalities of subspaces and degrees. -/
lemma map_congrIndex {S S' : Set Y} {T T' : Set Y'} {k k' : ℤ} (hS : S = S') (hT : T = T')
    (hk : k = k') (hTS : T ⊆ g ⁻¹' S) (hTS' : T' ⊆ g ⁻¹' S')
    (x : relativeSingularCohomology R (ModuleCat.of R R) Y S k) :
    (relativeSingularCohomology.map R (ModuleCat.of R R) g hTS' k').hom (congrIndex R Y hS hk x) =
      congrIndex R Y' hT hk
        ((relativeSingularCohomology.map R (ModuleCat.of R R) g hTS k).hom x) := by
  subst hS hT hk
  rfl

/-- Under `relativeSingularCohomologyEquiv`, the map induced by `g` on relative singular cohomology
is `relCohomologyMap`. -/
lemma map_relativeSingularCohomologyEquiv_symm {A' : Set Y'} {A : Set Y} (h : A' ⊆ g ⁻¹' A)
    (n : ℕ) (y : relCohomology R A n) :
    (relativeSingularCohomology.map R (ModuleCat.of R R) g h n).hom
        ((relativeSingularCohomologyEquiv R A n).symm y) =
      (relativeSingularCohomologyEquiv R A' n).symm (relCohomologyMap R g h n y) := by
  rw [LinearEquiv.eq_symm_apply, relativeSingularCohomologyEquiv_map, LinearEquiv.apply_symm_apply]

/-- **Naturality of the cup product** (Fulton, §19.1): for `g : Y' → Y` continuous and closed
`X, W ⊆ Y`, `X', W' ⊆ Y'` with `g⁻¹ X ⊆ X'`, `g⁻¹ W ⊆ W'`, the maps of pairs induced by `g`
satisfy `g^* (u ∪ v) = g^* u ∪ g^* v` in `H^{i+j}(Y', Y' - (X' ∩ W'))`. -/
theorem map_cup {X W : Set Y} {X' W' : Set Y'} (hX : IsClosed X) (hW : IsClosed W)
    (hX' : IsClosed X') (hW' : IsClosed W') (hgX : g ⁻¹' X ⊆ X') (hgW : g ⁻¹' W ⊆ W') (i j : ℤ)
    (a : cohomologyWithSupports R (ModuleCat.of R R) Y X i)
    (b : cohomologyWithSupports R (ModuleCat.of R R) Y W j) :
    (relativeSingularCohomology.map R (ModuleCat.of R R) g
        (compl_subset_preimage_compl (inter_subset_inter hgX hgW)) (i + j)).hom
        (cup R Y hX hW i j a b) =
      cup R Y' hX' hW' i j
        ((relativeSingularCohomology.map R (ModuleCat.of R R) g
          (compl_subset_preimage_compl hgX) i).hom a)
        ((relativeSingularCohomology.map R (ModuleCat.of R R) g
          (compl_subset_preimage_compl hgW) j).hom b) := by
  by_cases hij : 0 ≤ i ∧ 0 ≤ j
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hij.1
    obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hij.2
    have hAB : X'ᶜ ∪ W'ᶜ ⊆ g ⁻¹' (Xᶜ ∪ Wᶜ) :=
      union_subset_union (compl_subset_preimage_compl hgX) (compl_subset_preimage_compl hgW)
    rw [cup_natCast_eq R Y hX hW p q (p + q) rfl, cup_natCast_eq R Y' hX' hW' p q (p + q) rfl,
      map_congrIndex g (compl_inter X W).symm (compl_inter X' W').symm _ hAB,
      map_relativeSingularCohomologyEquiv_symm, relCohomologyMap_relCup g _ _ _ _
        (compl_subset_preimage_compl hgX) (compl_subset_preimage_compl hgW),
      relativeSingularCohomologyEquiv_map, relativeSingularCohomologyEquiv_map]
  · rw [cup_of_neg R Y hX hW (by omega), cup_of_neg R Y' hX' hW' (by omega)]
    simp

/-- The cup product commutes with pull-back: `f^* (u ∪ v) = f^* u ∪ f^* v` in
`H^{i+j}(Y', Y' - f⁻¹ (X ∩ W))`, `f⁻¹ (X ∩ W) = f⁻¹ X ∩ f⁻¹ W`. -/
theorem pullback_cup {X W : Set Y} (hX : IsClosed X) (hW : IsClosed W) (i j : ℤ)
    (a : cohomologyWithSupports R (ModuleCat.of R R) Y X i)
    (b : cohomologyWithSupports R (ModuleCat.of R R) Y W j) :
    (pullback R (ModuleCat.of R R) g (X ∩ W) (i + j)).hom (cup R Y hX hW i j a b) =
      cup R Y' (hX.preimage g.hom.continuous) (hW.preimage g.hom.continuous) i j
        ((pullback R (ModuleCat.of R R) g X i).hom a)
        ((pullback R (ModuleCat.of R R) g W j).hom b) :=
  map_cup g hX hW _ _ subset_rfl subset_rfl i j a b

/-- The cup product commutes with the forgetful maps: for `X ⊆ X'`, `W ⊆ W'`,
`(u ∪ v)|_{X' ∩ W'} = u|_{X'} ∪ v|_{W'}`. -/
theorem forget_cup {X W X' W' : Set Y} (hX : IsClosed X) (hW : IsClosed W) (hX' : IsClosed X')
    (hW' : IsClosed W') (hXX : X ⊆ X') (hWW : W ⊆ W') (i j : ℤ)
    (a : cohomologyWithSupports R (ModuleCat.of R R) Y X i)
    (b : cohomologyWithSupports R (ModuleCat.of R R) Y W j) :
    (forget R (ModuleCat.of R R) Y (inter_subset_inter hXX hWW) (i + j)).hom
        (cup R Y hX hW i j a b) =
      cup R Y hX' hW' i j ((forget R (ModuleCat.of R R) Y hXX i).hom a)
        ((forget R (ModuleCat.of R R) Y hWW j).hom b) :=
  map_cup (𝟙 Y) hX hW hX' hW' hXX hWW i j a b

end cohomologyWithSupports

end MMP
