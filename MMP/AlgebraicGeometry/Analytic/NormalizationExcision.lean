module

public import MMP.AlgebraicGeometry.Analytic.AnalyticMapOpenSubscheme
public import MMP.AlgebraicGeometry.Analytic.SupportedDuality

/-!
# Ordinary rational normalization excision

Let `R` be a reduced projective complex scheme, `ν : N ⟶ R` its normalization (a finite
morphism) and `A ⊆ R` a closed subset outside of which `ν` is an isomorphism; put
`F = ν⁻¹(A)` with its reduced structure. Write `X(ℂ)` for the underlying space of a complex
scheme with the classical topology. Since `ν` is finite, the sequence of constructible sheaves
`0 → ℚ_R → ν_*ℚ_N ⊕ ℚ_A → ν_*ℚ_F → 0` is exact, and its cohomology sequence is the long exact
sequence of rational singular cohomology
`⋯ → H^p(N) ⊕ H^p(A) → H^p(F) → H^{p+1}(R) → H^{p+1}(N) ⊕ H^{p+1}(A) → H^{p+1}(F) → ⋯`,
starting with `0 → H^0(R)`; dually, the rational homology of these compact spaces fits into
`⋯ → H_{k+1}(A) ⊕ H_{k+1}(N) → H_{k+1}(R) → H_k(F) → H_k(A) ⊕ H_k(N) → H_k(R) → ⋯`.
The map `H^{p}(N) ⊕ H^{p}(A) → H^{p}(F)` is pullback from `A` minus restriction from `N`, and
`H_k(F) → H_k(A) ⊕ H_k(N)` is its dual. The connecting maps are those of the localization
diagram: `ν` induces an isomorphism `H^*(R, A) ≅ H^*(N, F)` of relative cohomology, and
`H^p(F) → H^{p+1}(R)` is the coboundary `H^p(F) → H^{p+1}(N, F)`, followed by the inverse of
this isomorphism and the forgetful map `H^{p+1}(R, A) → H^{p+1}(R)`; in homology, `ν` induces an
isomorphism `H^BM_*(N - F) ≅ H^BM_*(R - A)` and `H_{k+1}(R) → H_k(F)` is the restriction to
`R - A`, followed by the inverse of this isomorphism and the Borel–Moore connecting map
`H^BM_{k+1}(N - F) → H_k(F)` of the closed subset `F ⊆ N`.

No mixed Hodge structure is involved: these are ordinary sequences of `ℚ`-vector spaces.

## Main results

* `MMP.Analytic.exact_normalization_excision`: the two long exact sequences, with their
  connecting maps.

## Implementation notes

* The spaces are `MMP.UnderlyingSpace ℂ X`; the points `A(ℂ)` and `F(ℂ)` are
  `MMP.UnderlyingSpace.pointsOver A ⊆ R(ℂ)` and its preimage in `N(ℂ)`, as
  subspaces. These are the classical spaces of the reduced closed subschemes on `A` and
  `ν⁻¹(A)`, so their cohomology is that of the reduced schemes `A` and `F`.
* Cohomology is `MMP.Fourfold.rationalCohomology`, with the pullbacks
  `MMP.Fourfold.rationalCohomologyMap`. Relative cohomology `H^*(Y, B)` is
  `MMP.cohomologyWithSupports Y Bᶜ`, with coboundary
  `MMP.cohomologyWithSupports.delta`.
* Homology is Borel–Moore homology `MMP.borelMooreHomology`, which on the compact
  spaces `R(ℂ)`, `N(ℂ)`, `A(ℂ)`, `F(ℂ)` is ordinary singular homology; it carries the
  localization connecting map `MMP.borelMooreHomology.connecting`, defined under
  the relative quasi-isomorphism `MMP.borelMooreHomology.IsRelativeQuasiIso`,
  which is asserted for `F(ℂ) ⊆ N(ℂ)`.
* The connecting maps are not given a name: each is asserted to exist together with the identity
  that determines it, given the bijectivity of the excision isomorphisms, which is asserted too.
* The normalization is described by its universal properties: `N` is normal, `ν` is finite, and
  `ν` is an isomorphism over a dense open subset of `R` whose preimage is dense in `N`.
* The auxiliary lemmas of the proof live in the namespace
  `MMP.Proof_lem_mmp_conductor_ordinary_normalization_excision`, opened only for the main result.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open MMP MMP.UnderlyingSpace
open MMP.Fourfold (rationalCohomology rationalCohomologyMap)

namespace MMP.Proof_lem_mmp_conductor_ordinary_normalization_excision

section BarrattWhitehead

variable {K : Type*} [Ring K]

private theorem exact_neg_left {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module K A] [Module K B] [Module K C] {f : A →ₗ[K] B} {g : B →ₗ[K] C}
    (h : Function.Exact f g) : Function.Exact (-f) g := by
  intro y
  rw [h y]
  constructor <;> rintro ⟨x, rfl⟩ <;> exact ⟨-x, by simp⟩

private theorem exact_neg_right {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module K A] [Module K B] [Module K C] {f : A →ₗ[K] B} {g : B →ₗ[K] C}
    (h : Function.Exact f g) : Function.Exact f (-g) := by
  intro y
  rw [← h y, LinearMap.neg_apply, neg_eq_zero]

/-- The first exactness of the Barratt–Whitehead sequence of a ladder. -/
private theorem exact_prod_coprod_neg {C₀ A B C C₀' A' B' C' : Type*}
    [AddCommGroup C₀] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup C₀'] [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    [Module K C₀] [Module K A] [Module K B] [Module K C]
    [Module K C₀'] [Module K A'] [Module K B'] [Module K C']
    (h₀ : C₀ →ₗ[K] A) (f : A →ₗ[K] B) (g : B →ₗ[K] C)
    (h₀' : C₀' →ₗ[K] A') (f' : A' →ₗ[K] B') (g' : B' →ₗ[K] C')
    (c₀ : C₀ →ₗ[K] C₀') (a : A →ₗ[K] A') (b : B →ₗ[K] B') (c : C →ₗ[K] C')
    (hc₀ : Function.Surjective c₀) (hc : Function.Injective c)
    (s₀ : ∀ x, a (h₀ x) = h₀' (c₀ x)) (s₁ : ∀ x, f' (a x) = b (f x))
    (s₂ : ∀ x, g' (b x) = c (g x))
    (e₀ : Function.Exact h₀ f) (e₁ : Function.Exact f g) (e₀' : Function.Exact h₀' f')
    (e₁' : Function.Exact f' g') :
    Function.Exact (a.prod f) (f'.coprod (-b)) := by
  rintro ⟨u, v⟩
  change f' u + -b v = 0 ↔ ∃ x, (a x, f x) = (u, v)
  constructor
  · intro huv
    have huv' : f' u = b v := add_neg_eq_zero.mp huv
    have hv : g v = 0 := hc (by rw [map_zero, ← s₂, ← huv', e₁'.apply_apply_eq_zero])
    obtain ⟨x₀, rfl⟩ := (e₁ v).1 hv
    have hu : f' (u - a x₀) = 0 := by rw [map_sub, huv', s₁, sub_self]
    obtain ⟨w, hw⟩ := (e₀' _).1 hu
    obtain ⟨w₀, rfl⟩ := hc₀ w
    refine ⟨x₀ + h₀ w₀, Prod.ext ?_ ?_⟩
    · change a (x₀ + h₀ w₀) = u
      rw [map_add, s₀, hw, add_sub_cancel]
    · change f (x₀ + h₀ w₀) = f x₀
      rw [map_add, e₀.apply_apply_eq_zero, add_zero]
  · rintro ⟨x, hx⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
    rw [s₁, add_neg_cancel]

/-- The second exactness of the Barratt–Whitehead sequence of a ladder. -/
private theorem exact_coprod_neg_comp {B C A₂ A' B' C' : Type*}
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup A₂] [AddCommGroup A'] [AddCommGroup B']
    [AddCommGroup C'] [Module K B] [Module K C] [Module K A₂] [Module K A'] [Module K B']
    [Module K C']
    (g : B →ₗ[K] C) (h : C →ₗ[K] A₂) (f' : A' →ₗ[K] B') (g' : B' →ₗ[K] C')
    (b : B →ₗ[K] B') (c : C ≃ₗ[K] C')
    (s₂ : ∀ x, g' (b x) = c (g x)) (e₂ : Function.Exact g h) (e₁' : Function.Exact f' g') :
    Function.Exact (f'.coprod (-b)) (h ∘ₗ c.symm.toLinearMap ∘ₗ g') := by
  intro y
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Set.mem_range,
    Prod.exists, LinearMap.coprod_apply, LinearMap.neg_apply]
  constructor
  · intro hy
    obtain ⟨v, hv⟩ := (e₂ _).1 hy
    obtain ⟨u, hu⟩ := (e₁' (y - b v)).1
      (by rw [map_sub, s₂, hv, LinearEquiv.apply_symm_apply, sub_self])
    exact ⟨u, -v, by rw [hu, map_neg, neg_neg, sub_add_cancel]⟩
  · rintro ⟨u, v, rfl⟩
    rw [map_add, e₁'.apply_apply_eq_zero, zero_add, map_neg, s₂, map_neg,
      LinearEquiv.symm_apply_apply, map_neg, e₂.apply_apply_eq_zero, neg_zero]

/-- The third exactness of the Barratt–Whitehead sequence of a ladder. -/
private theorem exact_comp_prod {C A₂ B₂ B' C' A₂' : Type*}
    [AddCommGroup C] [AddCommGroup A₂] [AddCommGroup B₂] [AddCommGroup B'] [AddCommGroup C']
    [AddCommGroup A₂'] [Module K C] [Module K A₂] [Module K B₂] [Module K B'] [Module K C']
    [Module K A₂']
    (h : C →ₗ[K] A₂) (f₂ : A₂ →ₗ[K] B₂) (g' : B' →ₗ[K] C') (h' : C' →ₗ[K] A₂')
    (c : C ≃ₗ[K] C') (a₂ : A₂ →ₗ[K] A₂')
    (s₃ : ∀ x, h' (c x) = a₂ (h x)) (e₃ : Function.Exact h f₂) (e₂' : Function.Exact g' h') :
    Function.Exact (h ∘ₗ c.symm.toLinearMap ∘ₗ g') (a₂.prod f₂) := by
  intro z
  change (a₂ z, f₂ z) = 0 ↔ ∃ y, h (c.symm (g' y)) = z
  constructor
  · intro hz
    obtain ⟨h1, h2⟩ := Prod.mk.inj hz
    obtain ⟨w, rfl⟩ := (e₃ z).1 h2
    obtain ⟨y, hy⟩ := (e₂' (c w)).1 (by rw [s₃, h1])
    exact ⟨y, by rw [hy, LinearEquiv.symm_apply_apply]⟩
  · rintro ⟨y, rfl⟩
    refine Prod.ext ?_ (e₃.apply_apply_eq_zero _)
    change a₂ (h (c.symm (g' y))) = 0
    rw [← s₃, LinearEquiv.apply_symm_apply, e₂'.apply_apply_eq_zero]

end BarrattWhitehead

section Cohomology

open SingularCochain SingularChain

/-- The map `Y' - X' → Y - X` induced by `f : Y' → Y` when `Y' - X' ⊆ f⁻¹(Y - X)`. -/
private def complMap {Y' Y : TopCat.{0}} (f : Y' ⟶ Y) {X : Set Y} {X' : Set Y'}
    (h : X'ᶜ ⊆ f ⁻¹' Xᶜ) : TopCat.of ↥X'ᶜ ⟶ TopCat.of ↥Xᶜ :=
  TopCat.ofHom ⟨fun y ↦ ⟨f y.1, h y.2⟩, (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- **Naturality of the coboundary of a pair.** For a map of pairs
`f : (Y', Y' - X') → (Y, Y - X)`, the coboundaries `H^p(Y - X) → H^{p+1}(Y, Y - X)` and
`H^p(Y' - X') → H^{p+1}(Y', Y' - X')` commute with the pullbacks. -/
private theorem map_delta {Y' Y : TopCat.{0}} (f : Y' ⟶ Y) {X : Set Y} {X' : Set Y'}
    (h : X'ᶜ ⊆ f ⁻¹' Xᶜ) (p : ℕ)
    (x : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of ↥Xᶜ) Set.univ p) :
    (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) f h (p + 1 : ℕ)).hom
        (cohomologyWithSupports.delta ℚ Y X p x) =
      cohomologyWithSupports.delta ℚ Y' X' p ((rationalCohomologyMap (complMap f h) p).hom x) := by
  apply (relativeSingularCohomologyEquiv ℚ X'ᶜ (p + 1)).injective
  obtain ⟨ψ, hψ⟩ := Submodule.Quotient.mk_surjective _
    (relativeSingularCohomologyEquiv ℚ _ p x)
  set χ : Simplex Y p → ℚ := extendCochain ψ.1
  have hχ : cochainPullback ℚ (subspaceInclusion Y Xᶜ) p χ = ψ.1 := cochainPullback_extendCochain _
  rw [relativeSingularCohomologyEquiv_map, cohomologyWithSupports.delta_mk p x ψ hψ.symm χ hχ,
    relCohomologyMap_mk]
  have hx' : relativeSingularCohomologyEquiv ℚ _ p ((rationalCohomologyMap (complMap f h) p).hom x)
      = Submodule.Quotient.mk ⟨cochainPullback ℚ (complMap f h) p ψ.1,
          cochainPullback_mem_relCocycles _ (fun _ hx ↦ hx) ψ.2⟩ := by
    refine (relativeSingularCohomologyEquiv_map (complMap f h)
      (A' := (Set.univ : Set (TopCat.of ↥X'ᶜ))ᶜ) (A := (Set.univ : Set (TopCat.of ↥Xᶜ))ᶜ)
      (fun _ hx ↦ absurd (Set.mem_univ _) hx) p x).trans ?_
    rw [← hψ]
    rfl
  have hχ' : cochainPullback ℚ (subspaceInclusion Y' X'ᶜ) p (cochainPullback ℚ f p χ) =
      cochainPullback ℚ (complMap f h) p ψ.1 := by
    rw [← hχ]
    rfl
  rw [cohomologyWithSupports.delta_mk p _ _ hx' _ hχ']
  congr 2

private theorem rationalCohomologyMap_eq_of_homotopy {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (q : ℕ) : rationalCohomologyMap f q = rationalCohomologyMap g q :=
  relativeSingularCohomology.map_eq_of_homotopy ℚ H (fun y hy ↦ absurd (Set.mem_univ y) hy) _ _ q

private theorem rationalCohomologyMap_apply_apply {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (q : ℕ) (x : rationalCohomology Z q) :
    (rationalCohomologyMap f q).hom ((rationalCohomologyMap g q).hom x) =
      (rationalCohomologyMap (f ≫ g) q).hom x := by
  rw [MMP.Fourfold.rationalCohomologyMap_comp]
  rfl

/-- A homotopy equivalence `i` with left inverse `r` induces a bijection in cohomology. -/
private theorem bijective_rationalCohomologyMap_of_homotopy {X Y : TopCat.{0}} (i : X ⟶ Y)
    (r : Y ⟶ X) (hri : i ≫ r = 𝟙 X) (H : TopCat.Homotopy (r ≫ i) (𝟙 Y)) (q : ℕ) :
    Function.Bijective (rationalCohomologyMap i q).hom := by
  refine Function.bijective_iff_has_inverse.2 ⟨(rationalCohomologyMap r q).hom, fun x ↦ ?_,
    fun x ↦ ?_⟩
  · rw [rationalCohomologyMap_apply_apply, rationalCohomologyMap_eq_of_homotopy H,
      MMP.Fourfold.rationalCohomologyMap_id]
    rfl
  · rw [rationalCohomologyMap_apply_apply, hri, MMP.Fourfold.rationalCohomologyMap_id]
    rfl

/-- **Relative cohomology of a deformation retract.** If `Y - X' ⊆ Y - X` and the inclusion
`Y - X' → Y - X` is a homotopy equivalence with a left inverse, then the forgetful map
`H^j(Y, Y - X) → H^j(Y, Y - X')` is bijective. -/
private theorem bijective_forget_of_homotopy {Y : TopCat.{0}} {X X' : Set Y} (hXX' : X ⊆ X')
    (r : TopCat.of ↥Xᶜ ⟶ TopCat.of ↥X'ᶜ)
    (hri : complMap (𝟙 Y) (Set.compl_subset_compl.2 hXX') ≫ r = 𝟙 _)
    (H : TopCat.Homotopy (r ≫ complMap (𝟙 Y) (Set.compl_subset_compl.2 hXX')) (𝟙 _)) (j : ℤ) :
    Function.Bijective (cohomologyWithSupports.forget ℚ (ModuleCat.of ℚ ℚ) Y hXX' j).hom := by
  set i := complMap (𝟙 Y) (Set.compl_subset_compl.2 hXX')
  have hi : ∀ q, Function.Bijective (rationalCohomologyMap i q).hom :=
    bijective_rationalCohomologyMap_of_homotopy i r hri H
  have hres : ∀ q (x : rationalCohomology Y q),
      (cohomologyWithSupports.restrictCompl ℚ Y X' q).hom x =
        (rationalCohomologyMap i q).hom ((cohomologyWithSupports.restrictCompl ℚ Y X q).hom x) := by
    intro q x
    change (rationalCohomologyMap (subspaceInclusion Y X'ᶜ) q).hom x =
      (rationalCohomologyMap i q).hom ((rationalCohomologyMap (subspaceInclusion Y Xᶜ) q).hom x)
    rw [rationalCohomologyMap_apply_apply]
    rfl
  have htoc : ∀ (q : ℕ) x, (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) Y X' q).hom
      ((cohomologyWithSupports.forget ℚ (ModuleCat.of ℚ ℚ) Y hXX' q).hom x) =
        (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) Y X q).hom x := by
    intro q x
    rw [cohomologyWithSupports.toCohomology, cohomologyWithSupports.toCohomology,
      ← ModuleCat.comp_apply, ← cohomologyWithSupports.forget_trans]
  rcases lt_or_ge j 0 with hj | hj
  · haveI := cohomologyWithSupports.subsingleton_of_neg (R := ℚ) (Z := Y) (S := X) hj
    have := cohomologyWithSupports.subsingleton_of_neg (R := ℚ) (Z := Y) (S := X') hj
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj
  cases n with
  | zero =>
    exact LinearMap.bijective_of_bijective_of_injective_of_left_exact
      (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) Y X (0 : ℕ)).hom
      (cohomologyWithSupports.restrictCompl ℚ Y X (0 : ℕ)).hom
      (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) Y X' (0 : ℕ)).hom
      (cohomologyWithSupports.restrictCompl ℚ Y X' (0 : ℕ)).hom
      (cohomologyWithSupports.forget ℚ (ModuleCat.of ℚ ℚ) Y hXX' (0 : ℕ)).hom LinearMap.id
      (rationalCohomologyMap i 0).hom (LinearMap.ext fun x ↦ htoc 0 x)
      (LinearMap.ext fun x ↦ hres 0 x)
      (cohomologyWithSupports.exact_toCohomology_restrictCompl ℚ Y X 0)
      (cohomologyWithSupports.exact_toCohomology_restrictCompl ℚ Y X' 0)
      Function.bijective_id (hi 0).1
      (cohomologyWithSupports.injective_toCohomology_zero ℚ Y X)
      (cohomologyWithSupports.injective_toCohomology_zero ℚ Y X')
  | succ m =>
    exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
      (cohomologyWithSupports.restrictCompl ℚ Y X m).hom
      (cohomologyWithSupports.delta ℚ Y X m)
      (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) Y X (m + 1 : ℕ)).hom
      (cohomologyWithSupports.restrictCompl ℚ Y X (m + 1 : ℕ)).hom
      (cohomologyWithSupports.restrictCompl ℚ Y X' m).hom
      (cohomologyWithSupports.delta ℚ Y X' m)
      (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) Y X' (m + 1 : ℕ)).hom
      (cohomologyWithSupports.restrictCompl ℚ Y X' (m + 1 : ℕ)).hom
      LinearMap.id (rationalCohomologyMap i m).hom
      (cohomologyWithSupports.forget ℚ (ModuleCat.of ℚ ℚ) Y hXX' (m + 1 : ℕ)).hom
      LinearMap.id (rationalCohomologyMap i (m + 1)).hom
      (LinearMap.ext fun x ↦ hres m x)
      (LinearMap.ext fun x ↦ (map_delta (𝟙 Y) (Set.compl_subset_compl.2 hXX') m x).symm)
      (LinearMap.ext fun x ↦ htoc (m + 1) x)
      (LinearMap.ext fun x ↦ hres (m + 1) x)
      (cohomologyWithSupports.exact_restrictCompl_delta ℚ Y X m)
      (cohomologyWithSupports.exact_delta_toCohomology ℚ Y X m)
      (cohomologyWithSupports.exact_toCohomology_restrictCompl ℚ Y X (m + 1))
      (cohomologyWithSupports.exact_restrictCompl_delta ℚ Y X' m)
      (cohomologyWithSupports.exact_delta_toCohomology ℚ Y X' m)
      (cohomologyWithSupports.exact_toCohomology_restrictCompl ℚ Y X' (m + 1))
      Function.surjective_id (hi m) Function.bijective_id (hi (m + 1)).1

private theorem map_eq_map {Y' Y : TopCat.{0}} {f g : Y' ⟶ Y} (hfg : f = g) {A' : Set Y'}
    {A : Set Y} (hf : A' ⊆ f ⁻¹' A) (hg : A' ⊆ g ⁻¹' A) (j : ℤ) :
    relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) f hf j =
      relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) g hg j := by
  subst hfg
  rfl

private theorem map_apply_map {Y'' Y' Y : TopCat.{0}} (g : Y'' ⟶ Y') (f : Y' ⟶ Y)
    {A'' : Set Y''} {A' : Set Y'} {A : Set Y} (hg : A'' ⊆ g ⁻¹' A') (hf : A' ⊆ f ⁻¹' A)
    (hgf : A'' ⊆ (g ≫ f) ⁻¹' A) (j : ℤ)
    (x : relativeSingularCohomology ℚ (ModuleCat.of ℚ ℚ) Y A j) :
    (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) g hg j).hom
        ((relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) f hf j).hom x) =
      (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) (g ≫ f) hgf j).hom x := by
  rw [relativeSingularCohomology.map_comp ℚ (ModuleCat.of ℚ ℚ) g f hg hf]
  rfl

/-- A map of pairs with an inverse map of pairs induces a bijection in cohomology. -/
private theorem bijective_map_of_inverse {Y' Y : TopCat.{0}} (e : Y' ⟶ Y) (e' : Y ⟶ Y')
    (h₁ : e ≫ e' = 𝟙 Y') (h₂ : e' ≫ e = 𝟙 Y) {A' : Set Y'} {A : Set Y} (h : A' ⊆ e ⁻¹' A)
    (h' : A ⊆ e' ⁻¹' A') (j : ℤ) :
    Function.Bijective (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) e h j).hom := by
  have hid : ∀ {Z : TopCat.{0}} (B : Set Z)
      (x : relativeSingularCohomology ℚ (ModuleCat.of ℚ ℚ) Z B j)
      (hB : B ⊆ (𝟙 Z) ⁻¹' B),
      (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) (𝟙 Z) hB j).hom x = x := by
    intro Z B x hB
    rw [relativeSingularCohomology.map_id]
    rfl
  refine Function.bijective_iff_has_inverse.2
    ⟨(relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) e' h' j).hom, fun x ↦ ?_, fun x ↦ ?_⟩
  · have hB : A ⊆ (e' ≫ e) ⁻¹' A := by
      rw [h₂]
      exact fun _ hx ↦ hx
    exact (map_apply_map e' e h' h hB j x).trans
      ((congrArg (fun φ ↦ φ.hom x) (map_eq_map h₂ hB (fun _ hx ↦ hx) j)).trans (hid A x _))
  · have hB : A' ⊆ (e ≫ e') ⁻¹' A' := by
      rw [h₁]
      exact fun _ hx ↦ hx
    exact (map_apply_map e e' h h' hB j x).trans
      ((congrArg (fun φ ↦ φ.hom x) (map_eq_map h₁ hB (fun _ hx ↦ hx) j)).trans (hid A' x _))

private theorem bijective_pullback_subspaceInclusion {Y : TopCat.{0}} {V X : Set Y}
    (hV : IsOpen V) (hX : IsClosed X) (hXV : X ⊆ V) (j : ℤ) :
    Function.Bijective
      (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (subspaceInclusion Y V) X j).hom :=
  (ConcreteCategory.isIso_iff_bijective _).1
    (cohomologyWithSupports.isIso_pullback_subspaceInclusion ℚ hV hX hXV j)

/-- **Excision along a map that is a homeomorphism near the supports.** Let `f : Y' → Y`,
`C ⊆ Y` closed and `U ⊇ C` open such that `f` restricts to a homeomorphism `f⁻¹(U) → U`. Then
`f^* : H^j(Y, Y - C) → H^j(Y', Y' - f⁻¹(C))` is bijective. -/
private theorem bijective_pullback_of_isHomeomorph {Y' Y : TopCat.{0}} (f : Y' ⟶ Y) {C U : Set Y}
    (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U) (hf : IsHomeomorph (U.restrictPreimage f))
    (j : ℤ) :
    Function.Bijective (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f C j).hom := by
  set e := hf.homeomorph
  let fU : TopCat.of ↥(f ⁻¹' U) ⟶ TopCat.of ↥U := TopCat.ofHom ⟨e, e.continuous⟩
  let gU : TopCat.of ↥U ⟶ TopCat.of ↥(f ⁻¹' U) := TopCat.ofHom ⟨e.symm, e.symm.continuous⟩
  have h2 := bijective_pullback_subspaceInclusion (Y := Y') (hU.preimage f.hom.continuous)
    (hC.preimage f.hom.continuous) (Set.preimage_mono hCU) j
  have hA : ((subspaceInclusion Y' (f ⁻¹' U)) ⁻¹' (f ⁻¹' C))ᶜ ⊆
      fU ⁻¹' ((subspaceInclusion Y U) ⁻¹' C)ᶜ := fun _ hx ↦ hx
  have hA' : ((subspaceInclusion Y U) ⁻¹' C)ᶜ ⊆
      gU ⁻¹' ((subspaceInclusion Y' (f ⁻¹' U)) ⁻¹' (f ⁻¹' C))ᶜ := fun y hy hy' ↦ by
    apply hy
    change (y : Y) ∈ C
    have : (e (e.symm y) : Y) = y := congrArg Subtype.val (e.apply_symm_apply y)
    rw [← this]
    exact hy'
  have key : (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
      (subspaceInclusion Y' (f ⁻¹' U)) (f ⁻¹' C) j).hom ∘
        (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f C j).hom =
      (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) fU hA j).hom ∘
        (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (subspaceInclusion Y U) C j).hom := by
    funext x
    have e1 := map_apply_map (subspaceInclusion Y' (f ⁻¹' U)) f (A := Cᶜ)
      (fun _ hx ↦ hx) (fun _ hx ↦ hx) (fun _ hx ↦ hx) j x
    have e2 := map_apply_map fU (subspaceInclusion Y U) (A := Cᶜ) hA
      (fun _ hx ↦ hx) (fun _ hx ↦ hx) j x
    have e3 : relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ)
        (subspaceInclusion Y' (f ⁻¹' U) ≫ f) (A := Cᶜ) (fun _ hx ↦ hx) j =
        relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) (fU ≫ subspaceInclusion Y U)
          (A := Cᶜ) (fun _ hx ↦ hx) j :=
      map_eq_map (TopCat.ext fun _ ↦ rfl) _ _ j
    exact e1.trans ((congrArg (fun φ ↦ φ.hom x) e3).trans e2.symm)
  rw [← Function.Bijective.of_comp_iff' h2, key]
  exact (bijective_map_of_inverse fU gU (TopCat.ext fun x ↦ e.symm_apply_apply x)
    (TopCat.ext fun y ↦ e.apply_symm_apply y) hA hA' j).comp
      (bijective_pullback_subspaceInclusion hU hC hCU j)

private theorem forget_pullback {Y' Y : TopCat.{0}} (f : Y' ⟶ Y) {X X' : Set Y} (h : X ⊆ X')
    (j : ℤ) (x : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y X j) :
    (cohomologyWithSupports.forget ℚ (ModuleCat.of ℚ ℚ) Y' (Set.preimage_mono h) j).hom
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f X j).hom x) =
      (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f X' j).hom
        ((cohomologyWithSupports.forget ℚ (ModuleCat.of ℚ ℚ) Y h j).hom x) := by
  have e1 := map_apply_map (𝟙 Y') f (A := Xᶜ) (A' := (f ⁻¹' X)ᶜ) (A'' := (f ⁻¹' X')ᶜ)
    (Set.compl_subset_compl.2 (Set.preimage_mono h)) (fun _ hx ↦ hx)
    (fun _ hx ↦ Set.compl_subset_compl.2 h hx) j x
  have e2 := map_apply_map f (𝟙 Y) (A := Xᶜ) (A' := X'ᶜ) (A'' := (f ⁻¹' X')ᶜ)
    (fun _ hx ↦ hx) (Set.compl_subset_compl.2 h) (fun _ hx ↦ Set.compl_subset_compl.2 h hx) j x
  have e3 : relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) (𝟙 Y' ≫ f) (A := Xᶜ)
      (A' := (f ⁻¹' X')ᶜ) (fun _ hx ↦ Set.compl_subset_compl.2 h hx) j =
      relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) (f ≫ 𝟙 Y)
        (fun _ hx ↦ Set.compl_subset_compl.2 h hx) j :=
    map_eq_map (by rw [Category.id_comp, Category.comp_id]) _ _ j
  exact e1.trans ((congrArg (fun φ ↦ φ.hom x) e3).trans e2.symm)

private theorem forget_apply_forget {Y : TopCat.{0}} {X X' X'' : Set Y} (h : X ⊆ X')
    (h' : X' ⊆ X'') (j : ℤ) (x : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y X j) :
    (cohomologyWithSupports.forget ℚ (ModuleCat.of ℚ ℚ) Y h' j).hom
        ((cohomologyWithSupports.forget ℚ (ModuleCat.of ℚ ℚ) Y h j).hom x) =
      (cohomologyWithSupports.forget ℚ (ModuleCat.of ℚ ℚ) Y (h.trans h') j).hom x := by
  rw [cohomologyWithSupports.forget_trans ℚ (ModuleCat.of ℚ ℚ) Y h h' j]
  rfl

private noncomputable abbrev fgt (j : ℤ) {Z : TopCat.{0}} {S S' : Set Z} (h : S ⊆ S') :=
  (cohomologyWithSupports.forget ℚ (ModuleCat.of ℚ ℚ) Z h j).hom

private theorem fgt_comp_fgt {Y : TopCat.{0}} {X X' X'' : Set Y} (h : X ⊆ X') (h' : X' ⊆ X'')
    (j : ℤ) : fgt j h' ∘ fgt j h = fgt j (h.trans h') :=
  funext (forget_apply_forget h h' j)

/-- The supports `S ⊆ Y` have *retracting neighbourhoods* if the complement `Y - S` has a
fundamental system of open neighbourhoods `Y - X` (`X` closed) of which it is a deformation
retract: the inclusion `Y - S → Y - X` has a left inverse which is a homotopy inverse. -/
private def HasRetractingNbhds {Y : TopCat.{0}} (S : Set Y) : Prop :=
  ∀ O : Set Y, IsOpen O → Sᶜ ⊆ O → ∃ X : Set Y, IsClosed X ∧ Oᶜ ⊆ X ∧ ∃ hXS : X ⊆ S,
    ∃ r : TopCat.of ↥Xᶜ ⟶ TopCat.of ↥Sᶜ,
      complMap (𝟙 Y) (Set.compl_subset_compl.2 hXS) ≫ r = 𝟙 _ ∧
      Nonempty (TopCat.Homotopy (r ≫ complMap (𝟙 Y) (Set.compl_subset_compl.2 hXS)) (𝟙 _))

private theorem HasRetractingNbhds.exists {Y : TopCat.{0}} {S : Set Y} (hS : HasRetractingNbhds S)
    {O : Set Y} (hO : IsOpen O) (hSO : Sᶜ ⊆ O) :
    ∃ X : Set Y, IsClosed X ∧ Oᶜ ⊆ X ∧ ∃ hXS : X ⊆ S, ∀ j : ℤ,
      Function.Bijective (cohomologyWithSupports.forget ℚ (ModuleCat.of ℚ ℚ) Y hXS j).hom := by
  obtain ⟨X, hX, hOX, hXS, r, hr, ⟨H⟩⟩ := hS O hO hSO
  exact ⟨X, hX, hOX, hXS, bijective_forget_of_homotopy hXS r hr H⟩

/-- **Excision for a closed map that is a homeomorphism off a closed set.** Let `f : Y' → Y` be a
closed map, `A ⊆ Y` closed such that `f` restricts to a homeomorphism `Y' - f⁻¹(A) → Y - A`, and
suppose `A` and `f⁻¹(A)` have retracting neighbourhoods. Then
`f^* : H^j(Y, A) → H^j(Y', f⁻¹(A))` is bijective. -/
private theorem bijective_pullback_compl {Y' Y : TopCat.{0}} (f : Y' ⟶ Y)
    (hfc : IsClosedMap f) {A : Set Y} (hA : IsClosed A)
    (hf : IsHomeomorph (Aᶜ.restrictPreimage f)) (hRA : HasRetractingNbhds Aᶜ)
    (hRF : HasRetractingNbhds (f ⁻¹' Aᶜ)) (j : ℤ) :
    Function.Bijective (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f Aᶜ j).hom := by
  have hcont := f.hom.continuous
  have hAo : IsOpen Aᶜ := hA.isOpen_compl
  -- `W = Y - X₁`, a retracting neighbourhood of `A`
  obtain ⟨X₁, hX₁, -, hX₁A, b₁⟩ := hRA.exists isOpen_univ (Set.subset_univ _)
  -- `V = Y' - X₂ ⊆ f⁻¹(W)`
  obtain ⟨X₂, hX₂, hX₁₂, hX₂F, b₂⟩ := hRF.exists (O := (f ⁻¹' X₁)ᶜ)
    (hX₁.preimage hcont).isOpen_compl
    (Set.compl_subset_compl.2 (Set.preimage_mono hX₁A))
  rw [compl_compl] at hX₁₂
  -- `W' = Y - X₃` with `f⁻¹(W') ⊆ V`
  obtain ⟨X₃, hX₃, hX₂₃, hX₃A, b₃⟩ := hRA.exists (O := (f '' X₂ ∪ X₁)ᶜ)
    ((hfc X₂ hX₂).union hX₁).isOpen_compl (by
      rw [Set.compl_subset_compl]
      rintro _ (⟨y, hy, rfl⟩ | hy)
      · exact hX₂F hy
      · exact hX₁A hy)
  rw [compl_compl] at hX₂₃
  have hX₂₃' : X₂ ⊆ f ⁻¹' X₃ := fun y hy ↦ hX₂₃ (Or.inl ⟨y, hy, rfl⟩)
  have hX₁₃ : X₁ ⊆ X₃ := fun y hy ↦ hX₂₃ (Or.inr hy)
  obtain ⟨X₄, -, hX₃₄, hX₄F, b₄⟩ := hRF.exists (O := (f ⁻¹' X₃)ᶜ)
    (hX₃.preimage hcont).isOpen_compl
    (Set.compl_subset_compl.2 (Set.preimage_mono hX₃A))
  rw [compl_compl] at hX₃₄
  have hP1 := bijective_pullback_of_isHomeomorph f hX₁ hAo hX₁A hf j
  have hP3 := bijective_pullback_of_isHomeomorph f hX₃ hAo hX₃A hf j
  have hY13 : Function.Bijective (fgt j hX₁₃) := by
    rw [← (b₃ j).of_comp_iff', fgt_comp_fgt]
    exact b₁ j
  have hYX : Function.Bijective (fgt j (hX₁₂.trans hX₂₃')) := by
    have : fgt j (hX₁₂.trans hX₂₃') ∘
        (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f X₁ j).hom
        = (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f X₃ j).hom ∘ fgt j hX₁₃ :=
      funext fun x ↦ forget_pullback f hX₁₃ j x
    rw [← Function.Bijective.of_comp_iff _ hP1, this]
    exact hP3.comp hY13
  have hzy : Function.Bijective (fgt j (hX₂₃'.trans hX₃₄)) := by
    rw [← (b₄ j).of_comp_iff', fgt_comp_fgt]
    exact b₂ j
  have hy : Function.Bijective (fgt j hX₂₃') :=
    ⟨Function.Injective.of_comp (f := fgt j hX₃₄) (by rw [fgt_comp_fgt]; exact hzy.1),
      Function.Surjective.of_comp (g := fgt j hX₁₂) (by rw [fgt_comp_fgt]; exact hYX.2)⟩
  have hx : Function.Bijective (fgt j hX₁₂) := by
    rw [← hy.of_comp_iff', fgt_comp_fgt]
    exact hYX
  rw [← Function.Bijective.of_comp_iff _ (b₁ j)]
  have : (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f Aᶜ j).hom ∘ fgt j hX₁A =
      fgt j hX₂F ∘ fgt j hX₁₂ ∘
        (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f X₁ j).hom := by
    funext x
    rw [Function.comp_apply, ← forget_pullback f hX₁A j x, Function.comp_apply,
      Function.comp_apply, forget_apply_forget]
  rw [this]
  exact (b₂ j).comp (hx.comp hP1)

private theorem exact_comp_of_bijective {M N P Q : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [AddCommGroup Q] [Module ℚ M] [Module ℚ N] [Module ℚ P] [Module ℚ Q]
    {u : M →ₗ[ℚ] N} {e : N →ₗ[ℚ] P} {v : P →ₗ[ℚ] Q} (he : Function.Bijective e)
    (h : Function.Exact (e ∘ₗ u) v) : Function.Exact u (v ∘ₗ e) := by
  intro y
  rw [LinearMap.comp_apply, h (e y)]
  exact ⟨fun ⟨x, hx⟩ ↦ ⟨x, he.1 hx⟩, fun ⟨x, hx⟩ ↦ ⟨x, congrArg e hx⟩⟩

/-- The inclusion `(Y - (Y - S))` into `S` and back, as an isomorphism. -/
private theorem bijective_rationalCohomologyMap_complCompl {Y : TopCat.{0}} (S : Set Y) (q : ℕ) :
    Function.Bijective (rationalCohomologyMap
      (TopCat.ofHom ⟨Set.inclusion (fun _ h ↦ not_not.mp h), continuous_inclusion _⟩ :
        TopCat.of ↥(Sᶜᶜ : Set Y) ⟶ TopCat.of ↥S) q).hom :=
  bijective_rationalCohomologyMap_of_homotopy _
    (TopCat.ofHom ⟨Set.inclusion (fun _ h ↦ not_not.mpr h), continuous_inclusion _⟩) rfl
    (ContinuousMap.Homotopy.refl _) q

private theorem restrictCompl_eq_comp {Y : TopCat.{0}} (S : Set Y) (q : ℕ) :
    (cohomologyWithSupports.restrictCompl ℚ Y Sᶜ q).hom =
      (rationalCohomologyMap
        (TopCat.ofHom ⟨Set.inclusion (fun _ h ↦ not_not.mp h), continuous_inclusion _⟩ :
          TopCat.of ↥(Sᶜᶜ : Set Y) ⟶ TopCat.of ↥S) q).hom ∘ₗ
        (rationalCohomologyMap (subspaceInclusion Y S) q).hom :=
  LinearMap.ext fun x ↦ (rationalCohomologyMap_apply_apply
    (TopCat.ofHom ⟨Set.inclusion (fun _ h ↦ not_not.mp h), continuous_inclusion _⟩ :
      TopCat.of ↥(Sᶜᶜ : Set Y) ⟶ TopCat.of ↥S) (subspaceInclusion Y S) q x).symm

private theorem exact_toCohomology_subspaceInclusion {Y : TopCat.{0}} (S : Set Y) (q : ℕ) :
    Function.Exact (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) Y Sᶜ q).hom
      (rationalCohomologyMap (subspaceInclusion Y S) q).hom :=
  (bijective_rationalCohomologyMap_complCompl S q).1.comp_exact_iff_exact.1
    (restrictCompl_eq_comp S q ▸ cohomologyWithSupports.exact_toCohomology_restrictCompl ℚ Y Sᶜ q)

private theorem exact_subspaceInclusion_delta {Y : TopCat.{0}} (S : Set Y) (q : ℕ) :
    Function.Exact (rationalCohomologyMap (subspaceInclusion Y S) q).hom
      (cohomologyWithSupports.delta ℚ Y Sᶜ q ∘ₗ (rationalCohomologyMap
        (TopCat.ofHom ⟨Set.inclusion (fun _ h ↦ not_not.mp h), continuous_inclusion _⟩ :
          TopCat.of ↥(Sᶜᶜ : Set Y) ⟶ TopCat.of ↥S) q).hom) :=
  exact_comp_of_bijective (bijective_rationalCohomologyMap_complCompl S q)
    (restrictCompl_eq_comp S q ▸ cohomologyWithSupports.exact_restrictCompl_delta ℚ Y Sᶜ q)

private theorem exact_delta_toCohomology_comp {Y : TopCat.{0}} (S : Set Y) (q : ℕ) :
    Function.Exact (cohomologyWithSupports.delta ℚ Y Sᶜ q ∘ₗ (rationalCohomologyMap
        (TopCat.ofHom ⟨Set.inclusion (fun _ h ↦ not_not.mp h), continuous_inclusion _⟩ :
          TopCat.of ↥(Sᶜᶜ : Set Y) ⟶ TopCat.of ↥S) q).hom)
      (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) Y Sᶜ (q + 1 : ℕ)).hom :=
  (bijective_rationalCohomologyMap_complCompl S q).2.comp_exact_iff_exact.2
    (cohomologyWithSupports.exact_delta_toCohomology ℚ Y Sᶜ q)

private theorem delta_comp_restrictPreimage {Y' Y : TopCat.{0}} (f : Y' ⟶ Y) (A : Set Y) (q : ℕ)
    (x : rationalCohomology (TopCat.of A) q) :
    cohomologyWithSupports.delta ℚ Y' (f ⁻¹' Aᶜ) q ((rationalCohomologyMap
        (TopCat.ofHom ⟨Set.inclusion (fun _ h ↦ not_not.mp h), continuous_inclusion _⟩ :
          TopCat.of ((f ⁻¹' Aᶜ)ᶜ : Set Y') ⟶ TopCat.of ↥(f ⁻¹' A)) q).hom
        ((rationalCohomologyMap (TopCat.ofHom (f.hom.restrictPreimage A)) q).hom x)) =
      (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f Aᶜ (q + 1 : ℕ)).hom
        (cohomologyWithSupports.delta ℚ Y Aᶜ q ((rationalCohomologyMap
          (TopCat.ofHom ⟨Set.inclusion (fun _ h ↦ not_not.mp h), continuous_inclusion _⟩ :
            TopCat.of ↥(Aᶜᶜ : Set Y) ⟶ TopCat.of A) q).hom x)) := by
  set g : TopCat.of ((f ⁻¹' Aᶜ)ᶜ : Set Y') ⟶ TopCat.of ↥(f ⁻¹' A) :=
    TopCat.ofHom ⟨Set.inclusion (fun _ h ↦ not_not.mp h), continuous_inclusion _⟩
  set gR : TopCat.of ↥(Aᶜᶜ : Set Y) ⟶ TopCat.of A :=
    TopCat.ofHom ⟨Set.inclusion (fun _ h ↦ not_not.mp h), continuous_inclusion _⟩
  set νF : TopCat.of ↥(f ⁻¹' A) ⟶ TopCat.of A := TopCat.ofHom (f.hom.restrictPreimage A)
  have hfX : (f ⁻¹' Aᶜ)ᶜ ⊆ f ⁻¹' Aᶜᶜ := fun _ hx ↦ hx
  have hsq : g ≫ νF = complMap f hfX ≫ gR := TopCat.ext fun _ ↦ rfl
  change cohomologyWithSupports.delta ℚ Y' (f ⁻¹' Aᶜ) q
      ((rationalCohomologyMap g q).hom ((rationalCohomologyMap νF q).hom x)) =
    (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) f hfX (q + 1 : ℕ)).hom
      (cohomologyWithSupports.delta ℚ Y Aᶜ q ((rationalCohomologyMap gR q).hom x))
  rw [map_delta f hfX q, rationalCohomologyMap_apply_apply, rationalCohomologyMap_apply_apply, hsq]

/-- **The cohomology sequence of a relative isomorphism.** Let `f : Y' → Y` and `A ⊆ Y` with
`f^* : H^*(Y, A) → H^*(Y', f⁻¹A)` bijective. Then the Barratt–Whitehead sequence
`⋯ → H^p Y → H^p Y' ⊕ H^p A → H^p (f⁻¹A) → H^{p+1} Y → ⋯` of the two pair sequences is exact,
with connecting map `H^p(f⁻¹A) → H^{p+1}(Y', f⁻¹A) ≅ H^{p+1}(Y, A) → H^{p+1} Y`. -/
private theorem cohomology_sequence {Y' Y : TopCat.{0}} (f : Y' ⟶ Y) (A : Set Y)
    (hbij : ∀ j : ℤ,
      Function.Bijective (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f Aᶜ j).hom) :
    let iA : TopCat.of A ⟶ Y := subspaceInclusion Y A
    let iF : TopCat.of ↥(f ⁻¹' A) ⟶ Y' := subspaceInclusion Y' (f ⁻¹' A)
    let νF : TopCat.of ↥(f ⁻¹' A) ⟶ TopCat.of A := TopCat.ofHom (f.hom.restrictPreimage A)
    let g : TopCat.of ((f ⁻¹' Aᶜ)ᶜ : Set Y') ⟶ TopCat.of ↥(f ⁻¹' A) :=
      TopCat.ofHom ⟨Set.inclusion (fun _ h ↦ not_not.mp h), continuous_inclusion _⟩
    (∀ p : ℕ, Function.Exact
        ((rationalCohomologyMap f p).hom.prod (rationalCohomologyMap iA p).hom)
        ((-(rationalCohomologyMap iF p).hom).coprod (rationalCohomologyMap νF p).hom)) ∧
    Function.Injective ((rationalCohomologyMap f 0).hom.prod (rationalCohomologyMap iA 0).hom) ∧
    ∀ p : ℕ, ∃ δ : rationalCohomology (TopCat.of ↥(f ⁻¹' A)) p →ₗ[ℚ] rationalCohomology Y (p + 1),
      Function.Exact
        ((-(rationalCohomologyMap iF p).hom).coprod (rationalCohomologyMap νF p).hom) δ ∧
      Function.Exact δ
        ((rationalCohomologyMap f (p + 1)).hom.prod (rationalCohomologyMap iA (p + 1)).hom) ∧
      ∀ x y, (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f Aᶜ (p + 1 : ℕ)).hom y =
          cohomologyWithSupports.delta ℚ Y' (f ⁻¹' Aᶜ) p ((rationalCohomologyMap g p).hom x) →
        δ x =
          (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) Y Aᶜ (p + 1 : ℕ)).hom y := by
  intro iA iF νF g
  let gR : TopCat.of ↥(Aᶜᶜ : Set Y) ⟶ TopCat.of A :=
    TopCat.ofHom ⟨Set.inclusion (fun _ h ↦ not_not.mp h), continuous_inclusion _⟩
  set dR := fun q : ℕ ↦ cohomologyWithSupports.delta ℚ Y Aᶜ q ∘ₗ (rationalCohomologyMap gR q).hom
  set dN := fun q : ℕ ↦
    cohomologyWithSupports.delta ℚ Y' (f ⁻¹' Aᶜ) q ∘ₗ (rationalCohomologyMap g q).hom
  set α := fun j : ℤ ↦ (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f Aᶜ j).hom
  set toR := fun j : ℤ ↦ (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) Y Aᶜ j).hom
  set toN := fun j : ℤ ↦
    (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) Y' (f ⁻¹' Aᶜ) j).hom
  -- the squares of the ladder
  have s₀ : ∀ (q : ℕ) x, (rationalCohomologyMap f q).hom (toR q x) = toN q (α q x) :=
    fun q x ↦ (forget_pullback f (Set.subset_univ Aᶜ) q x).symm
  have s₁ : ∀ (q : ℕ) x, (rationalCohomologyMap iF q).hom ((rationalCohomologyMap f q).hom x) =
      (rationalCohomologyMap νF q).hom ((rationalCohomologyMap iA q).hom x) := fun q x ↦ by
    rw [rationalCohomologyMap_apply_apply, rationalCohomologyMap_apply_apply]
    rfl
  have s₂ : ∀ (q : ℕ) x, dN q ((rationalCohomologyMap νF q).hom x) = α (q + 1 : ℕ) (dR q x) :=
    delta_comp_restrictPreimage f A
  have hcop : ∀ (q : ℕ), (-(rationalCohomologyMap iF q).hom).coprod (rationalCohomologyMap νF q).hom
      = -((rationalCohomologyMap iF q).hom.coprod (-(rationalCohomologyMap νF q).hom)) :=
    fun q ↦ by ext <;> simp
  refine ⟨fun p ↦ ?_, ?_, fun p ↦ ?_⟩
  · rw [hcop]
    exact exact_neg_right (exact_prod_coprod_neg (toR p) (rationalCohomologyMap iA p).hom (dR p)
      (toN p) (rationalCohomologyMap iF p).hom (dN p) (α p) (rationalCohomologyMap f p).hom
      (rationalCohomologyMap νF p).hom (α (p + 1 : ℕ)) (hbij p).2 (hbij (p + 1 : ℕ)).1
      (s₀ p) (s₁ p) (s₂ p) (exact_toCohomology_subspaceInclusion A p)
      (exact_subspaceInclusion_delta A p) (exact_toCohomology_subspaceInclusion (f ⁻¹' A) p)
      (exact_subspaceInclusion_delta (f ⁻¹' A) p))
  · refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
    obtain ⟨h1, h2⟩ := Prod.mk.inj hx
    obtain ⟨y, rfl⟩ := ((exact_toCohomology_subspaceInclusion A 0) x).1 h2
    have : α (0 : ℕ) y = 0 := cohomologyWithSupports.injective_toCohomology_zero ℚ Y' (f ⁻¹' Aᶜ)
      (by rw [map_zero]; exact (s₀ 0 y).symm.trans h1)
    rw [(injective_iff_map_eq_zero _).1 (hbij (0 : ℕ)).1 y this, map_zero]
  · let c := LinearEquiv.ofBijective (α (p + 1 : ℕ)) (hbij (p + 1 : ℕ))
    have s₂' : ∀ x, dN p (-(rationalCohomologyMap νF p).hom x) = c ((-dR p) x) := fun x ↦ by
      rw [map_neg, s₂, LinearMap.neg_apply, map_neg]
      rfl
    refine ⟨toR (p + 1 : ℕ) ∘ₗ c.symm.toLinearMap ∘ₗ dN p, ?_, ?_, fun x y hxy ↦ ?_⟩
    · simpa only [neg_neg] using exact_coprod_neg_comp (-dR p) (toR (p + 1 : ℕ))
        (-(rationalCohomologyMap iF p).hom) (dN p) (-(rationalCohomologyMap νF p).hom) c s₂'
        (exact_neg_left (exact_delta_toCohomology_comp A p))
        (exact_neg_left (exact_subspaceInclusion_delta (f ⁻¹' A) p))
    · exact exact_comp_prod (toR (p + 1 : ℕ)) (rationalCohomologyMap iA (p + 1)).hom (dN p)
        (toN (p + 1 : ℕ)) c (rationalCohomologyMap f (p + 1)).hom
        (fun x ↦ (s₀ (p + 1) x).symm) (exact_toCohomology_subspaceInclusion A (p + 1))
        (exact_delta_toCohomology_comp (f ⁻¹' A) p)
    · exact congrArg (toR (p + 1 : ℕ)) (c.symm_apply_eq.2 hxy.symm)

end Cohomology

section Homology

open Limits

variable {A B D A' B' D' : HomologicalComplex (ModuleCat.{0} ℚ) (ComplexShape.up ℤ)}

/-- **Naturality of the connecting map of a relative quasi-isomorphism.** -/
private theorem quasiIsoConnecting_naturality (f : A ⟶ B) (g : B ⟶ D) [Mono f] (w : f ≫ g = 0)
    (f' : A' ⟶ B') (g' : B' ⟶ D') [Mono f'] (w' : f' ≫ g' = 0)
    [QuasiIso (cokernel.desc f g w)] [QuasiIso (cokernel.desc f' g' w')]
    (a : A ⟶ A') (b : B ⟶ B') (d : D ⟶ D') (h₁ : f ≫ b = a ≫ f') (h₂ : g ≫ d = b ≫ g')
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    MMP.ModuleCatComplex.quasiIsoConnecting f g w i j hij ≫ HomologicalComplex.homologyMap a j =
      HomologicalComplex.homologyMap d i ≫
        MMP.ModuleCatComplex.quasiIsoConnecting f' g' w' i j hij := by
  let φ : ShortComplex.mk f (cokernel.π f) (cokernel.condition f) ⟶
      ShortComplex.mk f' (cokernel.π f') (cokernel.condition f') :=
    { τ₁ := a, τ₂ := b, τ₃ := cokernel.map f f' a b h₁, comm₁₂ := h₁.symm,
      comm₂₃ := by simp }
  have hδ := HomologicalComplex.HomologySequence.δ_naturality φ
    (MMP.ModuleCatComplex.shortExact_cokernel f) (MMP.ModuleCatComplex.shortExact_cokernel f')
    i j hij
  have hc : HomologicalComplex.homologyMap (cokernel.map f f' a b h₁) i ≫
      HomologicalComplex.homologyMap (cokernel.desc f' g' w') i =
      HomologicalComplex.homologyMap (cokernel.desc f g w) i ≫
        HomologicalComplex.homologyMap d i := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      cokernel.map_desc f g w f' g' w' a b d h₁ h₂]
  simp only [MMP.ModuleCatComplex.quasiIsoConnecting, Category.assoc]
  rw [hδ, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
  exact hc

private theorem chainMap_congr {Y' Y : TopCat.{0}} {f g : Y' ⟶ Y} (hfg : f = g) (hf : IsProperMap f)
    (hg : IsProperMap g) : borelMooreHomology.chainMap ℚ (ModuleCat.of ℚ ℚ) f hf =
      borelMooreHomology.chainMap ℚ (ModuleCat.of ℚ ℚ) g hg := by
  subst hfg
  rfl

private theorem restrictChainMap_comp_chainMap {Y' Y : TopCat.{0}} [T2Space Y'] [T2Space Y]
    (f : Y' ⟶ Y) (hf : IsProperMap f) (U : Opens Y) (U' : Opens Y')
    (hU : Opens.comap f.hom U = U') (g : TopCat.of U' ⟶ TopCat.of U) (hg : IsProperMap g)
    (hgf : ∀ x, (g x : Y) = f x) :
    borelMooreHomology.restrictChainMap ℚ (ModuleCat.of ℚ ℚ) U' ≫
        borelMooreHomology.chainMap ℚ (ModuleCat.of ℚ ℚ) g hg =
      borelMooreHomology.chainMap ℚ (ModuleCat.of ℚ ℚ) f hf ≫
        borelMooreHomology.restrictChainMap ℚ (ModuleCat.of ℚ ℚ) U := by
  subst hU
  rw [borelMooreHomology.chainMap_comp_restrictChainMap ℚ (ModuleCat.of ℚ ℚ) f hf U]
  congr 1
  exact chainMap_congr (TopCat.ext fun x ↦ Subtype.ext (hgf x)) _ _

/-- **Naturality of the Borel–Moore connecting map** under a proper map `f : Y' → Y` with
`f⁻¹(Y - X) = Y' - X'`: `∂ ∘ f_{U*} = f_{X*} ∘ ∂'`. -/
private theorem connecting_naturality {Y' Y : TopCat.{0}} [T2Space Y'] [T2Space Y] (f : Y' ⟶ Y)
    (hf : IsProperMap f) {X : Set Y} {X' : Set Y'} (hX : IsClosed X) (hX' : IsClosed X')
    (hU : Opens.comap f.hom (borelMooreHomology.complOpens hX) = borelMooreHomology.complOpens hX')
    (gX : TopCat.of X' ⟶ TopCat.of X) (hgX : IsProperMap gX)
    (hgXf : subspaceInclusion Y' X' ≫ f = gX ≫ subspaceInclusion Y X)
    (gU : TopCat.of (borelMooreHomology.complOpens hX') ⟶
      TopCat.of (borelMooreHomology.complOpens hX))
    (hgU : IsProperMap gU) (hgUf : ∀ x, (gU x : Y) = f x)
    (h : borelMooreHomology.IsRelativeQuasiIso ℚ (ModuleCat.of ℚ ℚ) hX)
    (h' : borelMooreHomology.IsRelativeQuasiIso ℚ (ModuleCat.of ℚ ℚ) hX') (k : ℤ) :
    borelMooreHomology.connecting ℚ (ModuleCat.of ℚ ℚ) hX' h' k ≫
        borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) gX hgX k =
      borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) gU hgU (k + 1) ≫
        borelMooreHomology.connecting ℚ (ModuleCat.of ℚ ℚ) hX h k := by
  have : QuasiIso _ := h
  have : QuasiIso _ := h'
  refine quasiIsoConnecting_naturality _ _ _ _ _ _
    (HomologicalComplex.extendMap (borelMooreHomology.chainMap ℚ (ModuleCat.of ℚ ℚ) gX hgX)
      ComplexShape.embeddingDownNat)
    (HomologicalComplex.extendMap (borelMooreHomology.chainMap ℚ (ModuleCat.of ℚ ℚ) f hf)
      ComplexShape.embeddingDownNat)
    (HomologicalComplex.extendMap (borelMooreHomology.chainMap ℚ (ModuleCat.of ℚ ℚ) gU hgU)
      ComplexShape.embeddingDownNat) ?_ ?_ _ _ _
  · rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
      ← borelMooreHomology.chainMap_comp, ← borelMooreHomology.chainMap_comp, chainMap_congr hgXf]
  · rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
      restrictChainMap_comp_chainMap f hf _ _ hU gU hgU hgUf]

private theorem pushforward_apply_comm {Y₁ Y₂ Y₃ Y₄ : TopCat.{0}} (f₁ : Y₁ ⟶ Y₂) (f₂ : Y₂ ⟶ Y₄)
    (g₁ : Y₁ ⟶ Y₃) (g₂ : Y₃ ⟶ Y₄) (h : f₁ ≫ f₂ = g₁ ≫ g₂) (hf₁ : IsProperMap f₁)
    (hf₂ : IsProperMap f₂) (hg₁ : IsProperMap g₁) (hg₂ : IsProperMap g₂) (k : ℤ) (x) :
    (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) f₂ hf₂ k).hom
        ((borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) f₁ hf₁ k).hom x) =
      (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) g₂ hg₂ k).hom
        ((borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) g₁ hg₁ k).hom x) := by
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← borelMooreHomology.pushforward_comp,
    ← borelMooreHomology.pushforward_comp]
  congr 2
  simp only [borelMooreHomology.pushforward, chainMap_congr h _ (hg₂.comp hg₁)]
  rfl

private theorem restrict_pushforward_comm {Y' Y : TopCat.{0}} [T2Space Y'] [T2Space Y]
    (f : Y' ⟶ Y) (hf : IsProperMap f) (U : Opens Y) (U' : Opens Y')
    (hU : Opens.comap f.hom U = U') (g : TopCat.of U' ⟶ TopCat.of U) (hg : IsProperMap g)
    (hgf : ∀ x, (g x : Y) = f x) (k : ℤ) (x) :
    (borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ) U k).hom
        ((borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) f hf k).hom x) =
      (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) g hg k).hom
        ((borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ) U' k).hom x) := by
  subst hU
  obtain rfl : g = borelMooreHomology.restrictPreimage f U :=
    TopCat.ext fun x ↦ Subtype.ext (hgf x)
  exact borelMooreHomology.restrict_pushforward_apply ℚ (ModuleCat.of ℚ ℚ) f hf U k x

/-- **The homology sequence of a relative isomorphism.** Let `f : Y' → Y` be proper, `X ⊆ Y`
closed with `f⁻¹(Y - X) = Y' - X'`, and suppose `f_* : H_*(Y' - X') → H_*(Y - X)` is bijective.
Then the Barratt–Whitehead sequence
`⋯ → H_{k+1} Y → H_k X' → H_k X ⊕ H_k Y' → H_k Y → ⋯` of the two localization sequences is
exact, with connecting map the restriction to `Y - X`, the inverse of `f_*` and `∂'`. -/
theorem homology_sequence {Y' Y : TopCat.{0}} [T2Space Y'] [T2Space Y] (f : Y' ⟶ Y)
    (hf : IsProperMap f) {X : Set Y} {X' : Set Y'} (hX : IsClosed X) (hX' : IsClosed X')
    (hU : Opens.comap f.hom (borelMooreHomology.complOpens hX) = borelMooreHomology.complOpens hX')
    (gX : TopCat.of X' ⟶ TopCat.of X) (hgX : IsProperMap gX)
    (hgXf : subspaceInclusion Y' X' ≫ f = gX ≫ subspaceInclusion Y X)
    (gU : TopCat.of (borelMooreHomology.complOpens hX') ⟶
      TopCat.of (borelMooreHomology.complOpens hX))
    (hgU : IsProperMap gU) (hgUf : ∀ x, (gU x : Y) = f x)
    (h : borelMooreHomology.IsRelativeQuasiIso ℚ (ModuleCat.of ℚ ℚ) hX)
    (h' : borelMooreHomology.IsRelativeQuasiIso ℚ (ModuleCat.of ℚ ℚ) hX')
    (hbij : ∀ k, Function.Bijective
      (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) gU hgU k).hom) :
    let pgX := fun k ↦ (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) gX hgX k).hom
    let pA := fun k ↦ (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (subspaceInclusion Y X)
      (borelMooreHomology.isProperMap_subspaceInclusion hX) k).hom
    let pF := fun k ↦ (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (subspaceInclusion Y' X') (borelMooreHomology.isProperMap_subspaceInclusion hX') k).hom
    let pf := fun k ↦ (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) f hf k).hom
    (∀ k : ℤ, Function.Exact ((pgX k).prod (-(pF k))) ((pA k).coprod (pf k))) ∧
    ∀ k : ℤ, ∃ bd : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y (k + 1) →ₗ[ℚ]
        borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of X') k,
      Function.Exact ((pA (k + 1)).coprod (pf (k + 1))) bd ∧
      Function.Exact bd ((pgX k).prod (-(pF k))) ∧
      ∀ c z, (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) gU hgU (k + 1)).hom z =
          (borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ)
            (borelMooreHomology.complOpens hX) (k + 1)).hom c →
        bd c = (borelMooreHomology.connecting ℚ (ModuleCat.of ℚ ℚ) hX' h' k).hom z := by
  intro pgX pA pF pf
  set pgU := fun k ↦ (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) gU hgU k).hom
  set res := fun k ↦ (borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ)
    (borelMooreHomology.complOpens hX) k).hom
  set res' := fun k ↦ (borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ)
    (borelMooreHomology.complOpens hX') k).hom
  set bdR := fun k ↦ (borelMooreHomology.connecting ℚ (ModuleCat.of ℚ ℚ) hX h k).hom
  set bdN := fun k ↦ (borelMooreHomology.connecting ℚ (ModuleCat.of ℚ ℚ) hX' h' k).hom
  have hnat : ∀ k x, pgX k (bdN k x) = bdR k (pgU (k + 1) x) := fun k x ↦
    congrArg (fun φ ↦ φ.hom x) (connecting_naturality f hf hX hX' hU gX hgX hgXf gU hgU hgUf h h' k)
  have s₁ : ∀ k x, pA k (pgX k x) = (-pf k) ((-pF k) x) := fun k x ↦ by
    rw [LinearMap.neg_apply, LinearMap.neg_apply, map_neg, neg_neg]
    exact (pushforward_apply_comm _ _ _ _ hgXf _ _ _ _ k x).symm
  have s₂ : ∀ k x, res k ((-pf k) x) = pgU k ((-res' k) x) := fun k x ↦ by
    rw [LinearMap.neg_apply, LinearMap.neg_apply, map_neg, map_neg]
    exact congrArg Neg.neg (restrict_pushforward_comm f hf _ _ hU gU hgU hgUf k x)
  refine ⟨fun k ↦ ?_, fun k ↦ ?_⟩
  · simpa only [neg_neg] using exact_prod_coprod_neg (bdN k) (-pF k) (-res' k) (bdR k) (pA k)
      (res k) (pgU (k + 1)) (pgX k) (-pf k) (pgU k) (hbij (k + 1)).2 (hbij k).1 (hnat k) (s₁ k)
      (s₂ k) (exact_neg_right (borelMooreHomology.exact_connecting_pushforward h' k))
      (exact_neg_left (exact_neg_right (borelMooreHomology.exact_pushforward_restrict h' k)))
      (borelMooreHomology.exact_connecting_pushforward h k)
      (borelMooreHomology.exact_pushforward_restrict h k)
  · let c := LinearEquiv.ofBijective (pgU (k + 1)) (hbij (k + 1))
    refine ⟨bdN k ∘ₗ c.symm.toLinearMap ∘ₗ res (k + 1), ?_, ?_, fun x z hxz ↦ ?_⟩
    · simpa only [neg_neg] using exact_coprod_neg_comp (-res' (k + 1)) (bdN k) (pA (k + 1))
        (res (k + 1)) (-pf (k + 1)) c (s₂ (k + 1))
        (exact_neg_left (borelMooreHomology.exact_restrict_connecting h' k))
        (borelMooreHomology.exact_pushforward_restrict h (k + 1))
    · exact exact_comp_prod (bdN k) (-pF k) (res (k + 1)) (bdR k) c (pgX k)
        (fun x ↦ (hnat k x).symm)
        (exact_neg_right (borelMooreHomology.exact_connecting_pushforward h' k))
        (borelMooreHomology.exact_restrict_connecting h k)
    · exact congrArg (bdN k) (c.symm_apply_eq.2 hxz.symm)

end Homology

section Geometry

/-- A complex point lies over `T` exactly when its point of the underlying space does. -/
private theorem mem_pointsOver_homeomorphUnderlyingSpace {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    (x : MMP.Analytic.ComplexPoints (X ↘ Spec (.of ℂ))) (T : Set X) :
    MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace x ∈ pointsOver (K := ℂ) T ↔
      x.toScheme ∈ T := by
  change x.hom _ ∈ T ↔ x.hom _ ∈ T
  exact Iff.of_eq (congrArg (fun a : ↥(Spec (.of ℂ)) ↦ x.hom a ∈ T) (Subsingleton.elim _ _))

/-- A morphism over `ℂ` which is an isomorphism over an open `V` induces a homeomorphism of
underlying spaces over `V(ℂ)`. -/
private theorem isHomeomorph_restrictPreimage_map {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [Y.Over (Spec (.of ℂ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))] (V : Y.Opens)
    [IsIso (f ∣_ V)] :
    IsHomeomorph ((pointsOver (K := ℂ) (V : Set Y)).restrictPreimage (map (K := ℂ) f)) := by
  set φX := MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace (X := X)
  set φY := MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace (X := Y)
  have hf : f ≫ Y ↘ Spec (.of ℂ) = X ↘ Spec (.of ℂ) := comp_over f _
  have h := MMP.Analytic.ComplexPoints.isHomeomorph_restrictPreimage_realize f hf V
  let eT : ↥{y : MMP.Analytic.ComplexPoints (Y ↘ Spec (.of ℂ)) | y.toScheme ∈ V} ≃ₜ
      ↥(pointsOver (K := ℂ) (V : Set Y)) :=
    φY.subtype fun y ↦ (mem_pointsOver_homeomorphUnderlyingSpace y _).symm
  let eP : ↥(map (K := ℂ) f ⁻¹' pointsOver (K := ℂ) (V : Set Y)) ≃ₜ
      ↥(MMP.Analytic.ComplexPoints.realize f hf ⁻¹'
        {y : MMP.Analytic.ComplexPoints (Y ↘ Spec (.of ℂ)) | y.toScheme ∈ V}) :=
    φX.symm.subtype fun p ↦
      (mem_pointsOver_homeomorphUnderlyingSpace (MMP.Analytic.ComplexPoints.realize f hf
        (φX.symm p)) _)
  exact (eP.trans (h.homeomorph.trans eT)).isHomeomorph

/-- The complex points of a closed subset of a projective complex scheme have retracting
neighbourhoods. -/
private theorem hasRetractingNbhds_pointsOver {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    (hX : IsProjective (X ↘ Spec (.of ℂ))) (D : Closeds X) :
    HasRetractingNbhds (Y := TopCat.of (UnderlyingSpace ℂ X))
      (pointsOver (K := ℂ) (D : Set X))ᶜ := by
  intro O hO hDO
  rw [compl_compl] at hDO
  set φ := MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace (X := X)
  set Dan : Set (MMP.Analytic.ComplexPoints (X ↘ Spec (.of ℂ))) :=
    MMP.Analytic.ComplexPoints.toScheme ⁻¹' (D : Set X)
  have hmem : ∀ x, φ x ∈ pointsOver (K := ℂ) (D : Set X) ↔ x ∈ Dan := fun x ↦
    mem_pointsOver_homeomorphUnderlyingSpace x _
  obtain ⟨Nb, hNb, hNbW, hDN, r, ⟨H⟩⟩ :=
    MMP.Analytic.exists_homotopicRel_retraction_of_isProjective (X ↘ Spec (.of ℂ)) hX D
      (φ ⁻¹' O) (hO.preimage φ.continuous) (fun x hx ↦ hDO ((hmem x).2 hx))
  have hXS : (φ.symm ⁻¹' Nb)ᶜ ⊆ (pointsOver (K := ℂ) (D : Set X))ᶜ := by
    intro y hy hyD
    exact hy (hDN ((hmem (φ.symm y)).1 ((φ.apply_symm_apply y).symm ▸ hyD)))
  refine ⟨(φ.symm ⁻¹' Nb)ᶜ, (hNb.preimage φ.symm.continuous).isClosed_compl, ?_, hXS, ?_⟩
  · intro y hy hyN
    apply hy
    have := hNbW hyN
    change φ (φ.symm y) ∈ O at this
    rwa [φ.apply_symm_apply] at this
  let e₁ : ↥((φ.symm ⁻¹' Nb)ᶜᶜ : Set (TopCat.of (UnderlyingSpace ℂ X))) ≃ₜ ↥Nb :=
    φ.symm.subtype fun _ ↦ not_not
  let e₂ : ↥((pointsOver (K := ℂ) (D : Set X))ᶜᶜ : Set (TopCat.of (UnderlyingSpace ℂ X))) ≃ₜ
      ↥Dan :=
    φ.symm.subtype fun y ↦ by
      rw [Set.mem_compl_iff, Set.mem_compl_iff, not_not, ← hmem, φ.apply_symm_apply]
  let ι : C(↥Dan, ↥Nb) := ⟨Set.inclusion hDN, continuous_inclusion hDN⟩
  have hr : ∀ d : ↥Dan, r (ι d) = d := fun d ↦ Set.inclusion_injective hDN
    (H.fst_eq_snd ⟨d, rfl⟩).symm
  refine ⟨TopCat.ofHom ((⟨e₂.symm, e₂.symm.continuous⟩ : C(_, _)).comp
    (r.comp ⟨e₁, e₁.continuous⟩)), ?_, ⟨?_⟩⟩
  · refine TopCat.ext fun y ↦ Subtype.ext ?_
    have : e₁ (complMap (𝟙 (TopCat.of (UnderlyingSpace ℂ X))) (Set.compl_subset_compl.2 hXS) y) =
      ι (e₂ y) := rfl
    change (φ (r (e₁ (complMap (𝟙 (TopCat.of (UnderlyingSpace ℂ X)))
      (Set.compl_subset_compl.2 hXS) y))).1) = y.1
    rw [this, hr]
    exact φ.apply_symm_apply y.1
  · refine (((ContinuousMap.Homotopy.refl (⟨e₁.symm, e₁.symm.continuous⟩ : C(_, _))).comp
      (H.toHomotopy.comp (ContinuousMap.Homotopy.refl (⟨e₁, e₁.continuous⟩ : C(_, _))))).symm).cast
      ?_ ?_
    · exact ContinuousMap.ext fun y ↦ rfl
    · exact ContinuousMap.ext fun y ↦ Subtype.ext (φ.apply_symm_apply y.1)

/-- The points of `X(ℂ)` over a closed subset of a complex scheme form a closed subset for which
the Borel–Moore localization sequence holds: it is the space of the reduced closed subscheme. -/
theorem isRelativeQuasiIso_pointsOver (S : Scheme.{0}) [S.Over (Spec (.of ℂ))]
    [IsComplexScheme S] (T : Closeds S)
    (hT : IsClosed (pointsOver (K := ℂ) (T : Set S) : Set (TopCat.of (UnderlyingSpace ℂ S)))) :
    borelMooreHomology.IsRelativeQuasiIso ℚ (ModuleCat.of ℚ ℚ)
      (Y := TopCat.of (UnderlyingSpace ℂ S)) hT := by
  obtain ⟨hYc, n, F, hF⟩ := hasBasis_contractible_and_exists_isClosedEmbedding S
  set i := (Scheme.IdealSheafData.vanishingIdeal T).subschemeι
  letI : (Scheme.IdealSheafData.vanishingIdeal T).subscheme.Over (Spec (.of ℂ)) :=
    ⟨i ≫ S ↘ Spec (.of ℂ)⟩
  haveI : i.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI : LocallyOfFiniteType ((Scheme.IdealSheafData.vanishingIdeal T).subscheme ↘
      Spec (.of ℂ)) := by
    rw [← comp_over i (Spec (.of ℂ))]
    infer_instance
  have hi := isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) i
  have hrange : Set.range (map (K := ℂ) i) = pointsOver (K := ℂ) (T : Set S) := by
    rw [range_map_of_isClosedImmersion, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hXc : HasOpenContractibleBasis ↥(pointsOver (K := ℂ) (T : Set S)) :=
    (UnderlyingSpace.hasOpenContractibleBasis _).of_homeomorph
      (hi.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange))
  exact borelMooreHomology.isRelativeQuasiIso_of_isClosedEmbedding ℚ (ModuleCat.of ℚ ℚ)
    (Y := TopCat.of (UnderlyingSpace ℂ S)) hF hT hXc hYc

/-- A scheme finite over a projective complex scheme is projective. -/
private theorem isProjective_of_isFinite_over {N R : Scheme.{0}} [R.Over (Spec (.of ℂ))]
    [N.Over (Spec (.of ℂ))] (hR : IsProjective (R ↘ Spec (.of ℂ))) (ν : N ⟶ R)
    [ν.IsOver (Spec (.of ℂ))] [IsFinite ν] : IsProjective (N ↘ Spec (.of ℂ)) := by
  rw [← comp_over ν (Spec (.of ℂ))]
  exact (Stacks.FiniteMorphismProjective.isProjective_of_isFinite ν).comp hR

/-- Push-forward along a homeomorphism is bijective. -/
theorem bijective_pushforward_of_homeomorph {Y' Y : TopCat.{0}} (g : Y' ⟶ Y)
    (hg : IsProperMap g) (e : Y' ≃ₜ Y) (he : ∀ x, g x = e x) (k : ℤ) :
    Function.Bijective (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) g hg k).hom := by
  let g' : Y ⟶ Y' := TopCat.ofHom ⟨e.symm, e.symm.continuous⟩
  have hg' : IsProperMap g' := e.symm.isProperMap
  have hid : ∀ {Z : TopCat.{0}} (u : Z ⟶ Z) (hu : IsProperMap u) (_ : u = 𝟙 Z) x,
      (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) u hu k).hom x = x := by
    intro Z u hu h x
    subst h
    rw [borelMooreHomology.pushforward_id]
    rfl
  refine Function.bijective_iff_has_inverse.2
    ⟨(borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) g' hg' k).hom, fun x ↦ ?_, fun x ↦ ?_⟩
  · rw [← ModuleCat.comp_apply, ← borelMooreHomology.pushforward_comp]
    exact hid _ _ (TopCat.ext fun y ↦ by
      change e.symm (g y) = y
      rw [he, e.symm_apply_apply]) x
  · rw [← ModuleCat.comp_apply, ← borelMooreHomology.pushforward_comp]
    exact hid _ _ (TopCat.ext fun y ↦ by
      change g (e.symm y) = y
      rw [he, e.apply_symm_apply]) x

end Geometry

end MMP.Proof_lem_mmp_conductor_ordinary_normalization_excision

namespace MMP.Analytic

open Proof_lem_mmp_conductor_ordinary_normalization_excision

/-- **Ordinary rational normalization excision.** Let `R` be a reduced projective complex scheme,
`ν : N ⟶ R` its normalization, and `A ⊆ R` closed with `ν` an isomorphism over `R - A`; let
`F(ℂ) = ν⁻¹(A(ℂ))`. Then in rational cohomology
`0 → H^0(R) → ⋯ → H^p(N) ⊕ H^p(A) → H^p(F) → H^{p+1}(R) → H^{p+1}(N) ⊕ H^{p+1}(A) → ⋯`
is exact, the maps being `(ν^*, i_A^*)`, `(a, b) ↦ ν_F^* b - i_F^* a`, and the connecting map
`ε : H^p(F) → H^{p+1}(R)` characterised by `ε x = forget y` whenever `ν^* y = δ x`, where
`ν^* : H^*(R, A) → H^*(N, F)` is bijective and `δ : H^p(F) → H^{p+1}(N, F)` is the coboundary.
In (Borel–Moore) homology,
`⋯ → H_{k+1}(A) ⊕ H_{k+1}(N) → H_{k+1}(R) → H_k(F) → H_k(A) ⊕ H_k(N) → H_k(R) → ⋯` is exact,
with maps `c ↦ (ν_{F*} c, -i_{F*} c)`, `(a, b) ↦ i_{A*} a + ν_* b`, and the connecting map
`∂ : H_{k+1}(R) → H_k(F)` characterised by `∂ c = ∂_{(N,F)} z` whenever `ν_* z = c|_{R - A}`,
where `ν_* : H^BM_*(N - F) → H^BM_*(R - A)` is bijective and `∂_{(N,F)}` is the Borel–Moore
connecting map of `F ⊆ N`. -/
@[mmp "lem_mmp_conductor_ordinary_normalization_excision"]
public theorem exact_normalization_excision
    {R N : Scheme.{0}} [R.Over (Spec (.of ℂ))] [N.Over (Spec (.of ℂ))]
    [IsComplexScheme R] [IsComplexScheme N] [IsReduced R]
    (hR : IsProjective (R ↘ Spec (.of ℂ)))
    (ν : N ⟶ R) [ν.IsOver (Spec (.of ℂ))] [IsFinite ν] [IsNormal N]
    (hν : ∃ U : R.Opens, Dense (U : Set R) ∧ Dense ((ν ⁻¹ᵁ U : N.Opens) : Set N) ∧
      IsIso (ν ∣_ U))
    (A : Closeds R) (hA : IsIso (ν ∣_ A.compl)) :
    let Rt := TopCat.of (UnderlyingSpace ℂ R)
    let Nt := TopCat.of (UnderlyingSpace ℂ N)
    let νt : Nt ⟶ Rt := TopCat.ofHom (map (K := ℂ) ν)
    let Aan : Set Rt := pointsOver (K := ℂ) (A : Set R)
    let Fan : Set Nt := νt ⁻¹' Aan
    let iA : TopCat.of Aan ⟶ Rt := subspaceInclusion Rt Aan
    let iF : TopCat.of Fan ⟶ Nt := subspaceInclusion Nt Fan
    let νF : TopCat.of Fan ⟶ TopCat.of Aan := TopCat.ofHom ((map (K := ℂ) ν).restrictPreimage Aan)
    let g : TopCat.of ((νt ⁻¹' Aanᶜ)ᶜ : Set Nt) ⟶ TopCat.of Fan :=
      TopCat.ofHom ⟨Set.inclusion (fun _ h ↦ not_not.mp h), continuous_inclusion _⟩
    let hAc : IsClosed Aan := isClosed_pointsOver A.isClosed
    let hFc : IsClosed Fan := hAc.preimage νt.hom.continuous
    let hνp : IsProperMap νt := IsComplexScheme.isProperMap_map ν
    let νC : TopCat.of (borelMooreHomology.complOpens hFc) ⟶
        TopCat.of (borelMooreHomology.complOpens hAc) :=
      TopCat.ofHom ((map (K := ℂ) ν).restrictPreimage Aanᶜ)
    let Hb : TopCat.{0} → ℤ → ModuleCat.{0} ℚ := fun Y k ↦
      MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y k
    let pA : ∀ k, Hb (TopCat.of Aan) k ⟶ Hb Rt k := fun k ↦
      borelMooreHomology.pushforward ℚ _ iA (borelMooreHomology.isProperMap_subspaceInclusion hAc) k
    let pF : ∀ k, Hb (TopCat.of Fan) k ⟶ Hb Nt k := fun k ↦
      borelMooreHomology.pushforward ℚ _ iF (borelMooreHomology.isProperMap_subspaceInclusion hFc) k
    let pν : ∀ k, Hb Nt k ⟶ Hb Rt k := fun k ↦ borelMooreHomology.pushforward ℚ _ νt hνp k
    let pνF : ∀ k, Hb (TopCat.of Fan) k ⟶ Hb (TopCat.of Aan) k := fun k ↦
      borelMooreHomology.pushforward ℚ _ νF (hνp.restrictPreimage Aan) k
    let pνC : ∀ k, Hb (TopCat.of (borelMooreHomology.complOpens hFc)) k ⟶
        Hb (TopCat.of (borelMooreHomology.complOpens hAc)) k := fun k ↦
      borelMooreHomology.pushforward ℚ _ νC (hνp.restrictPreimage Aanᶜ) k
    ((∀ p : ℕ, Function.Exact
        ((rationalCohomologyMap νt p).hom.prod (rationalCohomologyMap iA p).hom)
        ((-(rationalCohomologyMap iF p).hom).coprod (rationalCohomologyMap νF p).hom)) ∧
    Function.Injective
        ((rationalCohomologyMap νt 0).hom.prod (rationalCohomologyMap iA 0).hom) ∧
    (∀ j : ℤ, Function.Bijective
        (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) νt Aanᶜ j).hom) ∧
    ∀ p : ℕ, ∃ δ : rationalCohomology (TopCat.of Fan) p →ₗ[ℚ] rationalCohomology Rt (p + 1),
      Function.Exact
        ((-(rationalCohomologyMap iF p).hom).coprod (rationalCohomologyMap νF p).hom) δ ∧
      Function.Exact δ
        ((rationalCohomologyMap νt (p + 1)).hom.prod (rationalCohomologyMap iA (p + 1)).hom) ∧
      ∀ x y, (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) νt Aanᶜ (p + 1 : ℕ)).hom y =
          cohomologyWithSupports.delta ℚ Nt (νt ⁻¹' Aanᶜ) p ((rationalCohomologyMap g p).hom x) →
        δ x =
          (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) Rt Aanᶜ (p + 1 : ℕ)).hom y) ∧
    (∀ k : ℤ, Function.Exact ((pνF k).hom.prod (-(pF k).hom)) ((pA k).hom.coprod (pν k).hom)) ∧
    (∀ k : ℤ, Function.Bijective (pνC k).hom) ∧
    ∃ hrel : borelMooreHomology.IsRelativeQuasiIso ℚ (ModuleCat.of ℚ ℚ) hFc,
      ∀ k : ℤ, ∃ bd : Hb Rt (k + 1) →ₗ[ℚ] Hb (TopCat.of Fan) k,
        Function.Exact ((pA (k + 1)).hom.coprod (pν (k + 1)).hom) bd ∧
        Function.Exact bd ((pνF k).hom.prod (-(pF k).hom)) ∧
        ∀ c z, (pνC (k + 1)).hom z =
            (borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ)
              (borelMooreHomology.complOpens hAc) (k + 1)).hom c →
          bd c = (borelMooreHomology.connecting ℚ (ModuleCat.of ℚ ℚ) hFc hrel k).hom z := by
  intro Rt Nt νt Aan Fan iA iF νF g hAc hFc hνp νC Hb pA pF pν pνF pνC
  let AN : Closeds N := ⟨ν ⁻¹' (A : Set R), A.isClosed.preimage ν.continuous⟩
  have hhom : IsHomeomorph (Aanᶜ.restrictPreimage νt) := isHomeomorph_restrictPreimage_map ν A.compl
  have hRF : HasRetractingNbhds (νt ⁻¹' Aanᶜ) :=
    hasRetractingNbhds_pointsOver (isProjective_of_isFinite_over hR ν) AN
  have hbij := bijective_pullback_compl νt hνp.isClosedMap hAc hhom
    (hasRetractingNbhds_pointsOver hR A) hRF
  obtain ⟨c1, c2, c3⟩ := cohomology_sequence νt Aan hbij
  have hrelF : borelMooreHomology.IsRelativeQuasiIso ℚ (ModuleCat.of ℚ ℚ) hFc :=
    isRelativeQuasiIso_pointsOver N AN hFc
  have hbijC : ∀ k : ℤ, Function.Bijective (pνC k).hom := fun k ↦
    bijective_pushforward_of_homeomorph νC (hνp.restrictPreimage Aanᶜ) hhom.homeomorph
      (fun _ ↦ rfl) k
  obtain ⟨h1, h2⟩ := homology_sequence νt hνp hAc hFc (Opens.ext rfl) νF
    (hνp.restrictPreimage Aan) (TopCat.ext fun _ ↦ rfl) νC (hνp.restrictPreimage Aanᶜ)
    (fun _ ↦ rfl) (isRelativeQuasiIso_pointsOver R A hAc) hrelF hbijC
  exact ⟨⟨c1, c2, hbij, c3⟩, h1, hbijC, hrelF, h2⟩

end MMP.Analytic
